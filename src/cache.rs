use crate::formula::{Model, is_pbst};
use crate::{Address, Entry, Index, MetaInfo, Reader, Result, Storage, read_entry_with_index_check};
use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

#[cfg(test)]
mod test;

#[derive(PartialEq, Eq, Debug)]
pub struct Cache {
  level: usize,
  model: Option<Model>,
  cache: HashMap<Index, Arc<Entry>>,
  pbst_roots: HashMap<Index, MetaInfo>,
}

impl Cache {
  /// Creates empty cache with specified level.
  pub(crate) fn empty(level: usize) -> Self {
    let model = None;
    let entries = HashMap::new();
    let pbst_roots = HashMap::new();
    Cache { level, model, cache: entries, pbst_roots }
  }

  /// Build the cache from the specified storage, specifying the latest entry and the level of this cache.
  pub(crate) fn load<S>(storage: &mut S, level: usize, last_entry: Entry) -> Result<Cache>
  where
    S: Storage<Entry>,
  {
    let i = last_entry.enode.meta.address.i;
    let model = Model::new(i);
    let mut cache = HashMap::new();

    // collect PBST root addresses for the i-generation tree
    let mut pbst_root_addrs = Vec::with_capacity(last_entry.enode.meta.address.j as usize);
    for inode in last_entry.inodes.iter().rev() {
      if !is_pbst(inode.meta.address.i, inode.meta.address.j) {
        pbst_root_addrs.push(inode.left);
      } else {
        pbst_root_addrs.push(inode.meta.address);
        break;
      }
    }
    if pbst_root_addrs.last().map(|addr| addr.i != i).unwrap_or(true) {
      pbst_root_addrs.push(last_entry.enode.meta.address);
    }

    // build the cache by reading additional level entries from storage
    cache.insert(last_entry.enode.meta.address.i, Arc::new(last_entry));
    if level > 0 {
      let mut reader = storage.reader()?;
      Self::load_with_level(&mut reader, level, &pbst_root_addrs, &mut cache)?;
    }

    let entries = if level == 0 {
      let mut reader = storage.reader()?;
      let mut level1_entries = HashMap::new();
      Self::load_with_level(&mut reader, 1, &pbst_root_addrs, &mut level1_entries)?;
      Cow::Owned(level1_entries)
    } else {
      Cow::Borrowed(&cache)
    };
    let pbst_roots = pbst_root_addrs
      .iter()
      .map(|addr| {
        let meta = if let Some(e) = entries.get(&addr.i) {
          *e.meta(addr.j).unwrap()
        } else {
          panic!("address ({}, {}) is not in entry collection: {:?}", addr.i, addr.j, entries)
        };
        (addr.i, meta)
      })
      .collect::<HashMap<_, _>>();

    Ok(Cache { level, model: Some(model), cache, pbst_roots })
  }

  /// Migrates from the current cache to the next generation with the specified entry.
  pub(crate) fn migrate(&self, entry: Entry, model: Model) -> Cache {
    let i = entry.enode.meta.address.i;
    debug_assert_eq!(self.revision() + 1, i);
    debug_assert_eq!(self.revision() + 1, model.n());
    let level = self.level;

    // collect metadata for all PBST root in the next generation
    let pbst_roots = model
      .pbst_roots()
      .map(|root| {
        if let Some(meta) = self.pbst_roots.get(&root.i) {
          debug_assert_eq!(root.j, meta.address.j);
          (root.i, *meta)
        } else {
          let entry = if root.i == entry.enode.meta.address.i {
            &entry
          } else if let Some(cached_entry) = self.entry(root.i) {
            cached_entry
          } else {
            panic!(
              "The PBST root b_{{{},{}}} must be present in cache: get_next_pbst_roots({}): {self:?}",
              root.i,
              root.j,
              model.n()
            )
          };
          let meta = if root.j == 0 { entry.enode.meta } else { entry.inode(root.j).unwrap().meta };
          debug_assert_eq!(root.i, meta.address.i);
          (root.i, meta)
        }
      })
      .collect::<HashMap<_, _>>();

    // create a new cache consisting of entries from the new entry to the distance level
    let mut cache = HashMap::new();
    if level > 0 {
      Self::migrate_cache(&self.cache, &entry, level, &mut cache);
    }
    cache.insert(i, Arc::new(entry));

    Cache { level, model: Some(model), cache, pbst_roots }
  }

  /// Return the number of cached nodes.
  pub fn len(&self) -> usize {
    self.cache.len()
  }

  pub fn is_empty(&self) -> bool {
    self.cache.is_empty()
  }

  pub fn level(&self) -> usize {
    self.level
  }

  // Refer to the cached entry.
  pub fn entry(&self, i: Index) -> Option<&Entry> {
    self.cache.get(&i).map(|e| e.as_ref())
  }

  fn load_with_level(
    reader: &mut Box<dyn Reader<Entry>>,
    level: usize,
    addrs: &[Address],
    cache: &mut HashMap<Index, Arc<Entry>>,
  ) -> Result<()> {
    for addr in addrs.iter() {
      let entry = read_entry_with_index_check(reader, addr.position, addr.i)?;
      let i = entry.enode.meta.address.i;
      if level > 1 {
        let left_addrs = entry.inodes.iter().map(|inode| inode.left).collect::<Vec<_>>();
        cache.insert(i, Arc::new(entry));
        Self::load_with_level(reader, level - 1, &left_addrs, cache)?;
      } else {
        cache.insert(i, Arc::new(entry));
      }
    }
    Ok(())
  }

  /// Returns `None` for 0-th generation.
  pub fn last_entry(&self) -> Option<&Entry> {
    let i = self.revision();
    self.cache.get(&i).map(|x| x.as_ref())
  }

  /// Returns `None` for 0-th generation.
  pub fn root(&self) -> Option<&MetaInfo> {
    self.last_entry().map(|e| e.inodes.last().map(|i| &i.meta).unwrap_or(&e.enode.meta))
  }

  pub fn revision(&self) -> Index {
    self.model.as_ref().map(|model| model.n()).unwrap_or(0)
  }

  pub fn get_pbst_root(&self, i: Index, j: u8) -> &MetaInfo {
    if let Some(meta) = self.pbst_roots.get(&i) {
      debug_assert_eq!(j, meta.address.j);
      meta
    } else {
      // キャッシュの内容が矛盾している
      panic!("the specified node b_{{{i},{j}}} doesn't exist in the cache for revison {}: {self:?}", self.revision())
    }
  }

  fn migrate_cache(
    cache: &HashMap<Index, Arc<Entry>>,
    entry: &Entry,
    distance: usize,
    new_cache: &mut HashMap<Index, Arc<Entry>>,
  ) {
    debug_assert_ne!(0, distance);
    for inode in entry.inodes.iter() {
      let i = inode.left.i;
      let left_entry = cache.get(&i).unwrap().clone();
      if distance > 1 {
        Self::migrate_cache(cache, left_entry.as_ref(), distance - 1, new_cache);
      }
      new_cache.insert(i, left_entry);
    }
  }
}
