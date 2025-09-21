use std::collections::{HashMap, HashSet};
use std::sync::{Arc, RwLock};

use crate::cache::Cache;
use crate::formula::{Model, is_pbst, root_of, subnodes_of};
use crate::{Address, ENode, Entry, Hash, INode, Index, MetaInfo, Position, Reader, Result, Storage};

#[test]
fn verify_the_number_of_cache_entries_for_level() {
  for level in 0..=5 {
    let mut cache = Cache::empty(level);
    assert_eq!(0, cache.len());
    assert_eq!(None, cache.last_entry());
    assert_eq!(None, cache.root());
    assert_eq!(0, cache.revision());

    for i in 1..=256 {
      let model = Model::new(i);
      let entry = create_mock_entry(i);
      cache = cache.migrate(entry.clone(), model);

      let expected = expected_cached_indices(cache.revision(), level);
      assert_eq!(expected.len(), cache.len());
      assert_eq!(Some(&entry), cache.last_entry());
      assert_eq!(Some(entry.root()), cache.root().cloned());
      assert_eq!(i, cache.revision());
      for i in expected.into_iter() {
        assert!(cache.entry(i).is_some());
      }
    }
  }
}

#[test]
fn load_cache_from_storage() -> Result<()> {
  for level in 0..=5 {
    let mut storage = CacheStorage::new();
    let (_, mut position) = storage.last()?;
    for i in 1..=256 {
      position = storage.put(position, &create_mock_entry(i))?;

      let (entry, _) = storage.last()?;
      let entry = entry.unwrap();
      let cache = Cache::load(&mut storage, level, entry.clone())?;

      let expected = expected_cached_indices(cache.revision(), level);
      assert_eq!(expected.len(), cache.len());
      assert_eq!(Some(&entry), cache.last_entry());
      assert_eq!(Some(entry.root()), cache.root().cloned());
      assert_eq!(i, cache.revision());
      for i in expected.into_iter() {
        assert!(cache.entry(i).is_some());
      }
    }
  }
  Ok(())
}

fn create_mock_entry(i: Index) -> Entry {
  let model = Model::new(i);
  let enode = ENode::new(MetaInfo::new(Address::new(i, 0, i), Hash::new([0u8; Hash::SIZE])), vec![]);
  let inodes = model
    .inodes()
    .iter()
    .map(|inode| {
      assert_eq!(i, inode.node.i);
      INode::new(
        MetaInfo::new(Address::new(i, inode.node.j, i), Hash::new([0u8; Hash::SIZE])),
        Address::new(inode.left.i, inode.right.j, inode.left.i),
        Address::new(inode.right.i, inode.right.j, inode.right.i),
      )
    })
    .collect::<Vec<_>>();
  Entry::new(enode, inodes)
}

/// Structurally solves for and returns the number of cache entries in a given revision.
fn expected_cached_indices(n: Index, level: usize) -> HashSet<Index> {
  assert!(n > 0);
  fn _expected_cached_indices(n: Index, i: Index, level: usize, indices: &mut HashSet<Index>) {
    indices.insert(i);
    if level > 0 {
      let mut j = root_of(i).1;
      while j != 0 {
        if is_pbst(i, j) || i == n {
          let il = subnodes_of(i, j).0.0;
          _expected_cached_indices(n, il, level - 1, indices);
        }
        j = subnodes_of(i, j).1.1;
      }
    }
  }
  let mut indices = HashSet::new();
  _expected_cached_indices(n, n, level, &mut indices);
  indices
}

struct CacheStorage {
  n: Index,
  cache: Arc<RwLock<HashMap<Position, Entry>>>,
}

impl CacheStorage {
  pub fn new() -> Self {
    CacheStorage { n: 1, cache: Arc::new(RwLock::new(HashMap::new())) }
  }
}

impl Storage<Entry> for CacheStorage {
  fn first(&mut self) -> Result<(Option<Entry>, Position)> {
    unimplemented!()
  }

  fn last(&mut self) -> Result<(Option<Entry>, Position)> {
    Ok((self.cache.read()?.get(&(self.n - 1)).cloned(), self.n))
  }

  fn put(&mut self, position: Position, data: &Entry) -> Result<crate::Position> {
    assert_eq!(self.n, position);
    assert_eq!(self.n, data.enode.meta.address.i);
    let mut lock = self.cache.write()?;
    lock.insert(self.n, data.clone());
    self.n += 1;
    Ok(self.n)
  }

  fn truncate(&mut self, position: Position) -> Result<bool> {
    let mut lock = self.cache.write()?;
    if position < self.n {
      for i in position..self.n {
        lock.remove(&i);
      }
      self.n = position;
      Ok(true)
    } else {
      Ok(false)
    }
  }

  fn reader(&self) -> Result<Box<dyn crate::Reader<Entry>>> {
    struct R {
      cache: Arc<RwLock<HashMap<Position, Entry>>>,
    }
    impl Reader<Entry> for R {
      fn read(&mut self, position: Position) -> Result<Entry> {
        Ok(self.cache.read()?.get(&position).unwrap().clone())
      }
    }
    Ok(Box::new(R { cache: self.cache.clone() }))
  }
}
