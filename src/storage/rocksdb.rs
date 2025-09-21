use crate::{INDEX_SIZE, Index, Position, Result, Storage};
use crate::{Reader, Serializable};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use rocksdb::DB;
use std::io;
use std::io::Cursor;
use std::sync::{Arc, RwLock};

#[cfg(test)]
mod test;

#[derive(Debug)]
pub struct RocksDBStorage {
  db: Arc<RwLock<DB>>,
  key_prefix: Vec<u8>,
  key_hashing: bool,
  key_for_metadata: Vec<u8>,
}

impl RocksDBStorage {
  pub fn new(db: Arc<RwLock<DB>>, key_prefix: &[u8], key_hashing: bool) -> Self {
    let key_prefix = key_prefix.to_vec();
    let key_for_metadata = create_key(0, key_hashing, &key_prefix);
    Self { db, key_prefix, key_hashing, key_for_metadata }
  }

  fn key(&self, i: Index) -> Vec<u8> {
    create_key(i, self.key_hashing, &self.key_prefix)
  }

  fn get_metadata(&self, guard: &DB) -> Result<Option<Position>> {
    match guard.get(&self.key_for_metadata)? {
      Some(value) => {
        let position = Cursor::new(&value[..8]).read_u64::<LittleEndian>()?;
        debug_assert!(position != 0);
        Ok(Some(position))
      }
      None => Ok(None),
    }
  }

  fn set_metadata(&self, guard: &DB, next_position: Position) -> Result<()> {
    debug_assert!(next_position != 0);
    if next_position == 1 {
      guard.delete(&self.key_for_metadata)?;
    } else {
      let mut meatadata = match guard.get(&self.key_for_metadata)? {
        Some(value) => value,
        None => vec![0u8; 8],
      };
      Cursor::new(&mut meatadata).write_u64::<LittleEndian>(next_position)?;
      guard.put(&self.key_for_metadata, meatadata)?;
    }
    Ok(())
  }
}

impl<S: Serializable> Storage<S> for RocksDBStorage {
  fn first(&mut self) -> Result<(Option<S>, Position)> {
    let key = self.key(1);
    let guard = self.db.read()?;
    match guard.get(&key)? {
      Some(value) => {
        let data = S::read(&mut Cursor::new(&value), 1)?;
        Ok((Some(data), 1))
      }
      None => Ok((None, 1)),
    }
  }

  fn last(&mut self) -> Result<(Option<S>, Position)> {
    let guard = self.db.read()?;
    match self.get_metadata(&guard)? {
      Some(next_position) => {
        let key = self.key(next_position - 1);
        match guard.get(&key)? {
          Some(value) => {
            let last_data = S::read(&mut Cursor::new(&value), next_position - 1)?;
            Ok((Some(last_data), next_position))
          }
          None => key_not_found(&key, next_position),
        }
      }
      None => Ok((None, 1)),
    }
  }

  fn put(&mut self, position: Position, entry: &S) -> Result<Position> {
    debug_assert!(position != 0);

    // エントリをバイト配列に変換
    let key = self.key(position);
    let mut value = Vec::with_capacity(1024);
    entry.write(&mut Cursor::new(&mut value))?;

    {
      // 値の保存
      let guard = self.db.write()?;
      guard.put(key, value)?;

      // メタデータの保存
      self.set_metadata(&guard, position + 1)?;
    }

    Ok(position + 1)
  }

  fn truncate(&mut self, position: Position) -> Result<bool> {
    debug_assert!(position != 0);

    let guard = self.db.write()?;
    if let Some(next_position) = self.get_metadata(&guard)? {
      debug_assert!(next_position != 0);
      if position < next_position {
        let mut p = position;
        loop {
          let key = self.key(p);
          match guard.get(&key)? {
            Some(_) => {
              guard.delete(key)?;
              p += 1;
            }
            None => break,
          }
        }
        self.set_metadata(&guard, position)?;
        return Ok(true);
      }
    }
    Ok(false)
  }

  fn reader(&self) -> Result<Box<dyn Reader<S>>> {
    let db = self.db.clone();
    let key_prefix = self.key_prefix.clone();
    let key_hashing = self.key_hashing;
    Ok(Box::new(RocksDBReader { db, key_prefix, key_hashing }))
  }
}

struct RocksDBReader {
  db: Arc<RwLock<DB>>,
  key_prefix: Vec<u8>,
  key_hashing: bool,
}

impl<S: Serializable> Reader<S> for RocksDBReader {
  fn read(&mut self, position: Position) -> Result<S> {
    let key = create_key(position, self.key_hashing, &self.key_prefix);
    let value = self.db.read()?.get(&key)?;
    if let Some(value) = value {
      Ok(S::read(&mut Cursor::new(&value), position)?)
    } else {
      key_not_found(&key, position)
    }
  }
}

fn create_key(position: Position, hashing: bool, prefix: &[u8]) -> Vec<u8> {
  let key = if hashing { bijective_scramble(position) } else { position };
  let mut key_buffer = Vec::with_capacity(prefix.len() + INDEX_SIZE as usize);
  key_buffer.extend_from_slice(prefix);
  key_buffer.extend_from_slice(&key.to_be_bytes());
  key_buffer
}

/// 与えられた u64 値を、全単射な方法でランダム風に変換します。
/// この関数は全単射 (入力と出力が一意に 1 対 1 対応) であり、同じ入力には常に同じ出力が対応します。
fn bijective_scramble(mut x: u64) -> u64 {
  // SplitMix64
  x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
  x ^ (x >> 31)
}

fn key_not_found<T>(key: &[u8], position: Position) -> Result<T> {
  Err(
    io::Error::new(
      io::ErrorKind::NotFound,
      format!("There is no entry stored for key {key:?} corresponding to position {position}"),
    )
    .into(),
  )
}
