use crate::{Error, INDEX_SIZE, Index, Position, Result, Storage};
use crate::{Reader, Serializable};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use rocksdb::DB;
use std::io::Cursor;
use std::sync::{Arc, RwLock};

#[cfg(test)]
mod test;

pub struct RocksDBStorage {
  db: Arc<RwLock<DB>>,
  key_prefix: Vec<u8>,
  key_hashing: bool,
  key_for_position: Vec<u8>,
}

impl RocksDBStorage {
  pub fn new(db: Arc<RwLock<DB>>, key_prefix: &[u8], key_hashing: bool) -> Self {
    let key_prefix = key_prefix.to_vec();
    let key_for_position = create_key(0, key_hashing, &key_prefix);
    Self { db, key_prefix, key_hashing, key_for_position }
  }

  fn position_to_value(position: Position) -> Vec<u8> {
    let mut value = Vec::with_capacity(u64::BITS as usize / 8);
    Cursor::new(&mut value).write_u64::<LittleEndian>(position).unwrap();
    value
  }

  fn value_to_position(value: &[u8]) -> Result<Position> {
    Ok(Cursor::new(&value).read_u64::<LittleEndian>()?)
  }

  fn key(&self, i: Index) -> Vec<u8> {
    create_key(i, self.key_hashing, &self.key_prefix)
  }
}

impl<S: Serializable> Storage<S> for RocksDBStorage {
  fn boot(&mut self) -> Result<(Option<S>, Position)> {
    let guard = self.db.write()?;
    match guard.get(&self.key_for_position)? {
      Some(value) => {
        let position = Self::value_to_position(&value)?;
        let key = self.key(position - 1);
        match guard.get(&key)? {
          Some(value) => {
            let data = S::read(&mut Cursor::new(&value), position - 1)?;
            Ok((Some(data), position))
          }
          None => key_not_found(&key, position),
        }
      }
      None => Ok((None, 1)),
    }
  }

  fn put(&mut self, position: Position, entry: &S) -> Result<Position> {
    // エントリをバイト配列に変換
    let key = self.key(position);
    let mut value = Vec::with_capacity(1024);
    entry.write(&mut Cursor::new(&mut value))?;

    // 次の位置をバイト配列に変換
    let position_value = Self::position_to_value(position + 1);

    // 値の保存
    {
      let guard = self.db.write()?;
      guard.put(key, value)?;
      guard.put(&self.key_for_position, position_value)?;
    }

    Ok(position + 1)
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
  Err(Error::InternalStateInconsistency {
    message: format!("There is no entry stored for key {key:?} corresponding to position {position}"),
  })
}
