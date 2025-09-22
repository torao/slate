use crate::error::Error;
use crate::{BlockDevice, Position, Reader, Result, Serializable, Storage};
use std::collections::HashMap;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::sync::{Arc, LockResult, RwLock};

/// メモリ上の `HashMap` を Key-Value ストア型のストレージとして使用する実装です。`drop()` された時点で記録していた内容が消滅
/// するため、テストや動作確認での使用を想定しています。
/// 保存する `S` 型の値はシリアライズされずそのまま HashMap に保存されます。[MemoryStorage] と比較して [Entry] のシリアライズ
/// コストが省略されていますが、参照時に `clone()` を行うコストが存在します。
///
#[derive(Debug)]
pub struct MemKVS<S: Serializable + Clone + 'static> {
  kvs: Arc<RwLock<HashMap<Position, S>>>,
}

impl<S: Serializable + Clone + 'static> MemKVS<S> {
  pub fn new() -> Self {
    Self::with_kvs(Default::default())
  }

  pub fn with_kvs(kvs: Arc<RwLock<HashMap<Position, S>>>) -> Self {
    Self { kvs }
  }
}

impl<S: Serializable + Clone + 'static> Default for MemKVS<S> {
  fn default() -> Self {
    Self::new()
  }
}

impl<S: Serializable + Clone + 'static> Storage<S> for MemKVS<S> {
  type Reader = MemKVS<S>;

  fn first(&mut self) -> Result<(Option<S>, Position)> {
    let kvs = self.kvs.read()?;
    let n = kvs.len() as Position;
    Ok((kvs.get(&n).cloned(), n + 1))
  }

  fn last(&mut self) -> Result<(Option<S>, Position)> {
    let kvs = self.kvs.read()?;
    let n = kvs.len() as Position;
    if n == 0 { Ok((None, 1)) } else { Ok((kvs.get(&n).cloned(), n + 1)) }
  }

  fn put(&mut self, position: Position, data: &S) -> Result<Position> {
    let mut kvs = self.kvs.write()?;
    kvs.insert(position, data.clone());
    Ok(kvs.len() as Position + 1)
  }

  fn reader(&self) -> Result<Self::Reader> {
    Ok(MemKVS { kvs: self.kvs.clone() })
  }

  fn truncate(&mut self, position: Position) -> Result<bool> {
    let mut kvs = self.kvs.write()?;
    let mut p = position;
    while kvs.remove(&p).is_some() {
      p += 1;
    }
    Ok(p != position)
  }
}

impl<S: Serializable + Clone> Reader<S> for MemKVS<S> {
  fn read(&mut self, position: Position) -> Result<S> {
    let kvs = self.kvs.read()?;
    if let Some(data) = kvs.get(&position) {
      Ok(data.clone())
    } else {
      Err(
        io::Error::new(
          io::ErrorKind::NotFound,
          format!("There is no data stored corresponding to position {position}"),
        )
        .into(),
      )
    }
  }

  fn scan<E, F>(&mut self, position: Position, count: u64, mut callback: F) -> Result<u64>
  where
    E: std::error::Error + Send + Sync + 'static,
    F: FnMut(S) -> std::result::Result<(), E>,
  {
    let kvs = self.kvs.read()?;
    let mut read = 0;
    for i in 0..count {
      if let Some(data) = kvs.get(&(position + i)).cloned() {
        (callback)(data).map_err(|e| Error::Callback(Box::new(e)))?;
        read += 1;
      } else {
        break;
      }
    }
    Ok(read)
  }
}

/// メモリ上の領域をストレージとして使用する実装です。`drop()` された時点で記録していた内容が消滅するため、テストや
/// 調査での使用を想定しています。
///
#[derive(Debug)]
pub struct MemoryDevice {
  read_only: bool,
  buffer: Arc<RwLock<Vec<u8>>>,
  position: Position,
}

impl MemoryDevice {
  pub fn new() -> Self {
    Self::default()
  }

  /// 指定されたアトミック参照カウント/RWロック付きの可変バッファを使用するストレージを構築します。これは調査の目的で
  /// 外部からストレージの内容を参照することを想定しています。
  pub fn with(buffer: Arc<RwLock<Vec<u8>>>, read_only: bool) -> Self {
    let position = 0;
    Self { read_only, buffer, position }
  }
}

impl Default for MemoryDevice {
  /// 揮発性メモリを使用するストレージを構築します。
  fn default() -> Self {
    let buffer = Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024)));
    Self::with(buffer, false)
  }
}

impl BlockDevice for MemoryDevice {
  fn truncate(&mut self, position: Position) -> Result<bool> {
    if self.read_only {
      return Err(io::Error::new(io::ErrorKind::PermissionDenied, "this memory device is read-only").into());
    }
    let mut guard = lock2io(self.buffer.write())?;
    if position < guard.len() as Position {
      guard.truncate(position as usize);
      self.position = position;
      Ok(true)
    } else {
      Ok(false)
    }
  }

  fn clone_device(&self) -> Result<Self> {
    let read_only = true; // クローンは常に read-only
    let buffer = self.buffer.clone();
    let position = 0;
    Ok(Self { read_only, buffer, position })
  }
}

impl Read for MemoryDevice {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let guard = lock2io(self.buffer.read())?;
    let mut cursor = Cursor::new(&**guard);
    cursor.seek(SeekFrom::Start(self.position))?;
    let len = cursor.read(buf)?;
    debug_assert_eq!(self.position + len as u64, cursor.position());
    self.position = cursor.position();
    Ok(len)
  }
}

impl Write for MemoryDevice {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    if self.read_only {
      return Err(io::Error::new(io::ErrorKind::PermissionDenied, "this memory device is read-only"));
    }
    let mut guard = lock2io(self.buffer.write())?;
    let mut cursor = Cursor::new(&mut *guard);
    cursor.seek(SeekFrom::Start(self.position))?;
    let len = cursor.write(buf)?;
    debug_assert_eq!(self.position + len as u64, cursor.position());
    self.position = cursor.position();
    Ok(len)
  }

  fn flush(&mut self) -> io::Result<()> {
    Ok(())
  }
}

impl Seek for MemoryDevice {
  fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
    self.position = match pos {
      SeekFrom::Current(p) => (self.position as i64 + p) as u64,
      SeekFrom::End(p) => (lock2io(self.buffer.read())?.len() as i64 + p) as u64,
      SeekFrom::Start(p) => p,
    };
    Ok(self.position)
  }
}

/// `LockResult` を `io::Result` に変換します。
#[inline]
fn lock2io<T>(result: LockResult<T>) -> std::io::Result<T> {
  result.map_err(|err| std::io::Error::other(err.to_string()))
}
