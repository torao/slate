use crate::{BlockDevice, Position, Result};
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::sync::{Arc, LockResult, RwLock};

/// メモリ上の領域をストレージとして使用する実装です。`drop()` された時点で記録していた内容が消滅するため、テストや
/// 調査での使用を想定しています。
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
      return Err(io::Error::new(io::ErrorKind::PermissionDenied, "file is read-only"));
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
