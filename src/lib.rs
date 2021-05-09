use std::cmp::min;
use std::fs::*;
use std::io;
use std::io::Write;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LockResult, RwLock};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, Key};

use crate::checksum::{HashRead, HashWrite};
use crate::error::Detail::*;

mod checksum;
pub mod error;

#[cfg(test)]
mod test;

pub type Result<T> = std::result::Result<T, error::Detail>;

/// 抽象化されたストレージ。読み込み用または書き込み用のカーソルを参照することができる。
pub trait Storage {
  fn truncate(&mut self) -> Result<()>;
  fn open(&mut self, writable: bool) -> Result<Box<dyn Cursor>>;
}

impl Storage for dyn AsRef<Path> {
  fn truncate(&mut self) -> Result<()> {
    File::open(self)?.set_len(0)?;
    Ok(())
  }
  fn open(&mut self, writable: bool) -> Result<Box<dyn Cursor>> {
    Ok(Box::new(OpenOptions::new().write(writable).read(true).open(self)?))
  }
}

pub struct MemStorage {
  buffer: Arc<RwLock<Vec<u8>>>,
}

impl MemStorage {
  pub fn new() -> MemStorage {
    MemStorage { buffer: Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024))) }
  }
}

impl Storage for MemStorage {
  fn truncate(&mut self) -> Result<()> {
    let mut buffer = lock2io(self.buffer.write())?;
    buffer.truncate(0);
    Ok(())
  }

  fn open(&mut self, _writable: bool) -> Result<Box<dyn Cursor>> {
    Ok(Box::new(MemCursor { position: 0, buffer: self.buffer.clone() }))
  }
}

struct MemCursor {
  position: usize,
  buffer: Arc<RwLock<Vec<u8>>>,
}

impl Cursor for MemCursor {}

impl io::Seek for MemCursor {
  fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
    self.position = match pos {
      io::SeekFrom::Start(position) => position as usize,
      io::SeekFrom::End(position) => {
        let mut buffer = lock2io(self.buffer.write())?;
        let new_position = (buffer.len() as i64 + position) as usize;
        while buffer.len() < new_position {
          buffer.push(0u8);
        }
        new_position
      }
      io::SeekFrom::Current(position) => (self.position as i64 + position) as usize,
    };
    Ok(self.position as u64)
  }
}

impl io::Read for MemCursor {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let buffer = lock2io(self.buffer.read())?;
    let length = min(buf.len(), buffer.len() - self.position);
    (&mut buf[..]).write_all(&buffer[self.position..self.position + length])?;
    self.position += length;
    Ok(length)
  }
}

impl io::Write for MemCursor {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    let mut buffer = lock2io(self.buffer.write())?;
    let length = min(buf.len(), buffer.len() - self.position);
    if length > 0 {
      buffer.write_all(&buf[0..length])?;
    }
    let length = buf.len() - length;
    for i in 0..buf.len() - length {
      buffer.push(buf[length + i]);
    }
    self.position += buf.len();
    Ok(buf.len())
  }

  fn flush(&mut self) -> io::Result<()> {
    Ok(())
  }
}

fn lock2io<T>(result: LockResult<T>) -> io::Result<T> {
  result.map_err(|err| io::Error::new(io::ErrorKind::Other, err.to_string()))
}

pub trait Cursor: io::Seek + io::Read + io::Write {}

impl Cursor for File {}

impl Cursor for io::Cursor<&mut Vec<u8>> {}

const HIGHWAYHASH64_KEY: [u64; 4] = [0u64, 1, 2, 3];

pub const HASH_SIZE: usize = 32;

pub const MAX_PAYLOAD_SIZE: usize = 0x7FFFFFFF;

pub type Hash = [u8; HASH_SIZE];

#[derive(PartialEq, Eq, Debug)]
struct Address {
  /// LSHT のリスト構造上での位置。1 から開始します。
  i: u64,
  /// このノードから最も遠い葉ノードまでの距離 (レベル)。0 の場合、ノードが葉ノードであることを示しています。
  j: u8,
  /// このノードを含むエントリのファイル上での位置。
  position: u64,
}

#[derive(PartialEq, Eq, Debug)]
struct ENode {
  /// このノードのアドレス。
  address: Address,
  payload: Box<Vec<u8>>,
  hash: Hash,
}

#[derive(PartialEq, Eq, Debug)]
struct INode {
  /// このノードのアドレス。
  address: Address,
  /// 左枝のノードのアドレス
  left: Address,
  /// 右枝のノードのアドレス
  right: Address,
  /// このノードのハッシュ値
  hash: Hash,
}

#[derive(PartialEq, Eq, Debug)]
struct Entry {
  enode: ENode,
  inodes: Vec<INode>,
}

/// この実装のバージョン
const STORAGE_MAJOR_VERSION: u8 = 0u8;
const STORAGE_MINOR_VERSION: u8 = 0u8;
const STORAGE_VERSION: u8 = (STORAGE_MAJOR_VERSION << 4) | (STORAGE_MINOR_VERSION & 0x0F);

fn is_version_compatible(version: u8) -> bool {
  version >> 4 == STORAGE_MAJOR_VERSION
    && (STORAGE_MAJOR_VERSION != 0 || version & 0x0F != STORAGE_MINOR_VERSION)
}

/// LSHTree ファイルの先頭に記録される識別子
const STORAGE_IDENTIFIER: [u8; 3] = [0x01u8, 0xF3, 0x33];

pub struct LSHT<S: Storage> {
  storage: Box<S>,
  cursor: Box<dyn Cursor>,
  confirmed_index: AtomicU64,
}

impl<S: Storage> LSHT<S> {
  /// 指定されたストレージをデータベースとして使用します。
  pub fn new(mut storage: S) -> Result<LSHT<S>> {
    let cursor = storage.open(true)?;
    let mut db = LSHT { storage: Box::new(storage), cursor, confirmed_index: AtomicU64::new(0u64) };
    db.init()?;
    Ok(db)
  }

  fn init(&mut self) -> Result<()> {
    let mut cursor = self.storage.open(true)?;

    let length = cursor.seek(io::SeekFrom::End(0))?;
    match length {
      0 => {
        // マジックナンバーの書き込み
        cursor.write_all(&STORAGE_IDENTIFIER)?;
        cursor.write_u8(STORAGE_VERSION)?;
      }
      1..=3 => return Err(FileIsNotContentsOfLSHTree { message: "bad magic number" }),
      _ => {
        // マジックナンバーの確認
        let mut buffer = [0u8; 4];
        cursor.seek(io::SeekFrom::Start(0))?;
        cursor.read_exact(&mut buffer)?;
        if buffer[..3] != STORAGE_IDENTIFIER[..] {
          return Err(FileIsNotContentsOfLSHTree { message: "bad magic number" });
        } else if is_version_compatible(buffer[3]) {
          return Err(IncompatibleVersion(buffer[3] >> 4, buffer[3] & 0x0F));
        }
      }
    }

    let length = cursor.seek(io::SeekFrom::End(0))?;
    let tail = if length == 4 {
      None
    } else {
      // 末尾のエントリを読み込み
      back_to_safety(cursor.as_mut(), 4 + 8, "The first entry is corrupted.")?;
      let offset = cursor.read_u32::<LittleEndian>()?;
      back_to_safety(cursor.as_mut(), offset + 4, "The last entry is corrupted.")?;
      let entry = read_entry(&mut cursor)?;
      if cursor.stream_position()? != length {
        // 壊れたストレージから読み込んだ offset が、たまたまどこかの正しいエントリ境界を指していた場合、正しく
        // 読み込めるが結果となる位置は末尾と一致しない。
        let msg = "The last entry is corrupted.".to_string();
        return Err(DamagedStorage(msg));
      }
      Some(entry)
    };

    let confirmed_index = tail.map(|e| e.enode.address.i).unwrap_or(0u64);
    if confirmed_index != 0 {
      self.confirmed_index.store(confirmed_index, Ordering::SeqCst);
    }

    Ok(())
  }
}

/// 指定されたカーソルの現在の位置からエントリを読み込みます。
/// 正常終了時のカーソルは次のエントリを指しています。
fn read_entry<C: io::Seek + io::Read>(r: &mut C) -> Result<Entry> {
  let position = r.stream_position()?;
  let mut hasher = HighwayBuilder::new(Key(HIGHWAYHASH64_KEY));
  let mut r = HashRead::new(r, &mut hasher);
  let entry = read_entry_without_check(&mut r, position)?;

  // オフセットの検証
  let offset = r.length();
  let trailer_offset = r.read_u32::<LittleEndian>()?;
  if offset != trailer_offset as u64 {
    return Err(IncorrectEntryHeadOffset { expected: trailer_offset, actual: offset });
  }

  // チェックサムの検証
  let checksum = r.finish();
  let trailer_checksum = r.read_u64::<LittleEndian>()?;
  if checksum != trailer_checksum {
    let length = offset as u32 + 4 + 8;
    return Err(ChecksumVerificationFailed {
      at: position,
      length,
      expected: trailer_checksum,
      actual: checksum,
    });
  }

  Ok(entry)
}

/// 指定されたカーソルの現在の位置からエントリを読み込みます。トレイラーの offset と checksum は読み込まれない
/// ため、正常終了時のカーソルは offset の位置を指しています。
fn read_entry_without_check(r: &mut dyn io::Read, position: u64) -> Result<Entry> {
  let mut hash = [0u8; HASH_SIZE];

  let i = r.read_u64::<LittleEndian>()?;

  // 中間ノードの読み込み
  let inode_count = r.read_u8()?;
  let mut right_j = 0u8;
  let mut inodes = Vec::<INode>::with_capacity(inode_count as usize);
  for _ in 0..inode_count as usize {
    let j = (r.read_u8()? & (64 - 1)) + 1; // 下位 6-bit のみを使用
    let left_position = r.read_u64::<LittleEndian>()?;
    let left_i = r.read_u64::<LittleEndian>()?;
    let left_j = r.read_u8()?;
    r.read_exact(&mut hash)?;
    inodes.push(INode {
      address: Address { i, j, position },
      left: Address { i: left_i, j: left_j, position: left_position },
      right: Address { i, j: right_j, position },
      hash,
    });
    right_j = j;
  }

  // 葉ノードの読み込み
  let payload_size = r.read_u32::<LittleEndian>()? & MAX_PAYLOAD_SIZE as u32;
  let mut payload = Vec::<u8>::with_capacity(payload_size as usize);
  unsafe { payload.set_len(payload_size as usize) };
  r.read_exact(&mut payload)?;
  r.read_exact(&mut hash)?;
  let enode = ENode { address: Address { i, j: 0, position }, payload: Box::new(payload), hash };

  Ok(Entry { enode, inodes })
}

/// 指定されたカーソルにエントリを書き込みます。
/// このエントリに対して書き込みが行われた長さを返します。
fn write_entry(w: &mut dyn Write, e: &Entry) -> Result<usize> {
  debug_assert!(e.enode.payload.len() <= MAX_PAYLOAD_SIZE);
  debug_assert!(e.inodes.len() <= 0xFF);

  let mut hasher = HighwayBuilder::new(Key(HIGHWAYHASH64_KEY));
  let mut w = HashWrite::new(w, &mut hasher);

  // 中間ノードの書き込み
  w.write_u64::<LittleEndian>(e.enode.address.i)?;
  w.write_u8(e.inodes.len() as u8)?;
  for i in &e.inodes {
    debug_assert_eq!((i.address.j - 1) & (64 - 1), i.address.j - 1);
    w.write_u8((i.address.j - 1) & (64 - 1))?; // 下位 6-bit のみ保存
    w.write_u64::<LittleEndian>(i.left.position)?;
    w.write_u64::<LittleEndian>(i.left.i)?;
    w.write_u8(i.left.j)?;
    w.write_all(&i.hash)?;
  }

  // 葉ノードの書き込み
  w.write_u32::<LittleEndian>(e.enode.payload.len() as u32)?;
  w.write_all(&e.enode.payload)?;
  w.write_all(&e.enode.hash)?;

  // エントリ先頭までのオフセットを書き込み
  w.write_u32::<LittleEndian>(w.length() as u32)?;

  // チェックサムの書き込み
  w.write_u64::<LittleEndian>(w.finish())?;

  Ok(w.length() as usize)
}

/// 指定されたカーソルを現在の位置から `distance` バイト前方に移動します。移動先がカーソルの先頭を超える場合は
/// `if_err` をメッセージとしたエラーを発生します。
#[inline]
fn back_to_safety(cursor: &mut dyn Cursor, distance: u32, if_err: &'static str) -> Result<u64> {
  let from = cursor.stream_position()?;
  let to = from - distance as u64;
  if to < STORAGE_IDENTIFIER.len() as u64 + 1 {
    Err(DamagedStorage(format!("{} (cannot move position from {} to {})", if_err, from, to)))
  } else {
    Ok(cursor.seek(io::SeekFrom::Current(-(distance as i64)))?)
  }
}
