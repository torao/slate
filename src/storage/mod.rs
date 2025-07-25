use crate::checksum::HashWrite;
use crate::error::Error;
use crate::error::Error::*;
use crate::{Address, ENode, Entry, Hash, INDEX_SIZE, INode, MAX_PAYLOAD_SIZE, MetaInfo};
use crate::{Index, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayHasher, Key};
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, LockResult, RwLock};

#[cfg(test)]
mod test;

pub type Position = u64;

/// ハッシュツリーのエントリを保存するために抽象化されたストレージです。
pub trait Storage {
  // 起動時に呼び出され、最新のエントリと、次のエントリの位置を返します。
  fn boot(&mut self) -> Result<(Option<Entry>, Position)>;

  // 指定された位置にエントリの保存します。
  // 次のエントリの位置を返します。
  fn put(&mut self, position: Position, entry: &Entry) -> Result<Position>;

  // エントリを読み込むためのカーソルを参照します。
  fn cursor(&self) -> Result<Box<dyn Cursor>>;
}

/// ストレージからエントリを読み込むためのカーソルです。
pub trait Cursor {
  // 指定された位置からエントリを参照して返します。
  fn get(&mut self, position: Position, expected_index: Index) -> Result<Entry>;
}

/// ローカルファイルシステムのパスをストレージとして使用する実装です。
pub struct FileStorage {
  /// 読み出し時にオープンするためのこのファイルのパス。
  path: PathBuf,
  /// 読み出しようにオープンするためのオプション。
  read_options: OpenOptions,
  /// 書き込み専用で、必ずファイルの末尾を指している。
  file: File,
  /// このファイルの長さ
  position: u64,
}

impl FileStorage {
  pub fn new<P: AsRef<Path>>(path: P) -> Result<FileStorage> {
    Self::with_options(
      path,
      File::options().read(true).append(true).create(true).truncate(false).clone(),
      File::options().read(true).write(false).create(false).truncate(false).clone(),
    )
  }

  pub fn with_read_only<P: AsRef<Path>>(path: P) -> Result<FileStorage> {
    Self::with_options(
      path,
      File::options().read(true).write(false).create(false).truncate(false).clone(),
      File::options().read(true).write(false).create(false).truncate(false).clone(),
    )
  }

  pub fn with_options<P: AsRef<Path>>(
    path: P,
    write_options: OpenOptions,
    read_options: OpenOptions,
  ) -> Result<FileStorage> {
    let path = path.as_ref().to_path_buf();
    match write_options.open(&path) {
      Ok(file) => {
        let length = file.metadata()?.len();
        Ok(Self { path, read_options, file, position: length })
      }
      Err(err) => Err(Error::FailedToOpenLocalFile {
        file: path.to_str().map(|s| s.to_string()).unwrap_or(path.to_string_lossy().to_string()),
        message: err.to_string(),
      }),
    }
  }
}

impl Storage for FileStorage {
  fn cursor(&self) -> Result<Box<dyn Cursor>> {
    let file = self.read_options.open(&self.path)?;
    Ok(Box::new(FileCursor::new(file)))
  }

  fn boot(&mut self) -> Result<(Option<Entry>, Position)> {
    let (entry, position) = boot(&mut self.file)?;
    self.position = position;
    Ok((entry, position))
  }

  fn put(&mut self, position: Position, entry: &Entry) -> Result<Position> {
    debug_assert_eq!(self.position, position);
    let length = write_entry(&mut self.file, entry)?;
    self.file.flush()?;
    self.position += length as u64;
    Ok(self.position)
  }
}

struct FileCursor {
  file: File,
}

impl FileCursor {
  pub fn new(file: File) -> Self {
    FileCursor { file }
  }
}

impl Cursor for FileCursor {
  fn get(&mut self, position: Position, expected_index: Index) -> Result<Entry> {
    self.file.seek(SeekFrom::Current(position as i64))?;
    read_entry(&mut self.file, Some(expected_index))
  }
}

/// メモリ上の領域をストレージとして使用する実装です。`drop()` された時点で記録していた内容が消滅するため、テストや
/// 調査での使用を想定しています。
pub struct MemStorage {
  buffer: Arc<RwLock<Vec<u8>>>,
}

impl MemStorage {
  /// 揮発性メモリを使用するストレージを構築します。
  pub fn new() -> MemStorage {
    Self::with(Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024))))
  }

  /// 指定されたアトミック参照カウント/RWロック付きの可変バッファを使用するストレージを構築します。これは調査の目的で
  /// 外部からストレージの内容を参照することを想定しています。
  pub fn with(buffer: Arc<RwLock<Vec<u8>>>) -> MemStorage {
    MemStorage { buffer }
  }
}

impl Default for MemStorage {
  fn default() -> Self {
    Self::new()
  }
}

impl Storage for MemStorage {
  fn boot(&mut self) -> Result<(Option<Entry>, Position)> {
    let mut guard = lock2io(self.buffer.write())?;
    let mut cursor = io::Cursor::new(&mut *guard);
    boot(&mut cursor)
  }
  fn put(&mut self, position: Position, entry: &Entry) -> Result<Position> {
    debug_assert_eq!(lock2io(self.buffer.read())?.len() as Position, position);
    let len = {
      let mut guard = lock2io(self.buffer.write())?;
      let mut cursor = io::Cursor::new(&mut *guard);
      cursor.seek(SeekFrom::End(0))?;
      write_entry(&mut cursor, entry)?
    };
    debug_assert_eq!(lock2io(self.buffer.read())?.len() as Position, position + len as Position);
    Ok(position + len as Position)
  }
  fn cursor(&self) -> Result<Box<dyn Cursor>> {
    Ok(Box::new(MemCursor { buffer: self.buffer.clone() }))
  }
}

struct MemCursor {
  buffer: Arc<RwLock<Vec<u8>>>,
}

impl Cursor for MemCursor {
  fn get(&mut self, position: Position, expected_index: Index) -> Result<Entry> {
    let guard = lock2io(self.buffer.read())?;
    let mut cursor = io::Cursor::new(guard.as_slice());
    cursor.seek(SeekFrom::Start(position))?;
    read_entry_without_check(&mut cursor, position, Some(expected_index))
  }
}

/// `LockResult` を `io::Result` に変換します。
#[inline]
fn lock2io<T>(result: LockResult<T>) -> std::io::Result<T> {
  result.map_err(|err| std::io::Error::other(err.to_string()))
}

/// slate ファイルの先頭に記録される 3 バイトの識別子を表す定数です。値は Unicode でのdeciduous tree 🌲 (U+1F332)
/// に由来します。
pub const STORAGE_IDENTIFIER: [u8; 3] = [0x01u8, 0xF3, 0x33];

/// 識別子に続いて配置される、この実装におけるストレージフォーマットのバージョンです。現在は 1 を使用します。
pub const STORAGE_VERSION: u8 = 1;

/// 使用しようとしているストレージと互換性があるかを確認します。
pub(crate) fn is_version_compatible(version: u8) -> bool {
  version <= STORAGE_VERSION
}

fn boot<C>(cursor: &mut C) -> Result<(Option<Entry>, Position)>
where
  C: Write + Read + Seek,
{
  match cursor.seek(SeekFrom::End(0))? {
    0 => {
      // マジックナンバーの書き込み
      cursor.write_all(&STORAGE_IDENTIFIER)?;
      cursor.write_u8(STORAGE_VERSION)?;
      cursor.flush()?;
    }
    1..=3 => return Err(FileIsNotContentsOfLMTHTree { message: "bad magic number" }),
    _ => {
      // マジックナンバーの確認
      let mut buffer = [0u8; 4];
      cursor.seek(SeekFrom::Start(0))?;
      cursor.read_exact(&mut buffer)?;
      if buffer[..3] != STORAGE_IDENTIFIER[..] {
        return Err(FileIsNotContentsOfLMTHTree { message: "bad magic number" });
      } else if !is_version_compatible(buffer[3]) {
        return Err(IncompatibleVersion(buffer[3] >> 4, buffer[3] & 0x0F));
      }
    }
  }

  let next_position = cursor.seek(SeekFrom::End(0))?;
  let latest_entry = if next_position == 4 {
    None
  } else {
    // 末尾のエントリを読み込み
    back_to_safety(cursor, 4 /* offset */ + 8 /* checksum */, "The first entry is corrupted.")?;
    let offset = cursor.read_u32::<LittleEndian>()?;
    back_to_safety(cursor, offset + 4 /* offset */, "The last entry is corrupted.")?;
    let entry = read_entry(cursor, None)?;
    if cursor.stream_position()? != next_position {
      // 壊れたストレージから読み込んだ offset が、たまたまどこかの正しいエントリ境界を指していた場合、正しく
      // 読み込めるが結果となる位置は末尾と一致しない。
      let msg = "The last entry is corrupted.".to_string();
      return Err(DamagedStorage(msg));
    }

    Some(entry)
  };

  Ok((latest_entry, next_position))
}

/// 指定されたカーソルを現在の位置から `distance` バイト前方に移動します。移動先がカーソルの先頭を超える場合は
/// `if_err` をメッセージとしたエラーを発生します。
#[inline]
fn back_to_safety<R>(cursor: &mut R, distance: u32, if_err: &'static str) -> Result<u64>
where
  R: io::Read + io::Seek,
{
  let from = cursor.stream_position()?;
  if from < STORAGE_IDENTIFIER.len() as u64 + 1 + distance as u64 {
    Err(DamagedStorage(format!("{if_err} (cannot move {distance} bytes backword from the current position {from})")))
  } else {
    Ok(cursor.seek(io::SeekFrom::Current(-(distance as i64)))?)
  }
}

/// HighwayHash でチェックサム用のハッシュ値を生成するためのキー (256-bit 固定値)。
pub(crate) const CHECKSUM_HW64_KEY: [u64; 4] =
  [0xFA5015F2E22BCFC6u64, 0xCE5A4ED9A4025C80, 0x16B9731717F6315E, 0x0F34D06AE93BD8E9];

/// 指定されたカーソルの現在の位置からエントリを読み込みます。
/// 正常終了時のカーソルは次のエントリを指しています。
fn read_entry<R>(r: &mut R, expected_index: Option<Index>) -> Result<Entry>
where
  R: io::Read + io::Seek,
{
  use crate::checksum::HashRead;
  use highway::{HighwayHasher, Key};

  let position = r.stream_position()?;
  let mut hasher = HighwayHasher::new(Key(CHECKSUM_HW64_KEY));
  let mut r = HashRead::new(r, &mut hasher);
  let entry = read_entry_without_check(&mut r, position, expected_index)?;

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
    return Err(ChecksumVerificationFailed { at: position, length, expected: trailer_checksum, actual: checksum });
  }

  Ok(entry)
}

/// 指定されたカーソルの現在の位置からエントリを読み込みます。トレイラーの offset と checksum は読み込まれない
/// ため、正常終了時のカーソルは offset の位置を指しています。
fn read_entry_without_check<R>(r: &mut R, position: Position, expected_index: Option<Index>) -> Result<Entry>
where
  R: io::Read,
{
  let mut hash = [0u8; Hash::SIZE];

  // 中間ノードの読み込み
  let inodes = read_inodes(r, position)?;
  let i = inodes.first().map(|inode| inode.meta.address.i).unwrap_or(1);
  if expected_index.is_some_and(|expected| i != expected) {
    return Err(Error::IncorrectNodeBoundary { at: position });
  }

  // 葉ノードの読み込み
  let payload_size = r.read_u32::<LittleEndian>()? & MAX_PAYLOAD_SIZE as u32;
  let mut payload = vec![0u8; payload_size as usize];
  r.read_exact(&mut payload)?;
  r.read_exact(&mut hash)?;
  let enode = ENode { meta: MetaInfo::new(Address::new(i, 0, position), Hash::new(hash)), payload: Arc::new(payload) };

  Ok(Entry::new(enode, inodes))
}

/// 指定されたカーソルの現在の位置をエントリの先頭としてすべての `INode` を読み込みます。正常終了した場合、カーソル
/// 位置は最後の `INode` を読み込んだ直後を指しています。
fn read_inodes<R>(r: &mut R, position: Position) -> Result<Vec<INode>>
where
  R: io::Read,
{
  let mut hash = [0u8; Hash::SIZE];
  let i = r.read_u64::<LittleEndian>()?;
  let inode_count = r.read_u8()? as usize;
  let mut right_j = 0u8;
  let mut inodes = Vec::<INode>::with_capacity(inode_count);
  for _ in 0..inode_count {
    let j = (r.read_u8()? & (INDEX_SIZE - 1)) + 1; // 下位 6-bit のみを使用
    let left_position = r.read_u64::<LittleEndian>()?;
    let left_i = r.read_u64::<LittleEndian>()?;
    let left_j = r.read_u8()?;
    r.read_exact(&mut hash)?;
    inodes.push(INode {
      meta: MetaInfo::new(Address::new(i, j, position), Hash::new(hash)),
      left: Address::new(left_i, left_j, left_position),
      right: Address::new(i, right_j, position),
    });
    right_j = j;
  }
  Ok(inodes)
}

/// 指定されたカーソルにエントリを書き込みます。
/// このエントリに対して書き込みが行われた長さを返します。
pub fn write_entry<W: Write>(writer: &mut W, e: &Entry) -> Result<usize> {
  debug_assert!(e.enode.payload.len() <= MAX_PAYLOAD_SIZE);
  debug_assert!(e.inodes.len() <= 0xFF);

  let mut buffer = Vec::with_capacity(1024);
  let mut hasher = HighwayHasher::new(Key(CHECKSUM_HW64_KEY));
  let mut w = HashWrite::new(&mut buffer, &mut hasher);

  // 中間ノードの書き込み
  w.write_u64::<LittleEndian>(e.enode.meta.address.i)?;
  w.write_u8(e.inodes.len() as u8)?;
  for i in &e.inodes {
    debug_assert_eq!((i.meta.address.j - 1) & (INDEX_SIZE - 1), i.meta.address.j - 1);
    debug_assert_eq!(Hash::SIZE, i.meta.hash.value.len());
    w.write_u8((i.meta.address.j - 1) & (INDEX_SIZE - 1))?; // 下位 6-bit のみ保存
    w.write_u64::<LittleEndian>(i.left.position)?;
    w.write_u64::<LittleEndian>(i.left.i)?;
    w.write_u8(i.left.j)?;
    w.write_all(&i.meta.hash.value)?;
  }

  // 葉ノードの書き込み
  w.write_u32::<LittleEndian>(e.enode.payload.len() as u32)?;
  w.write_all(&e.enode.payload)?;
  w.write_all(&e.enode.meta.hash.value)?;

  // エントリ先頭までのオフセットを書き込み
  w.write_u32::<LittleEndian>(w.length() as u32)?;

  // チェックサムの書き込み
  w.write_u64::<LittleEndian>(w.finish())?;
  w.flush()?;

  writer.write_all(&buffer)?;
  writer.flush()?;
  Ok(buffer.len())
}
