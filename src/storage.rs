use crate::Result;
use crate::checksum::{ChecksumRead, ChecksumWrite};
use crate::error::Error;
use crate::error::Error::*;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::fs::{File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Cursor, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, LockResult, RwLock};

#[cfg(feature = "rocksdb")]
pub mod rocksdb;

#[cfg(test)]
mod test;

pub type Position = u64;

pub trait Serializable: Sized {
  fn write<W: Write>(&self, w: &mut W) -> Result<usize>;
  fn read<R: Read + Seek>(r: &mut R, position: Position) -> Result<Self>;
}

/// ハッシュツリーのデータを保存するために抽象化されたストレージです。
pub trait Storage<S: Serializable, const M: usize> {
  /// 起動時に呼び出され、現在のデータと、次のデータの位置を返します。
  /// ストレージにまだデータが保存されていない場合は None を返します。
  fn boot(&mut self) -> Result<(Option<S>, Position, Vec<u8>)>;

  /// 指定された位置にデータの保存します。
  /// 次のデータの位置を返します。
  fn put(&mut self, position: Position, data: &S) -> Result<Position>;

  /// データを読み込むためのカーソルを参照します。
  fn reader(&self) -> Result<Box<dyn Reader<S>>>;

  /// メタデータを書き込みます。
  fn flush_metadata(&mut self, metadata: &[u8]) -> Result<()>;
}

/// ストレージからデータを読み込むためのカーソルです。
pub trait Reader<S: Serializable> {
  // 指定された位置からデータを読み出して返します。
  fn read(&mut self, position: Position) -> Result<S>;
}

// ----------------------------------------

pub trait BlockDevice: Read + Write + Seek {
  fn clone_device(&self) -> Result<Self>
  where
    Self: std::marker::Sized;
}

impl<B: BlockDevice, S: Serializable> Reader<S> for B {
  fn read(&mut self, position: Position) -> Result<S> {
    self.seek(SeekFrom::Start(position))?;

    let mut br = BufReader::new(self);
    read_data(&mut br, position)
  }
}

pub struct BlockStorage<B: BlockDevice> {
  device: B,
  position: u64,
}

impl<B: BlockDevice> BlockStorage<B> {
  pub fn new(device: B) -> Self {
    let position = 0;
    BlockStorage { device, position }
  }
}

impl BlockStorage<MemoryDevice> {
  pub fn memory() -> Self {
    let device = MemoryDevice::new();
    BlockStorage::new(device)
  }

  pub fn from_buffer(buffer: Arc<RwLock<Vec<u8>>>, read_only: bool) -> Self {
    let device = MemoryDevice::with(buffer, read_only);
    BlockStorage::new(device)
  }
}

impl BlockStorage<FileDevice> {
  pub fn from_file<P: AsRef<Path>>(path: P, read_only: bool) -> Result<BlockStorage<FileDevice>> {
    let base = File::options().read(true).clone();
    let write_options = base.clone().write(!read_only).create(!read_only).truncate(false).clone();
    let read_options = base.clone().read(true).write(false).create(false).truncate(false).clone();
    Self::from_file_with_options(path, write_options, read_options)
  }

  pub fn from_file_with_options<P: AsRef<Path>>(
    path: P,
    write_options: OpenOptions,
    read_options: OpenOptions,
  ) -> Result<BlockStorage<FileDevice>> {
    let device = FileDevice::with_options(path, write_options, read_options)?;
    Ok(BlockStorage::new(device))
  }
}

impl<B: BlockDevice + 'static, S: Serializable, const M: usize> Storage<S, M> for BlockStorage<B> {
  fn reader(&self) -> Result<Box<dyn Reader<S>>> {
    let device = self.device.clone_device()?;
    Ok(Box::new(device))
  }

  fn boot(&mut self) -> Result<(Option<S>, Position, Vec<u8>)> {
    let (data, position, metadata) = boot(&mut self.device, M)?;
    self.position = position;
    Ok((data, position, metadata))
  }

  fn put(&mut self, position: Position, data: &S) -> Result<Position> {
    debug_assert_eq!(self.position, position);
    let mut bw = BufWriter::new(&mut self.device);
    let length = write_data(&mut bw, data)?;
    bw.flush()?;
    self.position += length as u64;
    Ok(self.position)
  }

  fn flush_metadata(&mut self, metadata: &[u8]) -> Result<()> {
    assert_eq!(M, metadata.len());
    self.device.seek(SeekFrom::Start(4))?;
    self.device.write_all(metadata)?;
    self.device.flush()?;
    self.device.seek(SeekFrom::End(0))?;
    Ok(())
  }
}

/// ローカルファイルをストレージとして使用する実装です。
pub struct FileDevice {
  /// 読み出し時にオープンするためのこのファイルのパス。
  path: PathBuf,
  /// 読み出し用にオープンするためのオプション。
  read_options: OpenOptions,
  /// 書き込み専用で、必ずファイルの末尾を指している。
  file: File,
}

impl FileDevice {
  pub fn new<P: AsRef<Path>>(path: P) -> Result<FileDevice> {
    Self::with_options(
      path,
      File::options().read(true).append(true).create(true).truncate(false).clone(),
      File::options().read(true).write(false).create(false).truncate(false).clone(),
    )
  }

  pub fn read_only<P: AsRef<Path>>(path: P) -> Result<FileDevice> {
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
  ) -> Result<FileDevice> {
    let path = path.as_ref().to_path_buf();
    write_options.open(&path).map(|file| Self { path: path.clone(), read_options, file }).map_err(|err| {
      Error::FailedToOpenLocalFile {
        file: path.to_str().map(|s| s.to_string()).unwrap_or(path.to_string_lossy().to_string()),
        message: err.to_string(),
      }
    })
  }
}

impl BlockDevice for FileDevice {
  fn clone_device(&self) -> Result<Self>
  where
    Self: std::marker::Sized,
  {
    let file = self.read_options.open(&self.path)?;
    Ok(Self { path: self.path.clone(), read_options: self.read_options.clone(), file })
  }
}

impl Read for FileDevice {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    self.file.read(buf)
  }
}

impl Write for FileDevice {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    self.file.write(buf)
  }

  fn flush(&mut self) -> io::Result<()> {
    self.file.flush()
  }
}

impl Seek for FileDevice {
  fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
    self.file.seek(pos)
  }
}

pub type FileStorage = BlockStorage<FileDevice>;

/// メモリ上の領域をストレージとして使用する実装です。`drop()` された時点で記録していた内容が消滅するため、テストや
/// 調査での使用を想定しています。
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

/// slate ファイルの先頭に記録される 3 バイトの識別子を表す定数です。値は Unicode でのdeciduous tree 🌲 (U+1F332)
/// に由来します。
pub const STORAGE_IDENTIFIER: [u8; 3] = [0x01u8, 0xF3, 0x33];

/// 識別子に続いて配置される、この実装におけるストレージフォーマットのバージョンです。現在は 1 を使用します。
pub const STORAGE_VERSION: u8 = 1;

/// 使用しようとしているストレージと互換性があるかを確認します。
pub(crate) fn is_version_compatible(version: u8) -> bool {
  version <= STORAGE_VERSION
}

fn boot<C, S: Serializable>(cursor: &mut C, meta_data_size: usize) -> Result<(Option<S>, Position, Vec<u8>)>
where
  C: Write + Read + Seek,
{
  let mut meta_data = vec![0u8; meta_data_size];
  match cursor.seek(SeekFrom::End(0))? {
    0 => {
      // マジックナンバーの書き込み
      cursor.write_all(&STORAGE_IDENTIFIER)?;
      cursor.write_u8(STORAGE_VERSION)?;
      // メタデータの書き込み
      cursor.write_all(&meta_data)?;
      cursor.flush()?;
    }
    1..=3 => return Err(StorageisNotForSlate { message: "bad magic number" }),
    _ => {
      // マジックナンバーの確認
      let mut buffer = [0u8; 4];
      cursor.seek(SeekFrom::Start(0))?;
      cursor.read_exact(&mut buffer)?;
      if buffer[..3] != STORAGE_IDENTIFIER[..] {
        return Err(StorageisNotForSlate { message: "bad magic number" });
      } else if !is_version_compatible(buffer[3]) {
        return Err(IncompatibleVersion(buffer[3] >> 4, buffer[3] & 0x0F));
      }
      // メタデータの読み込み
      cursor.read_exact(&mut meta_data)?;
    }
  }

  let next_position = cursor.seek(SeekFrom::End(0))?;
  let latest_entry = if next_position == 4 {
    None
  } else {
    // 末尾のデータを読み込み
    back_to_safety(cursor, 4 /* offset */ + 8 /* checksum */, "The first data is corrupted.")?;
    let offset = cursor.read_u32::<LittleEndian>()?;
    back_to_safety(cursor, offset + 4 /* offset */, "The last data is corrupted.")?;
    let position = cursor.stream_position()?;
    let data = read_data(cursor, position)?;
    if cursor.stream_position()? != next_position {
      // 壊れたストレージから読み込んだ offset が、たまたまどこかの正しいデータ境界を指していた場合、正しく
      // 読み込めるが結果となる位置は末尾と一致しない。
      let msg = format!(
        "The last data is corrupted; The data read from the position {} pointed to by the meta information {} was not the end.",
        position,
        next_position - (u32::BITS + u64::BITS) as u64 / 8
      );
      return Err(DamagedStorage(msg));
    }

    Some(data)
  };

  Ok((latest_entry, next_position, meta_data.to_vec()))
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

/// 指定されたカーソルにデータを書き込みます。
/// このデータに対して書き込みが行われた長さを返します。
fn write_data<W: Write + Seek, S: Serializable>(writer: &mut W, e: &S) -> Result<usize> {
  let mut w = ChecksumWrite::new(writer);
  let mut length = e.write(&mut w)?;
  length += w.write_delimiter()?;
  Ok(length)
}

fn read_data<R: Read + Seek, S: Serializable>(reader: &mut R, position: Position) -> Result<S> {
  let mut r = ChecksumRead::new(reader);
  let data = S::read(&mut r, position)?;
  r.check_delimiter()?;
  Ok(data)
}
