use crate::Result;
use crate::checksum::{ChecksumRead, ChecksumWrite};
use crate::error::Error::*;
use crate::file::FileDevice;
use crate::memory::MemoryDevice;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::fs::{File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::{Arc, RwLock};

pub mod file;
pub mod memory;

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
pub trait Storage<S: Serializable> {
  /// 先頭に位置するデータとその位置を返します。
  /// ストレージにまだデータが保存されていない場合は None を返します。
  /// 通常は使用されず、データストアのメンテナンスやデバッグ用に用意しています。
  fn first(&mut self) -> Result<(Option<S>, Position)>;

  /// 起動時に呼び出され、現在のデータと、次のデータの位置を返します。
  /// ストレージにまだデータが保存されていない場合は None を返します。
  fn last(&mut self) -> Result<(Option<S>, Position)>;

  /// 指定された位置にデータの保存します。
  /// 次のデータの位置を返します。
  fn put(&mut self, position: Position, data: &S) -> Result<Position>;

  /// データを読み込むためのカーソルを参照します。
  fn reader(&self) -> Result<Box<dyn Reader<S>>>;
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
  pub fn device(&self) -> &B {
    &self.device
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

impl<B: BlockDevice + 'static, S: Serializable> Storage<S> for BlockStorage<B> {
  fn reader(&self) -> Result<Box<dyn Reader<S>>> {
    let device = self.device.clone_device()?;
    Ok(Box::new(device))
  }

  fn first(&mut self) -> Result<(Option<S>, Position)> {
    let (first, _) = boot(&mut self.device)?;
    Ok(first)
  }

  fn last(&mut self) -> Result<(Option<S>, Position)> {
    let (_, (data, position)) = boot(&mut self.device)?;
    self.position = position;
    Ok((data, position))
  }

  fn put(&mut self, position: Position, data: &S) -> Result<Position> {
    if self.position != position {
      self.position = self.device.seek(SeekFrom::Start(position))?;
    }
    debug_assert_eq!(self.position, position);
    let mut bw = BufWriter::new(&mut self.device);
    let length = write_data(&mut bw, data)?;
    bw.flush()?;
    self.position += length as u64;
    Ok(self.position)
  }
}

pub type FileStorage = BlockStorage<FileDevice>;

/// slate ファイルの先頭に記録される 3 バイトの識別子を表す定数です。値は Unicode でのdeciduous tree 🌲 (U+1F332)
/// に由来します。
pub const STORAGE_IDENTIFIER: [u8; 3] = [0x01u8, 0xF3, 0x33];

/// 識別子に続いて配置される、この実装におけるストレージフォーマットのバージョンです。現在は 1 を使用します。
pub const STORAGE_VERSION: u8 = 1;

/// 使用しようとしているストレージと互換性があるかを確認します。
pub(crate) fn is_version_compatible(version: u8) -> bool {
  version <= STORAGE_VERSION
}

type FirstLast<S> = ((Option<S>, Position), (Option<S>, Position));

fn boot<C, S: Serializable>(cursor: &mut C) -> Result<FirstLast<S>>
where
  C: Write + Read + Seek,
{
  match cursor.seek(SeekFrom::End(0))? {
    0 => {
      // マジックナンバーの書き込み
      cursor.write_all(&STORAGE_IDENTIFIER)?;
      cursor.write_u8(STORAGE_VERSION)?;
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
    }
  }

  let first_position = cursor.stream_position()?;
  let next_position = cursor.seek(SeekFrom::End(0))?;
  if next_position == first_position {
    return Ok(((None, first_position), (None, next_position)));
  }
  let first_entry = {
    cursor.seek(SeekFrom::Start(first_position))?;
    Some(read_data(cursor, first_position)?)
  };

  cursor.seek(SeekFrom::End(0))?;
  let latest_entry = {
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

  Ok(((first_entry, first_position), (latest_entry, next_position)))
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
