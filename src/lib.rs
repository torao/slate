use std::fs::*;
use std::hash::Hasher;
use std::io::{Cursor, Read, Seek, SeekFrom, Write};
use std::path::Path;

use byteorder::{BigEndian, LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, HighwayHash, Key};

use crate::error::Detail::{
  ChecksumVerificationFailed, FileIsNotContentsOfLSHTree, IncorrectEntryHeadOffset, TooLargePayload,
};

#[cfg(test)]
mod test;

pub mod error;

pub type Result<T> = std::result::Result<T, error::Detail>;

/// 抽象化されたストレージ。Read, Write に加えて Seek の実装。
pub trait Storage: Seek + Read + Write {
  fn truncate(&mut self) -> Result<()>;
}

impl Storage for File {
  fn truncate(&mut self) -> Result<()> {
    self.set_len(0)?;
    Ok(())
  }
}

pub type MemStorage = Cursor<Vec<u8>>;

impl Storage for MemStorage {
  fn truncate(&mut self) -> Result<()> {
    self.get_mut().truncate(0);
    Ok(())
  }
}

struct HashWrite<'i> {
  output: &'i mut dyn Storage,
  hasher: &'i mut dyn Hasher,
  length: usize,
}

impl<'i> Write for HashWrite<'i> {
  fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
    let result = self.output.write(buf);
    self.hasher.write(buf);
    self.length += buf.len();
    result
  }

  fn flush(&mut self) -> std::io::Result<()> {
    self.output.flush()
  }
}

struct HashRead<'i> {
  input: &'i mut dyn Storage,
  hasher: &'i mut dyn Hasher,
  length: u64,
}

impl<'i> Read for HashRead<'i> {
  fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
    let size = self.input.read(buf)?;
    self.hasher.write(&buf[..size]);
    self.length += size as u64;
    Ok(size)
  }
}

const HIGHWAYHASH64_KEY: [u64; 4] = [0u64, 1, 2, 3];

pub const HASH_SIZE: usize = 32;

pub const MAX_PAYLOAD_SIZE: usize = 0x7FFFFFFF;

pub type Hash = [u8; HASH_SIZE];

#[derive(PartialEq, Eq, Debug)]
enum Node {
  Inner { left: u64, hash: Hash },
  External { index: u64, payload: Box<Vec<u8>>, hash: Hash },
}

impl Node {
  /// 指定されたストレージにノードの情報を書き込みます。
  pub fn write_to(&self, storage: &mut dyn Storage) -> Result<u32> {
    let mut hasher = HighwayBuilder::new(Key(HIGHWAYHASH64_KEY));
    let mut output = HashWrite { output: storage, hasher: &mut hasher, length: 0 };
    match self {
      Node::Inner { left, hash } => {
        output.write_u8(0)?;
        output.write_u64::<LittleEndian>(*left)?;
        output.write_all(hash)?;
      }
      Node::External { index, payload, hash } => {
        if payload.len() > MAX_PAYLOAD_SIZE {
          return Err(TooLargePayload { size: payload.len() });
        }
        output.write_u8(1)?;
        output.write_u64::<LittleEndian>(*index)?;
        output.write_u32::<LittleEndian>(payload.len() as u32)?;
        output.write_all(payload)?;
        output.write_all(hash)?;
      }
    };

    // トレイラーの出力
    output.write_u32::<LittleEndian>(output.length as u32)?;
    let length = output.length;

    // チェックサムの出力 (output のスコープは終わっている)
    let checksum = hasher.finalize64();
    storage.write_u64::<LittleEndian>(checksum)?;
    Ok(length as u32 + 8)
  }

  /// 指定されたストレージからこの位置のノードを読み込みます。
  /// 正常終了時のストレージは次のノードの先頭を指しています。
  pub fn read_from(storage: &mut dyn Storage) -> Result<Node> {
    let mut hasher = HighwayBuilder::new(Key(HIGHWAYHASH64_KEY));
    let mut input = HashRead { input: storage, hasher: &mut hasher, length: 0 };

    let status = input.read_u8()?;
    let mut hash = [0u8; HASH_SIZE];
    let node = if (status & 1) == 0 {
      let left = input.read_u64::<LittleEndian>()?;
      input.read_exact(&mut hash)?;
      Node::Inner { left, hash }
    } else {
      let index = input.read_u64::<LittleEndian>()?;
      let length = input.read_u32::<LittleEndian>()?;
      let mut payload = Vec::<u8>::with_capacity(length as usize);
      unsafe {
        payload.set_len(length as usize);
      }
      input.read_exact(&mut payload)?;
      input.read_exact(&mut hash)?;
      Node::External { index, payload: Box::new(payload), hash }
    };

    // エントリ先頭へのオフセットを検証
    let size = input.length;
    let offset = input.read_u32::<LittleEndian>()?;
    if size != offset as u64 {
      return Err(IncorrectEntryHeadOffset { expected: size, actual: offset });
    }

    // チェックサムの検証
    let checksum = storage.read_u64::<LittleEndian>()?;
    let actual = hasher.finalize64();
    if checksum != actual {
      let pos = storage.stream_position()?;
      let length = offset + 4 + 8;
      let at = pos - length as u64;
      return Err(ChecksumVerificationFailed { at, length, expected: checksum, actual });
    }

    Ok(node)
  }
}

/// LSHTree ファイルの先頭に記録される識別のためのマジックナンバー。
const MAGIC_NUMBER: u32 =
  (('L' as u32) << 24) | (('S' as u32) << 16) | (('H' as u32) << 8) | ('T' as u32);

pub struct LSHTree {
  storage: Box<dyn Storage>,
}

impl LSHTree {
  /// 指定されたストレージをデータベースとして使用します。
  pub fn new(storage: Box<dyn Storage>) -> Result<Self> {
    let mut db = LSHTree { storage };
    let length = db.storage.seek(SeekFrom::End(0))?;
    match length {
      0 => db.init_magic_number()?,
      1..=4 => return Err(FileIsNotContentsOfLSHTree { message: "bad magic number" }),
      _ => db.check_magic_number()?,
    }
    Ok(db)
  }

  /// 指定されたパスに存在するデータベースファイルをオープンします。ファイルが存在しない場合は新しく作成します。
  /// より詳細なオプションを使用する場合は `OpenOptions` ファイルを開き `new()` を使用してください。
  pub fn open(path: impl AsRef<Path>) -> Result<Self> {
    let file = OpenOptions::new().write(true).create(true).open(path)?;
    Self::new(Box::new(file))
  }

  /// データベースのマジックナンバーを確認します。
  fn check_magic_number(&mut self) -> Result<()> {
    self.storage.seek(SeekFrom::Start(0))?;
    let magic = self.storage.read_u32::<BigEndian>()?;
    if magic != MAGIC_NUMBER {
      return Err(FileIsNotContentsOfLSHTree { message: "bad magic number" });
    }
    Ok(())
  }

  /// データベースのマジックナンバーを初期化します。
  fn init_magic_number(&mut self) -> Result<()> {
    self.storage.truncate()?;
    self.storage.seek(SeekFrom::Start(0))?;
    self.storage.write_u32::<BigEndian>(MAGIC_NUMBER)?;
    Ok(())
  }
}
