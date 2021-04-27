use std::fs::*;
use std::io::{Cursor, Read, Seek, SeekFrom, Write};
use std::path::Path;

use byteorder::{BigEndian, LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, HighwayHash, Key};
use protobuf::Message;

use crate::error::Detail::{
  ChecksumVerificationFailed, FileIsNotContentsOfLSHTree, UnknownNodeClass,
};

mod proto;

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

const HIGHWAYHASH64_KEY: [u64; 4] = [0u64, 1, 2, 3];

pub type Hash = [u8; 32];

#[derive(Debug)]
enum Node {
  Intermediate(proto::Intermediate),
  Leaf(proto::Leaf),
}

impl Node {
  /// 指定されたストレージにノードの情報を書き込みます。
  pub fn write_to(&self, storage: &mut dyn Storage) -> Result<usize> {
    // ノードの種類によって識別子とバイナリデータを取得
    let (identifier, payload) = match self {
      Node::Intermediate(node) => ('I', node.write_to_bytes()?),
      Node::Leaf(leaf) => ('L', leaf.write_to_bytes()?),
    };

    // ノードの情報を書き込み
    storage.write_u8(identifier as u8)?;
    storage.write_u32::<LittleEndian>(payload.len() as u32)?;
    storage.write_u64::<LittleEndian>(Self::checksum(&payload))?;
    storage.write_all(&payload)?;
    storage.write_u32::<LittleEndian>(payload.len() as u32)?;
    Ok(1 + 4 + 8 + payload.len() + 4)
  }

  /// 指定されたストレージからこの位置のノードを読み込みます。
  /// 正常終了時のストレージは次のノードの先頭を指しています。
  fn read_from(storage: &mut dyn Storage) -> Result<Node> {
    // フィールドの読み込み
    let node_type = storage.read_u8()?;
    let length = storage.read_u32::<LittleEndian>()?;
    let checksum = storage.read_u64::<LittleEndian>()?;
    let mut payload = Vec::<u8>::with_capacity(length as usize);
    unsafe {
      payload.set_len(length as usize);
    }
    let payload = payload.as_mut();
    storage.read_exact(payload)?;
    let _ = storage.read_u32::<LittleEndian>()?;

    // バイナリデータのチェックサムを検証
    if checksum != Self::checksum(payload) {
      let at = storage.stream_position()? - 1 - 4 - 8 - payload.len() as u64 - 4;
      let length = payload.len();
      return Err(ChecksumVerificationFailed {
        at,
        length,
        expected: checksum,
        actual: Self::checksum(payload),
      });
    }

    // ノードの復元
    let node = match node_type as char {
      'I' => Node::Intermediate(proto::Intermediate::parse_from_bytes(payload)?),
      'L' => Node::Leaf(proto::Leaf::parse_from_bytes(payload)?),
      _ => {
        let at = storage.stream_position()? - 1 - 4 - 8 - payload.len() as u64 - 4;
        return Err(UnknownNodeClass { at, node_type: node_type as u8 });
      }
    };
    Ok(node)
  }

  /// 64-bit のチェックサムを算出します。
  fn checksum(value: &[u8]) -> u64 {
    HighwayBuilder::new(Key(HIGHWAYHASH64_KEY)).hash64(value)
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
