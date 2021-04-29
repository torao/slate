use std::any::Any;
use std::io::Seek;
use std::io::{Cursor, ErrorKind, SeekFrom, Write};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, HighwayHash, Key};
use mt19937::MT19937;
use rand::RngCore;

use crate::error::Detail::*;
use crate::test::GarblingField::*;
use crate::{MemStorage, Node, Result, Storage, HASH_SIZE, HIGHWAYHASH64_KEY};

#[test]
fn node_serialization() -> Result<()> {
  for node in representative_nodes() {
    let mut storage: MemStorage = Cursor::new(Vec::new());
    let write_length = node.write_to(&mut storage)?;
    let storage_length = storage.seek(SeekFrom::End(0))?;
    println!("write {} bytes, data size: {} bytes", write_length, storage_length);
    assert_eq!(write_length as u64, storage_length);
    storage.set_position(0);
    let expected = node;
    let actual = Node::read_from(&mut storage).unwrap();
    assert_eq!(expected.type_id(), actual.type_id());
    match (expected, actual) {
      (Node::Inner { left: l1, hash: h1 }, Node::Inner { left: l2, hash: h2 }) => {
        let length = 1 + 8 + HASH_SIZE + 4 + 8;
        assert_eq!(length, write_length as usize);
        assert_eq!(length, storage_length as usize);
        assert_eq!(l1, l2);
        assert_eq!(h1, h2);
      }
      (
        Node::External { index: i1, payload: p1, hash: h1 },
        Node::External { index: i2, payload: p2, hash: h2 },
      ) => {
        let length = 1 + 8 + 4 + p1.len() + HASH_SIZE + 4 + 8;
        assert_eq!(length, write_length as usize);
        assert_eq!(length, storage_length as usize);
        assert_eq!(i1, i2);
        assert_eq!(p1, p2);
        assert_eq!(h1, h2);
      }
      _ => panic!("the recovered node was different"),
    }

    // チェックサムの確認
    let expected = expected_checksum(&mut storage)?;
    let binary = storage.get_ref();
    let binary = &binary[0..write_length as usize - 8];
    println!("{}: {:X?}", binary.len(), binary);
    let actual = checksum(binary);
    assert_eq!(expected, actual);
  }
  Ok(())
}

/// シリアライズしたバイナリの任意の位置のバイトを破損させて、破損位置のフィールドに対して想定するエラーが発生することを
/// 検証します。
#[test]
fn garbled_at_any_position() -> Result<()> {
  for node in representative_nodes() {
    let mut storage: MemStorage = Cursor::new(Vec::new());
    let write_length = node.write_to(&mut storage)?;
    let storage_length = storage.seek(SeekFrom::End(0))?;
    assert_eq!(write_length as u64, storage_length);
    storage.seek(SeekFrom::Start(0))?;
    assert_eq!(node, Node::read_from(&mut storage)?);

    for position in 0..storage_length {
      let field = get_garbling_field(&mut storage, position)?;

      // データ破損の設定
      storage.seek(SeekFrom::Start(position))?;
      let correct = storage.read_u8()?;
      storage.seek(SeekFrom::Current(-1))?;
      storage.write_u8(!correct)?;

      // データ破損のフィールドに対して Node::read_from() で発生する可能性のあるすべてのエラーを検証
      storage.seek(SeekFrom::Start(0))?;
      match Node::read_from(&mut storage).unwrap_err() {
        ChecksumVerificationFailed { at, length, expected, actual } => {
          assert_ne!(expected, actual);
          assert_eq!(0, at);
          assert_eq!(write_length, length);
          assert_eq!(expected_checksum(&mut storage)?, expected);
          assert_eq!(actual_checksum(&mut storage)?, actual);
        }
        IncorrectEntryHeadOffset { expected, actual } if [Status, HeadOffset].contains(&field) => {
          assert_ne!(expected, actual as u64);
          if field != GarblingField::Status {
            assert_eq!(write_length as u64 - 4 - 8, expected, "{}", position);
          }
        }
        Io { source }
          if source.kind() == ErrorKind::UnexpectedEof && [Status, ELength].contains(&field) =>
        {
          // noop
        }
        unexpected => {
          panic!("It's not expected that corruption of the {:?} field (position {}) will result in an {:?}.", &field, position, unexpected);
        }
      }

      // 終了処理
      storage.seek(SeekFrom::Start(position))?;
      storage.write_u8(correct)?;
    }
  }
  Ok(())
}

/// ストレージに記録されているチェックサムを参照。
fn expected_checksum(storage: &mut dyn Storage) -> Result<u64> {
  let content = content_size(storage)?;
  storage.seek(SeekFrom::Start(1 + content + 4))?;
  Ok(storage.read_u64::<LittleEndian>()?)
}

/// ストレージの実際のチェックサムを参照。
fn actual_checksum(storage: &mut dyn Storage) -> Result<u64> {
  let length = 1 + content_size(storage)? as usize + 4;
  let mut buffer = Vec::<u8>::with_capacity(length);
  unsafe { buffer.set_len(length) }
  storage.seek(SeekFrom::Start(0))?;
  storage.read_exact(buffer.as_mut())?;
  Ok(checksum(&buffer))
}

/// ノードタイプを参照。
fn get_node_type(storage: &mut dyn Storage) -> Result<u8> {
  storage.seek(SeekFrom::Start(0))?;
  Ok(storage.read_u8()? & 1)
}

/// ノードの内容部分のサイズを参照。
fn content_size(storage: &mut dyn Storage) -> Result<u64> {
  if get_node_type(storage)? == 0 {
    Ok(8 + HASH_SIZE as u64)
  } else {
    storage.seek(SeekFrom::Start(1 + 8))?;
    Ok(8 + 4 + storage.read_u32::<LittleEndian>()? as u64 + HASH_SIZE as u64)
  }
}

/// 指定されたバイナリデータに対するチェックサムを算出。
fn checksum(bytes: &[u8]) -> u64 {
  let mut hasher = HighwayBuilder::new(Key(HIGHWAYHASH64_KEY));
  hasher.write_all(bytes).unwrap();
  hasher.finalize64()
}

#[derive(PartialEq, Debug)]
enum GarblingField {
  Status,
  ILeft,
  IHash,
  EIndex,
  ELength,
  EPayload,
  EHash,
  HeadOffset,
  Checksum,
}

fn get_garbling_field(storage: &mut dyn Storage, pos: u64) -> Result<GarblingField> {
  let content = content_size(storage)?;
  Ok(if pos == 0 {
    GarblingField::Status
  } else if pos >= 1 + content {
    if pos < 1 + content + 4 {
      GarblingField::HeadOffset
    } else if pos < 1 + content + 4 + 8 {
      GarblingField::Checksum
    } else {
      panic!()
    }
  } else if get_node_type(storage)? == 0 {
    if pos < 1 + 8 {
      GarblingField::ILeft
    } else if pos < 1 + 8 + HASH_SIZE as u64 {
      GarblingField::IHash
    } else {
      unreachable!()
    }
  } else {
    if pos < 1 + 8 {
      GarblingField::EIndex
    } else if pos < 1 + 8 + 4 {
      GarblingField::ELength
    } else {
      storage.seek(SeekFrom::Start(1 + 8))?;
      let length = storage.read_u32::<LittleEndian>()?;
      if pos < 1 + 8 + 4 + length as u64 {
        GarblingField::EPayload
      } else if pos < 1 + 8 + 4 + length as u64 + HASH_SIZE as u64 {
        GarblingField::EHash
      } else {
        unreachable!()
      }
    }
  })
}

// TODO ストレージ末尾の 4 バイトの指す位置がたまたま最後より前の要素だった場合に、その要素を最後の要素とみなして後続が上書きされないように検証すること。

/// テストに使用する代表的なノードの一覧を参照。
fn representative_nodes() -> Vec<Node> {
  vec![
    Node::Inner { left: 100u64, hash: random_hash(62288902) },
    Node::External {
      index: 0,
      payload: random_payload(100, 40808231),
      hash: random_hash(4322844765),
    },
  ]
}

fn random_payload(length: usize, s: u64) -> Box<Vec<u8>> {
  let mut seed = [0u32; 2];
  seed[0] = ((s >> 0) & 0xFFFFFFFF) as u32;
  seed[1] = ((s >> 8) & 0xFFFFFFFF) as u32;
  let mut rand = MT19937::new_with_slice_seed(&seed);
  let mut bytes = Vec::<u8>::with_capacity(length);
  unsafe {
    bytes.set_len(length);
  }
  rand.fill_bytes(&mut bytes);
  Box::new(bytes)
}

fn random_hash(s: u64) -> [u8; HASH_SIZE] {
  let mut seed = [0u32; 2];
  seed[0] = ((s >> 0) & 0xFFFFFFFF) as u32;
  seed[1] = ((s >> 8) & 0xFFFFFFFF) as u32;
  let mut rand = MT19937::new_with_slice_seed(&seed);
  let mut hash = [0u8; HASH_SIZE];
  rand.fill_bytes(&mut hash);
  hash
}
