use std::io::Seek;
use std::io::{Cursor, ErrorKind, SeekFrom};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::error::Detail::{ChecksumVerificationFailed, Io, UnknownNodeClass};
use crate::proto::{Intermediate, Leaf};
use crate::{MemStorage, Node, Result, Storage};

#[test]
fn node_serialization() -> Result<()> {
  for node in representative_nodes() {
    let mut storage: MemStorage = Cursor::new(Vec::new());
    let write_length = node.write_to(&mut storage)?;
    let storage_length = storage.seek(SeekFrom::End(0))?;
    println!("write {} bytes, data size: {} bytes", write_length, storage_length);
    storage.set_position(0);
    match (node, Node::read_from(&mut storage).unwrap()) {
      (Node::Intermediate(expected), Node::Intermediate(actual)) => {
        assert_eq!(32, write_length);
        assert_eq!(32, storage_length);
        assert_eq!(expected, actual);
        assert_eq!(expected.hash, actual.hash);
        assert_eq!(expected.left_node, actual.left_node);
        assert_eq!(expected.right_node, actual.right_node);
      }
      (Node::Leaf(expected), Node::Leaf(actual)) => {
        assert_eq!(39, write_length);
        assert_eq!(39, storage_length);
        assert_eq!(expected, actual);
        assert_eq!(expected.hash, actual.hash);
        assert_eq!(expected.payload, actual.payload);
      }
      _ => panic!("the recovered node was different"),
    }
  }
  Ok(())
}

#[test]
fn element_corruption() -> Result<()> {
  for node in representative_nodes() {
    let mut storage: MemStorage = Cursor::new(Vec::new());
    let write_length = node.write_to(&mut storage)?;
    let storage_length = storage.seek(SeekFrom::End(0))?;
    assert_eq!(write_length as u64, storage_length);

    // タイプ識別子の破損
    let correct = set_type(&mut storage, 'X' as u8)?;
    assert_eq!(
      format!("{:?}", UnknownNodeClass { at: 0, node_type: 'X' as u8 }),
      format!("{:?}", Node::read_from(&mut storage).unwrap_err())
    );
    set_type(&mut storage, correct)?;

    // ペイロード長破損 (EOF超過)
    let correct = set_length(&mut storage, 99999)?;
    if let Io { source: err } = Node::read_from(&mut storage).unwrap_err() {
      assert_eq!(ErrorKind::UnexpectedEof, err.kind());
    } else {
      panic!();
    }
    set_length(&mut storage, correct)?;

    // ペイロード長破損 (実際より短い)
    let correct = set_length(&mut storage, 3)?;
    let checksum_expected = get_checksum(&mut storage)?;
    let checksum_actual = Node::checksum(&(get_payload(&mut storage)?));
    assert_eq!(
      format!(
        "{:?}",
        ChecksumVerificationFailed {
          at: 0,
          length: 3,
          expected: checksum_expected,
          actual: checksum_actual
        }
      ),
      format!("{:?}", Node::read_from(&mut storage).unwrap_err())
    );
    set_length(&mut storage, correct)?;

    // チェックサムの破損
    let checksum_expected = 123456;
    let correct = set_checksum(&mut storage, checksum_expected)?;
    let checksum_actual = correct;
    let length = get_length(&mut storage)? as usize;
    assert_eq!(
      format!(
        "{:?}",
        ChecksumVerificationFailed {
          at: 0,
          length,
          expected: checksum_expected,
          actual: checksum_actual
        }
      ),
      format!("{:?}", Node::read_from(&mut storage).unwrap_err())
    );
    set_checksum(&mut storage, correct)?;

    // ペイロードの破損
    let mut payload = get_payload(&mut storage)?;
    payload[3] += 1;
    let correct = set_payload(&mut storage, &payload)?;
    let checksum_expected = get_checksum(&mut storage)?;
    let checksum_actual = Node::checksum(&payload);
    assert_eq!(
      format!(
        "{:?}",
        ChecksumVerificationFailed {
          at: 0,
          length,
          expected: checksum_expected,
          actual: checksum_actual
        }
      ),
      format!("{:?}", Node::read_from(&mut storage).unwrap_err())
    );
    set_payload(&mut storage, &correct)?;
  }
  Ok(())
}

// TODO ストレージ末尾の 4 バイトの指す位置がたまたま最後より前の要素だった場合に、その要素を最後の要素とみなして後続が上書きされないように検証すること。

fn set_type(storage: &mut dyn Storage, id: u8) -> Result<u8> {
  storage.seek(SeekFrom::Start(0))?;
  let id = replace_u8(storage, id)?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(id)
}

fn get_length(storage: &mut dyn Storage) -> Result<u32> {
  storage.seek(SeekFrom::Start(1))?;
  let length = storage.read_u32::<LittleEndian>()?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(length)
}

fn set_length(storage: &mut dyn Storage, length: u32) -> Result<u32> {
  storage.seek(SeekFrom::Start(1))?;
  let length = replace_u32(storage, length)?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(length)
}

fn get_checksum(storage: &mut dyn Storage) -> Result<u64> {
  storage.seek(SeekFrom::Start(1 + 4))?;
  let checksum = storage.read_u64::<LittleEndian>()?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(checksum)
}

fn set_checksum(storage: &mut dyn Storage, checksum: u64) -> Result<u64> {
  storage.seek(SeekFrom::Start(1 + 4))?;
  let checksum = replace_u64(storage, checksum)?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(checksum)
}

fn get_payload(storage: &mut dyn Storage) -> Result<Vec<u8>> {
  let length = get_length(storage)?;
  let mut payload = Vec::<u8>::with_capacity(length as usize);
  unsafe {
    payload.set_len(length as usize);
  }
  storage.seek(SeekFrom::Start(1 + 4 + 8))?;
  storage.read_exact(&mut payload)?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(payload)
}

fn set_payload(storage: &mut dyn Storage, payload: &[u8]) -> Result<Vec<u8>> {
  let current = get_payload(storage)?;
  assert_eq!(current.len(), payload.len());
  storage.seek(SeekFrom::Start(1 + 4 + 8))?;
  storage.write_all(payload)?;
  storage.seek(SeekFrom::Start(0))?;
  Ok(current)
}

fn replace_u8(storage: &mut dyn Storage, value: u8) -> Result<u8> {
  let old = storage.read_u8()?;
  storage.seek(SeekFrom::Current(-1))?;
  storage.write_u8(value)?;
  storage.seek(SeekFrom::Current(-1))?;
  Ok(old)
}

fn replace_u32(storage: &mut dyn Storage, value: u32) -> Result<u32> {
  let old = storage.read_u32::<LittleEndian>()?;
  storage.seek(SeekFrom::Current(-4))?;
  storage.write_u32::<LittleEndian>(value)?;
  storage.seek(SeekFrom::Current(-4))?;
  Ok(old)
}

fn replace_u64(storage: &mut dyn Storage, value: u64) -> Result<u64> {
  let old = storage.read_u64::<LittleEndian>()?;
  storage.seek(SeekFrom::Current(-8))?;
  storage.write_u64::<LittleEndian>(value)?;
  storage.seek(SeekFrom::Current(-8))?;
  Ok(old)
}

/// テストに使用する代表的なノードの一覧を参照。
fn representative_nodes() -> Vec<Node> {
  let mut intermediate = Intermediate::new();
  intermediate.set_left_node(100);
  intermediate.set_right_node(200);
  intermediate.set_hash(vec![0, 1, 2, 3, 4, 5, 6, 7]);

  let mut leaf = Leaf::new();
  leaf.set_hash(vec![9, 8, 7, 6, 5, 4, 3, 2]);
  leaf.set_payload(vec![0, 0, 1, 1, 2, 2, 3, 3, 4, 4]);

  vec![Node::Intermediate(intermediate.clone()), Node::Leaf(leaf.clone())]
}
