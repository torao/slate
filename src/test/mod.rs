use std::hash::Hasher;
use std::io;
use std::io::Seek;
use std::io::{SeekFrom, Write};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, Key};
use mt19937::MT19937;
use rand::RngCore;

use crate::*;
use std::cmp::max;

#[test]
fn entry_serialization() -> Result<()> {
  for entry in representative_entries() {
    // メモリ上に書き込みを行いサイズを確認
    let mut buffer = io::Cursor::new(Vec::<u8>::new());
    let write_length = write_entry(&mut buffer, &entry)?;
    let storage_length = buffer.seek(SeekFrom::End(0))?;
    println!("write {} bytes, data size: {} bytes", write_length, storage_length);
    assert_eq!(write_length as u64, storage_length);

    // 直列化後に復元したエントリと元のエントリが同一かを確認
    buffer.set_position(0);
    let expected = entry;
    let actual = read_entry(&mut buffer)?;
    assert_eq!(expected, actual);

    // チェックサムの確認
    verify_checksum(buffer.get_ref());
  }
  Ok(())
}

/// シリアライズしたバイナリの任意の位置のバイトを破損させて、破損位置のフィールドに対して想定するエラーが発生することを
/// 検証します。
#[test]
fn garbled_at_any_position() -> Result<()> {
  for entry in representative_entries() {
    let mut storage = io::Cursor::new(Vec::<u8>::new());
    let write_length = write_entry(&mut storage, &entry)?;
    let storage_length = storage.seek(SeekFrom::End(0))?;
    assert_eq!(write_length as u64, storage_length);
    storage.seek(SeekFrom::Start(0))?;
    assert_eq!(entry, read_entry(&mut storage)?);

    for position in 0..storage_length {
      // データ破損の設定
      storage.seek(SeekFrom::Start(position))?;
      let correct = storage.read_u8()?;
      storage.seek(SeekFrom::Current(-1))?;
      storage.write_u8(!correct)?;

      // データ破損に対して LSHT::read_entry() でエラーが発生することを検証
      // TODO 最終的に、どのフィールドのバイト値が破損したかを識別して想定したエラーが検知されていることを確認する
      storage.seek(SeekFrom::Start(0))?;
      let result = read_entry(&mut storage);
      assert!(result.is_err(), "{:?}", result);

      // 破損したデータをもとに戻す
      storage.seek(SeekFrom::Start(position))?;
      storage.write_u8(correct)?;
    }
  }
  Ok(())
}

/// エントリの直列表現のチェックサムを検証します。
fn verify_checksum(entry: &[u8]) {
  let mut cursor = io::Cursor::new(entry);

  // エントリの直列化表現に記録されているチェックサムを参照
  cursor.seek(SeekFrom::End(-8)).unwrap();
  let expected = cursor.read_u64::<LittleEndian>().unwrap();

  // エントリの実際のチェックサムを算出
  let actual = checksum(&entry[0..entry.len() - 8]);

  assert_eq!(expected, actual);
}

/// 指定されたバイナリデータに対するチェックサムを算出。
fn checksum(bytes: &[u8]) -> u64 {
  let mut hasher = HighwayBuilder::new(Key(HIGHWAYHASH64_KEY));
  hasher.write_all(bytes).unwrap();
  hasher.finish()
}

// TODO ストレージ末尾の 4 バイトの指す位置がたまたま最後より前の要素だった場合に、その要素を最後の要素とみなして
// 後続が上書きされないように検証すること。

/// テストに使用する代表的なノードの一覧を参照。
fn representative_entries() -> Vec<Entry> {
  vec![
    Entry { enode: enode(1, 0, random_payload(5, 302875)), inodes: vec![] },
    Entry { enode: enode(2, 0, random_payload(826, 48727)), inodes: vec![inode(2, 1, 0)] },
  ]
}

fn enode(i: u64, position: u64, payload: Box<Vec<u8>>) -> ENode {
  ENode { address: Address { i, j: 0, position }, payload, hash: random_hash(position ^ i) }
}

fn inode(i: u64, j: u8, position: u64) -> INode {
  INode {
    address: Address { i, j, position },
    left: Address { i: i - 1, j: 0, position: max(position as i64 - 100, 0) as u64 },
    right: Address { i, j: j - 1, position },
    hash: random_hash(position ^ j as u64),
  }
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
