use crate::checksum::hasher;
use crate::formula::Model;
use crate::storage::{read_data, write_data};
use crate::test::{random_payload, temp_file, verify_storage_spec};
use crate::{Address, BlockStorage, ENode, Entry, Hash, INode, Index, MetaInfo, Result, Serializable};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::fs::remove_file;
use std::hash::Hasher;
use std::io::{self, Cursor, Write};
use std::io::{Seek, SeekFrom};

/// 単一のエントリの直列化と復元をテストします。
#[test]
fn entry_serialization() -> Result<()> {
  for entry in sample_entries() {
    // メモリ上に書き込みを行いサイズを確認
    let mut buffer = Vec::new();
    let written_length = write_data(&mut Cursor::new(&mut buffer), &entry)?;
    assert_eq!(written_length, buffer.len());

    // バッファの末尾に u64 で書き込まれたチェックサムが存在することを確認
    verify_the_u64_at_the_end_is_checksum(&buffer);

    let expected = entry;

    // エントリ全体を読み出して同一かを確認
    let mut cursor = io::Cursor::new(buffer.clone());
    cursor.set_position(0);
    let actual = Entry::read(&mut cursor, 0)?;
    assert_eq!(expected, actual);
  }
  Ok(())
}

/// 直列化したバイナリの任意の位置のバイトを破損させて、破損位置のフィールドに対して想定するエラーが発生することを
/// 検証します。
#[test]
fn garbled_at_any_position() -> Result<()> {
  for entry in sample_entries() {
    // 正しく書き込まれたバイナリを取得
    let mut buffer = Vec::new();
    let write_length = write_data(&mut Cursor::new(&mut buffer), &entry)?;
    assert_eq!(write_length, buffer.len());

    let mut cursor = io::Cursor::new(buffer.clone());
    assert_eq!(entry, Entry::read(&mut cursor, 0)?);

    for position in 0u64..buffer.len() as u64 {
      // データ破損の設定
      cursor.seek(SeekFrom::Start(position))?;
      let correct = cursor.read_u8()?;
      cursor.seek(SeekFrom::Current(-1))?;
      cursor.write_u8(!correct)?;

      // データ破損に対して read_entry() でエラーが発生することを検証
      // TODO 最終的に、どのフィールドのバイト値が破損したかを識別して想定したエラーが検知されていることを確認する
      cursor.seek(SeekFrom::Start(0))?;
      let result = read_data::<_, Entry>(&mut cursor, 0);
      assert!(result.is_err(), "{result:?}");

      // 破損したデータをもとに戻す
      cursor.seek(SeekFrom::Start(position))?;
      cursor.write_u8(correct)?;
    }
  }
  Ok(())
}

/// ファイルストレージの適合テスト。
#[test]
fn test_file_storage() {
  let path = temp_file("storage", ".db");
  {
    let mut storage = BlockStorage::from_file(&path, false).unwrap();
    verify_storage_spec(&mut storage);
  }
  remove_file(&path).unwrap_or_else(|_| panic!("failed to remove temporary file: {}", path.to_string_lossy()));
}

/// メモリーストレージの適合テスト
#[test]
fn test_memory_storage() {
  verify_storage_spec(&mut BlockStorage::memory());
}

/// エントリの直列表現のチェックサムを検証します。
fn verify_the_u64_at_the_end_is_checksum(entry_buffer: &[u8]) {
  let mut cursor = io::Cursor::new(entry_buffer);

  // エントリの直列化表現に記録されているチェックサムを読み出し
  cursor.seek(SeekFrom::End(-(u64::BITS as i64) / 8)).unwrap();
  let expected = cursor.read_u64::<LittleEndian>().unwrap();

  // エントリの実際のチェックサムを算出
  let mut hasher = hasher();
  hasher.write_all(&entry_buffer[..(entry_buffer.len() - u64::BITS as usize / 8)]).unwrap();
  let actual = hasher.finish();
  assert_eq!(expected, actual);
}

// TODO ストレージ末尾の 4 バイトの指す位置がたまたま最後より前の要素だった場合に、その要素を最後の要素とみなして
// 後続が上書きされないように検証すること。

/// 単体のエントリの書き込みと読み込みに使用する代表的なエントリを参照。
fn sample_entries() -> Vec<Entry> {
  vec![
    create_sample_entry(1, Vec::new()),
    create_sample_entry(1, random_payload(5, 302875)),
    create_sample_entry(2, random_payload(826, 48727)),
    create_sample_entry(3, random_payload(826, 48727)),
  ]
}

fn create_sample_entry(i: Index, payload: Vec<u8>) -> Entry {
  let position = 0;
  let model = Model::new(i);
  let enode = ENode {
    meta: MetaInfo { address: Address { i, j: 0, position }, hash: Hash::new([0; crate::Hash::SIZE]) },
    payload,
  };
  let inodes = model
    .inodes()
    .iter()
    .map(|inode| INode {
      meta: MetaInfo {
        address: Address { i: inode.node.i, j: inode.node.j, position },
        hash: Hash::new([0; crate::Hash::SIZE]),
      },
      left: Address { i: inode.left.i, j: inode.left.j, position },
      right: Address { i: inode.right.i, j: inode.right.j, position },
    })
    .collect();
  Entry::new(enode, inodes)
}
