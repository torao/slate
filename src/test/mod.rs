use std::cmp::max;
use std::hash::Hasher;
use std::io;
use std::io::Seek;
use std::io::{SeekFrom, Write};
use std::ops::Add;

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, Key};
use mt19937::MT19937;
use rand::RngCore;

use crate::algorithm::ceil_log2;
use crate::*;

/// 単一のエントリの直列化と復元をテストします。
#[test]
fn entry_serialization() -> Result<()> {
  for entry in representative_entries(0) {
    // メモリ上に書き込みを行いサイズを確認
    let mut cursor = io::Cursor::new(Vec::<u8>::new());
    let write_length = write_entry(&mut cursor, &entry)?;
    let storage_length = cursor.seek(SeekFrom::End(0))?;
    assert_eq!(write_length as u64, storage_length);

    // チェックサムが実際に書き込まれたバイナリに対するものであることを確認
    verify_checksum(cursor.get_ref());

    let expected = entry;

    // 中間ノードのみを読み出して同一かを確認
    cursor.set_position(0);
    let inodes = read_inodes(&mut cursor, 0)?;
    assert_eq!(expected.inodes, inodes);

    // チェックサムによるチェックなし版から復元して元のエントリと同一かを確認
    cursor.set_position(0);
    let actual = read_entry_without_check(&mut cursor, 0, 0)?;
    assert_eq!(expected, actual);

    // チェックサムによるチェックあり版から復元して元のエントリと同一かを確認
    cursor.set_position(0);
    let actual = read_entry(&mut cursor, 0)?;
    assert_eq!(expected, actual);
  }
  Ok(())
}

/// 直列化したバイナリの任意の位置のバイトを破損させて、破損位置のフィールドに対して想定するエラーが発生することを
/// 検証します。
#[test]
fn garbled_at_any_position() -> Result<()> {
  for entry in representative_entries(0) {
    let mut cursor = io::Cursor::new(Vec::<u8>::new());
    let write_length = write_entry(&mut cursor, &entry)?;
    let storage_length = cursor.seek(SeekFrom::End(0))?;
    assert_eq!(write_length as u64, storage_length);
    cursor.seek(SeekFrom::Start(0))?;
    assert_eq!(entry, read_entry(&mut cursor, 0)?);

    for position in 0..storage_length {
      // データ破損の設定
      cursor.seek(SeekFrom::Start(position))?;
      let correct = cursor.read_u8()?;
      cursor.seek(SeekFrom::Current(-1))?;
      cursor.write_u8(!correct)?;

      // データ破損に対して LSHT::read_entry() でエラーが発生することを検証
      // TODO 最終的に、どのフィールドのバイト値が破損したかを識別して想定したエラーが検知されていることを確認する
      cursor.seek(SeekFrom::Start(0))?;
      let result = read_entry(&mut cursor, 0);
      assert!(result.is_err(), "{:?}", result);

      // 破損したデータをもとに戻す
      cursor.seek(SeekFrom::Start(position))?;
      cursor.write_u8(correct)?;
    }
  }
  Ok(())
}

#[test]
fn bootstrap() {
  // 空のストレージを指定してファイル識別子が出力されることを確認
  let buffer = Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024)));
  let storage = MemStorage::with(buffer.clone());
  let db = MVHT::new(storage).unwrap();
  let content = buffer.read().unwrap();
  assert_eq!(RootRef::None, db.root());
  assert_eq!(4, content.len());
  assert_eq!(&STORAGE_IDENTIFIER[..], &content[..3]);
  assert_eq!(STORAGE_VERSION, content[3]);

  // ストレージの末尾に存在するエントリをルートとして読み込んでいることを確認
  for entry in representative_entries(4) {
    let mut buffer = Vec::<u8>::with_capacity(4 * 1024);
    buffer.write_all(&STORAGE_IDENTIFIER).unwrap();
    buffer.write_u8(STORAGE_VERSION).unwrap();
    write_entry(&mut buffer, &entry).unwrap();
    let buffer = Arc::new(RwLock::new(buffer));
    let storage = MemStorage::with(buffer.clone());
    let db = MVHT::new(storage).unwrap();
    if let Some(last) = entry.inodes.last() {
      assert_eq!(RootRef::INode(&last), db.root());
    } else {
      assert_eq!(RootRef::ENode(&entry.enode), db.root());
    }
  }
}

const PAYLOAD_SIZE: usize = 4;

/// データを追加して取得します。
#[test]
fn test_append_and_get() {
  const N: u64 = 100;
  for n in 1..=N {
    let db = prepare_db(n, PAYLOAD_SIZE);

    // 単一の葉ノードを参照
    for i in 0..n {
      let expected = random_payload(PAYLOAD_SIZE, i + 1);
      let value = db.get(i + 1).unwrap();
      assert!(value.is_some(), "value cannot retrieve: {}, {}", i + 1, dump(&db));
      assert_eq!(expected, value.unwrap());
    }

    // 範囲外のノードを参照
    assert!(db.get(0).unwrap().is_none());
    assert!(db.get(n + 1).unwrap().is_none());
  }
}

/// ハッシュ付き値参照で取得した値とハッシュ値の検証。
#[test]
fn test_get_values_with_hashes() {
  const N: u64 = 100;
  for n in 1..=N {
    let db = prepare_db(n, PAYLOAD_SIZE);
    let tree = Generation::new(n);
    for i in 0..n {
      for j in 0..=ceil_log2(i + 1) {

        // 範囲外のノードを参照
        assert!(db.get_values_with_hashes(0, j).unwrap().is_none());
        assert!(db.get_values_with_hashes(n + 1, j).unwrap().is_none());

        if j != 0 && tree.inode(i + 1, j).is_none() {
          continue;
        }

        // 中間ノードを指定してそのノードに属する値をハッシュ値付きですべて参照
        let data_set = db.get_values_with_hashes(i + 1, j).unwrap().unwrap();

        // ルートハッシュを検証
        assert_eq!(db.root_hash().unwrap(), data_set.root_hash());

        // 想定した範囲の値を取得しているか
        let range = range(i + 1, j);
        let min = range.clone().min().unwrap();
        let max = range.clone().max().unwrap();
        assert_eq!((max - min) as usize + 1, data_set.values.len());

        // 取得した値はすべて想定した値か
        for (x, k) in range.enumerate() {
          let expected = random_payload(PAYLOAD_SIZE, data_set.values[x].i);
          assert_eq!(k, data_set.values[x].i);
          assert_eq!(expected, data_set.values[x].value);
        }

        // ルートノードからの経路は想定と一致するか
        assert_eq!(tree.path_to(i + 1, j).unwrap().steps.len(), data_set.branches.len());
        for (expected, actual) in tree.path_to(i + 1, j).unwrap().steps.iter().zip(data_set.branches.iter()) {
          assert_eq!(expected.neighbor.i, actual.i);
          assert_eq!(expected.neighbor.j, actual.j);
        }
      }
    }
  }
}

/// n 個の要素を持つ MVHT を構築します。それぞれの要素は乱数で初期化された `payload_size` サイズの値を持ちます。
fn prepare_db(n: u64, payload_size: usize) -> MVHT<MemStorage> {
  let buffer = Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024)));
  let storage = MemStorage::with(buffer.clone());
  let mut db = MVHT::new(storage).unwrap();

  for i in 0..n {
    let value = random_payload(payload_size, i + 1);
    let (index, hash) = db.append(value.as_slice()).expect("append() failed");
    // dump(&mut db);
    assert_eq!(i + 1, index, "{}", hex(buffer.read().unwrap().as_slice()));
    assert_eq!(Hash::hash(&value), hash);
  }
  db
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
  let mut hasher = HighwayBuilder::new(Key(CHECKSUM_HW64_KEY));
  hasher.write_all(bytes).unwrap();
  hasher.finish()
}

// TODO ストレージ末尾の 4 バイトの指す位置がたまたま最後より前の要素だった場合に、その要素を最後の要素とみなして
// 後続が上書きされないように検証すること。

/// テストに使用する代表的なノードの一覧を参照。
fn representative_entries(position: u64) -> Vec<Entry> {
  vec![
    Entry { enode: enode(1, position, random_payload(5, 302875)), inodes: vec![] },
    Entry { enode: enode(2, position, random_payload(826, 48727)), inodes: vec![inode(2, 1, position)] },
  ]
}

fn enode(i: u64, position: u64, payload: Vec<u8>) -> ENode {
  ENode { node: Node { address: Address { i, j: 0, position }, hash: random_hash(position ^ i) }, payload }
}

fn inode(i: u64, j: u8, position: u64) -> INode {
  INode {
    node: Node { address: Address { i, j, position }, hash: random_hash(position ^ j as u64) },
    left: Address { i: i - 1, j: 0, position: max(position as i64 - 100, 0) as u64 },
    right: Address { i, j: j - 1, position },
  }
}

fn random_payload(length: usize, s: u64) -> Vec<u8> {
  let mut seed = [0u32; 2];
  seed[0] = ((s >> 0) & 0xFFFFFFFF) as u32;
  seed[1] = ((s >> 8) & 0xFFFFFFFF) as u32;
  let mut rand = MT19937::new_with_slice_seed(&seed);
  let mut bytes = Vec::<u8>::with_capacity(length);
  unsafe {
    bytes.set_len(length);
  }
  rand.fill_bytes(&mut bytes);
  bytes
}

fn random_hash(s: u64) -> Hash {
  let mut seed = [0u32; 2];
  seed[0] = ((s >> 0) & 0xFFFFFFFF) as u32;
  seed[1] = ((s >> 8) & 0xFFFFFFFF) as u32;
  let mut rand = MT19937::new_with_slice_seed(&seed);
  let mut hash = [0u8; HASH_SIZE];
  rand.fill_bytes(&mut hash);
  Hash::new(hash)
}

fn dump<T: Storage>(db: &MVHT<T>) -> String {
  fn indent(size: usize) -> String {
    let mut indents = String::with_capacity(size * 2);
    for _ in 0..size {
      indents = indents.add("  ");
    }
    indents
  }
  fn node<C: io::Read + io::Seek>(r: &mut C, idt: usize, addr: &Address) -> String {
    r.seek(SeekFrom::Start(addr.position)).unwrap();
    let entry = read_entry_without_check(r, addr.position, 0).unwrap();
    if addr.j == 0 {
      let enode = entry.enode;
      format!(
        "{{\n{}i: {}, j: {}, position: {},\n{}hash: 0x{}, hash_length: {},\n{}payload: 0x{}, payload_length: {},\n{}}}",
        indent(idt + 1),
        enode.node.address.i,
        enode.node.address.j,
        enode.node.address.position,
        indent(idt + 1),
        hex(&enode.node.hash.value),
        enode.node.hash.value.len(),
        indent(idt + 1),
        hex(&enode.payload),
        enode.payload.len(),
        indent(idt)
      )
    } else if let Some(inode) = entry.inodes.iter().find(|n| n.node.address.j == addr.j) {
      let left = node(r, idt + 1, &inode.left);
      let right = node(r, idt + 1, &inode.right);
      format!(
        "{{\n{}i: {}, j: {}, position: {},\n{}hash: 0x{}, hash_length: {},\n{}left: {},\n{}right: {}\n{}}}",
        indent(idt + 1),
        inode.node.address.i,
        inode.node.address.j,
        inode.node.address.position,
        indent(idt + 1),
        hex(&inode.node.hash.value),
        inode.node.hash.value.len(),
        indent(idt + 1),
        left,
        indent(idt + 1),
        right,
        indent(idt)
      )
    } else {
      "error: \"inode {:?} is not exist in the entry.\"".to_string()
    }
  }
  let address = match db.root() {
    RootRef::None => None,
    RootRef::ENode(enode) => Some(enode.node.address),
    RootRef::INode(inode) => Some(inode.node.address),
  };
  if let Some(address) = address {
    let mut cursor = db.storage.open(false).unwrap();
    node(&mut cursor, 0, &address)
  } else {
    "".to_string()
  }
}
