use std::cmp::max;
use std::env::temp_dir;
use std::hash::Hasher;
use std::io;
use std::io::{ErrorKind, Seek};
use std::io::{SeekFrom, Write};
use std::path::{MAIN_SEPARATOR, PathBuf};
use std::thread::{JoinHandle, spawn};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuilder, Key};
use mt19937::MT19937;
use rand::RngCore;

use crate::*;
use crate::model::ceil_log2;

#[test]
fn test_multi_threaded_query() {
  const N: u64 = 100;
  for n in 1..=N {
    let db = Arc::new(prepare_db(n, PAYLOAD_SIZE));
    let mut handles = Vec::<JoinHandle<()>>::with_capacity(10);
    for _ in 0..handles.capacity() {
      let cloned_db = db.clone();
      handles.push(spawn(move || {
        let mut query = cloned_db.query().unwrap();
        for i in 0..=N {
          if let Some(value) = query.get(i).unwrap() {
            assert!(i > 0 || i <= n);
            assert_eq!(random_payload(PAYLOAD_SIZE, i), value);
          } else {
            assert!(i == 0 || i > n, "None for i={}, n={}", i, n);
          }
        }
      }));
    }

    // すべてのスレッドが終了するまで待機
    while !handles.is_empty() {
      let result = handles.pop().unwrap().join();
      assert!(result.is_ok(), "{:?}", result.unwrap_err());
    }
  }
}

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
fn test_bootstrap() {
  // 空のストレージを指定してファイル識別子が出力されることを確認
  let buffer = Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024)));
  let storage = MemStorage::with(buffer.clone());
  let db = MVHT::new(storage).unwrap();
  let content = buffer.read().unwrap();
  let mut session = db.query().unwrap();
  assert_eq!(None, db.root());
  assert_eq!(0, db.n());
  assert_eq!(None, db.root_hash());
  assert_eq!(0, session.n());
  assert_eq!(None, session.get(1).unwrap());
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
    let last = entry.inodes.last().map(|i| i.meta).unwrap_or(entry.enode.meta);
    assert_eq!(Some(Node::new(last.address.i, last.address.j, last.hash)), db.root());
  }
}

const PAYLOAD_SIZE: usize = 4;

/// データを追加して取得します。
#[test]
fn test_append_and_get() {
  const N: u64 = 100;
  for n in 1..=N {
    let db = prepare_db(n, PAYLOAD_SIZE);
    let mut query = db.query().unwrap();

    // 単一の葉ノードを参照
    for i in 0..n {
      let expected = random_payload(PAYLOAD_SIZE, i + 1);
      let value = query.get(i + 1).unwrap();
      assert!(value.is_some());
      assert_eq!(expected, value.unwrap());
    }

    // 範囲外のノードを参照
    assert!(query.get(0).unwrap().is_none());
    assert!(query.get(n + 1).unwrap().is_none());
  }
}

/// ハッシュ付き値参照で取得した値とハッシュ値の検証。
#[test]
fn test_get_values_with_hashes() {
  const N: u64 = 100;
  for n in 1..=N {
    let db = prepare_db(n, PAYLOAD_SIZE);
    let mut query = db.query().unwrap();
    let tree = NthGenHashTree::new(n);
    for i in 0..n {
      for j in 0..=ceil_log2(i + 1) {
        // 範囲外のノードを参照
        assert!(query.get_values_with_hashes(0, j).unwrap().is_none());
        assert!(query.get_values_with_hashes(n + 1, j).unwrap().is_none());

        if j != 0 && tree.inode(i + 1, j).is_none() {
          continue;
        }

        // 中間ノードを指定してそのノードに属する値をハッシュ値付きですべて参照
        let data_set = query.get_values_with_hashes(i + 1, j).unwrap().unwrap();

        // ルートハッシュを検証
        assert_eq!(db.root_hash().unwrap(), data_set.root().hash);

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
    let root = db.append(value.as_slice()).expect("append() failed");
    // dump(&mut db);
    assert_eq!(db.root().unwrap(), root);
    assert_eq!(i + 1, root.i);
    assert_eq!(ceil_log2(i + 1), root.j);
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
  ENode { meta: MetaInfo { address: Address { i, j: 0, position }, hash: random_hash(position ^ i) }, payload }
}

fn inode(i: u64, j: u8, position: u64) -> INode {
  INode {
    meta: MetaInfo { address: Address { i, j, position }, hash: random_hash(position ^ j as u64) },
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

/// ファイルストレージの適合テスト。
#[test]
fn test_file_storage() {
  let file = temp_file("mvht-storage", ".db");
  verify_storage_spec(&file).expect(&format!("MVHT compliance test filed: {}", file.to_string_lossy()));
  remove_file(file.to_path_buf()).expect(&format!("failed to remove temporary file: {}", file.to_string_lossy()));
}

/// メモリーストレージの適合テスト
#[test]
fn test_memory_storage() {
  verify_storage_spec(&MemStorage::new()).expect("MVHT compliance test filed");
}

/// 指定されたストレージが仕様に準拠していることを検証します。
pub fn verify_storage_spec(storage: &dyn Storage) -> Result<()> {
  // 読み込み専用または書き込み用に (同時に) オープンできることを確認
  let mut writer = storage.open(true).expect("failed to open cursor as writable");
  let mut reader1 = storage.open(false).expect("failed to open cursor as read-only #1");

  // まだ書き込んでいない状態で末尾までシーク
  let zero_position = reader1.seek(SeekFrom::End(0)).expect("failed to seek on zero-length storage");
  assert_eq!(0, zero_position);

  // 書き込みの実行
  let values = (0u8..=255).collect::<Vec<u8>>();
  for i in values.iter() {
    writer.write_u8(*i).expect(&format!("fail to write at {}", *i));
  }

  // 書き込み後に 2 つめの読み込み専用カーソルをオープン
  let mut reader2 = storage.open(false).expect("failed to open cursor as read-only #2");

  // 読み込みの実行
  for i in values.iter() {
    let value = reader1.read_u8().expect(&format!("failed to read at {}", *i));
    assert_eq!(*i, value);
  }

  // シークしてもう一度読み込みを実行 (ランダムアクセス)
  reader1.seek(SeekFrom::Start(0)).expect("fail to seek from 256 to 0");
  let mut rand = mt19937::MT19937::new_with_slice_seed(&[0u32]);
  for _ in 0..100 {
    let i = (rand.next_u32() & 0xFF) as u8;
    reader1.seek(SeekFrom::Start(i as u64)).expect(&format!("failed to seek to {}", i));
    let value = reader1.read_u8().expect(&format!("failed to read from cursor #1 at {}", i));
    assert_eq!(i, value);
    let i = (rand.next_u32() & 0xFF) as u8;
    reader2.seek(SeekFrom::Start(i as u64)).expect(&format!("failed to seek to {}", i));
    let value = reader2.read_u8().expect(&format!("failed to read from cursor #2 at {}", i));
    assert_eq!(i, value);
  }
  Ok(())
}

/// 指定された接頭辞と接尾辞を持つ 0 バイトのテンポラリファイルをシステムのテンポラリディレクトリ上に作成します。
/// 作成したファイルは呼び出し側で削除する必要があります。
pub fn temp_file(prefix: &str, suffix: &str) -> PathBuf {
  let dir = temp_dir();
  for i in 0u16..=u16::MAX {
    let file_name = format!("{}{}{}", prefix, i, suffix);
    let mut file = dir.to_path_buf();
    file.push(file_name);
    match OpenOptions::new().write(true).create_new(true).open(file.to_path_buf()) {
      Ok(_) => return file,
      Err(err) if err.kind() == ErrorKind::AlreadyExists => (),
      Err(err) => panic!("{}", err),
    }
  }
  panic!("cannot create new temporary file: {}{}{}nnn{}", dir.to_string_lossy(), MAIN_SEPARATOR, prefix, suffix);
}
