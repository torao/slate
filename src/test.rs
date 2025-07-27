use std::cmp::min;
use std::env::temp_dir as temprary_directory;
use std::fs::{OpenOptions, create_dir_all};
use std::io::ErrorKind;
use std::path::{MAIN_SEPARATOR, PathBuf};
use std::sync::RwLock;
use std::thread::{JoinHandle, spawn};

use crate::memory::MemoryDevice;
use crate::model::ceil_log2;
use crate::*;

#[test]
fn test_multi_threaded_query() {
  const N: u64 = 100;
  for n in 1..=N {
    let db = Arc::new(prepare_db(n, PAYLOAD_SIZE));
    let mut handles = Vec::<JoinHandle<()>>::with_capacity(10);
    for _ in 0..handles.capacity() {
      let cloned_db = db.clone();
      handles.push(spawn(move || {
        let snapshot = cloned_db.snapshot();
        let mut query = snapshot.query().unwrap();
        for i in 0..=N {
          if let Some(value) = query.get(i).unwrap() {
            assert!(i > 0 || i <= n);
            assert_eq!(&random_payload(PAYLOAD_SIZE, i), &value);
          } else {
            assert!(i == 0 || i > n, "None for i={i}, n={n}");
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

#[test]
fn test_bootstrap() {
  // 未初期化の空のストレージを指定してファイル識別子が書き込まれることを確認
  let buffer = Arc::new(RwLock::new(Vec::new()));
  let storage = BlockStorage::from_buffer(buffer.clone(), false);
  let db = Slate::new(storage).unwrap();
  let content = buffer.read().unwrap();
  let snapshot = db.snapshot();
  let mut query = snapshot.query().unwrap();
  assert_eq!(None, db.root());
  assert_eq!(0, db.n());
  assert_eq!(None, db.root_hash());
  assert_eq!(0, query.revision());
  assert_eq!(None, query.get(1).unwrap());
  assert_eq!(4, content.len());
  assert_eq!(&STORAGE_IDENTIFIER[..], &content[..3]);
  assert_eq!(STORAGE_VERSION, content[3]);

  // 0..n 個のエントリの直列化表現を作成
  let n = 100;
  let samples = (0..=n as u64)
    .map(|i| (0u64..i).map(|j| splitmix64(i * i + j)).collect::<Vec<_>>())
    .map(|value| value.iter().map(|i| i.to_le_bytes().to_vec()).collect::<Vec<_>>())
    .map(|values| {
      // 疑似ランダムな列の直列化形式を取得
      let buffer = Arc::new(RwLock::new(Vec::new()));
      let storage = BlockStorage::from_buffer(buffer.clone(), false);
      let mut db = Slate::new(storage).unwrap();
      for value in values.iter() {
        db.append(value).unwrap();
      }
      let buffer = buffer.clone().read().unwrap().clone();
      (values, buffer)
    })
    .collect::<Vec<_>>();

  // 0..n 個のエントリの直列化が保存されているストレージからデータ列を復元できることを確認
  for (values, buffer) in samples {
    let storage = BlockStorage::from_buffer(Arc::new(RwLock::new(buffer)), false);
    let db = Slate::new(storage).unwrap();
    let snapshot = db.snapshot();
    let mut query = snapshot.query().unwrap();
    for (i, expected) in values.iter().enumerate() {
      println!("{}/{}: {expected:?}", i + 1, db.n());
      let actual = query.get(i as u64 + 1).unwrap().unwrap();
      assert_eq!(expected, &actual);
    }
    match db.root() {
      Some(root) => {
        assert_eq!(values.len() as Index, root.i);
        assert_eq!(ceil_log2(values.len() as Index), root.j);
      }
      None => assert!(values.is_empty()),
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
    let snapshot = db.snapshot();
    let mut query = snapshot.query().unwrap();

    // 単一の葉ノードを参照
    for i in 0..n {
      let expected = random_payload(PAYLOAD_SIZE, i + 1);
      let value = query.get(i + 1).unwrap();
      assert!(value.is_some());
      assert_eq!(&expected, &value.unwrap());
    }

    // 範囲外のノードを参照
    assert!(query.get(0).unwrap().is_none());
    assert!(query.get(n + 1).unwrap().is_none());
  }
}

/// n 個の要素を持つ Slate を構築します。それぞれの要素は乱数で初期化された `payload_size` サイズの値を持ちます。
fn prepare_db(n: u64, payload_size: usize) -> Slate<BlockStorage<MemoryDevice>> {
  let buffer = Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024)));
  let storage = BlockStorage::from_buffer(buffer.clone(), false);
  let mut db = Slate::new(storage).unwrap();

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

/// 指定されたストレージが仕様に準拠していることを検証します。
pub fn verify_storage_spec<S: Storage<Entry, 0>>(storage: &mut S) {
  // まだ書き込んでいない状態では末尾のエントリは存在しない
  let (entry, first_position, _) = storage.boot().unwrap();
  assert!(entry.is_none());

  // 書き込みと読み込みを相互に実行
  let mut positions = [first_position].to_vec();
  for i in 0..1024 {
    if positions.len() == 1 || splitmix64(i as u64) < u64::MAX / 2 {
      // 書き込みの実行
      let i = positions.len() as u64;
      let position = *positions.last().unwrap();
      let value = i.to_le_bytes().to_vec();
      let entry = build_entry(i, &value, &positions);
      positions.push(storage.put(position, &entry).unwrap());
    } else {
      // 読み込みの実行
      let rand = splitmix64(!i as u64);
      let i = (rand % (positions.len() as u64 - 1) + 1) as Index;
      let position = positions[i as usize - 1];
      let value = i.to_le_bytes().to_vec();
      let expected = build_entry(i, &value, &positions);

      let mut cursor = storage.reader().unwrap();
      let entry = cursor.read(position).unwrap();
      assert_eq!(i, entry.enode.meta.address.i);
      assert_eq!(0, entry.enode.meta.address.j);
      assert_eq!(position, entry.enode.meta.address.position);
      assert_eq!(&value, &entry.enode.payload);
      let hash = Hash::from_bytes(&value);
      assert_eq!(hash, entry.enode.meta.hash);
      assert_eq!(&expected, &entry);
    }
  }
}

fn build_entry(i: Index, value: &[u8], positions: &[Index]) -> Entry {
  let position = positions[i as usize - 1];
  let model = NthGenHashTree::new(i);
  let enode =
    ENode { meta: MetaInfo::new(Address::new(i, 0, position), Hash::from_bytes(value)), payload: value.to_vec() };
  let inodes = model
    .inodes()
    .iter()
    .map(|inode| {
      let meta = MetaInfo::new(Address::new(inode.node.i, inode.node.j, position), Hash::new([0; Hash::SIZE]));
      let left = Address::new(inode.left.i, inode.left.j, positions[inode.left.i as usize - 1]);
      let right = Address::new(inode.right.i, inode.right.j, positions[inode.right.i as usize - 1]);
      INode::new(meta, left, right)
    })
    .collect();
  Entry::new(enode, inodes)
}

pub fn random_payload(length: usize, seed: u64) -> Vec<u8> {
  let mut buffer = Vec::with_capacity(length);
  let mut rand = seed;
  while buffer.len() < length {
    rand = splitmix64(rand);
    let bytes = rand.to_be_bytes();
    let len = min(bytes.len(), length - buffer.len());
    buffer.extend_from_slice(&bytes[..len]);
  }
  buffer
}

/// 指定された接頭辞と接尾辞を持つ 0 バイトの一時ファイルをシステムの一時ディレクトリの下に作成します。
/// 作成したファイルは呼び出し側で削除する必要があります。
pub fn temp_file(prefix: &str, suffix: &str) -> PathBuf {
  let tmp = temprary_directory();
  for i in 0u16..=u16::MAX {
    let file_name = format!("slate-{prefix}{i}{suffix}");
    let mut file = tmp.to_path_buf();
    file.push(file_name);
    match OpenOptions::new().write(true).create_new(true).open(&file) {
      Ok(_) => return file,
      Err(err) if err.kind() == ErrorKind::AlreadyExists => (),
      Err(err) => panic!("{}", err),
    }
  }
  panic!("cannot create new temporary file: {}{}{}nnn{}", tmp.to_string_lossy(), MAIN_SEPARATOR, prefix, suffix);
}

/// 指定された接頭辞と接尾辞を持つ空の一時ディレクトリをシステムの一時ディレクトリの下に作成します。
/// 作成したディレクトリは呼び出し側で削除する必要があります。
pub fn temp_dir(prefix: &str, suffix: &str) -> PathBuf {
  let tmp = temprary_directory();
  for i in 0u16..=u16::MAX {
    let dir_name = format!("slate-{prefix}{i}{suffix}");
    let mut dir = tmp.to_path_buf();
    dir.push(dir_name);
    if create_dir_all(&dir).is_ok() {
      return dir;
    }
  }
  panic!("cannot create new temporary directory: {}{}{}nnn{}", tmp.to_string_lossy(), MAIN_SEPARATOR, prefix, suffix);
}

pub fn splitmix64(x: u64) -> u64 {
  let mut z = x;
  z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
  z ^ (z >> 31)
}
