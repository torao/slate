use std::env::temp_dir;
use std::hash::BuildHasher;
use std::hash::Hasher;
use std::io;
use std::io::{ErrorKind, Seek};
use std::io::{SeekFrom, Write};
use std::path::{MAIN_SEPARATOR, PathBuf};
use std::thread::{JoinHandle, spawn};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayBuildHasher, Key};
use mt19937::MT19937;
use rand::RngCore;

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
        let mut query = cloned_db.query().unwrap();
        for i in 0..=N {
          if let Some(value) = query.get(i).unwrap() {
            assert!(i > 0 || i <= n);
            assert_eq!(&random_payload(PAYLOAD_SIZE, i), value.as_ref());
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

/// 単一のエントリの直列化と復元をテストします。
#[test]
fn entry_serialization() -> Result<()> {
  for entry in sample_entries() {
    // メモリ上に書き込みを行いサイズを確認
    let mut buffer = Vec::new();
    let write_length = write_entry(&mut buffer, &entry)?;
    assert_eq!(write_length, buffer.len());

    // チェックサムが実際に書き込まれたバイナリに対するものであることを確認
    verify_checksum(&buffer);

    let expected = entry;

    // 中間ノードのみを読み出して同一かを確認
    let mut cursor = io::Cursor::new(buffer.clone());
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
  for entry in sample_entries() {
    // 正しく書き込まれたバイナリを取得
    let mut buffer = Vec::new();
    let write_length = write_entry(&mut buffer, &entry)?;
    assert_eq!(write_length, buffer.len());

    let mut cursor = io::Cursor::new(buffer.clone());
    assert_eq!(entry, read_entry(&mut cursor, 0)?);

    for position in 0u64..buffer.len() as u64 {
      // データ破損の設定
      cursor.seek(SeekFrom::Start(position))?;
      let correct = cursor.read_u8()?;
      cursor.seek(SeekFrom::Current(-1))?;
      cursor.write_u8(!correct)?;

      // データ破損に対して LSHT::read_entry() でエラーが発生することを検証
      // TODO 最終的に、どのフィールドのバイト値が破損したかを識別して想定したエラーが検知されていることを確認する
      cursor.seek(SeekFrom::Start(0))?;
      let result = read_entry(&mut cursor, 0);
      assert!(result.is_err(), "{result:?}");

      // 破損したデータをもとに戻す
      cursor.seek(SeekFrom::Start(position))?;
      cursor.write_u8(correct)?;
    }
  }
  Ok(())
}

#[test]
fn test_bootstrap() {
  // 未初期化の空のストレージを指定してファイル識別子が書き込まれることを確認
  let buffer = Arc::new(RwLock::new(Vec::new()));
  let storage = MemStorage::with(buffer.clone());
  let db = Slate::new(storage).unwrap();
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

  // 0..n 個のエントリの直列化表現を作成
  let n = 100;
  let samples = (0..=n as u64)
    .map(|i| (0u64..i).map(|j| splitmix64(i * i + j)).collect::<Vec<_>>())
    .map(|values| values.iter().map(|i| i.to_le_bytes().to_vec()).collect::<Vec<_>>())
    .map(|values| {
      // 疑似ランダムな列の直列化形式を取得
      let buffer = Arc::new(RwLock::new(Vec::new()));
      let storage = MemStorage::with(buffer.clone());
      let mut db = Slate::new(storage).unwrap();
      for value in &values {
        db.append(value).unwrap();
      }
      let buffer = buffer.clone().read().unwrap().clone();
      (values, buffer)
    })
    .collect::<Vec<_>>();

  // 0..n 個のエントリの直列化が保存されているストレージからデータ列を復元できることを確認
  for (values, buffer) in samples {
    let storage = MemStorage::with(Arc::new(RwLock::new(buffer)));
    let db = Slate::new(storage).unwrap();
    let mut query = db.query().unwrap();
    for (i, expected) in values.iter().enumerate() {
      let actual = query.get(i as u64 + 1).unwrap().unwrap();
      assert_eq!(expected, actual.as_ref());
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
    let mut query = db.query().unwrap();

    // 単一の葉ノードを参照
    for i in 0..n {
      let expected = random_payload(PAYLOAD_SIZE, i + 1);
      let value = query.get(i + 1).unwrap();
      assert!(value.is_some());
      assert_eq!(&expected, value.unwrap().as_ref());
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

/// n 個の要素を持つ Slate を構築します。それぞれの要素は乱数で初期化された `payload_size` サイズの値を持ちます。
fn prepare_db(n: u64, payload_size: usize) -> Slate<MemStorage> {
  let buffer = Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024)));
  let storage = MemStorage::with(buffer.clone());
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
  let builder = HighwayBuildHasher::new(Key(CHECKSUM_HW64_KEY));
  let mut hasher = builder.build_hasher();
  hasher.write_all(bytes).unwrap();
  hasher.finish()
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
  let model = NthGenHashTree::new(i);
  let enode = ENode {
    meta: MetaInfo { address: Address { i, j: 0, position }, hash: random_hash(position ^ i) },
    payload: Arc::new(payload),
  };
  let inodes = model
    .inodes()
    .iter()
    .map(|inode| INode {
      meta: MetaInfo {
        address: Address { i: inode.node.i, j: inode.node.j, position },
        hash: random_hash(position ^ inode.node.j as u64),
      },
      left: Address { i: inode.left.i, j: inode.left.j, position },
      right: Address { i: inode.right.i, j: inode.right.j, position },
    })
    .collect();
  Entry { enode, inodes }
}

fn random_payload(length: usize, s: u64) -> Vec<u8> {
  let mut seed = [0u32; 2];
  seed[0] = (s & 0xFFFFFFFF) as u32;
  seed[1] = ((s >> 8) & 0xFFFFFFFF) as u32;
  let mut rand = MT19937::new_with_slice_seed(&seed);
  let mut bytes = vec![0u8; length];
  rand.fill_bytes(&mut bytes);
  bytes
}

fn random_hash(s: u64) -> Hash {
  let mut seed = [0u32; 2];
  seed[0] = (s & 0xFFFFFFFF) as u32;
  seed[1] = ((s >> 8) & 0xFFFFFFFF) as u32;
  let mut rand = MT19937::new_with_slice_seed(&seed);
  let mut hash = [0u8; HASH_SIZE];
  rand.fill_bytes(&mut hash);
  Hash::new(hash)
}

/// ファイルストレージの適合テスト。
#[test]
fn test_file_storage() {
  let file = temp_file("slate-storage", ".db");
  let mut db = FileStorage::new(&file).unwrap();
  verify_storage_spec(&mut db).unwrap_or_else(|_| panic!("Slate compliance test filed: {}", file.to_string_lossy()));
  remove_file(&file).unwrap_or_else(|_| panic!("failed to remove temporary file: {}", file.to_string_lossy()));
}

/// メモリーストレージの適合テスト
#[test]
fn test_memory_storage() {
  verify_storage_spec(&mut MemStorage::new()).expect("Slate compliance test filed");
}

/// 指定されたストレージが仕様に準拠していることを検証します。
pub fn verify_storage_spec(storage: &mut dyn Storage) -> Result<()> {
  // まだ書き込んでいない状態での末尾は 0
  let mut reader1 = storage.cursor().expect("failed to open cursor as read-only #1");
  let zero_position = reader1.seek(SeekFrom::End(0)).expect("failed to seek on zero-length storage");
  assert_eq!(0, zero_position);

  // 書き込みの実行
  let values = (0u8..=255).collect::<Vec<u8>>();
  storage.write_all(&values).unwrap_or_else(|_| panic!("fail to write"));
  storage.flush().unwrap();

  // 既存のカーソルは書き込みの影響を受けない
  assert_eq!(zero_position, reader1.stream_position()?);

  // 書き込み後に 2 つめの読み込み専用カーソルをオープン
  let mut reader2 = storage.cursor().expect("failed to open cursor as read-only #2");

  // 読み込みの実行
  for i in values.iter() {
    let value = reader1.read_u8().unwrap_or_else(|e| panic!("failed to read at {}, {}", *i, e));
    assert_eq!(*i, value);
  }

  // シークしてもう一度読み込みを実行 (ランダムアクセス)
  reader1.seek(SeekFrom::Start(0)).expect("fail to seek from 256 to 0");
  let mut rand = mt19937::MT19937::new_with_slice_seed(&[0u32]);
  for _ in 0..100 {
    let i = (rand.next_u32() & 0xFF) as u8;
    reader1.seek(SeekFrom::Start(i as u64)).unwrap_or_else(|_| panic!("failed to seek to {i}"));
    let value = reader1.read_u8().unwrap_or_else(|_| panic!("failed to read from cursor #1 at {i}"));
    assert_eq!(i, value);
    let i = (rand.next_u32() & 0xFF) as u8;
    reader2.seek(SeekFrom::Start(i as u64)).unwrap_or_else(|_| panic!("failed to seek to {i}"));
    let value = reader2.read_u8().unwrap_or_else(|_| panic!("failed to read from cursor #2 at {i}"));
    assert_eq!(i, value);
  }
  Ok(())
}

/// 指定された接頭辞と接尾辞を持つ 0 バイトのテンポラリファイルをシステムのテンポラリディレクトリ上に作成します。
/// 作成したファイルは呼び出し側で削除する必要があります。
pub fn temp_file(prefix: &str, suffix: &str) -> PathBuf {
  let dir = temp_dir();
  for i in 0u16..=u16::MAX {
    let file_name = format!("{prefix}{i}{suffix}");
    let mut file = dir.to_path_buf();
    file.push(file_name);
    match OpenOptions::new().write(true).create_new(true).open(&file) {
      Ok(_) => return file,
      Err(err) if err.kind() == ErrorKind::AlreadyExists => (),
      Err(err) => panic!("{}", err),
    }
  }
  panic!("cannot create new temporary file: {}{}{}nnn{}", dir.to_string_lossy(), MAIN_SEPARATOR, prefix, suffix);
}

fn splitmix64(x: u64) -> u64 {
  let mut z = x;
  z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
  z ^ (z >> 31)
}
