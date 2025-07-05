use std::env::temp_dir;
use std::fs::{create_dir_all, remove_dir_all, remove_file, OpenOptions};
use std::io::{ErrorKind, Write};
use std::path::{PathBuf, MAIN_SEPARATOR};

use criterion::{criterion_group, criterion_main, Criterion};
use db_key::Key;
use leveldb::database::Database;
use leveldb::kv::KV;
use leveldb::options::{Options, ReadOptions, WriteOptions};

use slate::model::NthGenHashTree;
use slate::{Hash, Index, MemStorage, Slate, HASH_SIZE};

fn bench_append(c: &mut Criterion) {
  let file = temp_file("bench", ".db");
  let _db = Slate::new(file.clone()).unwrap();
  let mut db = Slate::new(MemStorage::new()).unwrap();
  let data = &[0u8; 1024];
  c.bench_function("Slate append", |b| b.iter(|| db.append(data).unwrap()));
  remove_file(&file).unwrap();
}

fn bench_level_db(c: &mut Criterion) {
  let dir = temp_directory("bench", ".leveldb");
  {
    let mut opts = Options::new();
    opts.create_if_missing = true;
    let db: Database<KEY> = Database::open(dir.as_path(), opts).unwrap();
    let data = &[0u8; 1024];
    let write_option = WriteOptions::new();
    let mut i: Index = 1;
    c.bench_function("leveldb append", |b| {
      b.iter(|| {
        // 値の保存
        let key = format!("val{}", i);
        db.put(write_option, KEY(key), data).unwrap();

        // ハッシュ値の保存
        let key = format!("hash{}_0", i);
        let hash = Hash::from_bytes(data);
        db.put(write_option, KEY(key), &hash.value).unwrap();

        // 中間ノードのハッシュ値の保存
        let gen = NthGenHashTree::new(i as u64);
        let mut right_hash = hash;
        for inode in gen.inodes().iter() {
          let key = format!("hash{}_{}", inode.left.i, inode.left.j);
          let read_option = ReadOptions::new();
          let left_hash = db.get_bytes(read_option, &KEY(key)).unwrap().unwrap();
          let mut left_hash_bytes = [0u8; HASH_SIZE];
          (&mut left_hash_bytes[..]).write_all(left_hash.as_ref()).unwrap();
          let left_hash = Hash::new(left_hash_bytes);

          let key = format!("hash{}_{}", i, inode.node.j);
          let hash = left_hash.combine(&right_hash);
          db.put(write_option, KEY(key), &hash.value).unwrap();
          right_hash = hash;
        }

        i += 1;
      })
    });
  }
  remove_dir_all(dir).unwrap();
}

struct KEY(String);

impl Key for KEY {
  fn from_u8(key: &[u8]) -> Self {
    KEY(String::from_utf8(key.to_vec()).unwrap())
  }

  fn as_slice<T, F: Fn(&[u8]) -> T>(&self, f: F) -> T {
    f(self.0.as_bytes())
  }
}

criterion_group!(benches, bench_append, bench_level_db);
criterion_main!(benches);

/// 指定された接頭辞と接尾辞を持つ 0 バイトのテンポラリファイルをシステムのテンポラリディレクトリ上に作成します。
/// 作成したファイルは呼び出し側で削除する必要があります。
fn temp_file(prefix: &str, suffix: &str) -> PathBuf {
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

fn temp_directory(prefix: &str, suffix: &str) -> PathBuf {
  let dir = temp_dir();
  for i in 0u16..=u16::MAX {
    let dir_name = format!("{}{}{}", prefix, i, suffix);
    let mut dir = dir.to_path_buf();
    dir.push(dir_name);
    if dir.exists() {
      continue;
    }
    match create_dir_all(&dir) {
      Ok(_) => {
        assert!(dir.is_dir(), "{} is not directory", dir.to_string_lossy());
        assert_eq!(
          0,
          std::fs::read_dir(&dir).unwrap().count(),
          "{} has {} files or dirs",
          dir.to_string_lossy(),
          std::fs::read_dir(&dir).unwrap().count()
        );
        return dir;
      }
      Err(err) if err.kind() == ErrorKind::AlreadyExists => (),
      Err(err) => panic!("{}", err),
    }
  }
  panic!("cannot create new temporary dir: {}{}{}nnn{}", dir.to_string_lossy(), MAIN_SEPARATOR, prefix, suffix);
}
