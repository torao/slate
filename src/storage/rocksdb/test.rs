use std::fs::remove_dir_all;
use std::sync::{Arc, RwLock};

use rocksdb::{DB, Options};

use crate::test::temp_dir;
use crate::{rocksdb::RocksDBStorage, test::verify_storage_spec};

#[test]
fn test_rocks_db() {
  let path = temp_dir("rocksdb", "");
  remove_dir_all(&path).unwrap();
  {
    let mut opts = Options::default();
    opts.create_if_missing(true);
    let db = Arc::new(RwLock::new(DB::open(&opts, &path).unwrap()));
    let mut storage = RocksDBStorage::new(db, &[], true);
    verify_storage_spec(&mut storage);
  }
  remove_dir_all(&path).unwrap();
}
