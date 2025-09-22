use std::fs::remove_dir_all;
use std::sync::{Arc, RwLock};

use rocksdb::{DB, Options};

use crate::rocksdb::RocksDBStorage;
use crate::storage::test::verify_storage_compliance_with_standards;
use crate::test::temp_dir;
use crate::test::verify_storage_spec;

#[test]
fn test_rocks_db() {
  let path = temp_dir("test_rocks_db", "");
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

#[test]
fn verify_rocksdb_storage_compliance() -> crate::Result<()> {
  let path = temp_dir("storage-rocksdb", ".db");
  {
    let db = Arc::new(RwLock::new(DB::open_default(&path)?));
    verify_storage_compliance_with_standards(&db, |db| RocksDBStorage::new(db.clone(), &[], false))?;
  }
  remove_dir_all(&path)?;
  Ok(())
}
