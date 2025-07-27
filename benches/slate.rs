use std::fs::{OpenOptions, remove_file};
use std::io::ErrorKind;
use std::path::MAIN_SEPARATOR;
use std::{env::temp_dir as temporary_directory, path::PathBuf};

use criterion::{Criterion, criterion_group, criterion_main};
use slate::{BlockStorage, Slate};

const ITER_SIZE: usize = 10 * 1024;

fn append(c: &mut Criterion) {
  let path = temp_file("bench", ".db");
  c.bench_function(&format!("append()×{ITER_SIZE}"), |b| {
    b.iter_batched(
      || {
        remove_file(&path).unwrap();
        let storage = BlockStorage::from_file(&path, false).unwrap();
        Slate::new(storage).unwrap()
      },
      |mut slate| {
        for i in 0..ITER_SIZE {
          slate.append(&splitmix64(i as u64).to_le_bytes()).unwrap();
        }
      },
      criterion::BatchSize::PerIteration,
    );
  });
  remove_file(&path).unwrap();
}

fn query(c: &mut Criterion) {
  let path = temp_file("bench", ".db");
  let storage = BlockStorage::from_file(&path, false).unwrap();
  let mut slate = Slate::new(storage).unwrap();
  for i in 0..ITER_SIZE {
    slate.append(&splitmix64(i as u64).to_le_bytes()).unwrap();
  }
  let mut r = splitmix64(0);
  let mut query = slate.snapshot().query().unwrap();
  c.bench_function(&format!("query()×{ITER_SIZE}"), |b| {
    b.iter(|| {
      let index = r % ITER_SIZE as u64 + 1;
      query.get(index).unwrap().unwrap();
      r = splitmix64(r);
    });
  });
  remove_file(&path).unwrap();
}

criterion_group!(benches, append, query);
criterion_main!(benches);

fn temp_file(prefix: &str, suffix: &str) -> PathBuf {
  let tmp = temporary_directory();
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

fn splitmix64(x: u64) -> u64 {
  let mut z = x;
  z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
  z ^ (z >> 31)
}
