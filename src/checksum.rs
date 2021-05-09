use std::hash::Hasher;
use std::io::{Read, Write};

pub struct HashWrite<'i> {
  output: &'i mut dyn Write,
  hasher: &'i mut dyn Hasher,
  length: u64,
}

impl<'i> HashWrite<'i> {
  pub fn new(output: &'i mut dyn Write, hasher: &'i mut dyn Hasher) -> HashWrite<'i> {
    HashWrite { output, hasher, length: 0 }
  }

  pub fn length(&self) -> u64 {
    self.length
  }

  pub fn finish(&self) -> u64 {
    self.hasher.finish()
  }
}

impl<'i> Write for HashWrite<'i> {
  fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
    let result = self.output.write(buf);
    self.hasher.write(buf);
    self.length += buf.len() as u64;
    result
  }

  fn flush(&mut self) -> std::io::Result<()> {
    self.output.flush()
  }
}

pub struct HashRead<'i> {
  input: &'i mut dyn Read,
  hasher: &'i mut dyn Hasher,
  length: u64,
}

impl<'i> HashRead<'i> {
  pub fn new(input: &'i mut dyn Read, hasher: &'i mut dyn Hasher) -> HashRead<'i> {
    HashRead { input, hasher, length: 0 }
  }
  pub fn length(&self) -> u64 {
    self.length
  }
  pub fn finish(&self) -> u64 {
    self.hasher.finish()
  }
}

impl<'i> Read for HashRead<'i> {
  fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
    let size = self.input.read(buf)?;
    self.hasher.write(&buf[..size]);
    self.length += size as u64;
    Ok(size)
  }
}
