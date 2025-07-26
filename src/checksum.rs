use crate::Error::*;
use crate::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayHasher, Key};
use std::hash::Hasher;
use std::io::Seek;
use std::io::{Read, Write};

#[cfg(test)]
mod test;

/// HighwayHash でチェックサム用のハッシュ値を生成するためのキー (256-bit 固定値)。
const CHECKSUM_HW64_KEY: [u64; 4] = [0xFA5015F2E22BCFC6u64, 0xCE5A4ED9A4025C80, 0x16B9731717F6315E, 0x0F34D06AE93BD8E9];

pub fn hasher() -> HighwayHasher {
  HighwayHasher::new(Key(CHECKSUM_HW64_KEY))
}

pub struct ChecksumWrite<W: Write> {
  output: W,
  hasher: HighwayHasher,
  offset: u32,
}

impl<W: Write> ChecksumWrite<W> {
  pub fn new(output: W) -> Self {
    let hasher = hasher();
    let length = 0;
    ChecksumWrite { output, hasher, offset: length }
  }

  pub fn write_delimiter(&mut self) -> std::io::Result<usize> {
    // エントリ先頭までのオフセットを書き込み
    self.write_u32::<LittleEndian>(self.offset)?;

    // チェックサムの書き込み
    let checksum = self.hasher.finish();
    self.output.write_u64::<LittleEndian>(checksum)?;
    self.offset += u64::BITS / 8;

    Ok((u32::BITS + u64::BITS) as usize / 8)
  }
}

impl<W: Write> Write for ChecksumWrite<W> {
  fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
    let len = self.output.write(buf)?;
    self.hasher.write_all(&buf[..len])?;
    self.offset += len as u32;
    Ok(len)
  }

  fn flush(&mut self) -> std::io::Result<()> {
    self.output.flush()
  }
}

pub type Delimiter = (usize, (u32, u64), (u32, u64));

pub struct ChecksumRead<'a, R: Read + Seek> {
  input: &'a mut R,
  hasher: HighwayHasher,
  offset: u32,
}

impl<'a, R: Read + Seek> ChecksumRead<'a, R> {
  pub fn new(input: &'a mut R) -> Self {
    let hasher = hasher();
    let offset = 0;
    Self { input, hasher, offset }
  }

  pub fn read_delimiter(&mut self) -> Result<Delimiter> {
    let actual_offset = self.offset;
    let offset = self.read_u32::<LittleEndian>()?;
    let checksum = self.input.read_u64::<LittleEndian>()?;
    let actual_checksum = self.hasher.finish();
    Ok(((u32::BITS + u64::BITS) as usize / 8, (offset, checksum), (actual_offset, actual_checksum)))
  }

  pub fn check_delimiter(&mut self) -> Result<usize> {
    let (length, (offset, checksum), (actual_offset, actual_checksum)) = self.read_delimiter()?;
    if actual_offset != offset {
      dbg!(length, offset, actual_offset, checksum, actual_checksum);
      let mut buffer = vec![0u8; actual_offset as usize];
      let seek = std::cmp::max(0, self.input.stream_position().unwrap() as i64 - actual_offset as i64);
      self.input.seek(std::io::SeekFrom::Start(seek as u64)).unwrap();
      self.input.read_exact(&mut buffer).unwrap();
      dbg!(buffer);
      return Err(IncorrectEntryHeadOffset { expected: offset, actual: actual_offset });
    }
    if actual_checksum != checksum {
      let length = offset + (u32::BITS + u64::BITS) / 8;
      let position = self.input.stream_position()? - length as u64;
      return Err(ChecksumVerificationFailed { at: position, length, expected: checksum, actual: actual_checksum });
    }
    Ok(length)
  }
}

impl<'a, R: Read + Seek> Read for ChecksumRead<'a, R> {
  fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
    let size = self.input.read(buf)?;
    self.hasher.write_all(&buf[..size])?;
    self.offset += size as u32;
    Ok(size)
  }
}
