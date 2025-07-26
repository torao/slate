use std::hash::Hasher;
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

use crate::checksum::{ChecksumRead, ChecksumWrite};
use crate::error::Error;
use crate::test::splitmix64;
use crate::{Result, checksum::hasher};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

const OFFSET_AND_CHECKSUM_SIZE: usize = (u32::BITS + u64::BITS) as usize / 8;

#[test]
fn verify_the_written_offset_and_checksum_are_correct() -> Result<()> {
  for i in 0..1024 {
    // ランダムなバイト値を書き込み
    let buffer = {
      let mut buffer = Vec::new();
      let mut w = ChecksumWrite::new(&mut buffer);
      for j in 0..i {
        w.write_u8((splitmix64((i * 1024 + j) as u64) & 0xFF) as u8)?;
      }
      w.write_delimiter()?;
      buffer
    };
    assert!(buffer.len() == i + OFFSET_AND_CHECKSUM_SIZE);

    // オフセットを確認
    let mut cursor = Cursor::new(buffer.clone());
    let offset = cursor.seek(SeekFrom::End(-(OFFSET_AND_CHECKSUM_SIZE as i64)))?;
    let actual = cursor.read_u32::<LittleEndian>()?;
    assert_eq!(offset, actual as u64);

    // チェックサムを確認
    let mut hasher = hasher();
    hasher.write_all(&buffer[..(i + (u32::BITS) as usize / 8)])?;
    let checksum = hasher.finish();
    let actual = cursor.read_u64::<LittleEndian>()?;
    assert_eq!(checksum, actual);

    assert_eq!(buffer.len(), cursor.stream_position()? as usize);
  }
  Ok(())
}

#[test]
fn verify_the_written_data_can_be_read_correctly_with_check() {
  for i in 0..256 {
    // ランダムなバイト値を書き込み
    let expected = {
      let mut expected = Vec::with_capacity(i);
      for j in 0..i {
        expected.push((splitmix64((i * 1024 + j) as u64) & 0xFF) as u8);
      }
      expected
    };
    let actual = {
      let mut buffer = Vec::new();
      let mut w = ChecksumWrite::new(&mut buffer);
      w.write_all(&expected).unwrap();
      w.write_delimiter().unwrap();
      buffer
    };
    assert!(actual.len() == expected.len() + OFFSET_AND_CHECKSUM_SIZE);

    // チェックサムによる検証付きで読み出せることを確認
    let mut cursor = Cursor::new(actual.clone());
    let mut r = ChecksumRead::new(&mut cursor);
    let mut buffer = vec![0u8; expected.len()];
    r.read_exact(&mut buffer).unwrap();
    assert_eq!(expected, buffer);
    r.check_delimiter().unwrap();

    // すべての位置のビットを反転
    for bit in 0..(actual.len() * 8) {
      let byte = bit / 8;
      let bit = bit % 8;
      let mask = 1 << (7 - bit);

      // 検証が失敗することを確認
      let mut corrupted = actual.clone();
      corrupted[byte] ^= mask;
      let mut cursor = Cursor::new(&corrupted);
      let mut r = ChecksumRead::new(&mut cursor);
      r.read_exact(&mut vec![0u8; expected.len()]).unwrap();
      let result = r.check_delimiter();
      assert!(
        matches!(result, Err(Error::ChecksumVerificationFailed { .. }))
          || (byte >= expected.len() && matches!(result, Err(Error::IncorrectEntryHeadOffset { .. }))),
        "{result:?} {actual:?} <> {corrupted:?} @ {byte}.{bit}"
      );
      assert_eq!(actual.len(), cursor.stream_position().unwrap() as usize);
    }
  }
}
