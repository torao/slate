use thiserror::Error;

#[derive(Error, Debug)]
pub enum Detail {
  // LSHTree ファイルではない
  #[error("file is not the contents of LSHTree: {message}")]
  FileIsNotContentsOfLSHTree { message: &'static str },

  // ペイロードのサイズが大きすぎる
  #[error("too large payload: {size}")]
  TooLargePayload { size: usize },

  // エントリ先頭へのオフセットが間違っている
  #[error("incorrect entry-head offset: {expected} != {actual}")]
  IncorrectEntryHeadOffset { expected: u64, actual: u32 },

  // チェックサム検査に失敗
  #[error("file broken: checksum verification failed for {length} bytes starting at {at}; expected {expected} but got {actual}")]
  ChecksumVerificationFailed { at: u64, length: u32, expected: u64, actual: u64 },

  #[error("I/O error: {source}")]
  Io {
    #[from]
    source: std::io::Error,
  },
}
