use protobuf::ProtobufError;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Detail {
  // LSHTree ファイルではない
  #[error("file is not the contents of LSHTree: {message}")]
  FileIsNotContentsOfLSHTree { message: &'static str },

  // 未定義のノード識別子
  #[error("file broken: an undefined node class 0x{node_type:X} was detected in {at} byte")]
  UnknownNodeClass { at: u64, node_type: u8 },

  // チェックサム検査に失敗
  #[error("file broken: checksum verification failed for {length} bytes starting at {at}; expected {expected} but got {actual}")]
  ChecksumVerificationFailed { at: u64, length: usize, expected: u64, actual: u64 },

  #[error("I/O error: {source}")]
  Io {
    #[from]
    source: std::io::Error,
  },

  #[error("protocol buffers error: {source}")]
  Proto {
    #[from]
    source: ProtobufError,
  },
}
