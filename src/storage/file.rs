use crate::error::Error;
use crate::{BlockDevice, Result};
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

/// ローカルファイルをストレージとして使用する実装です。
pub struct FileDevice {
  /// 読み出し時にオープンするためのこのファイルのパス。
  path: PathBuf,
  /// 読み出し用にオープンするためのオプション。
  read_options: OpenOptions,
  /// 書き込み専用で、必ずファイルの末尾を指している。
  file: File,
}

impl FileDevice {
  pub fn new<P: AsRef<Path>>(path: P) -> Result<FileDevice> {
    Self::with_options(
      path,
      File::options().read(true).append(true).create(true).truncate(false).clone(),
      File::options().read(true).write(false).create(false).truncate(false).clone(),
    )
  }

  pub fn read_only<P: AsRef<Path>>(path: P) -> Result<FileDevice> {
    Self::with_options(
      path,
      File::options().read(true).write(false).create(false).truncate(false).clone(),
      File::options().read(true).write(false).create(false).truncate(false).clone(),
    )
  }

  pub fn with_options<P: AsRef<Path>>(
    path: P,
    write_options: OpenOptions,
    read_options: OpenOptions,
  ) -> Result<FileDevice> {
    let path = path.as_ref().to_path_buf();
    write_options.open(&path).map(|file| Self { path: path.clone(), read_options, file }).map_err(|err| {
      Error::FailedToOpenLocalFile {
        file: path.to_str().map(|s| s.to_string()).unwrap_or(path.to_string_lossy().to_string()),
        message: err.to_string(),
      }
    })
  }
}

impl BlockDevice for FileDevice {
  fn clone_device(&self) -> Result<Self>
  where
    Self: std::marker::Sized,
  {
    let file = self.read_options.open(&self.path)?;
    Ok(Self { path: self.path.clone(), read_options: self.read_options.clone(), file })
  }
}

impl Read for FileDevice {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    self.file.read(buf)
  }
}

impl Write for FileDevice {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    self.file.write(buf)
  }

  fn flush(&mut self) -> io::Result<()> {
    self.file.flush()
  }
}

impl Seek for FileDevice {
  fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
    self.file.seek(pos)
  }
}
