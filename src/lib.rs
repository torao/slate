//! `bht` crate represents Banded Hash Tree -- an implementation of a list structure with Hash Tree
//! (Merkle Tree) that stores a complete history of additive changes in that tree structure, with
//! efficient append characteristics for practical storage device. This allows data to be appended
//! and, like a typical hash tree, can be used to verify data corruption or tampering with very
//! small amounts of data.
//!
//! See also [my personal research page for more detail](https://hazm.at/mox/algorithm/structural-algorithm/banded-hash-tree/index.html).
//!
//! # Examples
//!
//! ```rust
//! use bht::{MemStorage, BHT, Value, Node};
//! let mut db = BHT::new(MemStorage::new()).unwrap();
//!
//! // Returns None for non-existent indices.
//! let mut query = db.query().unwrap();
//! assert_eq!(None, query.get(1).unwrap());
//!
//! // The first value is considered to index 1, and they are simply incremented thereafter.
//! let first = "first".as_bytes();
//! let root = db.append(first).unwrap();
//! let mut query = db.query().unwrap();
//! assert_eq!(1, root.i);
//! assert_eq!(first, query.get(root.i).unwrap().unwrap());
//!
//! // Similar to the typical hash tree, you can refer to a verifiable value using root hash.
//! let second = "second".as_bytes();
//! let third = "third".as_bytes();
//! db.append(second).unwrap();
//! let root = db.append(third).unwrap();
//! let mut query = db.query().unwrap();
//! let values = query.get_values_with_hashes(2, 0).unwrap().unwrap();
//! assert_eq!(1, values.values.len());
//! assert_eq!(Value::new(2, second.to_vec()), values.values[0]);
//! assert_eq!(Node::new(3, 2, root.hash), values.root());
//!
//! // By specifying `j` greater than 0, you can refer to contiguous values that belongs to
//! // the binary subtree. The following refers to the values belonging to intermediate nodes b₂₁.
//! let values = query.get_values_with_hashes(2, 1).unwrap().unwrap();
//! assert_eq!(2, values.values.len());
//! assert_eq!(Value::new(1, first.to_vec()), values.values[0]);
//! assert_eq!(Value::new(2, second.to_vec()), values.values[1]);
//! assert_eq!(Node::new(3, 2, root.hash), values.root());
//! ```
//!
use std::cmp::min;
use std::fmt::{Debug, Display, Formatter};
use std::fs::*;
use std::io;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::{Arc, LockResult, RwLock};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use highway::{HighwayHasher, Key};

use crate::checksum::{HashRead, HashWrite};
use crate::error::Detail;
use crate::error::Detail::*;
use crate::model::{range, NthGenHashTree};

pub(crate) mod checksum;
pub mod error;
pub mod inspect;
pub mod model;

#[cfg(test)]
pub mod test;

/// bht クレートで使用する標準 Result。[`error::Detail`] も参照。
pub type Result<T> = std::result::Result<T, error::Detail>;

/// ハッシュ木を保存する抽象化されたストレージです。read 用または read + write 用のカーソル参照を実装することで
/// 任意のデバイスに直列化することができます。
pub trait Storage {
  /// このストレージに対する read または read + write 用のカーソルを作成します。
  fn open(&self, writable: bool) -> Result<Box<dyn Cursor>>;
}

/// ローカルファイルシステムのパスをストレージとして使用する実装です。
impl<P: AsRef<Path>> Storage for P {
  fn open(&self, writable: bool) -> Result<Box<dyn Cursor>> {
    let file = OpenOptions::new().read(true).write(writable).create(writable).open(self);
    match file {
      Ok(file) => Ok(Box::new(file)),
      Err(err) => Err(Detail::FailedToOpenLocalFile {
        file: self.as_ref().to_str().map(|s| s.to_string()).unwrap_or(self.as_ref().to_string_lossy().to_string()),
        message: err.to_string(),
      }),
    }
  }
}

/// メモリ上の領域をストレージとして使用する実装です。`drop()` された時点で記録していた内容が消滅するためテストや
/// 調査での使用を想定しています。
pub struct MemStorage {
  buffer: Arc<RwLock<Vec<u8>>>,
}

impl MemStorage {
  /// 揮発性メモリを使用するストレージを構築します。
  pub fn new() -> MemStorage {
    Self::with(Arc::new(RwLock::new(Vec::<u8>::with_capacity(4 * 1024))))
  }

  /// 指定されたアトミック参照カウント/RWロック付きの可変バッファを使用するストレージを構築します。これは調査の目的で
  /// 外部からストレージの内容を参照することを想定しています。
  pub fn with(buffer: Arc<RwLock<Vec<u8>>>) -> MemStorage {
    MemStorage { buffer }
  }
}

impl Storage for MemStorage {
  fn open(&self, writable: bool) -> Result<Box<dyn Cursor>> {
    Ok(Box::new(MemCursor { writable, position: 0, buffer: self.buffer.clone() }))
  }
}

struct MemCursor {
  writable: bool,
  position: usize,
  buffer: Arc<RwLock<Vec<u8>>>,
}

impl Cursor for MemCursor {}

impl io::Seek for MemCursor {
  fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
    self.position = match pos {
      io::SeekFrom::Start(position) => position as usize,
      io::SeekFrom::End(position) => {
        let mut buffer = lock2io(self.buffer.write())?;
        let new_position = (buffer.len() as i64 + position) as usize;
        while buffer.len() < new_position {
          buffer.push(0u8);
        }
        new_position
      }
      io::SeekFrom::Current(position) => (self.position as i64 + position) as usize,
    };
    Ok(self.position as u64)
  }
}

impl io::Read for MemCursor {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let buffer = lock2io(self.buffer.read())?;
    let length = min(buf.len(), buffer.len() - self.position);
    (&mut buf[..]).write_all(&buffer[self.position..self.position + length])?;
    self.position += length;
    Ok(length)
  }
}

impl io::Write for MemCursor {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    if !self.writable {
      return Err(io::Error::from(io::ErrorKind::PermissionDenied));
    }
    let mut buffer = lock2io(self.buffer.write())?;
    let length = buffer.write(buf)?;
    self.position += length;
    Ok(length)
  }

  fn flush(&mut self) -> io::Result<()> {
    Ok(())
  }
}

/// `LockResult` を `io::Result` に変換します。
#[inline]
fn lock2io<T>(result: LockResult<T>) -> io::Result<T> {
  result.map_err(|err| io::Error::new(io::ErrorKind::Other, err.to_string()))
}

/// ストレージからデータの入出力を行うためのカーソルです。
pub trait Cursor: io::Seek + io::Read + io::Write {}

impl Cursor for File {}

/// BHT がインデックス i として使用する整数の型です。`u64` を表しています。
///
/// 64-bit がアプリケーションへの適用に大きすぎる場合 `small_index` feature を指定することで `u32` に変更する
/// ことができます。
///
pub type Index = model::Index;

/// [`Index`] 型のビット幅を表す定数です。64 を表しています。
///
/// コンパイル時に `small_index` feature を指定することでこの定数は 32 となります。
///
pub const INDEX_SIZE: u8 = model::INDEX_SIZE;

/// ハッシュ木を構成するノードを表します。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct Node {
  /// このノードのインデックス。
  pub i: Index,
  /// このノードの高さ。
  pub j: u8,
  /// このノードのハッシュ値。この値は [`Hash::hash()`] によって算出されています。
  pub hash: Hash,
}

impl Node {
  pub fn new(i: Index, j: u8, hash: Hash) -> Node {
    Node { i, j, hash }
  }
  fn for_node(node: &MetaInfo) -> Node {
    Self::new(node.address.i, node.address.j, node.hash.clone())
  }

  /// このノードを左枝、`right` ノードを右枝とする親ノードを算出します。
  pub fn parent(&self, right: &Node) -> Node {
    debug_assert!(self.i < right.i);
    debug_assert!(self.j >= right.j);
    let i = right.i;
    let j = self.j + 1;
    let hash = self.hash.combine(&right.hash);
    Node::new(i, j, hash)
  }
}

impl Display for Node {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.write_str(&format!("{},{}:{}", self.i, self.j, hex(&self.hash.value)))
  }
}

/// ハッシュ木に保存されている値を参照します。
#[derive(PartialEq, Eq, Debug)]
pub struct Value {
  /// この値のインデックス。
  pub i: Index,
  /// この値のバイナリ値。
  pub value: Vec<u8>,
}

impl Value {
  pub fn new(i: Index, value: Vec<u8>) -> Value {
    Value { i, value }
  }
  /// この値のハッシュ値を算出します。
  pub fn hash(&self) -> Hash {
    Hash::hash(&self.value)
  }
  pub fn to_node(&self) -> Node {
    Node::new(self.i, 0u8, self.hash())
  }
}

impl Display for Value {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.write_str(&format!("{}:{}", self.i, hex(&self.value)))
  }
}

/// ハッシュ木から取得した、経路の分岐先のハッシュ値を含む値のセットです。値のハッシュ値と分岐ノードのハッシュ値から
/// ルートハッシュを算出し、クライアントが持つルートハッシュと比較することで、取得した値が改変されていないことを検証
/// することができます。
#[derive(Debug)]
pub struct ValuesWithBranches {
  pub values: Vec<Value>,
  pub branches: Vec<Node>,
}

impl ValuesWithBranches {
  pub fn new(values: Vec<Value>, branches: Vec<Node>) -> ValuesWithBranches {
    // values は連続していなければならない
    #[cfg(debug_assertions)]
    for i in 0..values.len() - 1 {
      debug_assert_eq!(values[i].i + 1, values[i + 1].i);
    }
    ValuesWithBranches { values, branches }
  }

  /// この結果から得られるルートノードをルートハッシュ付きで算出します。
  pub fn root(&self) -> Node {
    // すべての値をハッシュ値に変換する
    let mut hashes = self.values.iter().map(|value| value.to_node()).collect::<Vec<Node>>();

    // 値から算出したハッシュ値を折りたたむ
    while hashes.len() > 1 {
      // hashes の要素を 2 つ一組で折りたたむ (要素数が奇数の場合は最も右もノードが一過性の中間ノード)
      for k in 0..hashes.len() / 2 {
        let left = &hashes[k * 2];
        let right = &hashes[k * 2 + 1];
        hashes[k] = left.parent(&right);
      }
      // 折りたたまれていない一過性の中間ノードは次に持ち越す
      let fraction = if hashes.len() % 2 != 0 {
        let len = hashes.len();
        hashes[len / 2] = hashes.pop().unwrap();
        1
      } else {
        0
      };
      hashes.truncate(hashes.len() / 2 + fraction);
    }

    // 経路から分岐したノードのハッシュ値と統合しルートノードを算出する
    let mut folding = hashes.remove(0);
    for k in 0..self.branches.len() {
      let branch = &self.branches[self.branches.len() - k - 1];
      let (left, right) = if folding.i < branch.i { (&folding, branch) } else { (branch, &folding) };
      folding = left.parent(&right);
    }
    folding
  }
}

// --------------------------------------------------------------------------

/// [`Hash::hash()`] によって得られるハッシュ値のバイトサイズを表す定数です。デフォルトの `feature = "sha256"`
/// ビルドでは 32 を表します。
pub const HASH_SIZE: usize = {
  #[cfg(feature = "highwayhash64")]
  {
    8
  }
  #[cfg(any(feature = "sha224", feature = "sha512_224"))]
  {
    28
  }
  #[cfg(any(feature = "sha256", feature = "sha512_256"))]
  {
    32
  }
  #[cfg(feature = "sha512")]
  {
    64
  }
};

/// ハッシュ木が使用するハッシュ値です。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct Hash {
  pub value: [u8; HASH_SIZE],
}

impl Hash {
  pub fn new(hash: [u8; HASH_SIZE]) -> Hash {
    Hash { value: hash }
  }

  /// 指定された値をハッシュ化します。
  pub fn hash(value: &[u8]) -> Hash {
    #[cfg(feature = "highwayhash64")]
    {
      use highway::HighwayHash;
      let mut builder = HighwayBuilder::default();
      builder.write_all(value).unwrap();
      Hash::new(builder.finalize64().to_le_bytes())
    }
    #[cfg(not(feature = "highwayhash64"))]
    {
      use sha2::Digest;
      #[cfg(feature = "sha224")]
      use sha2::Sha224 as Sha2;
      #[cfg(any(feature = "sha256"))]
      use sha2::Sha256 as Sha2;
      #[cfg(feature = "sha512")]
      use sha2::Sha512 as Sha2;
      #[cfg(feature = "sha512/224")]
      use sha2::Sha512Trunc224 as Sha2;
      #[cfg(feature = "sha512/256")]
      use sha2::Sha512Trunc256 as Sha2;
      let output = Sha2::digest(value);
      debug_assert_eq!(HASH_SIZE, output.len());
      let mut hash = [0u8; HASH_SIZE];
      (&mut hash[..]).write_all(&output).unwrap();
      Hash::new(hash)
    }
  }

  /// 指定されたハッシュ値と連結したハッシュ値 `hash(self.hash || other.hash)` を算出します。
  pub fn combine(&self, other: &Hash) -> Hash {
    let mut value = [0u8; HASH_SIZE * 2];
    value[..HASH_SIZE].copy_from_slice(&self.value);
    value[HASH_SIZE..].copy_from_slice(&other.value);
    Hash::hash(&value)
  }

  pub fn to_str(&self) -> String {
    hex(&self.value)
  }
}

/// ノード b_{i,j} を含むエントリがストレージ上のどこに位置するかを表します。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
struct Address {
  /// ハッシュ木のリスト構造上での位置。1 から開始し [`Index`] の最大値までの値を取ります。
  pub i: Index,
  /// このノードの高さ (最も遠い葉ノードまでの距離)。0 の場合、ノードが葉ノードであることを示しています。最大値は
  /// [`INDEX_SIZE`] です。
  pub j: u8,
  /// このノードが格納されているエントリのストレージ先頭からの位置です。
  pub position: u64,
}

impl Address {
  pub fn new(i: Index, j: u8, position: u64) -> Address {
    Address { i, j, position }
  }
}

/// ハッシュ値を含む、ノード b_{i,j} の属性情報を表します。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
struct MetaInfo {
  pub address: Address,
  pub hash: Hash,
}

impl MetaInfo {
  pub fn new(address: Address, hash: Hash) -> MetaInfo {
    MetaInfo { address, hash }
  }
}

impl Display for MetaInfo {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.write_str(&format!("Node({},{}@{}){}", self.address.i, self.address.j, self.address.position, self.hash.to_str()))
  }
}

/// 左右の枝を持つ中間ノードを表します。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
struct INode {
  pub meta: MetaInfo,
  /// 左枝のノード
  pub left: Address,
  /// 右枝のノード
  pub right: Address,
}

impl INode {
  pub fn new(meta: MetaInfo, left: Address, right: Address) -> INode {
    INode { meta, left, right }
  }
}

/// 値を持つ葉ノードを表します。
#[derive(PartialEq, Eq, Debug)]
struct ENode {
  pub meta: MetaInfo,
  pub payload: Vec<u8>,
}

#[derive(Eq, PartialEq, Debug)]
enum RootRef<'a> {
  None,
  INode(&'a INode),
  ENode(&'a ENode),
}

#[derive(PartialEq, Eq, Debug)]
struct Entry {
  enode: ENode,
  inodes: Vec<INode>,
}

// --------------------------------------------------------------------------

/// HighwayHash でチェックサム用のハッシュ値を生成するためのキー (256-bit 固定値)。
const CHECKSUM_HW64_KEY: [u64; 4] = [0xFA5015F2E22BCFC6u64, 0xCE5A4ED9A4025C80, 0x16B9731717F6315E, 0x0F34D06AE93BD8E9];

/// ペイロード (値) の最大バイトサイズを表す定数です。2GB (2,147,483,647 bytes) を表します。
///
/// トレイラーの offset 値を u32 にするためにはエントリの直列化表現を最大でも `u32::MAX` とする必要があります。
/// したがって任意帳のペイロードは 2GB までとします。この定数はビットマスクとしても使用するため 1-bit の連続で
/// 構成されている必要があります。
///
pub const MAX_PAYLOAD_SIZE: usize = 0x7FFFFFFF;

/// BHT ファイルの先頭に記録される 3 バイトの識別子を表す定数です。値は Unicode でのdeciduous tree 🌲 (U+1F332)
/// に由来します。
pub const STORAGE_IDENTIFIER: [u8; 3] = [0x01u8, 0xF3, 0x33];

/// 識別子に続いて配置される、この実装におけるストレージフォーマットのバージョンです。現在は 1 を使用します。
pub const STORAGE_VERSION: u8 = 1;

/// 使用しようとしているストレージと互換性があるかを確認します。
fn is_version_compatible(version: u8) -> bool {
  version <= STORAGE_VERSION
}

#[derive(PartialEq, Eq, Debug)]
struct CacheInner {
  last_entry: Entry,
  model: NthGenHashTree,
}

#[derive(PartialEq, Eq, Debug)]
struct Cache(Option<CacheInner>);

impl Cache {
  fn new(last_entry: Entry, model: NthGenHashTree) -> Self {
    debug_assert_eq!(model.n(), last_entry.enode.meta.address.i);
    Cache(Some(CacheInner { last_entry, model }))
  }
  fn from_entry(last_entry: Option<Entry>) -> Self {
    let inner = if let Some(last_entry) = last_entry {
      let n = last_entry.enode.meta.address.i;
      let model = NthGenHashTree::new(n);
      Some(CacheInner { last_entry, model })
    } else {
      None
    };
    Cache(inner)
  }

  fn last_entry(&self) -> Option<&Entry> {
    if let Some(CacheInner { last_entry, .. }) = &self.0 {
      Some(last_entry)
    } else {
      None
    }
  }

  fn root(&self) -> Option<Node> {
    self
      .last_entry()
      .map(|e| e.inodes.last().map(|i| &i.meta).unwrap_or(&e.enode.meta))
      .map(|root| Node::new(root.address.i, root.address.j, root.hash))
  }

  fn root_ref<'a>(&self) -> RootRef {
    self
      .last_entry()
      .map(|e| e.inodes.last().map(|i| RootRef::INode(i)).unwrap_or(RootRef::ENode(&e.enode)))
      .unwrap_or(RootRef::None)
  }

  fn n(&self) -> Index {
    self.last_entry().map(|e| e.enode.meta.address.i).unwrap_or(0)
  }
}

/// ストレージ上に直列化された Banded Hash Tree を表す木構造に対する操作を実装します。
pub struct BHT<S: Storage> {
  storage: Box<S>,
  latest_cache: Arc<Cache>,
}

impl<S: Storage> BHT<S> {
  /// 指定された [`Storage`] に直列化されたハッシュ木を保存する BHT を構築します。
  ///
  /// ストレージに [`std::path::Path`] や [`std::path::PathBuf`] のようなパスを指定したするとそのファイルに
  /// 直列化されたハッシュ木を保存します。テストや検証目的ではメモリ上にハッシュ木を直列化する [`MemStorage`] を
  /// 使用することができます。ストレージは抽象化されているため独自の [`Storage`] 実装を使用することができます。
  ///
  /// # Examples
  ///
  /// 以下はシステムのテンポラリディレクトリ上の `mbht-example.db` にハッシュ木を直列化する例です。
  ///
  /// ```rust
  /// use bht::{BHT,Storage,Result};
  /// use std::env::temp_dir;
  /// use std::fs::remove_file;
  /// use std::path::PathBuf;
  ///
  /// fn append_and_get(file: &PathBuf) -> Result<()>{
  ///   let mut db = BHT::new(file)?;
  ///   let root = db.append(&vec![0u8, 1, 2, 3])?;
  ///   assert_eq!(Some(vec![0u8, 1, 2, 3]), db.query()?.get(root.i)?);
  ///   Ok(())
  /// }
  ///
  /// let mut path = temp_dir();
  /// path.push("bht-example.db");
  /// append_and_get(&path).expect("test failed");
  /// remove_file(path.as_path()).unwrap();
  /// ```
  pub fn new(storage: S) -> Result<BHT<S>> {
    let gen_cache = Arc::new(Cache::from_entry(None));
    let mut db = BHT { storage: Box::new(storage), latest_cache: gen_cache };
    db.init()?;
    Ok(db)
  }

  /// 現在の木構造のルートノードを参照します。
  pub fn root(&self) -> Option<Node> {
    self.latest_cache.root()
  }

  /// 木構造の現在の世代 (リストとして何個の要素を保持しているか) を返します。
  pub fn n(&self) -> Index {
    self.latest_cache.n()
  }

  /// この BHT の現在の高さを参照します。ノードが一つも含まれていない場合は 0 を返します。
  pub fn height(&self) -> u8 {
    self.root().map(|root| root.j).unwrap_or(0)
  }

  /// この BHT のルートハッシュを参照します。一つのノードも含まれていない場合は `None` を返します。
  pub fn root_hash(&self) -> Option<Hash> {
    self.root().map(|root| root.hash)
  }

  pub fn storage(&self) -> &S {
    self.storage.as_ref()
  }

  fn init(&mut self) -> Result<()> {
    let mut cursor = self.storage.open(true)?;
    let length = cursor.seek(io::SeekFrom::End(0))?;
    match length {
      0 => {
        // マジックナンバーの書き込み
        cursor.write_all(&STORAGE_IDENTIFIER)?;
        cursor.write_u8(STORAGE_VERSION)?;
      }
      1..=3 => return Err(FileIsNotContentsOfLMTHTree { message: "bad magic number" }),
      _ => {
        // マジックナンバーの確認
        let mut buffer = [0u8; 4];
        cursor.seek(io::SeekFrom::Start(0))?;
        cursor.read_exact(&mut buffer)?;
        if buffer[..3] != STORAGE_IDENTIFIER[..] {
          return Err(FileIsNotContentsOfLMTHTree { message: "bad magic number" });
        } else if !is_version_compatible(buffer[3]) {
          return Err(IncompatibleVersion(buffer[3] >> 4, buffer[3] & 0x0F));
        }
      }
    }

    let length = cursor.seek(io::SeekFrom::End(0))?;
    let tail = if length == 4 {
      None
    } else {
      // 末尾のエントリを読み込み
      back_to_safety(cursor.as_mut(), 4 + 8, "The first entry is corrupted.")?;
      let offset = cursor.read_u32::<LittleEndian>()?;
      back_to_safety(cursor.as_mut(), offset + 4, "The last entry is corrupted.")?;
      let entry = read_entry(&mut cursor, 0)?;
      if cursor.stream_position()? != length {
        // 壊れたストレージから読み込んだ offset が、たまたまどこかの正しいエントリ境界を指していた場合、正しく
        // 読み込めるが結果となる位置は末尾と一致しない。
        let msg = "The last entry is corrupted.".to_string();
        return Err(DamagedStorage(msg));
      }
      Some(entry)
    };

    // キャッシュを更新
    let new_cache = Cache::from_entry(tail);
    self.latest_cache = Arc::new(new_cache);

    Ok(())
  }

  /// 指定された値をこの BHT に追加します。
  ///
  /// # Returns
  /// この操作によって更新されたルートノードを返します。このルートノードは新しい木構造のルートハッシュである
  /// `hash` に加えて、ハッシュ木に含まれる要素数 `i`、ハッシュ木の高さ `j` を持ちます。
  ///
  pub fn append(&mut self, value: &[u8]) -> Result<Node> {
    if value.len() > MAX_PAYLOAD_SIZE {
      return Err(TooLargePayload { size: value.len() });
    }

    let mut cursor = self.storage.open(true)?;

    // 葉ノードの構築
    let position = cursor.seek(SeekFrom::End(0))?;
    let i = self.latest_cache.root().map(|node| node.i + 1).unwrap_or(1);
    let hash = Hash::hash(value);
    let enode = ENode { meta: MetaInfo::new(Address::new(i, 0, position), hash), payload: Vec::from(value) };

    // 中間ノードの構築
    let mut inodes = Vec::<INode>::with_capacity(INDEX_SIZE as usize);
    let mut right_hash = enode.meta.hash;
    let gen = NthGenHashTree::new(i);
    let mut right_to_left_inodes = gen.inodes();
    right_to_left_inodes.reverse();
    for n in right_to_left_inodes.iter() {
      debug_assert_eq!(i, n.node.i);
      debug_assert_eq!(n.node.i, n.right.i);
      debug_assert!(n.node.j > n.right.j);
      debug_assert!(n.left.j >= n.right.j);
      if let Some(left) = Query::get_node(&self.latest_cache, &mut cursor, n.left.i, n.left.j)? {
        let right = Address::new(n.right.i, n.right.j, position);
        let hash = left.hash.combine(&right_hash);
        let node = MetaInfo::new(Address::new(n.node.i, n.node.j, position), hash);
        let inode = INode::new(node, left.address, right);
        inodes.push(inode);
        right_hash = hash;
      } else {
        // 内部の木構造とストレージ上のデータが矛盾している
        return inconsistency(format!("cannot find the node b_{{{},{}}}", n.left.i, n.left.j));
      }
    }

    // 返値のための高さとルートハッシュを取得
    let (j, root_hash) =
      if let Some(inode) = inodes.last() { (inode.meta.address.j, inode.meta.hash) } else { (0u8, enode.meta.hash) };

    // エントリを書き込んで状態を更新
    cursor.seek(SeekFrom::End(0))?;
    let entry = Entry { enode, inodes };
    write_entry(&mut cursor, &entry)?;

    // キャッシュを更新
    self.latest_cache = Arc::new(Cache::new(entry, gen));

    Ok(Node::new(i, j, root_hash))
  }

  pub fn query(&self) -> Result<Query> {
    let cursor = self.storage.open(false)?;
    let gen = self.latest_cache.clone();
    Ok(Query { cursor, gen })
  }
}

pub struct Query {
  cursor: Box<dyn Cursor>,
  gen: Arc<Cache>,
}

impl Query {
  /// このクエリーが対象としている木構造の世代を参照します。
  pub fn n(&self) -> Index {
    self.gen.n()
  }

  /// 範囲外のインデックス (0 を含む) を指定した場合は `None` を返します。
  pub fn get(&mut self, i: Index) -> Result<Option<Vec<u8>>> {
    if let Some(node) = Self::get_node(self.gen.as_ref(), &mut self.cursor, i, 0)? {
      self.cursor.seek(io::SeekFrom::Start(node.address.position))?;
      let entry = read_entry_without_check(&mut self.cursor, node.address.position, node.address.i)?;
      let Entry { enode: ENode { payload, .. }, .. } = entry;
      Ok(Some(payload))
    } else {
      Ok(None)
    }
  }

  /// 葉ノード b_i の値を中間ノードのハッシュ値付きで取得します。
  #[inline]
  pub fn get_with_hashes(&mut self, i: Index) -> Result<Option<ValuesWithBranches>> {
    self.get_values_with_hashes(i, 0)
  }

  /// 指定されたノード b_{i,j} をルートとする部分木に含まれているすべての値 (葉ノード) を中間ノードのハッシュ値
  /// 付きで取得します。この結果から算出されるルートハッシュを使用して、値のデータが破損や改ざんされていないことを
  /// 検証することができます。
  ///
  /// # Returns
  /// 返値には範囲に含まれる 1 個以上の値と、b_{i,j} への経路から分岐したノードが含まれています。ここで得られる
  /// 値の範囲は [model::range(i,j)](range) を使って算出することができます。b_{i,j} をルートとする
  /// [部分木が完全二分木](model::is_pbst) の場合、返値の数は `1 << j` 個になります。完全二分木でない場合は
  /// `1 << j` より少ない個数となります。
  ///
  /// `i` に 0 を含む範囲外のインデックスを指定した場合は `None` を返します。
  ///
  /// # Example
  /// ```rust
  /// use bht::{BHT, MemStorage, Hash};
  /// use lmtht::model::{range, is_pbst};
  ///
  /// let mut db = BHT::new(MemStorage::new()).unwrap();
  /// let mut latest_root_hash = Hash::hash(&vec![]);
  /// for i in 0u32..100 {
  ///   let current_root = db.append(&i.to_le_bytes()).unwrap();
  ///   latest_root_hash = current_root.hash;
  /// }
  /// let mut query = db.query().unwrap();
  /// let values = query.get_values_with_hashes(40, 3).unwrap().unwrap();
  /// assert!(is_pbst(40, 3));
  /// assert_eq!(1 << 3, values.values.len());
  /// assert_eq!(*range(40, 3).start(), values.values[0].i);
  /// assert_eq!(*range(40, 3).end(), values.values[(1 << 3) - 1].i);
  /// assert_eq!(latest_root_hash, values.root().hash);
  /// ```
  ///
  pub fn get_values_with_hashes(&mut self, i: Index, j: u8) -> Result<Option<ValuesWithBranches>> {
    let (last_entry, model) = if let Some(CacheInner { last_entry, model }) = &self.gen.0 {
      if i == 0 || i > model.n() {
        return Ok(None);
      }
      (last_entry, model)
    } else {
      return Ok(None);
    };
    let root = match self.gen.root_ref() {
      RootRef::INode(inode) => *inode,
      RootRef::ENode(enode) => {
        self.cursor.seek(SeekFrom::Start(enode.meta.address.position))?;
        let Entry { enode: ENode { payload, .. }, .. } =
          read_entry_without_check(&mut self.cursor, enode.meta.address.position, i)?;
        return Ok(Some(ValuesWithBranches { values: vec![Value { i, value: payload }], branches: vec![] }));
      }
      RootRef::None => return Ok(None),
    };
    let path = match model.path_to(i, j) {
      Some(path) => path,
      None => return Ok(None),
    };
    debug_assert_eq!(model.root().i, root.meta.address.i);
    debug_assert_eq!(model.root().j, root.meta.address.j);

    // 目的のノードまで経路を移動しながら分岐のハッシュ値を取得する
    let mut prev = root;
    let mut inodes = last_entry.inodes.clone();
    let mut branches = Vec::<Node>::with_capacity(INDEX_SIZE as usize);
    for step in path.steps.iter().map(|s| s.step) {
      // 左枝側のエントリの INode を読み込み (右枝側のノードは inodes に含まれている)
      self.cursor.seek(SeekFrom::Start(prev.left.position))?;
      let left_inodes = read_inodes(&mut self.cursor, prev.left.position)?;

      // 左右どちらの枝が次のノードでどちらが分岐のノードかを判断
      let (next, next_inodes, branch, branch_inodes) = if prev.left.i == step.i && prev.left.j == step.j {
        (&prev.left, left_inodes, &prev.right, inodes)
      } else {
        debug_assert!(prev.right.i == step.i && prev.right.j == step.j);
        (&prev.right, inodes, &prev.left, left_inodes)
      };

      // 分岐したノードのハッシュ値付きの情報を保存
      if branch.j > 0 {
        // INode として分岐したノードを参照して保存
        if let Some(inode) = branch_inodes.iter().find(|n| n.meta.address.j == branch.j) {
          debug_assert!(inode.meta.address == *branch);
          branches.push(Node::for_node(&inode.meta));
        } else {
          return inconsistency(format!(
            "in searching for b_{{{},{}}} in T_{}, branch inode b_{{{}, {}}} isn't included in {:?}",
            i,
            j,
            self.n(),
            branch.i,
            branch.j,
            branch_inodes
          ));
        }
      } else {
        // ENode として分岐したノードを読み込んで保存
        self.cursor.seek(SeekFrom::Start(branch.position))?;
        let entry = read_entry_without_check(&mut self.cursor, branch.position, branch.i)?;
        branches.push(Node::for_node(&entry.enode.meta));
      }

      if next.j == 0 {
        debug_assert_eq!((i, j), (next.i, next.j), "branch={:?}", branch);
        self.cursor.seek(SeekFrom::Start(next.position))?;
        let Entry { enode: ENode { payload, .. }, .. } =
          read_entry_without_check(&mut self.cursor, next.position, next.i)?;
        let values = vec![Value { i: next.i, value: payload }];
        return Ok(Some(ValuesWithBranches::new(values, branches)));
      }

      // 次のノードに移動
      if let Some(inode) = next_inodes.iter().find(|node| node.meta.address == *next) {
        prev = *inode;
        inodes = next_inodes;
      } else {
        return inconsistency(format!(
          "in searching for ({},{}), the inode ({}, {}) on the route isn't included in {:?}",
          i, j, next.i, next.j, next_inodes
        ));
      }
    }

    // 目的のノードに含まれている値を取得する
    let values = self.get_values_belonging_to(&prev)?;
    Ok(Some(ValuesWithBranches::new(values, branches)))
  }

  fn get_node(gen: &Cache, cursor: &mut Box<dyn Cursor>, i: Index, j: u8) -> Result<Option<MetaInfo>> {
    if let Some((position, _)) = Self::get_entry_position(gen, cursor, i, false)? {
      cursor.seek(io::SeekFrom::Start(position))?;
      if j == 0 {
        let entry = read_entry_without_check(cursor, position, i)?;
        Ok(Some(entry.enode.meta))
      } else {
        let inodes = read_inodes(cursor, position)?;
        Ok(inodes.iter().find(|inode| inode.meta.address.j == j).map(|inode| inode.meta))
      }
    } else {
      Ok(None)
    }
  }

  /// 指定された `inode` をルートとする部分木に含まれているすべての値を参照します。読み出し用のカーソルは `inode`
  /// の位置を指している必要はありません。
  fn get_values_belonging_to(&mut self, inode: &INode) -> Result<Vec<Value>> {
    // inode を左枝方向に葉に到達するまで移動
    let mut mover = *inode;
    while mover.left.j > 0 {
      self.cursor.seek(SeekFrom::Start(mover.left.position))?;
      let inodes = read_inodes(&mut self.cursor, mover.left.position)?;
      mover = match inodes.iter().find(|node| node.meta.address.j == mover.left.j) {
        Some(inode) => *inode,
        None => panic!(),
      };
    }

    let range = range(inode.meta.address.i, inode.meta.address.j);
    let (i0, i1) = (*range.start(), *range.end());
    let mut values = Vec::<Value>::with_capacity((i1 - i0) as usize);
    let mut i = mover.left.i;
    self.cursor.seek(SeekFrom::Start(mover.left.position))?;
    while i <= i1 {
      let Entry { enode: ENode { meta: node, payload }, .. } = read_entry_without_check_to_end(&mut self.cursor, i)?;
      debug_assert!(node.address.i == i);
      values.push(Value { i, value: payload });
      i += 1;
    }
    Ok(values)
  }

  /// `i` 番目のエントリの位置を参照します。この検索は現在のルートノードを基準にした探索を行います。
  fn get_entry_position(
    gen: &Cache,
    cursor: &mut Box<dyn Cursor>,
    i: Index,
    with_branch: bool,
  ) -> Result<Option<(Index, Vec<MetaInfo>)>> {
    match &gen.root_ref() {
      RootRef::INode(root) => {
        let root = (*root).clone();
        search_entry_position(cursor, &root, i, with_branch)
      }
      RootRef::ENode(root) if root.meta.address.i == i => Ok(Some((root.meta.address.position, vec![]))),
      _ => Ok(None),
    }
  }
}

/// 指定されたカーソルの現在の位置からエントリを読み込みます。
/// 正常終了時のカーソルは次のエントリを指しています。
fn read_entry<C>(r: &mut C, i_expected: Index) -> Result<Entry>
where
  C: io::Read + io::Seek,
{
  let position = r.stream_position()?;
  let mut hasher = HighwayHasher::new(Key(CHECKSUM_HW64_KEY));
  let mut r = HashRead::new(r, &mut hasher);
  let entry = read_entry_without_check(&mut r, position, i_expected)?;

  // オフセットの検証
  let offset = r.length();
  let trailer_offset = r.read_u32::<LittleEndian>()?;
  if offset != trailer_offset as u64 {
    return Err(IncorrectEntryHeadOffset { expected: trailer_offset, actual: offset });
  }

  // チェックサムの検証
  let checksum = r.finish();
  let trailer_checksum = r.read_u64::<LittleEndian>()?;
  if checksum != trailer_checksum {
    let length = offset as u32 + 4 + 8;
    return Err(ChecksumVerificationFailed { at: position, length, expected: trailer_checksum, actual: checksum });
  }

  Ok(entry)
}

/// 指定されたカーソルの現在の位置から checksum による検証なしでエントリを読み込みます。正常終了時のカーソルの位置は
/// 次のエントリの戦闘を指しています。
fn read_entry_without_check_to_end<C>(r: &mut C, i_expected: Index) -> Result<Entry>
where
  C: io::Read + io::Seek,
{
  let position = r.stream_position()?;
  let entry = read_entry_without_check(r, position, i_expected)?;
  r.seek(SeekFrom::Current(4 /* offset */ + 8 /* checksum */))?;
  Ok(entry)
}

/// 指定されたカーソルの現在の位置からエントリを読み込みます。トレイラーの offset と checksum は読み込まれない
/// ため、正常終了時のカーソルは offset の位置を指しています。
fn read_entry_without_check(r: &mut dyn io::Read, position: u64, i_expected: Index) -> Result<Entry> {
  let mut hash = [0u8; HASH_SIZE];

  // 中間ノードの読み込み
  let inodes = read_inodes(r, position)?;
  let i = inodes.first().map(|inode| inode.meta.address.i).unwrap_or(1);
  if i != i_expected && i_expected != 0 {
    return Err(Detail::IncorrectNodeBoundary { at: position });
  }

  // 葉ノードの読み込み
  let payload_size = r.read_u32::<LittleEndian>()? & MAX_PAYLOAD_SIZE as u32;
  let mut payload = Vec::<u8>::with_capacity(payload_size as usize);
  unsafe { payload.set_len(payload_size as usize) };
  r.read_exact(&mut payload)?;
  r.read_exact(&mut hash)?;
  let enode = ENode { meta: MetaInfo::new(Address::new(i, 0, position), Hash::new(hash)), payload };

  Ok(Entry { enode, inodes })
}

/// 指定されたカーソルの現在の位置をエントリの先頭としてすべての `INode` を読み込みます。正常終了した場合、カーソル
/// 位置は最後の `INode` を読み込んだ直後を指しています。
fn read_inodes(r: &mut dyn io::Read, position: u64) -> Result<Vec<INode>> {
  let mut hash = [0u8; HASH_SIZE];
  let i = r.read_u64::<LittleEndian>()?;
  let inode_count = r.read_u8()?;
  let mut right_j = 0u8;
  let mut inodes = Vec::<INode>::with_capacity(inode_count as usize);
  for _ in 0..inode_count as usize {
    let j = (r.read_u8()? & (INDEX_SIZE - 1)) + 1; // 下位 6-bit のみを使用
    let left_position = r.read_u64::<LittleEndian>()?;
    let left_i = r.read_u64::<LittleEndian>()?;
    let left_j = r.read_u8()?;
    r.read_exact(&mut hash)?;
    inodes.push(INode {
      meta: MetaInfo::new(Address::new(i, j, position), Hash::new(hash)),
      left: Address::new(left_i, left_j, left_position),
      right: Address::new(i, right_j, position),
    });
    right_j = j;
  }
  Ok(inodes)
}

/// 指定されたカーソルにエントリを書き込みます。
/// このエントリに対して書き込みが行われた長さを返します。
fn write_entry(w: &mut dyn Write, e: &Entry) -> Result<usize> {
  debug_assert!(e.enode.payload.len() <= MAX_PAYLOAD_SIZE);
  debug_assert!(e.inodes.len() <= 0xFF);

  let mut hasher = HighwayHasher::new(Key(CHECKSUM_HW64_KEY));
  let mut w = HashWrite::new(w, &mut hasher);

  // 中間ノードの書き込み
  w.write_u64::<LittleEndian>(e.enode.meta.address.i)?;
  w.write_u8(e.inodes.len() as u8)?;
  for i in &e.inodes {
    debug_assert_eq!((i.meta.address.j - 1) & (INDEX_SIZE - 1), i.meta.address.j - 1);
    w.write_u8((i.meta.address.j - 1) & (INDEX_SIZE - 1))?; // 下位 6-bit のみ保存
    w.write_u64::<LittleEndian>(i.left.position)?;
    w.write_u64::<LittleEndian>(i.left.i)?;
    w.write_u8(i.left.j)?;
    w.write_all(&i.meta.hash.value)?;
  }

  // 葉ノードの書き込み
  w.write_u32::<LittleEndian>(e.enode.payload.len() as u32)?;
  w.write_all(&e.enode.payload)?;
  w.write_all(&e.enode.meta.hash.value)?;

  // エントリ先頭までのオフセットを書き込み
  w.write_u32::<LittleEndian>(w.length() as u32)?;

  // チェックサムの書き込み
  w.write_u64::<LittleEndian>(w.finish())?;

  Ok(w.length() as usize)
}

/// `root` に指定された中間ノードを部分木構造のルートとして b_{i,*} に該当する葉ノードと中間ノードを含んでいる
/// エントリのストレージ内での位置を取得します。該当するエントリが存在しない場合は `None` を返します。
///
/// `with_branch` に true を指定した場合、返値には `root` から検索対象のノードに至るまでの分岐先のハッシュ値を
/// 持つノードが含まれます。これはハッシュツリーからハッシュ付きで値を参照するための動作です。false を指定した場合は
/// 長さ 0 の `Vec` を返します。
///
fn search_entry_position<C>(
  r: &mut C,
  root: &INode,
  i: Index,
  with_branch: bool,
) -> Result<Option<(u64, Vec<MetaInfo>)>>
where
  C: io::Read + io::Seek,
{
  if root.meta.address.i == i {
    // 指定されたルートノードが検索対象のノードの場合
    return Ok(Some((root.meta.address.position, vec![])));
  } else if i == 0 || i > root.meta.address.i {
    // インデックス 0 の特殊値を持つノードは明示的に存在しない
    return Ok(None);
  }

  let mut branches = Vec::<MetaInfo>::with_capacity(INDEX_SIZE as usize);
  let mut mover = root.clone();
  for _ in 0..INDEX_SIZE {
    // 次のノードのアドレスを参照
    let next = if i <= mover.left.i {
      read_branch(r, &mover.right, with_branch, &mut branches)?;
      mover.left
    } else if i <= mover.meta.address.i {
      read_branch(r, &mover.left, with_branch, &mut branches)?;
      mover.right
    } else {
      // 有効範囲外
      return Ok(None);
    };

    // 次のノードのアドレスが検索対象ならそのエントリの位置を返す
    if next.i == i {
      return Ok(Some((next.position, branches)));
    }

    // 末端に到達している場合は発見できなかったことを意味する
    if next.j == 0 {
      return Ok(None);
    }

    // b_{i,*} の中間ノードをロードして次の中間ノードを取得
    mover = read_inode(r, &next)?;
  }

  fn read_inode<C>(r: &mut C, addr: &Address) -> Result<INode>
  where
    C: io::Read + io::Seek,
  {
    debug_assert_ne!(0, addr.j);
    r.seek(io::SeekFrom::Start(addr.position))?;
    let inodes = read_inodes(r, addr.position)?;
    let inode = inodes.iter().find(|inode| inode.meta.address.j == addr.j);
    if let Some(inode) = inode {
      Ok(inode.clone())
    } else {
      // 内部の木構造とストレージ上のデータが矛盾している
      inconsistency(format!("entry i={} in storage doesn't contain an inode at specified level j={}", addr.i, addr.j))
    }
  }

  fn read_branch<C>(r: &mut C, addr: &Address, with_branch: bool, branches: &mut Vec<MetaInfo>) -> Result<()>
  where
    C: io::Read + io::Seek,
  {
    if with_branch {
      let branch = if addr.j == 0 {
        r.seek(io::SeekFrom::Start(addr.position))?;
        let entry = read_entry_without_check(r, addr.position, addr.i)?;
        entry.enode.meta
      } else {
        read_inode(r, &addr)?.meta
      };
      branches.push(branch);
    }
    Ok(())
  }

  // ストレージ上のデータのポインタが循環参照を起こしている
  inconsistency(format!(
    "The maximum hop count was exceeded before reaching node b_{} from node b_{{{},{}}}.\
     The data on the storage probably have circular references.",
    i, root.meta.address.i, root.meta.address.j
  ))
}

/// 指定されたカーソルを現在の位置から `distance` バイト前方に移動します。移動先がカーソルの先頭を超える場合は
/// `if_err` をメッセージとしたエラーを発生します。
#[inline]
fn back_to_safety(cursor: &mut dyn Cursor, distance: u32, if_err: &'static str) -> Result<u64> {
  let from = cursor.stream_position()?;
  let to = from - distance as u64;
  if to < STORAGE_IDENTIFIER.len() as u64 + 1 {
    Err(DamagedStorage(format!("{} (cannot move position from {} to {})", if_err, from, to)))
  } else {
    Ok(cursor.seek(io::SeekFrom::Current(-(distance as i64)))?)
  }
}

/// panic_over_inconsistency が定義されている場合は panic して内部矛盾を検出した場所を知らせる。
fn inconsistency<T>(msg: String) -> Result<T> {
  #[cfg(feature = "panic_over_inconsistency")]
  {
    panic!("{}", msg)
  }
  #[cfg(not(feature = "panic_over_inconsistency"))]
  {
    Err(InternalStateInconsistency { message: msg })
  }
}

#[inline]
fn hex(value: &[u8]) -> String {
  value.iter().map(|c| format!("{:02X}", c)).collect()
}
