//! `slate` crate represents Stratified Hash Tree -- an implementation of a list structure with Hash
//! Tree (Merkle Tree) that stores a complete history of additive changes in that tree structure,
//! with efficient append characteristics for practical storage device. This allows data to be
//! appended and, like a typical hash tree, can be used to verify data corruption or tampering with
//! very small amounts of data.
//!
//! See also [my personal research page for more detail](https://hazm.at/mox/algorithm/structural-algorithm/stratified-hash-tree/index.html).
//!
//! # Examples
//!
//! ```rust
//! use slate::{BlockStorage, Slate, Value, Node};
//! let mut db = Slate::new(BlockStorage::memory()).unwrap();
//!
//! // Returns None for non-existent indices.
//! let mut query = db.snapshot().query().unwrap();
//! assert_eq!(None, query.get(1).unwrap());
//! assert_eq!(None, query.get(2).unwrap());
//!
//! // The first value is considered to index 1, and they are simply incremented thereafter.
//! let first = "first".as_bytes();
//! let root = db.append(first).unwrap();
//! let mut query = db.snapshot().query().unwrap();
//! assert_eq!(1, root.i);
//! assert_eq!(first, query.get(root.i).unwrap().unwrap());
//! assert_eq!(None, query.get(2).unwrap());
//!
//! // Similar to the typical hash tree, you can refer to a verifiable value using root hash.
//! let second = "second".as_bytes();
//! let third = "third".as_bytes();
//! db.append(second).unwrap();
//! let root = db.append(third).unwrap();
//! let mut query = db.snapshot().query().unwrap();
//! // TODO: replace to AuthPath
//! //let values = query.get_values_with_hashes(2, 0).unwrap().unwrap();
//! //assert_eq!(1, values.values.len());
//! //assert_eq!(Value::new(2, second.to_vec()), values.values[0]);
//! //assert_eq!(Node::new(3, 2, root.hash), values.root());
//!
//! // By specifying `j` greater than 0, you can refer to contiguous values that belongs to
//! // the binary subtree. The following refers to the values belonging to intermediate nodes b₂₁.
//! //let values = query.get_values_with_hashes(2, 1).unwrap().unwrap();
//! //assert_eq!(2, values.values.len());
//! //assert_eq!(Value::new(1, first.to_vec()), values.values[0]);
//! //assert_eq!(Value::new(2, second.to_vec()), values.values[1]);
//! //assert_eq!(Node::new(3, 2, root.hash), values.root());
//! ```
//!
use crate::error::Error;
use crate::error::Error::*;
use crate::model::{NthGenHashTree, ceil_log2, contains, subnodes};
use crate::serialize::{read_entry_from, read_inodes_from, write_entry_to, write_inodes_to};
use std::fmt::{Debug, Display, Formatter};
use std::io::{Read, Seek, Write};
use std::sync::Arc;

pub(crate) mod checksum;
pub mod error;
pub mod inspect;
pub mod model;
mod storage;
pub use storage::*;
mod serialize;

#[cfg(test)]
pub mod test;

/// slate クレートで使用する標準 Result。[`error::Error`] も参照。
pub type Result<T> = std::result::Result<T, Error>;

/// slate がインデックス i として使用する整数の型です。`u64` を表しています。
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

/// ハッシュ木に保存されている値を表します。
#[derive(PartialEq, Eq, Debug)]
pub struct Value {
  /// この値のインデックス。
  pub i: Index,
  /// この値のバイナリ値。
  pub value: Arc<Vec<u8>>,
}

impl Value {
  pub fn new(i: Index, value: Arc<Vec<u8>>) -> Value {
    Value { i, value }
  }
  /// この値のハッシュ値を算出します。
  pub fn hash(&self) -> Hash {
    Hash::from_bytes(&self.value)
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
        hashes[k] = left.parent(right);
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
      folding = left.parent(right);
    }
    folding
  }
}

// --------------------------------------------------------------------------

/// ハッシュ木が使用するハッシュ値です。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct Hash {
  pub value: [u8; Self::SIZE],
}

impl Hash {
  #[cfg(feature = "highwayhash64")]
  pub const SIZE: usize = 8;

  #[cfg(any(feature = "sha224", feature = "sha512_224"))]
  pub const SIZE: usize = 28;

  /// [`Hash::hash()`] によって得られるハッシュ値のバイトサイズを表す定数です。デフォルトの `feature = "sha256"`
  /// ビルドでは 32 を表します。
  #[cfg(any(feature = "sha256", feature = "sha512_256"))]
  pub const SIZE: usize = 32;

  #[cfg(feature = "sha512")]
  pub const SIZE: usize = 64;

  #[cfg(feature = "blake3")]
  pub const SIZE: usize = blake3::OUT_LEN;

  pub fn new(hash: [u8; Self::SIZE]) -> Hash {
    Hash { value: hash }
  }

  /// 指定された値をハッシュ化します。
  pub fn from_bytes(value: &[u8]) -> Hash {
    #[cfg(feature = "blake3")]
    {
      let mut hash = [0u8; Hash::SIZE];
      (&mut hash[..]).write_all(blake3::hash(value).as_bytes()).unwrap();
      Hash::new(hash)
    }
    #[cfg(all(not(feature = "blake3"), feature = "highwayhash64"))]
    {
      let mut builder = HighwayBuilder::default();
      builder.write_all(value).unwrap();
      Hash::new(builder.finalize64().to_le_bytes())
    }
    #[cfg(all(not(feature = "blake3"), not(feature = "highwayhash64")))]
    {
      use sha2::Digest;
      #[cfg(feature = "sha256")]
      use sha2::Sha256 as Sha2;
      #[cfg(feature = "sha512_224")]
      use sha2::Sha512Trunc224 as Sha2;
      #[cfg(feature = "sha512_256")]
      use sha2::Sha512Trunc256 as Sha2;
      let output = Sha2::digest(value);
      debug_assert_eq!(Hash::SIZE, output.len());
      let mut hash = [0u8; Hash::SIZE];
      (&mut hash[..]).write_all(&output).unwrap();
      Hash::new(hash)
    }
  }

  /// 指定されたハッシュ値と連結したハッシュ値 `hash(self.hash || other.hash)` を算出します。
  pub fn combine(&self, other: &Hash) -> Hash {
    let mut value = [0u8; Hash::SIZE * 2];
    value[..Hash::SIZE].copy_from_slice(&self.value);
    value[Hash::SIZE..].copy_from_slice(&other.value);
    Hash::from_bytes(&value)
  }

  pub fn to_str(&self) -> String {
    hex(&self.value)
  }
}

/// ノード b_{i,j} を含むエントリがストレージ上のどこに位置するかを表します。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct Address {
  /// ハッシュ木のリスト構造上での位置。1 から開始し [`Index`] の最大値までの値を取ります。
  pub i: Index,
  /// このノードの高さ (最も遠い葉ノードまでの距離)。0 の場合、ノードが葉ノードであることを示しています。最大値は
  /// [`INDEX_SIZE`] です。
  pub j: u8,
  /// このノードが格納されているエントリのストレージ内の位置です。
  pub position: Position,
}

impl Address {
  pub fn new(i: Index, j: u8, position: Position) -> Address {
    Address { i, j, position }
  }
}

/// ハッシュ値を含む、ノード b_{i,j} の属性情報を表します。
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct MetaInfo {
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
pub struct INode {
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
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ENode {
  pub meta: MetaInfo,
  pub payload: Vec<u8>,
}

impl ENode {
  pub fn new(meta: MetaInfo, payload: Vec<u8>) -> Self {
    ENode { meta, payload }
  }
}

#[derive(Eq, PartialEq, Debug)]
enum PbstRoot {
  INode(INode),
  ENode(ENode),
}

#[derive(PartialEq, Eq, Debug)]
pub struct Entry {
  enode: ENode,
  inodes: Vec<INode>,
}

impl Entry {
  pub fn new(enode: ENode, inodes: Vec<INode>) -> Self {
    debug_assert!(inodes.iter().map(|i| i.meta.address.j).collect::<Vec<_>>().windows(2).all(|w| w[0] < w[1]));
    Entry { enode, inodes }
  }
}

impl Serializable for Entry {
  fn write<W: Write>(&self, w: &mut W) -> Result<usize> {
    debug_assert!(self.enode.payload.len() <= MAX_PAYLOAD_SIZE);
    debug_assert!(self.inodes.len() <= 0xFF);
    write_entry_to(self, w)
  }

  fn read<R: Read + Seek>(r: &mut R, position: Position) -> Result<Self> {
    read_entry_from(r, position)
  }
}

pub struct INodes(Index, Vec<INode>);

impl Serializable for INodes {
  fn write<W: Write>(&self, w: &mut W) -> Result<usize> {
    write_inodes_to(self.0, &self.1, w)
  }
  fn read<R: Read + Seek>(r: &mut R, position: Position) -> Result<Self> {
    let (index, inodes) = read_inodes_from(r, position)?;
    Ok(INodes(index, inodes))
  }
}

// --------------------------------------------------------------------------

/// ペイロード (値) の最大バイトサイズを表す定数です。2GB (2,147,483,647 bytes) を表します。
///
/// トレイラーの offset 値を u32 にするためにはエントリの直列化表現を最大でも `u32::MAX` とする必要があります。
/// したがって任意帳のペイロードは 2GB までとします。この定数はビットマスクとしても使用するため 1-bit の連続で
/// 構成されている必要があります。
///
pub const MAX_PAYLOAD_SIZE: usize = 0x7FFFFFFF;

#[derive(PartialEq, Eq, Debug)]
struct CacheInner {
  last_entry: Entry,
  pbst_roots: Vec<PbstRoot>,
  model: NthGenHashTree,
}

#[derive(PartialEq, Eq, Debug)]
struct Cache(Option<CacheInner>);

impl Cache {
  pub fn new(last_entry: Entry, pbst_roots: Vec<PbstRoot>, model: NthGenHashTree) -> Self {
    debug_assert_eq!(model.n(), last_entry.enode.meta.address.i);
    Cache(Some(CacheInner { last_entry, pbst_roots, model }))
  }

  pub fn empty() -> Self {
    Cache(None)
  }

  fn last_entry(&self) -> Option<&Entry> {
    if let Some(CacheInner { last_entry, .. }) = &self.0 { Some(last_entry) } else { None }
  }

  fn root(&self) -> Option<Node> {
    self
      .last_entry()
      .map(|e| e.inodes.last().map(|i| &i.meta).unwrap_or(&e.enode.meta))
      .map(|root| Node::new(root.address.i, root.address.j, root.hash))
  }

  fn n(&self) -> Index {
    self.last_entry().map(|e| e.enode.meta.address.i).unwrap_or(0)
  }

  fn get_pbst_root(&self, i: Index, j: u8) -> PbstRoot {
    if let Some(cache) = &self.0 {
      for node in cache.pbst_roots.iter() {
        match &node {
          PbstRoot::ENode(enode) if enode.meta.address.i == i && enode.meta.address.j == j => {
            return PbstRoot::ENode(enode.clone());
          }
          PbstRoot::INode(inode) if inode.meta.address.i == i && inode.meta.address.j == j => {
            return PbstRoot::INode(*inode);
          }
          _ => (),
        }
      }
      for node in cache.last_entry.inodes.iter() {
        if node.meta.address.i == i && node.meta.address.j == j {
          return PbstRoot::INode(*node);
        }
      }
      if cache.last_entry.enode.meta.address.i == i && cache.last_entry.enode.meta.address.j == j {
        return PbstRoot::ENode(cache.last_entry.enode.clone());
      }
    }
    // キャッシュの内容が矛盾している
    panic!("the specified node b_{{{i},{j}}} doesn't exist in the cache")
  }
}

pub struct Snapshot<'a, S: Storage<Entry>> {
  cache: Arc<Cache>,
  storage: &'a S,
}

impl<'a, S: Storage<Entry>> Snapshot<'a, S> {
  pub fn revision(&self) -> Index {
    self.cache.n()
  }

  pub fn query(&self) -> Result<Query> {
    let cursor = self.storage.reader()?;
    let revision = self.cache.clone();
    Ok(Query { cursor, revision })
  }
}

/// ストレージ上に直列化された Stratified Hash Tree を表す木構造に対する操作を実装します。
pub struct Slate<S: Storage<Entry>> {
  position: Position,
  storage: S,
  latest_cache: Arc<Cache>,
}

impl<S: Storage<Entry>> Slate<S> {
  /// 指定された [`Storage`] に直列化されたハッシュ木を保存する Slate を構築します。
  ///
  /// ストレージに [`std::path::Path`] や [`std::path::PathBuf`] のようなパスを指定したするとそのファイルに
  /// 直列化されたハッシュ木を保存します。テストや検証目的ではメモリ上にハッシュ木を直列化する [`MemStorage`] を
  /// 使用することができます。ストレージは抽象化されているため独自の [`Storage`] 実装を使用することができます。
  ///
  /// # Examples
  ///
  /// 以下はシステムのテンポラリディレクトリ上の `slate-example.db` にハッシュ木を直列化する例です。
  ///
  /// ```rust
  /// use slate::{BlockStorage,Slate,Storage,Result};
  /// use std::env::temp_dir;
  /// use std::fs::remove_file;
  /// use std::path::PathBuf;
  ///
  /// fn append_and_get(file: &PathBuf) -> Result<()>{
  ///   let storage = BlockStorage::from_file(file, false)?;
  ///   let mut db = Slate::new(storage)?;
  ///   let root = db.append(&[0u8, 1, 2, 3])?;
  ///   assert_eq!(Some(vec![0u8, 1, 2, 3]), db.snapshot().query()?.get(root.i)?.map(|x| x.clone()));
  ///   Ok(())
  /// }
  ///
  /// let mut path = temp_dir();
  /// path.push("slate-example.db");
  /// append_and_get(&path).expect("test failed");
  /// remove_file(path.as_path()).unwrap();
  /// ```
  pub fn new(mut storage: S) -> Result<Slate<S>> {
    let (cache, position) = Self::load_metadata(&mut storage)?;
    Ok(Slate { position, storage, latest_cache: Arc::new(cache) })
  }

  /// 現在の木構造のルートノードを参照します。
  pub fn root(&self) -> Option<Node> {
    self.latest_cache.root()
  }

  /// 木構造の現在の世代 (リストとして何個の要素を保持しているか) を返します。
  pub fn n(&self) -> Index {
    self.latest_cache.n()
  }

  /// この Slate の現在の高さを参照します。ノードが一つも含まれていない場合は 0 を返します。
  pub fn height(&self) -> u8 {
    self.root().map(|root| root.j).unwrap_or(0)
  }

  /// この Slate のルートハッシュを参照します。一つのノードも含まれていない場合は `None` を返します。
  pub fn root_hash(&self) -> Option<Hash> {
    self.root().map(|root| root.hash)
  }

  pub fn storage(&self) -> &S {
    &self.storage
  }

  fn load_metadata(storage: &mut S) -> Result<(Cache, Position)> {
    let (latest_entry, position) = storage.boot()?;
    let cache = match latest_entry {
      Some(entry) => {
        // PBST ルートノードの読み込み
        let mut cursor = storage.reader()?;
        let mut pbst_roots = Vec::with_capacity(entry.inodes.len());
        for inode in entry.inodes.iter() {
          let position = inode.left.position;
          let i_expected = inode.left.i;
          let entry = read_entry_with_index_check(&mut cursor, position, i_expected)?;
          let Entry { enode, mut inodes } = entry;
          let pbst_root = inodes.pop().map(PbstRoot::INode).unwrap_or(PbstRoot::ENode(enode));
          pbst_roots.push(pbst_root);
        }
        let model = NthGenHashTree::new(entry.enode.meta.address.i);
        Cache::new(entry, pbst_roots, model)
      }
      None => Cache::empty(),
    };
    Ok((cache, position))
  }

  /// 指定された値をこの Slate に追加します。
  ///
  /// # Returns
  /// この操作によって更新されたルートノードを返します。このルートノードは新しい木構造のルートハッシュである
  /// `hash` に加えて、ハッシュ木に含まれる要素数 `i`、ハッシュ木の高さ `j` を持ちます。
  ///
  pub fn append(&mut self, value: &[u8]) -> Result<Node> {
    if value.len() > MAX_PAYLOAD_SIZE {
      return Err(TooLargePayload { size: value.len() });
    }

    // 葉ノードの構築
    let position = self.position;
    let i = self.latest_cache.root().map(|node| node.i + 1).unwrap_or(1);
    let hash = Hash::from_bytes(value);
    let meta = MetaInfo::new(Address::new(i, 0, position), hash);
    let enode = ENode { meta, payload: Vec::from(value) };

    // 中間ノードとその左枝にある PBST ルートの構築
    let mut inodes = Vec::<INode>::with_capacity(INDEX_SIZE as usize);
    let mut right_hash = enode.meta.hash;
    let generation = NthGenHashTree::new(i);
    let right_to_left_inodes = generation.inodes();
    let mut pbst_roots = Vec::with_capacity(ceil_log2(i) as usize);
    for n in right_to_left_inodes.iter() {
      debug_assert_eq!(i, n.node.i);
      debug_assert_eq!(n.node.i, n.right.i);
      debug_assert!(n.node.j > n.right.j);
      debug_assert!(n.left.j >= n.right.j);

      // 左枝のノード (PBST ルート) を保存
      let left_node = self.latest_cache.get_pbst_root(n.left.i, n.left.j);
      let left = match &left_node {
        PbstRoot::ENode(enode) => enode.meta,
        PbstRoot::INode(inode) => inode.meta,
      };
      pbst_roots.push(left_node);

      // 右枝のノードを保存
      let right = Address::new(n.right.i, n.right.j, position);
      let hash = left.hash.combine(&right_hash);
      let node = MetaInfo::new(Address::new(n.node.i, n.node.j, position), hash);
      let inode = INode::new(node, left.address, right);
      inodes.push(inode);
      right_hash = hash;
    }

    // 返値のための高さとルートハッシュを取得
    let (j, root_hash) =
      if let Some(inode) = inodes.last() { (inode.meta.address.j, inode.meta.hash) } else { (0u8, enode.meta.hash) };

    // エントリを書き込んで状態を更新
    let entry = Entry::new(enode, inodes);
    self.position = self.storage.put(self.position, &entry)?;

    // キャッシュを更新
    let cache = Cache(Some(CacheInner { last_entry: entry, pbst_roots, model: generation }));
    self.latest_cache = Arc::new(cache);

    Ok(Node::new(i, j, root_hash))
  }

  pub fn snapshot(&self) -> Snapshot<'_, S> {
    Snapshot { cache: self.latest_cache.clone(), storage: &self.storage }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WalkDirection {
  Left,
  Right,
  Both,
  Stop,
}

#[derive(Debug)]
pub struct AuthPath {
  pub value: Value,
  pub path: Vec<Node>,
}

pub struct Query {
  cursor: Box<dyn Reader<Entry>>,
  revision: Arc<Cache>,
}

impl Query {
  /// このクエリーが対象としている木構造の版 (世代、スナップショットに相当) を参照します。
  pub fn revision(&self) -> Index {
    self.revision.n()
  }

  pub fn walk_down<F, E>(&mut self, callback: &mut F) -> Result<()>
  where
    F: FnMut(Index, Index, u8, &Hash, Option<&[u8]>) -> std::result::Result<WalkDirection, E>,
    E: std::error::Error + 'static,
  {
    let cache_opt = &self.revision.clone().0;
    let cache = if let Some(cache) = cache_opt { cache } else { return Ok(()) };
    let node_index = if cache.last_entry.inodes.is_empty() { 0 } else { cache.last_entry.inodes.len() };
    self._walk_down(node_index, &cache.last_entry, callback)
  }

  fn _walk_down<F, E>(&mut self, node_index: usize, entry: &Entry, callback: &mut F) -> Result<()>
  where
    F: FnMut(Index, Index, u8, &Hash, Option<&[u8]>) -> std::result::Result<WalkDirection, E>,
    E: std::error::Error + 'static,
  {
    let i = entry.enode.meta.address.i;
    let (j, hash, value) = if node_index == 0 {
      let node = &entry.enode;
      (node.meta.address.j, &node.meta.hash, Some(&node.payload))
    } else {
      let node = &entry.inodes[node_index - 1];
      (node.meta.address.j, &node.meta.hash, None)
    };

    let dir = (callback)(self.revision(), i, j, hash, value.map(|v| &**v)).map_err(|e| Error::WalkDown(Box::new(e)))?;

    if node_index == 0 || dir == WalkDirection::Stop {
      return Ok(());
    }
    if dir == WalkDirection::Right || dir == WalkDirection::Both {
      self._walk_down(node_index - 1, entry, callback)?
    }
    if dir == WalkDirection::Left || dir == WalkDirection::Both {
      let current = &entry.inodes[node_index - 1];
      let left = read_entry_with_index_check(&mut self.cursor, current.left.position, current.left.i)?;
      debug_assert_eq!(current.left.i, left.enode.meta.address.i);
      debug_assert!(left.enode.meta.address.i < i);
      let left_j = current.left.j;
      let left_node_index = if current.left.j == 0 {
        0
      } else {
        match left.inodes.iter().position(|inode| inode.meta.address.j == left_j) {
          Some(i) => i + 1,
          None => inconsistency(format!(
            "The node b_{{{},{}}} referenced as the right node of node b_{{{},{}}} isn't included in entry {} @ {}",
            current.right.i,
            current.right.j,
            current.meta.address.i,
            current.meta.address.j,
            current.right.i,
            current.right.position
          ))?,
        }
      };
      self._walk_down(left_node_index, &left, callback)?
    }
    Ok(())
  }

  /// 指定されたインデックスの値を参照します。
  /// 0 を含む範囲外のインデックスを指定した場合は `None` を返します。
  pub fn get(&mut self, i: Index) -> Result<Option<Vec<u8>>> {
    if i == 0 || i > self.revision.n() {
      return Ok(None);
    }
    let mut value = None;
    self.walk_down(&mut |_n, b_i, b_j, _hash, leaf_value: Option<&[u8]>| {
      if b_i == i {
        if b_j == 0 {
          if let Some(v) = leaf_value {
            value = Some(v.to_vec());
            Ok(WalkDirection::Stop)
          } else {
            inconsistency(format!("The value was not passed at the leaf node b_{b_i} reached"))
          }
        } else {
          Ok(WalkDirection::Right)
        }
      } else {
        let ((_il, _jl), (ir, jr)) = subnodes(b_i, b_j);
        if contains(ir, jr, i) { Ok(WalkDirection::Right) } else { Ok(WalkDirection::Left) }
      }
    })?;
    Ok(value)
  }

  // 指定されたデータ b_i とその認証パスを取得します。
  pub fn get_authentication_path(&mut self, _i: Index) -> Result<Option<AuthPath>> {
    unimplemented!()
  }

  // 指定された範囲 [i0, i1] (両端を含む) のエントリを取得します。
  pub fn scan<F>(&self, _i0: Index, _i1: Index, _callback: &mut F)
  where
    F: FnMut(Entry),
  {
    unimplemented!()
  }
}

fn read_entry_with_index_check(
  r: &mut Box<dyn Reader<Entry>>,
  position: Position,
  expected_index: Index,
) -> Result<Entry> {
  let entry = r.read(position)?;
  let actual_index = entry.enode.meta.address.i;
  if actual_index != expected_index {
    Err(InternalStateInconsistency {
      message: format!("The index of entry {expected_index} read from {position} was actually {actual_index}"),
    })
  } else {
    Ok(entry)
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
  value.iter().map(|c| format!("{c:02X}")).collect()
}
