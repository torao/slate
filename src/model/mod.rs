use std::fmt::Debug;
use std::ops::RangeInclusive;

#[cfg(test)]
mod test;

/// BHT がインデックス i として使用する整数の型です。`u64` を表しています。
///
/// 64-bit がアプリケーションへの適用に大きすぎる場合 `small_index` feature を指定することで `u32` に変更する
/// ことができます。
///
#[cfg(not(feature = "small_index"))]
pub type Index = u64;

#[cfg(feature = "small_index")]
pub type Index = u32;

/// [`Index`] 型のビット幅です。定数 64 を表しています。
///
/// コンパイル時に `small_index` feature を指定することでこの定数は 32 となります。
///
#[cfg(not(feature = "small_index"))]
pub const INDEX_SIZE: u8 = 64;

#[cfg(feature = "small_index")]
pub const INDEX_SIZE: u8 = 32;

/// BHT のアルゴリズムで使用する任意のノード b_{i,j} を表すための構造体です。
///
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct Node {
  pub i: Index,
  pub j: u8,
}

impl Node {
  pub fn new(i: Index, j: u8) -> Node {
    Node { i, j }
  }
}

/// BHT のアルゴリズムで使用する任意の中間ノードを表すための構造体です。左右の枝への分岐を含みます。
///
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct INode {
  pub node: Node,
  pub left: Node,
  pub right: Node,
}

impl INode {
  pub fn new(node: Node, left: Node, right: Node) -> INode {
    INode { node, left, right }
  }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct Step {
  pub step: Node,
  pub neighbor: Node,
}

/// 目的のノードまでの経路を、その経路から分岐した先のノードのハッシュ値を含む経路を表します。
/// 目的のノードまでの経路を表します。経路は `root` から開始し各ステップの `step` で示したノードをたどります。
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Path {
  pub root: Node,
  pub steps: Vec<Step>,
}

/// n≧1 世代のハッシュ木構造 𝑇ₙ をアルゴリズムによって表す概念モデルです。n 世代木における中間ノードや探索経路などの
/// アルゴリズムを実装します。
///
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct NthGenHashTree {
  n: Index,
  pbst_roots: Vec<Node>,
  ephemeral_nodes: Vec<INode>,
}

impl NthGenHashTree {
  /// 木構造 𝑇ₙ に含まれる独立した完全二分木のルートノードとそれらを接続する中間ノードを算出します。この列は木構造の
  /// 左に存在する完全二分木が先に来るように配置されています。
  pub fn new(n: Index) -> NthGenHashTree {
    debug_assert_ne!(0, n);
    let pbst_roots = NthGenHashTree::create_pbst_roots(n);
    let ephemeral_nodes = NthGenHashTree::create_ephemeral_nodes(n, &pbst_roots);
    debug_assert_ne!(0, pbst_roots.len());
    NthGenHashTree { n, pbst_roots, ephemeral_nodes }
  }

  /// このハッシュ木の世代を参照します。
  pub fn n(&self) -> Index {
    self.n
  }

  /// このハッシュ木のルートノードを参照します。
  pub fn root(&self) -> Node {
    self.ephemeral_nodes.first().map(|i| i.node).unwrap_or(*self.pbst_roots.first().unwrap())
  }

  /// 独立した完全二分木のルートノードを列挙します。
  pub fn pbst_roots(&self) -> impl Iterator<Item = &Node> {
    self.pbst_roots.iter()
  }

  /// 一過性の中間ノードを列挙します。
  pub fn ephemeral_nodes(&self) -> impl Iterator<Item = &INode> {
    self.ephemeral_nodes.iter()
  }

  /// この世代で追加される中間ノードを列挙します。
  pub fn inodes(&self) -> Vec<INode> {
    let mut inodes = Vec::<INode>::with_capacity(ceil_log2(self.n) as usize);
    for inode in self.ephemeral_nodes() {
      inodes.push(*inode);
    }
    if let Some(node) = self.pbst_roots().find(|node| node.i == self.n() && node.j != 0) {
      let i = node.i;
      for j in 0..node.j {
        let j = node.j - j;
        let left = Node::new(i - (1 << j) + (1 << (j - 1)), j - 1);
        let right = Node::new(i, j - 1);
        inodes.push(INode::new(Node::new(i, j), left, right))
      }
    }
    inodes
  }

  /// 一過性の中間ノードをたどって b_{i,j} を含む完全二分木のルートノードを検索します。ノードを 1 ステップ進むたびに
  /// `on_step(from, to)` のコールバックが行われます。b_{i,j} が一過性の中間ノードの場合 `Either::Right(node)`
  /// を返し、b_{i,j} を含む完全二分木のルートノードの場合 `Either::Left(root)` を返します。
  pub fn path_to(&self, i: Index, j: u8) -> Option<Path> {
    let root = self.root();
    if !contains(root.i, root.j, i) {
      return None;
    }

    // 一過性の中間ノードをたどって b_{i,j} を含む完全二分木のルートノードを検索する
    let mut steps = Vec::<Step>::with_capacity(INDEX_SIZE as usize);
    let pbst = if let Some(pbst) = self.ephemeral_nodes.last().map(|i| i.right) {
      let mut pbst = pbst;
      for x in 0..self.ephemeral_nodes.len() {
        let node = &self.ephemeral_nodes[x];

        // 目的のノードを検出した場合
        if node.node.i == i && node.node.j == j {
          return Some(Path { root, steps });
        }

        // 左枝側 (完全二分木) に含まれている場合は左枝を始点に設定
        if contains(node.left.i, node.left.j, i) {
          steps.push(Step { step: node.left, neighbor: node.right });
          pbst = node.left;
          break;
        }

        // このノードの次のステップを保存
        steps.push(Step { step: node.right, neighbor: node.left });
      }
      pbst
    } else {
      root
    };

    if pbst.i == i && pbst.j == j {
      return Some(Path { root, steps });
    } else if pbst.j < j {
      return None;
    }

    // 完全二分木上の経路を構築
    let mut mover = Self::pbst_inode(pbst.i, pbst.j);
    for _ in 0..INDEX_SIZE {
      // 目的のノードを検出した場合
      if mover.node.i == i && mover.node.j == j {
        return Some(Path { root, steps });
      }
      let (next, neighbor) = if contains(mover.left.i, mover.left.j, i) {
        (mover.left, mover.right)
      } else {
        debug_assert!(
          contains(mover.right.i, mover.right.j, i),
          "the subtree T_{{{},{}}} doesn't contain node b_{{{},{}}}",
          mover.right.i,
          mover.right.j,
          i,
          j
        );
        (mover.right, mover.left)
      };
      steps.push(Step { step: next, neighbor });
      if next.j != 0 {
        mover = Self::pbst_inode(next.i, next.j);
      } else {
        return Some(Path { root, steps });
      }
    }
    unreachable!("maximum step was reached in searching the route to ({}, {}) -> {:?}", i, j, steps)
  }

  /// 指定された中間ノード b_{i,j} を返します。該当する中間ノードが存在しない場合は `None` を返します。
  pub fn inode(&self, i: Index, j: u8) -> Option<INode> {
    if j == 0 {
      None
    } else if is_pbst(i, j) && i < self.n() {
      Some(Self::pbst_inode(i, j))
    } else {
      self.ephemeral_nodes().find(|node| node.node.i == i && node.node.j == j).map(|i| *i)
    }
  }

  #[inline]
  fn pbst_inode(i: Index, j: u8) -> INode {
    debug_assert!(is_pbst(i, j), "({}, {}) is not a PBST", i, j);
    debug_assert_ne!(0, j, "({}, {}) is a leaf node, not a inode", i, j);
    INode::new(Node::new(i, j), Node::new(i - (1 << (j - 1)), j - 1), Node::new(i, j - 1))
  }

  /// 完全二分木のルートノードを構築します。
  fn create_pbst_roots(n: Index) -> Vec<Node> {
    let capacity = ceil_log2(n) as usize;
    let mut remaining = n;
    let mut pbsts = Vec::<Node>::with_capacity(capacity);
    while remaining != 0 {
      let j = floor_log2(remaining);
      let i = n - remaining + (1 << j);
      pbsts.push(Node::new(i, j));
      remaining -= 1 << j;
    }
    pbsts
  }

  /// 一過性の中間ノードを参照します。
  fn create_ephemeral_nodes(n: Index, pbsts: &Vec<Node>) -> Vec<INode> {
    debug_assert_ne!(0, pbsts.len());
    let mut ephemerals = Vec::<INode>::with_capacity(pbsts.len() - 1);
    for i in 0..pbsts.len() - 1 {
      let position = pbsts.len() - 1 - i;
      ephemerals.insert(
        0,
        INode {
          node: Node::new(n, pbsts[position - 1].j + 1),
          left: pbsts[position - 1],
          right: if i != 0 { ephemerals[0].node } else { pbsts[position] },
        },
      );
    }
    ephemerals
  }
}

/// 指定されたノード b_{i,j} をルートとする部分木に含まれる葉ノード b_ℓ の範囲を算出します。
#[inline]
pub fn range(i: Index, j: u8) -> RangeInclusive<Index> {
  debug_assert!(j <= 64); // i=u64::MAX のとき j=64
  let i_min = (((i as u128 >> j) - (if is_pbst(i, j) { 1 } else { 0 })) << j) as u64 + 1;
  let i_max = i;
  i_min..=i_max
}

/// 指定されたノード b_{i,j} をルートとする部分木にノード b_{k,\*} が含まれているかを判定します。これは T_{k,*} が
/// T_{i,j} の部分木かを判定することと意味的に同じです。
#[inline]
pub fn contains(i: Index, j: u8, k: Index) -> bool {
  debug_assert!(j <= 64); // i=u64::MAX のとき j=64
  range(i, j).contains(&k)
}

/// 指定されたノード b_{i,j} をルートとする部分木が完全二分木であるかを判定します。
#[inline]
pub fn is_pbst(i: Index, j: u8) -> bool {
  i & (((1u128 << j) - 1) as u64) == 0
}

/// 指定された `x` に対して `𝑦=⌈log₂ 𝑥⌉` を求めます。返値は 0 (x=1) から 64 (x=u64::MAX) の範囲となります。
/// `x` に 0 を指定することはできません。
#[inline]
pub fn ceil_log2(x: Index) -> u8 {
  let rank = floor_log2(x);
  rank + (if x & ((1 << rank) - 1) == 0 { 0 } else { 1 })
}

/// 指定された `x` に対して `𝑦=⌊log₂ 𝑥⌋` を求めます。返値は 0 (x=1) から 63 (x=u64::MAX) の範囲となります。
/// `x` に 0 を指定することはできません。
#[inline]
pub fn floor_log2(x: Index) -> u8 {
  // まずビット列の中で最も上位に存在する 1 の位置より右側のすべてのビットが 1 となるようにビット論理和を繰り返し、
  // 次に数値内で 1 となっているビットの数を数えるというアプローチ (可能であれば後半は POPCNT CPU 命令が使う方が
  // 良いかもしれない)。
  // See also: https://qiita.com/pochman/items/d74930a62613bb8d3d00,
  // http://www.nminoru.jp/~nminoru/programming/bitcount.html
  debug_assert!(x > 0);
  let mut bits = x;
  bits = bits | (bits >> 1);
  bits = bits | (bits >> 2);
  bits = bits | (bits >> 4);
  bits = bits | (bits >> 8);
  bits = bits | (bits >> 16);
  bits = bits | (bits >> 32);
  bits = (bits & 0b0101010101010101010101010101010101010101010101010101010101010101)
    + (bits >> 1 & 0b0101010101010101010101010101010101010101010101010101010101010101);
  bits = (bits & 0b0011001100110011001100110011001100110011001100110011001100110011)
    + (bits >> 2 & 0b0011001100110011001100110011001100110011001100110011001100110011);
  bits = (bits & 0b0000111100001111000011110000111100001111000011110000111100001111)
    + (bits >> 4 & 0b0000111100001111000011110000111100001111000011110000111100001111);
  bits = (bits & 0b0000000011111111000000001111111100000000111111110000000011111111)
    + (bits >> 8 & 0b0000000011111111000000001111111100000000111111110000000011111111);
  bits = (bits & 0b0000000000000000111111111111111100000000000000001111111111111111)
    + (bits >> 16 & 0b0000000000000000111111111111111100000000000000001111111111111111);
  bits = (bits & 0b0000000000000000000000000000000011111111111111111111111111111111)
    + (bits >> 32 & 0b0000000000000000000000000000000011111111111111111111111111111111);
  bits as u8 - 1
}
