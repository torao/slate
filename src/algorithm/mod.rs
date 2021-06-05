use std::fmt::Debug;

#[cfg(test)]
mod test;

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct Node {
  pub i: u64,
  pub j: u8,
}

impl Node {
  pub fn new(i: u64, j: u8) -> Node {
    Node { i, j }
  }
}

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

#[derive(PartialEq, Eq, Debug)]
pub struct Generation {
  n: u64,
  pbst_roots: Vec<Node>,
  ephemeral_nodes: Vec<INode>,
}

impl Generation {
  /// 木構造 𝑇ₙ に含まれる独立した完全二分木のルートノードとそれらを接続する中間ノードを算出します。この列は木構造の
  /// 左に存在する完全二分木が先に来るように配置されています。
  pub fn new(n: u64) -> Generation {
    debug_assert_ne!(0, n);
    let pbst_roots = Generation::create_pbst_roots(n);
    let ephemeral_nodes = Generation::create_ephemeral_nodes(n, &pbst_roots);
    debug_assert_ne!(0, pbst_roots.len());
    Generation { n, pbst_roots, ephemeral_nodes }
  }

  /// この世代が何世代目かを参照します。
  pub fn n(&self) -> u64 {
    self.n
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

  /// 完全二分木のルートノードを構築します。
  fn create_pbst_roots(n: u64) -> Vec<Node> {
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
  fn create_ephemeral_nodes(n: u64, pbsts: &Vec<Node>) -> Vec<INode> {
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

#[inline]
pub fn is_pbst(i: u64, j: u8) -> bool {
  i & ((1 << j) - 1) == 0
}

/// 指定された `x` に対して `𝑦=⌈log₂ 𝑥⌉` を求めます。返値は 0 (x=1) から 64 (x=u64::MAX) の範囲となります。
/// `x` に 0 を指定することはできません。
#[inline]
pub fn ceil_log2(x: u64) -> u8 {
  let rank = floor_log2(x);
  rank + (if x & ((1 << rank) - 1) == 0 { 0 } else { 1 })
}

/// 指定された `x` に対して `𝑦=⌊log₂ 𝑥⌋` を求めます。返値は 0 (x=1) から 63 (x=u64::MAX) の範囲となります。
/// `x` に 0 を指定することはできません。
#[inline]
pub fn floor_log2(x: u64) -> u8 {
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
