use std::iter::FromIterator;

use crate::algorithm::{ceil_log2, floor_log2, Generation, Node, Path, Step};
use crate::Index;

#[test]
#[should_panic]
fn test_generation_new_with_zero() {
  Generation::new(0);
}

#[test]
fn test_generation() {
  // 高さ j の完全二分木のケース
  let pbt = |j: u8| (1 << j, (1..=j).rev().collect::<Vec<u8>>(), vec![], vec![(1 << j, j)]);

  // 高さ j の完全二分木となる手前のケース
  let pre_pbt = |j: u8| -> (u64, Vec<u8>, Vec<u8>, Vec<(u64, u8)>) {
    let mut ephemerals = (1..=j).rev().collect::<Vec<u8>>();
    ephemerals.remove(ephemerals.len() - 1);
    let pbsts = (0..j)
      .rev()
      .map(|j2| {
        let offset = ((j2 + 1)..j).map(|x| 1u64 << x).sum::<u64>();
        (offset + (1 << j2), j2)
      })
      .collect();
    let i = if j == 64 { 0xFFFFFFFFFFFFFFFFu64 } else { (1u64 << j) - 1 };
    (i, ephemerals.clone(), ephemerals, pbsts)
  };

  // 高さ j の完全二分木の次のケース
  let post_pbt = |j: u8| -> (Index, Vec<u8>, Vec<u8>, Vec<(Index, u8)>) {
    ((1 << j) + 1, vec![j + 1], vec![j + 1], vec![(1 << j, j), ((1 << j) + 1, 0)])
  };

  for (n, inode_js, ephemeral_js, pbst_roots) in vec![
    (1, vec![], vec![], vec![(1u64, 0u8)]),
    (2, vec![1u8], vec![], vec![(2, 1)]),
    (3, vec![2], vec![2u8], vec![(2, 1), (3, 0)]),
    (4, vec![2, 1], vec![], vec![(4, 2)]),
    (5, vec![3], vec![3], vec![(4, 2), (5, 0)]),
    (6, vec![3, 1], vec![3], vec![(4, 2), (6, 1)]),
    (7, vec![3, 2], vec![3, 2], vec![(4, 2), (6, 1), (7, 0)]),
    (8, vec![3, 2, 1], vec![], vec![(8, 3)]),
    (9, vec![4], vec![4], vec![(8, 3), (9, 0)]),
    (10, vec![4, 1], vec![4], vec![(8, 3), (10, 1)]),
    (11, vec![4, 2], vec![4, 2], vec![(8, 3), (10, 1), (11, 0)]),
    (12, vec![4, 2, 1], vec![4], vec![(8, 3), (12, 2)]),
    (13, vec![4, 3], vec![4, 3], vec![(8, 3), (12, 2), (13, 0)]),
    (14, vec![4, 3, 1], vec![4, 3], vec![(8, 3), (12, 2), (14, 1)]),
    (15, vec![4, 3, 2], vec![4, 3, 2], vec![(8, 3), (12, 2), (14, 1), (15, 0)]),
    (16, vec![4, 3, 2, 1], vec![], vec![(16, 4)]),
    pre_pbt(16),
    pbt(16),
    post_pbt(16),
    pre_pbt(31),
    pbt(31),
    post_pbt(31),
    pre_pbt(32),
    pbt(32),
    post_pbt(32),
    pre_pbt(33),
    pbt(33),
    post_pbt(33),
    pre_pbt(64),
  ] {
    let gen = Generation::new(n);
    assert_eq!(n, gen.n());

    // 一過性の中間ノード
    let expected = ephemeral_js.iter().map(|j| Node::new(n, *j)).collect::<Vec<Node>>();
    let actual = Vec::from_iter(gen.ephemeral_nodes().map(|i| i.node));
    assert_eq!(expected, actual);

    // 完全二分木のルートノード
    let expected = pbst_roots.iter().map(|(i, j)| Node::new(*i, *j)).collect::<Vec<Node>>();
    let actual = gen.pbst_roots().map(|i| *i).collect::<Vec<Node>>();
    assert_eq!(expected, actual);

    // n-th 世代の中間ノード
    let expected = inode_js.iter().map(|j| Node::new(n, *j)).collect::<Vec<Node>>();
    let actual = gen.inodes().iter().map(|i| i.node).collect::<Vec<Node>>();
    assert_eq!(expected, actual);
  }
}

/// n 個の要素を含む木構造 T_n のルートノードは b_{n,ceil(log₂ n)} です。
#[test]
fn test_generation_root() {
  for (n, expected) in ns().map(|i| (i, (i, ceil_log2(i)))) {
    let Node { i, j } = Generation::new(n).root();
    assert_eq!(expected, (i, j), "{:?}", Generation::new(n));
  }
}

#[test]
fn test_generation_path_to() {
  let path = |i: u64, steps: Vec<((Index, u8), (Index, u8))>| -> Path {
    let steps = steps.iter()
      .map(|s| Step { step: Node::new(s.0.0, s.0.1), neighbor: Node::new(s.1.0, s.1.1) })
      .collect();
    Path { root: Node::new(i, ceil_log2(i)), steps }
  };
  let mut cases = vec![
    (2, (1, 0), path(2, vec![((1, 0), (2, 0))])),
    (2, (2, 0), path(2, vec![((2, 0), (1, 0))])),
    (3, (2, 1), path(3, vec![((2, 1), (3, 0))])),
    (3, (3, 0), path(3, vec![((3, 0), (2, 1))])),
    (3, (1, 0), path(3, vec![((2, 1), (3, 0)), ((1, 0), (2, 0))])),
    (3, (2, 0), path(3, vec![((2, 1), (3, 0)), ((2, 0), (1, 0))])),
    (13, (1, 0), path(13, vec![((8, 3), (13, 3)), ((4, 2), (8, 2)), ((2, 1), (4, 1)), ((1, 0), (2, 0))])),
    (13, (6, 0), path(13, vec![((8, 3), (13, 3)), ((8, 2), (4, 2)), ((6, 1), (8, 1)), ((6, 0), (5, 0))])),
    (13, (13, 3), path(13, vec![((13, 3), (8, 3))])),
    (13, (13, 0), path(13, vec![((13, 3), (8, 3)), ((13, 0), (12, 2))])),
  ];
  cases.append(ns()
    .map(|i| (i, (i, ceil_log2(i)), path(i, vec![])))
    .collect::<Vec<(u64, (u64, u8), Path)>>().as_mut());
  for (n, (i, j), expected) in cases {
    println!("{}: ({}, {})", n, i, j);
    let gen = Generation::new(n);
    let actual = gen.path_to(i, j).unwrap();
    assert_eq!(expected, actual)
  }
}

#[test]
fn test_floor_and_ceil_log2() {
  fn expected_floor(mut n: Index) -> u8 {
    let mut rank: u8 = 0;
    while n != 0 {
      rank += 1;
      n >>= 1;
    }
    rank - 1
  }
  fn expected_ceil(n: Index) -> u8 {
    let rank = expected_floor(n);
    rank + (if n == (1 << rank) { 0 } else { 1 })
  }

  for x in vec![
    1u64,
    2,
    3,
    4,
    5,
    7,
    8,
    9,
    0xFFFFFFFF,
    0x100000000,
    0x100000001,
    0xFFFFFFFFFFFFFFFE,
    0xFFFFFFFFFFFFFFFF,
  ] {
    println!("floor(log₂ {}) = {}, ceil(log₂ {}) = {}", x, floor_log2(x), x, ceil_log2(x));
    assert_eq!(expected_floor(x), floor_log2(x));
    assert_eq!(expected_ceil(x), ceil_log2(x));
  }
}

#[test]
#[should_panic]
fn test_floor_log2_with_zero() {
  floor_log2(0);
}

#[test]
#[should_panic]
fn test_ceil_log2_with_zero() {
  ceil_log2(0);
}

fn ns() -> impl Iterator<Item=u64> {
  (1u64..1024).chain(
    (10..63).map(|i| vec![(1 << i) - 1, 1 << i, (1 << i) + 1]).flatten()
  ).chain(
    vec![u64::MAX - 2, u64::MAX - 1, u64::MAX]
  )
}