use std::collections::HashSet;
use std::iter::FromIterator;

use crate::formula::{Addr, Model, ceil_log2, floor_log2, is_valid, root_of, subnodes_of, total_nodes};
use crate::{INDEX_SIZE, Index};

#[test]
#[should_panic]
fn model_with_zero_generation() {
  Model::new(0);
}

#[test]
fn model_basic() {
  struct X(u64, Vec<u8>, Vec<u8>, Vec<(u64, u8)>);

  // 高さ j の完全二分木のケース
  let pbt = |j: u8| X(1 << j, (1..=j).rev().collect::<Vec<u8>>(), vec![], vec![(1 << j, j)]);

  // 高さ j の完全二分木となる手前のケース
  let pre_pbt = |j: u8| -> X {
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
    X(i, ephemerals.clone(), ephemerals, pbsts)
  };

  // 高さ j の完全二分木の次のケース
  let post_pbt = |j: u8| -> X { X((1 << j) + 1, vec![j + 1], vec![j + 1], vec![(1 << j, j), ((1 << j) + 1, 0)]) };

  for X(n, mut inode_js, ephemeral_js, pbst_roots) in vec![
    X(1, vec![], vec![], vec![(1u64, 0u8)]),
    X(2, vec![1u8], vec![], vec![(2, 1)]),
    X(3, vec![2], vec![2u8], vec![(2, 1), (3, 0)]),
    X(4, vec![2, 1], vec![], vec![(4, 2)]),
    X(5, vec![3], vec![3], vec![(4, 2), (5, 0)]),
    X(6, vec![3, 1], vec![3], vec![(4, 2), (6, 1)]),
    X(7, vec![3, 2], vec![3, 2], vec![(4, 2), (6, 1), (7, 0)]),
    X(8, vec![3, 2, 1], vec![], vec![(8, 3)]),
    X(9, vec![4], vec![4], vec![(8, 3), (9, 0)]),
    X(10, vec![4, 1], vec![4], vec![(8, 3), (10, 1)]),
    X(11, vec![4, 2], vec![4, 2], vec![(8, 3), (10, 1), (11, 0)]),
    X(12, vec![4, 2, 1], vec![4], vec![(8, 3), (12, 2)]),
    X(13, vec![4, 3], vec![4, 3], vec![(8, 3), (12, 2), (13, 0)]),
    X(14, vec![4, 3, 1], vec![4, 3], vec![(8, 3), (12, 2), (14, 1)]),
    X(15, vec![4, 3, 2], vec![4, 3, 2], vec![(8, 3), (12, 2), (14, 1), (15, 0)]),
    X(16, vec![4, 3, 2, 1], vec![], vec![(16, 4)]),
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
    let generation = Model::new(n);
    assert_eq!(n, generation.n());

    // 一過性の中間ノード
    let expected = ephemeral_js.iter().map(|j| Addr::new(n, *j)).collect::<Vec<Addr>>();
    let actual = Vec::from_iter(generation.ephemeral_nodes().map(|i| i.node));
    assert_eq!(expected, actual);

    // 完全二分木のルートノード
    let expected = pbst_roots.iter().map(|(i, j)| Addr::new(*i, *j)).collect::<Vec<Addr>>();
    let actual = generation.pbst_roots().copied().collect::<Vec<Addr>>();
    assert_eq!(expected, actual);

    // n-th 世代の中間ノード
    inode_js.reverse();
    let expected = inode_js.iter().map(|j| Addr::new(n, *j)).collect::<Vec<Addr>>();
    let actual = generation.inodes().iter().map(|i| i.node).collect::<Vec<Addr>>();
    assert_eq!(expected, actual);
  }
}

/// n 個の要素を含む木構造 T_n のルートノードは b_{n,ceil(log₂ n)} です。
#[test]
fn model_root() {
  for (n, expected) in ns().map(|i| (i, (i, ceil_log2(i)))) {
    let Addr { i, j } = Model::new(n).root();
    assert_eq!(expected, (i, j), "{:?}", Model::new(n));
  }
}

#[test]
fn verify_total_nodes() {
  let expecteds = [0u128, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31];
  for (n, expected) in expecteds.iter().enumerate() {
    assert_eq!(*expected, total_nodes(n as Index), "{n} {expected}");
  }

  // compare with structurally counted value
  fn _total_count_rec(i: Index, j: u8) -> u128 {
    if j == 0 {
      1
    } else {
      let ((il, jl), (ir, jr)) = subnodes_of(i, j);
      1 + _total_count_rec(il, jl) + _total_count_rec(ir, jr)
    }
  }
  for n in 1..=256 {
    let (i, j) = root_of(n);
    let expected = _total_count_rec(i, j);
    assert_eq!(expected, total_nodes(n));
  }

  // boundary condition
  assert_eq!(Index::MAX as u128 * 2 - 1, total_nodes(Index::MAX));
}

#[test]
fn calculated_index_of_roots() {
  // verify using indices obtained through stractural analysis
  for (i, j) in expected_index_for_roots() {
    assert_eq!((i, j), root_of(i));
  }

  // maximum acceptable index limit
  assert_eq!((Index::MAX, ceil_log2(Index::MAX)), root_of(Index::MAX));
}

#[test]
fn calculated_index_of_subnodes() {
  // verify using indices obtained through stractural analysis
  for ((i, j), (il, jl), (ir, jr)) in expected_index_for_subnodes() {
    assert_eq!(((il, jl), (ir, jr)), subnodes_of(i, j));
  }

  // maximum acceptable index limit
  assert_eq!(((Index::MAX - 1, 1), (Index::MAX, 0)), subnodes_of(Index::MAX, 2));
  assert_eq!(((Index::MAX - 3, 2), (Index::MAX, 2)), subnodes_of(Index::MAX, 3));
  assert_eq!(((Index::MAX - 7, 3), (Index::MAX, 3)), subnodes_of(Index::MAX, 4));
  assert_eq!(
    ((Index::MAX / 2 + 1, ceil_log2(Index::MAX) - 1), (Index::MAX, ceil_log2(Index::MAX) - 1)),
    subnodes_of(Index::MAX, ceil_log2(Index::MAX))
  );
}

#[test]
fn verify_valid_node() {
  // verify using indices obtained through stractural analysis
  let valids = expected_index_of_nodes().into_iter().collect::<HashSet<_>>();
  let indices = valids
    .iter()
    .map(|(i, _)| *i)
    .collect::<HashSet<_>>()
    .iter()
    .flat_map(|i| (0..=ceil_log2(*i) + 1).map(|j| (*i, j)))
    .chain(vec![(0 as Index, 0u8)])
    .collect::<Vec<_>>();
  for (i, j) in indices {
    assert_eq!(valids.contains(&(i, j)), is_valid(i, j), "({i}, {j})");
  }

  // maximum acceptable index limit
  assert!(is_valid(Index::MAX, 0));
  assert!(!is_valid(Index::MAX, 1));
  assert!(is_valid(Index::MAX, 2));
  assert!(is_valid(Index::MAX, 3));
  assert!(is_valid(Index::MAX, 4));
  assert!(is_valid(Index::MAX, ceil_log2(Index::MAX)));
  assert!(!is_valid(Index::MAX, ceil_log2(Index::MAX) + 1));
}

#[test]
fn floor_and_ceil_log2() {
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

  for x in [1u64, 2, 3, 4, 5, 7, 8, 9, 0xFFFFFFFF, 0x100000000, 0x100000001, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF] {
    println!("floor(log₂ {}) = {}, ceil(log₂ {}) = {}", x, floor_log2(x), x, ceil_log2(x));
    assert_eq!(expected_floor(x), floor_log2(x));
    assert_eq!(expected_ceil(x), ceil_log2(x));
  }
}

#[test]
#[should_panic]
fn verify_ceil_log2_with_zero() {
  ceil_log2(0);
}

#[test]
fn verify_ceil_log2() {
  // representative cases
  assert_eq!(ceil_log2(1), 0); // log2(1) = 0
  assert_eq!(ceil_log2(2), 1); // log2(2) = 1
  assert_eq!(ceil_log2(3), 2); // log2(3) = 1.58... → 2
  assert_eq!(ceil_log2(4), 2); // log2(4) = 2
  assert_eq!(ceil_log2(5), 3); // log2(5) = 2.32... → 3
  assert_eq!(ceil_log2(8), 3); // log2(8) = 3
  assert_eq!(ceil_log2(9), 4); // log2(9) = 3.16... → 4
  assert_eq!(ceil_log2(15), 4); // log2(15) = 3.90... → 4
  assert_eq!(ceil_log2(16), 4); // log2(16) = 4
  assert_eq!(ceil_log2(17), 5); // log2(17) = 4.08... → 5
  assert_eq!(ceil_log2(100), 7); // log2(100) = 6.64... → 7
  assert_eq!(ceil_log2(1024), 10); // log2(1024) = 10

  // boundary cases
  assert_eq!(ceil_log2(u64::MAX), 64); // 最大値: 2^64 - 1 → 64

  // Power of two with boundary
  assert_eq!(ceil_log2(1), 0); // 2^0
  assert_eq!(ceil_log2(2), 1); // 2^1
  assert_eq!(ceil_log2(3), 2); // 2^1 + 1 → 2
  assert_eq!(ceil_log2(7), 3); // 2^3 - 1 → 3
  assert_eq!(ceil_log2(8), 3); // 2^3 → 3
  assert_eq!(ceil_log2(9), 4); // 2^3 + 1 → 4
  assert_eq!(ceil_log2(127), 7); // 2^7 - 1 → 7
  assert_eq!(ceil_log2(128), 7); // 2^7
  assert_eq!(ceil_log2(129), 8); // 2^7 + 1 → 8
  assert_eq!(ceil_log2((1u64 << 32) - 1), 32); // 2^32 - 1 → 32
  assert_eq!(ceil_log2(1u64 << 32), 32); // 2^32
  assert_eq!(ceil_log2((1u64 << 32) + 1), 33); // 2^32 + 1 → 33
  assert_eq!(ceil_log2(1u64 << 63), 63); // 2^63

  // properties: 2^(j-1) < x <= 2^j
  for x in [2, 3, 5, 8, 9, 13, 100, 1000, 12345, u64::MAX - 1].iter() {
    let j = ceil_log2(*x);
    if *x > 1 {
      assert!(1u64 << (j - 1) < *x, "2^{} should be < {}", j - 1, x);
      if j < 64 {
        assert!(*x <= 1u64 << j, "{x} should be <= 2^{j}");
      }
    }
  }

  // relationship for floor_log2()
  for x in [1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33].iter() {
    let floor = floor_log2(*x);
    let ceil = ceil_log2(*x);

    // 2のべき乗の場合は一致、それ以外はceil = floor + 1
    if x & (x - 1) == 0 {
      // 2のべき乗チェック
      assert_eq!(ceil, floor, "Powers of 2 should have ceil == floor");
    } else if *x > 1 {
      assert_eq!(ceil, floor + 1, "Non-powers should have ceil = floor + 1");
    }
  }
}

#[test]
#[should_panic]
fn verify_floor_log2_with_zero() {
  floor_log2(0);
}

#[test]
fn verify_floor_log2() {
  // representative cases
  assert_eq!(floor_log2(1), 0); // log₂(1) = 0
  assert_eq!(floor_log2(2), 1); // log₂(2) = 1
  assert_eq!(floor_log2(3), 1); // log₂(3) = 1.58... → 1
  assert_eq!(floor_log2(4), 2); // log₂(4) = 2
  assert_eq!(floor_log2(5), 2); // log₂(5) = 2.32... → 2
  assert_eq!(floor_log2(8), 3); // log₂(8) = 3
  assert_eq!(floor_log2(15), 3); // log₂(15) = 3.90... → 3
  assert_eq!(floor_log2(16), 4); // log₂(16) = 4
  assert_eq!(floor_log2(17), 4); // log₂(17) = 4.08... → 4
  assert_eq!(floor_log2(100), 6); // log₂(100) = 6.64... → 6
  assert_eq!(floor_log2(1024), 10); // log₂(1024) = 10

  // bondary cases
  assert_eq!(floor_log2(u64::MAX), INDEX_SIZE - 1); // 最大値: 2^64 - 1

  // byte bit boundary
  assert_eq!(floor_log2(1), 0); // 2^0
  assert_eq!(floor_log2(7), 2); // 2^3 - 1
  assert_eq!(floor_log2(9), 3); // 2^3 + 1
  assert_eq!(floor_log2(127), 6); // 2^7 - 1
  assert_eq!(floor_log2(128), 7); // 2^7
  assert_eq!(floor_log2(129), 7); // 2^7 + 1
  assert_eq!(floor_log2(255), 7); // 2^8 - 1
  assert_eq!(floor_log2(256), 8); // 2^8
  assert_eq!(floor_log2((1u64 << 32) - 1), 31); // 2^32 - 1
  assert_eq!(floor_log2(1u64 << 32), 32); // 2^32
  assert_eq!(floor_log2((1u64 << 32) + 1), 32); // 2^32 + 1
  assert_eq!(floor_log2(1u64 << 63), 63); // 2^63

  // important properties: 2^j <= x < 2^(j+1)
  for x in [1, 5, 8, 13, 100, 1000, 12345, u64::MAX].iter() {
    let j = floor_log2(*x);
    assert!((1u64 << j) <= *x, "2^{j} should be <= {x}");
    if j < 63 {
      assert!(*x < 1u64 << (j + 1), "{} should be < 2^{}", x, j + 1);
    }
  }
}

fn ns() -> impl Iterator<Item = u64> {
  (1u64..1024).chain((10..63).flat_map(|i| vec![(1 << i) - 1, 1 << i, (1 << i) + 1])).chain(vec![
    u64::MAX - 2,
    u64::MAX - 1,
    u64::MAX,
  ])
}

fn expected_index_of_nodes() -> Vec<(Index, u8)> {
  include!("test_nodes.rs")
}

fn expected_index_for_roots() -> Vec<(Index, u8)> {
  include!("test_roots.rs")
}

type SubnodeIndex = ((Index, u8), (Index, u8), (Index, u8));
fn expected_index_for_subnodes() -> Vec<SubnodeIndex> {
  include!("test_branches.rs")
}

#[test]
fn yyy() -> std::result::Result<(), std::io::Error> {
  use std::fs::File;
  use std::io::Write;
  let mut file = File::create("test_nodes.rs").unwrap();
  writeln!(file, "vec![")?;
  for n in 1..=256 {
    let model = Model::new(n);
    let mut inodes = model.inodes();
    inodes.reverse();
    for inode in inodes {
      writeln!(file, "  ({}, {}),", inode.node.i, inode.node.j)?;
    }
    writeln!(file, "  ({n}, 0),")?;
  }
  writeln!(file, "]")?;
  Ok(())
}
