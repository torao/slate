# Logarithmic Multi-Tier Hash Tree
<!-- 多層 multi-layer, multi-tier -->

不変で木構造の完全な履歴を保持する効率的な追記指向のハッシュツリー (Merkle Tree) 構造である Logarithmic Multi-Tier Hash Tree について説明
します (同様のデータ構造やアルゴリズム十分に調査したわけではないが、ここで述べるアルゴリズムに関する呼称や研究などを見つけられていないため、
ここでは LMTHT という名前で呼びます)。これはログ構造のデータベースとして使用することができる。

## Logarithmic Multi-Tier Hash Tree の特徴

* 時系列データのように追加のみが行われるリスト構造。
* データの追加位置を示すインデックスにツリー構造を構築する。このツリー構造は不変であり、ハッシュツリー (Merkle Tree) として使用する
  ことによってデータの破損や改ざんを検出することができる。
* データの増加によってツリーは成長する。ただし、ツリー構造の完全な履歴を保持していることから、ある時点でのハッシュツリーをいつでも参照することが
  できる。
* append, read, range scan, full scan 操作が可能。delete はハッシュ値のみを残し削除することはできる。

## Append

![append operations from 1 to 16 on the Logarithmic Multi-Tier Hash Tree](docs/lmtht.gif)
