use crate::{Address, ENode, Entry, Hash, INDEX_SIZE, INode, Index, MAX_PAYLOAD_SIZE, MetaInfo, Position, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io::{Read, Write};

pub fn read_inodes_from<R: Read>(r: &mut R, position: Position) -> Result<(Index, Vec<INode>)> {
  let mut hash = [0u8; Hash::SIZE];

  // 中間ノードの読み込み
  let i = r.read_u64::<LittleEndian>()?;
  let inode_count = r.read_u8()? as usize;
  let mut right_j = 0u8;
  let mut inodes = Vec::<INode>::with_capacity(inode_count);
  for _ in 0..inode_count {
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
  Ok((i, inodes))
}

pub fn read_entry_from<R: Read>(r: &mut R, position: Position) -> Result<Entry> {
  // 中間ノードの読み込み
  let (i, inodes) = read_inodes_from(r, position)?;

  // 葉ノードの読み込み
  let mut hash = [0u8; Hash::SIZE];
  let payload_size = r.read_u32::<LittleEndian>()? & MAX_PAYLOAD_SIZE as u32;
  let mut payload = vec![0u8; payload_size as usize];
  r.read_exact(&mut payload)?;
  r.read_exact(&mut hash)?;
  let enode = ENode::new(MetaInfo::new(Address::new(i, 0, position), Hash::new(hash)), payload);

  Ok(Entry { enode, inodes })
}

pub fn write_inodes_to<W: Write>(index: Index, inodes: &[INode], w: &mut W) -> Result<usize> {
  debug_assert!(inodes.len() <= 0xFF);

  let mut length = (u64::BITS + u8::BITS) as usize / 8;
  w.write_u64::<LittleEndian>(index)?;
  w.write_u8(inodes.len() as u8)?;
  for i in inodes.iter() {
    debug_assert_eq!((i.meta.address.j - 1) & (INDEX_SIZE - 1), i.meta.address.j - 1);
    debug_assert_eq!(Hash::SIZE, i.meta.hash.value.len());
    length += (u8::BITS + u64::BITS + u64::BITS + u8::BITS) as usize / 8 + i.meta.hash.value.len();
    w.write_u8((i.meta.address.j - 1) & (INDEX_SIZE - 1))?; // 下位 6-bit のみ保存
    w.write_u64::<LittleEndian>(i.left.position)?;
    w.write_u64::<LittleEndian>(i.left.i)?;
    w.write_u8(i.left.j)?;
    w.write_all(&i.meta.hash.value)?;
  }
  Ok(length)
}

pub fn write_entry_to<W: Write>(entry: &Entry, w: &mut W) -> Result<usize> {
  debug_assert!(entry.enode.payload.len() <= MAX_PAYLOAD_SIZE);

  // 中間ノードの書き込み
  let mut length = write_inodes_to(entry.enode.meta.address.i, &entry.inodes, w)?;

  // 葉ノードの書き込み
  length += u32::BITS as usize / 8 + entry.enode.payload.len() + entry.enode.meta.hash.value.len();
  w.write_u32::<LittleEndian>(entry.enode.payload.len() as u32)?;
  w.write_all(&entry.enode.payload)?;
  w.write_all(&entry.enode.meta.hash.value)?;
  Ok(length)
}
