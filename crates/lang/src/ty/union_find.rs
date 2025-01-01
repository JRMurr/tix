use core::panic;
use std::fmt::Debug;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct UnionIdx {
    idx: u32,
    // _ty: PhantomData<fn() -> T>,
}

// impl<T> Copy for UnionIdx {}

// impl<T> Clone for UnionIdx {
//     #[inline]
//     fn clone(&self) -> UnionIdx {
//         *self
//     }
// }

// impl<T> PartialEq for UnionIdx {
//     #[inline]
//     fn eq(&self, rhs: &Self) -> bool {
//         self.idx == rhs.idx
//     }
// }

// impl<T> Eq for UnionIdx {}

impl UnionIdx {
    pub fn new(idx: u32) -> Self {
        Self { idx }
    }

    #[inline]
    pub fn idx(&self) -> usize {
        self.idx as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct UnionFindNode<T> {
    /// The value associated with this node (if it exists).
    value: Option<T>,
    /// The index of this node's parent (or itself if it's a root).
    parent: UnionIdx,
    /// The rank is used to optimize union operations (to avoid deep trees).
    rank: u8,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UnionFind<T> {
    nodes: Vec<UnionFindNode<T>>,
}

impl<T: Debug + Clone> UnionFind<T> {
    pub fn new(len: usize, mut make_default: impl FnMut(UnionIdx) -> T) -> Self {
        let len = u32::try_from(len).expect("Length overflow");
        Self {
            nodes: (0..len)
                .map(|i| UnionFindNode {
                    value: Some(make_default(UnionIdx::new(i))),
                    parent: UnionIdx::new(i),
                    rank: 0,
                })
                .collect(),
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn push_with_idx(&mut self, init: impl FnOnce(UnionIdx) -> T) -> UnionIdx {
        let i = self.nodes.len() as u32;
        let _ = i.checked_add(1).expect("Length overflow");
        let idx = UnionIdx::new(i);
        self.nodes.push(UnionFindNode {
            value: Some(init(idx)),
            parent: idx,
            rank: 0,
        });
        idx
    }

    pub fn push(&mut self, value: T) -> UnionIdx {
        self.push_with_idx(|_| value)
    }

    pub fn find(&mut self, x: UnionIdx) -> UnionIdx {
        let parent = self.nodes[x.idx()].parent;
        if parent != x {
            let root = self.find(parent);
            self.nodes[x.idx()].parent = root; // Path compression
            root
        } else {
            x
        }
    }

    // pub fn get(&self, x: UnionIdx) -> UnionIdx {

    // }

    pub fn get_mut(&mut self, x: UnionIdx) -> &mut T {
        let root = self.find(x);

        // let nodes = self.nodes.clone();

        if let Some(value) = self.nodes[root.idx()].value.as_mut() {
            value
        } else {
            panic!("Root node {:?} does not have a value", root)
            // println!("root: {}, x: {}, len: {}", root.idx(), x.idx(), nodes.len());
            // panic!("nodes: {:?}", nodes.clone())
        }
    }

    pub fn unify(&mut self, a: UnionIdx, b: UnionIdx) -> (UnionIdx, Option<T>) {
        let (a, b) = (self.find(a), self.find(b));

        if a == b {
            return (a, None);
        }

        // TODO: should probably make sure the idxs exist but probably fine...
        let (node_a, node_b) = unsafe {
            let ptr = self.nodes.as_mut_ptr();

            let node_a = &mut *ptr.add(a.idx());
            let node_b = &mut *ptr.add(b.idx());

            (node_a, node_b)
        };

        let lhs = node_a.value.take().unwrap();
        let rhs = node_b.value.take().unwrap();

        // Union by rank
        let idx = match node_a.rank.cmp(&node_b.rank) {
            std::cmp::Ordering::Less => {
                node_a.parent = b;
                node_b.value = Some(lhs);
                b
            }
            std::cmp::Ordering::Greater => {
                node_b.parent = a;
                node_a.value = Some(lhs);
                a
            }
            std::cmp::Ordering::Equal => {
                node_a.parent = b;
                node_b.rank += 1;
                node_b.value = Some(lhs);
                b
            }
        };

        (idx, Some(rhs))
    }
}
