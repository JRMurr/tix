use std::marker::PhantomData;

#[derive(Debug)]
pub struct UnionIdx<T> {
    idx: u32,
    _ty: PhantomData<fn() -> T>,
}

impl<T> Copy for UnionIdx<T> {}

impl<T> Clone for UnionIdx<T> {
    #[inline]
    fn clone(&self) -> UnionIdx<T> {
        *self
    }
}

impl<T> PartialEq for UnionIdx<T> {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.idx == rhs.idx
    }
}

impl<T> UnionIdx<T> {
    pub fn new(idx: u32) -> Self {
        Self {
            idx,
            _ty: PhantomData,
        }
    }

    #[inline]
    pub fn idx(&self) -> usize {
        self.idx as usize
    }
}

#[derive(Debug, Clone)]
struct UnionFindNode<T> {
    /// The value associated with this node (if it exists).
    value: Option<T>,
    /// The index of this node's parent (or itself if it's a root).
    parent: UnionIdx<T>,
    /// The rank is used to optimize union operations (to avoid deep trees).
    rank: u8,
}

#[derive(Debug, Clone, Default)]
pub struct UnionFind<T> {
    nodes: Vec<UnionFindNode<T>>,
}

impl<T> UnionFind<T> {
    pub fn new(len: usize, mut make_default: impl FnMut(UnionIdx<T>) -> T) -> Self {
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

    pub fn push(&mut self, value: T) -> u32 {
        let i = self.nodes.len() as u32;
        let _ = i.checked_add(1).expect("Length overflow");
        self.nodes.push(UnionFindNode {
            value: Some(value),
            parent: UnionIdx::new(i),
            rank: 0,
        });
        i
    }

    pub fn find(&mut self, x: UnionIdx<T>) -> UnionIdx<T> {
        let parent = self.nodes[x.idx()].parent;
        if parent != x {
            let root = self.find(parent);
            self.nodes[x.idx()].parent = root; // Path compression
            root
        } else {
            x
        }
    }

    pub fn get_mut(&mut self, x: UnionIdx<T>) -> &mut T {
        let root = self.find(x);
        self.nodes[root.idx()].value.as_mut().unwrap()
    }

    pub fn unify(&mut self, a: UnionIdx<T>, b: UnionIdx<T>) -> (UnionIdx<T>, Option<T>) {
        let (root_a, root_b) = (self.find(a), self.find(b));

        if root_a == root_b {
            return (root_a, None);
        }

        // TODO: should probably make sure the idxs exist but probably fine...
        let (node_a, node_b) = unsafe {
            let ptr = self.nodes.as_mut_ptr();

            let node_a = &mut *ptr.add(root_a.idx());
            let node_b = &mut *ptr.add(root_b.idx());

            (node_a, node_b)
        };

        // Union by rank
        match node_a.rank.cmp(&node_b.rank) {
            std::cmp::Ordering::Less => {
                node_a.parent = root_b;
                node_b.value = node_a.value.take();
                (root_b, node_b.value.take())
            }
            std::cmp::Ordering::Greater => {
                node_b.parent = root_a;
                node_a.value = node_b.value.take();
                (root_a, node_a.value.take())
            }
            std::cmp::Ordering::Equal => {
                node_a.parent = root_b;
                node_b.rank += 1;
                node_b.value = node_a.value.take();
                (root_b, node_b.value.take())
            }
        }
    }
}
