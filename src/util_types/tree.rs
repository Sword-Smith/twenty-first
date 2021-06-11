// Copied from
// https://github.com/SpinResearch/merkle.rs/blob/2acba1bc73eba800e29a833f85f18f337e465213/src/tree.rs

// use digest::Digest;
use super::hash_utils::{HashUtils, Hashable};
use ring::digest::{Algorithm, Digest};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Tree<T> {
    Empty {
        hash: Vec<u8>,
    },
    Leaf {
        hash: Vec<u8>,
        value: T,
    },
    Node {
        hash: Vec<u8>,
        // All recursive data types must use Box<T> as type for their self-reference,
        // since the compiler must, at compile time, know how much space the struct
        // takes up on the stack. Box means that the space is allocated on the heap.
        left: Box<Tree<T>>,
        right: Box<Tree<T>>,
    },
}

impl<T> Tree<T> {
    /// Create an empty tree
    pub fn empty(hash: Digest) -> Self {
        Tree::Empty {
            hash: hash.as_ref().into(),
        }
    }

    /// Create a new tree
    pub fn new(hash: Digest, value: T) -> Self {
        Tree::Leaf {
            hash: hash.as_ref().into(),
            value,
        }
    }

    /// Create a new leaf
    pub fn new_leaf(algo: &'static Algorithm, value: T) -> Tree<T>
    where
        T: Hashable,
    {
        let hash = algo.hash_leaf(&value);
        // println!("=> {:?}", hash);
        Tree::new(hash, value)
    }

    /// Returns a hash from the tree.
    pub fn hash(&self) -> &Vec<u8> {
        match *self {
            Tree::Empty { ref hash } => hash,
            Tree::Leaf { ref hash, .. } => hash,
            Tree::Node { ref hash, .. } => hash,
        }
    }

    /// Returns a borrowing iterator over the leaves of the tree.
    pub fn iter(&self) -> LeavesIterator<T> {
        LeavesIterator::new(self)
    }
}

/// An borrowing iterator over the leaves of a `Tree`.
/// Adapted from http://codereview.stackexchange.com/q/110283.
#[allow(missing_debug_implementations)]
pub struct LeavesIterator<'a, T>
where
    T: 'a,
{
    current_value: Option<&'a T>,
    right_nodes: Vec<&'a Tree<T>>,
}

impl<'a, T> LeavesIterator<'a, T> {
    fn new(root: &'a Tree<T>) -> Self {
        let mut iter = LeavesIterator {
            current_value: None,
            right_nodes: Vec::new(),
        };

        iter.add_left(root);

        iter
    }

    fn add_left(&mut self, mut tree: &'a Tree<T>) {
        loop {
            match *tree {
                Tree::Empty { .. } => {
                    self.current_value = None;
                    break;
                }

                Tree::Node {
                    ref left,
                    ref right,
                    ..
                } => {
                    self.right_nodes.push(right);
                    tree = left;
                }

                Tree::Leaf { ref value, .. } => {
                    self.current_value = Some(value);
                    break;
                }
            }
        }
    }
}

impl<'a, T> Iterator for LeavesIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let result = self.current_value.take();

        if let Some(rest) = self.right_nodes.pop() {
            self.add_left(rest);
        }

        result
    }
}

/// An iterator over the leaves of a `Tree`.
#[allow(missing_debug_implementations)]
pub struct LeavesIntoIterator<T> {
    current_value: Option<T>,
    right_nodes: Vec<Tree<T>>,
}

impl<T> LeavesIntoIterator<T> {
    fn new(root: Tree<T>) -> Self {
        let mut iter = LeavesIntoIterator {
            current_value: None,
            right_nodes: Vec::new(),
        };

        iter.add_left(root);

        iter
    }

    fn add_left(&mut self, mut tree: Tree<T>) {
        loop {
            match tree {
                Tree::Empty { .. } => {
                    self.current_value = None;
                    break;
                }

                Tree::Node { left, right, .. } => {
                    self.right_nodes.push(*right);
                    tree = *left;
                }

                Tree::Leaf { value, .. } => {
                    self.current_value = Some(value);
                    break;
                }
            }
        }
    }
}

impl<T> Iterator for LeavesIntoIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let result = self.current_value.take();

        if let Some(rest) = self.right_nodes.pop() {
            self.add_left(rest);
        }

        result
    }
}

impl<T> IntoIterator for Tree<T> {
    type Item = T;
    type IntoIter = LeavesIntoIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        LeavesIntoIterator::new(self)
    }
}