//! Siblings traversal.

use core::iter;
use core::mem;

use crate::{FrozenNode, Node};

/// Siblings traverser.
#[derive(Debug)]
pub struct SiblingsTraverser<T> {
    /// Next node to return.
    next: Option<Node<T>>,
}

impl<T> Clone for SiblingsTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> SiblingsTraverser<T> {
    /// Creates a traverser from the given node.
    #[inline]
    #[must_use]
    pub fn new(first: Option<Node<T>>) -> Self {
        Self { next: first }
    }

    /// Returns the next item without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&Node<T>> {
        self.next.as_ref()
    }
}

impl<T> Iterator for SiblingsTraverser<T> {
    type Item = Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_of_next = self.next.as_ref()?.next_sibling();
        mem::replace(&mut self.next, next_of_next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.next.as_ref().is_some() {
            (1, None)
        } else {
            (0, Some(0))
        }
    }
}

impl<T> iter::FusedIterator for SiblingsTraverser<T> {}

/// Reverse siblings traverser.
#[derive(Debug)]
pub struct ReverseSiblingsTraverser<T> {
    /// Next node to return.
    next: Option<Node<T>>,
}

impl<T> Clone for ReverseSiblingsTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> ReverseSiblingsTraverser<T> {
    /// Creates a traverser from the given node.
    #[inline]
    #[must_use]
    pub fn new(last: Option<Node<T>>) -> Self {
        Self { next: last }
    }

    /// Returns the next item without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&Node<T>> {
        self.next.as_ref()
    }
}

impl<T> Iterator for ReverseSiblingsTraverser<T> {
    type Item = Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_of_next = self.next.as_ref()?.prev_sibling();
        mem::replace(&mut self.next, next_of_next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.next.as_ref().is_some() {
            (1, None)
        } else {
            (0, Some(0))
        }
    }
}

impl<T> iter::FusedIterator for ReverseSiblingsTraverser<T> {}

/// Stable siblings traverser.
#[derive(Debug)]
pub struct StableSiblingsTraverser<T> {
    /// Next node to return.
    next: Option<(FrozenNode<T>, FrozenNode<T>)>,
}

impl<T> Clone for StableSiblingsTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> StableSiblingsTraverser<T> {
    /// Creates a traverser of the children of the given node.
    #[inline]
    #[must_use]
    pub fn with_parent(parent: Option<FrozenNode<T>>) -> Self {
        Self {
            next: parent.and_then(|parent| parent.first_last_child()),
        }
    }

    /// Returns the next forward item without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&FrozenNode<T>> {
        self.next.as_ref().map(|(next, _next_back)| next)
    }

    /// Returns the next backward item without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek_back(&self) -> Option<&FrozenNode<T>> {
        self.next.as_ref().map(|(_next, next_back)| next_back)
    }
}

impl<T> Iterator for StableSiblingsTraverser<T> {
    type Item = FrozenNode<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let (next, next_back) = self.next.take()?;
        self.next = next
            .next_sibling()
            .map(|next_of_next| (next_of_next, next_back));
        Some(next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.next.as_ref().is_some() {
            (1, None)
        } else {
            (0, Some(0))
        }
    }
}

impl<T> DoubleEndedIterator for StableSiblingsTraverser<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (next, next_back) = self.next.take()?;
        self.next = next_back
            .prev_sibling()
            .map(|next_of_next_back| (next, next_of_next_back));
        Some(next_back)
    }
}

impl<T> iter::FusedIterator for StableSiblingsTraverser<T> {}
