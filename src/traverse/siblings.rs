//! Siblings traversal.

use core::iter;
use core::mem;

use crate::Node;

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
