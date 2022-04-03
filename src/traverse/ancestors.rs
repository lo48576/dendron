//! Ancestors traversal.

use core::iter;
use core::mem;

use crate::Node;

/// Ancestors traverser.
#[derive(Debug)]
pub struct AncestorsTraverser<T> {
    /// Next node to return.
    next: Option<Node<T>>,
}

impl<T> Clone for AncestorsTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> AncestorsTraverser<T> {
    /// Creates a traverser from the given node.
    #[inline]
    #[must_use]
    pub fn new(next: Option<Node<T>>) -> Self {
        Self { next }
    }

    /// Returns the next item without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&Node<T>> {
        self.next.as_ref()
    }
}

impl<T> Iterator for AncestorsTraverser<T> {
    type Item = Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_of_next = self.next.as_ref()?.parent();
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

impl<T> iter::FusedIterator for AncestorsTraverser<T> {}
