//! Depth-first traversal.

use core::iter;

use crate::node::FrozenNode;
use crate::traverse::{DftEvent, StableShallowDepthFirstTraverser};

/// Non-allocating breadth-first tree traverser.
///
/// This traverser does not heap-allocate by itself.
/// (However `FrozenNode<T>` itself uses heap allocation.)
///
/// Note that traversing all nodes will be `O(n^2)` operation in worst case,
/// not `O(n)`.
#[derive(Debug)]
pub struct NonAllocatingBreadthFirstTraverser<T> {
    /// Internal shallow depth-first traverser.
    inner: StableShallowDepthFirstTraverser<T>,
    /// Root node.
    ///
    /// If this is `None`, it means that the iteration has been completed.
    root: Option<FrozenNode<T>>,
    /// Depth currently iterated.
    current_depth: usize,
}

impl<T> Clone for NonAllocatingBreadthFirstTraverser<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            root: self.root.clone(),
            current_depth: self.current_depth,
        }
    }
}

impl<T> NonAllocatingBreadthFirstTraverser<T> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    #[must_use]
    pub fn with_toplevel(toplevel: FrozenNode<T>, start_depth: usize) -> Self {
        Self {
            inner: StableShallowDepthFirstTraverser::with_toplevel(
                Some(toplevel.clone()),
                Some(start_depth),
            ),
            root: Some(toplevel),
            current_depth: start_depth,
        }
    }

    /// Returns the next node open event with the current depth.
    fn next_in_current_depth(&mut self) -> Option<FrozenNode<T>> {
        self.inner
            .by_ref()
            .filter_map(DftEvent::into_open)
            .find_map(|(node, depth)| {
                if depth == self.current_depth {
                    Some(node)
                } else {
                    None
                }
            })
    }
}

impl<T> Iterator for NonAllocatingBreadthFirstTraverser<T> {
    type Item = (FrozenNode<T>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let _ = self.root.as_ref()?;

        // Get the next event in the current depth, if available.
        if let Some(node) = self.next_in_current_depth() {
            return Some((node, self.current_depth));
        }

        // No more nodes in the current depth. Go deeper.
        self.current_depth += 1;
        self.inner = StableShallowDepthFirstTraverser::with_toplevel(
            self.root.clone(),
            Some(self.current_depth),
        );

        // Retry with the deeper depth.
        if let Some(node) = self.next_in_current_depth() {
            return Some((node, self.current_depth));
        }

        // If failed, there are no more nodes to iterate. All nodes are iterated.
        self.root = None;
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.root.is_none() {
            (0, Some(0))
        } else {
            (0, None)
        }
    }
}

impl<T> iter::FusedIterator for NonAllocatingBreadthFirstTraverser<T> {}
