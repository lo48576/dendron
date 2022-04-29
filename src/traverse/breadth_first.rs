//! Depth-first traversal.

use core::iter;

use alloc::collections::VecDeque;

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

/// Queued event for breadth-first traversal.
///
/// The size of this type must be equal to the size of `FrozenNode<T>` itself, due to
/// niche optimization.
#[derive(Debug)]
enum QueuedEvent<T> {
    /// Node at the current level.
    Node(FrozenNode<T>),
    /// No more nodes at the current level. Increment the depth.
    IncrementDepth,
}

impl<T> Clone for QueuedEvent<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Node(node) => Self::Node(node.clone()),
            Self::IncrementDepth => Self::IncrementDepth,
        }
    }
}

/// Allocating breadth-first tree traverser.
///
/// This traverser heap-allocates, and iterating all nodes is `O(n)` operation.
#[derive(Debug)]
pub struct AllocatingBreadthFirstTraverser<T> {
    /// Queued events.
    // This queue contains just one `IncrementDepth` whenever the queue is not
    // empty.
    events: VecDeque<QueuedEvent<T>>,
    /// Depth currently iterated.
    current_depth: usize,
}

impl<T> Clone for AllocatingBreadthFirstTraverser<T> {
    fn clone(&self) -> Self {
        Self {
            events: self.events.clone(),
            current_depth: self.current_depth,
        }
    }
}

impl<T> AllocatingBreadthFirstTraverser<T> {
    /// Creates a traverser from a toplevel node.
    ///
    /// The toplevel does not need to be the root of a tree.
    #[must_use]
    pub fn with_toplevel(toplevel: FrozenNode<T>, start_depth: usize) -> Self {
        let mut events = VecDeque::new();

        if start_depth == 0 {
            // Special case just to make the initialization efficient.
            events.push_back(QueuedEvent::Node(toplevel));
            events.push_back(QueuedEvent::IncrementDepth);
        } else {
            let nodes =
                StableShallowDepthFirstTraverser::with_toplevel(Some(toplevel), Some(start_depth))
                    .filter_map(DftEvent::into_open)
                    .filter_map(|(node, depth)| {
                        if depth == start_depth {
                            Some(node)
                        } else {
                            None
                        }
                    })
                    .map(QueuedEvent::Node);
            events.extend(nodes);
            events.push_back(QueuedEvent::IncrementDepth);
        }
        Self {
            events,
            current_depth: start_depth,
        }
    }

    /// Returns the next event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<(FrozenNode<T>, usize)> {
        match self.events.front().cloned()? {
            QueuedEvent::Node(next) => Some((next, self.current_depth)),
            QueuedEvent::IncrementDepth => match self.events.get(1).cloned()? {
                QueuedEvent::Node(next) => Some((next, self.current_depth + 1)),
                QueuedEvent::IncrementDepth => unreachable!(
                    "[consistency] `IncrementDepth` must not appear right after `IncrementDepth`"
                ),
            },
        }
    }

    /// Returns the current capacity of the internal buffer.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.events.capacity()
    }

    /// Shrinks the capacity of the internal buffer as much as possible.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.events.shrink_to_fit()
    }

    /// Shrinks the capacity of the internal buffer with a lower bound.
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.events.shrink_to(min_capacity)
    }
}

impl<T> Iterator for AllocatingBreadthFirstTraverser<T> {
    type Item = (FrozenNode<T>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(ev) = self.events.pop_front() {
            let next = match ev {
                QueuedEvent::Node(v) => v,
                QueuedEvent::IncrementDepth => {
                    if self.events.is_empty() {
                        // No more events to emit.
                        // Release the buffer since it won't be used anymore.
                        self.events = Default::default();
                        return None;
                    }
                    self.current_depth += 1;
                    self.events.push_back(QueuedEvent::IncrementDepth);
                    continue;
                }
            };

            // Get children of the node and push them to the queue.
            self.events
                .extend(next.children_stable().map(QueuedEvent::Node));

            return Some((next, self.current_depth));
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.events.len();
        // Note that if the queue always contains one `IncrementDepth` when the
        // queue is not empty.
        if len <= 1 {
            // Queue is empty, or contains only `IncrementDepth`.
            (0, Some(0))
        } else {
            (len - 1, None)
        }
    }
}
