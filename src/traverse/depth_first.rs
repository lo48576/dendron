//! Depth-first traversal.

use core::iter;

use crate::node::Node;

/// Event for depth first traversal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DftEvent<T> {
    /// Opening of a range.
    ///
    /// For forward iteration, this event will be emitted when entering a node.
    Open(T),
    /// Closing of a range.
    ///
    /// For forward iteration, this event will be emitted when leaving a node.
    Close(T),
}

impl<T> DftEvent<T> {
    /// Returns the value with ownership.
    #[must_use]
    pub fn into_value(self) -> T {
        match self {
            Self::Open(v) => v,
            Self::Close(v) => v,
        }
    }

    /// Returns a reference to the value.
    #[must_use]
    pub fn as_value(&self) -> &T {
        match self {
            Self::Open(v) => v,
            Self::Close(v) => v,
        }
    }

    /// Returns a mutable reference to the value.
    #[must_use]
    pub fn as_value_mut(&mut self) -> &mut T {
        match self {
            Self::Open(v) => v,
            Self::Close(v) => v,
        }
    }

    /// Converts the internal value.
    #[must_use]
    pub fn map<F, U>(self, f: F) -> DftEvent<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Self::Open(v) => DftEvent::Open(f(v)),
            Self::Close(v) => DftEvent::Close(f(v)),
        }
    }
}

impl<T> DftEvent<Node<T>> {
    /// Returns the next (forward direction) event.
    #[must_use]
    pub fn next(&self) -> Option<Self> {
        let next = match self {
            Self::Open(current) => {
                // Dive into the first child if available, or otherwise leave the node.
                match current.first_child() {
                    Some(child) => Self::Open(child),
                    None => Self::Close(current.clone()),
                }
            }
            Self::Close(current) => {
                // Dive into the next sibling if available, or leave the parent.
                match current.next_sibling() {
                    Some(next_sib) => Self::Open(next_sib),
                    None => Self::Close(current.parent()?),
                }
            }
        };
        Some(next)
    }

    /// Returns the previous (backward direction) event.
    #[must_use]
    pub fn prev(&self) -> Option<Self> {
        let prev = match self {
            Self::Close(current) => {
                // Dive into the last child if available, or otherwise leave the node.
                match current.last_child() {
                    Some(child) => Self::Close(child),
                    None => Self::Open(current.clone()),
                }
            }
            Self::Open(current) => {
                // Dive into the previous sibling if available, or leave the parent.
                match current.prev_sibling() {
                    Some(prev_sib) => Self::Close(prev_sib),
                    None => Self::Open(current.parent()?),
                }
            }
        };
        Some(prev)
    }
}

/// Depth first traversal iterator.
#[derive(Debug)]
pub struct DepthFirstTraverser<T> {
    /// Next event to emit, and the starting node.
    next: Option<(DftEvent<Node<T>>, Node<T>)>,
}

impl<T> Clone for DepthFirstTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> DepthFirstTraverser<T> {
    /// Creates a traverser from the opening of the given node.
    #[inline]
    #[must_use]
    pub fn with_start(next: Option<Node<T>>) -> Self {
        Self {
            next: next.map(|node| (DftEvent::Open(node.clone()), node)),
        }
    }

    /// Creates a traverser from the start node and the next event
    #[inline]
    #[must_use]
    pub fn with_next_event(start: Node<T>, next: Option<DftEvent<Node<T>>>) -> Self {
        Self {
            next: next.map(|next| (next, start)),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&DftEvent<Node<T>>> {
        self.next.as_ref().map(|(ev, _node)| ev)
    }
}

impl<T> Iterator for DepthFirstTraverser<T> {
    type Item = DftEvent<Node<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (next_ev, start) = self.next.take()?;
        self.next = next_ev.next().map(|next_of_next| (next_of_next, start));
        Some(next_ev)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.next.as_ref() {
            Some((DftEvent::Open(_), _)) => (2, None),
            Some((DftEvent::Close(next), start)) => {
                if Node::ptr_eq(next, start) {
                    // The next event is the last event.
                    (1, Some(1))
                } else {
                    (1, None)
                }
            }
            None => (0, Some(0)),
        }
    }
}

impl<T> iter::FusedIterator for DepthFirstTraverser<T> {}

/// Reverse depth first traversal iterator.
#[derive(Debug)]
pub struct ReverseDepthFirstTraverser<T> {
    /// Next event to emit, and the starting node.
    next: Option<(DftEvent<Node<T>>, Node<T>)>,
}

impl<T> Clone for ReverseDepthFirstTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> ReverseDepthFirstTraverser<T> {
    /// Creates a traverser from the opening of the given node.
    #[inline]
    #[must_use]
    pub fn with_start(next: Option<Node<T>>) -> Self {
        Self {
            next: next.map(|node| (DftEvent::Open(node.clone()), node)),
        }
    }

    /// Creates a traverser from the start node and the next event
    #[inline]
    #[must_use]
    pub fn with_next_event(start: Node<T>, next: Option<DftEvent<Node<T>>>) -> Self {
        Self {
            next: next.map(|next| (next, start)),
        }
    }

    /// Returns the next event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&DftEvent<Node<T>>> {
        self.next.as_ref().map(|(ev, _node)| ev)
    }
}

impl<T> Iterator for ReverseDepthFirstTraverser<T> {
    type Item = DftEvent<Node<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (next_ev, start) = self.next.take()?;
        self.next = next_ev.prev().map(|next_of_next| (next_of_next, start));
        Some(next_ev)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.next.as_ref() {
            Some((DftEvent::Close(_), _)) => (2, None),
            Some((DftEvent::Open(next), start)) => {
                if Node::ptr_eq(next, start) {
                    // The next event is the last event.
                    (1, Some(1))
                } else {
                    (1, None)
                }
            }
            None => (0, Some(0)),
        }
    }
}

impl<T> iter::FusedIterator for ReverseDepthFirstTraverser<T> {}
