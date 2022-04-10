//! Depth-first traversal.

use core::iter;

use crate::node::{FrozenNode, HotNode, Node};

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

/// Implements `DftEvent<$ty_node<T>>::{next,prev}`.
macro_rules! impl_dft_event_methods_for_node {
    ($ty_node:ident) => {
        impl<T> DftEvent<$ty_node<T>> {
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
    };
}

impl_dft_event_methods_for_node!(Node);
impl_dft_event_methods_for_node!(FrozenNode);
impl_dft_event_methods_for_node!(HotNode);

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

/// Stable depth first traversal iterator.
#[derive(Debug)]
pub struct StableDepthFirstTraverser<T> {
    /// Next event to emit, and the starting node.
    // The actual type is `Option<(DftEvent<FrozenNode<T>>, DftEvent<FrozenNode<T>>)>`,
    // and clippy lint `clippy::type_complexity` complains it is too complex...
    // However, "an optional pair of next and next_back events" is actually
    // so simple and clear!
    next: Option<(<Self as Iterator>::Item, <Self as Iterator>::Item)>,
}

impl<T> Clone for StableDepthFirstTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<T> StableDepthFirstTraverser<T> {
    /// Creates a traverser from the opening to the closing of the given node.
    #[must_use]
    pub fn with_toplevel(next: Option<FrozenNode<T>>) -> Self {
        Self {
            next: next.map(|node| (DftEvent::Open(node.clone()), DftEvent::Close(node))),
        }
    }

    /// Creates a traverser from the start node and the next event
    #[inline]
    #[must_use]
    pub fn with_first_last_event(
        first: DftEvent<FrozenNode<T>>,
        last: DftEvent<FrozenNode<T>>,
    ) -> Self {
        Self {
            next: Some((first, last)),
        }
    }

    /// Returns the next forward event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&DftEvent<FrozenNode<T>>> {
        self.next.as_ref().map(|(next, _next_back)| next)
    }

    /// Returns the next backward event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek_back(&self) -> Option<&DftEvent<FrozenNode<T>>> {
        self.next.as_ref().map(|(_next, next_back)| next_back)
    }
}

impl<T> Iterator for StableDepthFirstTraverser<T> {
    type Item = DftEvent<FrozenNode<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (next, next_back) = self.next.take()?;
        self.next = next.next().map(|next_of_next| (next_of_next, next_back));
        Some(next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.next.as_ref() {
            Some((DftEvent::Open(next), DftEvent::Open(next_back)))
            | Some((DftEvent::Close(next), DftEvent::Close(next_back)))
                if FrozenNode::ptr_eq(next, next_back) =>
            {
                // The next event is the last event.
                (1, Some(1))
            }
            Some((_, _)) => (2, None),
            None => (0, Some(0)),
        }
    }
}

impl<T> DoubleEndedIterator for StableDepthFirstTraverser<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (next, next_back) = self.next.take()?;
        self.next = next_back
            .prev()
            .map(|prev_of_next_back| (next, prev_of_next_back));
        Some(next_back)
    }
}

impl<T> iter::FusedIterator for StableDepthFirstTraverser<T> {}
