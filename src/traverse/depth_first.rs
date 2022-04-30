//! Depth-first traversal.

use core::cmp::Ordering;
use core::iter;
use core::num::NonZeroUsize;

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
    #[inline]
    #[must_use]
    pub fn into_value(self) -> T {
        match self {
            Self::Open(v) => v,
            Self::Close(v) => v,
        }
    }

    /// Returns a reference to the value.
    #[inline]
    #[must_use]
    pub fn as_value(&self) -> &T {
        match self {
            Self::Open(v) => v,
            Self::Close(v) => v,
        }
    }

    /// Returns a mutable reference to the value.
    #[inline]
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

    /// Extracts the value for `Open` event if possible.
    #[inline]
    #[must_use]
    pub fn into_open(self) -> Option<T> {
        match self {
            Self::Open(v) => Some(v),
            Self::Close(_) => None,
        }
    }

    /// Extracts the value for `Close` event if possible.
    #[inline]
    #[must_use]
    pub fn into_close(self) -> Option<T> {
        match self {
            Self::Open(_) => None,
            Self::Close(v) => Some(v),
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
        self.next = match &next_ev {
            DftEvent::Close(next_close) if next_close.ptr_eq(&start) => None,
            _ => next_ev.next().map(|next_of_next| (next_of_next, start)),
        };
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
            next: next.map(|node| (DftEvent::Close(node.clone()), node)),
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
        self.next = match &next_ev {
            DftEvent::Open(next_open) if next_open.ptr_eq(&start) => None,
            _ => next_ev.prev().map(|next_of_next| (next_of_next, start)),
        };
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
    /// Next events to emit.
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

/// Stable possibly-limited-depth depth first traversal iterator.
#[derive(Debug)]
pub struct StableShallowDepthFirstTraverser<T> {
    /// Next events to emit.
    #[allow(clippy::type_complexity)]
    next: Option<(
        DftEvent<(FrozenNode<T>, usize)>,
        DftEvent<(FrozenNode<T>, usize)>,
    )>,
    /// The minimal depth to ignore.
    ///
    /// If `None`, no depth limit is set.
    /// If `Some(1)`, events only for root node are returned, i.e. the root node
    /// of the subtree is considered as depth 0 and events for the subtree root
    /// cannot be omitted.
    depth_ignore: Option<NonZeroUsize>,
}

impl<T> Clone for StableShallowDepthFirstTraverser<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
            depth_ignore: self.depth_ignore,
        }
    }
}

impl<T> StableShallowDepthFirstTraverser<T> {
    /// Creates a traverser from the opening to the closing of the given node.
    #[must_use]
    pub fn with_toplevel(next: Option<FrozenNode<T>>, max_depth: Option<usize>) -> Self {
        let depth_ignore = max_depth.and_then(|max| NonZeroUsize::new(max.wrapping_add(1)));
        Self {
            next: next.map(|node| {
                (
                    DftEvent::Open((node.clone(), 0)),
                    DftEvent::Close((node, 0)),
                )
            }),
            depth_ignore,
        }
    }

    /// Returns the next forward event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek(&self) -> Option<&DftEvent<(FrozenNode<T>, usize)>> {
        self.next.as_ref().map(|(next, _next_back)| next)
    }

    /// Returns the next backward event without advancing the iterator.
    #[inline]
    #[must_use]
    pub fn peek_back(&self) -> Option<&DftEvent<(FrozenNode<T>, usize)>> {
        self.next.as_ref().map(|(_next, next_back)| next_back)
    }

    /// Returns the maximum depth of a node event that allowed to be iterated.
    #[inline]
    #[must_use]
    pub fn max_depth(&self) -> usize {
        self.depth_ignore
            .map_or(usize::MAX, |ignore| ignore.get() - 1)
    }

    /// Returns the next forward event of the next forward event.
    #[must_use]
    fn next_of_next_forward(&mut self) -> Option<DftEvent<(FrozenNode<T>, usize)>> {
        let (next, next_back) = self.next.as_ref()?;
        match (next, next_back) {
            (DftEvent::Open((next, depth)), DftEvent::Open((next_back, depth_back)))
            | (DftEvent::Close((next, depth)), DftEvent::Close((next_back, depth_back)))
                if FrozenNode::ptr_eq(next, next_back) =>
            {
                // The next event is the last event.
                debug_assert_eq!(
                    depth, depth_back,
                    "[validity] the identical node should be at the same place"
                );
                return None;
            }
            _ => {}
        }
        let next_of_next = match next {
            DftEvent::Open((next, depth)) => {
                // Leave the node if the current node is at maximum depth.
                if *depth == self.max_depth() {
                    return Some(DftEvent::Close((next.clone(), *depth)));
                }
                // Dive into the first child if available, or otherwise leave the node.
                match next.first_child() {
                    Some(child) => DftEvent::Open((child, *depth + 1)),
                    None => DftEvent::Close((next.clone(), *depth)),
                }
            }
            DftEvent::Close((next, depth)) => {
                // Dive into the next sibling if available, or leave the parent.
                match next.next_sibling() {
                    Some(next_sib) => DftEvent::Open((next_sib, *depth)),
                    None => DftEvent::Close((next.parent()?, *depth - 1)),
                }
            }
        };
        Some(next_of_next)
    }

    /// Returns the next backward event of the next backward event.
    #[must_use]
    fn next_of_next_backward(&mut self) -> Option<DftEvent<(FrozenNode<T>, usize)>> {
        let (next, next_back) = self.next.as_ref()?;
        match (next, next_back) {
            (DftEvent::Open((next, depth)), DftEvent::Open((next_back, depth_back)))
            | (DftEvent::Close((next, depth)), DftEvent::Close((next_back, depth_back)))
                if FrozenNode::ptr_eq(next, next_back) =>
            {
                // The next event is the last event.
                debug_assert_eq!(
                    depth, depth_back,
                    "[validity] the identical node should be at the same place"
                );
                return None;
            }
            _ => {}
        }
        let next_of_next_backward = match next_back {
            DftEvent::Close((next, depth)) => {
                // Leave the node if the current node is at maximum depth.
                if *depth == self.max_depth() {
                    return Some(DftEvent::Open((next.clone(), *depth)));
                }
                // Dive into the last child if available, or otherwise leave the node.
                match next.last_child() {
                    Some(child) => DftEvent::Close((child, *depth + 1)),
                    None => DftEvent::Open((next.clone(), *depth)),
                }
            }
            DftEvent::Open((next, depth)) => {
                // Dive into the previous sibling if available, or leave the parent.
                match next.prev_sibling() {
                    Some(prev_sib) => DftEvent::Close((prev_sib, *depth)),
                    None => DftEvent::Open((next.parent()?, *depth - 1)),
                }
            }
        };
        Some(next_of_next_backward)
    }
}

impl<T> Iterator for StableShallowDepthFirstTraverser<T> {
    /// The node and the depth of the node.
    ///
    /// Depth 0 is for the root node of the subtree, depth `n+1` is for the
    /// children of the node with depth `n`, and so on...
    type Item = DftEvent<(FrozenNode<T>, usize)>;

    fn next(&mut self) -> Option<Self::Item> {
        let _ = self.next.as_ref()?;
        let next_of_next = self.next_of_next_forward();
        let (next, next_back) = self.next.take()?;
        self.next = next_of_next.map(|next_of_next| (next_of_next, next_back));
        Some(next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (next, next_back) = match &self.next {
            Some((next, next_back)) => (next, next_back),
            None => return (0, Some(0)),
        };
        match (next, next_back) {
            (DftEvent::Open((next, depth)), DftEvent::Open((next_back, depth_back))) => {
                if FrozenNode::ptr_eq(next, next_back) {
                    // The next event is the last event.
                    debug_assert_eq!(
                        depth, depth_back,
                        "[validity] the identical node should be at the same place"
                    );
                    return (1, Some(1));
                }
                let min = match depth.cmp(depth_back) {
                    // `Open` for `depth`, `Close` for `depth..=depth_back`, and `Open` for `depth_back`.
                    Ordering::Greater => depth - depth_back + 3,
                    // `Open`, `Close`, and `Open` again for `depth`.
                    Ordering::Equal => 3,
                    // `Open` for `depth..=depth_back`.
                    Ordering::Less => depth_back - depth + 1,
                };
                (min, None)
            }
            (DftEvent::Close((next, depth)), DftEvent::Close((next_back, depth_back))) => {
                if FrozenNode::ptr_eq(next, next_back) {
                    // The next event is the last event.
                    debug_assert_eq!(
                        depth, depth_back,
                        "[validity] the identical node should be at the same place"
                    );
                    return (1, Some(1));
                }
                let min = match depth.cmp(depth_back) {
                    // `Close` for `depth..=depth_back`.
                    Ordering::Greater => depth - depth_back + 1,
                    // `Close`, `Open`, and `Close` again for `depth`.
                    Ordering::Equal => 3,
                    // `Close` for `depth`, `Open` for `depth..=depth_back`, and `Close` for `depth_back`.
                    Ordering::Less => depth_back - depth + 3,
                };
                (min, None)
            }
            (DftEvent::Open((next, depth)), DftEvent::Close((next_back, depth_back))) => {
                let min = match depth.cmp(depth_back) {
                    // `Open` for `depth`, and `Close` for `depth..=depth_back`.
                    Ordering::Greater => depth - depth_back + 2,
                    // `Open` and `Close` for `depth`.
                    Ordering::Equal if FrozenNode::ptr_eq(next, next_back) => return (2, Some(2)),
                    // `Open`, `Close`, `Open` again, and `Close` again for `depth`.
                    Ordering::Equal => 4,
                    // `Open` for `depth..=depth_back`, and `Close` for `depth`.
                    Ordering::Less => depth_back - depth + 2,
                };
                (min, None)
            }
            (DftEvent::Close((_, depth)), DftEvent::Open((_, depth_back))) => {
                let min = match depth.cmp(depth_back) {
                    // `Close` for `depth..=depth_back`, and `Open` for `depth`.
                    Ordering::Greater => depth - depth_back + 2,
                    // `Close` and `Open` for `depth`.
                    Ordering::Equal => 2,
                    // `Close` for `depth`, and `Open` for `depth..=depth_back`.
                    Ordering::Less => depth_back - depth + 2,
                };
                (min, None)
            }
        }
    }
}

impl<T> DoubleEndedIterator for StableShallowDepthFirstTraverser<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let _ = self.next.as_ref()?;
        let next_of_next_back = self.next_of_next_backward();
        let (next, next_back) = self.next.take()?;
        self.next = next_of_next_back.map(|next_of_next_back| (next, next_of_next_back));
        Some(next_back)
    }
}

impl<T> iter::FusedIterator for StableShallowDepthFirstTraverser<T> {}
