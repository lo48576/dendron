//! Conversion between a tree and series of events.

use core::cell::BorrowError;
use core::fmt;
use core::num::NonZeroUsize;

use crate::node::{FrozenNode, HotNode, Node};
use crate::traverse::{self, DftEvent};

/// An event to build tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Event<T> {
    /// An opening of a node with the given associated data.
    Open(T),
    /// Consecutive closings of nodes.
    Close(NonZeroUsize),
}

impl<T> Event<T> {
    /// Creates `Close(_)` event from the given value easily.
    ///
    /// # Panics
    ///
    /// Panics if the given value is zero.
    #[must_use]
    pub fn close(level: usize) -> Self {
        let level =
            NonZeroUsize::new(level).expect("[precondition] the close level should not be zero");
        Self::Close(level)
    }
}

impl<T: Clone> TryFrom<DftEvent<Node<T>>> for Event<T> {
    type Error = BorrowError;

    fn try_from(ev: DftEvent<Node<T>>) -> Result<Self, Self::Error> {
        match ev {
            DftEvent::Open(node) => node.try_borrow_data().map(|data| Event::Open(data.clone())),
            DftEvent::Close(_) => Ok(Event::close(1)),
        }
    }
}

impl<T: Clone> TryFrom<DftEvent<FrozenNode<T>>> for Event<T> {
    type Error = BorrowError;

    fn try_from(ev: DftEvent<FrozenNode<T>>) -> Result<Self, Self::Error> {
        match ev {
            DftEvent::Open(node) => node.try_borrow_data().map(|data| Event::Open(data.clone())),
            DftEvent::Close(_) => Ok(Event::close(1)),
        }
    }
}

impl<T> FromIterator<Event<T>> for Result<Node<T>, TreeBuildError> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Event<T>>,
    {
        let mut builder = TreeBuilder::new();
        builder.push_events(iter)?;
        builder.finish()
    }
}

impl<T: Clone> FromIterator<DftEvent<Node<T>>> for Result<Node<T>, TreeBuildError> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = DftEvent<Node<T>>>,
    {
        let mut builder = TreeBuilder::new();
        builder.push_dft_events(iter)?;
        builder.finish()
    }
}

impl<T> FromIterator<Event<T>> for Result<FrozenNode<T>, TreeBuildError> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Event<T>>,
    {
        let mut builder = TreeBuilder::new();
        builder.push_events(iter)?;
        builder.finish().map(|root| {
            root.bundle_new_structure_edit_prohibition()
                .expect("[validity] brand-new tree must be lockable")
        })
    }
}

impl<T> FromIterator<Event<T>> for Result<HotNode<T>, TreeBuildError> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Event<T>>,
    {
        let mut builder = TreeBuilder::new();
        builder.push_events(iter)?;
        builder.finish().map(|root| {
            root.bundle_new_structure_edit_grant()
                .expect("[validity] brand-new tree must be lockable")
        })
    }
}

/// An error for tree building from events.
#[derive(Debug)]
pub enum TreeBuildError {
    /// Root node is not yet opened.
    RootNotOpened,
    /// Root node is already closed.
    RootClosed,
    /// Failed to borrow node data.
    BorrowData(BorrowError),
}

impl fmt::Display for TreeBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::RootNotOpened => "attempt to close a node while root node is not yet opened",
            Self::RootClosed => {
                "cannot receive events anymore since the root node is already closed"
            }
            Self::BorrowData(_) => "cannot borrow node data because it was exclusively borrowed",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TreeBuildError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BorrowData(e) => Some(e),
            _ => None,
        }
    }
}

impl From<BorrowError> for TreeBuildError {
    #[inline]
    fn from(e: BorrowError) -> Self {
        Self::BorrowData(e)
    }
}

/// A builder to create a tree from series of events.
pub struct TreeBuilder<T> {
    /// Root node.
    root: Option<Node<T>>,
    /// Current node, i.e. the parent node to append a child if the next event is `Open`.
    current: Option<HotNode<T>>,
}

impl<T> Default for TreeBuilder<T> {
    #[inline]
    fn default() -> Self {
        Self {
            root: None,
            current: None,
        }
    }
}

impl<T> TreeBuilder<T> {
    /// Creates a new tree builder.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if the root node is already closed.
    #[inline]
    #[must_use]
    pub fn is_root_closed(&self) -> bool {
        self.root.is_some() && self.current.is_none()
    }

    /// Returns true if the root node is already created.
    #[inline]
    #[must_use]
    pub fn is_root_available(&self) -> bool {
        self.root.is_some()
    }

    /// Returns the constructed tree in `Result<_, _>`.
    ///
    /// Returns `None` if the root node is not yet opened.
    #[inline]
    pub fn finish(self) -> Result<Node<T>, TreeBuildError> {
        self.root.ok_or(TreeBuildError::RootNotOpened)
    }

    /// Returns the constructed tree in `Option<_>`.
    ///
    /// Returns `None` if the root node is not yet opened.
    #[inline]
    #[must_use]
    pub fn finish_opt(self) -> Option<Node<T>> {
        self.root
    }
}

impl<T> TreeBuilder<T> {
    /// Opens a new node.
    pub fn open(&mut self, data: T) -> Result<(), TreeBuildError> {
        if self.root.is_none() {
            let root = HotNode::new_tree(data);
            self.root = Some(root.plain());
            self.current = Some(root);

            return Ok(());
        }

        let current = self.current.as_mut().ok_or(TreeBuildError::RootClosed)?;
        *current = current.create_as_last_child(data);

        Ok(())
    }

    /// Closes the current node.
    pub fn close(&mut self, level: NonZeroUsize) -> Result<(), TreeBuildError> {
        if let Some(current) = &mut self.current {
            let parent_level = level.get() - 1;
            for _ in 0..parent_level {
                *current = current.parent().ok_or(TreeBuildError::RootClosed)?;
            }
            // Now `current` is a parent node of the result node.
            self.current = current.parent();
            Ok(())
        } else if self.root.is_some() {
            Err(TreeBuildError::RootClosed)
        } else {
            Err(TreeBuildError::RootNotOpened)
        }
    }

    /// Modifies the tree using the given event.
    pub fn push_event(&mut self, ev: Event<T>) -> Result<(), TreeBuildError> {
        match ev {
            Event::Open(data) => self.open(data),
            Event::Close(level) => self.close(level),
        }
    }

    /// Modifies the tree using the given events.
    pub fn push_events<I>(&mut self, events: I) -> Result<(), TreeBuildError>
    where
        I: IntoIterator<Item = Event<T>>,
    {
        self.push_events_impl(events.into_iter())
    }

    /// Modifies the tree using the given events.
    // Receive `Iterator` instead of `IntoIterator` directly in order to reduce
    // compile time and to mitigate binary bloat.
    fn push_events_impl<I>(&mut self, events: I) -> Result<(), TreeBuildError>
    where
        I: Iterator<Item = Event<T>>,
    {
        for ev in events {
            match ev {
                Event::Open(data) => self.open(data)?,
                Event::Close(level) => self.close(level)?,
            }
        }
        Ok(())
    }

    /// Modifies the tree using the given depth-first traversal event.
    pub fn push_dft_event(&mut self, ev: DftEvent<Node<T>>) -> Result<(), TreeBuildError>
    where
        T: Clone,
    {
        let ev: Event<T> = ev.try_into()?;
        self.push_event(ev)
    }

    /// Modifies the tree using the given depth-first traversal events.
    pub fn push_dft_events<I>(&mut self, events: I) -> Result<(), TreeBuildError>
    where
        I: IntoIterator<Item = DftEvent<Node<T>>>,
        T: Clone,
    {
        self.push_dft_events_impl(events.into_iter())
    }

    /// Modifies the tree using the given depth-first traversal events.
    // Receive `Iterator` instead of `IntoIterator` directly in order to reduce
    // compile time and to mitigate binary bloat.
    fn push_dft_events_impl<I>(&mut self, events: I) -> Result<(), TreeBuildError>
    where
        I: Iterator<Item = DftEvent<Node<T>>>,
        T: Clone,
    {
        for ev in events.map(TryInto::try_into) {
            match ev? {
                Event::Open(node) => self.open(node)?,
                Event::Close(level) => self.close(level)?,
            }
        }
        Ok(())
    }
}

/// An iterator type for serialized tree events.
#[derive(Debug, Clone)]
pub struct TreeSerializeIter<T> {
    /// Inner traverser.
    inner: traverse::DepthFirstTraverser<T>,
}

impl<T: Clone> TreeSerializeIter<T> {
    /// Creates a new iterator.
    #[inline]
    #[must_use]
    pub(crate) fn new(node: &Node<T>) -> Self {
        Self {
            inner: node.depth_first_traverse(),
        }
    }
}

impl<T: Clone> Iterator for TreeSerializeIter<T> {
    type Item = Result<Event<T>, BorrowError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next()? {
            DftEvent::Open(node) => {
                Some(node.try_borrow_data().map(|data| Event::Open(data.clone())))
            }
            DftEvent::Close(_) => {
                let mut count: usize = 1;
                while let Some(DftEvent::Close(_)) = self.inner.peek() {
                    match count.checked_add(1) {
                        Some(v) => {
                            self.inner.next();
                            count = v;
                        }
                        None => break,
                    };
                }
                let level = NonZeroUsize::new(count)
                    .expect("[consistency] count starts from nonzero and increases monotonically");
                Some(Ok(Event::Close(level)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::vec;
    use alloc::vec::Vec;

    use crate::traverse::DftEvent;

    //  root
    //  |-- 0
    //  |-- 1
    //  |   |-- 1-0
    //  |   |-- 1-1
    //  |   `-- 1-2
    //  |       `-- 1-2-0
    //  `-- 2
    fn sample_events() -> Vec<Event<&'static str>> {
        vec![
            Event::Open("root"),
            Event::Open("0"),
            Event::close(1),
            Event::Open("1"),
            Event::Open("1-0"),
            Event::close(1),
            Event::Open("1-1"),
            Event::close(1),
            Event::Open("1-2"),
            Event::Open("1-2-0"),
            Event::close(3),
            Event::Open("2"),
            Event::close(2),
        ]
    }

    const DFT_EVENTS: &[DftEvent<&str>] = &[
        DftEvent::Open("root"),
        DftEvent::Open("0"),
        DftEvent::Close("0"),
        DftEvent::Open("1"),
        DftEvent::Open("1-0"),
        DftEvent::Close("1-0"),
        DftEvent::Open("1-1"),
        DftEvent::Close("1-1"),
        DftEvent::Open("1-2"),
        DftEvent::Open("1-2-0"),
        DftEvent::Close("1-2-0"),
        DftEvent::Close("1-2"),
        DftEvent::Close("1"),
        DftEvent::Open("2"),
        DftEvent::Close("2"),
        DftEvent::Close("root"),
    ];

    fn sample_tree() -> Node<&'static str> {
        sample_events()
            .into_iter()
            .collect::<Result<_, _>>()
            .expect("valid events that can construct tree")
    }

    // node -> events.
    #[test]
    fn check_events() {
        let root = sample_tree();
        let dft_events = root
            .depth_first_traverse()
            .map(|ev| ev.map(|node| *node.borrow_data()))
            .collect::<Vec<_>>();

        assert_eq!(dft_events, DFT_EVENTS);
    }

    // events -> node -> events.
    #[test]
    fn roundtrip_from_events() {
        let expected_events = sample_events();
        let root: Node<&'static str> = expected_events
            .iter()
            .cloned()
            .collect::<Result<_, _>>()
            .expect("valid events that can construct tree");

        let expected_events = expected_events.into_iter().collect::<Vec<_>>();
        let events = root
            .to_events()
            .collect::<Result<Vec<_>, _>>()
            .expect("data associated to any nodes are not borrowed");

        assert_eq!(events, expected_events);
    }

    // dft-events -> node -> events.
    #[test]
    fn collect_dft_events() {
        let root = sample_tree();
        let expected_events = sample_events();

        let cloned_root: Node<_> = root
            .depth_first_traverse()
            .collect::<Result<_, _>>()
            .expect("tree should be traversable and events should be consistent");
        let events = cloned_root
            .to_events()
            .collect::<Result<Vec<_>, _>>()
            .expect("data associated to any nodes are not borrowed");

        assert_eq!(events, expected_events);
    }
}
