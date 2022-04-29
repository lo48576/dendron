//! Conversion between a tree and series of events.

use core::cell::BorrowError;
use core::fmt;

use crate::node::{FrozenNode, HotNode, Node};
use crate::traverse::{self, DftEvent};

/// An event to build tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Event<T> {
    /// An opening of a node with the given associated data.
    Open(T),
    /// The number of consecutive closings of nodes.
    Close(usize),
}

impl<T> Event<T> {
    /// Converts the internal open value.
    pub fn map<F, U>(self, f: F) -> Event<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Self::Open(v) => Event::Open(f(v)),
            Self::Close(v) => Event::Close(v),
        }
    }
}

impl<T: Clone> TryFrom<DftEvent<Node<T>>> for Event<T> {
    type Error = BorrowError;

    fn try_from(ev: DftEvent<Node<T>>) -> Result<Self, Self::Error> {
        match ev {
            DftEvent::Open(node) => node.try_borrow_data().map(|data| Event::Open(data.clone())),
            DftEvent::Close(_) => Ok(Event::Close(1)),
        }
    }
}

impl<T: Clone> TryFrom<DftEvent<FrozenNode<T>>> for Event<T> {
    type Error = BorrowError;

    fn try_from(ev: DftEvent<FrozenNode<T>>) -> Result<Self, Self::Error> {
        match ev {
            DftEvent::Open(node) => node.try_borrow_data().map(|data| Event::Open(data.clone())),
            DftEvent::Close(_) => Ok(Event::Close(1)),
        }
    }
}

impl<T: Clone> TryFrom<DftEvent<HotNode<T>>> for Event<T> {
    type Error = BorrowError;

    fn try_from(ev: DftEvent<HotNode<T>>) -> Result<Self, Self::Error> {
        match ev {
            DftEvent::Open(node) => node.try_borrow_data().map(|data| Event::Open(data.clone())),
            DftEvent::Close(_) => Ok(Event::Close(1)),
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
            root.bundle_new_hierarchy_edit_prohibition()
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
            root.bundle_new_hierarchy_edit_grant()
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
    ///
    /// This can happen when the associated data of the given nodes wrapped by
    /// [`DftEvent`] are already exclusively (i.e. mutably) borrowed.
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
///
/// # Usage
///
/// ## 1. Create a builder.
///
/// To create brand-new tree:
///
/// ```
/// use dendron::serial::TreeBuilder;
///
/// let mut builder = TreeBuilder::<&'static str>::new();
/// ```
///
/// Or, to create subtree under some existing node:
///
/// ```
/// use dendron::HotNode;
/// use dendron::serial::TreeBuilder;
///
/// let some_existing_node = HotNode::new_tree("sample");
///
/// let mut builder = TreeBuilder::with_root(some_existing_node);
/// ```
///
/// Note that you may need to specify node data type when you call
/// [`TreeBuilder::new`].
///
/// ## 2. Put events to the builder.
///
/// Using direct methods:
///
/// ```
/// use dendron::serial::{TreeBuilder, Event};
///
/// let mut builder = TreeBuilder::<&'static str>::new();
///
/// // Open a new node with the associated data `"root"`.
/// builder.open("root")?;
/// // Close one node.
/// builder.close(1)?;
/// # Ok::<_, dendron::serial::TreeBuildError>(())
/// ```
///
/// Using [`Event`] type:
///
/// ```
/// use dendron::serial::{TreeBuilder, Event};
///
/// let mut builder = TreeBuilder::<&'static str>::new();
///
/// // Open a new node with the associated data `"root"`.
/// builder.push_event(Event::Open("root"))?;
/// // Close one node.
/// builder.push_event(Event::Close(1))?;
/// # Ok::<_, dendron::serial::TreeBuildError>(())
/// ```
///
/// Using [`traverse::DftEvent<Node<T>>`][`crate::traverse::DftEvent`] type:
///
/// ```
/// use dendron::Node;
/// use dendron::serial::{TreeBuilder, Event};
/// use dendron::traverse::DftEvent;
///
/// let node = Node::new_tree("sample");
/// let mut builder = TreeBuilder::<&'static str>::new();
///
/// builder.push_dft_event(DftEvent::Open(node.clone()))?;
/// builder.push_dft_event(DftEvent::Close(node))?;
/// # Ok::<_, dendron::serial::TreeBuildError>(())
/// ```
///
/// And additionally, iterator versions exist ([`push_events`][`Self::push_events`]
/// and [`push_dft_events`][`Self::push_dft_events`]).
///
/// ## 3. Finalize.
///
/// ```
/// use dendron::serial::{TreeBuilder, Event};
///
/// let mut builder = TreeBuilder::<&'static str>::new();
///
/// builder.push_event(Event::Open("root"))?;
/// builder.push_event(Event::Close(1))?;
///
/// let new_node = builder.finish()?;
///
/// assert!(new_node.is_root());
/// assert!(!new_node.has_children());
/// assert_eq!(*new_node.borrow_data(), "root");
/// # Ok::<_, dendron::serial::TreeBuildError>(())
/// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::TreeBuilder;
    ///
    /// let builder = TreeBuilder::<i32>::new();
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new tree builder with the root node set.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let root = HotNode::new_tree("root");
    /// let child = root.create_as_last_child("child");
    ///
    /// let mut builder = TreeBuilder::with_root(child.clone());
    ///
    /// // Create a child node of `child` with associated data "grandchild".
    /// builder.push_event(Event::Open("grandchild"))?;
    /// builder.push_event(Event::Close(1))?;
    /// builder.finish()?;
    ///
    /// assert!(child.has_children(), "node \"grandchild\" is added under `child`");
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn with_root(root: HotNode<T>) -> Self {
        Self {
            root: Some(root.plain()),
            current: Some(root),
        }
    }

    /// Returns true if the root node is already closed.
    ///
    /// If this returns true, pushing more events will result in
    /// [`RootClosed`][`TreeBuildError::RootClosed`] error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    /// assert!(!builder.is_root_closed());
    ///
    /// builder.push_event(Event::Open("root"))?;
    /// assert!(!builder.is_root_closed());
    ///
    /// builder.push_event(Event::Close(1))?;
    /// assert!(builder.is_root_closed());
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn is_root_closed(&self) -> bool {
        self.root.is_some() && self.current.is_none()
    }

    /// Returns true if the root node is already created.
    ///
    /// If this returns true, [`finish`][`Self::finish`] method won't fail with
    /// [`RootNotOpened`][`TreeBuildError::RootNotOpened`] error.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    /// assert!(!builder.is_root_available());
    ///
    /// builder.push_event(Event::Open("root"));
    /// assert!(builder.is_root_available());
    ///
    /// builder.push_event(Event::Close(1));
    /// assert!(builder.is_root_available());
    /// ```
    ///
    /// If the root node is provided at the builder creation, this returns true.
    ///
    /// ```
    /// use dendron::HotNode;
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let root = HotNode::new_tree("root");
    /// let child = root.create_as_last_child("child");
    ///
    /// let mut builder = TreeBuilder::with_root(child);
    /// assert!(builder.is_root_available(), "root is already provided and is open");
    /// ```
    #[inline]
    #[must_use]
    pub fn is_root_available(&self) -> bool {
        self.root.is_some()
    }

    /// Returns the constructed tree in `Result<Node<T>, _>`.
    ///
    /// # Failures
    ///
    /// Fails with [`RootNotOpened`][`TreeBuildError::RootNotOpened`] if no root
    /// node is opened.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   `-- 0-1
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    /// let expected = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             "0-0",
    ///             "0-1",
    ///         ]),
    ///         "1",
    ///         /("2", [
    ///             "2-0",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let mut builder = TreeBuilder::new();
    /// builder.push_events([
    ///     Event::Open("root"),
    ///     Event::Open("0"),
    ///     Event::Open("0-0"),
    ///     // Close `0-0`.
    ///     Event::Close(1),
    ///     Event::Open("0-1"),
    ///     // Close `0-1` and `0`.
    ///     Event::Close(2),
    ///     Event::Open("1"),
    ///     // Close `1`.
    ///     Event::Close(1),
    ///     Event::Open("2"),
    ///     Event::Open("2-0"),
    ///     // Close `2-0`, `2`, and `root`.
    ///     Event::Close(3),
    /// ]).expect("valid events to create a tree");
    ///
    /// let node = builder.finish().expect("root node is created");
    /// assert_eq!(node, expected);
    /// ```
    #[inline]
    pub fn finish(self) -> Result<Node<T>, TreeBuildError> {
        self.root.ok_or(TreeBuildError::RootNotOpened)
    }

    /// Returns the constructed tree in `Option<_>`.
    ///
    /// # Failures
    ///
    /// Returns `None` if no root node is opened.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   `-- 0-1
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    /// let expected = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             "0-0",
    ///             "0-1",
    ///         ]),
    ///         "1",
    ///         /("2", [
    ///             "2-0",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let mut builder = TreeBuilder::new();
    /// builder.push_events([
    ///     Event::Open("root"),
    ///     Event::Open("0"),
    ///     Event::Open("0-0"),
    ///     // Close `0-0`.
    ///     Event::Close(1),
    ///     Event::Open("0-1"),
    ///     // Close `0-1` and `0`.
    ///     Event::Close(2),
    ///     Event::Open("1"),
    ///     // Close `1`.
    ///     Event::Close(1),
    ///     Event::Open("2"),
    ///     Event::Open("2-0"),
    ///     // Close `2-0`, `2`, and `root`.
    ///     Event::Close(3),
    /// ]).expect("valid events to create a tree");
    ///
    /// assert_eq!(builder.finish_opt(), Some(expected));
    /// ```
    #[inline]
    #[must_use]
    pub fn finish_opt(self) -> Option<Node<T>> {
        self.root
    }
}

impl<T> TreeBuilder<T> {
    /// Opens a new node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    ///
    /// builder.open("root")?;
    /// builder.open("child")?;
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
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
    ///
    /// # Failures
    ///
    /// Fails with [`RootClosed`][`TreeBuildError::RootClosed`] if the caller
    /// attempted to close more nodes while there are no open nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    ///
    /// builder.open("root")?;
    /// builder.open("child")?;
    /// builder.open("grandchild")?;
    ///
    /// // Close 1 child (only `grandchild`).
    /// builder.close(1)?;
    /// // Close 2 children (`child` and `root`).
    /// builder.close(2)?;
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
    pub fn close(&mut self, level: usize) -> Result<(), TreeBuildError> {
        if level == 0 {
            // Close zero nodes, i.e. do nothing.
            return Ok(());
        }
        if let Some(current) = &mut self.current {
            let parent_level = level - 1;
            for _ in 0..parent_level {
                let root = self
                    .root
                    .as_ref()
                    .expect("[validity] `root` should be set when some node is tracked");
                if current.ptr_eq_plain(root) {
                    // This is the root of the subtree, even if it has a parent.
                    return Err(TreeBuildError::RootClosed);
                }
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
    ///
    /// # Failures
    ///
    /// * Fails with [`RootNotOpened`][`TreeBuildError::RootNotOpened`] if no root
    ///   node is opened.
    /// * Fails with [`RootClosed`][`TreeBuildError::RootClosed`] if the caller
    ///   attempted to close more nodes while there are no open nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    ///
    /// builder.push_event(Event::Open("root"))?;
    /// builder.push_event(Event::Close(1))?;
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
    pub fn push_event(&mut self, ev: Event<T>) -> Result<(), TreeBuildError> {
        match ev {
            Event::Open(data) => self.open(data),
            Event::Close(level) => self.close(level),
        }
    }

    /// Modifies the tree using the given events.
    ///
    /// # Failures
    ///
    /// * Fails with [`RootNotOpened`][`TreeBuildError::RootNotOpened`] if no root
    ///   node is opened.
    /// * Fails with [`RootClosed`][`TreeBuildError::RootClosed`] if the caller
    ///   attempted to close more nodes while there are no open nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    ///
    /// builder.push_events([
    ///     Event::Open("root"),
    ///     Event::Close(1),
    /// ])?;
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
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
    ///
    /// # Failures
    ///
    /// * Fails with [`RootNotOpened`][`TreeBuildError::RootNotOpened`] if no root
    ///   node is opened.
    /// * Fails with [`RootClosed`][`TreeBuildError::RootClosed`] if the caller
    ///   attempted to close more nodes while there are no open nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    /// use dendron::serial::{Event, TreeBuilder};
    /// use dendron::traverse::DftEvent;
    ///
    /// let src = Node::new_tree("root");
    /// let mut builder = TreeBuilder::<&'static str>::new();
    ///
    /// builder.push_dft_event(DftEvent::Open(src.clone()))?;
    /// builder.push_dft_event(DftEvent::Close(src))?;
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
    pub fn push_dft_event(&mut self, ev: DftEvent<Node<T>>) -> Result<(), TreeBuildError>
    where
        T: Clone,
    {
        let ev: Event<T> = ev.try_into()?;
        self.push_event(ev)
    }

    /// Modifies the tree using the given depth-first traversal events.
    ///
    /// # Failures
    ///
    /// * Fails with [`RootNotOpened`][`TreeBuildError::RootNotOpened`] if no root
    ///   node is opened.
    /// * Fails with [`RootClosed`][`TreeBuildError::RootClosed`] if the caller
    ///   attempted to close more nodes while there are no open nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::serial::{Event, TreeBuilder};
    ///
    /// let src = tree_node! {
    ///     "root", [
    ///         "0",
    ///         /("1", [
    ///             "1-0",
    ///             "1-1",
    ///         ]),
    ///         "2",
    ///     ]
    /// };
    ///
    /// let mut builder = TreeBuilder::<&'static str>::new();
    ///
    /// builder.push_dft_events(src.depth_first_traverse())?;
    /// # Ok::<_, dendron::serial::TreeBuildError>(())
    /// ```
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
///
/// See [`Node::to_events`].
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
                Some(Ok(Event::Close(count)))
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

    mod builder {
        use super::*;

        #[test]
        fn root_not_opened() {
            let builder = TreeBuilder::<i32>::new();
            assert!(matches!(
                builder.finish(),
                Err(TreeBuildError::RootNotOpened)
            ));
        }

        #[test]
        fn excessive_close() {
            let mut builder = TreeBuilder::<&str>::new();
            builder.open("root").expect("root is not yet closed");
            assert!(matches!(builder.close(2), Err(TreeBuildError::RootClosed)));
        }
    }

    mod event_streaming {
        use super::*;

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
                Event::Close(1),
                Event::Open("1"),
                Event::Open("1-0"),
                Event::Close(1),
                Event::Open("1-1"),
                Event::Close(1),
                Event::Open("1-2"),
                Event::Open("1-2-0"),
                Event::Close(3),
                Event::Open("2"),
                Event::Close(2),
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
}
