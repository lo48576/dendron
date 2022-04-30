//! Tree.

mod debug_print;
mod lock;

use core::cell::{BorrowError, RefCell};

use alloc::rc::Rc;

use crate::node::{IntraTreeLink, Node};
use crate::traverse::DftEvent;

pub use self::debug_print::DebugPrintTreeLocal;
use self::lock::HierarchyLockManager;
pub(crate) use self::lock::LockAggregatorForNode;
pub use self::lock::{
    HierarchyEditGrant, HierarchyEditGrantError, HierarchyEditProhibition,
    HierarchyEditProhibitionError,
};

/// A core data of a tree.
///
/// This also represents an ownership of a tree. Every tree has just one
/// corresponding `TreeCore`.
///
/// A value of this type is shared among nodes in the tree, so this will be
/// referred as `Rc<RefCell<TreeCore<T>>>` or `Weak<RefCell<TreeCore<T>>>`.
#[derive(Debug)]
pub(crate) struct TreeCore<T> {
    /// Root node.
    root: RefCell<IntraTreeLink<T>>,
    /// Hierarchy lock manager.
    lock_manager: HierarchyLockManager,
}

impl<T> TreeCore<T> {
    /// Creates a new tree core.
    #[must_use]
    pub(crate) fn new_rc(root: IntraTreeLink<T>) -> Rc<Self> {
        Rc::new(Self {
            root: RefCell::new(root),
            lock_manager: Default::default(),
        })
    }

    /// Returns a link to the root node.
    #[must_use]
    pub(crate) fn root_link(&self) -> IntraTreeLink<T> {
        self.root
            .try_borrow()
            .expect("[consistency] `TreeCore::root` should not be borrowed nestedly")
            .clone()
    }

    /// Transfers a lock.
    ///
    /// # Failures
    ///
    /// Fails if the tree `dest` cannot be locked with the currently active
    /// tree hierarchy edit lock for `self`.
    // Intended only for use by `membership` module.
    pub(crate) fn transfer_single_lock_to(
        self: &Rc<TreeCore<T>>,
        dest: &Rc<TreeCore<T>>,
    ) -> Result<(), ()> {
        self.lock_manager
            .transfer_single_lock_to(&dest.lock_manager)
    }
}

// This drop prevents stack overflow on drop of very wide or very deep tree.
impl<T> Drop for TreeCore<T> {
    fn drop(&mut self) {
        // This panic should never happen (unless there are a bug).
        let root_link = self
            .root
            .try_borrow()
            .expect("[validity] `TreeCore` is being accessed exclusively")
            .clone();
        // Not using `DepthFirstLinkTraverser` here is intentional.
        // The links would be in inconsistent states before being dropped, so
        // avoid introducing hidden invariants from `DepthFirstLinkTraverser`.
        let mut next = Some(DftEvent::Open(root_link));
        while let Some(current) = next.take() {
            next = current.next();
            let close_link = match current {
                DftEvent::Open(_) => continue,
                DftEvent::Close(v) => v,
            };

            // Drop the leaf node.
            // It is safe to leave `prev_sibling_cyclic` inconsistent, since
            // `DftEvent<IntraTreeLink<T>>` is guaranteed to use only
            // `first_child`, `next_sibling`, and `parent` fields, and use once
            // respectively.
            if let Some(parent_link) = close_link.parent_link() {
                // This panic should never happen (unless there are a bug).
                let next_sibling = close_link.replace_next_sibling(None);
                // This panic should never happen (unless there are a bug).
                parent_link.replace_first_child(next_sibling);
            }
            drop(close_link);
        }
    }
}

/// Debug printing.
impl<T> TreeCore<T> {
    /// Returns a debug-printable proxy that does not dump nodes.
    #[inline]
    #[must_use]
    pub(crate) fn debug_print_local(&self) -> DebugPrintTreeLocal<'_, T> {
        DebugPrintTreeLocal::new(self)
    }
}

/// A reference to the tree, with shared ownership.
///
/// Tree cannot exist without the root node, so you should create tree by
/// creating a new root node. See [`Node::new_tree`] and
/// [`HotNode::new_tree`][`crate::HotNode::new_tree`].
///
/// There are convenience macro to create a tree ([`tree!`][`crate::tree!`]) or
/// a root node ([`tree_node!`][`crate::tree_node!`]).
#[derive(Debug)]
pub struct Tree<T> {
    /// A reference to the tree core.
    core: Rc<TreeCore<T>>,
}

impl<T, U: PartialEq<U>> PartialEq<Tree<U>> for Tree<T>
where
    T: PartialEq<U>,
{
    /// Compares two trees.
    ///
    /// Returns `Ok(true)` if the two trees are equal, even if they are stored
    /// in different allocation.
    ///
    /// # Panics
    ///
    /// May panic if associated data of some nodes are already borrowed
    /// exclusively (i.e. mutably).
    ///
    /// To avoid panicking, use [`try_eq`][`Self::try_eq`] method.
    ///
    /// # Examples
    ///
    /// See the documentation for [`try_eq`][`Self::try_eq`] method.
    #[inline]
    fn eq(&self, other: &Tree<U>) -> bool {
        self.try_eq(other).expect(
            "[precondition] data associated to the nodes in both trees should be borrowable",
        )
    }
}

impl<T: Eq> Eq for Tree<T> {}

impl<T> Tree<T> {
    /// Creates a new `Tree` from the given `Rc` to the core tree.
    #[inline]
    #[must_use]
    pub(crate) fn from_core_rc(core: Rc<TreeCore<T>>) -> Self {
        Self { core }
    }

    /// Returns the root node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Tree, tree};
    ///
    /// let tree = tree! {
    ///     "root", ["0"]
    /// };
    /// //  root
    /// //  `-- 0
    ///
    /// assert_eq!(*tree.root().borrow_data(), "root");
    /// ```
    #[inline]
    #[must_use]
    pub fn root(&self) -> Node<T> {
        let root_link = self.core.root_link();
        let membership = root_link
            .membership()
            .upgrade()
            .expect("[validity] the root node must have valid membership since the tree is alive");

        Node::with_link_and_membership(root_link, membership)
    }

    /// Prohibits the tree hierarchy edit.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Tree, tree};
    ///
    /// let tree = tree! {
    ///     "root", ["0"]
    /// };
    /// //  root
    /// //  `-- 0
    ///
    /// let prohibition = tree
    ///     .prohibit_hierarchy_edit()
    ///     .expect("hierarchy edit should not yet be granted");
    ///
    /// assert!(prohibition.is_valid_for_node(&tree.root()));
    /// ```
    #[inline]
    pub fn prohibit_hierarchy_edit(
        &self,
    ) -> Result<HierarchyEditProhibition<T>, HierarchyEditProhibitionError> {
        HierarchyEditProhibition::new(&self.core)
    }

    /// Grants the tree hierarchy edit.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Tree, tree};
    ///
    /// let tree = tree! {
    ///     "root", ["0"]
    /// };
    /// //  root
    /// //  `-- 0
    ///
    /// let grant = tree
    ///     .grant_hierarchy_edit()
    ///     .expect("hierarchy edit should not yet be prohibition");
    ///
    /// assert!(grant.is_valid_for_node(&tree.root()));
    /// ```
    #[inline]
    pub fn grant_hierarchy_edit(&self) -> Result<HierarchyEditGrant<T>, HierarchyEditGrantError> {
        HierarchyEditGrant::new(&self.core)
    }

    /// Returns `true` if the two `Tree`s point to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree;
    ///
    /// let tree1 = tree!("root");
    /// let tree2 = tree!("root");
    ///
    /// assert!(tree1.ptr_eq(&tree1));
    ///
    /// assert!(tree1 == tree2, "same content and hierarchy");
    /// assert!(
    ///     !tree1.ptr_eq(&tree2),
    ///     "same content and hierarchy but different allocation"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.core, &other.core)
    }

    /// Compares two trees.
    ///
    /// Returns `Ok(true)` if the two trees are equal, even if they are stored
    /// in different allocation.
    ///
    /// # Failures
    ///
    /// May return `Err(_)` if associated data of some nodes are already
    /// borrowed exclusively (i.e. mutably).
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{tree, Tree};
    ///
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   `-- 0-1
    /// //  |       `-- 0-1-0
    /// //  `-- 1
    /// let tree1: Tree<&'static str> = tree! {
    ///     "root", [
    ///         /("0", [
    ///             "0-0",
    ///             /("0-1", [
    ///                 "0-1-0",
    ///             ]),
    ///         ]),
    ///         "1",
    ///     ]
    /// };
    ///
    /// //  0
    /// //  |-- 0-0
    /// //  `-- 0-1
    /// //      `-- 0-1-0
    /// let tree2: Tree<String> = tree! {
    ///     "0".to_owned(), [
    ///         "0-0".into(),
    ///         /("0-1".into(), [
    ///             "0-1-0".into(),
    ///         ]),
    ///     ]
    /// };
    ///
    /// assert!(
    ///     !tree1.try_eq(&tree2).expect("data are not borrowed"),
    ///     "node1 and node2 are not equal"
    /// );
    ///
    /// let tree1_first_child_of_root = tree1.root()
    ///     .first_child()
    ///     .expect("the root of `tree1` has a child");
    /// assert!(
    ///     tree1_first_child_of_root
    ///         .try_eq(&tree2.root())
    ///         .expect("data are not borrowed"),
    ///     "the first child of the root of tree1 and tree2 are equal"
    /// );
    /// ```
    #[inline]
    pub fn try_eq<U>(&self, other: &Tree<U>) -> Result<bool, BorrowError>
    where
        T: PartialEq<U>,
    {
        self.root().try_eq(&other.root())
    }

    /// Creates a new tree that a clone of the tree.
    ///
    /// `Tree` type is a reference-conuted handle to the actual tree object, so
    /// `Tree::clone` (that is `<Tree as Clone>::clone`) does not duplicate the
    /// tree. Use this method to make an independent tree with the identical
    /// structure and content.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the tree is mutably
    /// (i.e. exclusively) borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree;
    ///
    /// let tree = tree! {
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
    /// let cloned = tree.try_clone_tree()
    ///     .expect("data are currently not borrowed");
    ///
    /// // Different allocation.
    /// assert!(!tree.ptr_eq(&cloned));
    /// // Identical content.
    /// assert_eq!(tree, cloned);
    /// ```
    #[inline]
    pub fn try_clone_tree(&self) -> Result<Self, BorrowError>
    where
        T: Clone,
    {
        self.root().try_clone_subtree().map(|root| root.tree())
    }

    /// Creates a new tree that a clone of the tree.
    ///
    /// See [`try_clone_tree`][`Self::try_clone_tree`] for detail.
    ///
    /// # Panics
    ///
    /// Panics if any data associated to the node in the tree is mutably
    /// (i.e. exclusively) borrowed.
    #[inline]
    #[must_use]
    pub fn clone_tree(&self) -> Self
    where
        T: Clone,
    {
        self.try_clone_tree()
            .expect("[precondition] data associated to nodes should be borrowable")
    }
}

/// Debug printing.
impl<T> Tree<T> {
    /// Returns a debug-printable proxy that does not dump nodes.
    #[inline]
    #[must_use]
    pub fn debug_print_local(&self) -> DebugPrintTreeLocal<'_, T> {
        self.core.debug_print_local()
    }
}
