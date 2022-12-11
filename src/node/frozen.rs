//! Frozen node, which is a [`Node`] with tree hierarchy edit prohibition bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::anchor::InsertAs;
use crate::node::debug_print::{DebugPrettyPrint, DebugPrintNodeLocal, DebugPrintSubtree};
use crate::node::{edit, HierarchyError, HotNode, Node, NodeCoreLink, NodeLink};
use crate::serial;
use crate::traverse;
use crate::tree::{HierarchyEditProhibition, HierarchyEditProhibitionError, Tree, TreeCore};

/// A [`Node`] with a tree hierarchy edit prohibition bundled.
///
/// `FrozenNode` can be created by [`Node::bundle_hierarchy_edit_prohibition`] or
/// [`Node::bundle_new_hierarchy_edit_prohibition`].
///
/// # Panics
///
/// Panics if the number of active edit prohibitions through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking prohibitions.
pub struct FrozenNode<T> {
    /// Node.
    inner: Node<T>,
}

impl<T> Drop for FrozenNode<T> {
    #[inline]
    fn drop(&mut self) {
        self.link().decrement_edit_lock_count();
    }
}

impl<T> Clone for FrozenNode<T> {
    #[inline]
    fn clone(&self) -> Self {
        self.link().increment_nonzero_edit_lock_count();
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for FrozenNode<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.debug_print_local().fmt(f)
    }
}

impl<T, U: PartialEq<U>> PartialEq<FrozenNode<U>> for FrozenNode<T>
where
    T: PartialEq<U>,
{
    /// Compares two subtrees.
    ///
    /// Returns `Ok(true)` if the two subtree are equal, even if they are stored
    /// in different allocation.
    ///
    /// # Panics
    ///
    /// May panic if associated data of some nodes are already borrowed
    /// exclusively (i.e. mutably).
    ///
    /// To avoid panicking, use [`Node::try_eq`] and [`plain`][`Self::plain`]
    /// method.
    ///
    /// # Examples
    ///
    /// See the documentation for [`Node::try_eq`] method.
    #[inline]
    fn eq(&self, other: &FrozenNode<U>) -> bool {
        self.link().try_eq(other.link()).expect(
            "[precondition] data associated to the nodes in both trees should be borrowable",
        )
    }
}

impl<T: Eq> Eq for FrozenNode<T> {}

impl<T> FrozenNode<T> {
    /// Creates a new `FrozenNode` from the given plain node.
    #[inline]
    pub(super) fn from_node(node: Node<T>) -> Result<Self, HierarchyEditProhibitionError> {
        node.link().acquire_edit_prohibition()?;
        Ok(Self { inner: node })
    }

    /// Creates a new `FrozenNode` from the given plain node and the prohibition.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit prohibition is not valid for the given node.
    ///
    /// Panics if there are too many prohibitions for the node or for the tree.
    #[must_use]
    pub(super) fn from_node_and_prohibition(
        node: Node<T>,
        prohibition: &HierarchyEditProhibition<T>,
    ) -> Self {
        prohibition.panic_if_invalid_for_node(&node);

        node.link()
            .acquire_edit_prohibition()
            .expect("[validity] a valid prohibition already exists for the tree");
        Self { inner: node }
    }

    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if a reference to the tree core is not valid.
    ///
    /// Panics if the tree is prohibited to be edited.
    #[must_use]
    pub(crate) fn from_node_link_with_prohibition(link: NodeCoreLink<T>) -> Self {
        let inner = Node::with_node_core(link);
        inner
            .link()
            .acquire_edit_prohibition()
            .expect("[consistency] there should have already been tree hierarchy edit prohibition");

        Self { inner }
    }

    /// Returns a reference to the node core.
    #[inline]
    #[must_use]
    pub(super) fn link(&self) -> &NodeLink<T> {
        self.inner.link()
    }

    /// Returns a reference to the node core.
    #[inline]
    #[must_use]
    pub(super) fn node_core(&self) -> &NodeCoreLink<T> {
        self.link().core()
    }

    /// Returns the tree core.
    #[inline]
    #[must_use]
    pub(super) fn tree_core(&self) -> Rc<TreeCore<T>> {
        self.link().tree_core()
    }

    /// Creates a plain node reference for the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{FrozenNode, Node};
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// let plain: Node<_> = frozen.plain();
    /// ```
    #[inline]
    #[must_use]
    pub fn plain(&self) -> Node<T> {
        self.inner.clone()
    }
}

impl<T> From<FrozenNode<T>> for Node<T> {
    #[inline]
    fn from(node: FrozenNode<T>) -> Self {
        node.plain()
    }
}

/// Tree hierarchy edit prohibitions.
impl<T> FrozenNode<T> {
    /// Returns a copy of the tree hierarchy edit prohibition.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{FrozenNode, Node};
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// let prohibition = frozen.extract_hierarchy_edit_prohibition();
    /// ```
    #[must_use]
    pub fn extract_hierarchy_edit_prohibition(&self) -> HierarchyEditProhibition<T> {
        self.tree()
            .prohibit_hierarchy_edit()
            .expect("[validity] the tree hierarchy is already prohibited to be edit")
    }
}

// Common methods below.

/// Data access.
impl<T> FrozenNode<T> {
    /// Returns a reference to the data associated to the node.
    ///
    /// # Failures
    ///
    /// Fails if the data is currently mutably (i.e. exclusively) borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert_eq!(
    ///     *frozen
    ///         .try_borrow_data()
    ///         .expect("should not fail since not mutably borrowed from other place"),
    ///     "root"
    /// );
    /// ```
    #[inline]
    pub fn try_borrow_data(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.node_core().try_borrow_data()
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert_eq!(*frozen.borrow_data(), "root");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data(&self) -> Ref<'_, T> {
        self.node_core().borrow_data()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// *frozen
    ///     .try_borrow_data_mut()
    ///     .expect("should not fail since not borrowed from other place")
    ///     = "ROOT";
    /// assert_eq!(*frozen.borrow_data(), "ROOT");
    /// ```
    #[inline]
    pub fn try_borrow_data_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.node_core().try_borrow_data_mut()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// *frozen.borrow_data_mut() = "ROOT";
    /// assert_eq!(*frozen.borrow_data(), "ROOT");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.node_core().borrow_data_mut()
    }

    /// Returns `true` if the two `FrozenNode`s point to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen1 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let frozen2 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen1.ptr_eq(&frozen1));
    ///
    /// assert!(frozen1 == frozen2, "same content and hierarchy");
    /// assert!(
    ///     !frozen1.ptr_eq(&frozen2),
    ///     "same content and hierarchy but different allocation"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        NodeCoreLink::ptr_eq(self.node_core(), other.node_core())
    }
}

/// Neighbor nodes accessor.
impl<T> FrozenNode<T> {
    /// Returns the tree the node belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let tree = frozen.tree();
    ///
    /// assert!(tree.root().ptr_eq(&frozen.plain()));
    /// ```
    #[inline]
    #[must_use]
    pub fn tree(&self) -> Tree<T> {
        Tree::from_core_rc(self.tree_core())
    }

    /// Returns true if the node is the root.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen.is_root());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_root(&self) -> bool {
        debug_assert_eq!(
            self.node_core().is_root(),
            self.tree_core().root_link().ptr_eq(self.node_core()),
        );
        // The node is a root if and only if the node has no parent.
        self.node_core().is_root()
    }

    /// Returns true if the node belongs to the given tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen1 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let frozen2 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen1.belongs_to(&frozen1.tree()));
    /// assert!(!frozen1.belongs_to(&frozen2.tree()));
    /// ```
    #[inline]
    #[must_use]
    pub fn belongs_to(&self, tree: &Tree<T>) -> bool {
        self.link().belongs_to(tree.core())
    }

    /// Returns true if the given node belong to the same tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen1 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let frozen2 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(!frozen1.belongs_to_same_tree(&frozen2));
    /// ```
    #[inline]
    #[must_use]
    pub fn belongs_to_same_tree(&self, other: &Self) -> bool {
        self.link().belongs_to_same_tree(other.link())
    }

    /// Returns the hot root node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen.root().ptr_eq(&frozen));
    /// ```
    #[inline]
    #[must_use]
    pub fn root(&self) -> Self {
        Self::from_node_link_with_prohibition(self.tree_core().root_link())
    }

    /// Returns the parent node.
    ///
    /// See [`Node::parent`] for usage examples.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.node_core()
            .parent_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the previous sibling.
    ///
    /// See [`Node::prev_sibling`] for usage examples.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.node_core()
            .prev_sibling_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the next sibling.
    ///
    /// See [`Node::next_sibling`] for usage examples.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.node_core()
            .next_sibling_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the first sibling.
    ///
    /// See [`Node::first_sibling`] for usage examples.
    #[must_use]
    pub fn first_sibling(&self) -> Self {
        if let Some(parent_link) = self.node_core().parent_link() {
            let first_child_link = parent_link
                .first_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::from_node_link_with_prohibition(first_child_link)
        } else {
            // `self` is the root node.
            self.clone()
        }
    }

    /// Returns the last sibling.
    ///
    /// See [`Node::last_sibling`] for usage examples.
    #[must_use]
    pub fn last_sibling(&self) -> Self {
        if let Some(parent_link) = self.node_core().parent_link() {
            let last_child_lin = parent_link
                .last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::from_node_link_with_prohibition(last_child_lin)
        } else {
            // `self` is the root node.
            self.clone()
        }
    }

    /// Returns the first and the last siblings.
    ///
    /// See [`Node::first_last_sibling`] for usage examples.
    #[must_use]
    pub fn first_last_sibling(&self) -> (Self, Self) {
        if let Some(parent_link) = self.node_core().parent_link() {
            let (first_child_link, last_child_link) = parent_link
                .first_last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            (
                Self::from_node_link_with_prohibition(first_child_link),
                Self::from_node_link_with_prohibition(last_child_link),
            )
        } else {
            // `self` is the root node.
            (self.clone(), self.clone())
        }
    }

    /// Returns the first child node.
    ///
    /// See [`Node::first_child`] for usage examples.
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.node_core()
            .first_child_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the last child node.
    ///
    /// See [`Node::last_child`] for usage examples.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.node_core()
            .last_child_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns links to the first and the last child nodes.
    ///
    /// See [`Node::first_last_child`] for usage examples.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.node_core().first_last_child_link()?;
        Some((
            Self::from_node_link_with_prohibition(first_link),
            Self::from_node_link_with_prohibition(last_link),
        ))
    }

    /// Returns true if the previous sibling exists.
    ///
    /// See [`Node::has_prev_sibling`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_prev_sibling(&self) -> bool {
        self.node_core().has_prev_sibling()
    }

    /// Returns true if the next sibling exists.
    ///
    /// See [`Node::has_prev_sibling`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_next_sibling(&self) -> bool {
        self.node_core().has_next_sibling()
    }

    /// Returns true if the node has any children.
    ///
    /// See [`Node::has_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_children(&self) -> bool {
        self.node_core().has_children()
    }

    /// Returns the number of children.
    ///
    /// This is `O(1)` operation.
    ///
    /// See [`Node::num_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn num_children(&self) -> usize {
        self.node_core().num_children_cell().get()
    }

    /// Returns true if the node has just one child.
    ///
    /// Use [`num_children`][`Self::num_children`] method instead, i.e. use
    /// `self.num_children() == 1`.
    ///
    /// See [`Node::has_one_child`] for usage examples.
    #[inline]
    #[must_use]
    #[deprecated(since = "0.1.1", note = "use `HotNode::num_children`")]
    pub fn has_one_child(&self) -> bool {
        self.num_children() == 1
    }

    /// Returns true if the node has two or more children.
    ///
    /// Use [`num_children`][`Self::num_children`] method instead, i.e. use
    /// `self.num_children() > 1`.
    ///
    /// See [`Node::has_multiple_children`] for usage examples.
    #[inline]
    #[must_use]
    #[deprecated(since = "0.1.1", note = "use `HotNode::num_children`")]
    pub fn has_multiple_children(&self) -> bool {
        self.num_children() > 1
    }

    /// Returns the number of children.
    ///
    /// Use [`num_children`][`Self::num_children`] method instead.
    ///
    /// See [`Node::count_children`] for usage examples.
    #[inline]
    #[must_use]
    #[deprecated(since = "0.1.1", note = "use `HotNode::num_children`")]
    pub fn count_children(&self) -> usize {
        self.node_core().count_children()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_preceding_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_preceding_siblings(&self) -> usize {
        self.node_core().count_preceding_siblings()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_following_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_following_siblings(&self) -> usize {
        self.node_core().count_following_siblings()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_ancestors`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_ancestors(&self) -> usize {
        self.node_core().count_ancestors()
    }
}

/// Tree traverser.
impl<T> FrozenNode<T> {
    /// Returns the depth-first traverser.
    ///
    /// See [`Node::depth_first_traverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self) -> traverse::DepthFirstTraverser<T> {
        self.plain().depth_first_traverse()
    }

    /// Returns the reverse depth-first traverser.
    ///
    /// See [`Node::depth_first_reverse_traverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn depth_first_reverse_traverse(&self) -> traverse::ReverseDepthFirstTraverser<T> {
        self.plain().depth_first_reverse_traverse()
    }

    /// Returns the children traverser.
    ///
    /// See [`Node::children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn children(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().children()
    }

    /// Returns the reverse children traverser.
    ///
    /// See [`Node::children_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn children_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().children_reverse()
    }

    /// Returns the ancestors traverser.
    ///
    /// See [`Node::ancestors`] for usage examples.
    #[inline]
    #[must_use]
    pub fn ancestors(&self) -> traverse::AncestorsTraverser<T> {
        self.plain().ancestors()
    }

    /// Returns the ancestors traverser.
    ///
    /// See [`Node::ancestors_or_self`] for usage examples.
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self) -> traverse::AncestorsTraverser<T> {
        self.plain().ancestors_or_self()
    }

    /// Returns the siblings traverser.
    ///
    /// See [`Node::siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn siblings(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().siblings()
    }

    /// Returns the reverse siblings traverser.
    ///
    /// See [`Node::siblings_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().siblings_reverse()
    }

    /// Returns the preceding siblings traverser.
    ///
    /// See [`Node::preceding_siblings_or_self_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().preceding_siblings_or_self_reverse()
    }

    /// Returns the preceding siblings traverser.
    ///
    /// See [`Node::preceding_siblings_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().preceding_siblings_reverse()
    }

    /// Returns the following siblings traverser.
    ///
    /// See [`Node::following_siblings_or_self`] for usage examples.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().following_siblings_or_self()
    }

    /// Returns the following siblings traverser.
    ///
    /// See [`Node::following_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn following_siblings(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().following_siblings()
    }

    /// Returns the stable double-ended depth-first traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// See [`Node::depth_first_traverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse_stable(&self) -> traverse::StableDepthFirstTraverser<T> {
        traverse::StableDepthFirstTraverser::with_toplevel(Some(self.clone()))
    }

    /// Returns the stable double-ended children traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// See [`Node::children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn children_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_parent(Some(self.clone()))
    }

    /// Returns the stable siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// See [`Node::siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children_stable(),
            None => self.following_siblings_or_self_stable(),
        }
    }

    /// Returns the stable preceding siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_first_last(Some((
            self.first_sibling(),
            self.clone(),
        )))
    }

    /// Returns the stable preceding siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        let mut iter = self.preceding_siblings_or_self_stable();
        iter.next();
        iter
    }

    /// Returns the stable following siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_first_last(Some((
            self.clone(),
            self.last_sibling(),
        )))
    }

    /// Returns the stable following siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn following_siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        let mut iter = self.following_siblings_or_self_stable();
        iter.next();
        iter
    }

    /// Returns the stable depth-first traverser that can limit the depth to iterate.
    ///
    /// If `None` is passed as `max_depth`, then the iterator traverses nodes
    /// in unlimited depth.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::traverse::DftEvent;
    ///
    /// let frozen = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             /("0-0", ["0-0-0", "0-0-1"]),
    ///             "0-1",
    ///             /("0-2", ["0-2-0"]),
    ///         ]),
    ///         /("1", [
    ///             "1-0",
    ///         ]),
    ///         "2",
    ///     ]
    /// }
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   |   |-- 0-0-0
    /// //  |   |   `-- 0-0-1
    /// //  |   |-- 0-1
    /// //  |   `-- 0-2
    /// //  |       `-- 0-2-0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- 2
    ///
    /// let max0 = frozen.shallow_depth_first_traverse_stable(Some(0))
    ///     .map(|ev| ev.map(|(node, depth)| (*node.borrow_data(), depth)))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     max0,
    ///     &[
    ///         DftEvent::Open(("root", 0)),
    ///         DftEvent::Close(("root", 0)),
    ///     ]
    /// );
    ///
    /// let max2 = frozen.shallow_depth_first_traverse_stable(Some(2))
    ///     .map(|ev| ev.map(|(node, depth)| (*node.borrow_data(), depth)))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     max2,
    ///     &[
    ///         DftEvent::Open(("root", 0)),
    ///         DftEvent::Open(("0", 1)),
    ///         DftEvent::Open(("0-0", 2)),
    ///         DftEvent::Close(("0-0", 2)),
    ///         DftEvent::Open(("0-1", 2)),
    ///         DftEvent::Close(("0-1", 2)),
    ///         DftEvent::Open(("0-2", 2)),
    ///         DftEvent::Close(("0-2", 2)),
    ///         DftEvent::Close(("0", 1)),
    ///         DftEvent::Open(("1", 1)),
    ///         DftEvent::Open(("1-0", 2)),
    ///         DftEvent::Close(("1-0", 2)),
    ///         DftEvent::Close(("1", 1)),
    ///         DftEvent::Open(("2", 1)),
    ///         DftEvent::Close(("2", 1)),
    ///         DftEvent::Close(("root", 0)),
    ///     ]
    /// );
    ///
    /// let max_unlimited = frozen.shallow_depth_first_traverse_stable(None)
    ///     .map(|ev| ev.map(|(node, _depth)| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// let all = frozen.depth_first_traverse()
    ///     .map(|ev| ev.map(|node| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(max_unlimited, all);
    /// ```
    #[inline]
    #[must_use]
    pub fn shallow_depth_first_traverse_stable(
        &self,
        max_depth: Option<usize>,
    ) -> traverse::StableShallowDepthFirstTraverser<T> {
        traverse::StableShallowDepthFirstTraverser::with_toplevel(Some(self.clone()), max_depth)
    }

    /// Returns the stable non-allocating breadth-first traverser.
    ///
    /// Note that traversing all nodes will be `O(n^2)` operation in worst case,
    /// not `O(n)`.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::traverse::DftEvent;
    ///
    /// let frozen = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             /("0-0", ["0-0-0", "0-0-1"]),
    ///             "0-1",
    ///             /("0-2", ["0-2-0"]),
    ///         ]),
    ///         /("1", [
    ///             "1-0",
    ///         ]),
    ///         "2",
    ///     ]
    /// }
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   |   |-- 0-0-0
    /// //  |   |   `-- 0-0-1
    /// //  |   |-- 0-1
    /// //  |   `-- 0-2
    /// //  |       `-- 0-2-0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- 2
    ///
    /// let depth2 = frozen
    ///     .non_allocating_breadth_first_traverse_stable(2)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     depth2,
    ///     &[
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    ///
    /// let all = frozen
    ///     .non_allocating_breadth_first_traverse_stable(0)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     all,
    ///     &[
    ///         ("root", 0),
    ///         ("0", 1), ("1", 1), ("2", 1),
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn non_allocating_breadth_first_traverse_stable(
        &self,
        start_depth: usize,
    ) -> traverse::NonAllocatingBreadthFirstTraverser<T> {
        traverse::NonAllocatingBreadthFirstTraverser::with_toplevel(self.clone(), start_depth)
    }

    /// Returns the stable allocating breadth-first traverser.
    ///
    /// The returned traverser will heap-allocate, and iterating all nodes is
    /// `O(n)` operation.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::traverse::DftEvent;
    ///
    /// let frozen = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             /("0-0", ["0-0-0", "0-0-1"]),
    ///             "0-1",
    ///             /("0-2", ["0-2-0"]),
    ///         ]),
    ///         /("1", [
    ///             "1-0",
    ///         ]),
    ///         "2",
    ///     ]
    /// }
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   |   |-- 0-0-0
    /// //  |   |   `-- 0-0-1
    /// //  |   |-- 0-1
    /// //  |   `-- 0-2
    /// //  |       `-- 0-2-0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- 2
    ///
    /// let depth2 = frozen
    ///     .allocating_breadth_first_traverse_stable(2)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     depth2,
    ///     &[
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    ///
    /// let all = frozen
    ///     .allocating_breadth_first_traverse_stable(0)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     all,
    ///     &[
    ///         ("root", 0),
    ///         ("0", 1), ("1", 1), ("2", 1),
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn allocating_breadth_first_traverse_stable(
        &self,
        start_depth: usize,
    ) -> traverse::AllocatingBreadthFirstTraverser<T> {
        traverse::AllocatingBreadthFirstTraverser::with_toplevel(self.clone(), start_depth)
    }
}

/// Node creation and modification (to the other tree).
impl<T> FrozenNode<T> {
    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    ///
    /// See [`Node::try_clone_subtree`] for usage examples.
    #[inline]
    pub fn try_clone_subtree(&self) -> Result<Node<T>, BorrowError>
    where
        T: Clone,
    {
        self.plain().try_clone_subtree()
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// See [`Node::try_clone_subtree`] for usage examples.
    ///
    /// # Panics
    ///
    /// Panics if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    #[inline]
    #[must_use]
    pub fn clone_subtree(&self) -> Node<T>
    where
        T: Clone,
    {
        self.try_clone_subtree()
            .expect("[precondition] data associated to nodes should be borrowable")
    }

    /// Clones the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the cloned new subtree.
    ///
    /// # Failures
    ///
    /// Fails with [`BorrowNodeData`][`HierarchyError::BorrowNodeData`] if any
    /// data associated to the node in the subtree is mutably (i.e. exclusively)
    /// borrowed.
    ///
    /// See [`Node::try_clone_insert_subtree`] for usage examples.
    #[inline]
    pub fn try_clone_insert_subtree(
        &self,
        dest: InsertAs<&HotNode<T>>,
    ) -> Result<HotNode<T>, HierarchyError>
    where
        T: Clone,
    {
        edit::try_clone_insert_subtree(&self.plain(), dest)
    }
}

/// Serialization.
impl<T: Clone> FrozenNode<T> {
    /// Returns an iterator of serialized events for the subtree.
    ///
    /// See [`Node::to_events`] for usage examples.
    #[inline]
    #[must_use]
    pub fn to_events(&self) -> serial::TreeSerializeIter<T> {
        serial::TreeSerializeIter::new(&self.plain())
    }
}

/// Debug printing.
impl<T> FrozenNode<T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// See [`Node::debug_pretty_print`] for usage and example output.
    #[inline]
    #[must_use]
    pub fn debug_pretty_print(&self) -> DebugPrettyPrint<'_, T> {
        DebugPrettyPrint::new(self.node_core())
    }

    /// Returns a debug-printable proxy that does not dump neighbor nodes.
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// See [`Node::debug_print_local`] for usage.
    #[inline]
    #[must_use]
    pub fn debug_print_local(&self) -> DebugPrintNodeLocal<'_, T> {
        DebugPrintNodeLocal::new_frozen(self.node_core())
    }

    /// Returns a debug-printable proxy that also dumps descendants recursively.
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// See [`Node::debug_print_subtree`] for usage.
    #[inline]
    #[must_use]
    pub fn debug_print_subtree(&self) -> DebugPrintSubtree<'_, T> {
        DebugPrintSubtree::new_frozen(self.node_core())
    }
}
