//! Hot node, which is a [`Node`] with tree hierarchy edit grant bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::anchor::{AdoptAs, InsertAs};
use crate::node::debug_print::{DebugPrettyPrint, DebugPrintNodeLocal, DebugPrintSubtree};
use crate::node::{edit, HierarchyError, Node, NodeCoreLink, NodeLink};
use crate::serial;
use crate::traverse;
use crate::tree::{HierarchyEditGrant, HierarchyEditGrantError, Tree, TreeCore};

/// A [`Node`] with a tree hierarchy edit grant bundled.
///
/// `HotNode` can be created by [`Node::bundle_hierarchy_edit_grant`] or
/// [`Node::bundle_new_hierarchy_edit_grant`].
///
/// # Panics
///
/// Panics if the number of active edit grants through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking grants.
pub struct HotNode<T> {
    /// Node.
    inner: Node<T>,
}

impl<T> Drop for HotNode<T> {
    #[inline]
    fn drop(&mut self) {
        self.link().decrement_edit_lock_count();
    }
}

impl<T> Clone for HotNode<T> {
    #[inline]
    fn clone(&self) -> Self {
        self.link().increment_nonzero_edit_lock_count();
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for HotNode<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.debug_print_local().fmt(f)
    }
}

impl<T, U: PartialEq<U>> PartialEq<HotNode<U>> for HotNode<T>
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
    fn eq(&self, other: &HotNode<U>) -> bool {
        self.inner.try_eq(&other.inner).expect(
            "[precondition] data associated to the nodes in both trees should be borrowable",
        )
    }
}

impl<T: Eq> Eq for HotNode<T> {}

impl<T> HotNode<T> {
    /// Creates a new `HotNode` from the given plain node.
    #[inline]
    pub(super) fn from_node(node: Node<T>) -> Result<Self, HierarchyEditGrantError> {
        node.link().acquire_edit_grant()?;
        Ok(Self { inner: node })
    }

    /// Creates a new `HotNode` from the given plain node and the grant.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// Panics if there are too many grants for the node or for the tree.
    #[must_use]
    pub(super) fn from_node_and_grant(node: Node<T>, grant: &HierarchyEditGrant<T>) -> Self {
        grant.panic_if_invalid_for_node(&node);

        node.link()
            .acquire_edit_grant()
            .expect("[validity] a valid grant already exists for the tree");
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
    fn from_node_link_with_grant(link: NodeCoreLink<T>) -> Self {
        let inner = Node::with_node_core(link);
        inner
            .link()
            .acquire_edit_grant()
            .expect("[consistency] there should have already been tree hierarchy edit grant");

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
    /// use dendron::{HotNode, Node};
    ///
    /// let hot = HotNode::new_tree("root");
    /// let plain: Node<_> = hot.plain();
    /// ```
    #[inline]
    #[must_use]
    pub fn plain(&self) -> Node<T> {
        self.inner.clone()
    }
}

impl<T> From<HotNode<T>> for Node<T> {
    #[inline]
    fn from(node: HotNode<T>) -> Self {
        node.plain()
    }
}

/// Tree hierarchy edit grants.
impl<T> HotNode<T> {
    /// Returns a copy of the tree hierarchy edit grant.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    /// let grant = hot.extract_hierarchy_edit_grant();
    /// ```
    #[must_use]
    pub fn extract_hierarchy_edit_grant(&self) -> HierarchyEditGrant<T> {
        self.tree()
            .grant_hierarchy_edit()
            .expect("[validity] the tree hierarchy is already granted to be edit")
    }
}

// Common methods below.

/// Data access.
impl<T> HotNode<T> {
    /// Returns a reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    /// assert_eq!(
    ///     *hot
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
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    /// assert_eq!(*hot.borrow_data(), "root");
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
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    ///
    /// *hot.try_borrow_data_mut()
    ///     .expect("should not fail since not borrowed from other place")
    ///     = "ROOT";
    /// assert_eq!(*hot.borrow_data(), "ROOT");
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
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    ///
    /// *hot.borrow_data_mut() = "ROOT";
    /// assert_eq!(*hot.borrow_data(), "ROOT");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.node_core().borrow_data_mut()
    }

    /// Returns `true` if the two `HotNode`s point to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let hot1 = HotNode::new_tree("root");
    /// let hot2 = HotNode::new_tree("root");
    ///
    /// assert!(hot1.ptr_eq(&hot1));
    ///
    /// assert!(hot1 == hot2, "same content and hierarchy");
    /// assert!(
    ///     !hot1.ptr_eq(&hot2),
    ///     "same content and hierarchy but different allocation"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        NodeCoreLink::ptr_eq(self.node_core(), other.node_core())
    }

    /// Returns `true` if `self` and the given `Node` point to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    /// assert!(hot.ptr_eq_plain(&hot.plain()));
    /// ```
    #[inline]
    #[must_use]
    pub fn ptr_eq_plain(&self, other: &Node<T>) -> bool {
        NodeCoreLink::ptr_eq(self.node_core(), other.node_core())
    }
}

/// Neighbor nodes accessor.
impl<T> HotNode<T> {
    /// Returns the tree the node belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let hot = HotNode::new_tree("root");
    /// let tree = hot.tree();
    ///
    /// assert!(tree.root().ptr_eq(&hot.plain()));
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
    /// use dendron::HotNode;
    ///
    /// let root = HotNode::new_tree("root");
    /// let child = root.create_as_last_child("child");
    /// //  root
    /// //  `-- child
    ///
    /// assert!(root.is_root());
    /// assert!(!child.is_root());
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
    /// use dendron::HotNode;
    ///
    /// let root = HotNode::new_tree("root");
    /// let child = root.create_as_last_child("child");
    /// //  root
    /// //  `-- child
    ///
    /// let other_node = HotNode::new_tree("other");
    ///
    /// assert!(root.belongs_to(&root.tree()));
    /// assert!(child.belongs_to(&root.tree()));
    ///
    /// assert!(!root.belongs_to(&other_node.tree()));
    /// ```
    #[inline]
    #[must_use]
    pub fn belongs_to(&self, tree: &Tree<T>) -> bool {
        self.link().belongs_to(tree.core())
    }

    /// Returns true if the node belongs to the given tree.
    #[inline]
    #[must_use]
    pub(super) fn belongs_to_tree_core(&self, tree_core: &Rc<TreeCore<T>>) -> bool {
        self.link().belongs_to(tree_core)
    }

    /// Returns true if the given node belong to the same tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let root = HotNode::new_tree("root");
    /// let child = root.create_as_last_child("child");
    /// //  root
    /// //  `-- child
    ///
    /// let other_node = HotNode::new_tree("other");
    ///
    /// assert!(root.belongs_to_same_tree(&child));
    /// assert!(child.belongs_to_same_tree(&root));
    ///
    /// assert!(!root.belongs_to_same_tree(&other_node));
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
    /// use dendron::HotNode;
    ///
    /// let node = HotNode::new_tree("root");
    /// let tree = node.tree();
    ///
    /// assert!(tree.root().ptr_eq(&node.plain()));
    /// ```
    #[inline]
    #[must_use]
    pub fn root(&self) -> Self {
        Self::from_node_link_with_grant(self.tree_core().root_link())
    }

    /// Returns the parent node.
    ///
    /// See [`Node::parent`] for usage examples.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.node_core()
            .parent_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the previous sibling.
    ///
    /// See [`Node::prev_sibling`] for usage examples.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.node_core()
            .prev_sibling_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the next sibling.
    ///
    /// See [`Node::next_sibling`] for usage examples.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.node_core()
            .next_sibling_link()
            .map(Self::from_node_link_with_grant)
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
            Self::from_node_link_with_grant(first_child_link)
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
            Self::from_node_link_with_grant(last_child_lin)
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
                Self::from_node_link_with_grant(first_child_link),
                Self::from_node_link_with_grant(last_child_link),
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
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the last child node.
    ///
    /// See [`Node::last_child`] for usage examples.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.node_core()
            .last_child_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns links to the first and the last child nodes.
    ///
    /// See [`Node::first_last_child`] for usage examples.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.node_core().first_last_child_link()?;
        Some((
            Self::from_node_link_with_grant(first_link),
            Self::from_node_link_with_grant(last_link),
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
    /// See [`Node::has_next_sibling`] for usage examples.
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
impl<T> HotNode<T> {
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
}

/// Node creation and hierarchy modification.
impl<T> HotNode<T> {
    /// Creates and returns a new hot node as the root of a new tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::HotNode;
    ///
    /// let root = HotNode::new_tree("root");
    /// ```
    #[must_use]
    pub fn new_tree(root_data: T) -> Self {
        Self::from_node(Node::new_tree(root_data)).expect("[validity] a new node can be locked")
    }

    /// Detaches the node and its descendant from the current tree, and let it be another tree.
    ///
    /// See [`Node::detach_subtree`] for usage examples.
    #[inline]
    pub fn detach_subtree(&self) {
        edit::detach_subtree(self.node_core());
    }

    /// Creates a node as the specified neighbor of `self`, and returns the new node.
    ///
    /// See [`Node::try_create_node_as`] for usage examples.
    #[inline]
    pub fn try_create_node_as(&self, data: T, dest: AdoptAs) -> Result<Self, HierarchyError> {
        edit::try_create_node_as(self.node_core(), self.tree_core(), data, dest)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
    }

    /// Creates a node as the specified neighbor of `self`, and returns the new node.
    ///
    /// See [`Node::create_node_as`] for usage examples.
    ///
    /// # Panics
    ///
    /// Panics if the creation of a node at the specified position will make the
    /// tree hierarchy invalid.
    #[inline]
    pub fn create_node_as(&self, data: T, dest: AdoptAs) -> Self {
        self.try_create_node_as(data, dest)
            .expect("[precondition] hierarchy to be created should be valid")
    }

    /// Creates a node as the first child of `self`.
    ///
    /// See [`Node::create_as_first_child`] for usage examples.
    #[inline]
    pub fn create_as_first_child(&self, data: T) -> Self {
        Self::from_node(edit::create_as_first_child(
            self.node_core(),
            self.tree_core(),
            data,
        ))
        .expect("[validity] a new node can be locked")
    }

    /// Creates a node as the last child of `self`.
    ///
    /// See [`Node::create_as_last_child`] for usage examples.
    #[inline]
    pub fn create_as_last_child(&self, data: T) -> Self {
        Self::from_node(edit::create_as_last_child(
            self.node_core(),
            self.tree_core(),
            data,
        ))
        .expect("[validity] a new node can be locked")
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// See [`Node::try_create_as_prev_sibling`] for usage examples.
    ///
    /// # Failures
    ///
    /// Returns [`HierarchyError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_prev_sibling(&self, data: T) -> Result<Self, HierarchyError> {
        edit::try_create_as_prev_sibling(self.node_core(), self.tree_core(), data)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// See [`Node::try_create_as_prev_sibling`] for usage examples.
    ///
    /// # Panics
    ///
    /// Panics if `self` is a root node.
    #[inline]
    pub fn create_as_prev_sibling(&self, data: T) -> Self {
        self.try_create_as_prev_sibling(data)
            .expect("[precondition] hierarchy to be created should be valid")
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// See [`Node::try_create_as_next_sibling`] for usage examples.
    ///
    /// # Failures
    ///
    /// Returns [`HierarchyError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_next_sibling(&self, data: T) -> Result<Self, HierarchyError> {
        edit::try_create_as_next_sibling(self.node_core(), self.tree_core(), data)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// See [`Node::try_create_as_next_sibling`] for usage examples.
    ///
    /// # Failures
    ///
    /// Returns [`HierarchyError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn create_as_next_sibling(&self, data: T) -> Self {
        self.try_create_as_next_sibling(data)
            .expect("[precondition] hierarchy to be created should be valid")
    }

    /// Creates a new node that interrupts between `self` and the parent.
    ///
    /// If `self` was the root, the new node will become a new root of the tree
    /// and `self` will be only child of the new root.
    ///
    /// Before:
    ///
    /// ```text
    /// root
    /// `-- this
    ///     |-- child0
    ///     |-- child1
    ///     `-- child2
    /// ```
    ///
    /// After `self.create_as_interrupting_parent`:
    ///
    /// ```text
    /// root
    /// `-- new
    ///     `-- this
    ///         |-- child0
    ///         |-- child1
    ///         `-- child2
    /// ```
    ///
    /// See [`create_as_interrupting_parent`][`Self::create_as_interrupting_parent`]
    /// method.
    #[inline]
    pub fn create_as_interrupting_parent(&self, data: T) -> Self {
        let new = edit::create_as_interrupting_parent(self.node_core(), data);
        Self::from_node(new).expect("[validity] a new node can be locked")
    }

    /// Creates a new node that interrupts between `self` and the children.
    ///
    /// The children of `self` will be moved under the new node, and the new
    /// node will be the only child of `self`.
    ///
    /// Before:
    ///
    /// ```text
    /// root
    /// `-- this
    ///     |-- child0
    ///     |-- child1
    ///     `-- child2
    /// ```
    ///
    /// After `self.create_as_interrupting_parent`:
    ///
    /// ```text
    /// root
    /// `-- this
    ///     `-- new
    ///         |-- child0
    ///         |-- child1
    ///         `-- child2
    /// ```
    ///
    /// See [`create_as_interrupting_child`][`Self::create_as_interrupting_child`]
    /// method.
    #[inline]
    pub fn create_as_interrupting_child(&self, data: T) -> Self {
        let new = edit::create_as_interrupting_child(self.node_core(), data);
        Self::from_node(new).expect("[validity] a new node can be locked")
    }

    /// Inserts the children at the position of the node, and detach the node.
    ///
    /// `self` will become the root of a new single-node tree.
    ///
    /// Before:
    ///
    /// ```text
    /// parent
    /// |-- prev
    /// |-- self
    /// |   |-- child0
    /// |   |   `-- grandchild0-0
    /// |   `-- child1
    /// `-- next
    /// ```
    ///
    /// After `self.try_replace_with_children()`:
    ///
    /// ```text
    /// parent
    /// |-- prev
    /// |-- child0
    /// |   `-- grandchild0-0
    /// |-- child1
    /// `-- next
    ///
    /// self (detached)
    /// ```
    ///
    /// See [`Node::try_replace_with_children`] for usage examples.
    ///
    /// # Failures
    ///
    /// Fails if:
    ///
    /// * the node is the root and has multiple children, or
    ///     + In this case, [`HierarchyError::SiblingsWithoutParent`] error is returned.
    /// * the node is the root and has no children.
    ///     + In this case, [`HierarchyError::EmptyTree`] error is returned.
    #[inline]
    pub fn try_replace_with_children(&self) -> Result<(), HierarchyError> {
        edit::try_replace_with_children(self.node_core())
    }

    /// Inserts the children at the position of the node, and detach the node.
    ///
    /// `self` will become the root of a new single-node tree.
    ///
    /// See [`try_replace_with_children`][`Self::try_replace_with_children`]
    /// method.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the node is the root and has multiple children, or
    /// * the node is the root and has no children.
    #[inline]
    pub fn replace_with_children(&self) {
        self.try_replace_with_children()
            .expect("[precondition] the hierarchy to be created should be valid")
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// See [`Node::try_clone_subtree`] for usage examples.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
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
    /// See [`Node::try_clone_insert_subtree`] for usage examples.
    ///
    /// # Failures
    ///
    /// Fails if:
    ///
    /// * the hierarchy to be created is invalid, or
    /// * any data associated to the node in the subtree is mutably (i.e.
    ///   exclusively) borrowed.
    ///     + Returns [`BorrowNodeData`][`HierarchyError::BorrowNodeData`] in
    ///       this case.
    #[inline]
    pub fn try_clone_insert_subtree(
        &self,
        dest: InsertAs<&HotNode<T>>,
    ) -> Result<Self, HierarchyError>
    where
        T: Clone,
    {
        edit::try_clone_insert_subtree(&self.plain(), dest)
    }

    /// Clones the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the cloned new subtree.
    ///
    /// See [`try_clone_insert_subtree`][`Self::try_clone_insert_subtree`]
    /// for detail.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the hierarchy to be created is invalid, or
    /// * any data associated to the node in the subtree is mutably (i.e.
    ///   exclusively) borrowed.
    #[inline]
    // This modifies hierarchy of the destination of the tree, so the returned
    // value is not necessarily used.
    #[allow(clippy::must_use_candidate)]
    pub fn clone_insert_subtree(&self, dest: InsertAs<&HotNode<T>>) -> Self
    where
        T: Clone,
    {
        self.try_clone_insert_subtree(dest).expect(
            "[precondition] the hierarchy to be created should be valid \
             and the node data should be borrowable",
        )
    }

    /// Detaches the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the transplanted subtree.
    ///
    /// See [`Node::try_detach_insert_subtree`] for usage examples.
    #[inline]
    pub fn try_detach_insert_subtree(
        &self,
        dest: InsertAs<&HotNode<T>>,
    ) -> Result<(), HierarchyError> {
        if self.link().belongs_to_same_tree(dest.anchor().link()) {
            // The source and the destination belong to the same tree.
            edit::detach_and_move_inside_same_tree(self.node_core(), dest.map(HotNode::node_core))
        } else {
            // The source and the destination belong to the different tree.
            edit::detach_and_move_to_another_tree(
                self.node_core(),
                dest.map(HotNode::node_core),
                &dest.anchor().tree_core(),
            )
        }
    }

    /// Detaches the node with its subtree, and inserts it to the given destination.
    ///
    /// See [`Node::try_detach_insert_subtree`] for detail.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the hierarchy edit grant is not valid for the given node, or
    /// * the node (being moved) is an ancestor of the destination.
    #[inline]
    pub fn detach_insert_subtree(&self, dest: InsertAs<&HotNode<T>>) {
        self.try_detach_insert_subtree(dest).expect(
            "[precondition] the node being moved should not be an ancestor of the destination",
        )
    }
}

/// Serialization.
impl<T: Clone> HotNode<T> {
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
impl<T> HotNode<T> {
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
        DebugPrintNodeLocal::new_hot(self.node_core())
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
        DebugPrintSubtree::new_hot(self.node_core())
    }
}
