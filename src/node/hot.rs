//! Hot node, which is a [`Node`] with tree hierarchy edit grant bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::anchor::{AdoptAs, InsertAs};
use crate::membership::{Membership, MembershipWithEditGrant};
use crate::node::{edit, DebugPrettyPrint, HierarchyError, IntraTreeLink, Node, NumChildren};
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
    /// Target node core.
    pub(super) intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: MembershipWithEditGrant<T>,
}

impl<T> Clone for HotNode<T> {
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            membership: self.membership.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for HotNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HotNode")
            .field("data", &self.intra_link.try_borrow_data())
            .field("next_sibling", &self.intra_link.next_sibling_link())
            .field("first_child", &self.intra_link.first_child_link())
            .field("membership", &self.membership)
            .finish()
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
        self.intra_link.try_eq(&other.intra_link).expect(
            "[precondition] data associated to the nodes in both trees should be borrowable",
        )
    }
}

impl<T: Eq> Eq for HotNode<T> {}

impl<T> HotNode<T> {
    /// Creates a new `HotNode` from the given plain node.
    pub(super) fn from_node(node: Node<T>) -> Result<Self, HierarchyEditGrantError> {
        let Node {
            intra_link,
            membership,
        } = node;
        let membership = MembershipWithEditGrant::new(membership)?;
        Ok(Self {
            intra_link,
            membership,
        })
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

        let Node {
            intra_link,
            membership,
        } = node;
        let membership = MembershipWithEditGrant::new(membership)
            .expect("[validity] a valid grant already exists for the tree");
        Self {
            intra_link,
            membership,
        }
    }

    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the membership field of the node link is not set up.
    ///
    /// Panics if a reference to the tree core is not valid.
    ///
    /// Panics if the tree is granted to be edited.
    #[must_use]
    pub(crate) fn from_node_link_with_grant(intra_link: IntraTreeLink<T>) -> Self {
        let membership = intra_link.membership().upgrade().expect(
            "[consistency] the membership must be alive since the corresponding node link is alive",
        );
        let membership = MembershipWithEditGrant::new(membership)
            .expect("[consistency] there should have already been tree hierarchy edit grant");

        Self {
            intra_link,
            membership,
        }
    }

    /// Returns the intra-tree link.
    #[inline]
    #[must_use]
    pub(super) fn intra_link(&self) -> &IntraTreeLink<T> {
        &self.intra_link
    }

    /// Returns a reference to the plain membership.
    #[inline]
    #[must_use]
    pub(super) fn plain_membership(&self) -> &Membership<T> {
        self.membership.as_inner()
    }

    /// Returns the tree core.
    #[inline]
    #[must_use]
    pub(super) fn tree_core(&self) -> Rc<TreeCore<T>> {
        self.plain_membership().tree_core()
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
    #[must_use]
    pub fn plain(&self) -> Node<T> {
        Node::with_link_and_membership(self.intra_link.clone(), self.membership.as_inner().clone())
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
        self.intra_link.try_borrow_data()
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
        self.intra_link.borrow_data()
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
        self.intra_link.try_borrow_data_mut()
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
        self.intra_link.borrow_data_mut()
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
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
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
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
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
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
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
        self.membership.belongs_to_same_tree(&other.membership)
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
    #[must_use]
    pub fn root(&self) -> Self {
        Self::from_node_link_with_grant(self.tree_core().root_link())
    }

    /// Returns the parent node.
    ///
    /// See [`Node::parent`] for usage examples.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link
            .parent_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the previous sibling.
    ///
    /// See [`Node::prev_sibling`] for usage examples.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link
            .prev_sibling_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the next sibling.
    ///
    /// See [`Node::next_sibling`] for usage examples.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link
            .next_sibling_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the first sibling.
    ///
    /// See [`Node::first_sibling`] for usage examples.
    #[must_use]
    pub fn first_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
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
        if let Some(parent_link) = self.intra_link.parent_link() {
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
        if let Some(parent_link) = self.intra_link.parent_link() {
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
        self.intra_link
            .first_child_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the last child node.
    ///
    /// See [`Node::last_child`] for usage examples.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link
            .last_child_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns links to the first and the last child nodes.
    ///
    /// See [`Node::first_last_child`] for usage examples.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
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
        self.intra_link.has_prev_sibling()
    }

    /// Returns true if the next sibling exists.
    ///
    /// See [`Node::has_next_sibling`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_next_sibling(&self) -> bool {
        self.intra_link.has_next_sibling()
    }

    /// Returns true if the node has any children.
    ///
    /// See [`Node::has_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_children(&self) -> bool {
        self.intra_link.has_children()
    }

    /// Returns true if the node has just one child.
    ///
    /// See [`Node::has_one_child`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_one_child(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::One
    }

    /// Returns true if the node has two or more children.
    ///
    /// See [`Node::has_multiple_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_multiple_children(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::TwoOrMore
    }

    /// Returns the number of children.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_children(&self) -> usize {
        self.intra_link.count_children()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_preceding_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_preceding_siblings(&self) -> usize {
        self.intra_link.count_preceding_siblings()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_following_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_following_siblings(&self) -> usize {
        self.intra_link.count_following_siblings()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_ancestors`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_ancestors(&self) -> usize {
        self.intra_link.count_ancestors()
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
        edit::detach_subtree(&self.intra_link);
    }

    /// Creates a node as the next sibling of `self`, and returns the new node.
    ///
    /// See [`Node::try_create_node_as`] for usage examples.
    #[inline]
    pub fn try_create_node_as(&self, data: T, dest: AdoptAs) -> Result<Self, HierarchyError> {
        edit::try_create_node_as(&self.intra_link, self.tree_core(), data, dest)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
    }

    /// Creates a node as the next sibling of `self`, and returns the new node.
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
            &self.intra_link,
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
            &self.intra_link,
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
        edit::try_create_as_prev_sibling(&self.intra_link, self.tree_core(), data)
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
        edit::try_create_as_next_sibling(&self.intra_link, self.tree_core(), data)
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
        edit::try_replace_with_children(&self.intra_link)
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
        if self
            .plain_membership()
            .belongs_to_same_tree(dest.anchor().plain_membership())
        {
            // The source and the destination belong to the same tree.
            edit::detach_and_move_inside_same_tree(&self.intra_link, dest.map(HotNode::intra_link))
        } else {
            // The source and the destination belong to the different tree.
            edit::detach_and_move_to_another_tree(
                &self.intra_link,
                dest.map(HotNode::intra_link),
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
        DebugPrettyPrint::new(&self.intra_link)
    }
}
