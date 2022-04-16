//! Hot node, which is a [`Node`] with tree structure edit grant bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::anchor::{AdoptAs, InsertAs};
use crate::membership::{Membership, MembershipWithEditGrant};
use crate::node::{edit, DebugPrettyPrint, IntraTreeLink, Node, NumChildren};
use crate::serial;
use crate::traverse;
use crate::tree::{StructureEditGrant, StructureEditGrantError, Tree, TreeCore};
use crate::StructureError;

/// A [`Node`] with a tree structure edit grant bundled.
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
    pub(super) fn from_node(node: Node<T>) -> Result<Self, StructureEditGrantError> {
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
    /// Panics if the structure edit grant is not valid for the given node.
    ///
    /// Panics if there are too many grants for the node or for the tree.
    #[must_use]
    pub(super) fn from_node_and_grant(node: Node<T>, grant: StructureEditGrant<T>) -> Self {
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
            .expect("[consistency] there should have already been tree structure edit grant");

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

/// Tree structure edit grants.
impl<T> HotNode<T> {
    /// Returns a copy of the tree structure edit grant.
    #[must_use]
    pub fn extract_structure_edit_grant(&self) -> StructureEditGrant<T> {
        self.tree()
            .grant_structure_edit()
            .expect("[validity] the tree structure is already granted to be edit")
    }
}

// Common methods below.

/// Data access.
impl<T> HotNode<T> {
    /// Returns a reference to the data associated to the node.
    #[inline]
    pub fn try_borrow_data(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.intra_link.try_borrow_data()
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub fn borrow_data(&self) -> Ref<'_, T> {
        self.intra_link.borrow_data()
    }

    /// Returns a mutable reference to the data associated to the node.
    #[inline]
    pub fn try_borrow_data_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.intra_link.try_borrow_data_mut()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.intra_link.borrow_data_mut()
    }

    /// Returns `true` if the two `HotNode`s point to the same allocation.
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }

    /// Returns `true` if `self` and the given `Node` point to the same allocation.
    #[inline]
    #[must_use]
    pub fn ptr_eq_plain(&self, other: &Node<T>) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }
}

/// Neighbor nodes accessor.
impl<T> HotNode<T> {
    /// Returns the tree the node belongs to.
    #[inline]
    #[must_use]
    pub fn tree(&self) -> Tree<T> {
        Tree::from_core_rc(self.tree_core())
    }

    /// Returns true if the node is the root.
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
    }

    /// Returns true if the given node belong to the same tree.
    #[inline]
    #[must_use]
    pub fn belongs_to_same_tree(&self, other: &Self) -> bool {
        self.membership.belongs_to_same_tree(&other.membership)
    }

    /// Returns the hot root node.
    #[must_use]
    pub fn root(&self) -> Self {
        Self::from_node_link_with_grant(self.tree_core().root_link())
    }

    /// Returns the parent node.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link
            .parent_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the previous sibling.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link
            .prev_sibling_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the next sibling.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link
            .next_sibling_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the first sibling.
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

    /// Returns the first and the last sibling.
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
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.intra_link
            .first_child_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns the last child node.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link
            .last_child_link()
            .map(Self::from_node_link_with_grant)
    }

    /// Returns links to the first and the last child nodes.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
        Some((
            Self::from_node_link_with_grant(first_link),
            Self::from_node_link_with_grant(last_link),
        ))
    }

    /// Returns true if the previous sibling exists.
    #[inline]
    #[must_use]
    pub fn has_prev_sibling(&self) -> bool {
        self.intra_link.has_prev_sibling()
    }

    /// Returns true if the next sibling exists.
    #[inline]
    #[must_use]
    pub fn has_next_sibling(&self) -> bool {
        self.intra_link.has_next_sibling()
    }

    /// Returns true if the node has any children.
    #[inline]
    #[must_use]
    pub fn has_children(&self) -> bool {
        self.intra_link.has_children()
    }

    /// Returns true if the node has just one child.
    #[inline]
    #[must_use]
    pub fn has_one_child(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::One
    }

    /// Returns true if the node has two or more children.
    #[inline]
    #[must_use]
    pub fn has_multiple_children(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::TwoOrMore
    }

    /// Returns the number of children.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_children(&self) -> usize {
        self.intra_link.count_children()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_preceding_siblings(&self) -> usize {
        self.intra_link.count_preceding_siblings()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_following_siblings(&self) -> usize {
        self.intra_link.count_following_siblings()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_ancestors(&self) -> usize {
        self.intra_link.count_ancestors()
    }
}

/// Tree traverser.
impl<T> HotNode<T> {
    /// Returns the depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self) -> traverse::DepthFirstTraverser<T> {
        self.plain().depth_first_traverse()
    }

    /// Returns the reverse depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_reverse_traverse(&self) -> traverse::ReverseDepthFirstTraverser<T> {
        self.plain().depth_first_reverse_traverse()
    }

    /// Returns the children traverser.
    #[inline]
    #[must_use]
    pub fn children(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().children()
    }

    /// Returns the reverse children traverser.
    #[inline]
    #[must_use]
    pub fn children_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().children_reverse()
    }

    /// Returns the ancestors traverser.
    #[inline]
    #[must_use]
    pub fn ancestors(&self) -> traverse::AncestorsTraverser<T> {
        self.plain().ancestors()
    }

    /// Returns the ancestors traverser.
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self) -> traverse::AncestorsTraverser<T> {
        self.plain().ancestors_or_self()
    }

    /// Returns the siblings traverser.
    #[inline]
    #[must_use]
    pub fn siblings(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().siblings()
    }

    /// Returns the reverse siblings traverser.
    #[inline]
    #[must_use]
    pub fn siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().siblings_reverse()
    }

    /// Returns the preceding siblings traverser.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().preceding_siblings_or_self_reverse()
    }

    /// Returns the preceding siblings traverser.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().preceding_siblings_reverse()
    }

    /// Returns the following siblings traverser.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().following_siblings_or_self()
    }

    /// Returns the following siblings traverser.
    #[inline]
    #[must_use]
    pub fn following_siblings(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().following_siblings()
    }
}

/// Node creation and structure modification.
impl<T> HotNode<T> {
    /// Creates and returns a new hot node as the root of a new tree.
    #[must_use]
    pub fn new_tree(root_data: T) -> Self {
        Self::from_node(Node::new_tree(root_data)).expect("[validity] a new node can be locked")
    }

    /// Detaches the node and its descendant from the current tree, and let it be another tree.
    #[inline]
    pub fn detach_subtree(&self) {
        edit::detach_subtree(&self.intra_link);
    }

    /// Creates a node as the next sibling of `self`, and returns the new node.
    #[inline]
    pub fn try_create_node_as(&self, data: T, dest: AdoptAs) -> Result<Self, StructureError> {
        edit::try_create_node_as(&self.intra_link, self.tree_core(), data, dest)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
    }

    /// Creates a node as the first child of `self`.
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
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_prev_sibling(&self, data: T) -> Result<Self, StructureError> {
        edit::try_create_as_prev_sibling(&self.intra_link, self.tree_core(), data)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_next_sibling(&self, data: T) -> Result<Self, StructureError> {
        edit::try_create_as_next_sibling(&self.intra_link, self.tree_core(), data)
            .map(|node| Self::from_node(node).expect("[validity] a new node can be locked"))
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
    /// After `self.replace_with_children()`:
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
    /// # Failures
    ///
    /// Fails if:
    ///
    /// * the node is the root and has multiple children, or
    ///     + In this case, [`StructureError::SiblingsWithoutParent`] error is returned.
    /// * the node is the root and has no children.
    ///     + In this case, [`StructureError::EmptyTree`] error is returned.
    #[inline]
    pub fn replace_with_children(&self) -> Result<(), StructureError> {
        edit::replace_with_children(&self.intra_link)
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    #[inline]
    pub fn clone_subtree(&self) -> Result<Node<T>, BorrowError>
    where
        T: Clone,
    {
        self.plain().clone_subtree()
    }

    /// Clones the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the cloned new subtree.
    ///
    /// # Failures
    ///
    /// Fails with [`BorrowNodeData`][`StructureError::BorrowNodeData`] if any
    /// data associated to the node in the subtree is mutably (i.e. exclusively)
    /// borrowed.
    #[inline]
    pub fn clone_insert_subtree(&self, dest: InsertAs<HotNode<T>>) -> Result<Self, StructureError>
    where
        T: Clone,
    {
        edit::clone_insert_subtree(&self.plain(), dest)
    }

    /// Detaches the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the transplanted subtree.
    #[inline]
    pub fn detach_insert_subtree(&self, dest: InsertAs<HotNode<T>>) -> Result<(), StructureError> {
        if self
            .plain_membership()
            .belongs_to_same_tree(dest.anchor().plain_membership())
        {
            // The source and the destination belong to the same tree.
            edit::detach_and_move_inside_same_tree(
                &self.intra_link,
                dest.as_ref().map(HotNode::intra_link),
            )
        } else {
            // The source and the destination belong to the different tree.
            edit::detach_and_move_to_another_tree(
                &self.intra_link,
                dest.as_ref().map(HotNode::intra_link),
                &dest.anchor().tree_core(),
            )
        }
    }
}

/// Serialization.
impl<T: Clone> HotNode<T> {
    /// Returns an iterator of serialized events for the subtree.
    #[inline]
    #[must_use]
    pub fn to_events(&self) -> serial::TreeSerializeIter<T> {
        serial::TreeSerializeIter::new(&self.plain())
    }
}

/// Debug printing.
impl<T> HotNode<T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    #[inline]
    #[must_use]
    pub fn debug_pretty_print(&self) -> DebugPrettyPrint<'_, T> {
        DebugPrettyPrint::new(&self.intra_link)
    }
}
