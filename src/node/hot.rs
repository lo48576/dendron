//! Hot node, which is a [`Node`] with tree structure edit grant bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::membership::{Membership, MembershipWithEditGrant};
use crate::node::{edit, IntraTreeLink, Node};
//use crate::traverse;
use crate::traverse;
use crate::tree::{StructureEditGrant, StructureEditGrantError, Tree, TreeCore};
use crate::{AdoptAs, StructureError};

/// A [`Node`] with a tree structure edit grant bundled.
///
/// # Panics
///
/// Panics if the number of active edit grants through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking grants.
pub struct HotNode<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
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

    /// Returns a reference to the plain membership.
    #[inline]
    #[must_use]
    fn plain_membership(&self) -> &Membership<T> {
        self.membership.as_inner()
    }

    /// Returns the tree core.
    #[inline]
    #[must_use]
    fn tree_core(&self) -> Rc<TreeCore<T>> {
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
}
