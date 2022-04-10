//! Node.

mod edit;
mod frozen;
mod hot;
mod internal;

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::{Rc, Weak};

use crate::membership::{Membership, WeakMembership};
use crate::traverse;
use crate::tree::{
    StructureEditGrant, StructureEditGrantError, StructureEditProhibition,
    StructureEditProhibitionError, Tree, TreeCore,
};
use crate::{AdoptAs, StructureError};

pub use self::frozen::FrozenNode;
pub use self::hot::HotNode;
pub(crate) use self::internal::IntraTreeLink;
use self::internal::{IntraTreeLinkWeak, NodeBuilder};

/// A shared owning reference to a node.
pub struct Node<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: Membership<T>,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            membership: self.membership.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("data", &self.intra_link.try_borrow_data())
            .field("next_sibling", &self.intra_link.next_sibling_link())
            .field("first_child", &self.intra_link.first_child_link())
            .field("membership", &self.membership)
            .finish()
    }
}

/// Node object creation.
impl<T> Node<T> {
    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the membership field of the node link is not set up.
    ///
    /// Panics if a reference to the tree core is not valid.
    #[must_use]
    pub(crate) fn with_link(intra_link: IntraTreeLink<T>) -> Self {
        let membership = intra_link.membership().upgrade().expect(
            "[consistency] the membership must be alive since the corresponding node link is alive",
        );

        Self {
            intra_link,
            membership,
        }
    }

    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the membership is set up for a node other than the given node.
    #[must_use]
    pub(crate) fn with_link_and_membership(
        intra_link: IntraTreeLink<T>,
        membership: Membership<T>,
    ) -> Self {
        if !Membership::ptr_eq_weak(&membership, intra_link.membership()) {
            panic!("[precondition] membership should be set up for the node of interest");
        }

        Self {
            intra_link,
            membership,
        }
    }
}

/// Tree structure edit grants and prohibitions.
impl<T> Node<T> {
    /// Returns the [`FrozenNode`], a node with tree structure edit prohibition bundled.
    #[inline]
    pub fn bundle_new_structure_edit_prohibition(
        self,
    ) -> Result<FrozenNode<T>, StructureEditProhibitionError> {
        FrozenNode::from_node(self)
    }

    /// Returns the [`HotNode`], a node with tree structure edit grant bundled.
    #[inline]
    pub fn bundle_new_structure_edit_grant(self) -> Result<HotNode<T>, StructureEditGrantError> {
        HotNode::from_node(self)
    }

    /// Returns the [`FrozenNode`], a node with tree structure edit prohibition bundled.
    ///
    /// # Panics
    ///
    /// Panics if the structure prohibition grant is not valid for the given node.
    #[inline]
    #[must_use]
    pub fn bundle_structure_edit_prohibition(
        self,
        prohibition: StructureEditProhibition<T>,
    ) -> FrozenNode<T> {
        FrozenNode::from_node_and_prohibition(self, prohibition)
    }

    /// Returns the [`HotNode`], a node with tree structure edit grant bundled.
    ///
    /// # Panics
    ///
    /// Panics if the structure edit grant is not valid for the given node.
    #[inline]
    #[must_use]
    pub fn bundle_structure_edit_grant(self, grant: StructureEditGrant<T>) -> HotNode<T> {
        HotNode::from_node_and_grant(self, grant)
    }
}

// Common methods below.

/// Data access.
impl<T> Node<T> {
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

    /// Returns `true` if the two `Node`s point to the same allocation.
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }

    /// Returns a reference to the tree core for the node.
    #[inline]
    #[must_use]
    pub(crate) fn ptr_eq_tree_core_weak(&self, other: &Weak<TreeCore<T>>) -> bool {
        Rc::as_ptr(&*self.membership.tree_core_ref()) == other.as_ptr()
    }
}

/// Neighbor nodes accessor.
impl<T> Node<T> {
    /// Returns the tree the node belongs to.
    #[inline]
    #[must_use]
    pub fn tree(&self) -> Tree<T> {
        Tree::from_core_rc(self.membership.tree_core())
    }

    /// Returns true if the node is the root.
    #[inline]
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
    }

    /// Returns the root node.
    #[inline]
    #[must_use]
    pub fn root(&self) -> Self {
        Self::with_link(self.membership.tree_core().root_link())
    }

    /// Returns the parent node.
    #[inline]
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link.parent_link().map(Self::with_link)
    }

    /// Returns the previous sibling.
    #[inline]
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link.prev_sibling_link().map(Self::with_link)
    }

    /// Returns the next sibling.
    #[inline]
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link.next_sibling_link().map(Self::with_link)
    }

    /// Returns the first sibling.
    #[must_use]
    pub fn first_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let first_child_link = parent_link
                .first_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::with_link(first_child_link)
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
            Self::with_link(last_child_lin)
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
                Self::with_link(first_child_link),
                Self::with_link(last_child_link),
            )
        } else {
            // `self` is the root node.
            (self.clone(), self.clone())
        }
    }

    /// Returns the first child node.
    #[inline]
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.intra_link.first_child_link().map(Self::with_link)
    }

    /// Returns the last child node.
    #[inline]
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link.last_child_link().map(Self::with_link)
    }

    /// Returns the first and the last child nodes.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
        Some((Self::with_link(first_link), Self::with_link(last_link)))
    }
}

/// Tree traverser.
impl<T> Node<T> {
    /// Returns the depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self) -> traverse::DepthFirstTraverser<T> {
        traverse::DepthFirstTraverser::with_start(Some(self.clone()))
    }

    /// Returns the reverse depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_reverse_traverse(&self) -> traverse::ReverseDepthFirstTraverser<T> {
        traverse::ReverseDepthFirstTraverser::with_start(Some(self.clone()))
    }

    /// Returns the children traverser.
    #[inline]
    #[must_use]
    pub fn children(&self) -> traverse::SiblingsTraverser<T> {
        traverse::SiblingsTraverser::new(self.first_child())
    }

    /// Returns the reverse children traverser.
    #[inline]
    #[must_use]
    pub fn children_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        traverse::ReverseSiblingsTraverser::new(self.last_child())
    }
}

/// Node creation and structure modification.
impl<T> Node<T> {
    /// Creates and returns a new node as the root of a new tree.
    #[must_use]
    pub fn new_tree(root_data: T) -> Self {
        let weak_membership = WeakMembership::new();
        let intra_link = NodeBuilder {
            data: root_data,
            parent: Default::default(),
            first_child: Default::default(),
            next_sibling: Default::default(),
            prev_sibling_cyclic: Default::default(),
            membership: weak_membership.clone(),
        }
        .build_link();

        let weak_link = intra_link.downgrade();
        intra_link.replace_prev_sibling_cyclic(weak_link);

        let tree_core_rc = TreeCore::new_rc(intra_link.clone());

        Self::with_link_and_membership(
            intra_link,
            weak_membership.initialize_membership(tree_core_rc),
        )
    }

    /// Detaches the node and its descendant from the current tree, and let it be another tree.
    #[inline]
    pub fn detach_subtree(&self, grant: StructureEditGrant<T>) {
        grant.panic_if_invalid_for_node(self);

        edit::detach_subtree(&self.intra_link);
    }

    /// Creates a node as the next sibling of `self`, and returns the new node.
    #[inline]
    pub fn try_create_node_as(
        &self,
        grant: StructureEditGrant<T>,
        data: T,
        dest: AdoptAs,
    ) -> Result<Self, StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_node_as(&self.intra_link, self.membership.tree_core(), data, dest)
    }

    /// Creates a node as the first child of `self`.
    #[inline]
    pub fn create_as_first_child(&self, grant: StructureEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_first_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the last child of `self`.
    #[inline]
    pub fn create_as_last_child(&self, grant: StructureEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_last_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_prev_sibling(
        &self,
        grant: StructureEditGrant<T>,
        data: T,
    ) -> Result<Self, StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_as_prev_sibling(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_next_sibling(
        &self,
        grant: StructureEditGrant<T>,
        data: T,
    ) -> Result<Self, StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_as_next_sibling(&self.intra_link, self.membership.tree_core(), data)
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
    pub fn replace_with_children(
        &self,
        grant: StructureEditGrant<T>,
    ) -> Result<(), StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::replace_with_children(&self.intra_link)
    }
}
