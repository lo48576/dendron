//! Frozen node, which is a [`Node`] with tree structure edit prohibition bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::membership::{Membership, MembershipWithEditProhibition};
use crate::node::{IntraTreeLink, Node};
use crate::traverse;
use crate::tree::{StructureEditProhibition, StructureEditProhibitionError, Tree, TreeCore};

/// A [`Node`] with a tree structure edit prohibition bundled.
///
/// # Panics
///
/// Panics if the number of active edit prohibitions through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking prohibitions.
pub struct FrozenNode<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: MembershipWithEditProhibition<T>,
}

impl<T> Clone for FrozenNode<T> {
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            membership: self.membership.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for FrozenNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FrozenNode")
            .field("data", &self.intra_link.try_borrow_data())
            .field("next_sibling", &self.intra_link.next_sibling_link())
            .field("first_child", &self.intra_link.first_child_link())
            .field("membership", &self.membership)
            .finish()
    }
}

impl<T> FrozenNode<T> {
    /// Creates a new `FrozenNode` from the given plain node.
    pub(super) fn from_node(node: Node<T>) -> Result<Self, StructureEditProhibitionError> {
        let Node {
            intra_link,
            membership,
        } = node;
        let membership = MembershipWithEditProhibition::new(membership)?;
        Ok(Self {
            intra_link,
            membership,
        })
    }

    /// Creates a new `FrozenNode` from the given plain node and the prohibition.
    ///
    /// # Panics
    ///
    /// Panics if the structure edit prohibition is not valid for the given node.
    ///
    /// Panics if there are too many prohibitions for the node or for the tree.
    #[must_use]
    pub(super) fn from_node_and_prohibition(
        node: Node<T>,
        prohibition: StructureEditProhibition<T>,
    ) -> Self {
        prohibition.panic_if_invalid_for_node(&node);

        let Node {
            intra_link,
            membership,
        } = node;
        let membership = MembershipWithEditProhibition::new(membership)
            .expect("[validity] a valid prohibition already exists for the tree");
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
    /// Panics if the tree is prohibited to be edited.
    #[must_use]
    pub(crate) fn from_node_link_with_prohibition(intra_link: IntraTreeLink<T>) -> Self {
        let membership = intra_link.membership().upgrade().expect(
            "[consistency] the membership must be alive since the corresponding node link is alive",
        );
        let membership = MembershipWithEditProhibition::new(membership)
            .expect("[consistency] there should have already been tree structure edit prohibition");

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

impl<T> From<FrozenNode<T>> for Node<T> {
    #[inline]
    fn from(node: FrozenNode<T>) -> Self {
        node.plain()
    }
}

// Common methods below.

/// Data access.
impl<T> FrozenNode<T> {
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

    /// Returns `true` if the two `FrozenNode`s point to the same allocation.
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }
}

/// Neighbor nodes accessor.
impl<T> FrozenNode<T> {
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
        Self::from_node_link_with_prohibition(self.tree_core().root_link())
    }

    /// Returns the parent node.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link
            .parent_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the previous sibling.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link
            .prev_sibling_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the next sibling.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link
            .next_sibling_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the first sibling.
    #[must_use]
    pub fn first_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
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
    #[must_use]
    pub fn last_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let last_child_lin = parent_link
                .last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::from_node_link_with_prohibition(last_child_lin)
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
                Self::from_node_link_with_prohibition(first_child_link),
                Self::from_node_link_with_prohibition(last_child_link),
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
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the last child node.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link
            .last_child_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns links to the first and the last child nodes.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
        Some((
            Self::from_node_link_with_prohibition(first_link),
            Self::from_node_link_with_prohibition(last_link),
        ))
    }
}

/// Tree traverser.
impl<T> FrozenNode<T> {
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

    /// Returns the stable double-ended depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse_stable(&self) -> traverse::StableDepthFirstTraverser<T> {
        traverse::StableDepthFirstTraverser::with_toplevel(Some(self.clone()))
    }

    /// Returns the stable double-ended children traverser.
    #[inline]
    #[must_use]
    pub fn children_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_parent(Some(self.clone()))
    }

    /// Returns the stable siblings traverser.
    #[inline]
    #[must_use]
    pub fn siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children_stable(),
            None => self.following_siblings_or_self_stable(),
        }
    }

    /// Returns the stable preceding siblings traverser.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_first_last(Some((
            self.first_sibling(),
            self.clone(),
        )))
    }

    /// Returns the stable preceding siblings traverser.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        let mut iter = self.preceding_siblings_or_self_stable();
        iter.next();
        iter
    }

    /// Returns the stable following siblings traverser.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_first_last(Some((
            self.clone(),
            self.last_sibling(),
        )))
    }

    /// Returns the stable following siblings traverser.
    #[inline]
    #[must_use]
    pub fn following_siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        let mut iter = self.following_siblings_or_self_stable();
        iter.next();
        iter
    }
}
