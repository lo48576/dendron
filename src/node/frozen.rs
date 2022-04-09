//! Frozen node, which is a [`Node`] with tree structure edit prohibition bundled.

use core::fmt;

use crate::membership::MembershipWithEditProhibition;
use crate::node::{IntraTreeLink, Node};
use crate::tree::{StructureEditProhibition, StructureEditProhibitionError};

/// A [`Node`] with a tree structure edit prohibition bundled.
///
/// # Panics
///
/// Panics if the number of active edit prohibitions through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking prohibitions.
#[derive(Clone)]
pub struct FrozenNode<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: MembershipWithEditProhibition<T>,
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
}
