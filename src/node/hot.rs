//! Hot node, which is a [`Node`] with tree structure edit grant bundled.

use core::fmt;

use crate::membership::MembershipWithEditGrant;
use crate::node::{IntraTreeLink, Node};
use crate::tree::{StructureEditGrant, StructureEditGrantError};

/// A [`Node`] with a tree structure edit grant bundled.
///
/// # Panics
///
/// Panics if the number of active edit grants through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking grants.
#[derive(Clone)]
pub struct HotNode<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: MembershipWithEditGrant<T>,
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
}
