//! Hot node, which is a [`Node`] with tree structure edit grant bundled.

use core::fmt;

use crate::membership::MembershipWithEditGrant;
use crate::node::{IntraTreeLink, Node};
use crate::tree::StructureEditGrantError;

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
}
