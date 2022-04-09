//! Frozen node, which is a [`Node`] with tree structure edit prohibition bundled.

use core::fmt;

use crate::membership::MembershipWithEditProhibition;
use crate::node::{IntraTreeLink, Node};
use crate::tree::StructureEditProhibitionError;

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
}
