//! Node.

mod debug_print;
mod edit;
mod frozen;
mod hot;
mod internal;
mod plain;

use core::cell::BorrowError;
use core::fmt;

pub(crate) use self::debug_print::DebugPrintSubtreeDescendant;
pub use self::debug_print::{DebugPrettyPrint, DebugPrintNodeLocal, DebugPrintSubtree};
pub use self::frozen::FrozenNode;
pub use self::hot::HotNode;
pub(crate) use self::internal::IntraTreeLink;
use self::internal::{IntraTreeLinkWeak, NodeBuilder, NumChildren};
pub use self::plain::{Node, NodeWeak};

/// Hierarchy modification error.
// `From<BorrowError> for Self` is not implemented because the crate should not
// allow users to convert any `BorrowError` into this error, especially when
// user-provided `BorrowError` is unrelated to the hierarchy modification.
#[derive(Debug)]
#[non_exhaustive]
pub enum HierarchyError {
    /// Attempt to make a node its own descendant or ancestor.
    AncestorDescendantLoop,
    /// Attempt to make a tree empty.
    ///
    /// A tree must have at least one node (the root node), so it cannot be empty.
    EmptyTree,
    /// Attempt to make a node the sibling of the root node.
    SiblingsWithoutParent,
    /// Failed to borrow node data.
    BorrowNodeData(BorrowError),
}

impl fmt::Display for HierarchyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match *self {
            Self::AncestorDescendantLoop => "attempt to make a node its own descendant or ancestor",
            Self::EmptyTree => "attempt to make a tree empty",
            Self::SiblingsWithoutParent => "attempt to make a node sibling of the root node",
            Self::BorrowNodeData(_) => "failed to borrow the data associated to the node",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for HierarchyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BorrowNodeData(e) => Some(e),
            _ => None,
        }
    }
}
