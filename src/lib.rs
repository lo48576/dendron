//! Tree data structure.
#![forbid(unsafe_code)]
//#![forbid(unsafe_op_in_unsafe_fn)]
//#![forbid(clippy::undocumented_unsafe_blocks)]
#![warn(rust_2018_idioms)]
// `clippy::missing_docs_in_private_items` implies `missing_docs`.
#![warn(clippy::missing_docs_in_private_items)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::unwrap_used)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

mod anchor;
mod membership;
mod node;
pub mod serial;
pub mod traverse;
mod tree;

use core::cell::BorrowError;
use core::fmt;

pub use self::anchor::AdoptAs;
pub use self::node::{DebugPrettyPrint, FrozenNode, HotNode, Node};
pub use self::tree::{
    StructureEditGrant, StructureEditGrantError, StructureEditProhibition,
    StructureEditProhibitionError, Tree,
};

/// Structure modification error.
// `From<BorrowError> for Self` is not implemented because the crate should not
// allow users to convert any `BorrowError` into this error, especially when
// user-provided `BorrowError` is unrelated to the structure modification.
#[derive(Debug)]
#[non_exhaustive]
pub enum StructureError {
    /// Attempt to make a tree empty.
    ///
    /// A tree must have at least one node (the root node), so it cannot be empty.
    EmptyTree,
    /// Attempt to make a node the sibling of the root node.
    SiblingsWithoutParent,
    /// Failed to borrow node data.
    BorrowNodeData(BorrowError),
}

impl fmt::Display for StructureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match *self {
            Self::EmptyTree => "attempt to make a tree empty",
            Self::SiblingsWithoutParent => "attempt to make a node sibling of the root node",
            Self::BorrowNodeData(_) => "failed to borrow the data associated to the node",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StructureError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BorrowNodeData(e) => Some(e),
            _ => None,
        }
    }
}
