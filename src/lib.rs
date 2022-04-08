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

mod affiliation;
mod node;
pub mod traverse;
mod tree;

use core::fmt;

pub use self::node::Node;

/// Relation of the node being `adopt`ed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdoptAs {
    /// As the first child.
    FirstChild,
    /// As the last child.
    LastChild,
    /// As the previous sibling.
    PreviousSibling,
    /// As the next sibling.
    NextSibling,
}

/// Structure inconsistency error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum StructureError {
    /// Attempt to make a tree empty.
    ///
    /// A tree must have at least one node (the root node), so it cannot be empty.
    EmptyTree,
    /// Attempt to make a node the sibling of the root node.
    SiblingsWithoutParent,
}

impl fmt::Display for StructureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match *self {
            Self::EmptyTree => "attempt to make a tree empty",
            Self::SiblingsWithoutParent => "attempt to make a node sibling of the root node",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StructureError {}
