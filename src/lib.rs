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

#[macro_use]
mod macros;

mod anchor;
mod membership;
mod node;
pub mod serial;
pub mod traverse;
mod tree;

pub use self::anchor::{AdoptAs, InsertAs};
pub use self::node::{DebugPrettyPrint, FrozenNode, HierarchyError, HotNode, Node};
pub use self::tree::{
    HierarchyEditGrant, HierarchyEditGrantError, HierarchyEditProhibition,
    HierarchyEditProhibitionError, Tree,
};
