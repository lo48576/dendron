//! Tree data structure.
//!
//! # Concepts
//!
//! ## Tree
//!
//! Tree consists of one or more nodes. Empty tree cannot exist since a tree
//! must have just one root node.
//!
//! ## Reference counting
//!
//! Lifetime of a tree is managed by references to a tree and its nodes.
//! An object of [`Tree`] type refers to a tree and makes the tree live longer
//! than the reference.
//! Objects of node types ([`Node`], [`FrozenNode`], and [`HotNode`] types)
//! refer to nodes. They make the node (and the tree it belongs to) live longer
//! than the references.
//!
//! These four types are similar to trees created by node types and
//! [`Rc`][`alloc::rc::Rc`], but this crate neither leaks the nodes nor releases
//! the nodes if they are connected to other nodes referred by the user.
//! See examples below for detail.
//!
//! ```
//! use dendron::Node;
//!
//! let root = Node::new_tree("root");
//! let grant = root.tree().grant_hierarchy_edit().unwrap();
//! let child0 = root.create_as_last_child(&grant, "child0");
//! let child1 = root.create_as_last_child(&grant, "child1");
//! let child1_0 = child1.create_as_last_child(&grant, "child1_0");
//! //  root
//! //  |-- child0
//! //  `-- child1
//! //      `-- child1_0
//!
//! drop(grant);
//! drop(root);
//! drop(child0);
//! drop(child1);
//! // Now only `child1_0` is alive.
//!
//! // `child1_0` makes the entire tree and belonging nodes alive,
//! // so `root` is still alive.
//! assert_eq!(*child1_0.root().borrow_data(), "root");
//!
//! let tree = child1_0.tree();
//! drop(child1_0);
//! // Now all node references are dropped and only `tree` is alive.
//!
//! // `tree` makes the entire tree and belonging nodes alive,
//! // so `child0` is still alive.
//! assert_eq!(
//!     *tree.root().first_child().unwrap().borrow_data(),
//!     "child0"
//! );
//!
//! drop(tree);
//! // Now all tree references and node references are dropped, so all objects
//! // in the tree is released. No memory leaks!
//! ```
//!
//! ## Hierarchy edit prohibitions and grants
//!
//! Sometimes users may wish tree hierarchy to be preserved, especially when
//! they are iterating nodes.
//!
//! ```
//! use dendron::tree_node;
//!
//! let root = tree_node! {
//!     "root", [
//!         "0",
//!         "1",
//!         "2",
//!     ]
//! };
//! let grant = root.tree().grant_hierarchy_edit().unwrap();
//! let mut children = root.children();
//! // Detach the first child from `root`.
//! root.first_child().unwrap().detach_subtree(&grant);
//!
//! // Next node is... not "1"! This is because `children` have a cache of
//! // "next node" at the creation of the iterator.
//! assert_eq!(children.next().map(|node| *node.borrow_data()), Some("0"));
//! assert_eq!(children.next(), None);
//! ```
//!
//! To enable "freezing" hierarchy, this crate requires users to have a "grant"
//! to edit hierarchy, and also provides capability to "prohibit" hierarchy
//! editing (for arbitrary duration).
//!
//! ```should_panic
//! use dendron::tree;
//!
//! let tree = tree! { "root" };
//!
//! // This "prohibition" prohibits tree hierarchy editing
//! // (and grant acquisition).
//! let freezer = tree.prohibit_hierarchy_edit().unwrap();
//!
//! // This `grant_hierarchy_edit()` fails, so you can ensure
//! // the hierarchy is stable until `freezer` is dropped!
//! let grant = tree.grant_hierarchy_edit().unwrap();
//! ```
//!
//! "Grant" ([`HierarchyEditGrant`]) and "prohibition" ([`HierarchyEditProhibition`])
//! works in ways similar to [`MutexGuard`][`std::sync::MutexGuard`].
//! The grants and prohibitions work like scoped locks; trees are editable or
//! non-editable during grants or prohibitions exist, and once they are dropped,
//! trees become neutral.
//!
//! Note that grants and prohibitions are mutually exclusive, but only multiple
//! grants or only multiple prohibitions can coexist for a tree, like reader
//! locks. In other words, you can have multiple grants for a tree, and also
//! can have multiple prohibitions for a tree, but not both at the same time.
//!
//! ```
//! use dendron::tree;
//!
//! let tree = tree! { "root" };
//!
//! let freezer1 = tree.prohibit_hierarchy_edit().unwrap();
//! // You can have multiple prohibitions at the same time.
//! let freezer2 = tree.prohibit_hierarchy_edit().unwrap();
//! let freezer3 = tree.prohibit_hierarchy_edit().unwrap();
//!
//! // But not both prohibitions and grants.
//! assert!(tree.grant_hierarchy_edit().is_err());
//!
//! // Release the locks.
//! drop(freezer1);
//! drop(freezer2);
//! drop(freezer3);
//!
//! // Now the tree is neutral. You can re-prohibit or grant hierarchy edit.
//! let grant = tree.grant_hierarchy_edit().unwrap();
//!
//! // Again, prohibitions and grants cannot coexist for the same tree.
//! assert!(tree.prohibit_hierarchy_edit().is_err());
//! ```
//!
//! ## Nodes
//!
//! The crate provides three node types: [`Node`], [`FrozenNode`], and
//! [`HotNode`]. They all have shared ownerships of the tree they belong to.
//!
//! [`Node`] is the basic neutral plain node. It can be turned into `FrozenNode`
//! or `HotNode` by generating or bundling a prohibition or a grant to edit
//! hierarchy.
//!
//! [`FrozenNode`] is a `Node` with a hierarchy edit prohibition bundled. This
//! exposes some extra methods to create tree traversal iterators, for example
//! [`FrozenNode::children_stable`] and
//! [`FrozenNode::allocating_breadth_first_traverse_stable`].
//!
//! [`HotNode`] is a `Node` with a hierarchy edit grant bundled. This exposes
//! some extra methods to edit tree hierarchy without passing grants as
//! arguments, for example [`HotNode::detach_subtree`] and
//! [`HotNode::try_create_node_as`].
//!
//! # Usage
//!
//! To create tree directly, use [`tree_node!`] or [`tree!`].
//!
//! ```
//! use dendron::{tree, tree_node};
//!
//! let root1 = tree_node! {
//!     "root", [
//!         "0",
//!         /("1", [
//!             /("1-0", [
//!                 "1-0-0"
//!             ]),
//!             "1-1",
//!         ]),
//!     ]
//! };
//! let tree1 = root1.tree();
//!
//! let tree2 = tree! {
//!     "root", [
//!         "0",
//!         /("1", [
//!             /("1-0", [
//!                 "1-0-0"
//!             ]),
//!             "1-1",
//!         ]),
//!     ]
//! };
//! let root2 = tree2.root();
//!
//! assert_eq!(root1, root2);
//! assert_eq!(tree1, tree2);
//! ```
//!
//! To create a new orphan (root) node, use [`Node::new_tree`] or
//! [`HotNode::new_tree`].
//!
//! ```
//! use dendron::Node;
//!
//! let root = Node::new_tree("root");
//! ```
//!
//! For other operations (creating a node that is connected to other nodes,
//! moving nodes to other places, iterating nodes, getting and setting data,
//! etc.), see methods of node types ([`Node`], [`FrozenNode`], and [`HotNode`]).
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
pub mod node;
pub mod serial;
pub mod traverse;
pub mod tree;

pub use self::anchor::{AdoptAs, InsertAs};
pub use self::node::{FrozenNode, HierarchyError, HotNode, Node, NodeWeak};
pub use self::tree::{HierarchyEditGrant, HierarchyEditProhibition, Tree, TreeWeak};

/// Deprecated re-export of [`node::DebugPrettyPrint`].
// `#[deprecated] cannot be used for `use` statement. See
// <https://github.com/rust-lang/rust/issues/30827>.
#[deprecated(since = "0.1.1", note = "use `node::DebugPrettyPrint` instead")]
pub type DebugPrettyPrint<'a, T> = self::node::DebugPrettyPrint<'a, T>;

/// Deprecated re-export of [`tree::HierarchyEditGrantError`].
// `#[deprecated] cannot be used for `use` statement. See
// <https://github.com/rust-lang/rust/issues/30827>.
#[deprecated(since = "0.1.1", note = "use `tree::HierarchyEditGrantError` instead")]
pub type HierarchyEditGrantError = self::tree::HierarchyEditGrantError;

/// Deprecated re-export of [`tree::HierarchyEditProhibitionError`].
// `#[deprecated] cannot be used for `use` statement. See
// <https://github.com/rust-lang/rust/issues/30827>.
#[deprecated(
    since = "0.1.1",
    note = "use `tree::HierarchyEditProhibitionError` instead"
)]
pub type HierarchyEditProhibitionError = self::tree::HierarchyEditProhibitionError;
