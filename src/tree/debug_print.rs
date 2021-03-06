//! Debug printing of a tree.

use core::fmt;

use crate::node::DebugPrintSubtreeDescendant;
use crate::tree::{Tree, TreeCore};

/// Tree printer for debugging.
///
/// This is provided mainly for debugging purpose. Node that the output format
/// is not guaranteed to be stable, and any format changes won't be considered
/// as breaking changes.
///
/// For usage and output examples, see
/// [`Node::debug_pretty_print`][`crate::Node::debug_pretty_print`] method.
#[derive(Clone, Copy)]
pub struct DebugPrettyPrint<'a, T> {
    /// Tree core.
    core: &'a TreeCore<T>,
}

impl<'a, T> DebugPrettyPrint<'a, T> {
    /// Creates a new `DebugPrint` object for the node.
    #[inline]
    pub(super) fn new(core: &'a TreeCore<T>) -> Self {
        Self { core }
    }
}

impl<'a, T: fmt::Display> fmt::Display for DebugPrettyPrint<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let root = self.core.root_link();
        crate::node::DebugPrettyPrint::new(&root).fmt(f)
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for DebugPrettyPrint<'a, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let root = self.core.root_link();
        crate::node::DebugPrettyPrint::new(&root).fmt(f)
    }
}

/// A wrapper to make a tree debug-printable without printing nodes.
#[derive(Clone, Copy)]
pub struct DebugPrintTreeLocal<'a, T> {
    /// Tree core.
    core: &'a TreeCore<T>,
}

impl<T> fmt::Debug for DebugPrintTreeLocal<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tree")
            .field("lock_manager", &self.core.lock_manager)
            .finish()
    }
}

impl<'a, T> DebugPrintTreeLocal<'a, T> {
    /// Creates a new `DebugPrintTreeLocal`.
    #[inline]
    #[must_use]
    pub(super) fn new(core: &'a TreeCore<T>) -> Self {
        Self { core }
    }
}

/// A wrapper to make a node debug-printable with nodes.
#[derive(Clone, Copy)]
pub struct DebugPrintTree<'a, T> {
    /// Tree.
    tree: &'a Tree<T>,
}

impl<T: fmt::Debug> fmt::Debug for DebugPrintTree<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let root_link = self.tree.core.root_link();
        f.debug_struct("Tree")
            .field("lock_manager", &self.tree.core.lock_manager)
            .field("nodes", &DebugPrintSubtreeDescendant::new_plain(&root_link))
            .finish()
    }
}

impl<'a, T: fmt::Debug> DebugPrintTree<'a, T> {
    /// Creates a new `DebugPrintTree`.
    #[inline]
    #[must_use]
    pub(super) fn new(tree: &'a Tree<T>) -> Self {
        Self { tree }
    }
}
