//! Debug printing of a single node.

use core::fmt;

use crate::node::NodeCoreLink;

use crate::node::debug_print::{FakeOption, RawStr};

/// Node type.
#[derive(Clone, Copy)]
enum NodeType {
    /// `Node`.
    Plain,
    /// `FrozenNode`.
    Frozen,
    /// `HotNode`.
    Hot,
}

impl NodeType {
    /// Returns the node type name.
    #[inline]
    #[must_use]
    fn name(self) -> &'static str {
        match self {
            Self::Plain => "Node",
            Self::Frozen => "FrozenNode",
            Self::Hot => "HotNode",
        }
    }
}

/// A wrapper to make a node debug-printable without neighbors.
#[derive(Clone, Copy)]
pub struct DebugPrintNodeLocal<'a, T> {
    /// Intra-tree link.
    link: &'a NodeCoreLink<T>,
    /// Node type.
    node_type: NodeType,
}

impl<T: fmt::Debug> fmt::Debug for DebugPrintNodeLocal<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ds = f.debug_struct(self.node_type.name());
        match self.link.try_borrow_data() {
            Ok(v) => ds.field("data", &v),
            Err(_) => ds.field("data", &RawStr("<borrowed>")),
        };
        ds.field("parent", &FakeOption::some_if_true(!self.link.is_root()))
            .field(
                "prev_sibling",
                &FakeOption::some_if_true(self.link.has_prev_sibling()),
            )
            .field(
                "next_sibling",
                &FakeOption::some_if_true(self.link.has_next_sibling()),
            )
            .field(
                "first_child",
                &FakeOption::some_if_true(self.link.has_children()),
            )
            .field("tree", &self.link.tree_core().debug_print_local())
            .finish()
    }
}

impl<'a, T> DebugPrintNodeLocal<'a, T> {
    /// Creates a new `DebugPrintNodeLocal` for plain `Node`.
    #[inline]
    #[must_use]
    pub(in crate::node) fn new_plain(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Plain,
        }
    }

    /// Creates a new `DebugPrintNodeLocal` for `FrozenNode`.
    #[inline]
    #[must_use]
    pub(in crate::node) fn new_frozen(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Frozen,
        }
    }

    /// Creates a new `DebugPrintNodeLocal` for `HotNode`.
    #[inline]
    #[must_use]
    pub(in crate::node) fn new_hot(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Hot,
        }
    }
}

/// A wrapper to make a node debug-printable without neighbors.
#[derive(Clone, Copy)]
pub struct DebugPrintSubtree<'a, T> {
    /// Intra-tree link.
    link: &'a NodeCoreLink<T>,
    /// Node type.
    node_type: NodeType,
}

impl<T: fmt::Debug> fmt::Debug for DebugPrintSubtree<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ds = f.debug_struct(self.node_type.name());
        ds.field("tree", &self.link.tree_core().debug_print_local());
        match self.link.try_borrow_data() {
            Ok(v) => ds.field("data", &v),
            Err(_) => ds.field("data", &RawStr("<borrowed>")),
        };
        ds.field(
            "children",
            &DebugPrintSubtreeChildren {
                link: self.link,
                node_type: self.node_type,
            },
        )
        .finish()
    }
}

impl<'a, T> DebugPrintSubtree<'a, T> {
    /// Creates a new `DebugPrintSubtree` for plain `Node`.
    #[inline]
    #[must_use]
    pub(in crate::node) fn new_plain(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Plain,
        }
    }

    /// Creates a new `DebugPrintSubtree` for `FrozenNode`
    #[inline]
    #[must_use]
    pub(in crate::node) fn new_frozen(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Plain,
        }
    }

    /// Creates a new `DebugPrintSubtree` for `HotNode`
    #[inline]
    #[must_use]
    pub(in crate::node) fn new_hot(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Hot,
        }
    }
}

/// An internal wrapper for descendants of `DebugPrintSubtree` target.
#[derive(Clone, Copy)]
struct DebugPrintSubtreeChildren<'a, T> {
    /// Intra-tree link.
    link: &'a NodeCoreLink<T>,
    /// Node type.
    node_type: NodeType,
}

impl<T: fmt::Debug> fmt::Debug for DebugPrintSubtreeChildren<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut dl = f.debug_list();
        let mut next_child = self.link.first_child_link();
        while let Some(child) = next_child {
            dl.entry(&DebugPrintSubtreeDescendant {
                link: &child,
                node_type: self.node_type,
            });
            next_child = child.next_sibling_link();
        }
        dl.finish()
    }
}

/// An internal wrapper for a descendant of `DebugPrintSubtree` target.
#[derive(Clone, Copy)]
pub(crate) struct DebugPrintSubtreeDescendant<'a, T> {
    /// Intra-tree link.
    link: &'a NodeCoreLink<T>,
    /// Node type.
    node_type: NodeType,
}

impl<T: fmt::Debug> fmt::Debug for DebugPrintSubtreeDescendant<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ds = f.debug_struct("Node");
        match self.link.try_borrow_data() {
            Ok(v) => ds.field("data", &v),
            Err(_) => ds.field("data", &RawStr("<borrowed>")),
        };
        ds.field(
            "children",
            &DebugPrintSubtreeChildren {
                link: self.link,
                node_type: self.node_type,
            },
        )
        .finish()
    }
}

impl<'a, T> DebugPrintSubtreeDescendant<'a, T> {
    /// Creates a new `DebugPrintSubtreeDescendant` for plain `Node`.
    #[inline]
    #[must_use]
    pub(crate) fn new_plain(link: &'a NodeCoreLink<T>) -> Self {
        Self {
            link,
            node_type: NodeType::Plain,
        }
    }
}
