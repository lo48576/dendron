//! Debug printing of a single node.

use core::fmt;

use crate::membership::Membership;
use crate::node::IntraTreeLink;

use crate::node::debug_print::{FakeOption, RawStr};

/// A wrapper to make a node debug-printable without neighbors.
#[derive(Clone, Copy)]
pub struct DebugPrintNodeLocal<'a, T> {
    /// Intra-tree link.
    link: &'a IntraTreeLink<T>,
    /// Membership.
    membership: &'a Membership<T>,
}

impl<T: fmt::Debug> fmt::Debug for DebugPrintNodeLocal<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ds = f.debug_struct("Node");
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
            .field(
                "tree",
                &(*self.membership.tree_core_ref()).debug_print_local(),
            )
            .finish()
    }
}

impl<'a, T> DebugPrintNodeLocal<'a, T> {
    /// Creates a new `DebugPrintNodeLocal`.
    #[inline]
    #[must_use]
    pub(in crate::node) fn new(link: &'a IntraTreeLink<T>, membership: &'a Membership<T>) -> Self {
        Self { link, membership }
    }
}
