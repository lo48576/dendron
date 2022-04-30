//! Debug printing of a tree.

use core::fmt;

use crate::tree::TreeCore;

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
