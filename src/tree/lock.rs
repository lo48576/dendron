//! Tree structure locking.

use core::cell::Cell;
use core::fmt;

use alloc::rc::Rc;

use crate::tree::TreeCore;

/// An error indicating that an attempt to prohibit edit of the tree structure failed.
///
/// Already existing edit grant is the only cause of this error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructureEditProhibitionError;

impl fmt::Display for StructureEditProhibitionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("edif of the tree structure is already granted")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StructureEditProhibitionError {}

/// An error indicating that an attempt to grant edit of the tree structure failed.
///
/// Already existing edit prohibition is the only cause of this error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructureEditGrantError;

impl fmt::Display for StructureEditGrantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("edit of the tree structure is already prohibited")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StructureEditGrantError {}

/// Manager for tree structure edit grant and prohibition.
///
/// Each tree has just one `StructureLockManager`.
///
/// If no locks are active, such state is called "neutral".
#[derive(Default, Debug)]
pub struct StructureLockManager {
    /// Lock count for the tree.
    ///
    /// Positive count represents the number of edit grants, and the negative
    /// count represents (the negation of) the number of edit prohibitions.
    num_grants: Cell<isize>,
}

impl StructureLockManager {
    /// Returns true if there is any active prohibitions or there are no active locks.
    ///
    /// Note that this does not mean more prohibitions can be acquirable; the
    /// lock number limit is not considered by this method.
    #[inline]
    pub(crate) fn ensure_prohibition_acquirable(
        &self,
    ) -> Result<(), StructureEditProhibitionError> {
        if self.num_grants.get() <= 0 {
            Ok(())
        } else {
            Err(StructureEditProhibitionError)
        }
    }

    /// Returns true if there is any active grants or there are no active locks.
    ///
    /// Note that this does not mean more grants can be acquirable; the
    /// lock number limit is not considered by this method.
    #[inline]
    pub(crate) fn ensure_grant_acquirable(&self) -> Result<(), StructureEditGrantError> {
        if self.num_grants.get() >= 0 {
            Ok(())
        } else {
            Err(StructureEditGrantError)
        }
    }

    /// Increments the edit prohibitions count.
    ///
    /// # Failures
    ///
    /// Fails if edit grants are already active.
    ///
    /// # Panics
    ///
    /// Panics if the number of active edit prohibitions for the tree exceeds
    /// `isize::MAX`. This is very unlikely to happen without leaking prohibitions.
    fn acquire_prohibition(&self) -> Result<(), StructureEditProhibitionError> {
        let old_count = self.num_grants.get();
        if old_count > 0 {
            return Err(StructureEditProhibitionError);
        }
        let new_count = old_count
            .checked_sub(1)
            .unwrap_or_else(|| panic!("[precondition] too many structure edit prohibitions"));
        self.num_grants.set(new_count);

        Ok(())
    }

    /// Increments the edit grants count.
    ///
    /// # Failures
    ///
    /// Fails if edit prohibitions are already active.
    ///
    /// # Panics
    ///
    /// Panics if the number of active edit grants for the tree exceeds
    /// `isize::MAX as usize + 1`. This is very unlikely to happen without
    /// leaking grants.
    fn acquire_grant(&self) -> Result<(), StructureEditGrantError> {
        let old_count = self.num_grants.get();
        if old_count < 0 {
            return Err(StructureEditGrantError);
        }
        let new_count = old_count
            .checked_add(1)
            .unwrap_or_else(|| panic!("[precondition] too many structure edit grants"));
        self.num_grants.set(new_count);

        Ok(())
    }

    /// Decrements lock count of any type, assuming it is nonzero.
    ///
    /// # Panics
    ///
    /// Panics if there is no active edit lock.
    fn release_any_lock(&self) {
        use core::cmp::Ordering;

        match self.num_grants.get().cmp(&0) {
            Ordering::Greater => {
                // Grants are active.
                let new_count = self.num_grants.get() - 1;
                self.num_grants.set(new_count);
            }
            Ordering::Equal => panic!("[consistency] lock count should be nonzero"),
            Ordering::Less => {
                // Prohibitions are active.
                let new_count = self.num_grants.get() + 1;
                self.num_grants.set(new_count);
            }
        }
    }
}

/// Aggregates locks that is following through a node, not following a tree directly.
#[derive(Default, Debug)]
pub(crate) struct LockAggregatorForNode {
    /// The number of aggregated lock acquisition through the node.
    ///
    /// This aggregator does not need to remember which type of lock is active
    /// because the backend `StructureLockManager` knows it.
    aggregated_count: usize,
}

impl LockAggregatorForNode {
    /// Decrements the lock count.
    ///
    /// # Panics
    ///
    /// Panics if the aggregated lock count is zero.
    pub(crate) fn decrement_count<T>(&mut self, tree_core: &Rc<TreeCore<T>>) {
        if self.aggregated_count == 0 {
            panic!("[consistency] attempt to decrement aggregated lock count while it is zero");
        }
        self.aggregated_count -= 1;

        if self.aggregated_count == 0 {
            tree_core.lock_manager.release_any_lock();
        }
    }

    /// Increments the lock count, assuming the count is nonzero.
    ///
    /// # Panics
    ///
    /// Panics if the aggregated lock count is zero or `usize::MAX`.
    pub(crate) fn increment_nonzero_count(&mut self) {
        if self.aggregated_count == 0 {
            panic!("[consistency] expected the lock aggregator already has some locks");
        }
        let new_count = self.aggregated_count.checked_add(1).unwrap_or_else(|| {
            panic!("[precondition] attempt to acuqire too many locks for a node")
        });
        self.aggregated_count = new_count;
    }

    /// Acquires structure edit prohibition.
    pub(crate) fn acquire_edit_prohibition<T>(
        &mut self,
        tree_core: &Rc<TreeCore<T>>,
    ) -> Result<(), StructureEditProhibitionError> {
        tree_core.lock_manager.ensure_prohibition_acquirable()?;
        if self.aggregated_count != 0 {
            // Already has locks.
            self.increment_nonzero_count();
        } else {
            // No active locks.
            tree_core.lock_manager.acquire_prohibition()?;
            self.aggregated_count = 1;
        }
        Ok(())
    }

    /// Acquires structure edit grant.
    pub(crate) fn acquire_edit_grant<T>(
        &mut self,
        tree_core: &Rc<TreeCore<T>>,
    ) -> Result<(), StructureEditGrantError> {
        tree_core.lock_manager.ensure_grant_acquirable()?;
        if self.aggregated_count != 0 {
            // Already has locks.
            self.increment_nonzero_count();
        } else {
            // No active locks.
            tree_core.lock_manager.acquire_grant()?;
            self.aggregated_count = 1;
        }
        Ok(())
    }
}
