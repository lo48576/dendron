//! Tree hierarchy locking.

use core::cell::Cell;
use core::fmt;

use alloc::rc::{Rc, Weak};

use crate::node::Node;
use crate::tree::TreeCore;

/// An error indicating that an attempt to prohibit edit of the tree hierarchy failed.
///
/// Already existing edit grant is the only cause of this error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HierarchyEditProhibitionError;

impl fmt::Display for HierarchyEditProhibitionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("edif of the tree hierarchy is already granted")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for HierarchyEditProhibitionError {}

/// An error indicating that an attempt to grant edit of the tree hierarchy failed.
///
/// Already existing edit prohibition is the only cause of this error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HierarchyEditGrantError;

impl fmt::Display for HierarchyEditGrantError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("edit of the tree hierarchy is already prohibited")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for HierarchyEditGrantError {}

/// Manager for tree hierarchy edit grant and prohibition.
///
/// Each tree has just one `HierarchyLockManager`.
///
/// If no locks are active, such state is called "neutral".
#[derive(Default, Debug)]
pub struct HierarchyLockManager {
    /// Lock count for the tree.
    ///
    /// Positive count represents the number of edit grants, and the negative
    /// count represents (the negation of) the number of edit prohibitions.
    num_grants: Cell<isize>,
}

impl HierarchyLockManager {
    /// Returns true if there is any active prohibitions or there are no active locks.
    ///
    /// Note that this does not mean more prohibitions can be acquirable; the
    /// lock number limit is not considered by this method.
    #[inline]
    pub(crate) fn ensure_prohibition_acquirable(
        &self,
    ) -> Result<(), HierarchyEditProhibitionError> {
        if self.num_grants.get() <= 0 {
            Ok(())
        } else {
            Err(HierarchyEditProhibitionError)
        }
    }

    /// Returns true if there is any active grants or there are no active locks.
    ///
    /// Note that this does not mean more grants can be acquirable; the
    /// lock number limit is not considered by this method.
    #[inline]
    pub(crate) fn ensure_grant_acquirable(&self) -> Result<(), HierarchyEditGrantError> {
        if self.num_grants.get() >= 0 {
            Ok(())
        } else {
            Err(HierarchyEditGrantError)
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
    fn acquire_prohibition(&self) -> Result<(), HierarchyEditProhibitionError> {
        let old_count = self.num_grants.get();
        if old_count > 0 {
            return Err(HierarchyEditProhibitionError);
        }
        let new_count = old_count
            .checked_sub(1)
            .unwrap_or_else(|| panic!("[precondition] too many hierarchy edit prohibitions"));
        self.num_grants.set(new_count);

        Ok(())
    }

    /// Decrements the edit prohibitions count.
    ///
    /// # Panics
    ///
    /// Panics if no edit prohibitions are active.
    fn release_prohibition(&self) {
        let old_count = self.num_grants.get();
        if old_count >= 0 {
            panic!("[consistency] attempt to release an edit prohibition while none are active");
        }
        self.num_grants.set(old_count + 1);
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
    fn acquire_grant(&self) -> Result<(), HierarchyEditGrantError> {
        let old_count = self.num_grants.get();
        if old_count < 0 {
            return Err(HierarchyEditGrantError);
        }
        let new_count = old_count
            .checked_add(1)
            .unwrap_or_else(|| panic!("[precondition] too many hierarchy edit grants"));
        self.num_grants.set(new_count);

        Ok(())
    }

    /// Decrements the edit grants count.
    ///
    /// # Panics
    ///
    /// Panics if no edit grants are active.
    fn release_grant(&self) {
        let old_count = self.num_grants.get();
        if old_count <= 0 {
            panic!("[consistency] attempt to release an edit grant while none are active");
        }
        self.num_grants.set(old_count - 1);
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

    /// Transfers a lock.
    ///
    /// # Failures
    ///
    /// Fails if `other` cannot be locked with the currently active tree
    /// hierarchy edit lock for `self`.
    pub(super) fn transfer_single_lock_to(&self, other: &Self) -> Result<(), ()> {
        use core::cmp::Ordering;

        match self.num_grants.get().cmp(&0) {
            Ordering::Greater => {
                // Grants are active.
                other.acquire_grant().map_err(|_| ())?;
                let new_count = self.num_grants.get() - 1;
                self.num_grants.set(new_count);
            }
            Ordering::Equal => {}
            Ordering::Less => {
                // Prohibitions are active.
                other.acquire_prohibition().map_err(|_| ())?;
                let new_count = self.num_grants.get() + 1;
                self.num_grants.set(new_count);
            }
        }
        Ok(())
    }
}

/// A token to keep the tree hierarchy prohibited to be edited.
///
/// A prohibition can be created by [`Tree::prohibit_hierarchy_edit`] or
/// [`FrozenNode::extract_hierarchy_edit_prohibition`].
///
/// [`Tree::prohibit_hierarchy_edit`]: `crate::Tree::prohibit_hierarchy_edit`
/// [`FrozenNode::extract_hierarchy_edit_prohibition`]:
///     `crate::FrozenNode::extract_hierarchy_edit_prohibition`
pub struct HierarchyEditProhibition<T>(Weak<TreeCore<T>>);

impl<T> Drop for HierarchyEditProhibition<T> {
    fn drop(&mut self) {
        if let Some(tree_core) = Weak::upgrade(&self.0) {
            tree_core.lock_manager.release_prohibition();
        }
    }
}

impl<T> HierarchyEditProhibition<T> {
    /// Creates a hierarchy edit prohibition for the given tree.
    pub(super) fn new(tree_core: &Rc<TreeCore<T>>) -> Result<Self, HierarchyEditProhibitionError> {
        tree_core.lock_manager.acquire_prohibition()?;
        Ok(HierarchyEditProhibition(Rc::downgrade(tree_core)))
    }

    /// Clones the tree hierarchy edit prohibition.
    ///
    /// # Failures
    ///
    /// Fails if the number of active edit prohibitions for the tree exceeds
    /// `isize::MAX`.
    pub fn try_clone(&self) -> Result<Self, HierarchyEditProhibitionError> {
        if let Some(tree_core) = Weak::upgrade(&self.0) {
            tree_core.lock_manager.acquire_prohibition()?;
        }
        Ok(Self(self.0.clone()))
    }

    /// Returns true if the prohibition is valid for the tree the given node belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node1 = Node::new_tree("foo");
    /// let node2 = Node::new_tree("bar");
    ///
    /// let prohibition1 = node1.tree()
    ///     .prohibit_hierarchy_edit()
    ///     .expect("hierarchy edit should not yet be granted");
    ///
    /// assert!(prohibition1.is_valid_for_node(&node1));
    /// assert!(!prohibition1.is_valid_for_node(&node2));
    /// ```
    ///
    /// [`Tree::prohibit_hierarchy_edit`]:
    ///     `crate::Tree::prohibit_hierarchy_edit`
    /// [`FrozenNode::extract_hierarchy_edit_prohibition`]:
    ///     `crate::FrozenNode::extract_hierarchy_edit_prohibition`
    #[inline]
    #[must_use]
    pub fn is_valid_for_node(&self, node: &Node<T>) -> bool {
        node.ptr_eq_tree_core_weak(&self.0)
    }

    /// Panics if the edit prohibition is not valid for the given node.
    #[inline]
    pub(crate) fn panic_if_invalid_for_node(&self, node: &Node<T>) {
        if !self.is_valid_for_node(node) {
            panic!("[precondition] the prohibition is not valid for the node of interest");
        }
    }
}

/// A token to keep the tree hierarchy granted to be edited.
///
/// A grant can be created by [`Tree::grant_hierarchy_edit`] or
/// [`HotNode::extract_hierarchy_edit_grant`].
///
/// A grant can be created by [`Tree::grant_hierarchy_edit`] or
/// [`HotNode::extract_hierarchy_edit_grant`].
///
/// [`Tree::grant_hierarchy_edit`]: `crate::Tree::grant_hierarchy_edit`
/// [`HotNode::extract_hierarchy_edit_grant`]:
///     `crate::HotNode::extract_hierarchy_edit_grant`
pub struct HierarchyEditGrant<T>(Weak<TreeCore<T>>);

impl<T> Drop for HierarchyEditGrant<T> {
    fn drop(&mut self) {
        if let Some(tree_core) = Weak::upgrade(&self.0) {
            tree_core.lock_manager.release_grant();
        }
    }
}

impl<T> Clone for HierarchyEditGrant<T> {
    /// Clones the tree hierarchy edit grant.
    ///
    /// If you want to avoid the risk of panic (even if it is very unlikely),
    /// use [`try_clone`][`Self::try_clone`] method.
    ///
    /// # Panics
    ///
    /// Panics if the number of active edit grants for the tree will exceed
    /// `isize::MAX`.
    fn clone(&self) -> Self {
        self.try_clone()
            .expect("[precondition] too many hierarchy edit grants are active")
    }
}

impl<T> HierarchyEditGrant<T> {
    /// Creates a hierarchy edit grant for the given tree.
    pub(super) fn new(tree_core: &Rc<TreeCore<T>>) -> Result<Self, HierarchyEditGrantError> {
        tree_core.lock_manager.acquire_grant()?;
        Ok(HierarchyEditGrant(Rc::downgrade(tree_core)))
    }

    /// Clones the tree hierarchy edit grant.
    ///
    /// # Failures
    ///
    /// Fails if the number of active edit grants for the tree exceeds
    /// `isize::MAX`.
    pub fn try_clone(&self) -> Result<Self, HierarchyEditGrantError> {
        if let Some(tree_core) = Weak::upgrade(&self.0) {
            tree_core.lock_manager.acquire_grant()?;
        }
        Ok(Self(self.0.clone()))
    }

    /// Returns true if the grant is valid for the tree the given node belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node1 = Node::new_tree("foo");
    /// let node2 = Node::new_tree("bar");
    ///
    /// let grant1 = node1.tree()
    ///     .grant_hierarchy_edit()
    ///     .expect("hierarchy edit should not yet be prohibited");
    ///
    /// assert!(grant1.is_valid_for_node(&node1));
    /// assert!(!grant1.is_valid_for_node(&node2));
    /// ```
    ///
    /// [`Tree::grant_hierarchy_edit`]: `crate::Tree::grant_hierarchy_edit`
    /// [`HotNode::extract_hierarchy_edit_grant`]:
    ///     `crate::HotNode::extract_hierarchy_edit_grant`
    #[inline]
    #[must_use]
    pub fn is_valid_for_node(&self, node: &Node<T>) -> bool {
        node.ptr_eq_tree_core_weak(&self.0)
    }

    /// Panics if the edit grant is not valid for the given node.
    #[inline]
    pub(crate) fn panic_if_invalid_for_node(&self, node: &Node<T>) {
        if !self.is_valid_for_node(node) {
            panic!("[precondition] the grant is not valid for the node of interest");
        }
    }
}

/// Aggregates locks that is following through a node, not following a tree directly.
#[derive(Default, Debug)]
pub(crate) struct LockAggregatorForNode {
    /// The number of aggregated lock acquisition through the node.
    ///
    /// This aggregator does not need to remember which type of lock is active
    /// because the backend `HierarchyLockManager` knows it.
    aggregated_count: usize,
}

impl LockAggregatorForNode {
    /// Returns true if the aggregator has any lock.
    #[inline]
    #[must_use]
    pub(crate) fn has_lock(&self) -> bool {
        self.aggregated_count != 0
    }

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

    /// Acquires hierarchy edit prohibition.
    pub(crate) fn acquire_edit_prohibition<T>(
        &mut self,
        tree_core: &Rc<TreeCore<T>>,
    ) -> Result<(), HierarchyEditProhibitionError> {
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

    /// Acquires hierarchy edit grant.
    pub(crate) fn acquire_edit_grant<T>(
        &mut self,
        tree_core: &Rc<TreeCore<T>>,
    ) -> Result<(), HierarchyEditGrantError> {
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
