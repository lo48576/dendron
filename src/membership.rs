//! Nodes' membership to trees.

use core::cell::{Ref, RefCell};
use core::fmt;
use core::num::NonZeroUsize;

use alloc::rc::{Rc, Weak};

use crate::tree::{
    HierarchyEditGrantError, HierarchyEditProhibitionError, LockAggregatorForNode, TreeCore,
};

/// A membership of a node to a tree.
///
/// Note that nodes may change its affiliation to another tree. In this case,
/// membership should also be changed for all `Node` objects referring to the
/// node, so this will be usually shared as `Rc<RefCell<<T>>>`.
pub(crate) enum MembershipCore<T> {
    /// Weak membership: non-owning reference to the tree core.
    ///
    /// If there are no `Node<T>`s for the node, the membership will stay in
    /// this state.
    Weak {
        /// A weak reference to the tree core.
        tree_core: Weak<TreeCore<T>>,
    },
    /// Strong membership: shared owning reference to the tree core, and strong refcounts.
    ///
    /// If there are any `Node<T>`s for the node, the membership will stay in
    /// this state. In other words, membership in this state guarantees that the
    /// tree and some nodes are alive.
    Strong {
        /// A strong reference to the tree core.
        tree_core: Rc<TreeCore<T>>,
        /// Strong reference count for the tree core from this membership.
        tree_refcount: NonZeroUsize,
        /// Lock aggregator.
        lock_aggregator: LockAggregatorForNode,
    },
}

impl<T: fmt::Debug> fmt::Debug for MembershipCore<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Weak { .. } => write!(f, "Weak {{ .. }}"),
            Self::Strong {
                tree_refcount,
                lock_aggregator,
                ..
            } => f
                .debug_struct("Strong")
                .field("tree_refcount", &tree_refcount)
                .field("lock_aggregator", &lock_aggregator)
                .finish_non_exhaustive(),
        }
    }
}

impl<T> MembershipCore<T> {
    /// Creates a new (weak) `MembershipCore` for the given tree.
    #[inline]
    #[must_use]
    pub(crate) fn new_for_existing_tree(tree_core: &Rc<TreeCore<T>>) -> Self {
        Self::Weak {
            tree_core: Rc::downgrade(tree_core),
        }
    }

    /// Creates a new (weak) `MembershipCore` with the dangling tree reference.
    #[inline]
    #[must_use]
    pub(crate) fn dangling() -> Self {
        Self::Weak {
            tree_core: Weak::new(),
        }
    }
}

/// A convenience wrapper for `RefCell<MembershipCore<T>>`.
#[derive(Clone, Copy)]
pub(crate) struct MembershipRef<'a, T>(&'a RefCell<MembershipCore<T>>);

impl<'a, T> MembershipRef<'a, T> {
    /// Creates a new membership reference.
    #[inline]
    #[must_use]
    pub(crate) fn new(core: &'a RefCell<MembershipCore<T>>) -> Self {
        Self(core)
    }

    /// Initializes the membership with the given tree, and sets the tree refcount to 1.
    ///
    /// # Panics
    ///
    /// Panics if the membership has been already associated to any tree.
    /// The membership should be a one that is unmodified since created by
    /// `MembershipCore::dangling()`.
    pub(crate) fn initialize_with_tree_and_set_refcount_to_1(self, tree_core: Rc<TreeCore<T>>) {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &*core {
            // Not testing if `weak` is dereferenceable, but testing if the
            // reference is the value created by `Weak::new()`. This condition
            // will be false once the membership is fully initialized.
            // This comparison with `&Weak::new()` is intentional.
            MembershipCore::Weak { tree_core } if Weak::ptr_eq(tree_core, &Weak::new()) => {}
            _ => panic!(
                "[consistency] the membership should be unmodified since created as dangling"
            ),
        }
        debug_assert!(matches!(&*core, MembershipCore::Weak { .. }));

        // Create a strong reference and set the count to 1.
        let tree_refcount = NonZeroUsize::new(1).expect("[validity] 1 is nonzero");
        *core = MembershipCore::Strong {
            tree_core,
            tree_refcount,
            lock_aggregator: Default::default(),
        };
    }

    /// Returns the temporary reference to the `Rc` of the tree core.
    #[must_use]
    pub(crate) fn tree_core_strong_ref(self) -> Option<Ref<'a, Rc<TreeCore<T>>>> {
        let core = self
            .0
            .try_borrow()
            .expect("[consistency] membership core should never be borrowed nestedly");
        Ref::filter_map(core, |core| match core {
            MembershipCore::Weak { .. } => None,
            MembershipCore::Strong { tree_core, .. } => Some(tree_core),
        })
        .ok()
    }

    /// Returns the shared owning reference to the tree core.
    #[must_use]
    pub(crate) fn tree_core_opt(self) -> Option<Rc<TreeCore<T>>> {
        let core = self
            .0
            .try_borrow()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &*core {
            MembershipCore::Weak { tree_core } => Weak::upgrade(tree_core),
            MembershipCore::Strong { tree_core, .. } => Some(tree_core.clone()),
        }
    }

    /// Increments the reference count of the tree.
    ///
    /// # Failures
    ///
    /// Fails if the tree is already released and unavailable.
    pub(crate) fn increment_tree_refcount(self) -> Result<(), ()> {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        // Increment refcount.
        match &mut *core {
            MembershipCore::Weak { tree_core } => {
                let tree_refcount = NonZeroUsize::new(1).expect("[consistency] 1 is nonzero");
                let tree_core = tree_core.upgrade().ok_or(())?;
                *core = MembershipCore::Strong {
                    tree_core,
                    tree_refcount,
                    lock_aggregator: Default::default(),
                };
            }
            MembershipCore::Strong { tree_refcount, .. } => {
                let incremented = tree_refcount
                    .checked_add(1)
                    .expect("[validity] the memory cannot have `usize::MAX` references");
                *tree_refcount = incremented;
            }
        }
        Ok(())
    }

    /// Increments the reference count of the tree, assuming the refcount is already nonzero.
    pub(crate) fn increment_nonzero_tree_refcount(self) {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        // Increment refcount.
        match &mut *core {
            MembershipCore::Weak { .. } => {
                unreachable!("[consistency] the membership should have a strong reference");
            }
            MembershipCore::Strong { tree_refcount, .. } => {
                let incremented = tree_refcount
                    .checked_add(1)
                    .expect("[validity] the memory cannot have `usize::MAX` references");
                *tree_refcount = incremented;
            }
        }
    }

    /// Decrements the reference count of the tree.
    pub(crate) fn decrement_tree_refcount(self) {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        // Decrement refcount.
        match &mut *core {
            MembershipCore::Weak { .. } => {
                unreachable!("[consistency] the membership should have a strong reference");
            }
            MembershipCore::Strong {
                tree_core,
                tree_refcount,
                lock_aggregator,
            } => {
                // This subtraction never overflows.
                let decremented = NonZeroUsize::new(tree_refcount.get() - 1);
                match decremented {
                    Some(new_count) => *tree_refcount = new_count,
                    None => {
                        assert!(
                            !lock_aggregator.has_lock(),
                            "[consistency] locks can be acquired only from strong node references"
                        );
                        let weak_core = Rc::downgrade(tree_core);
                        *core = MembershipCore::Weak {
                            tree_core: weak_core,
                        };
                    }
                }
            }
        }
    }

    /// Lets the membership refer to the given tree core.
    ///
    /// # Failures
    ///
    /// Fails if the new tree cannot be locked with the currently active tree
    /// hierarchy edit lock.
    pub(crate) fn set_tree_core(&self, new_tree_core: &Rc<TreeCore<T>>) -> Result<(), ()> {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &mut *core {
            MembershipCore::Weak { tree_core } => *tree_core = Rc::downgrade(new_tree_core),
            MembershipCore::Strong {
                tree_core,
                lock_aggregator,
                ..
            } => {
                if lock_aggregator.has_lock() {
                    tree_core.transfer_single_lock_to(new_tree_core)?;
                }
                *tree_core = new_tree_core.clone();
            }
        }
        Ok(())
    }

    /// Returns true if the membership refers to the same tree core allocation.
    #[must_use]
    pub(crate) fn ptr_eq_tree_core(&self, tree_core: &Rc<TreeCore<T>>) -> bool {
        let core = self
            .0
            .try_borrow()
            .expect("[consistency] membership core should never be borrowed nestedly");
        let self_ptr = match &*core {
            MembershipCore::Weak { tree_core } => tree_core.as_ptr(),
            MembershipCore::Strong { tree_core, .. } => Rc::as_ptr(tree_core),
        };
        self_ptr == Rc::as_ptr(tree_core)
    }

    /// Decrements the aggregated lock count.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the aggregated lock count is zero, or
    /// * the membership is not strong.
    pub(super) fn decrement_edit_lock_count(&self) {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &mut *core {
            MembershipCore::Weak { .. } => {
                unreachable!("[consistency] the node should have an incoming strong reference")
            }
            MembershipCore::Strong {
                tree_core,
                lock_aggregator,
                ..
            } => {
                lock_aggregator.decrement_count(tree_core);
            }
        }
    }

    /// Increments hierarchy edit lock count, assuming the count is nonzero.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the aggregated lock count is zero or `usize::MAX`, or
    /// * the membership is not strong.
    pub(super) fn increment_nonzero_edit_lock_count(&self) {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &mut *core {
            MembershipCore::Weak { .. } => {
                unreachable!("[consistency] the node should have an incoming strong reference")
            }
            MembershipCore::Strong {
                lock_aggregator, ..
            } => lock_aggregator.increment_nonzero_count(),
        }
    }

    /// Acquires hierarchy edit prohibition.
    ///
    /// # Panics
    ///
    /// Panics if the the membership is not strong.
    pub(super) fn acquire_edit_prohibition(&self) -> Result<(), HierarchyEditProhibitionError> {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &mut *core {
            MembershipCore::Weak { .. } => {
                unreachable!("[consistency] the node should have an incoming strong reference")
            }
            MembershipCore::Strong {
                tree_core,
                lock_aggregator,
                ..
            } => lock_aggregator.acquire_edit_prohibition(tree_core),
        }
    }

    /// Acquires hierarchy edit grant.
    ///
    /// # Panics
    ///
    /// Panics if the the membership is not strong.
    pub(crate) fn acquire_edit_grant(&self) -> Result<(), HierarchyEditGrantError> {
        let mut core = self
            .0
            .try_borrow_mut()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &mut *core {
            MembershipCore::Weak { .. } => {
                unreachable!("[consistency] the node should have an incoming strong reference")
            }
            MembershipCore::Strong {
                tree_core,
                lock_aggregator,
                ..
            } => lock_aggregator.acquire_edit_grant(tree_core),
        }
    }
}
