//! Nodes' membership to trees.

use core::cell::{Ref, RefCell};
use core::fmt;
use core::num::NonZeroUsize;

use alloc::rc::{Rc, Weak};

use crate::tree::{LockAggregatorForNode, Tree, TreeCore};

/// A membership of a node to a tree.
///
/// Note that nodes may change its affiliation to another tree. In this case,
/// membership should also be changed for all `Node` objects referring to the
/// node, so this will be usually shared as `Rc<RefCell<<T>>>`.
pub(crate) enum MembershipCore<T> {
    /// Non-owning reference to the tree core.
    ///
    /// If there are no `Node<T>`s for the node, the membership will stay in
    /// this state.
    Weak {
        /// A weak reference to the tree core.
        tree_core: Weak<TreeCore<T>>,
    },
    /// Shared owning reference to the tree core, and strong refcounts.
    ///
    /// If there are any `Node<T>`s for the node, the membership will stay in
    /// this state.
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

/// A convenience wrapper for `RefCell<MembershipCore<T>>`.
pub(crate) struct MembershipCoreWrap<'a, T>(&'a RefCell<MembershipCore<T>>);

impl<'a, T> MembershipCoreWrap<'a, T> {
    /// Returns the shared owning reference to the tree core.
    #[must_use]
    pub(crate) fn tree_core_opt(&self) -> Option<Rc<TreeCore<T>>> {
        let core = self
            .0
            .try_borrow()
            .expect("[consistency] membership core should never be borrowed nestedly");
        match &*core {
            MembershipCore::Weak { tree_core } => Weak::upgrade(tree_core),
            MembershipCore::Strong { tree_core, .. } => Some(tree_core.clone()),
        }
    }
}

impl<'a, T> From<&'a Membership<T>> for MembershipCoreWrap<'a, T> {
    #[inline]
    fn from(v: &'a Membership<T>) -> Self {
        Self(&v.inner)
    }
}

impl<'a, T> From<&'a WeakMembership<T>> for MembershipCoreWrap<'a, T> {
    #[inline]
    fn from(v: &'a WeakMembership<T>) -> Self {
        Self(&v.inner)
    }
}

/// A reference to the membership of a node, with strong ownership of a tree.
#[derive(Debug)]
pub(crate) struct Membership<T> {
    /// Target membership core.
    pub(crate) inner: Rc<RefCell<MembershipCore<T>>>,
}

impl<T> Drop for Membership<T> {
    fn drop(&mut self) {
        let mut membership_core = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] membership core should never borrowed nestedly");
        // Decrement refcount.
        match &mut *membership_core {
            MembershipCore::Weak { .. } => unreachable!("[validity] `self` has a strong reference"),
            MembershipCore::Strong {
                tree_core,
                tree_refcount,
                ..
            } => {
                // This subtraction never overflows.
                let decremented = NonZeroUsize::new(tree_refcount.get() - 1);
                match decremented {
                    Some(new_count) => *tree_refcount = new_count,
                    None => {
                        let weak_core = Rc::downgrade(tree_core);
                        *membership_core = MembershipCore::Weak {
                            tree_core: weak_core,
                        };
                    }
                }
            }
        };
    }
}

impl<T> Clone for Membership<T> {
    #[inline]
    fn clone(&self) -> Self {
        let mut membership_core = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] membership core should never borrowed nestedly");
        // Increment refcount.
        match &mut *membership_core {
            MembershipCore::Weak { .. } => unreachable!("[validity] `self` has a strong reference"),
            MembershipCore::Strong { tree_refcount, .. } => {
                // `NonZeroUsize::checked_add()` is unstable as of Rust 1.59.
                // See <https://github.com/rust-lang/rust/issues/84186>.
                let incremented = NonZeroUsize::new(tree_refcount.get().wrapping_add(1))
                    .expect("[consistency] the memory cannot have `usize::MAX` references");
                *tree_refcount = incremented;
            }
        }

        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T> Membership<T> {
    /// Returns a reference to the tree core without cloning `Rc`.
    #[must_use]
    fn tree_core_ref(&self) -> Ref<'_, Rc<TreeCore<T>>> {
        let membership_core = self
            .inner
            .try_borrow()
            .expect("[consistency] membership core should never borrowed nestedly");
        Ref::map(membership_core, |membership_core| match membership_core {
            MembershipCore::Weak { .. } => unreachable!("[validity] `self` has a strong reference"),
            MembershipCore::Strong { tree_core, .. } => tree_core,
        })
    }

    /// Creates a weakened membership.
    #[inline]
    #[must_use]
    pub(crate) fn downgrade(&self) -> WeakMembership<T> {
        WeakMembership {
            inner: self.inner.clone(),
        }
    }

    /// Creates a new membership object (and its new core) for the tree.
    #[must_use]
    pub(crate) fn create_new_membership(tree_core: Rc<TreeCore<T>>) -> Self {
        let tree_refcount = NonZeroUsize::new(1).expect("[consistency] 1 is nonzero");
        let membership = MembershipCore::Strong {
            tree_core,
            tree_refcount,
            lock_aggregator: Default::default(),
        };
        Membership {
            inner: Rc::new(RefCell::new(membership)),
        }
    }

    /// Returns `true` if the two memberships refer to the same core data allocation.
    #[inline]
    #[must_use]
    pub(crate) fn ptr_eq_weak(&self, other: &WeakMembership<T>) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }

    /// Returns true if the node belong to the given tree.
    #[inline]
    #[must_use]
    pub(crate) fn belongs_to(&self, tree: &Tree<T>) -> bool {
        Rc::ptr_eq(tree.core(), &*self.tree_core_ref())
    }

    /// Returns true if the given node belong to the same tree.
    #[must_use]
    pub(crate) fn belongs_to_same_tree(&self, other: &Self) -> bool {
        let self_ptr = Rc::as_ptr(&*self.tree_core_ref());
        let other_ptr = Rc::as_ptr(&*other.tree_core_ref());
        self_ptr == other_ptr
    }
}

/// A reference to the membership of a node, without ownership of a tree.
// This type does not have custom `Drop` implementation since it does not affect
// strongness of a reference to the tree core.
#[derive(Debug)]
pub(crate) struct WeakMembership<T> {
    /// Target membership core.
    pub(crate) inner: Rc<RefCell<MembershipCore<T>>>,
}

impl<T> Clone for WeakMembership<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

/// Initialization.
impl<T> WeakMembership<T> {
    /// Creates a new weak membership with null reference to the tree core.
    #[inline]
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(MembershipCore::Weak {
                tree_core: Weak::new(),
            })),
        }
    }

    /// Initialize the weak membership with the given reference to the tree core.
    ///
    /// # Panics
    ///
    /// The referred membership core should not be initialized yet. If not, this
    /// method panics.
    #[must_use]
    pub(crate) fn initialize_membership(self, tree_core: Rc<TreeCore<T>>) -> Membership<T> {
        let mut inner = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] membership core should not yet be borrowed elsewhere");
        match &*inner {
            // Not testing if `weak` is dereferenceable, but testing if the
            // reference is the value created by `Weak::new()`. This condition
            // will be false once the membership is fully initialized.
            // This comparison with `&Weak::new()` is intentional.
            MembershipCore::Weak { tree_core } if Weak::ptr_eq(tree_core, &Weak::new()) => {}
            _ => panic!("[precondition] weak membership should not be initialized twice"),
        }
        debug_assert!(matches!(&*inner, MembershipCore::Weak { .. }));

        // Create a strong reference and set the count to 1.
        let tree_refcount = NonZeroUsize::new(1).expect("[validity] 1 is nonzero");
        *inner = MembershipCore::Strong {
            tree_core,
            tree_refcount,
            lock_aggregator: Default::default(),
        };
        drop(inner);
        Membership { inner: self.inner }
    }

    /// Upgrade the membership to a strong one.
    #[must_use]
    pub(crate) fn upgrade(&self) -> Option<Membership<T>> {
        // Need to update strong refcount.
        let mut membership_core = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] membership core should never borrowed nestedly");
        match &mut *membership_core {
            MembershipCore::Weak { tree_core } => {
                let tree_refcount = NonZeroUsize::new(1).expect("[consistency] 1 is nonzero");
                let tree_core = tree_core.upgrade()?;
                *membership_core = MembershipCore::Strong {
                    tree_core,
                    tree_refcount,
                    lock_aggregator: Default::default(),
                };
            }
            MembershipCore::Strong { tree_refcount, .. } => {
                // `NonZeroUsize::checked_add()` is unstable as of Rust 1.59.
                // See <https://github.com/rust-lang/rust/issues/84186>.
                let incremented = NonZeroUsize::new(tree_refcount.get().wrapping_add(1))
                    .expect("[consistency] the memory cannot have `usize::MAX` references");
                *tree_refcount = incremented;
            }
        }

        Some(Membership {
            inner: self.inner.clone(),
        })
    }

    /// Returns true if the membership refers to the same tree core allocation.
    #[must_use]
    pub(crate) fn ptr_eq_tree_core(&self, other_tree_core: &Rc<TreeCore<T>>) -> bool {
        let membership_core = self
            .inner
            .try_borrow()
            .expect("[consistency] membership core should never borrowed nestedly");
        let ptr = match &*membership_core {
            MembershipCore::Weak { tree_core } => tree_core.as_ptr(),
            MembershipCore::Strong { tree_core, .. } => Rc::as_ptr(tree_core),
        };
        ptr == Rc::as_ptr(other_tree_core)
    }
}

/// Modification.
impl<T> WeakMembership<T> {
    /// Lets the membership refer to the given tree core.
    ///
    /// # Failures
    ///
    /// Fails if the new tree cannot be locked with the currently active tree
    /// hierarchy edit lock.
    pub(crate) fn set_tree_core(&self, new_tree_core: &Rc<TreeCore<T>>) -> Result<(), ()> {
        let mut inner = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] `WeakMembership::inner` should never borrowed nestedly");
        match &mut *inner {
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
}

impl<T> WeakMembership<T> {
    /// Returns the convenience wrapper.
    #[inline]
    #[must_use]
    pub(crate) fn core_wrap(&self) -> MembershipCoreWrap<'_, T> {
        self.into()
    }
}
