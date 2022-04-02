//! Affiliation of nodes to trees.

use core::cell::RefCell;
use core::fmt;
use core::num::NonZeroUsize;

use alloc::rc::{Rc, Weak};

use crate::tree::TreeCore;

/// An affiliation of a node to a tree.
///
/// Note that nodes may change its affiliation to another tree. In this case,
/// affiliation should also be changed for all referring `Node`s, so this will
/// be usually referred as `Rc<RefCell<Affiliation<T>>>` (not `Weak` reference).
enum Affiliation<T> {
    /// Non-owning reference to the tree core.
    ///
    /// If there are no `Node<T>`s for the node, the affiliation will stay in
    /// this state.
    Weak(Weak<TreeCore<T>>),
    /// Shared owning reference to the tree core, and strong refcounts.
    ///
    /// Strong references can only be held by `Node<T>`.
    Strong(Rc<TreeCore<T>>, NonZeroUsize),
}

impl<T: fmt::Debug> fmt::Debug for Affiliation<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Weak(_) => write!(f, "Weak(TreeCoreWeakRef)"),
            Self::Strong(_, count) => write!(f, "Strong(TreeCoreRef, {count})"),
        }
    }
}

/// A reference to the affiliation of a node, with strong ownership of a tree.
#[derive(Debug)]
pub(crate) struct StrongAffiliationRef<T> {
    /// Target affiliation.
    inner: Rc<RefCell<Affiliation<T>>>,
}

impl<T> Drop for StrongAffiliationRef<T> {
    fn drop(&mut self) {
        let mut affiliation = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] `StrongAffiliationRef::inner` should never borrowed nestedly");
        // Decrement refcount.
        match &mut *affiliation {
            Affiliation::Weak(_) => unreachable!("[validity] `self` has strong reference"),
            Affiliation::Strong(core, count) => {
                // This subtraction never overflows.
                let decremented = NonZeroUsize::new(count.get() - 1);
                match decremented {
                    Some(new_count) => *count = new_count,
                    None => {
                        let weak_core = Rc::downgrade(core);
                        *affiliation = Affiliation::Weak(weak_core);
                    }
                }
            }
        };
    }
}

impl<T> Clone for StrongAffiliationRef<T> {
    #[inline]
    fn clone(&self) -> Self {
        let mut affiliation = self
            .inner
            .try_borrow_mut()
            .expect("[consistency] `StrongAffiliationRef::inner` should never borrowed nestedly");
        // Increment refcount.
        match &mut *affiliation {
            Affiliation::Weak(_) => unreachable!("[validity] `self` has strong reference"),
            Affiliation::Strong(_, count) => {
                // `NonZeroUsize::checked_add()` is unstable as of Rust 1.59.
                // See <https://github.com/rust-lang/rust/issues/84186>.
                let incremented = NonZeroUsize::new(count.get().wrapping_add(1))
                    .expect("[consistency] the memory cannot have `usize::MAX` references");
                *count = incremented;
            }
        }

        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T> StrongAffiliationRef<T> {
    /// Returns a reference to the tree core.
    #[inline]
    #[must_use]
    pub(crate) fn tree_core(&self) -> Rc<TreeCore<T>> {
        let affiliation = self
            .inner
            .try_borrow()
            .expect("[consistency] affiliation should never borrowed nestedly");
        match &*affiliation {
            Affiliation::Weak(_) => unreachable!("[validity] `self` has strong reference"),
            Affiliation::Strong(core, _) => core.clone(),
        }
    }

    /// Creates a weakened reference to the tree core.
    #[inline]
    #[must_use]
    pub(crate) fn downgrade(&self) -> WeakAffiliationRef<T> {
        WeakAffiliationRef {
            inner: self.inner.clone(),
        }
    }

    /// Creates a new affiliation object for the tree.
    #[must_use]
    pub(crate) fn create_new_affiliation(tree_core: Rc<TreeCore<T>>) -> Self {
        let count = NonZeroUsize::new(1).expect("[consistency] 1 is nonzero");
        let affiliation = Affiliation::Strong(tree_core, count);
        StrongAffiliationRef {
            inner: Rc::new(RefCell::new(affiliation)),
        }
    }

    /// Returns `true` if the two affiliation references point to the same allocation.
    #[inline]
    #[must_use]
    pub(crate) fn ptr_eq_weak(&self, other: &WeakAffiliationRef<T>) -> bool {
        Rc::ptr_eq(&self.inner, &other.inner)
    }
}

/// A reference to the affiliation of a node, without ownership of a tree.
// This type does not have custom `Drop` implementation.
#[derive(Debug)]
pub(crate) struct WeakAffiliationRef<T> {
    /// Target affiliation.
    inner: Rc<RefCell<Affiliation<T>>>,
}

impl<T> Clone for WeakAffiliationRef<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

/// Initialization.
impl<T> WeakAffiliationRef<T> {
    /// Creates a new affiliation with null reference to the tree core.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(Affiliation::Weak(Weak::new()))),
        }
    }

    /// Initialize the affiliation with the given reference to the tree core.
    ///
    /// # Panics
    ///
    /// The referred affiliation must not be initialized yet. If not, this
    /// method panics.
    #[must_use]
    pub(crate) fn initialize_affiliation(
        self,
        tree_core: Rc<TreeCore<T>>,
    ) -> StrongAffiliationRef<T> {
        let mut inner = self
            .inner
            .try_borrow_mut()
            .expect("[precondition] affiliation must not yet be borrowed elsewhere");
        match &*inner {
            Affiliation::Weak(weak) if Weak::ptr_eq(weak, &Weak::new()) => {}
            _ => panic!("[precondition] affiliation should not be initialized twice"),
        }
        debug_assert!(matches!(&*inner, Affiliation::Weak(_)));

        // Create a strong reference and set the count to 1.
        let count = NonZeroUsize::new(1).expect("[consistency] 1 is nonzero");
        *inner = Affiliation::Strong(tree_core, count);
        drop(inner);
        StrongAffiliationRef { inner: self.inner }
    }
}

/// Modification.
impl<T> WeakAffiliationRef<T> {
    /// Lets the affiliation refer to the given tree core.
    pub(crate) fn set_tree_core(&self, tree_core: &Rc<TreeCore<T>>) {
        let mut inner = self
            .inner
            .try_borrow_mut()
            .expect("[precondition] affiliation must not yet be borrowed elsewhere");
        match &mut *inner {
            Affiliation::Weak(weak) => *weak = Rc::downgrade(tree_core),
            Affiliation::Strong(rc, _) => *rc = tree_core.clone(),
        }
    }
}
