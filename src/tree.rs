//! Tree.

mod lock;

use core::cell::RefCell;

use alloc::rc::Rc;

use crate::node::{IntraTreeLink, Node};
use crate::traverse::DftEvent;

pub(crate) use self::lock::LockAggregatorForNode;
use self::lock::StructureLockManager;
pub use self::lock::{
    StructureEditGrant, StructureEditGrantError, StructureEditProhibition,
    StructureEditProhibitionError,
};

/// A core data of a tree.
///
/// This also represents an ownership of a tree. Every tree has just one
/// corresponding `TreeCore`.
///
/// A value of this type is shared among nodes in the tree, so this will be
/// referred as `Rc<RefCell<TreeCore<T>>>` or `Weak<RefCell<TreeCore<T>>>`.
#[derive(Debug)]
pub(crate) struct TreeCore<T> {
    /// Root node.
    root: RefCell<IntraTreeLink<T>>,
    /// Structure lock manager.
    lock_manager: StructureLockManager,
}

impl<T> TreeCore<T> {
    /// Creates a new tree core.
    #[must_use]
    pub(crate) fn new_rc(root: IntraTreeLink<T>) -> Rc<Self> {
        Rc::new(Self {
            root: RefCell::new(root),
            lock_manager: Default::default(),
        })
    }

    /// Returns a link to the root node.
    #[must_use]
    pub(crate) fn root_link(&self) -> IntraTreeLink<T> {
        self.root
            .try_borrow()
            .expect("[consistency] `TreeCore::root` should not be borrowed nestedly")
            .clone()
    }

    /// Transfers a lock.
    ///
    /// # Failures
    ///
    /// Fails if the tree `dest` cannot be locked with the currently active
    /// tree structure edit lock for `self`.
    // Intended only for use by `membership` module.
    pub(crate) fn transfer_single_lock_to(
        self: &Rc<TreeCore<T>>,
        dest: &Rc<TreeCore<T>>,
    ) -> Result<(), ()> {
        self.lock_manager
            .transfer_single_lock_to(&dest.lock_manager)
    }
}

// This drop prevents stack overflow on drop of very wide or very deep tree.
impl<T> Drop for TreeCore<T> {
    fn drop(&mut self) {
        // This panic should never happen (unless there are a bug).
        let root_link = self
            .root
            .try_borrow()
            .expect("[validity] `TreeCore` is being accessed exclusively")
            .clone();
        let mut next = Some(DftEvent::Open(root_link));
        while let Some(current) = next.take() {
            next = current.next();
            let close_link = match current {
                DftEvent::Open(_) => continue,
                DftEvent::Close(v) => v,
            };

            // Drop the leaf node.
            // It is safe to leave `prev_sibling_cyclic` inconsistent, since
            // `DftEvent<IntraTreeLink<T>>` is guaranteed to use only
            // `first_child`, `next_sibling`, and `parent` fields, and use once
            // respectively.
            if let Some(parent_link) = close_link.parent_link() {
                // This panic should never happen (unless there are a bug).
                let next_sibling = close_link.replace_next_sibling(None);
                // This panic should never happen (unless there are a bug).
                parent_link.replace_first_child(next_sibling);
            }
            drop(close_link);
        }
    }
}

/// A reference to the tree.
#[derive(Debug)]
pub struct Tree<T> {
    /// A reference to the tree core.
    core: Rc<TreeCore<T>>,
}

impl<T> Tree<T> {
    /// Creates a new `Tree` from the given `Rc` to the core tree.
    #[inline]
    #[must_use]
    pub(crate) fn from_core_rc(core: Rc<TreeCore<T>>) -> Self {
        Self { core }
    }

    /// Returns the root node.
    #[inline]
    #[must_use]
    pub fn root(&self) -> Node<T> {
        let root_link = self.core.root_link();
        let membership = root_link
            .membership()
            .upgrade()
            .expect("[validity] the root node must have valid membership since the tree is alive");

        Node::with_link_and_membership(root_link, membership)
    }

    /// Prohibits the tree structure edit.
    #[inline]
    pub fn prohibit_structure_edit(
        &self,
    ) -> Result<StructureEditProhibition<T>, StructureEditProhibitionError> {
        StructureEditProhibition::new(&self.core)
    }

    /// Grants the tree structure edit.
    #[inline]
    pub fn grant_structure_edit(&self) -> Result<StructureEditGrant<T>, StructureEditGrantError> {
        StructureEditGrant::new(&self.core)
    }
}
