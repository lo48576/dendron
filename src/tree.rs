//! Tree.

use core::cell::RefCell;

use alloc::rc::Rc;

use crate::node::IntraTreeLink;
use crate::traverse::DftEvent;

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
}

impl<T> TreeCore<T> {
    /// Creates a new tree core.
    #[must_use]
    pub(crate) fn new_rc(root: IntraTreeLink<T>) -> Rc<Self> {
        Rc::new(Self {
            root: RefCell::new(root),
        })
    }

    /// Returns a link to the root node.
    #[must_use]
    pub(crate) fn root(&self) -> IntraTreeLink<T> {
        self.root
            .try_borrow()
            .expect("[consistency] `TreeCore::root` should not be borrowed nestedly")
            .clone()
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
