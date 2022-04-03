//! Internals of a node.

use core::cell::{BorrowError, BorrowMutError, Ref, RefCell, RefMut};
use core::fmt;
use core::mem;

use alloc::rc::{Rc, Weak};

use crate::affiliation::WeakAffiliationRef;
use crate::traverse::DftEvent;

/// Internal node data.
#[derive(Debug)]
struct NodeCore<T> {
    /// Data associated to the node.
    data: RefCell<T>,
    /// Parent.
    // Not using `Option<IntraTreeLinkWeak<T>>` here because
    // `IntraTreeLinkWeak<T>` itself acts as a weak and optional reference.
    parent: RefCell<IntraTreeLinkWeak<T>>,
    /// First child.
    first_child: RefCell<Option<IntraTreeLink<T>>>,
    /// Next sibling.
    next_sibling: RefCell<Option<IntraTreeLink<T>>>,
    /// Previous sibling.
    ///
    /// This field refers to the last sibling if the node is the first sibling.
    /// Otherwise, this field refers to the previous sibling.
    ///
    /// Note that the weak link must always refer some node once the node is
    /// accessible outside the node. In other words, this is allowed to be
    /// dangling reference only during the node itself is being constructed.
    prev_sibling_cyclic: RefCell<IntraTreeLinkWeak<T>>,
    /// Affiliation to a tree.
    affiliation: WeakAffiliationRef<T>,
}

/// Node builder.
pub(crate) struct NodeBuilder<T> {
    /// Data associated to the node.
    pub(crate) data: T,
    /// Parent.
    pub(crate) parent: IntraTreeLinkWeak<T>,
    /// First child.
    pub(crate) first_child: Option<IntraTreeLink<T>>,
    /// Next sibling.
    pub(crate) next_sibling: Option<IntraTreeLink<T>>,
    /// Previous sibling.
    pub(crate) prev_sibling_cyclic: IntraTreeLinkWeak<T>,
    /// Affiliation to a tree.
    pub(crate) affiliation: WeakAffiliationRef<T>,
}

impl<T> NodeBuilder<T> {
    /// Builds a node core.
    #[must_use]
    fn build_core_rc(self) -> Rc<NodeCore<T>> {
        Rc::new(NodeCore {
            data: RefCell::new(self.data),
            parent: RefCell::new(self.parent),
            first_child: RefCell::new(self.first_child),
            next_sibling: RefCell::new(self.next_sibling),
            prev_sibling_cyclic: RefCell::new(self.prev_sibling_cyclic),
            affiliation: self.affiliation,
        })
    }
    /// Builds a node core.
    #[inline]
    #[must_use]
    pub fn build_link(self) -> IntraTreeLink<T> {
        let core = self.build_core_rc();
        IntraTreeLink { core }
    }
}

/// An intra-tree owning reference to a node.
#[derive(Debug)]
pub(crate) struct IntraTreeLink<T> {
    /// Target node core.
    core: Rc<NodeCore<T>>,
}

impl<T> Clone for IntraTreeLink<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            core: self.core.clone(),
        }
    }
}

impl<T> IntraTreeLink<T> {
    /// Returns `true` if the two `Node`s point to the same allocation.
    #[inline]
    #[must_use]
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.core, &other.core)
    }

    /// Creates a weakened link.
    #[inline]
    #[must_use]
    pub(crate) fn downgrade(&self) -> IntraTreeLinkWeak<T> {
        IntraTreeLinkWeak {
            core: Rc::downgrade(&self.core),
        }
    }
}

/// Getters.
impl<T> IntraTreeLink<T> {
    /// Returns a link to the parent node.
    #[must_use]
    pub(crate) fn parent_link(&self) -> Option<Self> {
        self.core
            .parent
            .try_borrow()
            .expect("[consistency] `NodeCore::parent` should not be borrowed nestedly")
            .upgrade()
    }

    /// Returns true if the node has a parent.
    pub(crate) fn is_root(&self) -> bool {
        self.core
            .parent
            .try_borrow()
            .expect("[consistency] `NodeCore::parent` should not be borrowed nestedly")
            .is_dangling()
    }

    /// Returns a link to the cyclic previous sibling.
    #[must_use]
    pub(crate) fn prev_sibling_cyclic_link(&self) -> Self {
        self.core
            .prev_sibling_cyclic
            .try_borrow()
            .expect("[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly")
            .upgrade()
            .expect(
                "[validity] `NodeCore::prev_sibling_cyclic` must never dangle after constructed",
            )
    }

    /// Returns a weak link to the cyclic previous sibling.
    #[must_use]
    pub(crate) fn prev_sibling_cyclic_link_weak(&self) -> IntraTreeLinkWeak<T> {
        self.core
            .prev_sibling_cyclic
            .try_borrow()
            .expect("[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly")
            .clone()
    }

    /// Returns a link to the previous sibling.
    #[must_use]
    pub(crate) fn prev_sibling_link(&self) -> Option<Self> {
        let prev_sibling_cyclic = self.prev_sibling_cyclic_link();

        let is_next_of_prev_available = prev_sibling_cyclic
            .core
            .next_sibling
            .try_borrow()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly")
            .is_some();
        if is_next_of_prev_available {
            // `prev_sibling_cyclic` is not the last sibling.
            Some(prev_sibling_cyclic)
        } else {
            // `prev_sibling_cyclic` is not the previous sibling, but the last sibling.
            None
        }
    }

    /// Returns a link to the next sibling.
    #[must_use]
    pub(crate) fn next_sibling_link(&self) -> Option<Self> {
        self.core
            .next_sibling
            .try_borrow()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly")
            .clone()
    }

    /// Returns a link to the first child node.
    #[must_use]
    pub(crate) fn first_child_link(&self) -> Option<Self> {
        self.core
            .first_child
            .try_borrow()
            .expect("[consistency] `NodeCore::first_child` should not be borrowed nestedly")
            .clone()
    }

    /// Returns a link to the last child node.
    #[must_use]
    pub(crate) fn last_child_link(&self) -> Option<Self> {
        self.first_child_link()
            .map(|first_child| first_child.prev_sibling_cyclic_link())
    }

    /// Returns a link to the last child node.
    #[must_use]
    pub(crate) fn last_child_link_weak(&self) -> Option<IntraTreeLinkWeak<T>> {
        self.first_child_link()
            .map(|first_child| first_child.prev_sibling_cyclic_link_weak())
    }

    /// Returns links to the first and the last child nodes.
    #[must_use]
    pub(crate) fn first_last_child_link(&self) -> Option<(Self, Self)> {
        let first_child = self.first_child_link()?;
        let last_child = first_child.prev_sibling_cyclic_link();
        Some((first_child, last_child))
    }

    /// Returns the affiliation reference.
    #[inline]
    #[must_use]
    pub(crate) fn affiliation(&self) -> &WeakAffiliationRef<T> {
        &self.core.affiliation
    }

    /// Returns true if the current node is the first sibling.
    #[must_use]
    pub(crate) fn is_first_sibling(&self) -> bool {
        self.prev_sibling_cyclic_link().is_last_sibling()
    }

    /// Returns true if the current node is the last sibling.
    #[must_use]
    pub(crate) fn is_last_sibling(&self) -> bool {
        self.core
            .next_sibling
            .try_borrow()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly")
            .is_none()
    }
}

/// Setters.
impl<T> IntraTreeLink<T> {
    /// Sets the `parent` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_parent(&self, link: IntraTreeLinkWeak<T>) -> IntraTreeLinkWeak<T> {
        let mut parent = self
            .core
            .parent
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::parent` should not be borrowed nestedly");
        mem::replace(&mut *parent, link)
    }

    /// Sets the `prev_sibling_cyclic` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_prev_sibling_cyclic(
        &self,
        link: IntraTreeLinkWeak<T>,
    ) -> IntraTreeLinkWeak<T> {
        let mut prev_sibling_cyclic = self.core.prev_sibling_cyclic.try_borrow_mut().expect(
            "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
        );
        mem::replace(&mut *prev_sibling_cyclic, link)
    }

    /// Sets the `next_sibling` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_next_sibling(
        &self,
        link: Option<IntraTreeLink<T>>,
    ) -> Option<IntraTreeLink<T>> {
        let mut first_child = self
            .core
            .next_sibling
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly");
        mem::replace(&mut *first_child, link)
    }

    /// Sets the `first_child` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_first_child(
        &self,
        link: Option<IntraTreeLink<T>>,
    ) -> Option<IntraTreeLink<T>> {
        let mut first_child = self
            .core
            .first_child
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::first_child` should not be borrowed nestedly");
        mem::replace(&mut *first_child, link)
    }

    /// Connects adjacent siblings bidirectionally.
    pub(crate) fn connect_adjacent_siblings(prev: &IntraTreeLink<T>, next: IntraTreeLink<T>) {
        next.replace_prev_sibling_cyclic(prev.downgrade());
        prev.replace_next_sibling(Some(next));
    }
}

/// Data accessors.
impl<T> IntraTreeLink<T> {
    /// Returns a reference to the data associated to the node.
    #[inline]
    pub(crate) fn try_borrow_data(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.core.data.try_borrow()
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub(crate) fn borrow_data(&self) -> Ref<'_, T> {
        self.core.data.borrow()
    }

    /// Returns a mutable reference to the data associated to the node.
    #[inline]
    pub(crate) fn try_borrow_data_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.core.data.try_borrow_mut()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub(crate) fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.core.data.borrow_mut()
    }
}

impl<T> DftEvent<IntraTreeLink<T>> {
    /// Returns the next (forward direction) event.
    ///
    /// This method is guaranteed to access only `first_child`, `next_sibling`,
    /// and `parent` fields, and once for each of them, so this can be safely
    /// used if a node is in an inconsistent state of some kind.
    ///
    /// This method is also guaranteed to never access the nodes once they are
    /// `Close`d.
    #[must_use]
    pub(crate) fn next(&self) -> Option<Self> {
        let next = match self {
            Self::Open(current) => {
                // Dive into the first child if available, or otherwise leave the node.
                match current.first_child_link() {
                    Some(child) => Self::Open(child),
                    None => Self::Close(current.clone()),
                }
            }
            Self::Close(current) => {
                // Dive into the next sibling if available, or leave the parent.
                match current.next_sibling_link() {
                    Some(next_sib) => Self::Open(next_sib),
                    None => Self::Close(current.parent_link()?),
                }
            }
        };
        Some(next)
    }
}

/// An intra-tree non-owning reference to a node.
// Note that this value itself acts as optional reference since it has
// `alloc::rc::Weak` value.
pub(crate) struct IntraTreeLinkWeak<T> {
    /// Target node core.
    core: Weak<NodeCore<T>>,
}

impl<T> Clone for IntraTreeLinkWeak<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            core: self.core.clone(),
        }
    }
}

impl<T> Default for IntraTreeLinkWeak<T> {
    #[inline]
    fn default() -> Self {
        Self {
            core: Default::default(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for IntraTreeLinkWeak<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntraTreeLinkWeak").finish()
    }
}

impl<T> IntraTreeLinkWeak<T> {
    /// Creates a strong intra node link from the weak one.
    #[must_use]
    fn upgrade(&self) -> Option<IntraTreeLink<T>> {
        Weak::upgrade(&self.core).map(|core| IntraTreeLink { core })
    }

    /// Returns true if the link is dangling (i.e. no node is referred).
    #[inline]
    #[must_use]
    fn is_dangling(&self) -> bool {
        Weak::ptr_eq(&self.core, &Weak::new())
    }
}
