//! Internals of a node.

use core::cell::{BorrowError, BorrowMutError, Cell, Ref, RefCell, RefMut};
use core::iter;
use core::mem;

use alloc::rc::{Rc, Weak};

use crate::membership::WeakMembership;
use crate::traverse::DftEvent;
use crate::tree::TreeCore;

/// Internal node data.
struct NodeCore<T> {
    /// Data associated to the node.
    data: RefCell<T>,
    /// Neighbors.
    neighbors: RefCell<Neighbors<T>>,
    /// Membership to a tree.
    membership: WeakMembership<T>,
    /// The number of children.
    ///
    /// Note that this can be transiently inconsistent during editing node.
    /// This inconsistency should not be observed from outside of the crate.
    num_children: Cell<usize>,
}

/// A collection of links to neighbor nodes.
struct Neighbors<T> {
    /// Parent.
    // Not using `Option<IntraTreeLinkWeak<T>>` here because
    // `IntraTreeLinkWeak<T>` itself acts as a weak and optional reference.
    parent: IntraTreeLinkWeak<T>,
    /// First child.
    first_child: Option<IntraTreeLink<T>>,
    /// Next sibling.
    next_sibling: Option<IntraTreeLink<T>>,
    /// Previous sibling.
    ///
    /// This field refers to the last sibling if the node is the first sibling.
    /// Otherwise, this field refers to the previous sibling.
    ///
    /// Note that the weak link must always refer some node once the node is
    /// accessible outside the node. In other words, this is allowed to be
    /// dangling reference only during the node itself is being constructed.
    prev_sibling_cyclic: IntraTreeLinkWeak<T>,
}

/// Node builder.
pub(super) struct NodeBuilder<T> {
    /// Data associated to the node.
    pub(super) data: T,
    /// Parent.
    pub(super) parent: IntraTreeLinkWeak<T>,
    /// First child.
    pub(super) first_child: Option<IntraTreeLink<T>>,
    /// Next sibling.
    pub(super) next_sibling: Option<IntraTreeLink<T>>,
    /// Previous sibling.
    pub(super) prev_sibling_cyclic: IntraTreeLinkWeak<T>,
    /// Membership to a tree.
    pub(super) membership: WeakMembership<T>,
    /// Number of children.
    pub(super) num_children: usize,
}

impl<T> NodeBuilder<T> {
    /// Builds a node core.
    #[must_use]
    fn build_core_rc(self) -> Rc<NodeCore<T>> {
        Rc::new(NodeCore {
            data: RefCell::new(self.data),
            neighbors: RefCell::new(Neighbors {
                parent: self.parent,
                first_child: self.first_child,
                next_sibling: self.next_sibling,
                prev_sibling_cyclic: self.prev_sibling_cyclic,
            }),
            membership: self.membership,
            num_children: Cell::new(self.num_children),
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
    pub(super) fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.core, &other.core)
    }

    /// Creates a weakened link.
    #[inline]
    #[must_use]
    pub(super) fn downgrade(&self) -> IntraTreeLinkWeak<T> {
        IntraTreeLinkWeak {
            core: Rc::downgrade(&self.core),
        }
    }

    /// Returns true if the node belongs to the tree with the given tree core.
    #[inline]
    #[must_use]
    pub(super) fn belongs_to_tree_core_rc(&self, tree_core: &Rc<TreeCore<T>>) -> bool {
        self.membership().ptr_eq_tree_core(tree_core)
    }

    /// Returns the depth-first traverser for the subtree.
    #[inline]
    #[must_use]
    pub(super) fn depth_first_traverse(&self) -> DepthFirstLinkTraverser<'_, T> {
        DepthFirstLinkTraverser::with_start(self)
    }
}

/// Getters.
impl<T> IntraTreeLink<T> {
    /// Returns the tree core.
    #[must_use]
    pub(super) fn tree_core(&self) -> Rc<TreeCore<T>> {
        self.membership()
            .core_wrap()
            .tree_core_opt()
            .expect("[validity] the tree must be alive if a node is alive")
    }

    /// Returns the neighbors.
    #[must_use]
    fn neighbors(&self) -> Ref<'_, Neighbors<T>> {
        self.core
            .neighbors
            .try_borrow()
            .expect("[consistency] `NodeCore::neighbors` should not be borrowed nestedly")
    }

    /// Returns the mutable neighbors.
    #[must_use]
    fn neighbors_mut(&self) -> RefMut<'_, Neighbors<T>> {
        self.core
            .neighbors
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::neighbors` should not be borrowed nestedly")
    }

    /// Returns a link to the parent node.
    #[inline]
    #[must_use]
    pub(crate) fn parent_link(&self) -> Option<Self> {
        self.neighbors().parent.upgrade()
    }

    /// Returns true if the node has a parent.
    #[inline]
    pub(crate) fn is_root(&self) -> bool {
        self.neighbors().parent.is_unavailable()
    }

    /// Returns a link to the cyclic previous sibling.
    #[inline]
    #[must_use]
    pub(crate) fn prev_sibling_cyclic_link(&self) -> Self {
        self.neighbors().prev_sibling_cyclic.upgrade().expect(
            "[validity] `NodeCore::prev_sibling_cyclic` must never dangle after constructed",
        )
    }

    /// Returns a weak link to the cyclic previous sibling.
    #[inline]
    #[must_use]
    pub(crate) fn prev_sibling_cyclic_link_weak(&self) -> IntraTreeLinkWeak<T> {
        self.neighbors().prev_sibling_cyclic.clone()
    }

    /// Returns a link to the previous sibling.
    #[must_use]
    pub(crate) fn prev_sibling_link(&self) -> Option<Self> {
        let prev_sibling_cyclic = self.prev_sibling_cyclic_link();

        let is_next_of_prev_available = prev_sibling_cyclic.neighbors().next_sibling.is_some();
        if is_next_of_prev_available {
            // `prev_sibling_cyclic` is not the last sibling.
            Some(prev_sibling_cyclic)
        } else {
            // `prev_sibling_cyclic` is not the previous sibling, but the last sibling.
            None
        }
    }

    /// Returns true if the previous sibling exists.
    #[inline]
    #[must_use]
    pub(super) fn has_prev_sibling(&self) -> bool {
        let prev_sibling_cyclic = self.prev_sibling_cyclic_link();
        let result = prev_sibling_cyclic.neighbors().next_sibling.is_some();
        result
    }

    /// Returns a link to the next sibling.
    #[inline]
    #[must_use]
    pub(crate) fn next_sibling_link(&self) -> Option<Self> {
        self.neighbors().next_sibling.clone()
    }

    /// Returns true if the next sibling exists.
    #[inline]
    #[must_use]
    pub(super) fn has_next_sibling(&self) -> bool {
        self.neighbors().next_sibling.is_some()
    }

    /// Returns a link to the first child node.
    #[inline]
    #[must_use]
    pub(crate) fn first_child_link(&self) -> Option<Self> {
        self.neighbors().first_child.clone()
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

    /// Returns true if the node has any children.
    #[must_use]
    pub(super) fn has_children(&self) -> bool {
        self.core.num_children.get() != 0
    }

    /// Returns the membership.
    #[inline]
    #[must_use]
    pub(crate) fn membership(&self) -> &WeakMembership<T> {
        &self.core.membership
    }

    /// Returns true if the current node is the first sibling.
    #[inline]
    #[must_use]
    pub(crate) fn is_first_sibling(&self) -> bool {
        self.prev_sibling_cyclic_link().is_last_sibling()
    }

    /// Returns true if the current node is the last sibling.
    #[must_use]
    pub(crate) fn is_last_sibling(&self) -> bool {
        self.neighbors().next_sibling.is_none()
    }

    /// Returns the number of children.
    ///
    /// Note that this is O(N) operation.
    #[must_use]
    pub(super) fn count_children(&self) -> usize {
        iter::successors(self.first_child_link(), |link| link.next_sibling_link()).count()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    #[must_use]
    pub(super) fn count_preceding_siblings(&self) -> usize {
        iter::successors(self.prev_sibling_link(), |link| link.prev_sibling_link()).count()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    #[must_use]
    pub(super) fn count_following_siblings(&self) -> usize {
        iter::successors(self.next_sibling_link(), |link| link.next_sibling_link()).count()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    #[must_use]
    pub(super) fn count_ancestors(&self) -> usize {
        iter::successors(self.parent_link(), |link| link.parent_link()).count()
    }
}

/// Setters.
impl<T> IntraTreeLink<T> {
    /// Sets the `parent` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_parent(&self, link: IntraTreeLinkWeak<T>) -> IntraTreeLinkWeak<T> {
        let mut parent = RefMut::map(self.neighbors_mut(), |neighbors| &mut neighbors.parent);
        mem::replace(&mut *parent, link)
    }

    /// Sets the `prev_sibling_cyclic` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_prev_sibling_cyclic(
        &self,
        link: IntraTreeLinkWeak<T>,
    ) -> IntraTreeLinkWeak<T> {
        let mut prev_sibling_cyclic = RefMut::map(self.neighbors_mut(), |neighbors| {
            &mut neighbors.prev_sibling_cyclic
        });
        mem::replace(&mut *prev_sibling_cyclic, link)
    }

    /// Sets the `next_sibling` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_next_sibling(
        &self,
        link: Option<IntraTreeLink<T>>,
    ) -> Option<IntraTreeLink<T>> {
        let mut first_child = RefMut::map(self.neighbors_mut(), |neighbors| {
            &mut neighbors.next_sibling
        });
        mem::replace(&mut *first_child, link)
    }

    /// Sets the `first_child` field and returns the old value.
    ///
    /// Note that this does not take care of consistency.
    pub(crate) fn replace_first_child(
        &self,
        link: Option<IntraTreeLink<T>>,
    ) -> Option<IntraTreeLink<T>> {
        let mut first_child =
            RefMut::map(self.neighbors_mut(), |neighbors| &mut neighbors.first_child);
        mem::replace(&mut *first_child, link)
    }

    /// Connects adjacent siblings bidirectionally.
    #[inline]
    pub(crate) fn connect_adjacent_siblings(prev: &IntraTreeLink<T>, next: IntraTreeLink<T>) {
        next.replace_prev_sibling_cyclic(prev.downgrade());
        prev.replace_next_sibling(Some(next));
    }

    /// Returns a reference to the cached number of children.
    #[inline]
    pub(super) fn num_children_cell(&self) -> &Cell<usize> {
        &self.core.num_children
    }

    /// Adds the given number to the `num_children` cache.
    #[inline]
    pub(super) fn num_children_add(&self, v: usize) {
        let old = self.core.num_children.get();
        self.core.num_children.set(old + v);
    }

    /// Subtracts the given number from the `num_children` cache.
    #[inline]
    pub(super) fn num_children_sub(&self, v: usize) {
        let old = self.core.num_children.get();
        self.core.num_children.set(old - v);
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

/// Comparison.
impl<T> IntraTreeLink<T> {
    /// Compares two subtrees.
    ///
    /// Returns `Ok(true)` if the two subtree are equal, even if they are stored
    /// in different allocation.
    ///
    /// # Failures
    ///
    /// May return `Err(_)` if associated data of some nodes are already
    /// borrowed exclusively (i.e. mutably).
    pub(super) fn try_eq<U>(&self, other: &IntraTreeLink<U>) -> Result<bool, BorrowError>
    where
        T: PartialEq<U>,
    {
        // NOTE: `Iterator::eq_by` is not yet stabilized (as of Rust 1.60).
        let mut self_iter = self.depth_first_traverse();
        let mut other_iter = other.depth_first_traverse();
        loop {
            match (self_iter.next(), other_iter.next()) {
                (None, None) => return Ok(true),
                (Some(l), Some(r)) => match (l, r) {
                    (DftEvent::Open(l), DftEvent::Open(r)) => {
                        if *l.try_borrow_data()? != *r.try_borrow_data()? {
                            return Ok(false);
                        }
                    }
                    (DftEvent::Close(_), DftEvent::Close(_)) => {}
                    _ => return Ok(false),
                },
                _ => return Ok(false),
            }
        }
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

/// Depth-first traverser for intra-tree links.
pub(super) struct DepthFirstLinkTraverser<'a, T> {
    /// Next event to emit, and the starting node.
    // Using `&'a IntraTreeLink<T>` to guarantee the subtree lives longer
    // than the traverser.
    next: Option<(DftEvent<IntraTreeLink<T>>, &'a IntraTreeLink<T>)>,
}

impl<T> Clone for DepthFirstLinkTraverser<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            next: self.next.clone(),
        }
    }
}

impl<'a, T> DepthFirstLinkTraverser<'a, T> {
    /// Creates a traverser from the opening of the given node.
    #[inline]
    #[must_use]
    fn with_start(next: &'a IntraTreeLink<T>) -> Self {
        Self {
            next: Some((DftEvent::Open(next.clone()), next)),
        }
    }
}

impl<T> Iterator for DepthFirstLinkTraverser<'_, T> {
    type Item = DftEvent<IntraTreeLink<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (next_ev, start) = self.next.take()?;
        if let DftEvent::Close(link) = &next_ev {
            if IntraTreeLink::ptr_eq(link, start) {
                return None;
            }
        }
        self.next = next_ev.next().map(|next_of_next| (next_of_next, start));
        Some(next_ev)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.next.as_ref() {
            Some((DftEvent::Open(_), _)) => (2, None),
            Some((DftEvent::Close(next), start)) => {
                if IntraTreeLink::ptr_eq(next, start) {
                    // The next event is the last event.
                    (1, Some(1))
                } else {
                    (1, None)
                }
            }
            None => (0, Some(0)),
        }
    }
}

impl<T> core::iter::FusedIterator for DepthFirstLinkTraverser<'_, T> {}

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

impl<T> IntraTreeLinkWeak<T> {
    /// Creates a strong intra node link from the weak one.
    #[inline]
    #[must_use]
    pub(super) fn upgrade(&self) -> Option<IntraTreeLink<T>> {
        Weak::upgrade(&self.core).map(|core| IntraTreeLink { core })
    }

    /// Returns true if the link target is unavailable anymore (i.e. the link refers no live node).
    #[inline]
    #[must_use]
    fn is_unavailable(&self) -> bool {
        self.core.strong_count() == 0
    }
}
