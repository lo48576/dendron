//! Tree and nodes.

use core::cell::{BorrowError, BorrowMutError, Ref, RefCell, RefMut};
use core::fmt;

use alloc::rc::{Rc, Weak};

use crate::affiliation::{StrongAffiliationRef, WeakAffiliationRef};
use crate::traverse::{self, DftEvent};
use crate::{AdoptAs, StructureError};

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
    /// Returns a link to the root node.
    fn root(&self) -> IntraTreeLink<T> {
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
                let next_sibling = close_link
                    .core
                    .next_sibling
                    .try_borrow_mut()
                    .expect("[validity] the tree is being accessed exclusively")
                    .take();
                // This panic should never happen (unless there are a bug).
                *parent_link
                    .core
                    .first_child
                    .try_borrow_mut()
                    .expect("[validity] the tree is being accessed exclusively") = next_sibling;
            }
            drop(close_link);
        }
    }
}

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

/// An intra-tree owning reference to a node.
#[derive(Debug)]
struct IntraTreeLink<T> {
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
    fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.core, &other.core)
    }

    /// Creates a weakened link.
    #[inline]
    #[must_use]
    fn downgrade(&self) -> IntraTreeLinkWeak<T> {
        IntraTreeLinkWeak {
            core: Rc::downgrade(&self.core),
        }
    }
}

impl<T> IntraTreeLink<T> {
    /// Returns a link to the parent node.
    #[must_use]
    pub fn parent_link(&self) -> Option<Self> {
        self.core
            .parent
            .try_borrow()
            .expect("[consistency] `NodeCore::parent` should not be borrowed nestedly")
            .upgrade()
    }

    /// Returns a link to the cyclic previous sibling.
    #[must_use]
    fn prev_sibling_cyclic_link(&self) -> Self {
        self.core
            .prev_sibling_cyclic
            .try_borrow()
            .expect("[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly")
            .upgrade()
            .expect(
                "[validity] `NodeCore::prev_sibling_cyclic` must never dangle after constructed",
            )
    }

    /// Returns a link to the previous sibling.
    #[must_use]
    fn prev_sibling_link(&self) -> Option<Self> {
        let prev_sibling_cyclic_link = self.prev_sibling_cyclic_link();

        let is_next_of_prev_available = prev_sibling_cyclic_link
            .core
            .next_sibling
            .try_borrow()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly")
            .is_some();
        if is_next_of_prev_available {
            // `prev_sibling_cyclic_link` is not the last sibling.
            Some(prev_sibling_cyclic_link)
        } else {
            // `prev_sibling_cyclic_link` is not the previous sibling, but the last sibling.
            None
        }
    }

    /// Returns a link to the next sibling.
    #[must_use]
    fn next_sibling_link(&self) -> Option<Self> {
        self.core
            .next_sibling
            .try_borrow()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly")
            .clone()
    }

    /// Returns a link to the first child node.
    #[must_use]
    fn first_child_link(&self) -> Option<Self> {
        self.core
            .first_child
            .try_borrow()
            .expect("[consistency] `NodeCore::first_child` should not be borrowed nestedly")
            .clone()
    }

    /// Returns a link to the last child node.
    #[must_use]
    fn last_child_link(&self) -> Option<Self> {
        self.first_child_link()
            .map(|first_child| first_child.prev_sibling_cyclic_link())
    }

    /// Returns links to the first and the last child nodes.
    #[must_use]
    fn first_last_child_link(&self) -> Option<(Self, Self)> {
        let first_child_link = self.first_child_link()?;
        let last_child_link = first_child_link.prev_sibling_cyclic_link();
        Some((first_child_link, last_child_link))
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
    fn next(&self) -> Option<Self> {
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
struct IntraTreeLinkWeak<T> {
    /// Target node core.
    core: Weak<NodeCore<T>>,
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

/// A shared owning reference to a node.
pub struct Node<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
    /// Affiliation of a node with ownership of the tree.
    affiliation: StrongAffiliationRef<T>,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            affiliation: self.affiliation.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("data", &self.intra_link.core.data)
            .field("next_sibling", &self.intra_link.core.next_sibling)
            .field("first_child", &self.intra_link.core.first_child)
            .field("affiliation", &self.affiliation)
            .finish()
    }
}

/// Data access.
impl<T> Node<T> {
    /// Returns a reference to the data associated to the node.
    #[inline]
    pub fn try_borrow_data(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.intra_link.core.data.try_borrow()
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub fn borrow_data(&self) -> Ref<'_, T> {
        self.intra_link.core.data.borrow()
    }

    /// Returns a mutable reference to the data associated to the node.
    #[inline]
    pub fn try_borrow_data_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.intra_link.core.data.try_borrow_mut()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.intra_link.core.data.borrow_mut()
    }

    /// Returns `true` if the two `Node`s point to the same allocation.
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }
}

/// Neighbor nodes accessor.
impl<T> Node<T> {
    /// Returns true if the node is the root.
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link
            .core
            .parent
            .try_borrow()
            .expect("[consistency] `NodeCore::parent` should not be borrowed nestedly")
            .is_dangling()
    }

    /// Returns the root node.
    #[must_use]
    pub fn root(&self) -> Self {
        Self {
            intra_link: self.affiliation.tree_core().root(),
            affiliation: self.affiliation.clone(),
        }
    }

    /// Returns the parent node.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.parent_link()?,
            affiliation: self.affiliation.clone(),
        })
    }

    /// Returns the previous sibling.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.prev_sibling_link()?,
            affiliation: self.affiliation.clone(),
        })
    }

    /// Returns the next sibling.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.next_sibling_link()?,
            affiliation: self.affiliation.clone(),
        })
    }

    /// Returns the first child node.
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.first_child_link()?,
            affiliation: self.affiliation.clone(),
        })
    }

    /// Returns the last child node.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.last_child_link()?,
            affiliation: self.affiliation.clone(),
        })
    }
}

/// Tree traverser.
impl<T> Node<T> {
    /// Returns the depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self) -> traverse::DepthFirstTraverser<T> {
        traverse::DepthFirstTraverser::with_start(Some(self.clone()))
    }

    /// Returns the reverse depth-first traverser.
    #[inline]
    #[must_use]
    pub fn depth_first_reverse_traverse(&self) -> traverse::ReverseDepthFirstTraverser<T> {
        traverse::ReverseDepthFirstTraverser::with_start(Some(self.clone()))
    }

    /// Returns the children traverser.
    #[inline]
    #[must_use]
    pub fn children(&self) -> traverse::SiblingsTraverser<T> {
        traverse::SiblingsTraverser::new(self.first_child())
    }

    /// Returns the reverse children traverser.
    #[inline]
    #[must_use]
    pub fn children_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        traverse::ReverseSiblingsTraverser::new(self.last_child())
    }
}

/// Node creation and structure modification.
impl<T> Node<T> {
    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the affiliation reference refers the different tree than the
    /// tree the node link belongs to.
    #[must_use]
    fn with_link_and_affiliation(
        intra_link: IntraTreeLink<T>,
        affiliation: StrongAffiliationRef<T>,
    ) -> Self {
        if !StrongAffiliationRef::ptr_eq_weak(&affiliation, &intra_link.core.affiliation) {
            panic!("[precondition] affiliation should refer the tree the node link belongs to");
        }

        Self {
            intra_link,
            affiliation,
        }
    }

    /// Creates and returns a new node as the root of a new tree.
    #[must_use]
    pub fn new_tree(root_data: T) -> Self {
        let weak_affiliation = WeakAffiliationRef::new();
        let intra_link = IntraTreeLink {
            core: Rc::new(NodeCore {
                data: RefCell::new(root_data),
                parent: Default::default(),
                first_child: Default::default(),
                next_sibling: Default::default(),
                prev_sibling_cyclic: Default::default(),
                affiliation: weak_affiliation.clone(),
            }),
        };
        {
            let weak_link = intra_link.downgrade();
            let mut prev_sibling_cyclic = intra_link
                .core
                .prev_sibling_cyclic
                .try_borrow_mut()
                .expect(
                "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed elsewhere",
            );
            *prev_sibling_cyclic = weak_link;
        }
        let tree_core_rc = Rc::new(TreeCore {
            root: RefCell::new(intra_link.clone()),
        });

        Self::with_link_and_affiliation(
            intra_link,
            weak_affiliation.initialize_affiliation(tree_core_rc),
        )
    }

    /// Detaches the node and its descendant from the current tree, and let it be another tree.
    pub fn detach_subtree(&self) {
        if self.is_root() {
            // Detaching entire tree is meaningless.
            // Do nothing.
            return;
        }
        // Change the references to the tree core.
        let tree_core_rc = Rc::new(TreeCore {
            root: RefCell::new(self.intra_link.clone()),
        });
        self.set_affiliations_of_descendants_and_self(&tree_core_rc);

        // Unlink from the neighbors.
        // Fields to update:
        //  * parent --> self
        //      * parent.first_child (if necessary)
        //      * self.parent (if available)
        //  * prev_sibling --> self
        //      * prev_sibling.next_sibling (if available)
        //      * self.prev_sibling_cyclic (mandatory)
        //  * self --> next_sibling
        //      * self.next_sibling (if available)
        //      * next_sibling.prev_sibling_cyclic (if available)

        let parent_link = self.intra_link.parent_link();
        let prev_sibling_link = self.intra_link.prev_sibling_link();
        let prev_sibling_cyclic_link = self.intra_link.prev_sibling_cyclic_link();
        let next_sibling_link = self.intra_link.next_sibling_link();
        if let Some(parent_link) = &parent_link {
            let first_sibling_link = parent_link
                .first_child_link()
                .expect("[validity] parent must have at least one child (including `self`)");
            if IntraTreeLink::ptr_eq(&self.intra_link, &first_sibling_link) {
                *parent_link.core.first_child.try_borrow_mut().expect(
                    "[consistency] `NodeCore::first_child` should not be borrowed nestedly",
                ) = next_sibling_link.clone();
            }
        }
        *self
            .intra_link
            .core
            .parent
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::first_child` should not be borrowed nestedly") =
            IntraTreeLinkWeak::default();

        if let Some(prev_sibling_link) = prev_sibling_link {
            *prev_sibling_link
                .core
                .next_sibling
                .try_borrow_mut()
                .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly") =
                next_sibling_link.clone();
        }
        let self_link_weak = self.intra_link.downgrade();
        *self
            .intra_link
            .core
            .prev_sibling_cyclic
            .try_borrow_mut()
            .expect(
                "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
            ) = self_link_weak;

        if let Some(next_sibling_link) = next_sibling_link {
            *next_sibling_link
                .core
                .prev_sibling_cyclic
                .try_borrow_mut()
                .expect(
                    "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
                ) = prev_sibling_cyclic_link.downgrade();
        }
        *self
            .intra_link
            .core
            .next_sibling
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly") =
            None;
    }

    /// Changes the affiliation of the `self` node and its descendants to the given tree.
    fn set_affiliations_of_descendants_and_self(&self, tree_core_rc: &Rc<TreeCore<T>>) {
        let start = &self.intra_link;
        let mut next = Some(DftEvent::Open(start.clone()));
        while let Some(current) = next.take() {
            next = current.next();
            let open_link = match current {
                DftEvent::Open(link) => link,
                DftEvent::Close(link) => {
                    if IntraTreeLink::ptr_eq(&link, start) {
                        // All descendants are modified.
                        return;
                    }
                    continue;
                }
            };
            open_link.core.affiliation.set_tree_core(tree_core_rc);
        }
    }

    /// Creates a node as the next sibling of `self`, and returns the new node.
    pub fn try_create_node_as(&self, data: T, dest: AdoptAs) -> Result<Self, StructureError> {
        match dest {
            AdoptAs::FirstChild => Ok(self.create_as_first_child(data)),
            AdoptAs::LastChild => Ok(self.create_as_last_child(data)),
            AdoptAs::PreviousSibling => self.try_create_as_prev_sibling(data),
            AdoptAs::NextSibling => self.try_create_as_next_sibling(data),
        }
    }

    /// Creates a node as the first child of `self`.
    pub fn create_as_first_child(&self, data: T) -> Self {
        // Fields to update:
        //  * parent --> new_child
        //      * new_child.parent (mandatory)
        //      * self.first_child (mandatory)
        //  * new_child --> old_first_child
        //      * new_child.next_sibling (if available)
        //      * old_first_child.prev_sibling_cyclic (if available)
        //  * last_child --> new_child
        //      * new_child.prev_sibling_cyclic (mandatory)

        let affiliation =
            StrongAffiliationRef::create_new_affiliation(self.affiliation.tree_core());
        let intra_link = IntraTreeLink {
            core: Rc::new(NodeCore {
                data: RefCell::new(data),
                parent: RefCell::new(self.intra_link.downgrade()),
                first_child: Default::default(),
                next_sibling: Default::default(),
                prev_sibling_cyclic: Default::default(),
                affiliation: affiliation.downgrade(),
            }),
        };
        if let Some((old_first_child_link, last_child_link)) =
            self.intra_link.first_last_child_link()
        {
            // Connect the new first child and the last child.
            *intra_link.core.prev_sibling_cyclic.try_borrow_mut().expect(
                "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
            ) = last_child_link.downgrade();

            // Connect the new first child and the old first child.
            *old_first_child_link
                .core
                .prev_sibling_cyclic
                .try_borrow_mut()
                .expect(
                    "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
                ) = intra_link.downgrade();
            *intra_link
                .core
                .next_sibling
                .try_borrow_mut()
                .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly") =
                Some(old_first_child_link);
        } else {
            *intra_link.core.prev_sibling_cyclic.try_borrow_mut().expect(
                "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
            ) = intra_link.downgrade();
        }
        *self
            .intra_link
            .core
            .first_child
            .try_borrow_mut()
            .expect("[consistency] `NodeCore::first_child` should not be borrowed nestedly") =
            Some(intra_link.clone());

        Self::with_link_and_affiliation(intra_link, affiliation)
    }

    /// Creates a node as the last child of `self`.
    pub fn create_as_last_child(&self, data: T) -> Self {
        // Fields to update:
        //  * parent --> new_child
        //      * new_child.parent (mandatory)
        //  * old_last_child --> new_child
        //      * new_child.prev_sibling_cyclic (mandatory)
        //      * old_last_child.next (if available)
        //  * first_child --> new_child
        //      * first_child.prev_sibling_cyclic (mandatory)

        let affiliation =
            StrongAffiliationRef::create_new_affiliation(self.affiliation.tree_core());
        let intra_link = IntraTreeLink {
            core: Rc::new(NodeCore {
                data: RefCell::new(data),
                parent: RefCell::new(self.intra_link.downgrade()),
                first_child: Default::default(),
                next_sibling: Default::default(),
                prev_sibling_cyclic: Default::default(),
                affiliation: affiliation.downgrade(),
            }),
        };
        if let Some((first_child_link, old_last_child_link)) =
            self.intra_link.first_last_child_link()
        {
            // Connect the old last child and the new last child.
            *intra_link.core.prev_sibling_cyclic.try_borrow_mut().expect(
                "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
            ) = old_last_child_link.downgrade();
            *old_last_child_link
                .core
                .next_sibling
                .try_borrow_mut()
                .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly") =
                Some(intra_link.clone());

            // Connect the first child and the new last child.
            *first_child_link
                .core
                .prev_sibling_cyclic
                .try_borrow_mut()
                .expect(
                    "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
                ) = intra_link.downgrade();
        } else {
            *intra_link.core.prev_sibling_cyclic.try_borrow_mut().expect(
                "[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly",
            ) = intra_link.downgrade();
            *self
                .intra_link
                .core
                .first_child
                .try_borrow_mut()
                .expect("[consistency] `NodeCore::first_child` should not be borrowed nestedly") =
                Some(intra_link.clone());
        }

        Self::with_link_and_affiliation(intra_link, affiliation)
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    pub fn try_create_as_prev_sibling(&self, data: T) -> Result<Self, StructureError> {
        let parent = self.parent().ok_or(StructureError::SiblingsWithoutParent)?;
        let new_node = match self.intra_link.prev_sibling_link() {
            Some(prev_sibling_link) => create_insert_between(
                data,
                self.affiliation.tree_core(),
                &parent.intra_link,
                &prev_sibling_link,
                &self.intra_link,
            ),
            None => parent.create_as_first_child(data),
        };
        Ok(new_node)
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    pub fn try_create_as_next_sibling(&self, data: T) -> Result<Self, StructureError> {
        let parent = self.parent().ok_or(StructureError::SiblingsWithoutParent)?;
        let new_node = match self.intra_link.next_sibling_link() {
            Some(next_sibling_link) => create_insert_between(
                data,
                self.affiliation.tree_core(),
                &parent.intra_link,
                &self.intra_link,
                &next_sibling_link,
            ),
            None => parent.create_as_last_child(data),
        };
        Ok(new_node)
    }
}

/// Inserts the `new_node` between `prev_sibling` and `next_sibling`
fn create_insert_between<T>(
    data: T,
    tree_core: Rc<TreeCore<T>>,
    parent_link: &IntraTreeLink<T>,
    prev_sibling_link: &IntraTreeLink<T>,
    next_sibling_link: &IntraTreeLink<T>,
) -> Node<T> {
    // Check consistency of the given nodes.
    debug_assert!(prev_sibling_link
        .parent_link()
        .map_or(false, |p| IntraTreeLink::ptr_eq(&p, parent_link)));
    debug_assert!(next_sibling_link
        .parent_link()
        .map_or(false, |p| IntraTreeLink::ptr_eq(&p, parent_link)));
    debug_assert!(prev_sibling_link
        .next_sibling_link()
        .map_or(false, |p| IntraTreeLink::ptr_eq(&p, next_sibling_link)));
    debug_assert!(next_sibling_link
        .prev_sibling_link()
        .map_or(false, |p| IntraTreeLink::ptr_eq(&p, prev_sibling_link)));

    // Fields to update:
    //  * parent --> new_child
    //      * new_child.parent (mandatory)
    //      * (Note that `parent.first_child` won't be set since `self` is
    //        not the first child.)
    //  * prev_sibling --> new_node
    //      * prev_sibling.next_sibling (mandatory)
    //      * new_node.prev_sibling_cyclic (mandatory)
    //  * new_node --> next_sibling
    //      * new_node.next_sibling (mandatory)
    //      * next_sibling.prev_sibling_cyclic (mandatory)

    let affiliation = StrongAffiliationRef::create_new_affiliation(tree_core);
    let intra_link = IntraTreeLink {
        core: Rc::new(NodeCore {
            data: RefCell::new(data),
            parent: RefCell::new(parent_link.downgrade()),
            first_child: Default::default(),
            next_sibling: RefCell::new(Some(next_sibling_link.clone())),
            prev_sibling_cyclic: RefCell::new(prev_sibling_link.downgrade()),
            affiliation: affiliation.downgrade(),
        }),
    };

    *next_sibling_link
        .core
        .prev_sibling_cyclic
        .try_borrow_mut()
        .expect("[consistency] `NodeCore::prev_sibling_cyclic` should not be borrowed nestedly") =
        intra_link.downgrade();
    *prev_sibling_link
        .core
        .next_sibling
        .try_borrow_mut()
        .expect("[consistency] `NodeCore::next_sibling` should not be borrowed nestedly") =
        Some(intra_link.clone());

    Node::with_link_and_affiliation(intra_link, affiliation)
}
