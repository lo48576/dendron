//! Frozen node, which is a [`Node`] with tree hierarchy edit prohibition bundled.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::Rc;

use crate::anchor::InsertAs;
use crate::membership::{Membership, MembershipWithEditProhibition};
use crate::node::debug_print::{DebugPrettyPrint, DebugPrintNodeLocal};
use crate::node::{edit, HierarchyError, HotNode, IntraTreeLink, Node, NumChildren};
use crate::serial;
use crate::traverse;
use crate::tree::{HierarchyEditProhibition, HierarchyEditProhibitionError, Tree, TreeCore};

/// A [`Node`] with a tree hierarchy edit prohibition bundled.
///
/// `FrozenNode` can be created by [`Node::bundle_hierarchy_edit_prohibition`] or
/// [`Node::bundle_new_hierarchy_edit_prohibition`].
///
/// # Panics
///
/// Panics if the number of active edit prohibitions through this node is
/// `usize::MAX`. This is very unlikely to happen without leaking prohibitions.
pub struct FrozenNode<T> {
    /// Target node core.
    pub(super) intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: MembershipWithEditProhibition<T>,
}

impl<T> Clone for FrozenNode<T> {
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            membership: self.membership.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for FrozenNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FrozenNode")
            .field("data", &self.intra_link.try_borrow_data())
            .field("next_sibling", &self.intra_link.next_sibling_link())
            .field("first_child", &self.intra_link.first_child_link())
            .field("membership", &self.membership)
            .finish()
    }
}

impl<T, U: PartialEq<U>> PartialEq<FrozenNode<U>> for FrozenNode<T>
where
    T: PartialEq<U>,
{
    /// Compares two subtrees.
    ///
    /// Returns `Ok(true)` if the two subtree are equal, even if they are stored
    /// in different allocation.
    ///
    /// # Panics
    ///
    /// May panic if associated data of some nodes are already borrowed
    /// exclusively (i.e. mutably).
    ///
    /// To avoid panicking, use [`Node::try_eq`] and [`plain`][`Self::plain`]
    /// method.
    ///
    /// # Examples
    ///
    /// See the documentation for [`Node::try_eq`] method.
    #[inline]
    fn eq(&self, other: &FrozenNode<U>) -> bool {
        self.intra_link.try_eq(&other.intra_link).expect(
            "[precondition] data associated to the nodes in both trees should be borrowable",
        )
    }
}

impl<T: Eq> Eq for FrozenNode<T> {}

impl<T> FrozenNode<T> {
    /// Creates a new `FrozenNode` from the given plain node.
    pub(super) fn from_node(node: Node<T>) -> Result<Self, HierarchyEditProhibitionError> {
        let Node {
            intra_link,
            membership,
        } = node;
        let membership = MembershipWithEditProhibition::new(membership)?;
        Ok(Self {
            intra_link,
            membership,
        })
    }

    /// Creates a new `FrozenNode` from the given plain node and the prohibition.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit prohibition is not valid for the given node.
    ///
    /// Panics if there are too many prohibitions for the node or for the tree.
    #[must_use]
    pub(super) fn from_node_and_prohibition(
        node: Node<T>,
        prohibition: &HierarchyEditProhibition<T>,
    ) -> Self {
        prohibition.panic_if_invalid_for_node(&node);

        let Node {
            intra_link,
            membership,
        } = node;
        let membership = MembershipWithEditProhibition::new(membership)
            .expect("[validity] a valid prohibition already exists for the tree");
        Self {
            intra_link,
            membership,
        }
    }

    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the membership field of the node link is not set up.
    ///
    /// Panics if a reference to the tree core is not valid.
    ///
    /// Panics if the tree is prohibited to be edited.
    #[must_use]
    pub(crate) fn from_node_link_with_prohibition(intra_link: IntraTreeLink<T>) -> Self {
        let membership = intra_link.membership().upgrade().expect(
            "[consistency] the membership must be alive since the corresponding node link is alive",
        );
        let membership = MembershipWithEditProhibition::new(membership)
            .expect("[consistency] there should have already been tree hierarchy edit prohibition");

        Self {
            intra_link,
            membership,
        }
    }

    /// Returns a reference to the plain membership.
    #[inline]
    #[must_use]
    fn plain_membership(&self) -> &Membership<T> {
        self.membership.as_inner()
    }

    /// Returns the tree core.
    #[inline]
    #[must_use]
    fn tree_core(&self) -> Rc<TreeCore<T>> {
        self.plain_membership().tree_core()
    }

    /// Creates a plain node reference for the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{FrozenNode, Node};
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// let plain: Node<_> = frozen.plain();
    /// ```
    #[must_use]
    pub fn plain(&self) -> Node<T> {
        Node::with_link_and_membership(self.intra_link.clone(), self.membership.as_inner().clone())
    }
}

impl<T> From<FrozenNode<T>> for Node<T> {
    #[inline]
    fn from(node: FrozenNode<T>) -> Self {
        node.plain()
    }
}

/// Tree hierarchy edit prohibitions.
impl<T> FrozenNode<T> {
    /// Returns a copy of the tree hierarchy edit prohibition.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{FrozenNode, Node};
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// let prohibition = frozen.extract_hierarchy_edit_prohibition();
    /// ```
    #[must_use]
    pub fn extract_hierarchy_edit_prohibition(&self) -> HierarchyEditProhibition<T> {
        self.tree()
            .prohibit_hierarchy_edit()
            .expect("[validity] the tree hierarchy is already prohibited to be edit")
    }
}

// Common methods below.

/// Data access.
impl<T> FrozenNode<T> {
    /// Returns a reference to the data associated to the node.
    ///
    /// # Failures
    ///
    /// Fails if the data is currently mutably (i.e. exclusively) borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert_eq!(
    ///     *frozen
    ///         .try_borrow_data()
    ///         .expect("should not fail since not mutably borrowed from other place"),
    ///     "root"
    /// );
    /// ```
    #[inline]
    pub fn try_borrow_data(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.intra_link.try_borrow_data()
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert_eq!(*frozen.borrow_data(), "root");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data(&self) -> Ref<'_, T> {
        self.intra_link.borrow_data()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// *frozen
    ///     .try_borrow_data_mut()
    ///     .expect("should not fail since not borrowed from other place")
    ///     = "ROOT";
    /// assert_eq!(*frozen.borrow_data(), "ROOT");
    /// ```
    #[inline]
    pub fn try_borrow_data_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.intra_link.try_borrow_data_mut()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// *frozen.borrow_data_mut() = "ROOT";
    /// assert_eq!(*frozen.borrow_data(), "ROOT");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.intra_link.borrow_data_mut()
    }

    /// Returns `true` if the two `FrozenNode`s point to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen1 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let frozen2 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen1.ptr_eq(&frozen1));
    ///
    /// assert!(frozen1 == frozen2, "same content and hierarchy");
    /// assert!(
    ///     !frozen1.ptr_eq(&frozen2),
    ///     "same content and hierarchy but different allocation"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }
}

/// Neighbor nodes accessor.
impl<T> FrozenNode<T> {
    /// Returns the tree the node belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let tree = frozen.tree();
    ///
    /// assert!(tree.root().ptr_eq(&frozen.plain()));
    /// ```
    #[inline]
    #[must_use]
    pub fn tree(&self) -> Tree<T> {
        Tree::from_core_rc(self.tree_core())
    }

    /// Returns true if the node is the root.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen.is_root());
    /// ```
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
    }

    /// Returns true if the given node belong to the same tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen1 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// let frozen2 = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(!frozen1.belongs_to_same_tree(&frozen2));
    /// ```
    #[inline]
    #[must_use]
    pub fn belongs_to_same_tree(&self, other: &Self) -> bool {
        self.membership.belongs_to_same_tree(&other.membership)
    }

    /// Returns the hot root node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let frozen = Node::new_tree("root")
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    ///
    /// assert!(frozen.root().ptr_eq(&frozen));
    /// ```
    #[must_use]
    pub fn root(&self) -> Self {
        Self::from_node_link_with_prohibition(self.tree_core().root_link())
    }

    /// Returns the parent node.
    ///
    /// See [`Node::parent`] for usage examples.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link
            .parent_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the previous sibling.
    ///
    /// See [`Node::prev_sibling`] for usage examples.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link
            .prev_sibling_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the next sibling.
    ///
    /// See [`Node::next_sibling`] for usage examples.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link
            .next_sibling_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the first sibling.
    ///
    /// See [`Node::first_sibling`] for usage examples.
    #[must_use]
    pub fn first_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let first_child_link = parent_link
                .first_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::from_node_link_with_prohibition(first_child_link)
        } else {
            // `self` is the root node.
            self.clone()
        }
    }

    /// Returns the last sibling.
    ///
    /// See [`Node::last_sibling`] for usage examples.
    #[must_use]
    pub fn last_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let last_child_lin = parent_link
                .last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::from_node_link_with_prohibition(last_child_lin)
        } else {
            // `self` is the root node.
            self.clone()
        }
    }

    /// Returns the first and the last siblings.
    ///
    /// See [`Node::first_last_sibling`] for usage examples.
    #[must_use]
    pub fn first_last_sibling(&self) -> (Self, Self) {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let (first_child_link, last_child_link) = parent_link
                .first_last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            (
                Self::from_node_link_with_prohibition(first_child_link),
                Self::from_node_link_with_prohibition(last_child_link),
            )
        } else {
            // `self` is the root node.
            (self.clone(), self.clone())
        }
    }

    /// Returns the first child node.
    ///
    /// See [`Node::first_child`] for usage examples.
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.intra_link
            .first_child_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns the last child node.
    ///
    /// See [`Node::last_child`] for usage examples.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link
            .last_child_link()
            .map(Self::from_node_link_with_prohibition)
    }

    /// Returns links to the first and the last child nodes.
    ///
    /// See [`Node::first_last_child`] for usage examples.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
        Some((
            Self::from_node_link_with_prohibition(first_link),
            Self::from_node_link_with_prohibition(last_link),
        ))
    }

    /// Returns true if the previous sibling exists.
    ///
    /// See [`Node::has_prev_sibling`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_prev_sibling(&self) -> bool {
        self.intra_link.has_prev_sibling()
    }

    /// Returns true if the next sibling exists.
    ///
    /// See [`Node::has_prev_sibling`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_next_sibling(&self) -> bool {
        self.intra_link.has_next_sibling()
    }

    /// Returns true if the node has any children.
    ///
    /// See [`Node::has_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_children(&self) -> bool {
        self.intra_link.has_children()
    }

    /// Returns true if the node has just one child.
    ///
    /// See [`Node::has_one_child`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_one_child(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::One
    }

    /// Returns true if the node has two or more children.
    ///
    /// See [`Node::has_multiple_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn has_multiple_children(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::TwoOrMore
    }

    /// Returns the number of children.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_children(&self) -> usize {
        self.intra_link.count_children()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_preceding_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_preceding_siblings(&self) -> usize {
        self.intra_link.count_preceding_siblings()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_following_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_following_siblings(&self) -> usize {
        self.intra_link.count_following_siblings()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    ///
    /// See [`Node::count_ancestors`] for usage examples.
    #[inline]
    #[must_use]
    pub fn count_ancestors(&self) -> usize {
        self.intra_link.count_ancestors()
    }
}

/// Tree traverser.
impl<T> FrozenNode<T> {
    /// Returns the depth-first traverser.
    ///
    /// See [`Node::depth_first_traverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self) -> traverse::DepthFirstTraverser<T> {
        self.plain().depth_first_traverse()
    }

    /// Returns the reverse depth-first traverser.
    ///
    /// See [`Node::depth_first_reverse_traverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn depth_first_reverse_traverse(&self) -> traverse::ReverseDepthFirstTraverser<T> {
        self.plain().depth_first_reverse_traverse()
    }

    /// Returns the children traverser.
    ///
    /// See [`Node::children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn children(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().children()
    }

    /// Returns the reverse children traverser.
    ///
    /// See [`Node::children_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn children_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().children_reverse()
    }

    /// Returns the ancestors traverser.
    ///
    /// See [`Node::ancestors`] for usage examples.
    #[inline]
    #[must_use]
    pub fn ancestors(&self) -> traverse::AncestorsTraverser<T> {
        self.plain().ancestors()
    }

    /// Returns the ancestors traverser.
    ///
    /// See [`Node::ancestors_or_self`] for usage examples.
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self) -> traverse::AncestorsTraverser<T> {
        self.plain().ancestors_or_self()
    }

    /// Returns the siblings traverser.
    ///
    /// See [`Node::siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn siblings(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().siblings()
    }

    /// Returns the reverse siblings traverser.
    ///
    /// See [`Node::siblings_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().siblings_reverse()
    }

    /// Returns the preceding siblings traverser.
    ///
    /// See [`Node::preceding_siblings_or_self_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().preceding_siblings_or_self_reverse()
    }

    /// Returns the preceding siblings traverser.
    ///
    /// See [`Node::preceding_siblings_reverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        self.plain().preceding_siblings_reverse()
    }

    /// Returns the following siblings traverser.
    ///
    /// See [`Node::following_siblings_or_self`] for usage examples.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().following_siblings_or_self()
    }

    /// Returns the following siblings traverser.
    ///
    /// See [`Node::following_siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn following_siblings(&self) -> traverse::SiblingsTraverser<T> {
        self.plain().following_siblings()
    }

    /// Returns the stable double-ended depth-first traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// See [`Node::depth_first_traverse`] for usage examples.
    #[inline]
    #[must_use]
    pub fn depth_first_traverse_stable(&self) -> traverse::StableDepthFirstTraverser<T> {
        traverse::StableDepthFirstTraverser::with_toplevel(Some(self.clone()))
    }

    /// Returns the stable double-ended children traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// See [`Node::children`] for usage examples.
    #[inline]
    #[must_use]
    pub fn children_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_parent(Some(self.clone()))
    }

    /// Returns the stable siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// See [`Node::siblings`] for usage examples.
    #[inline]
    #[must_use]
    pub fn siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children_stable(),
            None => self.following_siblings_or_self_stable(),
        }
    }

    /// Returns the stable preceding siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_first_last(Some((
            self.first_sibling(),
            self.clone(),
        )))
    }

    /// Returns the stable preceding siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        let mut iter = self.preceding_siblings_or_self_stable();
        iter.next();
        iter
    }

    /// Returns the stable following siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        traverse::StableSiblingsTraverser::with_first_last(Some((
            self.clone(),
            self.last_sibling(),
        )))
    }

    /// Returns the stable following siblings traverser.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    #[inline]
    #[must_use]
    pub fn following_siblings_stable(&self) -> traverse::StableSiblingsTraverser<T> {
        let mut iter = self.following_siblings_or_self_stable();
        iter.next();
        iter
    }

    /// Returns the stable depth-first traverser that can limit the depth to iterate.
    ///
    /// If `None` is passed as `max_depth`, then the iterator traverses nodes
    /// in unlimited depth.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::traverse::DftEvent;
    ///
    /// let frozen = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             /("0-0", ["0-0-0", "0-0-1"]),
    ///             "0-1",
    ///             /("0-2", ["0-2-0"]),
    ///         ]),
    ///         /("1", [
    ///             "1-0",
    ///         ]),
    ///         "2",
    ///     ]
    /// }
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   |   |-- 0-0-0
    /// //  |   |   `-- 0-0-1
    /// //  |   |-- 0-1
    /// //  |   `-- 0-2
    /// //  |       `-- 0-2-0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- 2
    ///
    /// let max0 = frozen.shallow_depth_first_traverse_stable(Some(0))
    ///     .map(|ev| ev.map(|(node, depth)| (*node.borrow_data(), depth)))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     max0,
    ///     &[
    ///         DftEvent::Open(("root", 0)),
    ///         DftEvent::Close(("root", 0)),
    ///     ]
    /// );
    ///
    /// let max2 = frozen.shallow_depth_first_traverse_stable(Some(2))
    ///     .map(|ev| ev.map(|(node, depth)| (*node.borrow_data(), depth)))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     max2,
    ///     &[
    ///         DftEvent::Open(("root", 0)),
    ///         DftEvent::Open(("0", 1)),
    ///         DftEvent::Open(("0-0", 2)),
    ///         DftEvent::Close(("0-0", 2)),
    ///         DftEvent::Open(("0-1", 2)),
    ///         DftEvent::Close(("0-1", 2)),
    ///         DftEvent::Open(("0-2", 2)),
    ///         DftEvent::Close(("0-2", 2)),
    ///         DftEvent::Close(("0", 1)),
    ///         DftEvent::Open(("1", 1)),
    ///         DftEvent::Open(("1-0", 2)),
    ///         DftEvent::Close(("1-0", 2)),
    ///         DftEvent::Close(("1", 1)),
    ///         DftEvent::Open(("2", 1)),
    ///         DftEvent::Close(("2", 1)),
    ///         DftEvent::Close(("root", 0)),
    ///     ]
    /// );
    ///
    /// let max_unlimited = frozen.shallow_depth_first_traverse_stable(None)
    ///     .map(|ev| ev.map(|(node, _depth)| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// let all = frozen.depth_first_traverse()
    ///     .map(|ev| ev.map(|node| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(max_unlimited, all);
    /// ```
    #[inline]
    #[must_use]
    pub fn shallow_depth_first_traverse_stable(
        &self,
        max_depth: Option<usize>,
    ) -> traverse::StableShallowDepthFirstTraverser<T> {
        traverse::StableShallowDepthFirstTraverser::with_toplevel(Some(self.clone()), max_depth)
    }

    /// Returns the stable non-allocating breadth-first traverser.
    ///
    /// Note that traversing all nodes will be `O(n^2)` operation in worst case,
    /// not `O(n)`.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::traverse::DftEvent;
    ///
    /// let frozen = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             /("0-0", ["0-0-0", "0-0-1"]),
    ///             "0-1",
    ///             /("0-2", ["0-2-0"]),
    ///         ]),
    ///         /("1", [
    ///             "1-0",
    ///         ]),
    ///         "2",
    ///     ]
    /// }
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   |   |-- 0-0-0
    /// //  |   |   `-- 0-0-1
    /// //  |   |-- 0-1
    /// //  |   `-- 0-2
    /// //  |       `-- 0-2-0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- 2
    ///
    /// let depth2 = frozen
    ///     .non_allocating_breadth_first_traverse_stable(2)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     depth2,
    ///     &[
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    ///
    /// let all = frozen
    ///     .non_allocating_breadth_first_traverse_stable(0)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     all,
    ///     &[
    ///         ("root", 0),
    ///         ("0", 1), ("1", 1), ("2", 1),
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn non_allocating_breadth_first_traverse_stable(
        &self,
        start_depth: usize,
    ) -> traverse::NonAllocatingBreadthFirstTraverser<T> {
        traverse::NonAllocatingBreadthFirstTraverser::with_toplevel(self.clone(), start_depth)
    }

    /// Returns the stable allocating breadth-first traverser.
    ///
    /// The returned traverser will heap-allocate, and iterating all nodes is
    /// `O(n)` operation.
    ///
    /// "Stable" here means that the hierarchy of the tree is currently frozen.
    /// Stable traverser implements
    /// [`DoubleEndedIterator`][`core::iter::DoubleEndedIterator`] and can be
    /// iterated backward.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    /// use dendron::traverse::DftEvent;
    ///
    /// let frozen = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             /("0-0", ["0-0-0", "0-0-1"]),
    ///             "0-1",
    ///             /("0-2", ["0-2-0"]),
    ///         ]),
    ///         /("1", [
    ///             "1-0",
    ///         ]),
    ///         "2",
    ///     ]
    /// }
    ///     .bundle_new_hierarchy_edit_prohibition()
    ///     .expect("no hierarchy edit grant exist");
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   |   |-- 0-0-0
    /// //  |   |   `-- 0-0-1
    /// //  |   |-- 0-1
    /// //  |   `-- 0-2
    /// //  |       `-- 0-2-0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- 2
    ///
    /// let depth2 = frozen
    ///     .allocating_breadth_first_traverse_stable(2)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     depth2,
    ///     &[
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    ///
    /// let all = frozen
    ///     .allocating_breadth_first_traverse_stable(0)
    ///     .map(|(node, depth)| (*node.borrow_data(), depth))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     all,
    ///     &[
    ///         ("root", 0),
    ///         ("0", 1), ("1", 1), ("2", 1),
    ///         ("0-0", 2), ("0-1", 2), ("0-2", 2), ("1-0", 2),
    ///         ("0-0-0", 3), ("0-0-1", 3), ("0-2-0", 3)
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn allocating_breadth_first_traverse_stable(
        &self,
        start_depth: usize,
    ) -> traverse::AllocatingBreadthFirstTraverser<T> {
        traverse::AllocatingBreadthFirstTraverser::with_toplevel(self.clone(), start_depth)
    }
}

/// Node creation and modification (to the other tree).
impl<T> FrozenNode<T> {
    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    ///
    /// See [`Node::try_clone_subtree`] for usage examples.
    #[inline]
    pub fn try_clone_subtree(&self) -> Result<Node<T>, BorrowError>
    where
        T: Clone,
    {
        self.plain().try_clone_subtree()
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// See [`Node::try_clone_subtree`] for usage examples.
    ///
    /// # Panics
    ///
    /// Panics if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    #[inline]
    #[must_use]
    pub fn clone_subtree(&self) -> Node<T>
    where
        T: Clone,
    {
        self.try_clone_subtree()
            .expect("[precondition] data associated to nodes should be borrowable")
    }

    /// Clones the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the cloned new subtree.
    ///
    /// # Failures
    ///
    /// Fails with [`BorrowNodeData`][`HierarchyError::BorrowNodeData`] if any
    /// data associated to the node in the subtree is mutably (i.e. exclusively)
    /// borrowed.
    ///
    /// See [`Node::try_clone_insert_subtree`] for usage examples.
    #[inline]
    pub fn try_clone_insert_subtree(
        &self,
        dest: InsertAs<&HotNode<T>>,
    ) -> Result<HotNode<T>, HierarchyError>
    where
        T: Clone,
    {
        edit::try_clone_insert_subtree(&self.plain(), dest)
    }
}

/// Serialization.
impl<T: Clone> FrozenNode<T> {
    /// Returns an iterator of serialized events for the subtree.
    ///
    /// See [`Node::to_events`] for usage examples.
    #[inline]
    #[must_use]
    pub fn to_events(&self) -> serial::TreeSerializeIter<T> {
        serial::TreeSerializeIter::new(&self.plain())
    }
}

/// Debug printing.
impl<T> FrozenNode<T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// See [`Node::debug_pretty_print`] for usage and example output.
    #[inline]
    #[must_use]
    pub fn debug_pretty_print(&self) -> DebugPrettyPrint<'_, T> {
        DebugPrettyPrint::new(&self.intra_link)
    }

    /// Returns a debug-printable proxy that does not dump neighbor nodes.
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// See [`Node::debug_print_local`] for usage.
    #[inline]
    #[must_use]
    pub fn debug_print_local(&self) -> DebugPrintNodeLocal<'_, T> {
        DebugPrintNodeLocal::new(&self.intra_link, self.membership.as_ref())
    }
}
