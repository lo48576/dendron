//! Plain node.

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::{Rc, Weak};

use crate::anchor::{AdoptAs, InsertAs};
use crate::membership::{Membership, WeakMembership};
use crate::node::debug_print::{DebugPrettyPrint, DebugPrintNodeLocal, DebugPrintSubtree};
use crate::node::edit;
use crate::node::internal::{IntraTreeLink, IntraTreeLinkWeak, NodeBuilder};
use crate::node::{FrozenNode, HierarchyError, HotNode};
use crate::serial::{self, TreeBuildError};
use crate::traverse;
use crate::tree::{
    HierarchyEditGrant, HierarchyEditGrantError, HierarchyEditProhibition,
    HierarchyEditProhibitionError, Tree, TreeCore,
};

/// A shared owning reference to a node.
pub struct Node<T> {
    /// Target node core.
    pub(super) intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    pub(super) membership: Membership<T>,
}

impl<T> Clone for Node<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            membership: self.membership.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.debug_print_local().fmt(f)
    }
}

impl<T, U: PartialEq<U>> PartialEq<Node<U>> for Node<T>
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
    /// To avoid panicking, use [`try_eq`][`Node::try_eq`] method.
    ///
    /// # Examples
    ///
    /// See the documentation for [`try_eq`][`Self::try_eq`] method.
    #[inline]
    fn eq(&self, other: &Node<U>) -> bool {
        self.try_eq(other).expect(
            "[precondition] data associated to the nodes in both trees should be borrowable",
        )
    }
}

impl<T: Eq> Eq for Node<T> {}

/// Implements comparisons for different node types.
macro_rules! impl_cmp_different_node_types {
    ($ty_lhs:ident, $ty_rhs:ident) => {
        impl<T, U: PartialEq<U>> PartialEq<$ty_rhs<U>> for $ty_lhs<T>
        where
            T: PartialEq<U>,
        {
            impl_cmp_different_node_types!(@inner_fn, $ty_rhs<U>);
        }

        impl<T, U: PartialEq<U>> PartialEq<$ty_lhs<U>> for $ty_rhs<T>
        where
            T: PartialEq<U>,
        {
            impl_cmp_different_node_types!(@inner_fn, $ty_lhs<U>);
        }

        impl<T, U: PartialEq<U>> PartialEq<&$ty_rhs<U>> for $ty_lhs<T>
        where
            T: PartialEq<U>,
        {
            impl_cmp_different_node_types!(@inner_fn, &$ty_rhs<U>);
        }

        impl<T, U: PartialEq<U>> PartialEq<&$ty_lhs<U>> for $ty_rhs<T>
        where
            T: PartialEq<U>,
        {
            impl_cmp_different_node_types!(@inner_fn, &$ty_lhs<U>);
        }

        impl<T, U: PartialEq<U>> PartialEq<$ty_rhs<U>> for &$ty_lhs<T>
        where
            T: PartialEq<U>,
        {
            impl_cmp_different_node_types!(@inner_fn, $ty_rhs<U>);
        }

        impl<T, U: PartialEq<U>> PartialEq<$ty_lhs<U>> for &$ty_rhs<T>
        where
            T: PartialEq<U>,
        {
            impl_cmp_different_node_types!(@inner_fn, $ty_lhs<U>);
        }
    };
    (@inner_fn, $ty_rhs:ty) => {
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
        /// To avoid panicking, use [`Node::try_eq`], [`FrozenNode::plain`], and
        /// [`HotNode::plain`] methods.
        ///
        /// # Examples
        ///
        /// See the documentation for [`Node::try_eq`] method.
        #[inline]
        fn eq(&self, other: &$ty_rhs) -> bool {
            self.intra_link.try_eq(&other.intra_link).expect(
                "[precondition] data associated to the nodes in both trees should be borrowable",
            )
        }
    }
}

impl_cmp_different_node_types!(Node, FrozenNode);
impl_cmp_different_node_types!(Node, HotNode);
impl_cmp_different_node_types!(FrozenNode, HotNode);

/// Node object creation.
impl<T> Node<T> {
    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the membership field of the node link is not set up.
    ///
    /// Panics if a reference to the tree core is not valid.
    #[must_use]
    pub(crate) fn with_link(intra_link: IntraTreeLink<T>) -> Self {
        let membership = intra_link.membership().upgrade().expect(
            "[consistency] the membership must be alive since the corresponding node link is alive",
        );

        Self {
            intra_link,
            membership,
        }
    }

    /// Creates a node from the internal values.
    ///
    /// # Panics
    ///
    /// Panics if the membership is set up for a node other than the given node.
    #[must_use]
    pub(crate) fn with_link_and_membership(
        intra_link: IntraTreeLink<T>,
        membership: Membership<T>,
    ) -> Self {
        if !Membership::ptr_eq_weak(&membership, intra_link.membership()) {
            panic!("[precondition] membership should be set up for the node of interest");
        }

        Self {
            intra_link,
            membership,
        }
    }

    /// Downgrades the reference to a weak one.
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let root_weak = root.downgrade();
    /// assert!(root_weak.upgrade().is_some());
    ///
    /// drop(root);
    /// assert!(root_weak.upgrade().is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn downgrade(&self) -> NodeWeak<T> {
        NodeWeak {
            intra_link: self.intra_link.downgrade(),
        }
    }
}

/// Tree hierarchy edit grants and prohibitions.
impl<T> Node<T> {
    /// Returns the [`FrozenNode`], a node with tree hierarchy edit prohibition bundled.
    ///
    /// # Failures
    ///
    /// Fails if the hierarchy is already granted to be edited.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// let frozen = node.bundle_new_hierarchy_edit_prohibition()?;
    /// # Ok::<_, dendron::tree::HierarchyEditProhibitionError>(())
    /// ```
    #[inline]
    pub fn bundle_new_hierarchy_edit_prohibition(
        self,
    ) -> Result<FrozenNode<T>, HierarchyEditProhibitionError> {
        FrozenNode::from_node(self)
    }

    /// Returns the [`HotNode`], a node with tree hierarchy edit grant bundled.
    ///
    /// # Failures
    ///
    /// Fails if the hierarchy is already granted to be edited.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// let hot_node = node.bundle_new_hierarchy_edit_grant()?;
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn bundle_new_hierarchy_edit_grant(self) -> Result<HotNode<T>, HierarchyEditGrantError> {
        HotNode::from_node(self)
    }

    /// Returns the [`FrozenNode`], a node with tree hierarchy edit prohibition bundled.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy prohibition grant is not valid for the given node.
    ///
    /// # Failures
    ///
    /// Fails if the hierarchy is already prohibited to be edited.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// let prohibition = node.tree().prohibit_hierarchy_edit()?;
    ///
    /// let frozen_node = node.bundle_hierarchy_edit_prohibition(&prohibition);
    /// # Ok::<_, dendron::tree::HierarchyEditProhibitionError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn bundle_hierarchy_edit_prohibition(
        self,
        prohibition: &HierarchyEditProhibition<T>,
    ) -> FrozenNode<T> {
        FrozenNode::from_node_and_prohibition(self, prohibition)
    }

    /// Returns the [`HotNode`], a node with tree hierarchy edit grant bundled.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Failures
    ///
    /// Fails if the hierarchy is already granted to be edited.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// let grant = node.tree().grant_hierarchy_edit()?;
    ///
    /// let hot_node = node.bundle_hierarchy_edit_grant(&grant);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn bundle_hierarchy_edit_grant(self, grant: &HierarchyEditGrant<T>) -> HotNode<T> {
        HotNode::from_node_and_grant(self, grant)
    }
}

// Common methods below.

/// Data access.
impl<T> Node<T> {
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
    /// let node = Node::new_tree("root");
    /// assert_eq!(
    ///     *node
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
    /// let node = Node::new_tree("root");
    /// assert_eq!(*node.borrow_data(), "root");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data(&self) -> Ref<'_, T> {
        self.intra_link.borrow_data()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Failures
    ///
    /// Fails if the data is currently borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// *node
    ///     .try_borrow_data_mut()
    ///     .expect("should not fail since not borrowed from other place")
    ///     = "ROOT";
    /// assert_eq!(*node.borrow_data(), "ROOT");
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
    /// let node = Node::new_tree("root");
    /// *node.borrow_data_mut() = "ROOT";
    /// assert_eq!(*node.borrow_data(), "ROOT");
    /// ```
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.intra_link.borrow_data_mut()
    }

    /// Returns `true` if the two `Node`s point to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node1 = Node::new_tree("root");
    /// let node2 = Node::new_tree("root");
    ///
    /// assert!(node1.ptr_eq(&node1));
    ///
    /// assert!(node1 == node2, "same content and hierarchy");
    /// assert!(
    ///     !node1.ptr_eq(&node2),
    ///     "same content and hierarchy but different allocation"
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        IntraTreeLink::ptr_eq(&self.intra_link, &other.intra_link)
    }

    /// Returns a reference to the tree core for the node.
    #[inline]
    #[must_use]
    pub(crate) fn ptr_eq_tree_core_weak(&self, other: &Weak<TreeCore<T>>) -> bool {
        Rc::as_ptr(&*self.membership.tree_core_ref()) == other.as_ptr()
    }
}

/// Neighbor nodes accessor.
impl<T> Node<T> {
    /// Returns the tree the node belongs to.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// let tree = node.tree();
    ///
    /// assert!(tree.root().ptr_eq(&node));
    /// ```
    #[inline]
    #[must_use]
    pub fn tree(&self) -> Tree<T> {
        Tree::from_core_rc(self.membership.tree_core())
    }

    /// Returns true if the node belongs to the given tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child = root.create_as_last_child(&grant, "child");
    /// //  root
    /// //  `-- child
    ///
    /// let other_node = Node::new_tree("other");
    ///
    /// assert!(root.belongs_to(&root.tree()));
    /// assert!(child.belongs_to(&root.tree()));
    ///
    /// assert!(!root.belongs_to(&other_node.tree()));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn belongs_to(&self, tree: &Tree<T>) -> bool {
        self.membership.belongs_to(tree)
    }

    /// Returns true if the given node belong to the same tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child = root.create_as_last_child(&grant, "child");
    /// //  root
    /// //  `-- child
    ///
    /// let other_node = Node::new_tree("other");
    ///
    /// assert!(root.belongs_to_same_tree(&child));
    /// assert!(child.belongs_to_same_tree(&root));
    ///
    /// assert!(!root.belongs_to_same_tree(&other_node));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn belongs_to_same_tree(&self, other: &Self) -> bool {
        self.membership.belongs_to_same_tree(&other.membership)
    }

    /// Returns true if the node is the root.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child = root.create_as_last_child(&grant, "child");
    /// //  root
    /// //  `-- child
    ///
    /// assert!(root.is_root());
    /// assert!(!child.is_root());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn is_root(&self) -> bool {
        debug_assert_eq!(
            self.intra_link.is_root(),
            self.membership
                .tree_core_ref()
                .root_link()
                .ptr_eq(&self.intra_link),
        );
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
    }

    /// Returns the root node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let node = Node::new_tree("root");
    /// let tree = node.tree();
    ///
    /// assert!(tree.root().ptr_eq(&node));
    /// ```
    #[inline]
    #[must_use]
    pub fn root(&self) -> Self {
        Self::with_link(self.membership.tree_core().root_link())
    }

    /// Returns the parent node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child = root.create_as_last_child(&grant, "child");
    /// //  root
    /// //  `-- child
    ///
    /// assert!(child.parent().expect("has parent").ptr_eq(&root));
    /// assert!(root.parent().is_none());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link.parent_link().map(Self::with_link)
    }

    /// Returns the previous sibling.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// assert!(child0.prev_sibling().is_none());
    /// assert!(child1.prev_sibling().expect("has prev sibling").ptr_eq(&child0));
    /// assert!(root.prev_sibling().is_none());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link.prev_sibling_link().map(Self::with_link)
    }

    /// Returns the next sibling.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// assert!(child0.next_sibling().expect("has next sibling").ptr_eq(&child1));
    /// assert!(child1.next_sibling().is_none());
    /// assert!(root.prev_sibling().is_none());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link.next_sibling_link().map(Self::with_link)
    }

    /// Returns the first sibling.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    ///
    /// assert!(child0.first_sibling().ptr_eq(&child0));
    /// assert!(child1.first_sibling().ptr_eq(&child0));
    /// assert!(child2.first_sibling().ptr_eq(&child0));
    ///
    /// assert!(root.first_sibling().ptr_eq(&root));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[must_use]
    pub fn first_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let first_child_link = parent_link
                .first_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::with_link(first_child_link)
        } else {
            // `self` is the root node.
            self.clone()
        }
    }

    /// Returns the last sibling.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    ///
    /// assert!(child0.last_sibling().ptr_eq(&child2));
    /// assert!(child1.last_sibling().ptr_eq(&child2));
    /// assert!(child2.last_sibling().ptr_eq(&child2));
    ///
    /// assert!(root.first_sibling().ptr_eq(&root));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[must_use]
    pub fn last_sibling(&self) -> Self {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let last_child_lin = parent_link
                .last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            Self::with_link(last_child_lin)
        } else {
            // `self` is the root node.
            self.clone()
        }
    }

    /// Returns the first and the last sibling.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    ///
    /// let (first_sib, last_sib) = child1.first_last_sibling();
    /// assert!(first_sib.ptr_eq(&child0));
    /// assert!(last_sib.ptr_eq(&child2));
    ///
    /// let (root_first_sib, root_last_sib) = root.first_last_sibling();
    /// assert!(root_first_sib.ptr_eq(&root));
    /// assert!(root_last_sib.ptr_eq(&root));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[must_use]
    pub fn first_last_sibling(&self) -> (Self, Self) {
        if let Some(parent_link) = self.intra_link.parent_link() {
            let (first_child_link, last_child_link) = parent_link
                .first_last_child_link()
                .expect("[validity] the parent must have at least one child (`self`)");
            (
                Self::with_link(first_child_link),
                Self::with_link(last_child_link),
            )
        } else {
            // `self` is the root node.
            (self.clone(), self.clone())
        }
    }

    /// Returns the first child node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// assert!(root.first_child().expect("has children").ptr_eq(&child0));
    /// assert!(child0.first_child().is_none());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.intra_link.first_child_link().map(Self::with_link)
    }

    /// Returns the last child node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// assert!(root.last_child().expect("has children").ptr_eq(&child1));
    /// assert!(child0.last_child().is_none());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link.last_child_link().map(Self::with_link)
    }

    /// Returns the first and the last child nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    ///
    /// let (first_child, last_child) = root.first_last_child()
    ///     .expect("has children");
    /// assert!(first_child.ptr_eq(&child0));
    /// assert!(last_child.ptr_eq(&child2));
    ///
    /// assert!(child1.first_last_child().is_none());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
        Some((Self::with_link(first_link), Self::with_link(last_link)))
    }

    /// Returns true if the previous sibling exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// assert!(!child0.has_prev_sibling());
    /// assert!(child1.has_prev_sibling());
    /// assert!(!root.has_prev_sibling());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn has_prev_sibling(&self) -> bool {
        self.intra_link.has_prev_sibling()
    }

    /// Returns true if the next sibling exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// assert!(child0.has_next_sibling());
    /// assert!(!child1.has_next_sibling());
    /// assert!(!root.has_next_sibling());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn has_next_sibling(&self) -> bool {
        self.intra_link.has_next_sibling()
    }

    /// Returns the number of children.
    ///
    /// This is `O(1)` operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// assert_eq!(root.num_children(), 0);
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// assert_eq!(root.num_children(), 1);
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// assert_eq!(root.num_children(), 2);
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// assert_eq!(root.num_children(), 3);
    /// let child2_0 = child2.create_as_last_child(&grant, "child2_0");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    /// //      `-- child2_0
    ///
    /// assert_eq!(root.count_children(), 3);
    /// assert_eq!(child0.count_children(), 0);
    /// assert_eq!(child1.count_children(), 0);
    /// assert_eq!(child2.count_children(), 1);
    /// assert_eq!(child2_0.count_children(), 0);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn num_children(&self) -> usize {
        self.intra_link.num_children_cell().get()
    }

    /// Returns true if the node has any children.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child1_0 = child1.create_as_last_child(&grant, "child1_0");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    /// //      `-- child1_0
    ///
    /// assert!(root.has_children());
    /// assert!(child1.has_children());
    ///
    /// assert!(!child0.has_children());
    /// assert!(!child1_0.has_children());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn has_children(&self) -> bool {
        self.num_children() != 0
    }

    /// Returns true if the node has just one child.
    ///
    /// Use [`num_children`][`Self::num_children`] method instead, i.e. use
    /// `self.num_children() == 1`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child1_0 = child1.create_as_last_child(&grant, "child1_0");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    /// //      `-- child1_0
    ///
    /// assert!(child1.has_one_child());
    ///
    /// assert!(!root.has_one_child());
    /// assert!(!child0.has_one_child());
    /// assert!(!child1_0.has_one_child());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    #[deprecated(since = "0.1.1", note = "use `Node::num_children`")]
    pub fn has_one_child(&self) -> bool {
        self.num_children() == 1
    }

    /// Returns true if the node has two or more children.
    ///
    /// Use [`num_children`][`Self::num_children`] method instead, i.e. use
    /// `self.num_children() > 1`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child1_0 = child1.create_as_last_child(&grant, "child1_0");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    /// //      `-- child1_0
    ///
    /// assert!(root.has_multiple_children());
    ///
    /// assert!(!child0.has_multiple_children());
    /// assert!(!child1.has_multiple_children());
    /// assert!(!child1_0.has_multiple_children());
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    #[deprecated(since = "0.1.1", note = "use `Node::num_children`")]
    pub fn has_multiple_children(&self) -> bool {
        self.num_children() > 1
    }

    /// Returns the number of children.
    ///
    /// Use [`num_children`][`Self::num_children`] method instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// let child2_0 = child2.create_as_last_child(&grant, "child2_0");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    /// //      `-- child2_0
    ///
    /// assert_eq!(root.count_children(), 3);
    /// assert_eq!(child0.count_children(), 0);
    /// assert_eq!(child1.count_children(), 0);
    /// assert_eq!(child2.count_children(), 1);
    /// assert_eq!(child2_0.count_children(), 0);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    #[deprecated(since = "0.1.1", note = "use `Node::num_children`")]
    pub fn count_children(&self) -> usize {
        self.num_children()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// let child2_0 = child2.create_as_last_child(&grant, "child2_0");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    /// //      `-- child2_0
    ///
    /// assert_eq!(root.count_preceding_siblings(), 0);
    /// assert_eq!(child0.count_preceding_siblings(), 0);
    /// assert_eq!(child1.count_preceding_siblings(), 1);
    /// assert_eq!(child2.count_preceding_siblings(), 2);
    /// assert_eq!(child2_0.count_preceding_siblings(), 0);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn count_preceding_siblings(&self) -> usize {
        self.intra_link.count_preceding_siblings()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child2 = root.create_as_last_child(&grant, "child2");
    /// let child2_0 = child2.create_as_last_child(&grant, "child2_0");
    /// //  root
    /// //  |-- child0
    /// //  |-- child1
    /// //  `-- child2
    /// //      `-- child2_0
    ///
    /// assert_eq!(root.count_following_siblings(), 0);
    /// assert_eq!(child0.count_following_siblings(), 2);
    /// assert_eq!(child1.count_following_siblings(), 1);
    /// assert_eq!(child2.count_following_siblings(), 0);
    /// assert_eq!(child2_0.count_following_siblings(), 0);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn count_following_siblings(&self) -> usize {
        self.intra_link.count_following_siblings()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "child0");
    /// let child1 = root.create_as_last_child(&grant, "child1");
    /// let child1_0 = child1.create_as_last_child(&grant, "child1_0");
    /// //  root
    /// //  |-- child0
    /// //  `-- child1
    /// //      `-- child1_0
    ///
    /// assert_eq!(root.count_ancestors(), 0);
    /// assert_eq!(child0.count_ancestors(), 1);
    /// assert_eq!(child1.count_ancestors(), 1);
    /// assert_eq!(child1_0.count_ancestors(), 2);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn count_ancestors(&self) -> usize {
        self.intra_link.count_ancestors()
    }
}

/// Tree traverser.
impl<T> Node<T> {
    /// Returns the depth-first traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    /// use dendron::traverse::DftEvent;
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         "0",
    ///         "1",
    ///         /("2", [
    ///             "2-0",
    ///             "2-1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let events = root.depth_first_traverse()
    ///     .map(|ev| ev.map(|node| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     events,
    ///     &[
    ///         DftEvent::Open("root"),
    ///         DftEvent::Open("0"),
    ///         DftEvent::Close("0"),
    ///         DftEvent::Open("1"),
    ///         DftEvent::Close("1"),
    ///         DftEvent::Open("2"),
    ///         DftEvent::Open("2-0"),
    ///         DftEvent::Close("2-0"),
    ///         DftEvent::Open("2-1"),
    ///         DftEvent::Close("2-1"),
    ///         DftEvent::Close("2"),
    ///         DftEvent::Close("root"),
    ///     ]
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn depth_first_traverse(&self) -> traverse::DepthFirstTraverser<T> {
        traverse::DepthFirstTraverser::with_start(Some(self.clone()))
    }

    /// Returns the reverse depth-first traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    /// use dendron::traverse::DftEvent;
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         "0",
    ///         "1",
    ///         /("2", [
    ///             "2-0",
    ///             "2-1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let events = root.depth_first_reverse_traverse()
    ///     .map(|ev| ev.map(|node| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(
    ///     events,
    ///     &[
    ///         DftEvent::Close("root"),
    ///         DftEvent::Close("2"),
    ///         DftEvent::Close("2-1"),
    ///         DftEvent::Open("2-1"),
    ///         DftEvent::Close("2-0"),
    ///         DftEvent::Open("2-0"),
    ///         DftEvent::Open("2"),
    ///         DftEvent::Close("1"),
    ///         DftEvent::Open("1"),
    ///         DftEvent::Close("0"),
    ///         DftEvent::Open("0"),
    ///         DftEvent::Open("root"),
    ///     ]
    /// );
    /// ```
    ///
    /// The iterator returns depth first traversal events in reverse order.
    ///
    /// ```
    /// # use dendron::{Node, tree_node};
    /// # use dendron::traverse::DftEvent;
    /// # let root = tree_node! {
    /// #     "root", [
    /// #         "0",
    /// #         "1",
    /// #         /("2", [
    /// #             "2-0",
    /// #             "2-1",
    /// #         ]),
    /// #     ]
    /// # };
    /// let events = root.depth_first_traverse()
    ///     .map(|ev| ev.map(|node| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    /// let mut reverse_events = root.depth_first_reverse_traverse()
    ///     .map(|ev| ev.map(|node| *node.borrow_data()))
    ///     .collect::<Vec<_>>();
    ///
    /// reverse_events.reverse();
    /// assert_eq!(events, reverse_events);
    /// ```
    #[inline]
    #[must_use]
    pub fn depth_first_reverse_traverse(&self) -> traverse::ReverseDepthFirstTraverser<T> {
        traverse::ReverseDepthFirstTraverser::with_start(Some(self.clone()))
    }

    /// Returns the children traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    /// use dendron::traverse::DftEvent;
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         "0",
    ///         "1",
    ///         /("2", [
    ///             "2-0",
    ///             "2-1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let children = root.children()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(children, &["0", "1", "2"]);
    /// ```
    #[inline]
    #[must_use]
    pub fn children(&self) -> traverse::SiblingsTraverser<T> {
        traverse::SiblingsTraverser::new(self.first_child())
    }

    /// Returns the reverse children traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    /// use dendron::traverse::DftEvent;
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         "0",
    ///         "1",
    ///         /("2", [
    ///             "2-0",
    ///             "2-1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let children = root.children_reverse()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(children, &["2", "1", "0"]);
    /// ```
    #[inline]
    #[must_use]
    pub fn children_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        traverse::ReverseSiblingsTraverser::new(self.last_child())
    }

    /// Returns the ancestors traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let ancestors = child1_0.ancestors()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(ancestors, &["1", "root"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn ancestors(&self) -> traverse::AncestorsTraverser<T> {
        let mut iter = self.ancestors_or_self();
        iter.next();
        iter
    }

    /// Returns the ancestors traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let ancestors_or_self = child1_0.ancestors_or_self()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(ancestors_or_self, &["1-0", "1", "root"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self) -> traverse::AncestorsTraverser<T> {
        traverse::AncestorsTraverser::new(Some(self.clone()))
    }

    /// Returns the siblings traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let siblings = child1.siblings()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(siblings, &["0", "1", "2"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[must_use]
    pub fn siblings(&self) -> traverse::SiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children(),
            None => self.following_siblings_or_self(),
        }
    }

    /// Returns the reverse siblings traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let siblings = child1.siblings_reverse()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(siblings, &["2", "1", "0"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[must_use]
    pub fn siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children_reverse(),
            None => self.preceding_siblings_or_self_reverse(),
        }
    }

    /// Returns the reverse preceding siblings traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let siblings = child1.preceding_siblings_or_self_reverse()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(siblings, &["1", "0"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        traverse::ReverseSiblingsTraverser::new(Some(self.clone()))
    }

    /// Returns the reverse preceding siblings traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let siblings = child1.preceding_siblings_reverse()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(siblings, &["0"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn preceding_siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        let mut iter = self.preceding_siblings_or_self_reverse();
        iter.next();
        iter
    }

    /// Returns the following siblings traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let siblings = child1.following_siblings_or_self()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(siblings, &["1", "2"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self) -> traverse::SiblingsTraverser<T> {
        traverse::SiblingsTraverser::new(Some(self.clone()))
    }

    /// Returns the following siblings traverser.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let siblings = child1.following_siblings()
    ///     .map(|node| *node.borrow_data())
    ///     .collect::<Vec<_>>();
    /// assert_eq!(siblings, &["2"]);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn following_siblings(&self) -> traverse::SiblingsTraverser<T> {
        let mut iter = self.following_siblings_or_self();
        iter.next();
        iter
    }
}

/// Node creation and hierarchy modification.
impl<T> Node<T> {
    /// Creates and returns a new node as the root of a new tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// ```
    #[must_use]
    pub fn new_tree(root_data: T) -> Self {
        let weak_membership = WeakMembership::new();
        let intra_link = NodeBuilder {
            data: root_data,
            parent: Default::default(),
            first_child: Default::default(),
            next_sibling: Default::default(),
            prev_sibling_cyclic: Default::default(),
            membership: weak_membership.clone(),
            num_children: 0,
        }
        .build_link();

        let weak_link = intra_link.downgrade();
        intra_link.replace_prev_sibling_cyclic(weak_link);

        let tree_core_rc = TreeCore::new_rc(intra_link.clone());

        Self::with_link_and_membership(
            intra_link,
            weak_membership.initialize_membership(tree_core_rc),
        )
    }

    /// Detaches the node and its descendant from the current tree, and let it be another tree.
    ///
    /// Detaching the root node does nothing, but valid `grant` should be
    /// passed even in this case.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Failures
    ///
    /// Fails if the resulting hierarchy will be invalid as a tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// let child1_1 = child1.create_as_last_child(&grant, "1-1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   |-- 1-0
    /// //  |   `-- 1-1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// child1.detach_subtree(&grant);
    /// //  root
    /// //  |-- 0
    /// //  `-- 2
    /// //      `-- 2-0
    /// //  1
    /// //  |-- 1-0
    /// //  `-- 1-1
    ///
    /// // Nodes in the detached subtree is now part of another tree.
    /// assert!(!child1.root().ptr_eq(&root));
    /// assert!(!root.belongs_to_same_tree(&child1));
    /// assert!(!root.belongs_to_same_tree(&child1_0));
    /// assert!(!root.belongs_to_same_tree(&child1_1));
    /// assert_eq!(
    ///     root,
    ///     tree_node! {
    ///         "root", [
    ///             "0",
    ///             /("2", ["2-0"]),
    ///         ]
    ///     }
    /// );
    ///
    /// // Hierarchy of subtree is preserved.
    /// assert!(child1.belongs_to_same_tree(&child1_0));
    /// assert!(child1.belongs_to_same_tree(&child1_1));
    /// assert_eq!(
    ///     child1,
    ///     tree_node! {
    ///         "1", [
    ///             "1-0",
    ///             "1-1",
    ///         ]
    ///     }
    /// );
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn detach_subtree(&self, grant: &HierarchyEditGrant<T>) {
        grant.panic_if_invalid_for_node(self);

        edit::detach_subtree(&self.intra_link);
    }

    /// Creates a node as the specified neighbor of `self`, and returns the new node.
    ///
    /// # Failures
    ///
    /// Fails if creation of a node at the specified position will make the tree
    /// hierarchy invalid.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Examples
    ///
    /// ## `AdoptAs::FirstChild`
    ///
    /// ```
    /// use dendron::{AdoptAs, Node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1
    ///     .try_create_node_as(&grant, "new", AdoptAs::FirstChild)
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      |-- new
    /// //      `-- 1-0
    ///
    /// assert!(child1.first_child().expect("has children").ptr_eq(&new));
    /// assert!(child1_0.prev_sibling().expect("has a sibling").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    ///
    /// ## `AdoptAs::LastChild`
    ///
    /// ```
    /// use dendron::{AdoptAs, Node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1
    ///     .try_create_node_as(&grant, "new", AdoptAs::LastChild)
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      |-- 1-0
    /// //      `-- new
    ///
    /// assert!(child1.last_child().expect("has children").ptr_eq(&new));
    /// assert!(child1_0.next_sibling().expect("has a sibling").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    ///
    /// ## `AdoptAs::PreviousSibling`
    ///
    /// ```
    /// use dendron::{AdoptAs, Node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1
    ///     .try_create_node_as(&grant, "new", AdoptAs::PreviousSibling)
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  |-- new
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// assert!(child0.next_sibling().expect("has siblings").ptr_eq(&new));
    /// assert!(child1.prev_sibling().expect("has siblings").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    ///
    /// ## `AdoptAs::NextSibling`
    ///
    /// ```
    /// use dendron::{AdoptAs, Node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1
    ///     .try_create_node_as(&grant, "new", AdoptAs::NextSibling)
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- new
    ///
    /// assert!(root.last_child().expect("has children").ptr_eq(&new));
    /// assert!(child1.next_sibling().expect("has siblings").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn try_create_node_as(
        &self,
        grant: &HierarchyEditGrant<T>,
        data: T,
        dest: AdoptAs,
    ) -> Result<Self, HierarchyError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_node_as(&self.intra_link, self.membership.tree_core(), data, dest)
    }

    /// Creates a node as the specified neighbor of `self`, and returns the new node.
    ///
    /// See [`try_create_node_as`][`Self::try_create_node_as`] for usage
    /// examples.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the hierarchy edit grant is not valid for the given node, or
    /// * creation of a node at the specified position will make the tree
    ///   hierarchy invalid.
    #[inline]
    pub fn create_node_as(&self, grant: &HierarchyEditGrant<T>, data: T, dest: AdoptAs) -> Self {
        self.try_create_node_as(grant, data, dest)
            .expect("[precondition] hierarchy to be created should be valid")
    }

    /// Creates a node as the first child of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1.create_as_first_child(&grant, "new");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      |-- new
    /// //      `-- 1-0
    ///
    /// assert!(child1.first_child().expect("has children").ptr_eq(&new));
    /// assert!(child1_0.prev_sibling().expect("has a sibling").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn create_as_first_child(&self, grant: &HierarchyEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_first_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the last child of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1.create_as_last_child(&grant, "new");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      |-- 1-0
    /// //      `-- new
    ///
    /// assert!(child1.last_child().expect("has children").ptr_eq(&new));
    /// assert!(child1_0.next_sibling().expect("has a sibling").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn create_as_last_child(&self, grant: &HierarchyEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_last_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`HierarchyError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1.try_create_as_prev_sibling(&grant, "new")
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  |-- new
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// assert!(child0.next_sibling().expect("has siblings").ptr_eq(&new));
    /// assert!(child1.prev_sibling().expect("has siblings").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn try_create_as_prev_sibling(
        &self,
        grant: &HierarchyEditGrant<T>,
        data: T,
    ) -> Result<Self, HierarchyError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_as_prev_sibling(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// See [`try_create_as_prev_sibling`][`Self::try_create_as_prev_sibling`]
    /// for usage examples.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// - the hierarchy edit grant is not valid for the given node, or
    /// - `self` is a root node.
    #[inline]
    pub fn create_as_prev_sibling(&self, grant: &HierarchyEditGrant<T>, data: T) -> Self {
        self.try_create_as_prev_sibling(grant, data)
            .expect("[precondition] hierarchy to be created should be valid")
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`HierarchyError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let new = child1.try_create_as_next_sibling(&grant, "new")
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   `-- 1-0
    /// //  `-- new
    ///
    /// assert!(root.last_child().expect("has children").ptr_eq(&new));
    /// assert!(child1.next_sibling().expect("has siblings").ptr_eq(&new));
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn try_create_as_next_sibling(
        &self,
        grant: &HierarchyEditGrant<T>,
        data: T,
    ) -> Result<Self, HierarchyError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_as_next_sibling(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// See [`try_create_as_next_sibling`][`Self::try_create_as_next_sibling`]
    /// for usage examples.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// - the hierarchy edit grant is not valid for the given node, or
    /// - `self` is a root node.
    #[inline]
    pub fn create_as_next_sibling(&self, grant: &HierarchyEditGrant<T>, data: T) -> Self {
        self.try_create_as_next_sibling(grant, data)
            .expect("[precondition] hierarchy to be created should be valid")
    }

    /// Creates a new node that interrupts between `self` and the parent.
    ///
    /// If `self` was the root, the new node will become a new root of the tree
    /// and `self` will be only child of the new root.
    ///
    /// Before:
    ///
    /// ```text
    /// root
    /// `-- this
    ///     |-- child0
    ///     |-- child1
    ///     `-- child2
    /// ```
    ///
    /// After `self.create_as_interrupting_parent`:
    ///
    /// ```text
    /// root
    /// `-- this
    ///     `-- new
    ///         |-- child0
    ///         |-- child1
    ///         `-- child2
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{tree_node, Node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let _prev = root.create_as_last_child(&grant, "prev");
    /// let this = root.create_as_last_child(&grant, "this");
    /// let _child0 = this.create_as_last_child(&grant, "child0");
    /// let _child1 = this.create_as_last_child(&grant, "child1");
    /// let _child2 = this.create_as_last_child(&grant, "child2");
    /// let _next = root.create_as_last_child(&grant, "next");
    /// //  root
    /// //  |-- prev
    /// //  |-- this
    /// //  |   |-- child0
    /// //  |   |-- child1
    /// //  |   `-- child2
    /// //  `-- next
    ///
    /// let new = this.create_as_interrupting_parent(&grant, "new");
    ///
    /// //  root
    /// //  |-- prev
    /// //  |-- new
    /// //  |   `-- this
    /// //  |       |-- child0
    /// //  |       |-- child1
    /// //  |       `-- child2
    /// //  `-- next
    /// let expected = tree_node! {
    ///     "root", [
    ///         "prev",
    ///         /("new", [
    ///             /("this", [
    ///                 "child0",
    ///                 "child1",
    ///                 "child2",
    ///             ]),
    ///         ]),
    ///         "next",
    ///     ]
    /// };
    ///
    /// assert_eq!(root, expected);
    /// assert!(root.root().ptr_eq(&root));
    ///
    /// assert!(new.first_child().unwrap().ptr_eq(&this));
    /// assert!(this.parent().unwrap().ptr_eq(&new));
    ///
    /// assert_eq!(new.num_children(), 1, "`this`");
    /// assert_eq!(this.num_children(), 3, "`child0`, `child1`, and `child2`");
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    ///
    /// If `self` is a root:
    ///
    /// ```
    /// use dendron::{tree_node, Node};
    ///
    /// let this = Node::new_tree("this");
    /// let grant = this.tree().grant_hierarchy_edit()?;
    /// let _child0 = this.create_as_last_child(&grant, "child0");
    /// let _child1 = this.create_as_last_child(&grant, "child1");
    /// //  this
    /// //  |-- child0
    /// //  `-- child1
    ///
    /// let new = this.create_as_interrupting_parent(&grant, "new");
    ///
    /// //  new
    /// //  `-- this
    /// //      |-- child0
    /// //      `-- child1
    /// let expected = tree_node! {
    ///     "new", [
    ///         /("this", [
    ///             "child0",
    ///             "child1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// assert_eq!(new, expected);
    /// assert!(this.root().ptr_eq(&new));
    ///
    /// assert!(new.first_child().unwrap().ptr_eq(&this));
    /// assert!(this.parent().unwrap().ptr_eq(&new));
    ///
    /// assert_eq!(new.num_children(), 1, "`this`");
    /// assert_eq!(this.num_children(), 2, "`child0` and `child1`");
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn create_as_interrupting_parent(&self, grant: &HierarchyEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_interrupting_parent(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a new node that interrupts between `self` and the children.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{tree_node, Node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let _prev = root.create_as_last_child(&grant, "prev");
    /// let this = root.create_as_last_child(&grant, "this");
    /// let _child0 = this.create_as_last_child(&grant, "child0");
    /// let _child1 = this.create_as_last_child(&grant, "child1");
    /// let _child2 = this.create_as_last_child(&grant, "child2");
    /// let _next = root.create_as_last_child(&grant, "next");
    /// //  root
    /// //  |-- prev
    /// //  |-- this
    /// //  |   |-- child0
    /// //  |   |-- child1
    /// //  |   `-- child2
    /// //  `-- next
    ///
    /// let new = this.create_as_interrupting_child(&grant, "new");
    ///
    /// //  root
    /// //  |-- prev
    /// //  |-- this
    /// //  |   `-- new
    /// //  |       |-- child0
    /// //  |       |-- child1
    /// //  |       `-- child2
    /// //  `-- next
    /// let expected = tree_node! {
    ///     "root", [
    ///         "prev",
    ///         /("this", [
    ///             /("new", [
    ///                 "child0",
    ///                 "child1",
    ///                 "child2",
    ///             ]),
    ///         ]),
    ///         "next",
    ///     ]
    /// };
    ///
    /// assert_eq!(root, expected);
    /// assert!(root.root().ptr_eq(&root));
    ///
    /// assert!(this.first_child().unwrap().ptr_eq(&new));
    /// assert!(new.parent().unwrap().ptr_eq(&this));
    ///
    /// assert_eq!(new.num_children(), 3, "`child0`, `child1`, and `child2`");
    /// assert_eq!(this.num_children(), 1, "`new`");
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn create_as_interrupting_child(&self, grant: &HierarchyEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_interrupting_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Inserts the children at the position of the node, and detach the node.
    ///
    /// `self` will become the root of a new single-node tree.
    ///
    /// Before:
    ///
    /// ```text
    /// parent
    /// |-- prev
    /// |-- self
    /// |   |-- child0
    /// |   |   `-- grandchild0-0
    /// |   `-- child1
    /// `-- next
    /// ```
    ///
    /// After `self.try_replace_with_children()`:
    ///
    /// ```text
    /// parent
    /// |-- prev
    /// |-- child0
    /// |   `-- grandchild0-0
    /// |-- child1
    /// `-- next
    ///
    /// self (detached)
    /// ```
    ///
    /// # Failures
    ///
    /// Fails if:
    ///
    /// * the node is the root and has multiple children, or
    ///     + In this case, [`HierarchyError::SiblingsWithoutParent`] error is returned.
    /// * the node is the root and has no children.
    ///     + In this case, [`HierarchyError::EmptyTree`] error is returned.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    #[inline]
    pub fn try_replace_with_children(
        &self,
        grant: &HierarchyEditGrant<T>,
    ) -> Result<(), HierarchyError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_replace_with_children(&self.intra_link, &self.membership.tree_core())
    }

    /// Inserts the children at the position of the node, and detach the node.
    ///
    /// `self` will become the root of a new single-node tree.
    ///
    /// See [`try_replace_with_children`][`Self::try_replace_with_children`]
    /// method.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the hierarchy edit grant is not valid for the given node,
    /// * the node is the root and has multiple children, or
    /// * the node is the root and has no children.
    #[inline]
    pub fn replace_with_children(&self, grant: &HierarchyEditGrant<T>) {
        self.try_replace_with_children(grant)
            .expect("[precondition] the hierarchy to be created should be valid")
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    // No grant is required because this operation is read-only for this tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    ///
    /// let cloned = child1.try_clone_subtree()
    ///     .expect("data are currently not borrowed");
    /// //  root
    /// //  |-- 0
    /// //  `-- 1
    /// //      `-- 1-0
    /// //  1
    /// //  `-- 1-0
    ///
    /// // Cloned subtree is independent tree.
    /// assert!(!cloned.belongs_to_same_tree(&root));
    /// // Descendants are also cloned.
    /// assert_eq!(cloned, child1);
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    pub fn try_clone_subtree(&self) -> Result<Self, BorrowError>
    where
        T: Clone,
    {
        // NOTE: Can be made simpler by nightly Rust.
        // `Iterator::try_collect()` is not yet stabilized as of Rust 1.60.0.
        // See <https://github.com/rust-lang/rust/issues/94047>.
        //self.to_events()
        //    .try_collect::<Result<Self, TreeBuildError>>()?
        //    .map_err(|e| match e {
        //        TreeBuildError::BorrowData(e) => e,
        //        TreeBuildError::RootNotOpened | TreeBuildError::RootClosed => {
        //            unreachable!("[validity] subtree should be consistently serializable")
        //        }
        //    })

        self.to_events()
            .try_fold(serial::TreeBuilder::new(), |mut builder, ev_res| {
                builder.push_event(ev_res?)?;
                Ok(builder)
            })
            .and_then(|builder| builder.finish())
            .map_err(|e| match e {
                TreeBuildError::BorrowData(e) => e,
                TreeBuildError::RootNotOpened | TreeBuildError::RootClosed => {
                    unreachable!("[validity] subtree should be consistently serializable")
                }
            })
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// # Panics
    ///
    /// Panics if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    #[inline]
    #[must_use]
    pub fn clone_subtree(&self) -> Self
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
    /// Fails if:
    ///
    /// * the hierarchy to be created is invalid, or
    /// * any data associated to the node in the subtree is mutably (i.e.
    ///   exclusively) borrowed.
    ///     + Returns [`BorrowNodeData`][`HierarchyError::BorrowNodeData`] in
    ///       this case.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{InsertAs, Node, tree_node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let node0 = root.create_as_last_child(&grant, "0");
    /// let node1 = root.create_as_last_child(&grant, "1");
    /// let node1_0 = node1.create_as_last_child(&grant, "1-0");
    /// let node1_0_0 = node1_0.create_as_last_child(&grant, "1-0-0");
    /// let node1_1 = node1.create_as_last_child(&grant, "1-1");
    /// let node2 = root.create_as_last_child(&grant, "2");
    /// let node2_0 = node2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   |-- 1-0
    /// //  |   |   `-- 1-0-0
    /// //  |   `-- 1-1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let node2_0_hot = node2_0.bundle_hierarchy_edit_grant(&grant);
    /// let cloned = node1
    ///     .try_clone_insert_subtree(InsertAs::PreviousSiblingOf(&node2_0_hot))
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   |-- 1-0
    /// //  |   |   `-- 1-0-0
    /// //  |   `-- 1-1
    /// //  `-- 2
    /// //      |-- 1
    /// //      |   |-- 1-0
    /// //      |   |   `-- 1-0-0
    /// //      |   `-- 1-1
    /// //      `-- 2-0
    ///
    /// assert!(!cloned.plain().ptr_eq(&node1));
    /// // Cloned node belongs to the same tree.
    /// assert!(cloned.plain().belongs_to_same_tree(&node1));
    ///
    /// assert_eq!(
    ///     root,
    ///     tree_node! {
    ///         "root", [
    ///             "0",
    ///             /("1", [
    ///                 /("1-0", ["1-0-0"]),
    ///                 "1-1",
    ///             ]),
    ///             /("2", [
    ///                 /("1", [
    ///                     /("1-0", ["1-0-0"]),
    ///                     "1-1",
    ///                 ]),
    ///                 "2-0"
    ///             ]),
    ///         ]
    ///     }
    /// );
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    pub fn try_clone_insert_subtree(
        &self,
        dest: InsertAs<&HotNode<T>>,
    ) -> Result<HotNode<T>, HierarchyError>
    where
        T: Clone,
    {
        edit::try_clone_insert_subtree(self, dest)
    }

    /// Clones the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the cloned new subtree.
    ///
    /// See [`try_clone_insert_subtree`][`Self::try_clone_insert_subtree`]
    /// for detail.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the hierarchy to be created is invalid, or
    /// * any data associated to the node in the subtree is mutably (i.e.
    ///   exclusively) borrowed.
    #[inline]
    // This modifies hierarchy of the destination of the tree, so the returned
    // value is not necessarily used.
    #[allow(clippy::must_use_candidate)]
    pub fn clone_insert_subtree(&self, dest: InsertAs<&HotNode<T>>) -> HotNode<T>
    where
        T: Clone,
    {
        self.try_clone_insert_subtree(dest).expect(
            "[precondition] the hierarchy to be created should be valid \
             and the node data should be borrowable",
        )
    }

    /// Detaches the node with its subtree, and inserts it to the given destination.
    ///
    /// # Failures
    ///
    /// Fails if the node (being moved) is an ancestor of the destination.
    ///
    /// # Panics
    ///
    /// Panics if the hierarchy edit grant is not valid for the given node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{InsertAs, Node, tree_node};
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let node0 = root.create_as_last_child(&grant, "0");
    /// let node1 = root.create_as_last_child(&grant, "1");
    /// let node1_0 = node1.create_as_last_child(&grant, "1-0");
    /// let node1_0_0 = node1_0.create_as_last_child(&grant, "1-0-0");
    /// let node1_1 = node1.create_as_last_child(&grant, "1-1");
    /// let node2 = root.create_as_last_child(&grant, "2");
    /// let node2_0 = node2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   |-- 1-0
    /// //  |   |   `-- 1-0-0
    /// //  |   `-- 1-1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let node2_0_hot = node2_0.bundle_hierarchy_edit_grant(&grant);
    /// node1
    ///     .try_detach_insert_subtree(
    ///         &grant,
    ///         InsertAs::PreviousSiblingOf(&node2_0_hot)
    ///     )
    ///     .expect("creating valid hierarchy");
    /// //  root
    /// //  |-- 0
    /// //  `-- 2
    /// //      |-- 1
    /// //      |   |-- 1-0
    /// //      |   |   `-- 1-0-0
    /// //      |   `-- 1-1
    /// //      `-- 2-0
    ///
    /// assert!(node1.parent().expect("has a parent").ptr_eq(&node2));
    /// // Cloned node belongs to the same tree.
    /// assert!(node1.belongs_to_same_tree(&node2));
    ///
    /// assert_eq!(
    ///     root,
    ///     tree_node! {
    ///         "root", [
    ///             "0",
    ///             /("2", [
    ///                 /("1", [
    ///                     /("1-0", ["1-0-0"]),
    ///                     "1-1",
    ///                 ]),
    ///                 "2-0"
    ///             ]),
    ///         ]
    ///     }
    /// );
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    pub fn try_detach_insert_subtree(
        &self,
        grant: &HierarchyEditGrant<T>,
        dest: InsertAs<&HotNode<T>>,
    ) -> Result<(), HierarchyError> {
        grant.panic_if_invalid_for_node(self);

        if self
            .membership
            .belongs_to_same_tree(dest.anchor().plain_membership())
        {
            // The source and the destination belong to the same tree.
            edit::detach_and_move_inside_same_tree(&self.intra_link, dest.map(HotNode::intra_link))
        } else {
            // The source and the destination belong to the different tree.
            edit::detach_and_move_to_another_tree(
                &self.intra_link,
                dest.map(HotNode::intra_link),
                &dest.anchor().tree_core(),
            )
        }
    }

    /// Detaches the node with its subtree, and inserts it to the given destination.
    ///
    /// See [`Node::try_detach_insert_subtree`] for detail.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// * the hierarchy edit grant is not valid for the given node, or
    /// * the node (being moved) is an ancestor of the destination.
    #[inline]
    pub fn detach_insert_subtree(
        &self,
        grant: &HierarchyEditGrant<T>,
        dest: InsertAs<&HotNode<T>>,
    ) {
        self.try_detach_insert_subtree(grant, dest).expect(
            "[precondition] the node being moved should not be an ancestor of the destination",
        )
    }
}

/// Comparison.
impl<T> Node<T> {
    /// Compares two subtrees.
    ///
    /// Returns `Ok(true)` if the two subtree are equal, even if they are stored
    /// in different allocation.
    ///
    /// # Failures
    ///
    /// May return `Err(_)` if associated data of some nodes are already
    /// borrowed exclusively (i.e. mutably).
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{tree_node, Node};
    ///
    /// //  root
    /// //  |-- 0
    /// //  |   |-- 0-0
    /// //  |   `-- 0-1
    /// //  |       `-- 0-1-0
    /// //  `-- 1
    /// let node1: Node<&'static str> = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             "0-0",
    ///             /("0-1", [
    ///                 "0-1-0",
    ///             ]),
    ///         ]),
    ///         "1",
    ///     ]
    /// };
    ///
    /// //  0
    /// //  |-- 0-0
    /// //  `-- 0-1
    /// //      `-- 0-1-0
    /// let node2: Node<String> = tree_node! {
    ///     "0".to_owned(), [
    ///         "0-0".into(),
    ///         /("0-1".into(), [
    ///             "0-1-0".into(),
    ///         ]),
    ///     ]
    /// };
    ///
    /// assert!(
    ///     !node1.try_eq(&node2).expect("data are not borrowed"),
    ///     "node1 and node2 are not equal"
    /// );
    ///
    /// let node1_first_child = node1.first_child().expect("node1 has a child");
    /// assert!(
    ///     node1_first_child.try_eq(&node2).expect("data are not borrowed"),
    ///     "the first child of node1 and node2 are equal"
    /// );
    /// ```
    #[inline]
    pub fn try_eq<U>(&self, other: &Node<U>) -> Result<bool, BorrowError>
    where
        T: PartialEq<U>,
    {
        self.intra_link.try_eq(&other.intra_link)
    }
}

/// Serialization.
impl<T: Clone> Node<T> {
    /// Returns an iterator of serialized events for the subtree.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::Node;
    /// use dendron::serial::Event;
    ///
    /// let root = Node::new_tree("root");
    /// let grant = root.tree().grant_hierarchy_edit()?;
    /// let child0 = root.create_as_last_child(&grant, "0");
    /// let child1 = root.create_as_last_child(&grant, "1");
    /// let child1_0 = child1.create_as_last_child(&grant, "1-0");
    /// let child1_1 = child1.create_as_last_child(&grant, "1-1");
    /// let child2 = root.create_as_last_child(&grant, "2");
    /// let child2_0 = child2.create_as_last_child(&grant, "2-0");
    /// //  root
    /// //  |-- 0
    /// //  |-- 1
    /// //  |   |-- 1-0
    /// //  |   `-- 1-1
    /// //  `-- 2
    /// //      `-- 2-0
    ///
    /// let events = root.to_events()
    ///     .collect::<Result<Vec<_>, _>>()
    ///     .expect("data are not exclusively borrowed now");
    /// assert_eq!(
    ///     events,
    ///     &[
    ///         Event::Open("root"),
    ///         Event::Open("0"),
    ///         // Close `1`.
    ///         Event::Close(1),
    ///         Event::Open("1"),
    ///         Event::Open("1-0"),
    ///         // Close `1-0`.
    ///         Event::Close(1),
    ///         Event::Open("1-1"),
    ///         // Close `1-1` and `2`.
    ///         Event::Close(2),
    ///         Event::Open("2"),
    ///         Event::Open("2-0"),
    ///         // Close `2-0`, `2`, and `root`.
    ///         Event::Close(3),
    ///     ]
    /// );
    /// # Ok::<_, dendron::tree::HierarchyEditGrantError>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn to_events(&self) -> serial::TreeSerializeIter<T> {
        serial::TreeSerializeIter::new(self)
    }
}

/// Debug printing.
impl<T> Node<T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    ///
    /// # (No) guarantees
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::tree_node;
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             "0\n0",
    ///             "0\n1",
    ///         ]),
    ///         "1",
    ///         /("2", [
    ///             /("2\n0", [
    ///                 "2\n0\n0",
    ///             ])
    ///         ]),
    ///     ]
    /// };
    ///
    /// let printable = root.debug_pretty_print();
    ///
    /// let expected_debug = r#""root"
    /// |-- "0"
    /// |   |-- "0\n0"
    /// |   `-- "0\n1"
    /// |-- "1"
    /// `-- "2"
    ///     `-- "2\n0"
    ///         `-- "2\n0\n0""#;
    /// assert_eq!(format!("{:?}", printable), expected_debug);
    ///
    /// let expected_display = r#"root
    /// |-- 0
    /// |   |-- 0
    /// |   |   0
    /// |   `-- 0
    /// |       1
    /// |-- 1
    /// `-- 2
    ///     `-- 2
    ///         0
    ///         `-- 2
    ///             0
    ///             0"#;
    /// assert_eq!(printable.to_string(), expected_display);
    /// ```
    #[inline]
    #[must_use]
    pub fn debug_pretty_print(&self) -> DebugPrettyPrint<'_, T> {
        DebugPrettyPrint::new(&self.intra_link)
    }

    /// Returns a debug-printable proxy that does not dump neighbor nodes.
    ///
    /// # (No) guarantees
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             "0-0",
    ///             "0-1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let printable = root.debug_print_local();
    ///
    /// println!("default oneliner = {:?}", printable);
    /// println!("alternate multiline = {:#?}", printable);
    /// ```
    #[inline]
    #[must_use]
    pub fn debug_print_local(&self) -> DebugPrintNodeLocal<'_, T> {
        DebugPrintNodeLocal::new_plain(&self.intra_link, &self.membership)
    }

    /// Returns a debug-printable proxy that dumps descendant nodes.
    ///
    /// # (No) guarantees
    ///
    /// This is provided mainly for debugging purpose. Node that the output
    /// format is not guaranteed to be stable, and any format changes won't be
    /// considered as breaking changes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dendron::{Node, tree_node};
    ///
    /// let root = tree_node! {
    ///     "root", [
    ///         /("0", [
    ///             "0-0",
    ///             "0-1",
    ///         ]),
    ///     ]
    /// };
    ///
    /// let printable = root.debug_print_subtree();
    ///
    /// println!("default oneliner = {:?}", printable);
    /// println!("alternate multiline = {:#?}", printable);
    /// ```
    #[inline]
    #[must_use]
    pub fn debug_print_subtree(&self) -> DebugPrintSubtree<'_, T> {
        DebugPrintSubtree::new_plain(&self.intra_link, &self.membership)
    }
}

/// A shared weak reference to a node.
pub struct NodeWeak<T> {
    /// Target node core.
    // Node core contains `WeakMembership` internally, so no need to have a
    // copy of it.
    intra_link: IntraTreeLinkWeak<T>,
}

impl<T> Clone for NodeWeak<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for NodeWeak<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.upgrade() {
            Some(node) => f
                .debug_tuple("NodeWeak")
                .field(&node.debug_print_local())
                .finish(),
            None => f.write_str("NodeWeak(<dropped>)"),
        }
    }
}

impl<T> NodeWeak<T> {
    /// Attempts to upgrade the weak reference of a node to a `Node`.
    ///
    /// Returns `None` if the target node is already dropped.
    ///
    /// ```
    /// use dendron::Node;
    ///
    /// let root = Node::new_tree("root");
    /// let root_weak = root.downgrade();
    /// assert!(root_weak.upgrade().is_some());
    ///
    /// drop(root);
    /// assert!(root_weak.upgrade().is_none());
    /// ```
    #[must_use]
    pub fn upgrade(&self) -> Option<Node<T>> {
        let intra_link = self.intra_link.upgrade()?;
        let membership = intra_link.membership().upgrade().expect(
            "[consistency] the membership must be alive since \
             the corresponding node link is alive",
        );
        Some(Node {
            intra_link,
            membership,
        })
    }
}
