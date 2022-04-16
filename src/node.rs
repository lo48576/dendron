//! Node.

mod debug_print;
mod edit;
mod frozen;
mod hot;
mod internal;

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::{Rc, Weak};

use crate::anchor::{AdoptAs, InsertAs};
use crate::membership::{Membership, WeakMembership};
use crate::serial::{self, TreeBuildError};
use crate::traverse;
use crate::tree::{
    StructureEditGrant, StructureEditGrantError, StructureEditProhibition,
    StructureEditProhibitionError, Tree, TreeCore,
};

pub use self::debug_print::DebugPrettyPrint;
pub use self::frozen::FrozenNode;
pub use self::hot::HotNode;
pub(crate) use self::internal::IntraTreeLink;
use self::internal::{IntraTreeLinkWeak, NodeBuilder, NumChildren};

/// Structure modification error.
// `From<BorrowError> for Self` is not implemented because the crate should not
// allow users to convert any `BorrowError` into this error, especially when
// user-provided `BorrowError` is unrelated to the structure modification.
#[derive(Debug)]
#[non_exhaustive]
pub enum StructureError {
    /// Attempt to make a node its own descendant or ancestor.
    AncestorDescendantLoop,
    /// Attempt to make a tree empty.
    ///
    /// A tree must have at least one node (the root node), so it cannot be empty.
    EmptyTree,
    /// Attempt to make a node the sibling of the root node.
    SiblingsWithoutParent,
    /// Failed to borrow node data.
    BorrowNodeData(BorrowError),
}

impl fmt::Display for StructureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match *self {
            Self::AncestorDescendantLoop => "attempt to make a node its own descendant or ancestor",
            Self::EmptyTree => "attempt to make a tree empty",
            Self::SiblingsWithoutParent => "attempt to make a node sibling of the root node",
            Self::BorrowNodeData(_) => "failed to borrow the data associated to the node",
        };
        f.write_str(msg)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for StructureError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BorrowNodeData(e) => Some(e),
            _ => None,
        }
    }
}

/// A shared owning reference to a node.
pub struct Node<T> {
    /// Target node core.
    intra_link: IntraTreeLink<T>,
    /// Membership of a node with ownership of the tree.
    membership: Membership<T>,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            intra_link: self.intra_link.clone(),
            membership: self.membership.clone(),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("data", &self.intra_link.try_borrow_data())
            .field("next_sibling", &self.intra_link.next_sibling_link())
            .field("first_child", &self.intra_link.first_child_link())
            .field("membership", &self.membership)
            .finish()
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
}

/// Tree structure edit grants and prohibitions.
impl<T> Node<T> {
    /// Returns the [`FrozenNode`], a node with tree structure edit prohibition bundled.
    #[inline]
    pub fn bundle_new_structure_edit_prohibition(
        self,
    ) -> Result<FrozenNode<T>, StructureEditProhibitionError> {
        FrozenNode::from_node(self)
    }

    /// Returns the [`HotNode`], a node with tree structure edit grant bundled.
    #[inline]
    pub fn bundle_new_structure_edit_grant(self) -> Result<HotNode<T>, StructureEditGrantError> {
        HotNode::from_node(self)
    }

    /// Returns the [`FrozenNode`], a node with tree structure edit prohibition bundled.
    ///
    /// # Panics
    ///
    /// Panics if the structure prohibition grant is not valid for the given node.
    #[inline]
    #[must_use]
    pub fn bundle_structure_edit_prohibition(
        self,
        prohibition: StructureEditProhibition<T>,
    ) -> FrozenNode<T> {
        FrozenNode::from_node_and_prohibition(self, prohibition)
    }

    /// Returns the [`HotNode`], a node with tree structure edit grant bundled.
    ///
    /// # Panics
    ///
    /// Panics if the structure edit grant is not valid for the given node.
    #[inline]
    #[must_use]
    pub fn bundle_structure_edit_grant(self, grant: StructureEditGrant<T>) -> HotNode<T> {
        HotNode::from_node_and_grant(self, grant)
    }
}

// Common methods below.

/// Data access.
impl<T> Node<T> {
    /// Returns a reference to the data associated to the node.
    #[inline]
    pub fn try_borrow_data(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.intra_link.try_borrow_data()
    }

    /// Returns a reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub fn borrow_data(&self) -> Ref<'_, T> {
        self.intra_link.borrow_data()
    }

    /// Returns a mutable reference to the data associated to the node.
    #[inline]
    pub fn try_borrow_data_mut(&self) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.intra_link.try_borrow_data_mut()
    }

    /// Returns a mutable reference to the data associated to the node.
    ///
    /// # Panics
    ///
    /// Panics if the data is already mutably borrowed.
    #[inline]
    #[must_use]
    pub fn borrow_data_mut(&self) -> RefMut<'_, T> {
        self.intra_link.borrow_data_mut()
    }

    /// Returns `true` if the two `Node`s point to the same allocation.
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
    #[inline]
    #[must_use]
    pub fn tree(&self) -> Tree<T> {
        Tree::from_core_rc(self.membership.tree_core())
    }

    /// Returns true if the given node belong to the same tree.
    #[inline]
    #[must_use]
    pub fn belongs_to_same_tree(&self, other: &Self) -> bool {
        self.membership.belongs_to_same_tree(&other.membership)
    }

    /// Returns true if the node is the root.
    #[inline]
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
    }

    /// Returns the root node.
    #[inline]
    #[must_use]
    pub fn root(&self) -> Self {
        Self::with_link(self.membership.tree_core().root_link())
    }

    /// Returns the parent node.
    #[inline]
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.intra_link.parent_link().map(Self::with_link)
    }

    /// Returns the previous sibling.
    #[inline]
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        self.intra_link.prev_sibling_link().map(Self::with_link)
    }

    /// Returns the next sibling.
    #[inline]
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        self.intra_link.next_sibling_link().map(Self::with_link)
    }

    /// Returns the first sibling.
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
    #[inline]
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        self.intra_link.first_child_link().map(Self::with_link)
    }

    /// Returns the last child node.
    #[inline]
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        self.intra_link.last_child_link().map(Self::with_link)
    }

    /// Returns the first and the last child nodes.
    #[must_use]
    pub fn first_last_child(&self) -> Option<(Self, Self)> {
        let (first_link, last_link) = self.intra_link.first_last_child_link()?;
        Some((Self::with_link(first_link), Self::with_link(last_link)))
    }

    /// Returns true if the previous sibling exists.
    #[inline]
    #[must_use]
    pub fn has_prev_sibling(&self) -> bool {
        self.intra_link.has_prev_sibling()
    }

    /// Returns true if the next sibling exists.
    #[inline]
    #[must_use]
    pub fn has_next_sibling(&self) -> bool {
        self.intra_link.has_next_sibling()
    }

    /// Returns true if the node has any children.
    #[inline]
    #[must_use]
    pub fn has_children(&self) -> bool {
        self.intra_link.has_children()
    }

    /// Returns true if the node has just one child.
    #[inline]
    #[must_use]
    pub fn has_one_child(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::One
    }

    /// Returns true if the node has two or more children.
    #[inline]
    #[must_use]
    pub fn has_multiple_children(&self) -> bool {
        self.intra_link.num_children_rough() == NumChildren::TwoOrMore
    }

    /// Returns the number of children.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_children(&self) -> usize {
        self.intra_link.count_children()
    }

    /// Returns the number of preceding siblings.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_preceding_siblings(&self) -> usize {
        self.intra_link.count_preceding_siblings()
    }

    /// Returns the number of following siblings.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_following_siblings(&self) -> usize {
        self.intra_link.count_following_siblings()
    }

    /// Returns the number of ancestors.
    ///
    /// Note that this is O(N) operation.
    #[inline]
    #[must_use]
    pub fn count_ancestors(&self) -> usize {
        self.intra_link.count_ancestors()
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

    /// Returns the ancestors traverser.
    #[inline]
    #[must_use]
    pub fn ancestors(&self) -> traverse::AncestorsTraverser<T> {
        let mut iter = self.ancestors_or_self();
        iter.next();
        iter
    }

    /// Returns the ancestors traverser.
    #[inline]
    #[must_use]
    pub fn ancestors_or_self(&self) -> traverse::AncestorsTraverser<T> {
        traverse::AncestorsTraverser::new(Some(self.clone()))
    }

    /// Returns the siblings traverser.
    #[must_use]
    pub fn siblings(&self) -> traverse::SiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children(),
            None => self.following_siblings_or_self(),
        }
    }

    /// Returns the reverse siblings traverser.
    #[must_use]
    pub fn siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        match self.parent() {
            Some(parent) => parent.children_reverse(),
            None => self.preceding_siblings_or_self_reverse(),
        }
    }

    /// Returns the reverse preceding siblings traverser.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_or_self_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        traverse::ReverseSiblingsTraverser::new(Some(self.clone()))
    }

    /// Returns the reverse preceding siblings traverser.
    #[inline]
    #[must_use]
    pub fn preceding_siblings_reverse(&self) -> traverse::ReverseSiblingsTraverser<T> {
        let mut iter = self.preceding_siblings_or_self_reverse();
        iter.next();
        iter
    }

    /// Returns the following siblings traverser.
    #[inline]
    #[must_use]
    pub fn following_siblings_or_self(&self) -> traverse::SiblingsTraverser<T> {
        traverse::SiblingsTraverser::new(Some(self.clone()))
    }

    /// Returns the following siblings traverser.
    #[inline]
    #[must_use]
    pub fn following_siblings(&self) -> traverse::SiblingsTraverser<T> {
        let mut iter = self.following_siblings_or_self();
        iter.next();
        iter
    }
}

/// Node creation and structure modification.
impl<T> Node<T> {
    /// Creates and returns a new node as the root of a new tree.
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
    #[inline]
    pub fn detach_subtree(&self, grant: StructureEditGrant<T>) {
        grant.panic_if_invalid_for_node(self);

        edit::detach_subtree(&self.intra_link);
    }

    /// Creates a node as the next sibling of `self`, and returns the new node.
    #[inline]
    pub fn try_create_node_as(
        &self,
        grant: StructureEditGrant<T>,
        data: T,
        dest: AdoptAs,
    ) -> Result<Self, StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_node_as(&self.intra_link, self.membership.tree_core(), data, dest)
    }

    /// Creates a node as the first child of `self`.
    #[inline]
    pub fn create_as_first_child(&self, grant: StructureEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_first_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the last child of `self`.
    #[inline]
    pub fn create_as_last_child(&self, grant: StructureEditGrant<T>, data: T) -> Self {
        grant.panic_if_invalid_for_node(self);

        edit::create_as_last_child(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the previous sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_prev_sibling(
        &self,
        grant: StructureEditGrant<T>,
        data: T,
    ) -> Result<Self, StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_as_prev_sibling(&self.intra_link, self.membership.tree_core(), data)
    }

    /// Creates a node as the next sibling of `self`.
    ///
    /// # Failures
    ///
    /// Returns [`StructureError::SiblingsWithoutParent`] as an error if `self`
    /// is a root node.
    #[inline]
    pub fn try_create_as_next_sibling(
        &self,
        grant: StructureEditGrant<T>,
        data: T,
    ) -> Result<Self, StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::try_create_as_next_sibling(&self.intra_link, self.membership.tree_core(), data)
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
    /// After `self.replace_with_children()`:
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
    ///     + In this case, [`StructureError::SiblingsWithoutParent`] error is returned.
    /// * the node is the root and has no children.
    ///     + In this case, [`StructureError::EmptyTree`] error is returned.
    #[inline]
    pub fn replace_with_children(
        &self,
        grant: StructureEditGrant<T>,
    ) -> Result<(), StructureError> {
        grant.panic_if_invalid_for_node(self);

        edit::replace_with_children(&self.intra_link)
    }

    /// Clones the subtree and returns it as a new independent tree.
    ///
    /// # Failures
    ///
    /// Fails if any data associated to the node in the subtree is mutably
    /// (i.e. exclusively) borrowed.
    // No grant is required because this operation is read-only for this tree.
    pub fn clone_subtree(&self) -> Result<Self, BorrowError>
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

    /// Clones the node with its subtree, and inserts it to the given destination.
    ///
    /// Returns the root node of the cloned new subtree.
    ///
    /// # Failures
    ///
    /// Fails with [`BorrowNodeData`][`StructureError::BorrowNodeData`] if any
    /// data associated to the node in the subtree is mutably (i.e. exclusively)
    /// borrowed.
    #[inline]
    pub fn clone_insert_subtree(
        &self,
        dest: InsertAs<HotNode<T>>,
    ) -> Result<HotNode<T>, StructureError>
    where
        T: Clone,
    {
        edit::clone_insert_subtree(self, dest)
    }

    /// Detaches the node with its subtree, and inserts it to the given destination.
    #[inline]
    pub fn detach_insert_subtree(
        &self,
        grant: StructureEditGrant<T>,
        dest: InsertAs<HotNode<T>>,
    ) -> Result<(), StructureError> {
        grant.panic_if_invalid_for_node(self);

        if self
            .membership
            .belongs_to_same_tree(dest.anchor().plain_membership())
        {
            // The source and the destination belong to the same tree.
            edit::detach_and_move_inside_same_tree(
                &self.intra_link,
                dest.as_ref().map(HotNode::intra_link),
            )
        } else {
            // The source and the destination belong to the different tree.
            edit::detach_and_move_to_another_tree(
                &self.intra_link,
                dest.as_ref().map(HotNode::intra_link),
                &dest.anchor().tree_core(),
            )
        }
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
    #[inline]
    #[must_use]
    pub fn to_events(&self) -> serial::TreeSerializeIter<T> {
        serial::TreeSerializeIter::new(self)
    }
}

/// Debug printing.
impl<T> Node<T> {
    /// Returns the pretty-printable proxy object to the node and descendants.
    #[inline]
    #[must_use]
    pub fn debug_pretty_print(&self) -> DebugPrettyPrint<'_, T> {
        DebugPrettyPrint::new(&self.intra_link)
    }
}
