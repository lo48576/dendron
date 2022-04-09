//! Node.

mod frozen;
mod hot;
mod internal;

use core::cell::{BorrowError, BorrowMutError, Ref, RefMut};
use core::fmt;

use alloc::rc::{Rc, Weak};

use crate::membership::{Membership, WeakMembership};
use crate::traverse::{self, DftEvent};
use crate::tree::{
    StructureEditGrant, StructureEditGrantError, StructureEditProhibition,
    StructureEditProhibitionError, Tree, TreeCore,
};
use crate::{AdoptAs, StructureError};

pub use self::frozen::FrozenNode;
pub use self::hot::HotNode;
pub(crate) use self::internal::IntraTreeLink;
use self::internal::{IntraTreeLinkWeak, NodeBuilder};

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

    /// Returns true if the node is the root.
    #[must_use]
    pub fn is_root(&self) -> bool {
        // The node is a root if and only if the node has no parent.
        self.intra_link.is_root()
    }

    /// Returns the root node.
    #[must_use]
    pub fn root(&self) -> Self {
        Self {
            intra_link: self.membership.tree_core().root_link(),
            membership: self.membership.clone(),
        }
    }

    /// Returns the parent node.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.parent_link()?,
            membership: self.membership.clone(),
        })
    }

    /// Returns the previous sibling.
    #[must_use]
    pub fn prev_sibling(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.prev_sibling_link()?,
            membership: self.membership.clone(),
        })
    }

    /// Returns the next sibling.
    #[must_use]
    pub fn next_sibling(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.next_sibling_link()?,
            membership: self.membership.clone(),
        })
    }

    /// Returns the first child node.
    #[must_use]
    pub fn first_child(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.first_child_link()?,
            membership: self.membership.clone(),
        })
    }

    /// Returns the last child node.
    #[must_use]
    pub fn last_child(&self) -> Option<Self> {
        Some(Self {
            intra_link: self.intra_link.last_child_link()?,
            membership: self.membership.clone(),
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
    /// Panics if the membership refers the different tree than the tree the
    /// node link belongs to.
    #[must_use]
    pub(crate) fn with_link_and_membership(
        intra_link: IntraTreeLink<T>,
        membership: Membership<T>,
    ) -> Self {
        if !Membership::ptr_eq_weak(&membership, intra_link.membership()) {
            panic!("[precondition] membership should refer the tree the node link belongs to");
        }

        Self {
            intra_link,
            membership,
        }
    }

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
    pub fn detach_subtree(&self) {
        if self.is_root() {
            // Detaching entire tree is meaningless.
            // Do nothing.
            return;
        }
        // Update the references to the tree core.
        let tree_core_rc = TreeCore::new_rc(self.intra_link.clone());
        self.set_memberships_of_descendants_and_self(&tree_core_rc);

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

        // Update neighbors.
        if let Some(parent_link) = &parent_link {
            if self.intra_link.is_first_sibling() {
                parent_link.replace_first_child(next_sibling_link.clone());
            }
        }
        if let Some(prev_sibling_link) = prev_sibling_link {
            prev_sibling_link.replace_next_sibling(next_sibling_link.clone());
        }
        if let Some(next_sibling_link) = next_sibling_link {
            next_sibling_link.replace_prev_sibling_cyclic(prev_sibling_cyclic_link.downgrade());
        }

        // Update `self`.
        self.intra_link.replace_parent(IntraTreeLinkWeak::default());
        let self_link_weak = self.intra_link.downgrade();
        self.intra_link.replace_prev_sibling_cyclic(self_link_weak);
        self.intra_link.replace_next_sibling(None);
    }

    /// Changes the memberships of the `self` node and its descendants to the given tree.
    fn set_memberships_of_descendants_and_self(&self, tree_core_rc: &Rc<TreeCore<T>>) {
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
            open_link.membership().set_tree_core(tree_core_rc);
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

        let membership = Membership::create_new_membership(self.membership.tree_core());
        let intra_link = NodeBuilder {
            data,
            parent: self.intra_link.downgrade(),
            first_child: Default::default(),
            next_sibling: Default::default(),
            prev_sibling_cyclic: Default::default(),
            membership: membership.downgrade(),
        }
        .build_link();
        if let Some((old_first_child_link, last_child_link)) =
            self.intra_link.first_last_child_link()
        {
            // Connect the new first child and the last child.
            intra_link.replace_prev_sibling_cyclic(last_child_link.downgrade());
            // Connect the new first child and the old first child.
            IntraTreeLink::connect_adjacent_siblings(&intra_link, old_first_child_link);
        } else {
            // No siblings for the new node.
            intra_link.replace_prev_sibling_cyclic(intra_link.downgrade());
        }
        self.intra_link
            .replace_first_child(Some(intra_link.clone()));

        Self::with_link_and_membership(intra_link, membership)
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

        let membership = Membership::create_new_membership(self.membership.tree_core());
        let intra_link = NodeBuilder {
            data,
            parent: self.intra_link.downgrade(),
            first_child: Default::default(),
            next_sibling: Default::default(),
            prev_sibling_cyclic: Default::default(),
            membership: membership.downgrade(),
        }
        .build_link();
        if let Some((first_child_link, old_last_child_link)) =
            self.intra_link.first_last_child_link()
        {
            // Connect the old last child and the new last child.
            IntraTreeLink::connect_adjacent_siblings(&old_last_child_link, intra_link.clone());
            // Connect the first child and the new last child.
            first_child_link.replace_prev_sibling_cyclic(intra_link.downgrade());
        } else {
            // No siblings for the new node.
            intra_link.replace_prev_sibling_cyclic(intra_link.downgrade());
            self.intra_link
                .replace_first_child(Some(intra_link.clone()));
        }

        Self::with_link_and_membership(intra_link, membership)
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
                self.membership.tree_core(),
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
                self.membership.tree_core(),
                &parent.intra_link,
                &self.intra_link,
                &next_sibling_link,
            ),
            None => parent.create_as_last_child(data),
        };
        Ok(new_node)
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
    pub fn replace_with_children(&self) -> Result<(), StructureError> {
        let first_child_link = self.intra_link.first_child_link();

        if let Some(parent_link) = self.intra_link.parent_link() {
            // `self` is not the root.

            // Reset `parent`s of the children.
            {
                let mut next = first_child_link.clone();
                while let Some(current) = next {
                    next = current.next_sibling_link();
                    current.replace_parent(parent_link.downgrade());
                }
            }

            let prev_sibling_link = self.intra_link.prev_sibling_link();
            let next_sibling_link = self.intra_link.next_sibling_link();

            if let Some(first_child_link) = first_child_link {
                // `self` has children. Connect children and prev/next siblings.

                // The last child is stored as `prev_sibling_cyclic` of the first child.
                let last_child_link = first_child_link.prev_sibling_cyclic_link();

                match (prev_sibling_link, next_sibling_link) {
                    (Some(prev_sibling_link), Some(next_sibling_link)) => {
                        IntraTreeLink::connect_adjacent_siblings(
                            &prev_sibling_link,
                            first_child_link,
                        );
                        IntraTreeLink::connect_adjacent_siblings(
                            &last_child_link,
                            next_sibling_link,
                        );
                    }
                    (Some(prev_sibling_link), None) => {
                        IntraTreeLink::connect_adjacent_siblings(
                            &prev_sibling_link,
                            first_child_link,
                        );
                        let first_sibling_link = parent_link.first_child_link().expect(
                            "[validity] the parent has at least one child (prev of `self`)",
                        );
                        // `last_child` is the new last sibling.
                        first_sibling_link.replace_prev_sibling_cyclic(last_child_link.downgrade());
                    }
                    (None, Some(next_sibling_link)) => {
                        IntraTreeLink::connect_adjacent_siblings(
                            &last_child_link,
                            next_sibling_link,
                        );
                        let last_sibling_link_weak = parent_link.last_child_link_weak().expect(
                            "[validity] the parent has at least one child (next of `self`)",
                        );
                        // `first_child` is the new first sibling.
                        first_child_link.replace_prev_sibling_cyclic(last_sibling_link_weak);
                        parent_link.replace_first_child(Some(first_child_link));
                    }
                    (None, None) => {
                        parent_link.replace_first_child(Some(first_child_link));
                    }
                }
            } else {
                // `self` has no children. Just connect previous and next siblings.
                match (prev_sibling_link, next_sibling_link) {
                    (Some(prev_sibling_link), Some(next_sibling_link)) => {
                        IntraTreeLink::connect_adjacent_siblings(
                            &prev_sibling_link,
                            next_sibling_link,
                        );
                    }
                    (Some(prev_sibling_link), None) => {
                        prev_sibling_link.replace_next_sibling(None);
                    }
                    (None, Some(next_sibling_link)) => {
                        let last_sibling_link_weak = parent_link.last_child_link_weak().expect(
                            "[validity] the parent has at least one child (next of `self`)",
                        );
                        // `next_sibling_link` is the new first sibling.
                        next_sibling_link.replace_prev_sibling_cyclic(last_sibling_link_weak);
                        parent_link.replace_first_child(Some(next_sibling_link));
                    }
                    (None, None) => {
                        // Now the parent has no child.
                        parent_link.replace_first_child(None);
                    }
                }
            }
        } else {
            // `self` is the root.
            debug_assert!(
                self.is_root(),
                "[validity] the node without parent must be the root"
            );

            // Get the only child.
            let child_link = match first_child_link {
                Some(first_child_link) => {
                    if first_child_link.next_sibling_link().is_some() {
                        // The root node has more than two children.
                        return Err(StructureError::SiblingsWithoutParent);
                    }
                    first_child_link
                }
                // The root has no children.
                None => return Err(StructureError::EmptyTree),
            };

            // Disconnect the child from `self`.
            child_link.replace_parent(IntraTreeLinkWeak::default());
        }

        // Disconnect `self` from neighbors.
        self.intra_link.replace_parent(IntraTreeLinkWeak::default());
        self.intra_link.replace_first_child(None);
        let self_link_weak = self.intra_link.downgrade();
        self.intra_link.replace_prev_sibling_cyclic(self_link_weak);
        self.intra_link.replace_next_sibling(None);

        // Create new tree core for `self`.
        let tree_core_rc = TreeCore::new_rc(self.intra_link.clone());
        self.set_memberships_of_descendants_and_self(&tree_core_rc);

        Ok(())
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

/// Inserts the `new_node` between `prev_sibling` and `next_sibling`
///
/// Before:
///
/// ```text
///           parent
///           /    \
/// prev_sibling->next_sibling
/// ```
///
/// After:
///
/// ```text
///              parent
///            ___/|\___
///           /    |    \
/// prev_sibling->NEW->next_sibling
/// ```
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

    let membership = Membership::create_new_membership(tree_core);
    let intra_link = NodeBuilder {
        data,
        parent: parent_link.downgrade(),
        first_child: Default::default(),
        next_sibling: Some(next_sibling_link.clone()),
        prev_sibling_cyclic: prev_sibling_link.downgrade(),
        membership: membership.downgrade(),
    }
    .build_link();

    next_sibling_link.replace_prev_sibling_cyclic(intra_link.downgrade());
    prev_sibling_link.replace_next_sibling(Some(intra_link.clone()));

    Node::with_link_and_membership(intra_link, membership)
}
