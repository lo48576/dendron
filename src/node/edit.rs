//! Node edit algorithms.

use alloc::rc::Rc;

use crate::anchor::{AdoptAs, InsertAs};
use crate::membership::Membership;
use crate::node::{HotNode, IntraTreeLink, IntraTreeLinkWeak, Node, NodeBuilder, StructureError};
use crate::serial::{TreeBuildError, TreeBuilder};
use crate::traverse::DftEvent;
use crate::tree::TreeCore;

/// A root node of an orphan tree.
///
/// The node managed by this type should have no root and no siblings. However,
/// the node don't need to be referred from the tree core as the root node.
///
/// The node link managed by this type is in a temporary inconsistent state, so
/// users should consume `self` by any method of this type.
struct OrphanRoot<'a, T> {
    /// The (possibly temporarily inconsistent) orphan root node.
    link: &'a IntraTreeLink<T>,
    /// Whether the managed node is newly created.
    ///
    /// When this is true, some checks (such as loop detection) can be omitted.
    is_newly_created: bool,
}

impl<'a, T> OrphanRoot<'a, T> {
    /// Creates a new orphan node from the data.
    fn create_and_process<F, E>(
        data: T,
        tree_core: Rc<TreeCore<T>>,
        process: F,
    ) -> Result<Node<T>, E>
    where
        for<'b> F: FnOnce(OrphanRoot<'b, T>) -> Result<(), E>,
    {
        let membership = Membership::create_new_membership(tree_core);
        let intra_link = NodeBuilder {
            data,
            parent: Default::default(),
            first_child: Default::default(),
            next_sibling: Default::default(),
            prev_sibling_cyclic: Default::default(),
            membership: membership.downgrade(),
        }
        .build_link();
        let node = Node::with_link_and_membership(intra_link, membership);

        process(OrphanRoot {
            link: &node.intra_link,
            is_newly_created: true,
        })?;

        Ok(node)
    }

    /// Unlinks a node from the parent and the siblings.
    ///
    /// This method does not update the tree core references, so callers are
    /// responsible to set them if necessary.
    #[must_use]
    fn new_by_unlink(node_to_unlink: &'a IntraTreeLink<T>) -> Self {
        if node_to_unlink.is_root() {
            // Has no parent and sibling.
            return Self {
                link: node_to_unlink,
                is_newly_created: false,
            };
        }

        // Unlink from the neighbors.
        // Fields to update:
        //  * parent --> node_to_unlink
        //      * parent.first_child (if necessary)
        //      * node_to_unlink.parent (if available)
        //  * prev_sibling --> node_to_unlink
        //      * prev_sibling.next_sibling (if available)
        //      * node_to_unlink.prev_sibling_cyclic (mandatory)
        //  * node_to_unlink --> next_sibling
        //      * node_to_unlink.next_sibling (if available)
        //      * next_sibling.prev_sibling_cyclic (if available)

        let parent = node_to_unlink.parent_link();
        let prev_sibling = node_to_unlink.prev_sibling_link();
        let prev_sibling_cyclic = node_to_unlink.prev_sibling_cyclic_link();
        let next_sibling = node_to_unlink.next_sibling_link();

        // Update neighbors.
        if let Some(parent) = &parent {
            if node_to_unlink.is_first_sibling() {
                parent.replace_first_child(next_sibling.clone());
            }
        }
        if let Some(prev_sibling) = prev_sibling {
            prev_sibling.replace_next_sibling(next_sibling.clone());
        }
        if let Some(next_sibling) = next_sibling {
            next_sibling.replace_prev_sibling_cyclic(prev_sibling_cyclic.downgrade());
        }

        // Update `node_to_unlink`.
        node_to_unlink.replace_parent(IntraTreeLinkWeak::default());
        let link_weak = node_to_unlink.downgrade();
        node_to_unlink.replace_prev_sibling_cyclic(link_weak);
        node_to_unlink.replace_next_sibling(None);

        Self {
            link: node_to_unlink,
            is_newly_created: true,
        }
    }

    /// Sets the given tree core to every node in the subtree, including `self`.
    #[inline]
    fn set_tree_core(&self, tree_core: &Rc<TreeCore<T>>) -> Result<(), ()> {
        set_memberships_of_descendants_and_self(self.link, tree_core)
    }

    /// Make the orphan subtree a new independent tree.
    fn create_new_tree(self) {
        let tree_core = TreeCore::new_rc(self.link.clone());
        self.set_tree_core(&tree_core)
            .expect("[validity] brand-new tree structure can be locked by any types of lock");
    }

    /// Returns true if the given node is an ancestor of `self`.
    #[must_use]
    fn is_ancestor_of(&self, node: IntraTreeLink<T>) -> bool {
        let mut current = Some(node);
        while let Some(ancestor) = current {
            if self.link.ptr_eq(&ancestor) {
                return true;
            }
            current = ancestor.parent_link();
        }

        false
    }

    /// Inserts the node into the given destination.
    fn insert(self, dest: InsertAs<&IntraTreeLink<T>>) -> Result<(), StructureError> {
        match dest {
            InsertAs::FirstChildOf(parent) => self.insert_as_first_child_of(parent),
            InsertAs::LastChildOf(parent) => self.insert_as_last_child_of(parent),
            InsertAs::PreviousSiblingOf(anchor) => {
                let parent = anchor
                    .parent_link()
                    .ok_or(StructureError::SiblingsWithoutParent)?;
                match anchor.prev_sibling_link() {
                    Some(prev_sibling) => {
                        // siblings: prev_sibling --> self --> anchor
                        self.insert_between(&parent, &prev_sibling, anchor);
                        Ok(())
                    }
                    None => self.insert_as_first_child_of(&parent),
                }
            }
            InsertAs::NextSiblingOf(anchor) => {
                let parent = anchor
                    .parent_link()
                    .ok_or(StructureError::SiblingsWithoutParent)?;
                match anchor.next_sibling_link() {
                    Some(next_sibling) => {
                        // siblings: anchor --> this --> next_sibling
                        self.insert_between(&parent, anchor, &next_sibling);
                        Ok(())
                    }
                    None => self.insert_as_last_child_of(&parent),
                }
            }
        }
    }

    /// Inserts the node as the first child of the given node.
    fn insert_as_first_child_of(self, parent: &IntraTreeLink<T>) -> Result<(), StructureError> {
        if !self.is_newly_created && self.is_ancestor_of(parent.clone()) {
            return Err(StructureError::AncestorDescendantLoop);
        }

        // Fields to update:
        //  * parent --> self
        //      * self.parent (mandatory)
        //      * parent.first_child (mandatory)
        //  * self --> old_first_child
        //      * self.next_sibling (if available)
        //      * old_first_child.prev_sibling_cyclic (if available)
        //  * last_child --> this
        //      * self.prev_sibling_cyclic (mandatory)

        // Connect siblings.
        if let Some((old_first_child, last_child)) = parent.first_last_child_link() {
            // Connect the new first child and the last child.
            self.link
                .replace_prev_sibling_cyclic(last_child.downgrade());
            // Connect the new first child and the old first child.
            IntraTreeLink::connect_adjacent_siblings(self.link, old_first_child);
        } else {
            // No siblings for the new node.
            self.link.replace_prev_sibling_cyclic(self.link.downgrade());
        }

        // Set up parent-child relations.
        self.link.replace_parent(parent.downgrade());
        parent.replace_first_child(Some(self.link.clone()));

        Ok(())
    }

    /// Inserts the node as the last child of the given node.
    fn insert_as_last_child_of(self, parent: &IntraTreeLink<T>) -> Result<(), StructureError> {
        if !self.is_newly_created && self.is_ancestor_of(parent.clone()) {
            return Err(StructureError::AncestorDescendantLoop);
        }

        // Fields to update:
        //  * parent --> self
        //      * this.parent (mandatory)
        //  * old_last_child --> self
        //      * self.prev_sibling_cyclic (mandatory)
        //      * old_last_child.next (if available)
        //  * first_child --> self
        //      * first_child.prev_sibling_cyclic (mandatory)

        if let Some((first_child, old_last_child)) = parent.first_last_child_link() {
            // Connect the first child and the new last child.
            first_child.replace_prev_sibling_cyclic(self.link.downgrade());
            // Connect the old last child and the new last child.
            IntraTreeLink::connect_adjacent_siblings(&old_last_child, self.link.clone());
        } else {
            // No siblings for the new node.
            self.link.replace_prev_sibling_cyclic(self.link.downgrade());
            parent.replace_first_child(Some(self.link.clone()));
        }
        self.link.replace_parent(parent.downgrade());

        Ok(())
    }

    /// Inserts a node between the given siblings (previous and next).
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
    /// prev_sibling->self->next_sibling
    /// ```
    fn insert_between(
        self,
        parent: &IntraTreeLink<T>,
        prev_sibling: &IntraTreeLink<T>,
        next_sibling: &IntraTreeLink<T>,
    ) {
        // Check consistency of the given nodes.
        debug_assert!(
            prev_sibling
                .parent_link()
                .map_or(false, |p| IntraTreeLink::ptr_eq(&p, parent)),
            "`prev_sibling` must be a child of `parent`"
        );
        debug_assert!(
            next_sibling
                .parent_link()
                .map_or(false, |p| IntraTreeLink::ptr_eq(&p, parent)),
            "`next_sibling` must be a child of `parent`"
        );
        debug_assert!(
            prev_sibling
                .next_sibling_link()
                .map_or(false, |p| IntraTreeLink::ptr_eq(&p, next_sibling)),
            "`next_sibling` must be the next sibling of `prev_sibling`"
        );
        debug_assert!(
            next_sibling
                .prev_sibling_link()
                .map_or(false, |p| IntraTreeLink::ptr_eq(&p, prev_sibling)),
            "`prev_sibling` must be the previous sibling of `next_sibling`"
        );

        // Fields to update:
        //  * parent --> self
        //      * self.parent (mandatory)
        //      * (Note that `parent.first_child` won't be set since the `self`
        //        is not the first child.)
        //  * prev_sibling --> self
        //      * prev_sibling.next_sibling (mandatory)
        //      * self.prev_sibling_cyclic (mandatory)
        //  * self --> next_sibling
        //      * self.next_sibling (mandatory)
        //      * next_sibling.prev_sibling_cyclic (mandatory)

        // Set parent-child relation.
        self.link.replace_parent(parent.downgrade());
        // You can use `IntraTreeLink::connect_adjacent_siblings`,
        // but manipulate manually to reduce cloning of links.
        //
        // siblings: prev_sibling --> self --> next_sibling
        let next_sibling_owned = prev_sibling.replace_next_sibling(Some(self.link.clone()));
        self.link.replace_next_sibling(next_sibling_owned);
        let prev_sibling_weak = next_sibling.replace_prev_sibling_cyclic(self.link.downgrade());
        self.link.replace_prev_sibling_cyclic(prev_sibling_weak);
    }
}

/// Detaches the node and its descendant from the current tree, and let it be another tree.
pub(super) fn detach_subtree<T>(this: &IntraTreeLink<T>) {
    if this.is_root() {
        // Detaching entire tree is meaningless.
        // Do nothing.
        return;
    }

    let orphan_this = OrphanRoot::new_by_unlink(this);
    orphan_this.create_new_tree();
}

/// Detaches the node and its descendant from the current parent, and inserts to other place in the
/// same tree.
pub(super) fn detach_and_move_inside_same_tree<T>(
    this: &IntraTreeLink<T>,
    dest: InsertAs<&IntraTreeLink<T>>,
) -> Result<(), StructureError> {
    if this.is_root() {
        // Detaching entire tree here is meaningless.
        // Do nothing.
        return Ok(());
    }

    let orphan_this = OrphanRoot::new_by_unlink(this);
    orphan_this.insert(dest)
}

/// Detaches the node and its descendant from the current tree, and inserts to other tree.
///
/// # Preconditions
///
/// * `dest_tree_core` must be the tree core for the anchor nod of the destination.
/// * The anchor node of the destination must be granted to be edited.
pub(super) fn detach_and_move_to_another_tree<T>(
    this: &IntraTreeLink<T>,
    dest: InsertAs<&IntraTreeLink<T>>,
    dest_tree_core: &Rc<TreeCore<T>>,
) -> Result<(), StructureError> {
    let orphan_this = OrphanRoot::new_by_unlink(this);
    orphan_this
        .set_tree_core(dest_tree_core)
        .expect("[consistency] brand-new tree structure can be locked by any types of lock");
    orphan_this.insert(dest)
}

/// Changes the memberships of the given node and its descendants to the given tree.
fn set_memberships_of_descendants_and_self<T>(
    this: &IntraTreeLink<T>,
    tree_core_rc: &Rc<TreeCore<T>>,
) -> Result<(), ()> {
    for current in this.depth_first_traverse() {
        if let DftEvent::Open(link) = current {
            link.membership().set_tree_core(tree_core_rc)?;
        }
    }
    Ok(())
}

/// Creates a node as the next sibling of the given node, and returns the new node.
///
/// # Panics
///
/// The given node `this` should belong to the tree with the given tree core
/// `tree_core`. If not, this function MAY panic.
///
/// It is caller's responsibility to satisfy this precondition.
pub(super) fn try_create_node_as<T>(
    this: &IntraTreeLink<T>,
    tree_core: Rc<TreeCore<T>>,
    data: T,
    dest: AdoptAs,
) -> Result<Node<T>, StructureError> {
    match dest {
        AdoptAs::FirstChild => Ok(create_as_first_child(this, tree_core, data)),
        AdoptAs::LastChild => Ok(create_as_last_child(this, tree_core, data)),
        AdoptAs::PreviousSibling => try_create_as_prev_sibling(this, tree_core, data),
        AdoptAs::NextSibling => try_create_as_next_sibling(this, tree_core, data),
    }
}

/// Creates a node as the first child of the given node.
///
/// # Panics
///
/// The given node `this` should belong to the tree with the given tree core
/// `tree_core`. If not, this function MAY panic.
///
/// It is caller's responsibility to satisfy this precondition.
pub(super) fn create_as_first_child<T>(
    this: &IntraTreeLink<T>,
    tree_core: Rc<TreeCore<T>>,
    data: T,
) -> Node<T> {
    debug_assert!(
        this.belongs_to_tree_core_rc(&tree_core),
        "[validity] the given node link must belong to the tree with the given core"
    );

    OrphanRoot::create_and_process(data, tree_core, |orphan_link| {
        orphan_link.insert_as_first_child_of(this)
    })
    .expect("[validity] the structure of the tree the parent belongs to should be editable")
}

/// Creates a node as the last child of the given node.
///
/// # Panics
///
/// The given node `this` should belong to the tree with the given tree core
/// `tree_core`. If not, this function MAY panic.
///
/// It is caller's responsibility to satisfy this precondition.
pub(super) fn create_as_last_child<T>(
    this: &IntraTreeLink<T>,
    tree_core: Rc<TreeCore<T>>,
    data: T,
) -> Node<T> {
    debug_assert!(
        this.belongs_to_tree_core_rc(&tree_core),
        "[validity] the given node link must belong to the tree with the given core"
    );

    OrphanRoot::create_and_process(data, tree_core, |orphan_link| {
        orphan_link.insert_as_last_child_of(this)
    })
    .expect("[validity] the structure of the tree the parent belongs to should be editable")
}

/// Creates a node as the previous sibling of the given node.
///
/// # Failures
///
/// Returns [`StructureError::SiblingsWithoutParent`] as an error if the given
/// node is a root node.
///
/// # Panics
///
/// The given node `this` should belong to the tree with the given tree core
/// `tree_core`. If not, this function MAY panic.
///
/// It is caller's responsibility to satisfy this precondition.
pub(super) fn try_create_as_prev_sibling<T>(
    this: &IntraTreeLink<T>,
    tree_core: Rc<TreeCore<T>>,
    data: T,
) -> Result<Node<T>, StructureError> {
    debug_assert!(
        this.belongs_to_tree_core_rc(&tree_core),
        "[validity] the given node link must belong to the tree with the given core"
    );

    OrphanRoot::create_and_process(data, tree_core, |orphan_link| {
        orphan_link.insert(InsertAs::PreviousSiblingOf(this))
    })
}

/// Creates a node as the next sibling of the given node.
///
/// # Failures
///
/// Returns [`StructureError::SiblingsWithoutParent`] as an error if the given
/// node is a root node.
///
/// # Panics
///
/// The given node `this` should belong to the tree with the given tree core
/// `tree_core`. If not, this function MAY panic.
///
/// It is caller's responsibility to satisfy this precondition.
pub(super) fn try_create_as_next_sibling<T>(
    this: &IntraTreeLink<T>,
    tree_core: Rc<TreeCore<T>>,
    data: T,
) -> Result<Node<T>, StructureError> {
    debug_assert!(
        this.belongs_to_tree_core_rc(&tree_core),
        "[validity] the given node link must belong to the tree with the given core"
    );

    OrphanRoot::create_and_process(data, tree_core, |orphan_link| {
        orphan_link.insert(InsertAs::NextSiblingOf(this))
    })
}

/// Inserts the children at the position of the node, and detach the node.
///
/// `this` will become the root of a new single-node tree.
///
/// Before:
///
/// ```text
/// parent
/// |-- prev
/// |-- this
/// |   |-- child0
/// |   |   `-- grandchild0-0
/// |   `-- child1
/// `-- next
/// ```
///
/// After `replace_with_children(this)`:
///
/// ```text
/// parent
/// |-- prev
/// |-- child0
/// |   `-- grandchild0-0
/// |-- child1
/// `-- next
///
/// this (detached)
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
pub(super) fn replace_with_children<T>(this: &IntraTreeLink<T>) -> Result<(), StructureError> {
    let first_child_link = this.first_child_link();

    if let Some(parent_link) = this.parent_link() {
        // `this` is not the root.

        // Reset `parent`s of the children.
        {
            let mut next = first_child_link.clone();
            while let Some(current) = next {
                next = current.next_sibling_link();
                current.replace_parent(parent_link.downgrade());
            }
        }

        let prev_sibling_link = this.prev_sibling_link();
        let next_sibling_link = this.next_sibling_link();

        if let Some(first_child_link) = first_child_link {
            // `this` has children. Connect children and prev/next siblings.

            // The last child is stored as `prev_sibling_cyclic` of the first child.
            let last_child_link = first_child_link.prev_sibling_cyclic_link();

            match (prev_sibling_link, next_sibling_link) {
                (Some(prev_sibling_link), Some(next_sibling_link)) => {
                    IntraTreeLink::connect_adjacent_siblings(&prev_sibling_link, first_child_link);
                    IntraTreeLink::connect_adjacent_siblings(&last_child_link, next_sibling_link);
                }
                (Some(prev_sibling_link), None) => {
                    IntraTreeLink::connect_adjacent_siblings(&prev_sibling_link, first_child_link);
                    let first_sibling_link = parent_link
                        .first_child_link()
                        .expect("[validity] the parent has at least one child (prev of `self`)");
                    // `last_child` is the new last sibling.
                    first_sibling_link.replace_prev_sibling_cyclic(last_child_link.downgrade());
                }
                (None, Some(next_sibling_link)) => {
                    IntraTreeLink::connect_adjacent_siblings(&last_child_link, next_sibling_link);
                    let last_sibling_link_weak = parent_link
                        .last_child_link_weak()
                        .expect("[validity] the parent has at least one child (next of `self`)");
                    // `first_child` is the new first sibling.
                    first_child_link.replace_prev_sibling_cyclic(last_sibling_link_weak);
                    parent_link.replace_first_child(Some(first_child_link));
                }
                (None, None) => {
                    parent_link.replace_first_child(Some(first_child_link));
                }
            }
        } else {
            // `this` has no children. Just connect previous and next siblings.
            match (prev_sibling_link, next_sibling_link) {
                (Some(prev_sibling_link), Some(next_sibling_link)) => {
                    IntraTreeLink::connect_adjacent_siblings(&prev_sibling_link, next_sibling_link);
                }
                (Some(prev_sibling_link), None) => {
                    prev_sibling_link.replace_next_sibling(None);
                }
                (None, Some(next_sibling_link)) => {
                    let last_sibling_link_weak = parent_link
                        .last_child_link_weak()
                        .expect("[validity] the parent has at least one child (next of `self`)");
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
        // `this` is the root.
        debug_assert!(
            this.is_root(),
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

        // Disconnect the child from `this`.
        child_link.replace_parent(IntraTreeLinkWeak::default());
    }

    // Disconnect `this` from neighbors.
    this.replace_parent(IntraTreeLinkWeak::default());
    this.replace_first_child(None);
    let this_weak = this.downgrade();
    this.replace_prev_sibling_cyclic(this_weak);
    this.replace_next_sibling(None);

    // Create a new tree core for `this`.
    let tree_core_rc = TreeCore::new_rc(this.clone());
    set_memberships_of_descendants_and_self(this, &tree_core_rc)
        .expect("[validity] brand-new tree structure can be locked by any types of lock");

    Ok(())
}

/// Clones the node and its subtree, and inserts it to the given destination.
///
/// Returns the root node of the cloned new subtree.
///
/// # Failures
///
/// Fails with [`BorrowNodeData`][`StructureError::BorrowNodeData`] if any
/// data associated to the node in the subtree is mutably (i.e. exclusively)
/// borrowed.
pub(super) fn clone_insert_subtree<T>(
    source: &Node<T>,
    dest: InsertAs<HotNode<T>>,
) -> Result<HotNode<T>, StructureError>
where
    T: Clone,
{
    let subtree_root = dest.try_create_node(
        source
            .try_borrow_data()
            .map_err(StructureError::BorrowNodeData)?
            .clone(),
    )?;
    let mut events = source.to_events();
    // Skip the opening of the root, since it will be processed by calling
    // `TreeBuilder::with_root()`.
    events.next();
    events
        .try_fold(
            TreeBuilder::with_root(subtree_root),
            |mut builder, ev_res| {
                builder.push_event(ev_res?)?;
                Ok(builder)
            },
        )
        .and_then(|builder| builder.finish())
        .map(|node| {
            node.bundle_new_structure_edit_grant()
                .expect("[consistency] the structure of the destination tree is already editable")
        })
        .map_err(|e| match e {
            TreeBuildError::BorrowData(e) => StructureError::BorrowNodeData(e),
            TreeBuildError::RootNotOpened | TreeBuildError::RootClosed => {
                unreachable!("[validity] subtree should be consistently serializable")
            }
        })
}
