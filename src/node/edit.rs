//! Node edit algorithms.

use alloc::rc::Rc;

use crate::anchor::{AdoptAs, InsertAs};
use crate::membership::Membership;
use crate::node::{HotNode, IntraTreeLink, IntraTreeLinkWeak, Node, NodeBuilder, StructureError};
use crate::serial::{TreeBuildError, TreeBuilder};
use crate::traverse::DftEvent;
use crate::tree::TreeCore;

/// Detaches the node and its descendant from the current tree, and let it be another tree.
pub(super) fn detach_subtree<T>(this: &IntraTreeLink<T>) {
    if this.is_root() {
        // Detaching entire tree is meaningless.
        // Do nothing.
        return;
    }

    // Update the references to the tree core.
    let tree_core_rc = TreeCore::new_rc(this.clone());
    set_memberships_of_descendants_and_self(this, &tree_core_rc)
        .expect("[validity] brand-new tree structure can be locked by any types of lock");

    unlink_from_parent_and_siblings(this);
}

/// Detaches the node and its descendant from the current tree.
///
/// The caller should not pass the root node to the subtree, since it is meaningless.
fn unlink_from_parent_and_siblings<T>(this: &IntraTreeLink<T>) {
    debug_assert!(
        !this.is_root(),
        "[consistency] root node should be rejected by the caller"
    );

    // Unlink from the neighbors.
    // Fields to update:
    //  * parent --> this
    //      * parent.first_child (if necessary)
    //      * this.parent (if available)
    //  * prev_sibling --> this
    //      * prev_sibling.next_sibling (if available)
    //      * this.prev_sibling_cyclic (mandatory)
    //  * this --> next_sibling
    //      * this.next_sibling (if available)
    //      * next_sibling.prev_sibling_cyclic (if available)

    let parent_link = this.parent_link();
    let prev_sibling_link = this.prev_sibling_link();
    let prev_sibling_cyclic_link = this.prev_sibling_cyclic_link();
    let next_sibling_link = this.next_sibling_link();

    // Update neighbors.
    if let Some(parent_link) = &parent_link {
        if this.is_first_sibling() {
            parent_link.replace_first_child(next_sibling_link.clone());
        }
    }
    if let Some(prev_sibling_link) = prev_sibling_link {
        prev_sibling_link.replace_next_sibling(next_sibling_link.clone());
    }
    if let Some(next_sibling_link) = next_sibling_link {
        next_sibling_link.replace_prev_sibling_cyclic(prev_sibling_cyclic_link.downgrade());
    }

    // Update `this`.
    this.replace_parent(IntraTreeLinkWeak::default());
    let this_weak = this.downgrade();
    this.replace_prev_sibling_cyclic(this_weak);
    this.replace_next_sibling(None);
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

    // Fields to update:
    //  * parent --> new_child
    //      * new_child.parent (mandatory)
    //      * this.first_child (mandatory)
    //  * new_child --> old_first_child
    //      * new_child.next_sibling (if available)
    //      * old_first_child.prev_sibling_cyclic (if available)
    //  * last_child --> new_child
    //      * new_child.prev_sibling_cyclic (mandatory)

    let membership = Membership::create_new_membership(tree_core);
    let intra_link = NodeBuilder {
        data,
        parent: this.downgrade(),
        first_child: Default::default(),
        next_sibling: Default::default(),
        prev_sibling_cyclic: Default::default(),
        membership: membership.downgrade(),
    }
    .build_link();
    if let Some((old_first_child_link, last_child_link)) = this.first_last_child_link() {
        // Connect the new first child and the last child.
        intra_link.replace_prev_sibling_cyclic(last_child_link.downgrade());
        // Connect the new first child and the old first child.
        IntraTreeLink::connect_adjacent_siblings(&intra_link, old_first_child_link);
    } else {
        // No siblings for the new node.
        intra_link.replace_prev_sibling_cyclic(intra_link.downgrade());
    }
    this.replace_first_child(Some(intra_link.clone()));

    Node::with_link_and_membership(intra_link, membership)
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

    // Fields to update:
    //  * parent --> new_child
    //      * new_child.parent (mandatory)
    //  * old_last_child --> new_child
    //      * new_child.prev_sibling_cyclic (mandatory)
    //      * old_last_child.next (if available)
    //  * first_child --> new_child
    //      * first_child.prev_sibling_cyclic (mandatory)

    let membership = Membership::create_new_membership(tree_core);
    let intra_link = NodeBuilder {
        data,
        parent: this.downgrade(),
        first_child: Default::default(),
        next_sibling: Default::default(),
        prev_sibling_cyclic: Default::default(),
        membership: membership.downgrade(),
    }
    .build_link();
    if let Some((first_child_link, old_last_child_link)) = this.first_last_child_link() {
        // Connect the old last child and the new last child.
        IntraTreeLink::connect_adjacent_siblings(&old_last_child_link, intra_link.clone());
        // Connect the first child and the new last child.
        first_child_link.replace_prev_sibling_cyclic(intra_link.downgrade());
    } else {
        // No siblings for the new node.
        intra_link.replace_prev_sibling_cyclic(intra_link.downgrade());
        this.replace_first_child(Some(intra_link.clone()));
    }

    Node::with_link_and_membership(intra_link, membership)
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

    let parent_link = this
        .parent_link()
        .ok_or(StructureError::SiblingsWithoutParent)?;
    let new_node = match this.prev_sibling_link() {
        Some(prev_sibling_link) => {
            create_insert_between(data, tree_core, &parent_link, &prev_sibling_link, this)
        }
        None => create_as_first_child(&parent_link, tree_core, data),
    };
    Ok(new_node)
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

    let parent_link = this
        .parent_link()
        .ok_or(StructureError::SiblingsWithoutParent)?;
    let new_node = match this.next_sibling_link() {
        Some(next_sibling_link) => {
            create_insert_between(data, tree_core, &parent_link, this, &next_sibling_link)
        }
        None => create_as_last_child(&parent_link, tree_core, data),
    };
    Ok(new_node)
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
    //      * (Note that `parent.first_child` won't be set since the new node is
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
