//! Tests to ensure the tree is dropped expectedly.

use std::rc::{Rc, Weak};

use dendron::HotNode;

/// A minimum depth to nest objects to be dropped.
///
/// Increase this value if
/// `should_cause_stack_overflow_due_to_large_min_drop_depth` test (you should
/// uncomment the `#[test]` attribute to run this) does not crash by stack
/// overflow.
///
// In the original author's environment (rustc 1.59.0 and LLVM 13.0.0 on
// `x86_64-unknown-linux-gnu`), this should be larger than `21769`
// (as of 2022-04).
// This value may vary among test implementations, toolchain versions, and
// hardwares, so use more and more larger values for this constant.
const MIN_DROP_DEPTH: usize = 140_000;

//#[test] // NOTE: uncomment this line to test whether `MIN_DROP_DEPTH` is large enough.
#[allow(dead_code)]
fn should_cause_stack_overflow_due_to_large_min_drop_depth() {
    // Simple recursive call of doing-nothing function would be optimized away,
    // so create actual deeply nested objects and drop it.

    enum SimplifiedNode {
        Leaf(Rc<()>),
        Node(Box<SimplifiedNode>, Rc<()>),
    }

    let (counter, node_data) = create_counter(());
    let mut head = SimplifiedNode::Leaf(node_data.clone());

    for _ in 1..MIN_DROP_DEPTH {
        head = SimplifiedNode::Node(Box::new(head), node_data.clone());
    }
    drop(node_data);
    assert_eq!(counter.strong_count(), MIN_DROP_DEPTH);

    drop(head);
    assert_eq!(counter.strong_count(), 0);
    panic!("this test should crash by stack overflow, but did not");
}

#[must_use]
fn create_counter<T>(v: T) -> (Weak<T>, Rc<T>) {
    let rc = Rc::new(v);
    let weak = Rc::downgrade(&rc);
    (weak, rc)
}

#[test]
fn drop_single_node_tree() {
    let (counter, root_data) = create_counter(());
    let root = HotNode::new_tree(root_data);
    assert_eq!(counter.strong_count(), 1, "only the root node exists");
    assert!(root.is_root());

    drop(root);
    assert_eq!(counter.strong_count(), 0, "the tree should not leak");
}

#[test]
fn drop_nested_node_tree() {
    let (counter, node_data) = create_counter(());
    let root = HotNode::new_tree(node_data.clone());
    let child0 = root.create_as_last_child(node_data.clone());
    let child1 = root.create_as_last_child(node_data.clone());
    let child0_0 = child0.create_as_last_child(node_data);
    //  root
    //  |-- child0
    //  |   `-- child0_0
    //  `-- child1

    assert_eq!(counter.strong_count(), 4, "there are four nodes");
    drop(root);
    assert_eq!(
        counter.strong_count(),
        4,
        "no nodes should be destructed since other nodes in the tree are still alive"
    );
    drop(child0);
    assert_eq!(
        counter.strong_count(),
        4,
        "no nodes should be destructed since other nodes in the tree are still alive"
    );
    drop(child1);
    assert_eq!(
        counter.strong_count(),
        4,
        "no nodes should be destructed since `child0_0` in the same tree is still alive"
    );
    drop(child0_0);
    assert_eq!(
        counter.strong_count(),
        0,
        "now the user cannot refer any nodes in the tree, so all nodes are released"
    );
}

#[test]
fn drop_detached_tree() {
    let (counter, node_data) = create_counter(());
    let root = HotNode::new_tree(node_data.clone());
    let child0 = root.create_as_last_child(node_data.clone());
    let child1 = root.create_as_last_child(node_data.clone());
    let child0_0 = child0.create_as_last_child(node_data.clone());
    let child0_1 = child0.create_as_last_child(node_data.clone());
    let child1_0 = child1.create_as_last_child(node_data);
    //  root
    //  |-- child0
    //  |   |-- child0_0
    //  |   `-- child0_1
    //  `-- child1
    //      `-- child1_0
    assert_eq!(counter.strong_count(), 6, "there are six nodes");
    assert!(HotNode::ptr_eq(&root.root(), &root));
    assert!(HotNode::ptr_eq(&child0.root(), &root));
    assert!(HotNode::ptr_eq(&child1.root(), &root));
    assert!(HotNode::ptr_eq(&child0_0.root(), &root));
    assert!(HotNode::ptr_eq(&child0_1.root(), &root));
    assert!(HotNode::ptr_eq(&child1_0.root(), &root));
    assert!(root.is_root());
    assert!(!child0.is_root());
    assert!(!child1.is_root());
    assert!(!child0_0.is_root());
    assert!(!child0_1.is_root());
    assert!(!child1_0.is_root());

    // Detach `child0` node from the tree.
    child0.detach_subtree();
    //  root
    //  `-- child1
    //      `-- child1_1
    //  child0
    //  |-- child0_0
    //  `-- child0_1
    assert_eq!(counter.strong_count(), 6, "there are still six nodes");
    assert!(HotNode::ptr_eq(&root.root(), &root));
    assert!(HotNode::ptr_eq(&child1.root(), &root));
    assert!(HotNode::ptr_eq(&child1_0.root(), &root));
    assert!(HotNode::ptr_eq(&child0.root(), &child0));
    assert!(HotNode::ptr_eq(&child0_0.root(), &child0));
    assert!(HotNode::ptr_eq(&child0_1.root(), &child0));
    assert!(root.is_root());
    assert!(!child1.is_root());
    assert!(!child1_0.is_root());
    assert!(child0.is_root(), "child0 is now the root of a new tree");
    assert!(!child0_0.is_root());
    assert!(!child0_1.is_root());

    drop(root);
    assert_eq!(counter.strong_count(), 6, "there are still six nodes");
    assert!(!child1.is_root());
    assert!(!child1_0.is_root());

    drop(child1);
    assert_eq!(counter.strong_count(), 6, "there are still six nodes");
    assert!(!child1_0.is_root());

    drop(child1_0);
    assert_eq!(
        counter.strong_count(),
        3,
        "`root`, `child1`, and `child1_0` are released"
    );

    drop(child0);
    assert_eq!(counter.strong_count(), 3, "there are still three nodes");
    assert!(!child0_0.is_root());
    assert!(!child0_1.is_root());

    drop(child0_1);
    assert_eq!(counter.strong_count(), 3, "there are still three nodes");
    assert!(!child0_0.is_root());

    drop(child0_0);
    assert_eq!(counter.strong_count(), 0, "all nodes are now unreachable");
}

#[test]
fn drop_very_deep_tree() {
    let (counter, node_data) = create_counter(());
    let root = HotNode::new_tree(node_data.clone());
    {
        let mut current = root.clone();
        for _ in 1..MIN_DROP_DEPTH {
            current = current.create_as_last_child(node_data.clone());
        }
        drop(node_data);
    }
    // Now the leaf node has DEPTH-1 ancestors.

    assert_eq!(
        counter.strong_count(),
        MIN_DROP_DEPTH,
        "there should be {MIN_DROP_DEPTH} nodes"
    );
    drop(root);
    assert_eq!(
        counter.strong_count(),
        0,
        "the entire tree is now dropped without causing stack overflow"
    );
}

#[test]
fn drop_very_wide_tree() {
    let (counter, node_data) = create_counter(());
    let root = HotNode::new_tree(node_data.clone());
    for _ in 0..MIN_DROP_DEPTH {
        root.create_as_last_child(node_data.clone());
    }
    drop(node_data);
    // Now the root has WIDTH child nodes.

    assert_eq!(
        counter.strong_count(),
        MIN_DROP_DEPTH + 1,
        "there should be a root and {MIN_DROP_DEPTH} children"
    );
    drop(root);
    assert_eq!(
        counter.strong_count(),
        0,
        "the entire tree is now dropped without causing stack overflow"
    );
}
