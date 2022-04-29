//! Tests for `HotNode::replace_with_children`.

use dendron::traverse::DftEvent;
use dendron::{HierarchyError, HotNode};

fn serialize_subtree<T: Clone>(node: &HotNode<T>) -> Vec<DftEvent<T>> {
    node.depth_first_traverse()
        .map(|ev| ev.map(|node| (*node.borrow_data()).clone()))
        .collect()
}

#[test]
fn replace_root_without_children() {
    let root = HotNode::new_tree("root");

    assert!(
        matches!(root.replace_with_children(), Err(HierarchyError::EmptyTree)),
        "tree cannot be empty"
    );
}

#[test]
fn replace_root_with_single_child() {
    let root = HotNode::new_tree("root");
    let child = root.create_as_last_child("child");
    //  root
    //  `-- child
    assert!(root.is_root());
    assert!(!child.is_root());

    //  root
    //  child
    assert!(root.replace_with_children().is_ok());
    assert!(root.is_root());
    assert!(child.is_root());
}

#[test]
fn replace_root_with_multiple_children() {
    let root = HotNode::new_tree("root");
    root.create_as_last_child("child0");
    root.create_as_last_child("child1");
    //  root
    //  |-- child0
    //  `-- child1

    assert!(matches!(
        root.replace_with_children(),
        Err(HierarchyError::SiblingsWithoutParent)
    ));
}

/// Config.
#[derive(Debug, Clone, Copy)]
struct Config {
    num_prev_siblings: usize,
    num_next_siblings: usize,
    num_children: usize,
}

/// Creates a tree with the given paremeters, and returns a pair of root and the target node.
///
/// Exmaple of the created tree:
///
/// ```text
/// root
/// |-- prev1
/// |-- prev0
/// |-- target
/// |   |-- child0
/// |   |-- child1
/// |   `-- child2
/// |-- next0
/// `-- next1
/// ```
///
/// Expected result of `target.replace_with_children()` is:
///
/// ```text
/// root
/// |-- prev1
/// |-- prev0
/// |-- child0
/// |-- child1
/// |-- child2
/// |-- next0
/// `-- next1
/// ```
fn create_source_tree_with_params(config: Config) -> (HotNode<String>, HotNode<String>) {
    let root = HotNode::new_tree("root".into());
    let target = root.create_as_last_child("target".into());

    for i in 0..config.num_prev_siblings {
        root.create_as_first_child(format!("prev{i}"));
    }
    for i in 0..config.num_next_siblings {
        root.create_as_last_child(format!("next{i}"));
    }
    for i in 0..config.num_children {
        target.create_as_last_child(format!("child{i}"));
    }

    (root, target)
}

fn create_result_events_with_params(config: Config) -> Vec<DftEvent<String>> {
    let mut vec = Vec::with_capacity(
        1 + config.num_prev_siblings + config.num_next_siblings + config.num_children,
    );
    vec.push(DftEvent::Open("root".into()));

    for i in (0..config.num_prev_siblings).rev() {
        let name = format!("prev{i}");
        vec.push(DftEvent::Open(name.clone()));
        vec.push(DftEvent::Close(name));
    }
    for i in 0..config.num_children {
        let name = format!("child{i}");
        vec.push(DftEvent::Open(name.clone()));
        vec.push(DftEvent::Close(name));
    }
    for i in 0..config.num_next_siblings {
        let name = format!("next{i}");
        vec.push(DftEvent::Open(name.clone()));
        vec.push(DftEvent::Close(name));
    }

    vec.push(DftEvent::Close("root".into()));
    vec
}

#[test]
fn replace_non_root() {
    const PREV_SIB_PARAMS: [usize; 3] = [0, 1, 2];
    const NEXT_SIB_PARAMS: [usize; 3] = [0, 1, 2];
    const CHILDREN_PARAMS: [usize; 3] = [0, 1, 2];

    for num_prev_siblings in PREV_SIB_PARAMS {
        for num_next_siblings in NEXT_SIB_PARAMS {
            for num_children in CHILDREN_PARAMS {
                let config = Config {
                    num_prev_siblings,
                    num_next_siblings,
                    num_children,
                };
                dbg!(&config);
                let (root, target) = create_source_tree_with_params(config);
                assert!(root.is_root());
                assert!(!target.is_root(), "config={config:?}");

                assert!(
                    target.replace_with_children().is_ok(),
                    "HotNode::replace_with_children should success (config={config:?})"
                );
                assert!(
                    root.is_root(),
                    "root must be still root (config={config:?})"
                );
                assert!(
                    target.is_root(),
                    "target must be a root (config={config:?})"
                );

                assert_eq!(
                    serialize_subtree(&root),
                    create_result_events_with_params(config),
                    "config={config:?}"
                );
            }
        }
    }
}
