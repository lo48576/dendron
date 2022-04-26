//! Macros.

/// A macro that evaluates to the root node of a new tree.
///
/// Syntax is simple:
///
/// * For non-root nodes:
///     + `data` to describe a leaf node.
///     + `(data, [descendants_recursive])` to describe a node with descendants.
/// * For the root node:
///     + `data` to describe single node tree.
///     + `data, [descendants_recursive]` to describe a tree with descendants.
///
/// # Examples
///
/// ```
/// use dendron::tree_node;
/// use dendron::traverse::DftEvent::{Close, Open};
///
/// //  root
/// //  |-- 0
/// //  |   |-- 0-0
/// //  |   `-- 0-1
/// //  |-- 1
/// //  `-- 2
/// //      |-- 2-0
/// //      |   `-- 2-0-0
/// //      `-- 2-1
/// let root = tree_node! {
///     "root", [
///         /("0", [
///             "0-0",
///             "0-1",
///         ]),
///         "1",
///         /("2", [
///             /("2-0", [
///                 "2-0-0",
///             ]),
///             "2-1",
///         ]),
///     ]
/// };
///
/// assert_eq!(
///     root.depth_first_traverse()
///         .map(|ev| ev.map(|node| *node.borrow_data()))
///         .collect::<Vec<_>>(),
///     &[
///         Open("root"),
///             Open("0"),
///                 Open("0-0"),
///                 Close("0-0"),
///                 Open("0-1"),
///                 Close("0-1"),
///             Close("0"),
///             Open("1"),
///             Close("1"),
///             Open("2"),
///                 Open("2-0"),
///                     Open("2-0-0"),
///                     Close("2-0-0"),
///                 Close("2-0"),
///                 Open("2-1"),
///                 Close("2-1"),
///             Close("2"),
///         Close("root"),
///     ]
/// );
/// ```
#[macro_export]
macro_rules! tree_node {
    // A tree should have a root node.
    () => {
        compile_error!("tree should have a root node")
    };
    // A tree without descendants.
    ($data:expr) => {
        $crate::Node::new_tree($data)
    };
    // A tree (possibly) with descendants.
    ($data:expr, [$($descendant:tt)*] $(,)?) => {{
        let root = $crate::HotNode::new_tree($data);
        $crate::tree_node!(@@process_descendant, root, [$($descendant)*]);
        root.plain()
    }};
    // The last non-leaf node.
    (@@process_descendant, $parent:ident, [
        /($data:expr, [$($descendant:tt)*]) $(,)?
    ]) => {
        {
            let node = $parent.create_as_last_child($data);
            $crate::tree_node!(@@process_descendant, node, [$($descendant)*]);
        }
    };
    // A non-last non-leaf node.
    (@@process_descendant, $parent:ident, [
        /($data:expr, [$($descendant:tt)*]),
        $($rest:tt)*
    ]) => {
        {
            let node = $parent.create_as_last_child($data);
            $crate::tree_node!(@@process_descendant, node, [$($descendant)*]);
        }
        $crate::tree_node!(@@process_descendant, $parent, [$($rest)*]);
    };
    // The last leaf node.
    (@@process_descendant, $parent:ident, [$data:expr $(,)?]) => {
        $parent.create_as_last_child($data);
    };
    // A non-last non-leaf node.
    (@@process_descendant, $parent:ident, [$data:expr, $($rest:tt)*]) => {
        $parent.create_as_last_child($data);
        $crate::tree_node!(@@process_descendant, $parent, [$($rest)*]);
    };
    // No children.
    (@@process_descendant, $parent:ident, []) => {};
}

/// A macro that evaluates to the root node of a new tree.
///
/// Syntax is simple:
///
/// * For non-root nodes:
///     + `data` to describe a leaf node.
///     + `(data, [descendants_recursive])` to describe a node with descendants.
/// * For the root node:
///     + `data` to describe single node tree.
///     + `data, [descendants_recursive]` to describe a tree with descendants.
///
/// See [`tree_node`] macro for usage examples.
#[macro_export]
macro_rules! tree {
    ($($tt:tt)*) => {
        $crate::tree_node!($($tt)*).tree()
    };
}
