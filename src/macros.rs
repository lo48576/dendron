//! Macros.

/// A macro that evaluates to the root node of a new tree.
///
/// # Examples
///
/// ```
/// use dendron::tree_node;
/// use dendron::traverse::DftEvent::{Close, Open};
///
/// let root = tree_node! {
///     "root", [
///         ("0", [
///             ("0-0", []),
///             ("0-1", []),
///         ]),
///         ("1", []),
///         ("2", [
///             ("2-0", [
///                 ("2-0-0", []),
///             ]),
///             ("2-1", []),
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
    () => {
        compile_error!("tree should have a root node")
    };
    ($data:expr) => {
        $crate::Node::new_tree($data)
    };
    ($data:expr, [$($children:tt)*]) => {{
        let root = $crate::HotNode::new_tree($data);
        $crate::tree_node!(@@append_child, root, [$($children)*]);
        root.plain()
    }};
    (@@append_child, $parent:ident, [$(($child_data:expr, [$($descendants:tt)*])),* $(,)?]) => {{
        $({
            let node = $parent.create_as_last_child($child_data);
            $crate::tree_node!(@@append_child, node, [$($descendants)*]);
        })*
    }};
}
