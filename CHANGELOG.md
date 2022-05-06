# Change Log

## [Unreleased]
* Implement `Clone` for `Tree<T>` and `TreeWeak<T>`.

### Added
* Implement `Clone` for `Tree<T>` and `TreeWeak<T>`.


## [0.1.2]

* Add `belongs_to` methods to node types.
* Make `Tree` track the new root when `replace_with_children()` is called on the root.
* Add `insert_as_interrupting_{parent,child}` methods to editable node types.

### Added
* Add `belongs_to` methods to node types.
* Add `insert_as_interrupting_{parent,child}` methods to editable node types.
    + Add methods:
        - `Node::insert_as_interrupting_parent`
        - `Node::insert_as_interrupting_child`
        - `HotNode::insert_as_interrupting_parent`
        - `HotNode::insert_as_interrupting_child`

### Fixed
* Make `Tree` track the new root when `replace_with_children()` is called on the root.


## [0.1.1]

* Reorganize some modules (in non-breaking way).
* Implement better and various debug formatting.
* Implement events-to-tree conversion.
* Add weak reference types.
* Add constant-time `num_children` methods to node types.
* Deprecate O(N) methods to count children.

### Added
* Implement better and various debug formatting.
    + Add `debug_print_local` and `debug_print_subtree` methods to node types.
    + Add `debug_print_local` and `debug_print` methods to `Tree` type.
    + Add `debug_pretty_print` method to `Tree` type.
    + Add related debug-printable types:
        - `node::DebugPrintNodeLocal`
        - `node::DebugPrintSubtree`
        - `tree::DebugPrettyPrint`
        - `tree::DebugPrint`
        - `tree::DebugPrintLocal`
    + Make debug formatting of node types and `Tree` simpler and easier to read.
* Add weak reference types.
    + Add `TreeWeak` and `NodeWeak` types.
    + They can be upgradable to `Tree` and `Node` respectively if the target
      tree or node is still alive.
* Implement events-to-tree conversion.
    + Add trait implementation
      `FromIterator<serial::Event<T>> for Result<Tree<T>, TreeBuilderError>`.
* Add constant-time `num_children` methods to node types.
    + Now nodes caches the number of its children, so `num_children` is O(1)
      operaiton.
    + Deprecate O(N) methods to count children in favor of `num_children`.
        + `count_children()` is now equivalent to `num_children()`.
        + `has_multiple_children()` is now equivalent to `num_children() > 1`.
        + `has_one_child()` is now equivalent to `num_children() == 1`.

### Non-breaking changes
* Reorganize some modules.
    + Make `node` and `tree` modules public.
    + Items exported from the crate toplevel are still available, though some of
      them are deprecated in favor of the new paths in deeper modules.

### Deprecations
* `crate::DebugPrettyPrint` is deprecated
    + in favor of the new path `node::DebugPrettyPrint`.
* `crate::HierarchyEditGrantError` is deprecated
    + in favor of the new path `tree::HierarchyEditGrantError`.
* `crate::HierarchyEditProhibitionError` is deprecated
    + in favor of the new path `tree::HierarchyEditProhibitionError`.
* `count_children` method of node types are deprecated
    + in favor of the new name `num_children`.
* `has_multiple_children` method of node types are deprecated
    + in favor of another method `num_children`.
* `has_one_child` method of node types are deprecated
    + in favor of another method `num_children`.


## [0.1.0]

Initial release.

[Unreleased]: <https://gitlab.com/nop_thread/dendron/-/compare/v0.1.2...develop>
[0.1.2]: <https://gitlab.com/nop_thread/dendron/-/tags/v0.1.2>
[0.1.1]: <https://gitlab.com/nop_thread/dendron/-/tags/v0.1.1>
[0.1.0]: <https://gitlab.com/nop_thread/dendron/-/tags/v0.1.0>
