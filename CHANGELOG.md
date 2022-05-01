# Change Log

## [Unreleased]

* Reorganize some modules (in non-breaking way).
* Implement better and various debug formatting.
* Add weak reference types.

### Added
* Implement better and various debug formatting.
    + Add `debug_print_local` and `debug_print_subtree` methods to node types.
    + Add `debug_print_local` and `debug_print` methods to `Tree` type.
    + Add related debug-printable types:
        - `node::DebugPrintNodeLocal`
        - `node::DebugPrintSubtree`
        - `tree::DebugPrint`
        - `tree::DebugPrintLocal`
    + Make debug formatting of node types and `Tree` simpler and easier to read.
* Add weak reference types.
    + Add `TreeWeak` and `NodeWeak` types.
    + They can be upgradable to `Tree` and `Node` respectively if the target
      tree or node is still alive.

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

## [0.0.1]

Initial release.

[Unreleased]: <https://gitlab.com/nop_thread/dendron/-/compare/v0.0.1...develop>
[0.0.1]: <https://gitlab.com/nop_thread/dendron/-/tags/v0.0.1>
