# Change Log

## [Unreleased]

* Reorganize some modules (in non-breaking way).

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
