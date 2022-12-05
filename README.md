# dendron

![Minimum supported rustc version: 1.59](https://img.shields.io/badge/rustc-1.59+-lightgray.svg)

Generic tree data structure.

## Yet another tree structure?

See [the comparison of crates](docs/comparison.md).

| feature | `dendron` | `rctree` | `indextree` |
|:--------|----------:|---------:|------------:|
| root node does not have siblings | yes | no | no |
| reference to any node preserves entire tree | yes | no | no |
| no "strong invalid node reference" | yes | yes | no |
| multithreading support | partial | no | yes |
| efficient indexed access to a child | no | no | no |

In short, you will prefer `dendron` especially when you are manipulating
DOM-like structure, for example:

* detaching subtree as independent tree,
* joining multiple trees into single tree,
* detaching subtree and transplanting it to another place,
* iterating nodes, and/or
* navigating to parent, adjacent siblings, and children.

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE.txt](LICENSE-APACHE.txt) or
  <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT.txt](LICENSE-MIT.txt) or
  <https://opensource.org/licenses/MIT>)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
