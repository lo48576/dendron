# Comparison among other crates

`dendron` provides a strict tree and reference counting that is easy to manage.

* A tree has a single (not multiple) root node.
* Root node does not have siblings.
* Reference to any node preserves entire tree.
* No "invalid node reference" can possible for strong reference.

Of course, there are also downsides:

* Partial multithreading support.
    + Trees cannot be shared directly, but sent (copied) between threads.
* Indexed access to children is `O(N)`.
    + Think of childrens as managed by doubly linked list.

Let's compare major tree structrure crates [`rctree`] and [`indextree`] from
these points of view.

[`rctree`]: https://crates.io/crates/rctree
[`indextree`]: https://crates.io/crates/indextree

| feature | `dendron` | `rctree` | `indextree` |
|:--------|----------:|---------:|------------:|
| root node does not have siblings | yes | no | no |
| reference to any node preserves entire tree | yes | no | no |
| no "strong invalid node reference" | yes | yes | no |
| multithreading support | partial | no | yes |
| efficient indexed access to a child | no | no | yes |

## Root node does not have siblings

By definition, a tree tree should have no siblings.

```rust
// dendron v0.1.1
use dendron::HotNode;

fn main() {
    let root = HotNode::new_tree("root");
    // Root node cannot have sibling.
    assert!(root.try_create_as_next_sibling("sibling").is_err());
}
```

`rctree` allows a root node to have siblings.

```rust
// rctree v0.4.0
use rctree::Node;

fn main() {
    let mut root = Node::new("root");
    root.insert_after(Node::new("sibling"));
    // Root node can have a sibling!?
    assert!(root.next_sibling().is_some());
}
```

`indextree` also allows a root node to have siblings.

```rust
// indextree v4.4.0
use indextree::Arena;

fn main() {
    let mut arena = Arena::new();
    let root = arena.new_node("root");
    let sibling = arena.new_node("sibling");
    root.insert_after(sibling, &mut arena);
    // Root node can have a sibling!?
    assert!(arena[root].next_sibling().is_some());
}
```

## Reference to any node preserves entire tree

Using `dendron`, you can preserve and access entire tree only using a reference
to a descendant node.

```rust
// dendron v0.1.1
use dendron::{HotNode, Node};

fn build_tree_and_return_descendant() -> Node<&'static str> {
    let root = HotNode::new_tree("root");
    root.create_as_last_child("0");
    root.create_as_last_child("1");
    let child2 = root.create_as_last_child("2");
    let child2_0 = child2.create_as_last_child("2-0");
    child2.create_as_last_child("2-1");
    //  root
    //  |-- 0
    //  |-- 1
    //  `-- 2
    //      |-- 2-0
    //      `-- 2-1
    child2_0.plain()
}

fn main() {
    let child2_0 = build_tree_and_return_descendant();
    // A descendant node preserves the entire tree!
    assert!(child2_0.parent().is_some());
    assert!(child2_0.next_sibling().is_some());
    assert_eq!(*child2_0.root().borrow_data(), "root");
}
```

`Node` in `rctree` does not preserve ancestors, so carrying only a descendant
ends up in dropped neighbors (see <https://github.com/RazrFalcon/rctree/issues/11>).
If you want to move a tree like this, you should also bring the root node around
as if the root node is "arena".

```rust
// rctree v0.4.0
use rctree::Node;

fn build_tree_and_return_descendant() -> Node<&'static str> {
    let mut root = Node::new("root");
    let child0 = Node::new("0");
    let child1 = Node::new("1");
    let mut child2 = Node::new("2");
    let child2_0 = Node::new("2-0");
    let child2_1 = Node::new("2-1");
    root.append(child0);
    root.append(child1);
    root.append(child2.clone());
    child2.append(child2_0.clone());
    child2.append(child2_1);
    //  root
    //  |-- 0
    //  |-- 1
    //  `-- 2
    //      |-- 2-0
    //      `-- 2-1
    child2_0
}

fn main() {
    let child2_0 = build_tree_and_return_descendant();

    // These assertion succeeds... This means a descendant node does not
    // preserve the entire tree while nodes in the tree are connected.
    assert!(child2_0.parent().is_none(), "`child2` no longer exist!");
    assert!(child2_0.next_sibling().is_none(), "`child2_1` no longer exist!");
}
```

`indextree` uses arena to manage actual nodes data, so carrying only `NodeId` of
a descendant you cannot access to a tree.

```rust
// indextree v4.4.0
use indextree::{Arena, NodeId};

fn build_tree_and_return_descendant() -> (Arena<&'static str>, NodeId) {
    let mut arena = Arena::new();
    let root = arena.new_node("root");
    let child0 = arena.new_node("0");
    let child1 = arena.new_node("1");
    let child2 = arena.new_node("2");
    let child2_0 = arena.new_node("2-0");
    let child2_1 = arena.new_node("2-1");
    root.append(child0, &mut arena);
    root.append(child1, &mut arena);
    root.append(child2, &mut arena);
    child2.append(child2_0, &mut arena);
    child2.append(child2_1, &mut arena);
    //  root
    //  |-- 0
    //  |-- 1
    //  `-- 2
    //      |-- 2-0
    //      `-- 2-1
    (arena, child2_0)
}

fn main() {
    let (arena, child2_0) = build_tree_and_return_descendant();
    // You can do nothing without carrying arena everywhere!
    assert!(arena[child2_0].parent().is_some());
    assert!(arena[child2_0].next_sibling().is_some());
}
```

### No "invalid node reference" can possible for strong reference

Arena and node ID values are independent objects in `indextree`, so when
mismatching pairs are used, they can silently success with unintentional result.
Additionally, every node reference can fail since they are possibly mismatched
but cannot validated at compile time.

```rust
// indextree v4.4.0
use indextree::Arena;

fn main() {
    let mut arena = Arena::new();
    let root = arena.new_node("root");
    let another_root = arena.new_node("another-root");

    let mut another_arena = Arena::new();
    another_arena.new_node(42);

    // Random node reference!
    println!("another_arena[root] = {}", another_arena[root].get());
    // Reference can fail!
    assert!(another_arena.get(another_root).is_none());
}
```

Node reference types in `dendron` (v0.1.1) and `rctree` (v0.4.0) directly refer
the internal node data, so this kind of problems are not present.

### Multithreading support

`indextree` supports sending a tree between threads.
Additionally, it supports read-only shared access to an arena from multiple
threads.

```rust
// indextree v0.4.0
use indextree::{Arena, NodeId};

fn build_tree() -> (Arena<&'static str>, NodeId) {
    let mut arena = Arena::new();
    let root = arena.new_node("root");
    let child0 = arena.new_node("child0");
    let child1 = arena.new_node("child1");
    root.append(child0, &mut arena);
    root.append(child1, &mut arena);

    (arena, root)
}

fn main() {
    let (arena, root) = std::thread::spawn(build_tree)
        .join()
        .expect("join successfully");

    assert_eq!(*arena[root].get(), "root");
    assert!(arena[root].first_child().is_some());
}
```

`dendron` supports sending a tree (or a subtree) between threads, but it needs
explicit serialization and deserialization.

Read-only shared access from multiple threads are not supported (since `dendron`
internally uses `Rc`).

```rust
// dendron v0.1.1
use dendron::serial::Event;
use dendron::{tree_node, Node};

fn build_tree() -> Vec<Event<&'static str>> {
    let root = tree_node! {
        "root", ["0", "1"]
    };
    // Serialize a tree to series of events.
    root.to_events()
        .collect::<Result<Vec<_>, _>>()
        .expect("no node data are borrowed exculsively now")
}

fn main() {
    let events = std::thread::spawn(build_tree)
        .join()
        .expect("join successfully");
    // Deserialize a tree to series of events.
    // Use `Iterator::collect()`.
    let root = events
        .into_iter()
        .collect::<Result<Node<_>, _>>()
        .expect("events are generated from valid tree");

    assert_eq!(*root.borrow_data(), "root");
}
```
