//! Anchor types.

/// Relation of the node being `adopt`ed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdoptAs {
    /// As the first child.
    FirstChild,
    /// As the last child.
    LastChild,
    /// As the previous sibling.
    PreviousSibling,
    /// As the next sibling.
    NextSibling,
}

/// Target destination to insert, append, or prepend a node.
#[derive(Clone)]
// All variants have the common suffix "Of", but this is intended.
// Variants would be used as, for example, `InsertAs::FirsChildOf(some_node)`.
#[allow(clippy::enum_variant_names)]
pub enum InsertAs<T> {
    /// As the first child.
    FirstChildOf(T),
    /// As the last child.
    LastChildOf(T),
    /// As the previous sibling.
    PreviousSiblingOf(T),
    /// As the next sibling.
    NextSiblingOf(T),
}
