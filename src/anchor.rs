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
