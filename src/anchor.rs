//! Anchor types.

use crate::node::HotNode;
use crate::StructureError;

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

impl<T> InsertAs<T> {
    /// Converts the anchor type.
    pub fn map<U, F>(self, f: F) -> InsertAs<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Self::FirstChildOf(v) => InsertAs::FirstChildOf(f(v)),
            Self::LastChildOf(v) => InsertAs::LastChildOf(f(v)),
            Self::PreviousSiblingOf(v) => InsertAs::PreviousSiblingOf(f(v)),
            Self::NextSiblingOf(v) => InsertAs::NextSiblingOf(f(v)),
        }
    }

    /// Retruns a reference to the anchor.
    #[inline]
    pub(super) fn anchor(&self) -> &T {
        match self {
            Self::FirstChildOf(v)
            | Self::LastChildOf(v)
            | Self::PreviousSiblingOf(v)
            | Self::NextSiblingOf(v) => v,
        }
    }

    /// Returns the corresponding `AdoptAs` value.
    #[must_use]
    pub(super) fn to_adopt_as(&self) -> AdoptAs {
        match self {
            Self::FirstChildOf(_) => AdoptAs::FirstChild,
            Self::LastChildOf(_) => AdoptAs::LastChild,
            Self::PreviousSiblingOf(_) => AdoptAs::PreviousSibling,
            Self::NextSiblingOf(_) => AdoptAs::NextSibling,
        }
    }
}

impl<T> InsertAs<HotNode<T>> {
    /// Creates a new node and inserts to the destination.
    #[inline]
    pub(super) fn try_create_node(&self, data: T) -> Result<HotNode<T>, StructureError> {
        self.anchor().try_create_node_as(data, self.to_adopt_as())
    }
}
