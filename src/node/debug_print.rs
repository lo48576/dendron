//! Debug printing of a subtree.

mod debug;
mod pretty;

use core::fmt;

pub use self::debug::{DebugPrintNodeLocal, DebugPrintSubtree};
pub use self::pretty::DebugPrettyPrint;

/// Fake option for debug printing.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum FakeOption {
    /// Fake `Some(_)`.
    Some,
    /// Fake `None`.
    None,
}

impl fmt::Debug for FakeOption {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FakeOption {
    /// Returns `Some` if the given value is true, `None` if false.
    #[inline]
    #[must_use]
    fn some_if_true(v: bool) -> Self {
        if v {
            Self::Some
        } else {
            Self::None
        }
    }

    /// Returns the string to be printed.
    #[inline]
    #[must_use]
    fn as_str(&self) -> &'static str {
        match self {
            Self::Some => "Some(_)",
            Self::None => "None",
        }
    }
}

/// Raw string for debug printing.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct RawStr<'a>(&'a str);

impl fmt::Debug for RawStr<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}
