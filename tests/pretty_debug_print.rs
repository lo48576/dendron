//! Tests for pretty debug printing.

use core::fmt;

use dendron::serial::Event;
use dendron::Node;

//  []
//  |-- [0]
//  |-- [1]
//  |   |-- [1, 0]
//  |   |   `-- [1, 0, 0]
//  |   |-- [1, 1]
//  |   `-- [1, 2]
//  |       `-- [1, 2, 0]
//  `-- [2]
//      |-- [2, 0]
//      |   `-- [2, 0, 0]
//      `-- [2, 1]
//          `-- [2, 1, 0]
fn sample_events() -> Vec<Event<Vec<i32>>> {
    vec![
        Event::Open(vec![]),
        Event::Open(vec![0]),
        Event::close(1),
        Event::Open(vec![1]),
        Event::Open(vec![1, 0]),
        Event::Open(vec![1, 0, 0]),
        Event::close(2),
        Event::Open(vec![1, 1]),
        Event::close(1),
        Event::Open(vec![1, 2]),
        Event::Open(vec![1, 2, 0]),
        Event::close(3),
        Event::Open(vec![2]),
        Event::Open(vec![2, 0]),
        Event::Open(vec![2, 0, 0]),
        Event::close(2),
        Event::Open(vec![2, 1]),
        Event::Open(vec![2, 1, 0]),
        Event::close(3),
    ]
}

#[derive(Clone)]
struct Label(Vec<i32>);

impl fmt::Debug for Label {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Use `Vec<i32>`'s debug formatting.
        self.0.fmt(f)
    }
}

impl fmt::Display for Label {
    // `1/2/3` for normal formatting, and `1 -> 2 -> 3` for alternate formatting.
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = self.0.iter();
        match iter.next() {
            Some(v) => write!(f, "{v}")?,
            None => return write!(f, "root"),
        }
        if f.alternate() {
            iter.try_for_each(|v| write!(f, " -> {v}"))
        } else {
            iter.try_for_each(|v| write!(f, "/{v}"))
        }
    }
}

fn sample_tree() -> Node<Label> {
    sample_events()
        .into_iter()
        .map(|ev| ev.map(Label))
        .collect::<Result<_, _>>()
        .expect("valid events that can construct tree")
}

#[test]
fn debug() {
    const EXPECTED: &str = r#"[]
|-- [0]
|-- [1]
|   |-- [1, 0]
|   |   `-- [1, 0, 0]
|   |-- [1, 1]
|   `-- [1, 2]
|       `-- [1, 2, 0]
`-- [2]
    |-- [2, 0]
    |   `-- [2, 0, 0]
    `-- [2, 1]
        `-- [2, 1, 0]"#;

    assert_eq!(
        format!("{:?}", sample_tree().debug_pretty_print()),
        EXPECTED
    );
}

#[test]
fn debug_alternate() {
    const EXPECTED: &str = r#"[]
|-- [
|       0,
|   ]
|-- [
|       1,
|   ]
|   |-- [
|   |       1,
|   |       0,
|   |   ]
|   |   `-- [
|   |           1,
|   |           0,
|   |           0,
|   |       ]
|   |-- [
|   |       1,
|   |       1,
|   |   ]
|   `-- [
|           1,
|           2,
|       ]
|       `-- [
|               1,
|               2,
|               0,
|           ]
`-- [
        2,
    ]
    |-- [
    |       2,
    |       0,
    |   ]
    |   `-- [
    |           2,
    |           0,
    |           0,
    |       ]
    `-- [
            2,
            1,
        ]
        `-- [
                2,
                1,
                0,
            ]"#;

    assert_eq!(
        format!("{:#?}", sample_tree().debug_pretty_print()),
        EXPECTED
    );
}

#[test]
fn display() {
    const EXPECTED: &str = r#"root
|-- 0
|-- 1
|   |-- 1/0
|   |   `-- 1/0/0
|   |-- 1/1
|   `-- 1/2
|       `-- 1/2/0
`-- 2
    |-- 2/0
    |   `-- 2/0/0
    `-- 2/1
        `-- 2/1/0"#;

    assert_eq!(format!("{}", sample_tree().debug_pretty_print()), EXPECTED);
}

#[test]
fn display_alternate() {
    const EXPECTED: &str = r#"root
|-- 0
|-- 1
|   |-- 1 -> 0
|   |   `-- 1 -> 0 -> 0
|   |-- 1 -> 1
|   `-- 1 -> 2
|       `-- 1 -> 2 -> 0
`-- 2
    |-- 2 -> 0
    |   `-- 2 -> 0 -> 0
    `-- 2 -> 1
        `-- 2 -> 1 -> 0"#;

    assert_eq!(
        format!("{:#}", sample_tree().debug_pretty_print()),
        EXPECTED
    );
}
