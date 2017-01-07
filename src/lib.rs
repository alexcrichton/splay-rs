//! Contains an implementation of splay trees where each node has a key/value
//! pair to be used in maps and sets. The only requirement is that the key must
//! implement the Ord trait.
//!
//! # Example
//!
//! ```rust
//! use splay::SplayMap;
//!
//! let mut map = SplayMap::new();
//! map.insert("foo", "bar");
//! map.insert("hello", "world");
//! map.insert("splay", "tree");
//!
//! for (k, v) in map.into_iter() {
//!     println!("{} => {}", k, v);
//! }
//! ```

#![doc(html_root_url = "http://alexcrichton.com/splay-rs")]
#![cfg_attr(test, deny(warnings))]

#[cfg(test)] extern crate rand;

pub use self::set::SplaySet;
pub use self::map::SplayMap;

pub mod set;
pub mod map;
mod node;

#[cfg(test)]
mod test {
    use super::{SplayMap, SplaySet};
    use std::ops::Range;

    // Lots of these are shamelessly stolen from the TreeMap tests, it'd be
    // awesome if they could share them...

    #[test]
    fn insert_simple() {
        let mut t = SplayMap::new();
        assert_eq!(t.insert(1, 2), None);
        assert_eq!(t.insert(1, 3), Some(2));
        assert_eq!(t.insert(2, 3), None);
    }

    #[test]
    fn remove_simple() {
        let mut t = SplayMap::new();
        assert_eq!(t.insert(1, 2), None);
        assert_eq!(t.insert(2, 3), None);
        assert_eq!(t.insert(3, 4), None);
        assert_eq!(t.insert(0, 5), None);
        assert_eq!(t.remove(&1), Some(2));
    }

    #[test]
    fn pop_simple() {
        let mut t = SplayMap::new();
        assert_eq!(t.insert(1, 2), None);
        assert_eq!(t.insert(2, 3), None);
        assert_eq!(t.insert(3, 4), None);
        assert_eq!(t.insert(0, 5), None);
        assert_eq!(t.remove(&1), Some(2));
        assert_eq!(t.remove(&1), None);
        assert_eq!(t.remove(&0), Some(5));
    }

    #[test]
    fn find_mut_simple() {
        let mut t = SplayMap::new();
        assert_eq!(t.insert(1, 2), None);
        assert_eq!(t.insert(2, 3), None);
        assert_eq!(t.insert(3, 4), None);
        assert_eq!(t.insert(0, 5), None);

        {
            let ptr = t.get_mut(&1);
            assert!(ptr.is_some());
            let ptr = ptr.unwrap();
            assert_eq!(*ptr, 2);
            *ptr = 4;
        }

        let ptr = t.get_mut(&1);
        assert!(ptr.is_some());
        assert_eq!(*ptr.unwrap(), 4);
    }

    #[test]
    fn test_len() {
        let mut m = SplayMap::new();
        assert_eq!(m.insert(3, 6), None);
        assert_eq!(m.len(), 1);
        assert_eq!(m.insert(0, 0), None);
        assert_eq!(m.len(), 2);
        assert_eq!(m.insert(4, 8), None);
        assert_eq!(m.len(), 3);
        assert_eq!(m.remove(&3), Some(6));
        assert_eq!(m.len(), 2);
        assert_eq!(m.remove(&5), None);
        assert_eq!(m.len(), 2);
        assert_eq!(m.insert(2, 4), None);
        assert_eq!(m.len(), 3);
        assert_eq!(m.insert(1, 2), None);
        assert_eq!(m.len(), 4);
    }

    #[test]
    fn test_clear() {
        let mut m = SplayMap::new();
        m.clear();
        assert_eq!(m.insert(5, 11), None);
        assert_eq!(m.insert(12, -3), None);
        assert_eq!(m.insert(19, 2), None);
        m.clear();
        assert_eq!(m.get(&5), None);
        assert_eq!(m.get(&12), None);
        assert_eq!(m.get(&19), None);
        assert!(m.is_empty());
    }

    #[test]
    fn insert_replace() {
        let mut m = SplayMap::new();
        assert_eq!(m.insert(5, 2), None);
        assert_eq!(m.insert(2, 9), None);
        assert_eq!(m.insert(2, 11), Some(9));
        assert_eq!(m[&2], 11);
    }

    #[test]
    fn find_empty() {
        let m: SplayMap<i32, i32> = SplayMap::new();
        assert_eq!(m.get(&5), None);
    }

    #[test]
    fn find_not_found() {
        let mut m = SplayMap::new();
        assert_eq!(m.insert(1, 2), None);
        assert_eq!(m.insert(5, 3), None);
        assert_eq!(m.insert(9, 3), None);
        assert_eq!(m.get(&2), None);
    }

    #[test]
    fn get_works() {
        let mut m = SplayMap::new();
        m.insert(1, 1);
        assert_eq!(m[&1], 1);
    }

    #[test]
    fn into_iter() {
        let mut m = SplayMap::new();
        m.insert(1, 1);
        m.insert(2, 1);
        m.insert(0, 1);
        let mut cur = 0;
        for (k, v) in m.into_iter() {
            assert_eq!(k, cur);
            assert_eq!(v, 1);
            cur += 1;
        }
    }

    #[test]
    fn into_iter_backwards() {
        let mut m = SplayMap::new();
        m.insert(1, 1);
        m.insert(2, 1);
        m.insert(0, 1);
        let mut cur = 2;
        for (k, v) in m.into_iter().rev() {
            assert_eq!(k, cur);
            assert_eq!(v, 1);
            cur -= 1;
        }
    }

    #[test] #[should_panic]
    fn get_panic_works() {
        let mut m = SplayMap::new();
        m.insert(2, 2);
        m[&1];
    }

    #[test]
    fn large() {
        use rand::random;
        let mut m = SplaySet::new();
        let mut v = Vec::new();

        for _ in 0..400 {
            let i: i32 = random();
            m.insert(i);
            v.push(i);
        }

        for i in v.iter() {
            assert!(m.contains(i));
        }
    }

    #[test]
    fn remove_range() {
        let mut m = SplaySet::new();
        let mut v = Vec::new();

        for i in 0..400 {
            m.insert(i);
            v.push(i);
        }

        let mut output = vec![];

        let m = &mut m;
        let output = &mut output;

        check_remove_range(m, 42..142, output, 42, 142);

        check_remove_range(m, 42..42, output, 42, 42);

        check_remove_range(m, 142..142, output, 142, 142);

        check_remove_range(m, 42..142, output, 142, 142);

        check_remove_range(m, 41..42, output, 41, 42);

        check_remove_range(m, 40..142, output, 40, 41);

        check_remove_range2(m, 39..143, output, vec![39, 142]);

        check_remove_range2(m, 1..399, output, (1..39).chain(143..399).collect());

        check_remove_range(m, 0..10, output, 0, 1);

        check_remove_range(m, 0..399, output, 0, 0);

        check_remove_range(m, 400..1000, output, 0, 0);

        check_remove_range(m, 399..400, output, 399, 400);

        assert!(m.is_empty(), "size={}", m.len());
    }


    fn check_remove_range(m: &mut SplaySet<usize>, range: Range<usize>, output: &mut Vec<usize>, expect_from: usize, expect_to: usize) {
        output.clear();
        m.remove_range(&range.start .. &range.end, output);
        assert!(output.len() == expect_to-expect_from, "len={}, output={:?}", output.len(), output);
        output.sort();
        assert_eq!(output, &mut (expect_from..expect_to).collect::<Vec<_>>(), "len={}, output={:?}", output.len(), output);
    }

    fn check_remove_range2(m: &mut SplaySet<usize>, range: Range<usize>, output: &mut Vec<usize>, mut expect_items: Vec<usize>) {
        output.clear();
        m.remove_range(&range.start .. &range.end, output);
        assert!(output.len() == expect_items.len(), "len={}, output={:?}", output.len(), output);
        output.sort();
        assert_eq!(output, &mut expect_items, "len={}, output={:?}", output.len(), output);
    }
}
