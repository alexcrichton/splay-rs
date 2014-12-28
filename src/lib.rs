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

#![feature(unsafe_destructor)]
//#![cfg_attr(not(test), deny(experimental, unstable))]

pub use set::SplaySet;
pub use map::SplayMap;

pub mod set;
pub mod map;
mod node;

#[cfg(test)]
mod test {
    use super::{SplayMap, SplaySet};

    // Lots of these are shamelessly stolen from the TreeMap tests, it'd be
    // awesome if they could share them...

    #[test]
    fn insert_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1i, 2i));
        assert!(!t.insert(1, 3));
        assert!(t.insert(2, 3));
    }

    #[test]
    fn remove_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1i, 2i));
        assert!(t.insert(2, 3));
        assert!(t.insert(3, 4));
        assert!(t.insert(0, 5));
        assert!(t.remove(&1));
    }

    #[test]
    fn pop_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1i, 2i));
        assert!(t.insert(2, 3));
        assert!(t.insert(3, 4));
        assert!(t.insert(0, 5));
        assert_eq!(t.pop(&1), Some(2));
        assert_eq!(t.pop(&1), None);
        assert_eq!(t.pop(&0), Some(5));
    }

    #[test]
    fn find_mut_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1i, 2i));
        assert!(t.insert(2, 3));
        assert!(t.insert(3, 4));
        assert!(t.insert(0, 5));

        {
            let ptr = t.find_mut(&1);
            assert!(ptr.is_some());
            let ptr = ptr.unwrap();
            assert!(*ptr == 2);
            *ptr = 4;
        }

        let ptr = t.find_mut(&1);
        assert!(ptr.is_some());
        assert!(*ptr.unwrap() == 4);
    }

    #[test]
    fn test_len() {
        let mut m = SplayMap::new();
        assert!(m.insert(3i, 6i));
        assert!(m.len() == 1);
        assert!(m.insert(0, 0));
        assert!(m.len() == 2);
        assert!(m.insert(4, 8));
        assert!(m.len() == 3);
        assert!(m.remove(&3));
        assert!(m.len() == 2);
        assert!(!m.remove(&5));
        assert!(m.len() == 2);
        assert!(m.insert(2, 4));
        assert!(m.len() == 3);
        assert!(m.insert(1, 2));
        assert!(m.len() == 4);
    }

    #[test]
    fn test_clear() {
        let mut m = SplayMap::new();
        m.clear();
        assert!(m.insert(5i, 11i));
        assert!(m.insert(12, -3));
        assert!(m.insert(19, 2));
        m.clear();
        assert!(m.find(&5).is_none());
        assert!(m.find(&12).is_none());
        assert!(m.find(&19).is_none());
        assert!(m.is_empty());
    }

    #[test]
    fn insert_replace() {
        let mut m = SplayMap::new();
        assert!(m.insert(5i, 2i));
        assert!(m.insert(2, 9));
        assert!(!m.insert(2, 11));
        assert!(m.find(&2).unwrap() == &11);
    }

    #[test]
    fn find_empty() {
        let m: SplayMap<int, int> = SplayMap::new();
        assert!(m.find(&5) == None);
    }

    #[test]
    fn find_not_found() {
        let mut m = SplayMap::new();
        assert!(m.insert(1i, 2i));
        assert!(m.insert(5, 3));
        assert!(m.insert(9, 3));
        assert!(m.find(&2) == None);
    }

    #[test]
    fn get_works() {
        let mut m = SplayMap::new();
        m.insert(1i, 1i);
        assert!(m[1] == 1);
    }

    #[test]
    fn into_iter() {
        let mut m = SplayMap::new();
        m.insert(1i, 1i);
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
        m.insert(1i, 1i);
        m.insert(2, 1);
        m.insert(0, 1);
        let mut cur = 2;
        for (k, v) in m.into_iter().rev() {
            assert_eq!(k, cur);
            assert_eq!(v, 1);
            cur -= 1;
        }
    }

    #[test] #[should_fail]
    fn get_panic_works() {
        let mut m = SplayMap::new();
        m.insert(2i, 2i);
        m[1];
    }

    #[test]
    fn large() {
        use std::rand::random;
        let mut m = SplaySet::new();
        let mut v = Vec::new();

        for _ in range(0i, 400) {
            let i: int = random();
            m.insert(i);
            v.push(i);
        }

        for i in v.iter() {
            assert!(m.contains(i));
        }
    }
}
