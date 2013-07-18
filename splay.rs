//! Contains an implementation of splay trees where each node has a key/value
//! pair to be used in maps and sets. The only requirement is that the key must
//! implement the TotalOrd trait.

#[link(name = "splay", vers = "0.0")];
#[license = "MIT"];
#[crate_type = "lib"];

use std::cast;
use std::util;

/// The implementation of this splay tree is largely based on the c code at:
///     ftp://ftp.cs.cmu.edu/usr/ftp/usr/sleator/splaying/top-down-splay.c
/// This version of splaying is a top-down splay operation.
pub struct SplayMap<K, V> {
    priv root: Option<~Node<K, V>>,
    priv size: uint,
}

pub struct SplaySet<T> {
    map: SplayMap<T, ()>
}

struct Node<K, V> {
  key: K,
  value: V,
  left: Option<~Node<K, V>>,
  right: Option<~Node<K, V>>,
}

/// Performs a top-down splay operation on a tree rooted at `node`. This will
/// modify the pointer to contain the new root of the tree once the splay
/// operation is done. When finished, if `key` is in the tree, it will be at the
/// root. Otherwise the closest key to the specified key will be at the root.
fn splay<K: TotalOrd, V>(key: &K, node: &mut ~Node<K, V>) {
    let mut newleft = None;
    let mut newright = None;

    // Eplicitly grab a new scope so the loans on newleft/newright are
    // terminated before we move out of them.
    {
        // Yes, these are backwards, that's intentional.
        let mut l = &mut newright;
        let mut r = &mut newleft;

        loop {
            match key.cmp(&node.key) {
                // Found it, yay!
                Equal => { break }

                Less => {
                    match node.pop_left() {
                        None => { break }
                        Some(left) => {
                            let mut left = left;
                            // rotate this node right if necessary
                            if key.cmp(&left.key) == Less {
                                // A bit odd, but avoids drop glue
                                util::swap(&mut node.left, &mut left.right);
                                util::swap(&mut left, node);
                                let none = util::replace(&mut node.right,
                                                         Some(left));
                                match util::replace(&mut node.left, none) {
                                    Some(l) => { left = l; }
                                    None    => { break }
                                }
                            }

                            let prev = util::replace(node, left);
                            forget(r, Some(prev));
                            let tmp = r;
                            r = &mut tmp.get_mut_ref().left;
                        }
                    }
                }

                // If you look closely, you may have seen some similar code
                // before
                Greater => {
                    match node.pop_right() {
                        None => { break }
                        // rotate left if necessary
                        Some(right) => {
                            let mut right = right;
                            if key.cmp(&right.key) == Greater {
                                util::swap(&mut node.right, &mut right.left);
                                util::swap(&mut right, node);
                                let none = util::replace(&mut node.left,
                                                         Some(right));
                                match util::replace(&mut node.right, none) {
                                    Some(r) => { right = r; }
                                    None    => { break }
                                }
                            }
                            let prev = util::replace(node, right);
                            forget(l, Some(prev));
                            let tmp = l;
                            l = &mut tmp.get_mut_ref().right;
                        }
                    }
                }
            }
        }

        util::swap(l, &mut node.left);
        util::swap(r, &mut node.right);
    }

    forget(&mut node.left, newright);
    forget(&mut node.right, newleft);
}

impl<K: TotalOrd, V> SplayMap<K, V> {
    pub fn new() -> SplayMap<K, V> { SplayMap{ root: None, size: 0 } }

    /// Similar to `find`, but fails if the key is not present in the map
    pub fn get<'a>(&'a self, k: &K) -> &'a V {
        self.find(k).expect("key not present in SplayMap")
    }

    /// Similar to `find_mut`, but fails if the key is not present in the map
    pub fn get_mut<'a>(&'a mut self, k: &K) -> &'a mut V {
        self.find_mut(k).expect("key not present in SplayMap")
    }

    /// Visit all values in order
    #[inline(always)]
    fn each<'a>(&'a self, f: &fn(&K, &'a V) -> bool) -> bool {
        self.root.iter().advance(|n| n.each(|a, b| f(a, b)))
    }

    /// Iterate over the map and mutate the contained values
    #[inline(always)]
    fn mutate_values(&mut self, f: &fn(&K, &mut V) -> bool) -> bool {
        self.root.mut_iter().advance(|n| n.each_mut(|a, b| f(a, b)))
    }

    /// Visit all keys in order
    #[inline(always)]
    fn each_key(&self, f: &fn(&K) -> bool) -> bool { self.each(|k, _| f(k)) }

    /// Visit all values in order
    #[inline(always)]
    fn each_value<'a>(&'a self, f: &fn(&'a V) -> bool) -> bool {
        self.each(|_, v| f(v))
    }
}

impl<K, V> Container for SplayMap<K, V> {
    fn len(&const self) -> uint { self.size }
    fn is_empty(&const self) -> bool { self.len() == 0 }
}

impl<K, V> Mutable for SplayMap<K, V> {
    fn clear(&mut self) {
        self.root = None;
        self.size = 0;
    }
}

impl<K: TotalOrd, V> Map<K, V> for SplayMap<K, V> {
    /// Return true if the map contains a value for the specified key
    #[inline(always)]
    fn contains_key(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    /// Return a reference to the value corresponding to the key
    fn find<'a>(&'a self, key: &K) -> Option<&'a V> {
        // Splay trees are self-modifying, so they can't exactly operate with
        // the immutable self given by the Map interface for this method. It can
        // be guaranteed, however, that the callers of this method are not
        // modifying the tree, they may just be rotating it. Each node is a
        // pointer on the heap, so we know that none of the pointers inside
        // these nodes (the value returned from this function) will be moving.
        //
        // With this in mind, we can unsafely use a mutable version of this tree
        // to invoke the splay operation and return a pointer to the inside of
        // one of the nodes (the pointer won't be deallocated or moved).
        unsafe {
            let this = cast::transmute_mut(self);
            this.find_mut(key).map_consume(cast::transmute_immut)
        }
    }
}

impl<K: TotalOrd, V> MutableMap<K, V> for SplayMap<K, V> {
    /// Return a mutable reference to the value corresponding to the key
    fn find_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        match self.root {
            None => { return None; }
            Some(ref mut root) => {
                splay(key, root);
                if key.equals(&root.key) {
                    return Some(&mut root.value);
                }
                return None;
            }
        }
    }

    /// Insert a key-value pair into the map. An existing value for a
    /// key is replaced by the new value. Return true if the key did
    /// not already exist in the map.
    #[inline(always)]
    fn insert(&mut self, key: K, value: V) -> bool {
        self.swap(key, value).is_none()
    }

    /// Insert a key-value pair from the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise None is returned.
    fn swap(&mut self, key: K, value: V) -> Option<V> {
        match self.root {
            None => {
                /* is forget necessary or is llvm smarter than that? */
                forget(&mut self.root, Some(Node::new(key, value, None, None)));
            }
            Some(ref mut root) => {
                splay(&key, root);

                match key.cmp(&root.key) {
                    Equal => {
                        let old = util::replace(&mut root.value, value);
                        return Some(old);
                    }
                    /* TODO: would unsafety help perf here? */
                    Less => {
                        let left = root.pop_left();
                        let new = Node::new(key, value, left, None);
                        let prev = util::replace(root, new);
                        forget(&mut root.right, Some(prev));
                    }
                    Greater => {
                        let right = root.pop_right();
                        let new = Node::new(key, value, None, right);
                        let prev = util::replace(root, new);
                        forget(&mut root.left, Some(prev));
                    }
                }
            }
        }
        self.size += 1;
        return None;
    }

    /// Remove a key-value pair from the map. Return true if the key
    /// was present in the map, otherwise false.
    #[inline(always)]
    fn remove(&mut self, key: &K) -> bool {
        self.pop(key).is_some()
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    fn pop(&mut self, key: &K) -> Option<V> {
        match self.root {
            None => { return None; }
            Some(ref mut root) => {
                splay(key, root);
                if !key.equals(&root.key) { return None; }
            }
        }

        // TODO: Extra storage of None isn't necessary
        let (value, left, right) = match self.root.take_unwrap() {
            ~Node {left, right, value, _} => (value, left, right)
        };

        match left {
            None => { forget(&mut self.root, right); }
            Some(node) => {
                let mut node = node;
                splay(key, &mut node);
                forget(&mut node.right, right);
                forget(&mut self.root, Some(node));
            }
        }

        self.size -= 1;
        return Some(value);
    }
}

impl<K: TotalOrd, V: Eq> Eq for SplayMap<K, V> {
  fn eq(&self, other: &SplayMap<K, V>) -> bool {
    if self.len() != other.len() {
      return false;
    }
    for self.each |k, v| {
      match other.find(k) {
        None => { return false; }
        Some(v2) if v != v2 => { return false; }
        Some(_) => {}
      }
    }
    return true;
  }

  fn ne(&self, other: &SplayMap<K, V>) -> bool { !self.eq(other) }
}

impl<T> Container for SplaySet<T> {
    #[inline(always)]
    fn len(&const self) -> uint { self.map.len() }
    #[inline(always)]
    fn is_empty(&const self) -> bool { self.map.is_empty() }
}

impl<T> Mutable for SplaySet<T> {
    #[inline(always)]
    fn clear(&mut self) { self.map.clear() }
}

impl<T: TotalOrd> Set<T> for SplaySet<T> {
    /// Return true if the set contains a value
    #[inline(always)]
    pub fn contains(&self, t: &T) -> bool { self.map.contains_key(t) }

    pub fn is_disjoint(&self, _: &SplaySet<T>) -> bool { fail!(); }
    pub fn is_subset(&self, _: &SplaySet<T>) -> bool { fail!(); }
    pub fn is_superset(&self, _: &SplaySet<T>) -> bool { fail!(); }
    pub fn difference(&self, _: &SplaySet<T>, _: &fn(&T) -> bool) -> bool {
        fail!();
    }
    pub fn symmetric_difference(&self, _: &SplaySet<T>, _: &fn(&T) -> bool) -> bool {
        fail!();
    }
    pub fn intersection(&self, _: &SplaySet<T>, _: &fn(&T) -> bool) -> bool {
        fail!();
    }
    pub fn union(&self, _: &SplaySet<T>, _: &fn(&T) -> bool) -> bool {
        fail!();
    }
}

impl<T: TotalOrd> MutableSet<T> for SplaySet<T> {
    /// Add a value to the set. Return true if the value was not already
    /// present in the set.
    #[inline(always)]
    pub fn insert(&mut self, t: T) -> bool { self.map.insert(t, ()) }

    /// Remove a value from the set. Return true if the value was
    /// present in the set.
    #[inline(always)]
    pub fn remove(&mut self, t: &T) -> bool { self.map.remove(t) }
}

impl<T: TotalOrd> SplaySet<T> {
    /// Creates a new empty set
    pub fn new() -> SplaySet<T> { SplaySet { map: SplayMap::new() } }

    /// Iterates over all values contained in the set
    pub fn each(&self, f: &fn(&T) -> bool) -> bool {
      self.map.each_key(f)
    }
}

impl<T: TotalOrd> Eq for SplaySet<T> {
  pub fn eq(&self, other: &SplaySet<T>) -> bool { self.map == other.map }
  pub fn ne(&self, other: &SplaySet<T>) -> bool { self.map != other.map }
}

impl<K: TotalOrd, V> Node<K, V> {
    fn new(k: K, v: V, l: Option<~Node<K, V>>,
           r: Option<~Node<K, V>>) -> ~Node<K, V> {
        ~Node{ key: k, value: v, left: l, right: r }
    }

    fn each<'a>(&'a self, f: &fn(&K, &'a V) -> bool) -> bool {
        self.left.iter().advance(|l| l.each(|a, b| f(a, b))) &&
            f(&self.key, &self.value) &&
            self.right.iter().advance(|r| r.each(|a, b| f(a, b)))
    }

    fn each_mut(&mut self, f: &fn(&K, &mut V) -> bool) -> bool {
        self.left.mut_iter().advance(|l| l.each_mut(|a, b| f(a, b))) &&
            f(&self.key, &mut self.value) &&
            self.right.mut_iter().advance(|r| r.each_mut(|a, b| f(a, b)))
    }

    #[inline(always)]
    fn pop_left(&mut self) -> Option<~Node<K, V>> {
        util::replace(&mut self.left, None)
    }

    #[inline(always)]
    fn pop_right(&mut self) -> Option<~Node<K, V>> {
        util::replace(&mut self.right, None)
    }
}

#[inline(always)]
fn forget<K, V>(slot: &mut Option<~Node<K, V>>, node: Option<~Node<K, V>>) {
    use std::cast;
    let prev = util::replace(slot, node);
    unsafe { cast::forget(prev) }
}

#[cfg(test)]
mod test {
    use super::*;

    // Lots of these are shamelessly stolen from the TreeMap tests, it'd be
    // awesome if they could share them...

    #[test]
    fn insert_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1, 2));
        assert!(!t.insert(1, 3));
        assert!(t.insert(2, 3));
    }

    #[test]
    fn remove_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1, 2));
        assert!(t.insert(2, 3));
        assert!(t.insert(3, 4));
        assert!(t.insert(0, 5));
        assert!(t.remove(&1));
    }

    #[test]
    fn pop_simple() {
        let mut t = SplayMap::new();
        assert!(t.insert(1, 2));
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
        assert!(t.insert(1, 2));
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
    fn each_simple() {
        let mut m = SplayMap::new();
        assert!(m.insert(3, 6));
        assert!(m.insert(0, 0));
        assert!(m.insert(4, 8));
        assert!(m.insert(2, 4));
        assert!(m.insert(1, 2));

        let mut n = 0;
        for m.each |k, v| {
            assert!(*k == n);
            assert!(*v == n * 2);
            n += 1;
        }
    }

    #[test]
    fn test_len() {
        let mut m = SplayMap::new();
        assert!(m.insert(3, 6));
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
        assert!(m.insert(5, 11));
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
        assert!(m.insert(5, 2));
        assert!(m.insert(2, 9));
        assert!(!m.insert(2, 11));
        assert!(m.find(&2).unwrap() == &11);
    }

    #[test]
    fn find_empty() {
        let m = SplayMap::new::<int, int>();
        assert!(m.find(&5) == None);
    }

    #[test]
    fn find_not_found() {
        let mut m = SplayMap::new();
        assert!(m.insert(1, 2));
        assert!(m.insert(5, 3));
        assert!(m.insert(9, 3));
        assert!(m.find(&2) == None);
    }

    #[test]
    fn eq_works() {
        let mut m1 = SplayMap::new();
        let mut m2 = SplayMap::new();
        let mut m3 = SplayMap::new();
        m1.insert(1, 1);
        m1.insert(2, 1);
        m2.insert(2, 1);
        m2.insert(1, 1);
        m3.insert(1, 1);
        m3.insert(2, 2);

        assert!(m1 == m2);
        assert!(m1 != m3);
        assert!(m2 != m3);
    }

    #[test]
    fn get_works() {
        let mut m = SplayMap::new();
        m.insert(1, 1);
        assert!(*m.get(&1) == 1);
    }

    #[test] #[should_fail]
    fn get_failing_works() {
        let mut m = SplayMap::new::<int, int>();
        m.insert(2, 2);
        m.get(&1);
    }

    #[test]
    fn large() {
        use std::rand::random;
        let mut m = SplaySet::new();
        let mut v = ~[];

        for 400.times {
            let i: int = random();
            m.insert(i);
            v.push(i);
        }

        for v.iter().advance |i| {
            assert!(m.contains(i));
        }
    }
}
