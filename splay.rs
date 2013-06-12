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

impl<K: TotalOrd, V> SplayMap<K, V> {
    pub fn new() -> SplayMap<K, V> { SplayMap{ root: None, size: 0 } }

    /// Performs a splay operation on the tree, moving a key to the root, or one
    /// of the closest values to the key to the root.
    pub fn splay(&mut self, key: &K) {
        let mut root = self.pop_root();
        let mut newleft = None;
        let mut newright = None;

        // Yes, these are backwards, that's intentional.
        root = root.splay(key, &mut newright, &mut newleft);

        root.left = newright;
        root.right = newleft;
        self.root = Some(root);
    }

    fn pop_root(&mut self) -> ~Node<K, V> {
        util::replace(&mut self.root, None).unwrap()
    }

    /// Similar to `find`, but fails if the key is not present in the map
    pub fn get<'a>(&'a self, k: &K) -> &'a V {
        self.find(k).expect("key not present in SplayMap")
    }

    /// Similar to `find_mut`, but fails if the key is not present in the map
    pub fn get_mut<'a>(&'a mut self, k: &K) -> &'a mut V {
        self.find_mut(k).expect("key not present in SplayMap")
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

    /// Visit all values in order
    #[inline(always)]
    fn each<'a>(&'a self, f: &fn(&K, &'a V) -> bool) -> bool {
        self.root.each(|n| n.each(f))
    }

    /// Iterate over the map and mutate the contained values
    #[inline(always)]
    fn mutate_values(&mut self, f: &fn(&K, &mut V) -> bool) -> bool {
        self.root.each_mut(|n| n.each_mut(f))
    }

    /// Visit all keys in order
    #[inline(always)]
    fn each_key(&self, f: &fn(&K) -> bool) -> bool { self.each(|k, _| f(k)) }

    /// Visit all values in order
    #[inline(always)]
    fn each_value<'a>(&'a self, f: &fn(&'a V) -> bool) -> bool {
        self.each(|_, v| f(v))
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
        if self.root.is_none() {
            self.root = Some(Node::new(key, value, None, None));
            self.size += 1;
            return None;
        }

        self.splay(&key);
        let mut root = self.pop_root();

        match key.cmp(&root.key) {
            Equal => {
                let ret = util::replace(&mut root.value, value);
                self.root = Some(root);
                return Some(ret);
            }
            Less => {
                let left = root.pop_left();
                self.root = Some(Node::new(key, value, left, Some(root)));
            }
            Greater => {
                let right = root.pop_right();
                self.root = Some(Node::new(key, value, Some(root), right));
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
        if self.root.is_none() {
            return None;
        }

        self.splay(key);
        let root = self.pop_root();
        if !key.equals(&root.key) {
            self.root = Some(root);
            return None;
        }

        let (value, left, right) = match root {
            ~Node {left, right, value, _} => (value, left, right)
        };

        if left.is_none() {
            self.root = right;
        } else {
            self.root = left;
            self.splay(key);
            self.root.get_mut_ref().right = right;
        }

        self.size -= 1;
        return Some(value);
    }

    /// Return a mutable reference to the value corresponding to the key
    fn find_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        if self.root.is_none() {
            return None;
        }
        self.splay(key);
        let root = self.root.get_mut_ref();
        if key.equals(&root.key) {
            return Some(&mut root.value);
        }
        return None;
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

impl<T: TotalOrd> SplaySet<T> {
    /// Creates a new empty set
    pub fn new() -> SplaySet<T> { SplaySet { map: SplayMap::new() } }

    /// Add a value to the set. Return true if the value was not already
    /// present in the set.
    #[inline(always)]
    pub fn insert(&mut self, t: T) -> bool { self.map.insert(t, ()) }

    /// Return true if the set contains a value
    #[inline(always)]
    pub fn contains(&self, t: &T) -> bool { self.map.contains_key(t) }

    /// Remove a value from the set. Return true if the value was
    /// present in the set.
    #[inline(always)]
    pub fn remove(&mut self, t: &T) -> bool { self.map.remove(t) }

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

    /// Performs the top-down splay operation at a current node. The key is the
    /// value which is being splayed. The `l` and `r` arguments are storage
    /// locations for the traversal down the tree. Once a node is recursed on,
    /// one of the children is placed in either 'l' or 'r'.
    fn splay(~self, key: &K,
             l: &mut Option<~Node<K, V>>,
             r: &mut Option<~Node<K, V>>) -> ~Node<K, V>
    {
        assert!(r.is_none());
        assert!(l.is_none());

        // When finishing the top-down splay operation, we need to ensure that
        // `self` doesn't have any children, so move its remaining children into
        // the `l` and `r` arguments.
        fn fixup<K: TotalOrd, V>(mut me: ~Node<K, V>,
                                 l: &mut Option<~Node<K, V>>,
                                 r: &mut Option<~Node<K, V>>) -> ~Node<K, V>
        {
            *l = me.pop_left();
            *r = me.pop_right();
            return me;
        }

        let mut this = self;
        match key.cmp(&this.key) {
            // Found it, yay!
            Equal => { return fixup(this, l, r); }

            Less => {
                match this.pop_left() {
                    None => { return fixup(this, l, r); }
                    Some(left) => {
                        let mut left = left;
                        // rotate this node right if necessary
                        if key.cmp(&left.key) == Less {
                            this.left = left.pop_right();
                            left.right = Some(this);
                            this = left;
                            match this.pop_left() {
                                Some(l) => { left = l; }
                                None => { return fixup(this, l, r); }
                            }
                        }

                        // Bit of an odd way to get some loans, but it works
                        *r = Some(this);
                        match *r {
                            None => fail!(),
                            Some(ref mut me) => {
                                return left.splay(key, l, &mut me.left);
                            }
                        }
                    }
                }
            }

            // If you look closely, you may have seen some similar code before
            Greater => {
                match this.pop_right() {
                    None => { return fixup(this, l, r); }
                    // rotate left if necessary
                    Some(right) => {
                        let mut right = right;
                        if key.cmp(&right.key) == Greater {
                            this.right = right.pop_left();
                            right.left = Some(this);
                            this = right;
                            match this.pop_right() {
                                Some(r) => { right = r; }
                                None => { return fixup(this, l, r); }
                            }
                        }

                        *l = Some(this);
                        match *l {
                            None => fail!(),
                            Some(ref mut me) => {
                                return right.splay(key, &mut me.right, r);
                            }
                        }
                    }
                }
            }
        }
    }

    fn each<'a>(&'a self, f: &fn(&K, &'a V) -> bool) -> bool {
        self.left.each(|l| l.each(f)) &&
            f(&self.key, &self.value) &&
            self.right.each(|r| r.each(f))
    }

    fn each_mut(&mut self, f: &fn(&K, &mut V) -> bool) -> bool {
        self.left.each_mut(|l| l.each_mut(f)) &&
            f(&self.key, &mut self.value) &&
            self.right.each_mut(|r| r.each_mut(f))
    }

    fn pop_left(&mut self) -> Option<~Node<K, V>> {
        util::replace(&mut self.left, None)
    }

    fn pop_right(&mut self) -> Option<~Node<K, V>> {
        util::replace(&mut self.right, None)
    }
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
}
