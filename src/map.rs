use std::default::Default;
use std::kinds::marker;
use std::mem;

use node::Node;

/// The implementation of this splay tree is largely based on the c code at:
///     ftp://ftp.cs.cmu.edu/usr/ftp/usr/sleator/splaying/top-down-splay.c
/// This version of splaying is a top-down splay operation.
#[deriving(Clone)]
pub struct SplayMap<K, V> {
    root: Option<Box<Node<K, V>>>,
    size: uint,
    marker: marker::NoSync, // lookups mutate the tree
}

pub struct IntoIter<K, V> {
    cur: Option<Box<Node<K, V>>>,
    remaining: uint,
}

/// Performs a top-down splay operation on a tree rooted at `node`. This will
/// modify the pointer to contain the new root of the tree once the splay
/// operation is done. When finished, if `key` is in the tree, it will be at the
/// root. Otherwise the closest key to the specified key will be at the root.
fn splay<K: Ord, V>(key: &K, node: &mut Box<Node<K, V>>) {
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
                    let mut left = match node.pop_left() {
                        Some(left) => left, None => break
                    };
                    // rotate this node right if necessary
                    if key.cmp(&left.key) == Less {
                        // A bit odd, but avoids drop glue
                        mem::swap(&mut node.left, &mut left.right);
                        mem::swap(&mut left, node);
                        let none = mem::replace(&mut node.right, Some(left));
                        match mem::replace(&mut node.left, none) {
                            Some(l) => { left = l; }
                            None    => { break }
                        }
                    }

                    *r = Some(mem::replace(node, left));
                    let tmp = r;
                    r = &mut tmp.as_mut().unwrap().left;
                }

                // If you look closely, you may have seen some similar code
                // before
                Greater => {
                    match node.pop_right() {
                        None => { break }
                        // rotate left if necessary
                        Some(mut right) => {
                            if key.cmp(&right.key) == Greater {
                                mem::swap(&mut node.right, &mut right.left);
                                mem::swap(&mut right, node);
                                let none = mem::replace(&mut node.left,
                                                         Some(right));
                                match mem::replace(&mut node.right, none) {
                                    Some(r) => { right = r; }
                                    None    => { break }
                                }
                            }
                            *l = Some(mem::replace(node, right));
                            let tmp = l;
                            l = &mut tmp.as_mut().unwrap().right;
                        }
                    }
                }
            }
        }

        mem::swap(l, &mut node.left);
        mem::swap(r, &mut node.right);
    }

    node.left = newright;
    node.right = newleft;
}

impl<K: Ord, V> SplayMap<K, V> {
    pub fn new() -> SplayMap<K, V> {
        SplayMap{ root: None, size: 0, marker: marker::NoSync }
    }

    /// Moves all values out of this map, transferring ownership to the given
    /// iterator.
    pub fn into_iter(&mut self) -> IntoIter<K, V> {
        IntoIter { cur: self.root.take(), remaining: self.size }
    }

    pub fn len(&self) -> uint { self.size }
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Clears the tree in O(1) extra space (including the stack). This is
    /// necessary to prevent stack exhaustion with extremely large trees.
    pub fn clear(&mut self) {
        let mut iter = IntoIter {
            cur: self.root.take(),
            remaining: self.size,
        };
        for _ in iter {
            // ignore, drop the values (and the node)
        }
        self.size = 0;
    }

    /// Return true if the map contains a value for the specified key
    pub fn contains_key(&self, key: &K) -> bool {
        self.find(key).is_some()
    }

    /// Return a reference to the value corresponding to the key
    pub fn find(&self, key: &K) -> Option<&V> {
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
        //
        // However I'm not entirely sure whether this works with iteration or
        // not. Arbitrary lookups can occur during iteration, and during
        // iteration there's some form of "stack" remembering the nodes that
        // need to get visited. I don't believe that it's safe to allow lookups
        // while the tree is being iterated. Right now there are no iterators
        // exposed on this splay tree implementation, and more thought would be
        // required if there were.
        unsafe {
            let this = mem::transmute::<&_, &mut SplayMap<K, V>>(self);
            this.find_mut(key).map(|x| &*x)
        }
    }

    /// Return a mutable reference to the value corresponding to the key
    pub fn find_mut(&mut self, key: &K) -> Option<&mut V> {
        match self.root {
            None => { return None; }
            Some(ref mut root) => {
                splay(key, root);
                if *key == root.key {
                    return Some(&mut root.value);
                }
                return None;
            }
        }
    }

    /// Insert a key-value pair into the map. An existing value for a
    /// key is replaced by the new value. Return true if the key did
    /// not already exist in the map.
    pub fn insert(&mut self, key: K, value: V) -> bool {
        self.swap(key, value).is_none()
    }

    /// Insert a key-value pair from the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise None is returned.
    pub fn swap(&mut self, key: K, value: V) -> Option<V> {
        match self.root {
            None => self.root = Some(Node::new(key, value, None, None)),
            Some(ref mut root) => {
                splay(&key, root);

                match key.cmp(&root.key) {
                    Equal => {
                        let old = mem::replace(&mut root.value, value);
                        return Some(old);
                    }
                    /* TODO: would unsafety help perf here? */
                    Less => {
                        let left = root.pop_left();
                        let new = Node::new(key, value, left, None);
                        let prev = mem::replace(root, new);
                        root.right = Some(prev);
                    }
                    Greater => {
                        let right = root.pop_right();
                        let new = Node::new(key, value, None, right);
                        let prev = mem::replace(root, new);
                        root.left = Some(prev);
                    }
                }
            }
        }
        self.size += 1;
        return None;
    }

    /// Remove a key-value pair from the map. Return true if the key
    /// was present in the map, otherwise false.
    pub fn remove(&mut self, key: &K) -> bool {
        self.pop(key).is_some()
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    pub fn pop(&mut self, key: &K) -> Option<V> {
        match self.root {
            None => { return None; }
            Some(ref mut root) => {
                splay(key, root);
                if *key != root.key { return None }
            }
        }

        // TODO: Extra storage of None isn't necessary
        let (value, left, right) = match self.root.take().unwrap() {
            box Node {left, right, value, ..} => (value, left, right)
        };

        match left {
            None => self.root = right,
            Some(node) => {
                let mut node = node;
                splay(key, &mut node);
                node.right = right;
                self.root = Some(node);
            }
        }

        self.size -= 1;
        return Some(value);
    }
}

impl<K: Ord, V> Index<K, V> for SplayMap<K, V> {
    fn index(&self, k: &K) -> &V {
        match self.find(k) {
            Some(v) => v,
            None => panic!("key not present in SplayMap"),
        }
    }
}

impl<K: Ord, V> IndexMut<K, V> for SplayMap<K, V> {
    fn index_mut(&mut self, k: &K) -> &mut V {
        match self.find_mut(k) {
            Some(v) => v,
            None => panic!("key not present in SplayMap"),
        }
    }
}

impl<K: Ord, V> Default for SplayMap<K, V> {
    fn default() -> SplayMap<K, V> { SplayMap::new() }
}

impl<K: Ord, V> FromIterator<(K, V)> for SplayMap<K, V> {
    fn from_iter<I: Iterator<(K, V)>>(iterator: I) -> SplayMap<K, V> {
        let mut map = SplayMap::new();
        map.extend(iterator);
        map
    }
}

impl<K: Ord, V> Extendable<(K, V)> for SplayMap<K, V> {
    fn extend<I: Iterator<(K, V)>>(&mut self, mut i: I) {
        for (k, v) in i {
            self.insert(k, v);
        }
    }
}

impl<K, V> Iterator<(K, V)> for IntoIter<K, V> {
    fn next(&mut self) -> Option<(K, V)> {
        let mut cur = match self.cur.take() {
            Some(cur) => cur,
            None => return None,
        };
        loop {
            match cur.pop_left() {
                Some(node) => {
                    let mut node = node;
                    cur.left = node.pop_right();
                    node.right = Some(cur);
                    cur = node;
                }

                None => {
                    self.cur = cur.pop_right();
                    // left and right fields are both None
                    let node = *cur;
                    let Node { key, value, .. } = node;
                    self.remaining -= 1;
                    return Some((key, value));
                }
            }
        }
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<K, V> DoubleEndedIterator<(K, V)> for IntoIter<K, V> {
    // Pretty much the same as the above code, but with left replaced with right
    // and vice-versa.
    fn next_back(&mut self) -> Option<(K, V)> {
        let mut cur = match self.cur.take() {
            Some(cur) => cur,
            None => return None,
        };
        loop {
            match cur.pop_right() {
                Some(node) => {
                    let mut node = node;
                    cur.right = node.pop_left();
                    node.left = Some(cur);
                    cur = node;
                }

                None => {
                    self.cur = cur.pop_left();
                    // left and right fields are both None
                    let node = *cur;
                    let Node { key, value, .. } = node;
                    self.remaining -= 1;
                    return Some((key, value));
                }
            }
        }
    }
}

#[unsafe_destructor]
impl<K: Ord, V> Drop for SplayMap<K, V> {
    fn drop(&mut self) {
        // Be sure to not recurse too deep on destruction
        self.clear();
    }
}
