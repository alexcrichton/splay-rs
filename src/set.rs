use map::{mod, SplayMap};

#[deriving(Clone)]
pub struct SplaySet<T> {
    map: SplayMap<T, ()>
}

pub struct IntoIter<T> {
    inner: map::IntoIter<T, ()>,
}

impl<T: Ord> SplaySet<T> {
    /// Creates a new empty set
    pub fn new() -> SplaySet<T> { SplaySet { map: SplayMap::new() } }

    /// Moves all values out of this set, transferring ownership to the given
    /// iterator.
    pub fn into_iter(&mut self) -> IntoIter<T> {
        IntoIter { inner: self.map.into_iter() }
    }

    pub fn len(&self) -> uint { self.map.len() }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn clear(&mut self) { self.map.clear() }

    /// Return true if the set contains a value
    pub fn contains(&self, t: &T) -> bool { self.map.contains_key(t) }

    /// Add a value to the set. Return true if the value was not already
    /// present in the set.
    pub fn insert(&mut self, t: T) -> bool { self.map.insert(t, ()) }

    /// Remove a value from the set. Return true if the value was
    /// present in the set.
    pub fn remove(&mut self, t: &T) -> bool { self.map.remove(t) }
}

impl<T> Iterator<T> for IntoIter<T> {
    fn next(&mut self) -> Option<T> { self.inner.next().map(|p| p.val0()) }
    fn size_hint(&self) -> (uint, Option<uint>) { self.inner.size_hint() }
}

impl<T> DoubleEndedIterator<T> for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}
