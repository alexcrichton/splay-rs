use std::default::Default;
use std::iter::{FromIterator, IntoIterator};

use map::{self, SplayMap};

#[derive(Clone)]
pub struct SplaySet<T: Ord> {
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
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self.map.into_iter() }
    }

    pub fn len(&self) -> usize { self.map.len() }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn clear(&mut self) { self.map.clear() }

    /// Return true if the set contains a value
    pub fn contains(&self, t: &T) -> bool { self.map.contains_key(t) }

    /// Add a value to the set. Return true if the value was not already
    /// present in the set.
    pub fn insert(&mut self, t: T) -> bool { self.map.insert(t, ()).is_none() }

    /// Remove a value from the set. Return true if the value was
    /// present in the set.
    pub fn remove(&mut self, t: &T) -> bool { self.map.remove(t).is_some() }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> { self.inner.next().map(|p| p.0) }
    fn size_hint(&self) -> (usize, Option<usize>) { self.inner.size_hint() }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<T: Ord> Default for SplaySet<T> {
    fn default() -> SplaySet<T> { SplaySet::new() }
}

impl<T: Ord> FromIterator<T> for SplaySet<T> {
    fn from_iter<I: IntoIterator<Item=T>>(iterator: I) -> SplaySet<T> {
        let mut set = SplaySet::new();
        set.extend(iterator);
        set
    }
}

impl<T: Ord> Extend<T> for SplaySet<T> {
    fn extend<I: IntoIterator<Item=T>>(&mut self, i: I) {
        for t in i { self.insert(t); }
    }
}
