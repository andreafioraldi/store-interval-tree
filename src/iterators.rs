use alloc::vec::Vec;
use core::{cmp::Ord, fmt::Debug};

use crate::{interval::Interval, node::Node};

/// A `find` query on the interval tree does not directly return references to the nodes in the tree, but
/// wraps the fields `interval` and `data` in an `Entry`.
#[derive(PartialEq, Eq, Debug)]
pub struct Entry<'a, T: Ord, V> {
    value: &'a V,
    interval: &'a Interval<T>,
}

impl<'a, T: Ord + 'a, V: 'a> Entry<'a, T, V> {
    /// Get a reference to the data for this entry
    pub fn value(&self) -> &'a V {
        self.value
    }

    /// Get a reference to the interval for this entry
    pub fn interval(&self) -> &'a Interval<T> {
        self.interval
    }
}

/// An `IntervalTreeIterator` is returned by `Intervaltree::find` and iterates over the entries
/// overlapping the query
pub struct IntervalTreeIterator<'a, T: Ord, V> {
    pub(crate) nodes: Vec<&'a Node<T, V>>,
    pub(crate) interval: &'a Interval<T>,
}

impl<'a, T: Ord + 'a, V: 'a> Iterator for IntervalTreeIterator<'a, T, V> {
    type Item = Entry<'a, T, V>;

    fn next(&mut self) -> Option<Entry<'a, T, V>> {
        loop {
            let node_ref = match self.nodes.pop() {
                None => return None,
                Some(node) => node,
            };

            if node_ref.right_child.is_some() {
                self.nodes.push(node_ref.right_child.as_ref().unwrap());
            }
            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    node_ref.left_child.as_ref().unwrap().get_max(),
                    self.interval.get_low(),
                )
            {
                self.nodes.push(node_ref.left_child.as_ref().unwrap());
            }

            if Interval::overlaps(node_ref.interval(), &self.interval) {
                return Some(Entry {
                    value: node_ref.value(),
                    interval: &node_ref.interval(),
                });
            }
        }
    }
}

/// A `find_mut` query on the interval tree does not directly return references to the nodes in the tree, but
/// wraps the fields `interval` and `data` in an `EntryMut`. Only the data part can be mutably accessed
/// using the `data` method
#[derive(PartialEq, Eq, Debug)]
pub struct EntryMut<'a, T: Ord, V> {
    value: &'a mut V,
    interval: &'a Interval<T>,
}

impl<'a, T: Ord + 'a, V: 'a> EntryMut<'a, T, V> {
    /// Get a mutable reference to the data for this entry
    pub fn value(&'a mut self) -> &'a mut V {
        &mut self.value
    }

    /// Get a reference to the interval for this entry
    pub fn interval(&self) -> &'a Interval<T> {
        self.interval
    }
}

/// An `IntervalTreeIteratorMut` is returned by `Intervaltree::find_mut` and iterates over the entries
/// overlapping the query allowing mutable access to the data `D`, not the `Interval`.
pub struct IntervalTreeIteratorMut<'a, T: Ord, V> {
    pub(crate) nodes: Vec<&'a mut Node<T, V>>,
    pub(crate) interval: &'a Interval<T>,
}

impl<'a, T: Ord + 'a, V: 'a> Iterator for IntervalTreeIteratorMut<'a, T, V> {
    type Item = EntryMut<'a, T, V>;

    fn next(&mut self) -> Option<EntryMut<'a, T, V>> {
        loop {
            let node_ref = match self.nodes.pop() {
                None => return None,
                Some(node) => node,
            };

            let overlaps = Interval::overlaps(node_ref.interval(), &self.interval);

            if node_ref.right_child.is_some() {
                self.nodes.push(node_ref.right_child.as_mut().unwrap());
            }
            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    node_ref.left_child.as_ref().unwrap().get_max(),
                    self.interval.get_low(),
                )
            {
                self.nodes.push(node_ref.left_child.as_mut().unwrap());
            }

            if overlaps {
                return Some(EntryMut {
                    value: node_ref.value.as_mut().unwrap(),
                    interval: node_ref.interval.as_ref().unwrap(),
                });
            }
        }
    }
}
