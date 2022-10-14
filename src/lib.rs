#![no_std]
#![warn(clippy::cargo)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(clippy::all)]
#![warn(
    missing_debug_implementations,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications,
    unused_must_use
)]
#![warn(clippy::pedantic)]
#![allow(clippy::comparison_chain)]
// TODO: check https://rust-lang.github.io/rust-clippy/master/index.html#derive_hash_xor_eq
#![allow(clippy::derive_hash_xor_eq)]
#![allow(clippy::missing_panics_doc)]

#[macro_use]
pub extern crate alloc;

use alloc::{boxed::Box, rc::Rc, vec::Vec};
use core::cmp::Ord;
use core::fmt::Debug;
use core::ops::Bound;

mod interval;
pub use interval::Interval;

mod node;
use node::Node;

mod iterators;
pub use iterators::{Entry, EntryMut, IntervalTreeIterator, IntervalTreeIteratorMut};

/// An interval tree is a tree data structure to hold intervals.
/// Specifically, it allows one to efficiently find all intervals that overlap with any given interval or point.
///
/// This data structure is backed by a `store_interval_tree:IntervalTree`
///
/// # Examples
/// ```
/// use store_interval_tree::IntervalTree;
/// use store_interval_tree::Interval;
/// use std::ops::Bound::*;
///
/// // initialize an interval tree with end points of type usize
/// let mut interval_tree = IntervalTree::<usize, ()>::new();
///
/// // insert interval into the tree
/// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
/// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
/// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
/// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
/// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
/// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
/// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
/// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
/// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
///
/// let interval1 = Interval::new(Excluded(23), Included(26));
///
/// // interval (25, 30] is overlapped with interval (23,26]
/// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
///
/// // there is no interval in the tree that has interval with (10,15)
/// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
///
/// // find all overlaps with an interval
/// let interval = Interval::new(Included(8), Included(26));
/// // intervals are: (8,9], [6,10],(19,20], [16,21), (15,23), [17,19), (25,30], [26,26]
/// let intervals = interval_tree.find_overlaps(&interval);
///
/// // delete interval
/// let interval = Interval::new(Included(15), Included(18));
/// let overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
/// interval_tree.delete(&overlapped_interval);
///
/// // find all intervals between two intervals/points
/// let low = Interval::point(14);
/// let high = Interval::point(24);
/// // intervals are: (15,23), [16,21), [17,19), (19,20]
/// let intervals = interval_tree.intervals_between(&low, &high);
/// ```
#[derive(Clone, Default, Hash)]
pub struct IntervalTree<T: Ord, V> {
    root: Option<Box<Node<T, V>>>,
}

impl<T: Ord, V> IntervalTree<T, V> {
    /// Initialize an interval tree with end points of type usize
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    /// ```
    #[must_use]
    pub fn new() -> IntervalTree<T, V> {
        IntervalTree { root: None }
    }

    /// Returns true if there are no intervals in the tree, false otherwise
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Returns total number of intervals in the tree
    #[must_use]
    pub fn size(&self) -> usize {
        Node::size(&self.root)
    }

    /// Returns height of the tree
    #[must_use]
    pub fn height(&self) -> i64 {
        Node::height(&self.root)
    }

    /// Find overlapping intervals in the tree and returns an
    /// `IntervalTreeIterator` that allows access to the stored value
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let interval1 = Interval::new(Excluded(23), Included(26));
    ///
    /// // interval (25, 30] is overlapped with interval (23,26]
    /// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
    ///
    /// // there is no interval in the tree that has interval with (10,15)
    /// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
    /// ```
    #[must_use]
    pub fn query<'a, 'b>(&'a self, interval: &'b Interval<T>) -> IntervalTreeIterator<'b, T, V>
    where
        'a: 'b,
    {
        if let Some(ref n) = self.root {
            IntervalTreeIterator {
                nodes: vec![n],
                interval,
            }
        } else {
            let nodes = vec![];
            IntervalTreeIterator { nodes, interval }
        }
    }

    /// Find overlapping intervals in the tree and returns an
    /// `IntervalTreeIteratorMut` that allows mutable access to the stored value
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let interval1 = Interval::new(Excluded(23), Included(26));
    ///
    /// // interval (25, 30] is overlapped with interval (23,26]
    /// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
    ///
    /// // there is no interval in the tree that has interval with (10,15)
    /// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
    /// ```
    pub fn query_mut<'a, 'b>(
        &'a mut self,
        interval: &'b Interval<T>,
    ) -> IntervalTreeIteratorMut<'b, T, V>
    where
        'a: 'b,
    {
        if let Some(ref mut n) = self.root {
            IntervalTreeIteratorMut {
                nodes: vec![n],
                interval,
            }
        } else {
            let nodes = vec![];
            IntervalTreeIteratorMut { nodes, interval }
        }
    }

    /// Returns true if there exists an interval in the tree that overlaps with specified `interval`
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    ///
    /// assert!(!interval_tree.overlaps(&Interval::new(Included(4), Excluded(6))));
    /// assert!(interval_tree.overlaps(&Interval::new(Included(4), Included(6))));
    /// ```
    #[must_use]
    pub fn overlaps(&self, interval: &Interval<T>) -> bool {
        self.find_overlap(interval).is_some()
    }

    /// Returns first interval that overlaps with specified `interval`
    ///
    /// # Arguments:
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let interval1 = Interval::new(Excluded(23), Included(26));
    ///
    /// // interval (25, 30] is overlapped with interval (23,26]
    /// assert!(interval_tree.find_overlap(&interval1).unwrap() == Interval::new(Excluded(25), Included(30)));
    ///
    /// // there is no interval in the tree that has interval with (10,15)
    /// assert!(interval_tree.find_overlap(&Interval::new(Excluded(10), Excluded(15))).is_none());
    /// ```
    #[must_use]
    pub fn find_overlap(&self, interval: &Interval<T>) -> Option<Interval<T>> {
        IntervalTree::_find_overlap(&self.root, interval)
    }

    fn _find_overlap(
        node: &Option<Box<Node<T, V>>>,
        interval: &Interval<T>,
    ) -> Option<Interval<T>> {
        if node.is_none() {
            return None;
        }
        let mut current = node;
        while current.is_some() {
            let node_ref = current.as_ref().unwrap();
            if Interval::overlaps(node_ref.interval(), interval) {
                break;
            }

            if node_ref.left_child.is_some()
                && Node::<T, V>::is_ge(
                    &node_ref.left_child.as_ref().unwrap().get_max(),
                    &interval.get_low(),
                )
            {
                current = &node_ref.left_child;
            } else {
                current = &node_ref.right_child;
            }
        }

        if current.is_none() {
            None
        } else {
            Some(current.as_ref().unwrap().interval().duplicate())
        }
    }

    /// Returns all intervals that overlap with the specified `interval`
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for any overlaps
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// // find all overlaps with an interval
    /// let interval = Interval::new(Included(8), Included(26));
    /// // intervals are: (8,9], [6,10],(19,20], [16,21), (15,23), [17,19), (25,30], [26,26]
    /// let intervals = interval_tree.find_overlaps(&interval);
    /// ```
    #[must_use]
    pub fn find_overlaps(&self, interval: &Interval<T>) -> Vec<Interval<T>> {
        let mut overlaps = Vec::<Interval<T>>::new();

        IntervalTree::_find_overlaps(&self.root, interval, &mut overlaps);

        overlaps
    }

    fn _find_overlaps(
        node: &Option<Box<Node<T, V>>>,
        interval: &Interval<T>,
        overlaps: &mut Vec<Interval<T>>,
    ) {
        if node.is_none() {
            return;
        }
        let node_ref = node.as_ref().unwrap();
        if Interval::overlaps(node_ref.interval(), interval) {
            overlaps.push(node_ref.interval().duplicate());
        }

        if node_ref.left_child.is_some()
            && Node::<T, V>::is_ge(
                &node_ref.left_child.as_ref().unwrap().get_max(),
                &interval.get_low(),
            )
        {
            IntervalTree::_find_overlaps(&node_ref.left_child, interval, overlaps);
        }
        IntervalTree::_find_overlaps(&node_ref.right_child, interval, overlaps);
    }

    /// Inserts an interval in the tree. if interval already exists, `interval` will be ignored
    ///
    /// # Arguments
    /// * `interval`: interval to be inserted in the tree
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    /// ```
    pub fn insert(&mut self, interval: Interval<T>, value: V) {
        let max = interval.get_high();

        self.root = Some(IntervalTree::_insert(
            self.root.take(),
            interval,
            value,
            max,
        ));
    }

    fn _insert(
        node: Option<Box<Node<T, V>>>,
        interval: Interval<T>,
        value: V,
        max: Rc<Bound<T>>,
    ) -> Box<Node<T, V>> {
        if node.is_none() {
            return Box::new(Node::init(interval, value, max, 0, 1));
        }

        let mut node_ref = node.unwrap();

        if interval < *node_ref.interval() {
            node_ref.left_child = Some(IntervalTree::_insert(
                node_ref.left_child,
                interval,
                value,
                max,
            ));
        } else if interval > *node_ref.interval() {
            node_ref.right_child = Some(IntervalTree::_insert(
                node_ref.right_child,
                interval,
                value,
                max,
            ));
        } else {
            return node_ref;
        }

        node_ref.update_height();
        node_ref.update_size();
        node_ref.update_max();

        IntervalTree::balance(node_ref)
    }

    fn balance(mut node: Box<Node<T, V>>) -> Box<Node<T, V>> {
        if Node::balance_factor(&node) < -1 {
            if Node::balance_factor(node.right_child.as_ref().unwrap()) > 0 {
                node.right_child = Some(IntervalTree::rotate_right(node.right_child.unwrap()));
            }
            node = IntervalTree::rotate_left(node);
        } else if Node::balance_factor(&node) > 1 {
            if Node::balance_factor(node.left_child.as_ref().unwrap()) < 0 {
                node.left_child = Some(IntervalTree::rotate_left(node.left_child.unwrap()));
            }
            node = IntervalTree::rotate_right(node);
        }
        node
    }

    fn rotate_right(mut node: Box<Node<T, V>>) -> Box<Node<T, V>> {
        let mut y = node.left_child.unwrap();
        node.left_child = y.right_child;
        y.size = node.size;
        node.update_height();
        node.update_size();
        node.update_max();

        y.right_child = Some(node);
        y.update_height();
        y.update_max();

        y
    }

    fn rotate_left(mut node: Box<Node<T, V>>) -> Box<Node<T, V>> {
        let mut y = node.right_child.unwrap();
        node.right_child = y.left_child;
        y.size = node.size;

        node.update_height();
        node.update_size();
        node.update_max();

        y.left_child = Some(node);
        y.update_height();
        y.update_max();

        y
    }

    /// Delete the specified `interval` if found
    ///
    /// # Arguments
    /// * `interval`: interval to be deleted
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// // initialize an interval tree with end points of type usize
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// // insert interval into the tree
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// // delete interval
    /// let interval = Interval::new(Included(15), Included(18));
    /// let overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
    /// interval_tree.delete(&overlapped_interval);
    /// ```
    pub fn delete(&mut self, interval: &Interval<T>) {
        if !self.is_empty() {
            self.root = IntervalTree::_delete(self.root.take(), interval);
        }
    }

    fn _delete(node: Option<Box<Node<T, V>>>, interval: &Interval<T>) -> Option<Box<Node<T, V>>> {
        match node {
            None => None,
            Some(mut node) => {
                if *interval < *node.interval() {
                    node.left_child = IntervalTree::_delete(node.left_child.take(), interval);
                } else if *interval > *node.interval() {
                    node.right_child = IntervalTree::_delete(node.right_child.take(), interval);
                } else if node.left_child.is_none() {
                    return node.right_child;
                } else if node.right_child.is_none() {
                    return node.left_child;
                } else {
                    let mut y = node;
                    node = IntervalTree::_min(&mut y.right_child);
                    node.right_child = IntervalTree::_delete_min(y.right_child.unwrap());
                    node.left_child = y.left_child;
                }

                node.update_height();
                node.update_size();
                node.update_max();
                Some(IntervalTree::balance(node))
            }
        }
    }
    fn _min(node: &mut Option<Box<Node<T, V>>>) -> Box<Node<T, V>> {
        match node {
            Some(node) => {
                if node.left_child.is_none() {
                    Box::new(Node::init(
                        node.get_interval(),
                        node.get_value(),
                        node.get_max(),
                        0,
                        1,
                    ))
                } else {
                    IntervalTree::_min(&mut node.left_child)
                }
            }
            None => panic!("Called min on None node"),
        }
    }

    /// Deletes minimum interval in the tree
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// interval_tree.delete_min();
    /// interval_tree.delete_min();
    ///
    /// assert!(interval_tree.find_overlap(&Interval::new(Included(1), Excluded(6))).is_none());
    /// ```
    pub fn delete_min(&mut self) {
        if !self.is_empty() {
            self.root = IntervalTree::_delete_min(self.root.take().unwrap());
        }
    }

    fn _delete_min(mut node: Box<Node<T, V>>) -> Option<Box<Node<T, V>>> {
        if node.left_child.is_none() {
            return node.right_child.take();
        }

        node.left_child = IntervalTree::_delete_min(node.left_child.unwrap());

        node.update_height();
        node.update_size();
        node.update_size();

        Some(IntervalTree::balance(node))
    }

    /// Deletes maximum interval in the tree
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// interval_tree.delete_max();
    /// interval_tree.delete_max();
    ///
    /// assert!(interval_tree.find_overlap(&Interval::new(Included(25), Excluded(30))).is_none());
    pub fn delete_max(&mut self) {
        if !self.is_empty() {
            self.root = IntervalTree::_delete_max(self.root.take().unwrap());
        }
    }

    fn _delete_max(mut node: Box<Node<T, V>>) -> Option<Box<Node<T, V>>> {
        if node.right_child.is_none() {
            return node.left_child.take();
        }

        node.right_child = IntervalTree::_delete_max(node.right_child.unwrap());

        node.update_height();
        node.update_size();
        node.update_max();

        Some(IntervalTree::balance(node))
    }

    /// Returns the kth smallest interval
    ///
    /// # Arguments
    /// * `k`: the order statistic
    ///
    /// # Panics
    /// * panics if k is not in range: 0 <= k <= size - 1
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// assert!(format!("{}", interval_tree.select(0).unwrap()) == String::from("[0,3)"));
    /// assert!(format!("{}", interval_tree.select(1).unwrap()) == String::from("(0,1]"));
    /// assert!(format!("{}", interval_tree.select(2).unwrap()) == String::from("[6,10]"));
    /// assert!(format!("{}", interval_tree.select(3).unwrap()) == String::from("(8,9]"));
    /// ```
    #[must_use]
    pub fn select(&self, k: usize) -> Option<Interval<T>> {
        assert!(k <= self.size(), "K must be in range 0 <= k <= size - 1");
        IntervalTree::_select(&self.root, k)
    }

    fn _select(node: &Option<Box<Node<T, V>>>, k: usize) -> Option<Interval<T>> {
        if node.is_none() {
            return None;
        }
        let node_ref = node.as_ref().unwrap();

        let t = Node::size(&node_ref.left_child);
        if t > k {
            IntervalTree::_select(&node_ref.left_child, k)
        } else if t < k {
            IntervalTree::_select(&node_ref.right_child, k - t - 1)
        } else {
            return Some(node_ref.interval().duplicate());
        }
    }

    /// Returns minimum interval in the tree
    #[must_use]
    pub fn min(&self) -> Option<Interval<T>> {
        self.select(0)
    }

    /// Returns maximum interval in the tree
    #[must_use]
    pub fn max(&self) -> Option<Interval<T>> {
        self.select(self.size() - 1)
    }

    /// Returns all intervals between two intervals/points
    ///
    /// # Arguments
    /// * `low_bound`: lowest interval of the range
    /// * `high_bound`: highest interval of the range
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let low = Interval::new(Included(14), Included(14));
    /// let high = Interval::new(Included(24), Included(24));
    /// let intervals = interval_tree.intervals_between(&low, &high);
    ///
    /// let accept = String::from("(15,23)[16,21)[17,19)(19,20]");
    ///
    /// let mut result = String::from("");
    /// for interval in intervals {
    ///     result.push_str(&format!("{}", interval))
    /// }
    ///
    /// assert_eq!(result, accept);
    /// ```
    #[must_use]
    pub fn intervals_between(
        &self,
        low_bound: &Interval<T>,
        high_bound: &Interval<T>,
    ) -> Vec<&Interval<T>> {
        let mut intervals: Vec<&Interval<T>> = Vec::new();

        IntervalTree::_intervals_between(&self.root, low_bound, high_bound, &mut intervals);

        intervals
    }

    fn _intervals_between<'a>(
        node: &'a Option<Box<Node<T, V>>>,
        low_bound: &Interval<T>,
        high_bound: &Interval<T>,
        intervals: &mut Vec<&'a Interval<T>>,
    ) {
        if node.is_none() {
            return;
        }

        let node_ref = node.as_ref().unwrap();
        if *low_bound < *node_ref.interval() {
            IntervalTree::_intervals_between(
                &node_ref.left_child,
                low_bound,
                high_bound,
                intervals,
            );
        }
        if *low_bound <= *node_ref.interval() && *node_ref.interval() <= *high_bound {
            intervals.push(node_ref.interval());
        }
        if *high_bound > *node_ref.interval() {
            IntervalTree::_intervals_between(
                &node_ref.right_child,
                low_bound,
                high_bound,
                intervals,
            );
        }
    }

    /// Returns all intervals in the tree following an in-order traversal.
    /// Therefore intervals are sorted from smallest to largest
    #[must_use]
    pub fn intervals(&self) -> Vec<Interval<T>> {
        let mut intervals: Vec<Interval<T>> = Vec::new();

        IntervalTree::_intervals_in_order(&self.root, &mut intervals);

        intervals
    }

    fn _intervals_in_order(node: &Option<Box<Node<T, V>>>, intervals: &mut Vec<Interval<T>>) {
        if node.is_none() {
            return;
        }

        let node_ref = node.as_ref().unwrap();
        IntervalTree::_intervals_in_order(&node_ref.left_child, intervals);
        intervals.push(node_ref.interval().duplicate());
        IntervalTree::_intervals_in_order(&node_ref.right_child, intervals);
    }

    /// Returns the number of intervals in the tree less than `interval`
    ///
    /// # Arguments
    /// * `interval`: interval to be searched for
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// assert_eq!(interval_tree.rank(&Interval::point(5)), 1);
    /// ```
    #[must_use]
    pub fn rank(&self, interval: &Interval<T>) -> usize {
        IntervalTree::_rank(&self.root, interval)
    }
    fn _rank(node: &Option<Box<Node<T, V>>>, interval: &Interval<T>) -> usize {
        if node.is_none() {
            return 0;
        }
        let node_ref = node.as_ref().unwrap();
        if *interval < *node_ref.interval() {
            IntervalTree::_rank(&node_ref.left_child, interval)
        } else if *interval >= *node_ref.interval() {
            1 + Node::size(&node_ref.left_child)
                + IntervalTree::_rank(&node_ref.right_child, interval)
        } else {
            Node::size(&node_ref.left_child)
        }
    }

    /// Returns the number of intervals in the tree between `low_bound` and `high_bound`
    ///
    /// # Arguments
    /// * `low_bound`: lowest interval of the range
    /// * `high_bound`: highest interval of the range
    ///
    /// # Examples
    /// ```
    /// use store_interval_tree::IntervalTree;
    /// use store_interval_tree::Interval;
    /// use std::ops::Bound::*;
    ///
    /// let mut interval_tree = IntervalTree::<usize, ()>::new();
    ///
    /// interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
    /// interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
    /// interval_tree.insert(Interval::new(Included(6), Included(10)), ());
    /// interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
    /// interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
    /// interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
    /// interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
    /// interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
    /// interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
    /// interval_tree.insert(Interval::new(Included(26), Included(26)), ());
    ///
    /// let low = Interval::point(10);
    /// let high = Interval::point(25);
    /// assert_eq!(interval_tree.size_between(&low, &high), 5);
    /// ```
    #[must_use]
    pub fn size_between(&self, low_bound: &Interval<T>, high_bound: &Interval<T>) -> usize {
        if self.is_empty() {
            return 0;
        }
        if *low_bound > *high_bound {
            return 0;
        }

        self.rank(high_bound) - self.rank(low_bound) + 1
    }
}

impl<T: Debug + Ord, V: Debug> Debug for IntervalTree<T, V> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
        fmt.write_str("IntervalTree ")?;
        fmt.debug_set().entries(self.intervals().iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::String;

    use super::*;
    use core::ops::Bound::{Excluded, Included, Unbounded};

    #[test]
    fn tree_interval_init() {
        let interval_tree = IntervalTree::<usize, ()>::new();

        assert!(interval_tree.is_empty());
        assert_eq!(interval_tree.size(), 0);
    }

    #[test]
    fn tree_interval_insert() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Included(0), Included(3)), ());
        interval_tree.insert(Interval::new(Included(5), Included(8)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Included(8), Included(9)), ());
        interval_tree.insert(Interval::new(Included(15), Included(23)), ());
        interval_tree.insert(Interval::new(Included(16), Included(21)), ());
        interval_tree.insert(Interval::new(Included(17), Included(19)), ());
        interval_tree.insert(Interval::new(Included(19), Included(20)), ());
        interval_tree.insert(Interval::new(Included(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());

        assert_eq!(interval_tree.size(), 10);
    }

    #[test]
    fn tree_interval_find_overlap_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Included(0), Included(3)), ());
        interval_tree.insert(Interval::new(Included(5), Included(8)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Included(8), Included(9)), ());
        interval_tree.insert(Interval::new(Included(15), Included(23)), ());
        interval_tree.insert(Interval::new(Included(16), Included(21)), ());
        interval_tree.insert(Interval::new(Included(17), Included(19)), ());
        interval_tree.insert(Interval::new(Included(19), Included(20)), ());
        interval_tree.insert(Interval::new(Included(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(1), Included(2)))
                    .unwrap()
            ) == *"[0,3]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(4), Included(5)))
                    .unwrap()
            ) == *"[5,8]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(10), Included(14)))
                    .unwrap()
            ) == *"[6,10]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(14), Included(15)))
                    .unwrap()
            ) == *"[15,23]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(15), Included(18)))
                    .unwrap()
            ) == *"[16,21]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(19), Included(19)))
                    .unwrap()
            ) == *"[19,20]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(23), Included(23)))
                    .unwrap()
            ) == *"[15,23]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(24), Included(26)))
                    .unwrap()
            ) == *"[25,30]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(26), Included(36)))
                    .unwrap()
            ) == *"[25,30]"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(31), Included(36)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(12)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(13), Included(13)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(14)))
            .is_none());
    }

    #[test]
    fn tree_interval_find_overlap_2() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
        interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(1), Included(2)))
                    .unwrap()
            ) == *"[0,3)"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(4), Included(5)))
            .is_none());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(10), Included(14)))
                    .unwrap()
            ) == *"[6,10]"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(14), Included(15)))
            .is_none());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(15), Included(18)))
                    .unwrap()
            ) == *"[16,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(19), Included(19)))
                    .unwrap()
            ) == *"[16,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(23), Included(26)))
                    .unwrap()
            ) == *"(25,30]"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Excluded(10), Excluded(15)))
            .is_none());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(21), Included(23)))
                    .unwrap()
            ) == *"(15,23)"
        );

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(31), Included(36)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(12)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(13), Included(13)))
            .is_none());
        assert!(interval_tree
            .find_overlap(&Interval::new(Included(12), Included(14)))
            .is_none());
    }

    #[test]
    fn tree_interval_find_overlap_3() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Unbounded, Excluded(3)), ());
        interval_tree.insert(Interval::new(Excluded(5), Included(8)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Unbounded, Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Unbounded, Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Unbounded), ());
        interval_tree.insert(Interval::new(Unbounded, Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Unbounded), ());

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(1), Included(2)))
                    .unwrap()
            ) == *"(_,9]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(4), Included(5)))
                    .unwrap()
            ) == *"(_,9]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(10), Included(14)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(14), Included(15)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(15), Included(18)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Included(19), Included(19)))
                    .unwrap()
            ) == *"(_,21)"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(23), Included(26)))
                    .unwrap()
            ) == *"(_,30]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Excluded(21), Included(23)))
                    .unwrap()
            ) == *"(_,30]"
        );

        assert!(
            format!(
                "{}",
                interval_tree
                    .find_overlap(&Interval::new(Unbounded, Included(0)))
                    .unwrap()
            ) == *"(_,9]"
        );
    }

    #[test]
    fn tree_interval_delete_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Included(0), Included(3)), ());
        interval_tree.insert(Interval::new(Included(5), Included(8)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Included(8), Included(9)), ());
        interval_tree.insert(Interval::new(Included(15), Included(23)), ());
        interval_tree.insert(Interval::new(Included(16), Included(21)), ());
        interval_tree.insert(Interval::new(Included(17), Included(19)), ());
        interval_tree.insert(Interval::new(Included(19), Included(20)), ());
        interval_tree.insert(Interval::new(Included(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());
        let mut interval = Interval::new(Included(1), Included(2));
        let mut overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        assert!(interval_tree.find_overlap(&interval).is_none());

        interval = Interval::new(Included(15), Included(18));
        overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        overlapped_interval = interval_tree.find_overlap(&interval).unwrap();
        interval_tree.delete(&overlapped_interval);
        assert!(interval_tree.find_overlap(&interval).is_none());
    }

    #[test]
    fn tree_interval_delete_max_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());
        interval_tree.delete_max();
        interval_tree.delete_max();

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(23), Included(23)))
            .is_none());
    }

    #[test]
    fn tree_interval_delete_min_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Included(0), Included(3)), ());
        interval_tree.insert(Interval::new(Included(5), Included(8)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Included(8), Included(9)), ());
        interval_tree.insert(Interval::new(Included(15), Included(23)), ());
        interval_tree.insert(Interval::new(Included(16), Included(21)), ());
        interval_tree.insert(Interval::new(Included(17), Included(19)), ());
        interval_tree.insert(Interval::new(Included(19), Included(20)), ());
        interval_tree.insert(Interval::new(Included(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());
        interval_tree.delete_min();
        interval_tree.delete_min();

        assert!(interval_tree
            .find_overlap(&Interval::new(Included(1), Excluded(6)))
            .is_none());
    }

    #[test]
    fn tree_interval_select_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());
        assert!(format!("{}", interval_tree.select(0).unwrap()) == *"[0,3)");
        assert!(format!("{}", interval_tree.select(1).unwrap()) == *"(0,1]");
        assert!(format!("{}", interval_tree.select(2).unwrap()) == *"[6,10]");
        assert!(format!("{}", interval_tree.select(3).unwrap()) == *"(8,9]");
        assert!(format!("{}", interval_tree.select(4).unwrap()) == *"(15,23)");
        assert!(format!("{}", interval_tree.select(5).unwrap()) == *"[16,21)");
        assert!(format!("{}", interval_tree.select(6).unwrap()) == *"[17,19)");
        assert!(format!("{}", interval_tree.select(7).unwrap()) == *"(19,20]");
        assert!(format!("{}", interval_tree.select(8).unwrap()) == *"(25,30]");
        assert!(format!("{}", interval_tree.select(9).unwrap()) == *"[26,26]");
    }

    #[test]
    fn tree_interval_intervals_between_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());

        let low = Interval::new(Included(14), Included(14));
        let high = Interval::new(Included(24), Included(24));
        let intervals = interval_tree.intervals_between(&low, &high);

        let accept = String::from("(15,23)[16,21)[17,19)(19,20]");

        let mut result = String::from("");
        for interval in intervals {
            result.push_str(&format!("{}", interval));
        }

        assert_eq!(result, accept);
    }

    #[test]
    fn tree_interval_find_overlaps_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());

        let interval = Interval::new(Included(8), Included(26));
        let intervals = interval_tree.find_overlaps(&interval);

        let accept = String::from("(8,9][6,10](19,20][16,21)(15,23)[17,19)(25,30][26,26]");

        let mut result = String::from("");
        for interval in intervals {
            result.push_str(&format!("{}", interval));
        }

        assert_eq!(result, accept);
    }

    #[test]
    fn tree_interval_query_1() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), ());
        interval_tree.insert(Interval::new(Included(6), Included(10)), ());
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), ());
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), ());
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), ());
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), ());
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), ());
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), ());
        interval_tree.insert(Interval::new(Included(26), Included(26)), ());

        let interval = Interval::new(Included(8), Included(26));
        let iter = interval_tree.query(&interval);

        let accept = String::from("(8,9][6,10](19,20][16,21)(15,23)[17,19)(25,30][26,26]");

        let mut result = String::from("");
        for entry in iter {
            result.push_str(&format!("{}", entry.interval()));
        }

        assert_eq!(result, accept);
    }

    #[test]
    fn tree_interval_query_2() {
        let mut interval_tree = IntervalTree::<usize, bool>::new();

        interval_tree.insert(Interval::new(Excluded(0), Included(1)), true);
        interval_tree.insert(Interval::new(Included(0), Excluded(3)), true);
        interval_tree.insert(Interval::new(Included(6), Included(10)), true);
        interval_tree.insert(Interval::new(Excluded(8), Included(9)), true);
        interval_tree.insert(Interval::new(Excluded(15), Excluded(23)), true);
        interval_tree.insert(Interval::new(Included(16), Excluded(21)), true);
        interval_tree.insert(Interval::new(Included(17), Excluded(19)), true);
        interval_tree.insert(Interval::new(Excluded(19), Included(20)), true);
        interval_tree.insert(Interval::new(Excluded(25), Included(30)), true);
        interval_tree.insert(Interval::new(Included(26), Included(26)), true);

        let interval = Interval::new(Included(8), Included(26));
        let iter = interval_tree.query_mut(&interval);

        for mut entry in iter {
            *entry.value() = false;
        }

        let iter = interval_tree.query(&interval);
        for entry in iter {
            assert!(!*entry.value());
        }
    }

    #[test]
    fn tree_interval_debug() {
        let mut interval_tree = IntervalTree::<usize, ()>::new();
        assert_eq!(format!("{:?}", &interval_tree), "IntervalTree {}");
        interval_tree.insert(Interval::new(Excluded(0), Included(1)), ());
        assert_eq!(
            format!("{:?}", &interval_tree),
            "IntervalTree {Interval { low: Excluded(0), high: Included(1) }}"
        );
    }
}
