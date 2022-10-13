use std::cmp::Ord;
use std::ops::Bound;
use std::ops::Bound::*;
use std::rc::Rc;

use crate::interval::Interval;

#[derive(Hash)]
pub(crate) struct Node<T: Ord, V> {
    pub interval: Option<Interval<T>>,
    pub value: Option<V>,
    pub max: Option<Rc<Bound<T>>>,
    pub height: usize,
    pub size: usize,
    pub left_child: Option<Box<Node<T, V>>>,
    pub right_child: Option<Box<Node<T, V>>>,
}

impl<T: Ord, V> Node<T, V> {
    pub fn init(
        interval: Interval<T>,
        value: V,
        max: Rc<Bound<T>>,
        height: usize,
        size: usize,
    ) -> Node<T, V> {
        Node {
            interval: Some(interval),
            value: Some(value),
            max: Some(max),
            height: height,
            size: size,
            left_child: None,
            right_child: None,
        }
    }

    pub fn value(&self) -> &V {
        self.value.as_ref().unwrap()
    }

    // fn value_mut(&mut self) -> &mut V {
    //    self.value.as_mut().unwrap()
    //}

    pub fn get_value(&mut self) -> V {
        self.value.take().unwrap()
    }

    pub fn interval(&self) -> &Interval<T> {
        self.interval.as_ref().unwrap()
    }

    pub fn get_interval(&mut self) -> Interval<T> {
        self.interval.take().unwrap()
    }

    pub fn get_max(&self) -> Rc<Bound<T>> {
        Rc::clone(&self.max.as_ref().unwrap())
    }

    pub fn update_height(&mut self) {
        self.height = (1 + Node::_max_height(&self.left_child, &self.right_child)) as usize;
    }

    pub fn update_size(&mut self) {
        self.size = 1 + Node::size(&self.left_child) + Node::size(&self.right_child);
    }

    pub fn update_max(&mut self) {
        let max = match (&self.left_child, &self.right_child) {
            (Some(_left_child), Some(_right_child)) => Node::<T, V>::find_max(
                self.interval().get_high(),
                Node::<T, V>::find_max(_left_child.get_max(), _right_child.get_max()),
            ),
            (Some(_left_child), None) => {
                Node::<T, V>::find_max(self.interval().get_high(), _left_child.get_max())
            }
            (None, Some(_right_child)) => {
                Node::<T, V>::find_max(self.interval().get_high(), _right_child.get_max())
            }
            (None, None) => self.interval().get_high(),
        };

        self.max = Some(Rc::clone(&max));
    }

    pub fn find_max(bound1: Rc<Bound<T>>, bound2: Rc<Bound<T>>) -> Rc<Bound<T>> {
        match (bound1.as_ref(), bound2.as_ref()) {
            (Included(_val1), Included(_val2))
            | (Included(_val1), Excluded(_val2))
            | (Excluded(_val1), Excluded(_val2)) => {
                if _val1 >= _val2 {
                    bound1
                } else {
                    bound2
                }
            }
            (Excluded(_val1), Included(_val2)) => {
                if _val1 > _val2 {
                    bound1
                } else {
                    bound2
                }
            }
            (Unbounded, _) => bound1,
            (_, Unbounded) => bound2,
        }
    }

    pub fn is_ge(bound1: Rc<Bound<T>>, bound2: Rc<Bound<T>>) -> bool {
        match (bound1.as_ref(), bound2.as_ref()) {
            (Included(_val1), Included(_val2)) => _val1 >= _val2,
            (Included(_val1), Excluded(_val2)) => _val1 > _val2,
            (Excluded(_val1), Included(_val2)) => _val1 > _val2,
            (Excluded(_val1), Excluded(_val2)) => _val1 > _val2,

            (Unbounded, Included(_val2)) => true,
            (Unbounded, Excluded(_val2)) => true,
            (Included(_val1), Unbounded) => true,
            (Excluded(_val1), Unbounded) => true,

            (Unbounded, Unbounded) => true,
        }
    }

    pub fn _max_height(node1: &Option<Box<Node<T, V>>>, node2: &Option<Box<Node<T, V>>>) -> i64 {
        std::cmp::max(Node::height(node1), Node::height(node2))
    }

    pub fn height(node: &Option<Box<Node<T, V>>>) -> i64 {
        match node {
            Some(_node) => _node.height as i64,
            None => -1,
        }
    }

    pub fn size(node: &Option<Box<Node<T, V>>>) -> usize {
        match node {
            Some(_node) => _node.size,
            None => 0,
        }
    }

    pub fn balance_factor(node: &Box<Node<T, V>>) -> i64 {
        Node::height(&node.left_child) - Node::height(&node.right_child)
    }
}
