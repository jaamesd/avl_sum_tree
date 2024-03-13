#[allow(dead_code)]

use std;

use node::*;


pub struct AvlSumTree<'a, T: 'a> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {
    root: Node<T>,
    distance: &'a Fn(&T, &T) -> T,
    compare: &'a Fn(&T, &T) -> std::cmp::Ordering,
}


impl <'a, T: 'a> AvlSumTree<'a, T> where T: Ord + Copy + std::default::Default + std::ops::Add<Output = T> + std::ops::Sub<Output = T> + std::fmt::Debug {

    fn default_distance(value1: & T, value2: & T) -> T {
        if value1 > value2 {
            *value1 - *value2
        } else {
            *value2 - *value1
        }
    }

    fn new() -> Self {
        AvlSumTree{
            root: Node::None,
            distance: & Self::default_distance,
            compare: & T::cmp,
        }
    }

    fn insert<Cmp>(&mut self, value: T) {
        self.root.insert(value, &self.compare)
    }

    fn delete<Cmp>(&mut self, value: T) -> bool {
        self.root.delete(value, &self.compare)
    }

    fn nearest(&self, value: T) -> Option<T> {
        self.root.nearest(value, &self.compare, &self.distance)
    }

    fn into_boxed_slice(self) -> Box<[T]> {
        Box::new([T::default()])
    }

    fn new_from_slice(slice: &[T]) -> Self {
        unimplemented!();
        Self::new()
    }

    // Iterators
}

impl <'a, T: 'a> AvlSumTree<'a, T> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {

    fn new_with<Dist, Cmp>(compare: &'a Cmp, distance: &'a Dist) -> Self
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering, Dist: Fn(&T, &T) -> T {
        AvlSumTree{
            root: Node::None,
            distance: distance,
            compare: compare,
        }
    }

    fn new_from_slice_with<Dist, Cmp>(slice: &[T], compare: &'a Cmp, distance: &'a Dist) -> Self
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering, Dist: Fn(&T, &T) -> T {
        unimplemented!();
        Self::new_with(compare, distance)
    }

}