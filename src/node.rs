extern crate rand;

use std;

#[derive(Debug, Eq, PartialEq, Clone, Default)]
pub struct InternalNode<T> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {
    value: T,
    sum : T,
    height: i8,
    left: Node<T>,
    right: Node<T>,
}

#[derive(Debug, Eq, PartialEq, Clone, Default)]
pub struct LeafNode<T> {
    value: T,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Node<T> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {
    Internal(Box<InternalNode<T>>),
    Leaf(Box<LeafNode<T>>),
    None,
}

impl<T> std::default::Default for Node<T> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {
    fn default() -> Node<T> {
        Node::None
    }
}

impl<T> From<T> for Node<T> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {
    fn from (value: T) -> Self {
        Node::new(value)
    }
}

impl <T> Node<T> where T: PartialEq + Copy + std::default::Default + std::ops::Add<Output = T> + std::fmt::Debug {
    pub fn new(value: T) -> Node<T> {
        Node::Leaf(Box::new(LeafNode{value: value}))
    }

    pub fn promote(&mut self) {
        match self {
            &mut Node::Leaf(_) => {
                *self = Node::Internal(Box::new(InternalNode{
                    value: self.value(),
                    sum: self.value(),
                    height: 1,
                    left: Node::None,
                    right: Node::None,
                }))
            },
            _ => panic!("Attempted to promote non leaf node {:?}", self),
        }
    }

    pub fn demote(&mut self) {
        match self {
            &mut Node::Internal(_) => {
                debug_assert_eq!(*self.left(), Node::None);
                debug_assert_eq!(*self.right(), Node::None);
                *self = Node::new(self.value())
            },
            _ => panic!("Attempted to demote non internal node {:?}", self),
        }
    }

    pub fn insert<Cmp>(&mut self, value: T, compare: &Cmp)
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering {
        match self {
            &mut Node::Internal(_) => {
                match compare(& value, & self.value()) {
                    std::cmp::Ordering::Less => {
                        self.left_mut().insert(value, compare);
                    },
                    std::cmp::Ordering::Equal => {
                        if *self.left() == Node::None {
                            self.left_mut().insert(value, compare);
                        } else {
                            self.right_mut().insert(value, compare);
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        self.right_mut().insert(value, compare);
                    },
                };
                self.update();
            },
            &mut Node::Leaf(_) => {
                self.promote();
                self.insert(value, compare);
            }
            &mut Node::None => {
                *self = Node::Leaf(Box::new(LeafNode{value: value}));
            }
        }
    }

    pub fn delete<Cmp>(&mut self, value: T, compare: &Cmp) -> bool
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering {
        match self {
            &mut Node::Internal(_) => {
                let success = match compare(& value, & self.value()) {
                    std::cmp::Ordering::Less => {
                        self.left_mut().delete(value, compare)
                    },
                    std::cmp::Ordering::Equal => {
                        if value == self.value() {
                            if self.left().height() > self.right().height() {
                                *self.value_mut() = self.left_mut().delete_rightmost();
                            } else {
                                *self.value_mut() = self.right_mut().delete_leftmost();
                            }
                            true
                        } else {
                            self.left_mut().delete(value, compare) ||
                            self.right_mut().delete(value, compare)
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        self.right_mut().delete(value, compare)
                    },
                };
                self.update();
                success
            },
            &mut Node::Leaf(_) => {
                match compare(& value, & self.value()) {
                    std::cmp::Ordering::Less => {
                        false
                    },
                    std::cmp::Ordering::Equal => {
                        *self = Node::None;
                        true
                    }
                    std::cmp::Ordering::Greater => {
                        false
                    },
                }
            },
            &mut Node::None => {
                false
            }
        }
    }

    pub fn delete_leftmost(&mut self) -> T {
        let value;
        match self {
            &mut Node::Internal(_) => {
                match self.left().height() {
                    0 => {
                        debug_assert_eq!(self.right().height(), 1, "{:#?}", self);
                        value = self.value();
                        *self.value_mut() = self.right().value();
                        *self.right_mut() = Node::None;
                        self.update();
                    }
                    _ => {
                        value = self.left_mut().delete_leftmost();
                        self.update();
                    }
                }
            },
            &mut Node::Leaf(_) => {
                value = self.value();
                *self = Node::None;
            }
            &mut Node::None => {
                panic!("leftmost of {:?}", self);
            }
        }
        value
    }

    pub fn delete_rightmost(&mut self) -> T {
        let value;
        match self {
            &mut Node::Internal(_) => {
                match self.right().height() {
                    0 => {
                        debug_assert_eq!(self.left().height(), 1, "{:#?}", self);
                        value = self.value();
                        *self.value_mut() = self.left().value();
                        *self.left_mut() = Node::None;
                        self.update();
                    }
                    _ => {
                        value = self.right_mut().delete_rightmost();
                        self.update();
                    }
                }
            },
            &mut Node::Leaf(_) => {
                value = self.value();
                *self = Node::None;
            }
            &mut Node::None => {
                panic!("rightmost of {:?}", self);
            }
        }
        value
    }

    pub fn update(&mut self) {
        if let Node::Internal(_) = *self {
            if *self.left() == Node::None && *self.right() == Node::None {
                self.demote();
            } else {
                match self.right().height() - self.left().height() {
                    -2 => {
                        if self.left().left().height() < self.left().right().height()
                        {
                            self.left_mut().rotate_left();
                        }

                        self.rotate_right();
                    },
                    2 => {
                        if self.right().right().height() < self.right().left().height()
                        {
                            self.right_mut().rotate_right();
                        }

                        self.rotate_left();
                    },
                    -1 | 0 | 1 => {
                        self.update_sum();
                        self.update_height();
                    },
                    _ => panic!("{:?} {:?}", self.right(), self.left()),
                }
            }
        }
    }

    pub fn rotate_right(&mut self) {
        match self.left().height() {
            0 => panic!("invalid rotation {:?}", self),
            1 => {
                debug_assert_eq!(self.right().height(), 0);
                let node_nonce = Node::None;
                let left = std::mem::replace(self.left_mut(), node_nonce);
                let right = std::mem::replace(self.right_mut(), left);
                debug_assert_eq!(right, Node::None);

                let value_nonce = T::default();
                let value = std::mem::replace(self.value_mut(), value_nonce);
                let right_value = std::mem::replace(self.right_mut().value_mut(), value);
                let value_nonce = std::mem::replace(self.value_mut(), right_value);
                debug_assert_eq!(value_nonce, T::default());

                self.update_height();
                self.update_sum();
            },
            _ => {
                let node_nonce = Node::None;
                let right = std::mem::replace(self.right_mut(), node_nonce);
                let left_right = std::mem::replace(self.left_mut().right_mut(), right);
                let left_left = std::mem::replace(self.left_mut().left_mut(), left_right);
                let left = std::mem::replace(self.left_mut(), left_left);
                let node_nonce = std::mem::replace(self.right_mut(), left);
                debug_assert_eq!(node_nonce, Node::None);

                let value_nonce = T::default();
                let value = std::mem::replace(self.value_mut(), value_nonce);
                let right_value = std::mem::replace(self.right_mut().value_mut(), value);
                let value_nonce = std::mem::replace(self.value_mut(), right_value);
                debug_assert_eq!(value_nonce, T::default());

                if *self.right().left() == Node::None && *self.right().right() == Node::None {
                    self.right_mut().demote();
                } else {
                    self.right_mut().update_height();
                    self.right_mut().update_sum();
                }

                self.update_height();
                self.update_sum();
            }
        }
    }

    pub fn rotate_left(&mut self) {
        match self.right().height() {
            0 => panic!("invalid rotation {:?}", self),
            1 => {
                debug_assert_eq!(self.left().height(), 0);
                let node_nonce = Node::None;
                let right = std::mem::replace(self.right_mut(), node_nonce);
                let left = std::mem::replace(self.left_mut(), right);
                debug_assert_eq!(left, Node::None);

                let value_nonce = T::default();
                let value = std::mem::replace(self.value_mut(), value_nonce);
                let left_value = std::mem::replace(self.left_mut().value_mut(), value);
                let value_nonce = std::mem::replace(self.value_mut(), left_value);
                debug_assert_eq!(value_nonce, T::default());

                self.update_height();
                self.update_sum();
            },
            _ => {
                let node_nonce = Node::None;
                let left = std::mem::replace(self.left_mut(), node_nonce);
                let right_left = std::mem::replace(self.right_mut().left_mut(), left);
                let right_right = std::mem::replace(self.right_mut().right_mut(), right_left);
                let right = std::mem::replace(self.right_mut(), right_right);
                let node_nonce = std::mem::replace(self.left_mut(), right);
                debug_assert_eq!(node_nonce, Node::None);

                let value_nonce = T::default();
                let value = std::mem::replace(self.value_mut(), value_nonce);
                let left_value = std::mem::replace(self.left_mut().value_mut(), value);
                let value_nonce = std::mem::replace(self.value_mut(), left_value);
                debug_assert_eq!(value_nonce, T::default());


                if *self.left().left() == Node::None && *self.left().right() == Node::None {
                    self.left_mut().demote();
                } else {
                    self.left_mut().update_height();
                    self.left_mut().update_sum();
                }

                self.update_height();
                self.update_sum();
            }
        }
    }

    pub fn sum(&self) -> T {
        match self {
            & Node::Internal(ref internal) => internal.sum,
            & Node::Leaf(ref leaf) => leaf.value,
            & Node::None => T::default(),
        }
    }

    pub fn sum_lt<Cmp>(&self, value: T, compare: &Cmp ) -> T
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering {
        match self {
            & Node::Internal(_) => {
                match compare(&self.value(), &value) {
                    std::cmp::Ordering::Less =>
                        self.left().sum() + self.value() + self.right().sum_lt(value, compare),
                    std::cmp::Ordering::Equal |
                    std::cmp::Ordering::Greater =>
                        self.left().sum_lt(value, compare),
                }
            },
            & Node::Leaf(_) => {
                match compare(&self.value(), &value) {
                    std::cmp::Ordering::Less => self.sum(),
                    std::cmp::Ordering::Equal |
                    std::cmp::Ordering::Greater => T::default(),
                }
            }
            & Node::None => {
                T::default()
            }
        }
    }

    pub fn sum_eq<Cmp>(&self, value: T, compare: &Cmp ) -> T
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering {
        match self {
            & Node::Internal(_) => {
                match compare(&self.value(), &value) {
                    std::cmp::Ordering::Less =>
                        self.right().sum_eq(value, compare),
                    std::cmp::Ordering::Equal => {
                        let mut sum_eq = self.value();

                        let mut left = self.left();
                        loop {
                            match left.height() {
                                0 | 1 =>  {
                                    sum_eq = sum_eq + left.sum_eq(value, compare);
                                    break;
                                },
                                _ =>  {
                                    match compare(&left.value(), &value) {
                                        std::cmp::Ordering::Less => (),
                                        std::cmp::Ordering::Equal => {
                                            sum_eq = sum_eq + left.value() + left.right().sum();
                                            left = left.left();
                                        }
                                        std::cmp::Ordering::Greater =>
                                            panic!("not correctly ordered {:?}", self),
                                    }
                                }
                            }
                        };

                        let mut right = self.right();
                        loop {
                            match right.height() {
                                0 | 1 => {
                                    sum_eq = sum_eq + right.sum_eq(value, compare);
                                    break;
                                }
                                _ =>  {
                                    match compare(&right.value(), &value) {
                                        std::cmp::Ordering::Less =>
                                            panic!("not correctly ordered {:?}", self),
                                        std::cmp::Ordering::Equal => {
                                            sum_eq = sum_eq + right.value() + right.left().sum();
                                            right = right.right();
                                        }
                                        std::cmp::Ordering::Greater => (),
                                    }
                                }
                            }
                        };
                        sum_eq
                    }
                    std::cmp::Ordering::Greater =>
                        self.left().sum_eq(value, compare),
                }
            },
            & Node::Leaf(_) => {
                match compare(&self.value(), &value) {
                    std::cmp::Ordering::Less => T::default(),
                    std::cmp::Ordering::Equal => self.sum(),
                    std::cmp::Ordering::Greater => T::default(),
                }
            }
            & Node::None => {
                T::default()
            }
        }
    }

    pub fn sum_gt<Cmp>(&self, value: T, compare: &Cmp ) -> T
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering {
        match self {
            & Node::Internal(_) => {
                match compare(&self.value(), &value) {
                    std::cmp::Ordering::Less |
                    std::cmp::Ordering::Equal =>
                        self.right().sum_gt(value, compare),
                    std::cmp::Ordering::Greater =>
                        self.left().sum_gt(value, compare) + self.value() + self.right().sum(),
                }
            },
            & Node::Leaf(_) => {
                match compare(&self.value(), &value) {
                    std::cmp::Ordering::Less |
                    std::cmp::Ordering::Equal => T::default(),
                    std::cmp::Ordering::Greater => self.sum(),
                }
            }
            & Node::None => {
                T::default()
            }
        }
    }

    pub fn update_sum(&mut self) {
        match self {
            &mut Node::Internal(ref mut internal) =>
            {
                internal.sum = internal.value + internal.left.sum() + internal.right.sum();
            }
            _ => {},
        }
    }

    pub fn value(& self) -> T {
        match self {
            & Node::Internal(ref  internal) => internal.value,
            & Node::Leaf(ref  leaf) => leaf.value,
            // & Node::None => T::default(),
            _ => panic!("{:?}", self),
        }
    }

    pub fn value_mut(&mut self) -> &mut T {
        match self {
            &mut Node::Internal(ref mut internal) => &mut internal.value,
            &mut Node::Leaf(ref mut leaf) => &mut leaf.value,
            _ => panic!("{:?}", self),
        }
    }

    pub fn left(& self) -> & Self {
        match self {
            & Node::Internal(ref  internal) => & internal.left,
            _ => panic!("{:?}", self),
        }
    }

    pub fn left_mut(&mut self) -> &mut Self {
        match self {
            &mut Node::Internal(ref mut internal) => &mut internal.left,
            _ => panic!("{:?}", self),
        }
    }

    pub fn right(&self) -> & Self {
        match self {
            & Node::Internal(ref  internal) => & internal.right,
            _ => panic!("{:?}", self),
        }
    }

    pub fn right_mut(&mut self) -> &mut Self {
        match self {
            &mut Node::Internal(ref mut internal) => &mut internal.right,
            _ => panic!("{:?}", self),
        }
    }

    pub fn height(& self) -> i8 {
        match self {
            & Node::Internal(ref node) => node.height,
            & Node::Leaf(_) => 1,
            & Node::None => 0,
        }
    }

    pub fn update_height(&mut self) {
        let default: Self = Node::None;
        let mut height = default.height();
        if let Node::Internal(_) = *self {
            height = 1 + std::cmp::max(self.left().height(), self.right().height());
        }
        if let &mut Node::Internal(ref mut node) = self {
            node.height = height;
        }
    }

    pub fn nearest<Dist, Cmp>(&self, value: T, compare: &Cmp, distance: &Dist) -> Option<T>
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering, Dist: Fn(&T, &T) -> T {
        match self {
            & Node::Internal(_) => {
                match compare(&value, &self.value()) {
                    std::cmp::Ordering::Less => {
                        let nearest_left = self.left().nearest(value, compare, distance);
                        Some(Self::nearest_to(value, self.value(), nearest_left, compare, distance))
                    },
                    std::cmp::Ordering::Equal => {
                        Some(self.value())
                    }
                    std::cmp::Ordering::Greater => {
                        let nearest_right = self.right().nearest(value, compare, distance);
                        Some(Self::nearest_to(value, self.value(), nearest_right, compare, distance))
                    },
                }
            },
            & Node::Leaf(_) => {
                Some(self.value())
            }
            & Node::None => {
                None
            }
        }
    }

    pub fn nearest_to<Dist, Cmp>(value: T, current_value: T, decendent_nearest: Option<T>, compare: &Cmp, distance: Dist) -> T
        where Cmp: Fn(&T, &T) -> std::cmp::Ordering, Dist: Fn(&T, &T) -> T, {
        if let Some(decendent_value) = decendent_nearest {
            let current_distance = distance(&value, &current_value);
            let decendent_distance = distance(&value, &decendent_value);

            if compare(&decendent_distance, &current_distance) == std::cmp::Ordering::Less {
                decendent_value
            } else {
                current_value
            }
        } else {
            current_value
        }
    }

}

#[allow(dead_code)]
fn test_tree(min: i32, max: i32, spacing: i32) -> (Node<i32>, i32) {
    if max - min < spacing {
        (Node::default(), i32::default())
    } else {
        let mid = (min + max) / 2;
        let mut node = Node::new(mid);
        node.promote();

        let (left, _) = test_tree(min, mid - 1, spacing);
        *node.left_mut() = left;
        let (right, _) = test_tree(mid + 1, max, spacing);
        *node.right_mut() = right;

        node.update();

        let sum = node.sum();
        (node, sum)
    }
}

#[allow(dead_code)]
fn sum(node: &Node<i32>) -> i32 {
    match node {
        & Node::Internal(_) => {
            assert_eq!(node.sum(), node.value() + sum(node.left()) + sum(node.right()));
            node.sum()
        },
        & Node::Leaf(_) => {
            assert_eq!(node.sum(), node.value());
            node.sum()
        }
        & Node::None => {
            assert_eq!(node.sum(), i32::default());
            node.sum()
        }
    }
}

#[allow(dead_code)]
fn height(node: &Node<i32>) -> i8 {
    match node {
        & Node::Internal(_) => {
            let left_height = height(node.left());
            let right_height = height(node.right());
            assert!(i8::abs(right_height - left_height) < 2);
            assert_eq!(node.height(), 1 + i8::max(left_height, right_height));
            node.height()
        },
        & Node::Leaf(_) => {
            assert_eq!(node.height(), 1);
            node.height()
        }
        & Node::None => {
            assert_eq!(node.sum(), 0);
            node.height()
        }
    }
}

#[allow(dead_code)]
fn range(node: &Node<i32>, min: Option<i32>, max: Option<i32>) -> (Option<i32>, Option<i32>) {
    match node {
        & Node::Internal(_) => {
            let new_min;
            let new_max;

            if node.left().height() != 0 && min.is_some() {
                assert!(node.left().value() >=  min.unwrap(),
                    "{:#?}\n{} >= {}", node, node.left().value(), min.unwrap())
            }

            if node.right().height() != 0 && max.is_some() {
                assert!(node.right().value() <=  max.unwrap(),
                    "{:#?}\n{} <= {}", node, node.right().value(), max.unwrap())
            }


            let (left_min, left_max) = range(node.left(), min, Some(node.value()));
            let (right_min, right_max) = range(node.right(), Some(node.value()), max);

            if left_min.is_some() {
                if min.is_some() {
                    assert!(left_min.unwrap() >= min.unwrap());
                }
                assert!(left_max.is_some());
                assert!(left_max.unwrap() <= node.value());
                new_min = left_min;
            } else {
                assert_eq!(node.left().height(), 0);
                new_min = Some(node.value());
            }

            if right_max.is_some() {
                if max.is_some() {
                    assert!(right_max.unwrap() <= max.unwrap());
                }
                assert!(right_min.is_some());
                assert!(right_min.unwrap() >= node.value());
                new_max = right_max;
            } else {
                assert_eq!(node.right().height(), 0);
                new_max = Some(node.value());
            }

            (new_min, new_max)
        },
        & Node::Leaf(_) => {
            (Some(node.value()), Some(node.value()))
        }
        & Node::None => {
            (None, None)
        }
    }
}

#[test]
fn refrence_tree() {
    let (root, root_sum) = test_tree(0, 6, 0);
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), 21);
    assert_eq!(root.height(), 3);
    assert_eq!(root_sum, 21);

    assert_eq!(sum(&root), 21);
    assert_eq!(height(&root), 3);
    assert_eq!(range(&root, Some(0), Some(6)), (Some(0), Some(6)));
}

#[test]
fn basic_operations() {
    let ref cmp = |a: &f32, b: &f32|{ a.partial_cmp(&b).unwrap()};
    let mut root: Node<f32> = Node::default();

    assert_eq!(root, Node::None);
    assert_eq!(root.sum(), 0.0);
    assert_eq!(root.height(), 0);

    root.insert(1.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 1.0);
    assert_eq!(root.height(), 1);

    root.insert(2.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 3.0);
    assert_eq!(root.height(), 2);

    root.insert(0.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 3.0);
    assert_eq!(root.height(), 2);

    root.delete(0.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 3.0);
    assert_eq!(root.height(), 2);

    root.insert(0.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 3.0);
    assert_eq!(root.height(), 2);

    root.delete(2.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 1.0);
    assert_eq!(root.height(), 2);

    root.insert(2.0, cmp);
    assert_eq!(root.value(), 1.0);
    assert_eq!(root.sum(), 3.0);
    assert_eq!(root.height(), 2);

    root.delete(1.0, cmp);
    assert!(root.value() != 1.0);
    assert_eq!(root.sum(), 2.0);
    assert_eq!(root.height(), 2);

    root.delete(2.0, cmp);
    assert_eq!(root.value(), 0.0);
    assert_eq!(root.sum(), 0.0);
    assert_eq!(root.height(), 1);

    root.delete(0.0, cmp);
    assert_eq!(root.height(), 0);
    assert_eq!(root.sum(), 0.0);
}

#[test]
fn insert_left_left() {
    let mut root = Node::default();
    root.insert(5, &i32::cmp);
    root.insert(3, &i32::cmp);
    root.insert(2, &i32::cmp);
    assert_eq!(root.left().value(), 2);
    assert_eq!(root.value(), 3);
    assert_eq!(root.right().value(), 5);
}

#[test]
fn insert_right_right() {
    let mut root = Node::default();
    root.insert(3, &i32::cmp);
    root.insert(5, &i32::cmp);
    root.insert(7, &i32::cmp);
    assert_eq!(root.left().value(), 3);
    assert_eq!(root.value(), 5);
    assert_eq!(root.right().value(), 7);
}

#[test]
fn insert_left_right() {
    let mut root = Node::default();
    root.insert(5, &i32::cmp);
    root.insert(3, &i32::cmp);
    root.insert(4, &i32::cmp);
    assert_eq!(root.left().value(), 3);
    assert_eq!(root.value(), 4);
    assert_eq!(root.right().value(), 5);
}

#[test]
fn insert_right_left() {
    let mut root = Node::default();
    root.insert(3, &i32::cmp);
    root.insert(5, &i32::cmp);
    root.insert(4, &i32::cmp);
    println!("{:#?}", root);
    assert_eq!(root.left().value(), 3);
    assert_eq!(root.value(), 4);
    assert_eq!(root.right().value(), 5);
}

#[test]
fn delete_left_left() {
    let (mut root, mut node_sum) = test_tree(0, 6, 0);

    assert_eq!(root.delete(4, &i32::cmp), true);
    node_sum -= 4;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(6, &i32::cmp), true);
    node_sum -= 6;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(5, &i32::cmp), true);
    node_sum -= 5;

    assert_eq!(root.value(), 1);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.left().value(), 0);
    assert_eq!(root.left().sum(), 0);
    assert_eq!(root.left().height(), 1);

    assert_eq!(root.right().value(), 3);
    assert_eq!(root.right().sum(), 5);
    assert_eq!(root.right().height(), 2);

    assert_eq!(root.right().left().value(), 2);
    assert_eq!(root.right().left().sum(), 2);
    assert_eq!(root.right().left().height(), 1);
}

#[test]
fn delete_left_right() {
    let (mut root, mut node_sum) = test_tree(0, 6, 0);

    assert_eq!(root.delete(0, &i32::cmp), true);
    node_sum -= 0;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(6, &i32::cmp), true);
    node_sum -= 6;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(4, &i32::cmp), true);
    node_sum -= 4;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(5, &i32::cmp), true);
    node_sum -= 5;

    assert_eq!(root.value(), 2);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 2);

    assert_eq!(root.left().value(), 1);
    assert_eq!(root.left().sum(), 1);
    assert_eq!(root.left().height(), 1);

    assert_eq!(root.right().value(), 3);
    assert_eq!(root.right().sum(), 3);
    assert_eq!(root.right().height(), 1);
}


#[test]
fn delete_right_left() {
    let (mut root, mut node_sum) = test_tree(0, 6, 0);

    assert_eq!(root.delete(2, &i32::cmp), true);
    node_sum -= 2;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(0, &i32::cmp), true);
    node_sum -= 0;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(6, &i32::cmp), true);
    node_sum -= 6;
    assert_eq!(root.value(), 3);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 3);

    assert_eq!(root.delete(1, &i32::cmp), true);
    node_sum -= 1;

    assert_eq!(root.value(), 4);
    assert_eq!(root.sum(), node_sum);
    assert_eq!(root.height(), 2);

    assert_eq!(root.left().value(), 3);
    assert_eq!(root.left().sum(), 3);
    assert_eq!(root.left().height(), 1);

    assert_eq!(root.right().value(), 5);
    assert_eq!(root.right().sum(), 5);
    assert_eq!(root.right().height(), 1);
}

#[test]
fn delete_leftmost() {
    let (mut root, mut root_sum) = test_tree(0, 6, 0);
    for i in 0..6 {
        root_sum -= i;
        assert_eq!(root.delete_leftmost(), i);
        assert_eq!(sum(&root), root_sum);
        assert_eq!(range(&root, Some(i+1), Some(6)), (Some(i+1), Some(6)));
        assert!(height(&root) != 0);
    }
    root_sum -= 6;
    assert_eq!(root.delete_leftmost(), 6);
    assert_eq!(sum(&root), root_sum);
    assert_eq!(range(&root, None, None), (None, None));
    assert_eq!(height(&root), 0);
}

#[test]
fn delete_rightmost() {
    let (mut root, mut root_sum) = test_tree(0, 6, 0);
    for i in (1..7).rev() { // [6..1] in haskell
        root_sum -= i;
        assert_eq!(root.delete_rightmost(), i);
        assert_eq!(sum(&root), root_sum);
        assert_eq!(range(&root, Some(0), Some(i-1)), (Some(0), Some(i-1)));
        assert!(height(&root) != 0);
    }
    root_sum -= 0;
    assert_eq!(root.delete_rightmost(), 0);
    assert_eq!(sum(&root), root_sum);
    assert_eq!(range(&root, None, None), (None, None));
    assert_eq!(height(&root), 0);
}

#[test]
fn delete_center() {
    let (mut root, _) = test_tree(0, 6, 0);
    assert_eq!(sum(&root), 21);
    assert_eq!(height(&root), 3);
    assert_eq!(range(&root, Some(0), Some(6)), (Some(0), Some(6)));

    assert_eq!(root.value(), 3);
    root.delete(3, &i32::cmp);
    assert!(root.value() == 2 || root.value() == 4);
    assert_eq!(sum(&root), 18);
    assert_eq!(height(&root), 3);
    assert_eq!(range(&root, Some(0), Some(6)), (Some(0), Some(6)));
}

#[test]
fn random_walk() {
    let mut root = Node::<i32>::default();

    let (mut range_min, mut range_max) = range(&root, None, None);
    let mut root_height = height(&root);
    let mut root_sum = sum(&root);
    let mut node_count: isize = 0;

    let iterations = 10000;
    let mut random_value = 0;
    let mut step_size = 20;
    for _ in 0..iterations {
        step_size += rand::random::<i32>() % 2;
        if step_size != 0
        {
            random_value += rand::random::<i32>() % step_size
        };

        if rand::random() {
            node_count += 1;
            range_min = range_min.map_or(Some(random_value), |min| Some(min.min(random_value)));
            range_max = range_max.map_or(Some(random_value), |max| Some(max.max(random_value)));
            root_sum += random_value;
            root.insert(random_value, &i32::cmp);
            assert_eq!(range(&root, range_min, range_max), (range_min, range_max));
        } else {
            if root.delete(random_value, &i32::cmp)
            {
                node_count -= 1;

                range_min = range_min.map_or(None, |min| {
                    if random_value == min {
                        root.nearest(min, &i32::cmp, &|a, b| (a - b).abs())
                    } else {
                        Some(min)
                    }});
                range_max = range_max.map_or(None, |max| {
                    if random_value == max {
                        root.nearest(max, &i32::cmp, &|a, b| (a - b).abs())
                    } else {
                        Some(max)
                    }});

                root_sum -= random_value;
                assert_eq!(range(&root, range_min, range_max), (range_min, range_max));
            } else {
                let nearest = root.nearest(random_value, &i32::cmp, &|a, b| (a - b).abs());
                assert!(node_count == 0 && nearest.is_none() || nearest.is_some() && nearest.unwrap() != random_value);
            }
        }

        let new_root_height = height(&root);
        assert_eq!(sum(&root), root_sum);
        assert!(i8::abs(root_height - new_root_height) <= 1);
        assert!(node_count <= 100 || new_root_height as f32 / 2.0 <= (node_count as f32).log2().ceil());
        root_height = new_root_height;
    }
}

#[test]
fn summations() {
    let (mut root, _) = test_tree(0, 10, 0);
    root.insert(3, &i32::cmp);
    root.insert(3, &i32::cmp);
    root.insert(3, &i32::cmp);

    assert_eq!(root.sum_lt(3, &i32::cmp), 3);
    assert_eq!(root.sum_eq(3, &i32::cmp), 12);
    assert_eq!(root.sum_gt(3, &i32::cmp), 49);
}

