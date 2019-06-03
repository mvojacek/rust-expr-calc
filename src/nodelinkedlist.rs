#![allow(unused_macros, unused_imports)]

use std::rc::Rc;
use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::rc::Weak;
use std::ops::Deref;
use std::ops::DerefMut;
use std::cell::RefMut;
use std::cell::Ref;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Error;
use std::mem;
use std::ptr;
use std::iter::FromIterator;
use std::iter;
use std::iter::Chain;
use std::iter::Once;
use itertools::Itertools;
use itertools::assert_equal;

type WeakNode<T> = Weak<RefCell<NodeInner<T>>>;
type StrongNode<T> = Rc<RefCell<NodeInner<T>>>;

#[derive(Debug)]
pub struct NodeInner<T> {
    pub data: T,
    prev: Option<WeakNode<T>>,
    next: Option<Node<T>>,
}

impl<T> NodeInner<T> {
    pub fn new(data: T) -> Self {
        Self { data, prev: None, next: None }
    }
}

#[derive(Debug)]
pub struct Node<T> (StrongNode<T>);

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Rc::clone(self).into()
    }
}

impl<T: Display> Display for Node<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.iter_walk_back().collect::<Vec<_>>().into_iter().rev().try_for_each(|n| {
            n.bor().data.fmt(f)?;
            f.write_str("<-")
        })?;
        self.bor().data.fmt(f)?;
        self.iter_walk().try_for_each(|n| {
            f.write_str(" ")?; //FIXME
            n.bor().data.fmt(f)
        })
    }
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self {
        Node(Rc::new(RefCell::new(NodeInner::new(data))))
    }

    pub fn bor_mut(&self) -> RefMut<NodeInner<T>> {
        RefCell::borrow_mut(self)
    }

    pub fn bor(&self) -> Ref<NodeInner<T>> {
        RefCell::borrow(self)
    }
}

impl<T> From<StrongNode<T>> for Node<T> {
    fn from(rc: StrongNode<T>) -> Self {
        Node(rc)
    }
}

impl<T> Deref for Node<T> {
    type Target = StrongNode<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Node<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() as *const _ == other.as_ref() as *const _
    }
}

impl<T> Eq for Node<T> {}

// helpers
impl<T> Node<T> {
    pub fn use_value<F, R>(&self, func: F) -> R where F: FnOnce(&T) -> R {
        func(&self.bor().data)
    }

    pub fn from_weak(weak: &WeakNode<T>) -> Option<Self> {
        weak.upgrade().map(From::from)
    }

    pub fn weak_node(node: &Self) -> WeakNode<T> {
        Rc::downgrade(node)
    }
}

// manipulation
impl<T> Node<T> {
    pub fn link(&self, next: Self) {
        next.bor_mut().prev = Some(Rc::downgrade(self));
        self.bor_mut().next = Some(next)
    }

    pub fn insert_after_node(&self, node: &Self) {
        if let Some(next) = self.next() {
            node.link(next);
        }
        self.link(node.clone());
    }

    pub fn insert_before_node(self, node: &Self) {
        if let Some(prev) = self.prev() {
            prev.link(node.clone());
        }
        node.link(self);
    }

    pub fn insert_after(&self, val: T) -> Self {
        let node = Node::new(val);
        self.insert_after_node(&node);
        node
    }

    pub fn insert_before(&self, val: T) -> Self {
        let node = Node::new(val);
        self.clone().insert_before_node(&node);
        node
    }


    fn isolate_prev(&self) {
        self.bor_mut().prev = None
    }

    fn isolate_next(&self) {
        self.bor_mut().next = None
    }

    fn isolate(&self) {
        self.isolate_prev();
        self.isolate_next();
    }

    pub fn split_after(&self) {
        if let Some(next) = self.next() {
            next.isolate_prev();
        }
        self.isolate_next();
    }

    pub fn split_before(&self) {
        if let Some(prev) = self.prev() {
            prev.isolate_next();
        }
        self.isolate_prev();
    }

    pub fn cut(&self) {
        match (self.prev(), self.next()) {
            (Some(prev), Some(next)) => prev.link(next),
            (Some(prev), None) => prev.isolate_next(),
            (None, Some(next)) => next.isolate_prev(),
            _ => {}
        }
        self.isolate();
    }
}

// navigation
impl<T> Node<T> {
    pub fn next(&self) -> Option<Self> {
        self.bor().next.clone()
    }

    pub fn prev(&self) -> Option<Self> {
        self.bor().prev.as_ref().and_then(|w| Node::from_weak(w))
    }

    pub fn iter_walk(&self) -> WalkingIter<T> {
        WalkingIter { current: Node::weak_node(self) }
    }

    pub fn iter_walk_back(&self) -> WalkingIterBack<T> {
        WalkingIterBack { current: Node::weak_node(self) }
    }

    pub fn iter_walk_val(&self) -> WalkingIterVal<T> where T: Clone {
        self.iter_walk().into()
    }

    pub fn list_iter(&self) -> Chain<Once<Self>, WalkingIter<T>> {
        iter::once(self.clone()).chain(self.iter_walk())
    }

    pub fn list_iter_back(&self) -> Chain<Once<Self>, WalkingIterBack<T>> {
        iter::once(self.clone()).chain(self.iter_walk_back())
    }

    pub fn list_iter_val(&self) -> Chain<Once<T>, WalkingIterVal<T>> where T: Clone {
        iter::once(self.bor().data.clone()).chain(self.iter_walk_val())
    }
}

impl<T> Node<T> {
    pub fn tail(&self) -> Self {
        self.list_iter().last().unwrap()
    }

    pub fn head(&self) -> Self {
        self.list_iter_back().last().unwrap()
    }

    pub fn list_len(&self) -> usize {
        self.list_iter().count()
    }

    pub fn list_distance(&self, following: &Self) -> Option<usize> {
        self.list_iter().find_position(|n| *n == *following).map(|t| t.0)
    }

    // returns true if other comes after self
    pub fn list_find(&self, other: &Self) -> Option<(bool, usize)> {
        self.list_distance(other).map(|d| (true, d))
            .or_else(|| other.list_distance(self).map(|d| (false, d)))
    }
}

impl<T> Node<T> {
    // list extension
    pub fn list_append_node(&self, node: &Self) {
        self.tail().insert_after_node(node);
    }

    pub fn list_append(&self, val: T) -> Self {
        self.tail().insert_after(val)
    }

    pub fn list_prepend_node(&self, node: &Self) {
        self.head().insert_before_node(node);
    }

    pub fn list_prepend(&self, val: T) -> Self {
        self.head().insert_before(val)
    }
}

#[derive(Clone)]
pub struct WalkingIter<T> {
    current: WeakNode<T>,
}

impl<T> Iterator for WalkingIter<T> {
    type Item = Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        Node::from_weak(&self.current).and_then(|n| n.next()).map(|n| {
            self.current = Node::weak_node(&n);
            n
        })
    }
}

#[derive(Clone)]
pub struct WalkingIterBack<T> {
    current: WeakNode<T>,
}

impl<T> Iterator for WalkingIterBack<T> {
    type Item = Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        Node::from_weak(&self.current).and_then(|n| n.prev()).map(|n| {
            self.current = Node::weak_node(&n);
            n
        })
    }
}

#[derive(Clone)]
pub struct WalkingIterVal<T: Clone> {
    iter: WalkingIter<T>
}

impl<T: Clone> From<WalkingIter<T>> for WalkingIterVal<T> {
    fn from(it: WalkingIter<T>) -> Self {
        WalkingIterVal { iter: it }
    }
}

impl<T: Clone> Iterator for WalkingIterVal<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|n| n.bor().data.clone())
    }
}

#[derive(Debug, Clone)]
pub struct NodeList<T> {
    pub head: Option<Node<T>>
}

impl<A> FromIterator<A> for NodeList<A> {
    fn from_iter<T: IntoIterator<Item=A>>(iter: T) -> Self {
        let it = &mut iter.into_iter() as &mut Iterator<Item=A>;
        NodeList {
            head: it.next().map(|a| {
                let head = Node::new(a);
                let mut node = head.clone();
                while let Some(a) = it.next() {
                    node = node.insert_after(a)
                }
                head
            })
        }
    }
}

macro_rules! assert_list_eq {
    ($node:expr, $str:expr) => (assert_eq!(format!("{}", &$node), $str);)
}

fn make_linkedlist_for_tests() -> [Node<i32>; 4] {
    let arr = unsafe {
        let mut n: [Node<i32>; 4] = mem::uninitialized();
        ptr::write(&mut n[0], Node::new(0));
        ptr::write(&mut n[1], n[0].insert_after(1));
        ptr::write(&mut n[2], n[1].insert_after(2));
        ptr::write(&mut n[3], n[2].insert_after(3));
        n
    };
    assert_list_eq!(&arr[0], "0->1->2->3");
    assert_list_eq!(&arr[0], "0->1->2->3");
    arr
}

#[test]
fn test_list_iter_val() {
    let n1 = Node::new(1);
    let n2 = Node::new(2);
    let n3 = Node::new(3);
    let n4 = Node::new(4);

    let mut it = n1.list_iter_val();


    assert_eq!(it.next(), Some(1));
    assert_eq!(it.next(), None);
    assert_eq!(it.next(), None);
    n1.link(n2.clone());
    n2.link(n3.clone());
    assert_eq!(it.next(), Some(2));
    assert_eq!(it.next(), Some(3));
    assert_eq!(it.next(), None);
    assert_eq!(it.next(), None);
    n3.link(n4.clone());
    assert_eq!(it.next(), Some(4));
    assert_eq!(it.next(), None);
    assert_eq!(it.next(), None);
}

#[test]
fn test_find_distance() {
    let n = make_linkedlist_for_tests();
    assert_list_eq!(&n[0], "0->1->2->3");
    let x = Node::new(4);

    assert_eq!(n[0].list_distance(&n[2]), Some(2));
    assert_eq!(n[0].list_distance(&x), None);

    assert_eq!(n[1].list_find(&n[2]), Some((true, 1)));
    assert_eq!(n[1].list_find(&x), None);
    assert_eq!(n[3].list_find(&n[1]), Some((false, 2)));
}

#[test]
fn test_equal() {
    let n = make_linkedlist_for_tests();
    n[2].bor_mut().data = 1;
    assert_list_eq!(&n[0], "0->1->1->3");

    assert_eq!(n[1] == n[0].next().unwrap(), true);
    assert_eq!(n[1] == n[1].next().unwrap(), false);
}

#[test]
fn test_head_tail() {
    let n = make_linkedlist_for_tests();
    assert_list_eq!(&n[0], "0->1->2->3");

    assert_eq!(n[3].head().bor().data, 0);
    assert_eq!(n[2].tail().bor().data, 3);
}

#[test]
fn test_cut() {
    let n = make_linkedlist_for_tests();
    assert_list_eq!(n[0], "0->1->2->3");

    n[2].cut();
    assert_list_eq!(n[0], "0->1->3");
    assert_list_eq!(n[2], "2");

    n[2].cut();
    assert_list_eq!(n[2], "2");

    n[0].cut();
    assert_list_eq!(n[1], "1->3");
    assert_list_eq!(n[0], "0");

    n[3].cut();
    assert_list_eq!(n[1], "1");
    assert_list_eq!(n[3], "3");
}

#[test]
fn test_link() {
    let n1 = Node::new(1);
    let n2 = Node::new(2);
    let n3 = Node::new(3);
    let n4 = Node::new(4);

    assert_list_eq!(&n1, "1");

    n1.link(n2.clone());
    assert_list_eq!(&n1, "1->2");

    n2.link(n3.clone());
    assert_list_eq!(&n1, "1->2->3");
    assert_list_eq!(&n2, "1<-2->3");

    n1.link(n3.clone());
    assert_list_eq!(&n1, "1->3");
    assert_list_eq!(&n2, "1<-2->3");
}

#[test]
fn test_insert_after() {
    let n1 = Node::new(1);
    let n2 = Node::new(2);
    let n3 = Node::new(3);
    let n4 = Node::new(4);

    n1.link(n2.clone());
    n1.insert_after_node(&n3);
    assert_list_eq!(&n1, "1->3->2");
    n2.insert_after_node(&n4);
    assert_list_eq!(&n1, "1->3->2->4");
}

#[test]
fn test_insert_before() {
    let n1 = Node::new(1);
    let n2 = Node::new(2);
    let n3 = Node::new(3);
    let n4 = Node::new(4);

    n1.link(n2.clone());
    n2.clone().insert_before_node(&n3);
    assert_list_eq!(&n1, "1->3->2");
    n1.clone().insert_before_node(&n4);
    assert_list_eq!(&n1, "4<-1->3->2");
    assert_list_eq!(&n4, "4->1->3->2");
}