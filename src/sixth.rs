use std::cmp;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::{marker::PhantomData, ptr::NonNull};

// Note on variance:
//
// LinkedList<T> (and most collections) needs to effectively hold a mutable reference
// to T. Normally, a mutable reference to T is invariant over T, so using straight-up
// *mut pointer would make LinkedList also invariant over T. What that means is
// LinkedList<&'big u32> would not be allowed where LinkedList<&'small u32> is
// expected, for example. But such subtyping can be supported. According to the book,
// because of Rust's ownership system, LinkedList<T> is semantically equivalent to T,
// and that means it's safe to be covariant. In my understanding, it means since
// LinkedList<T> owns T and cannot be mutated without mutable reference to
// LinkedList, it's safe to be covariant. That's why we use NonNull<T> for the
// mutable pointer, which itself is a covariant. Use of PhantomData is not strictly
// necessary, but it declares that we *think* LinkedList owns T.

pub struct LinkedList<T> {
    head: Link<T>,
    tail: Link<T>,
    len: usize,
    // declare that semantically, list owns T
    _own: PhantomData<T>,
}

pub struct Node<T> {
    val: T,
    next: Link<T>,
    prev: Link<T>,
}

type Link<T> = Option<NonNull<Node<T>>>;

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            _own: PhantomData,
        }
    }

    pub fn push_front(&mut self, val: T) {
        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                val,
                next: None,
                prev: None,
            })));
            if let Some(old_head) = self.head {
                (*new_node.as_ptr()).next = Some(old_head);
                (*old_head.as_ptr()).prev = Some(new_node);
            } else {
                self.tail = Some(new_node);
            }
            self.head = Some(new_node);
            self.len += 1;
        }
    }

    pub fn push_back(&mut self, val: T) {
        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                val,
                next: None,
                prev: None,
            })));
            if let Some(old_tail) = self.tail {
                (*new_node.as_ptr()).prev = Some(old_tail);
                (*old_tail.as_ptr()).next = Some(new_node);
            } else {
                self.head = Some(new_node);
            }
            self.tail = Some(new_node);
            self.len += 1;
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        unsafe {
            self.head.map(|head| {
                let boxed_head = Box::from_raw(head.as_ptr());
                if let Some(new_head) = boxed_head.next {
                    (*new_head.as_ptr()).prev = None;
                }
                self.head = boxed_head.next;
                if self.head.is_none() {
                    self.tail = None;
                }
                self.len -= 1;
                boxed_head.val
            })
        }
    }

    pub fn pop_back(&mut self) -> Option<T> {
        unsafe {
            self.tail.map(|tail| {
                let boxed_tail = Box::from_raw(tail.as_ptr());
                if let Some(new_tail) = boxed_tail.prev {
                    (*new_tail.as_ptr()).next = None;
                }
                self.tail = boxed_tail.prev;
                if self.tail.is_none() {
                    self.head = None;
                }
                self.len -= 1;
                boxed_tail.val
            })
        }
    }

    pub fn front(&self) -> Option<&T> {
        unsafe { self.head.map(|head| &(*head.as_ptr()).val) }
    }

    pub fn front_mut(&self) -> Option<&mut T> {
        unsafe { self.head.map(|head| &mut (*head.as_ptr()).val) }
    }

    pub fn back(&self) -> Option<&T> {
        unsafe { self.tail.map(|tail| &(*tail.as_ptr()).val) }
    }

    pub fn back_mut(&self) -> Option<&mut T> {
        unsafe { self.tail.map(|tail| &mut (*tail.as_ptr()).val) }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }

    pub fn iter(&self) -> Iter<T> {
        self.into_iter()
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        self.into_iter()
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

pub struct Iter<'a, T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.len == 0 {
                return None;
            }
            self.front.map(|f| {
                self.len -= 1;
                self.front = (*f.as_ptr()).next;
                &(*f.as_ptr()).val
            })
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.len == 0 {
                return None;
            }
            self.back.map(|b| {
                self.len -= 1;
                self.back = (*b.as_ptr()).prev;
                &(*b.as_ptr()).val
            })
        }
    }
}

impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

pub struct IterMut<'a, T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    _phantom: PhantomData<&'a ()>,
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.len == 0 {
                return None;
            }
            self.front.map(|f| {
                self.len -= 1;
                self.front = (*f.as_ptr()).next;
                &mut (*f.as_ptr()).val
            })
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            if self.len == 0 {
                return None;
            }
            self.back.map(|b| {
                self.len -= 1;
                self.back = (*b.as_ptr()).prev;
                &mut (*b.as_ptr()).val
            })
        }
    }
}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

pub struct IntoIter<T> {
    list: LinkedList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.list.len()
    }
}

impl<'a, T> IntoIterator for &'a mut LinkedList<T> {
    type IntoIter = IterMut<'a, T>;
    type Item = <IterMut<'a, T> as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            front: self.head,
            back: self.tail,
            len: self.len,
            _phantom: PhantomData,
        }
    }
}

impl<'a, T> IntoIterator for &'a LinkedList<T> {
    type IntoIter = Iter<'a, T>;
    type Item = <Iter<'a, T> as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            front: self.head,
            back: self.tail,
            len: self.len,
            _phantom: PhantomData,
        }
    }
}

impl<T> IntoIterator for LinkedList<T> {
    type IntoIter = IntoIter<T>;
    type Item = <IntoIter<T> as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        LinkedList::new()
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut new_list = LinkedList::new();
        for item in self {
            new_list.push_back(item.clone());
        }
        new_list
    }
}

impl<T> Extend<T> for LinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, vals: I) {
        for item in vals {
            self.push_back(item);
        }
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(vals: I) -> Self {
        let mut list = Self::new();
        list.extend(vals);
        list
    }
}

impl<T: Debug> Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for LinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for LinkedList<T> {}

impl<T: PartialOrd> PartialOrd for LinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for LinkedList<T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash> Hash for LinkedList<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for item in self {
            item.hash(state);
        }
    }
}

#[cfg(test)]
mod test {
    use super::LinkedList;

    fn list_from<T: Clone>(elems: &[T]) -> LinkedList<T> {
        elems.iter().cloned().collect()
    }

    #[test]
    fn test_front() {
        let mut list = LinkedList::new();

        // test empty list
        assert_eq!(0, list.len());
        assert_eq!(None, list.pop_front());
        assert_eq!(0, list.len());

        // test list with one entry
        list.push_front(1);
        assert_eq!(1, list.len());
        assert_eq!(Some(1), list.pop_front());
        assert_eq!(0, list.len());
        assert_eq!(None, list.pop_front());
        assert_eq!(0, list.len());

        // mix ops
        list.push_front(1);
        list.push_front(2);
        assert_eq!(2, list.len());
        assert_eq!(Some(2), list.pop_front());
        assert_eq!(Some(1), list.pop_front());
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        assert_eq!(3, list.len());
        assert_eq!(Some(3), list.pop_front());
        assert_eq!(Some(2), list.pop_front());
        list.push_front(4);
        assert_eq!(2, list.len());
        assert_eq!(Some(4), list.pop_front());
        list.push_front(5);
        assert_eq!(Some(5), list.pop_front());
        assert_eq!(Some(1), list.pop_front());

        for i in 0..100 {
            list.push_front(i * 10);
        }

        for i in (0..100).rev() {
            assert_eq!(Some(i * 10), list.pop_front());
        }
    }

    #[test]
    fn test_basic() {
        let mut t = LinkedList::new();
        assert_eq!(t.pop_front(), None);
        assert_eq!(t.pop_back(), None);
        assert_eq!(t.pop_front(), None);
        t.push_back(1);
        assert_eq!(t.pop_back(), Some(1));
        t.push_front(1);
        assert_eq!(t.pop_back(), Some(1));
        t.push_front(1);
        t.push_front(2);
        assert_eq!(t.len(), 2);
        assert_eq!(t.pop_front(), Some(2));
        assert_eq!(t.pop_back(), Some(1));
        assert_eq!(t.len(), 0);
        assert!(t.is_empty());

        t.push_back(3);
        t.push_back(5);
        t.push_back(7);
        t.push_back(11);
        assert_eq!(t.pop_front(), Some(3));

        let mut m = LinkedList::new();
        m.push_back(21);
        m.push_back(22);
        {
            assert_eq!(m.front(), Some(&21));
            let f = m.front_mut().unwrap();
            *f = 31;
            assert_eq!(m.front(), Some(&31));
        }
        {
            assert_eq!(m.back(), Some(&22));
            let b = m.back_mut().unwrap();
            *b = 32;
            assert_eq!(m.back(), Some(&32));
        }
    }

    #[test]
    fn test_iterator() {
        let m = list_from(&[0, 1, 2, 3, 4, 5, 6]);
        for (i, elem) in m.iter().enumerate() {
            assert_eq!(i, *elem);
        }

        // test iterating empty list
        let mut n = LinkedList::new();
        assert_eq!(n.iter().next(), None);

        n.push_back(1);
        assert_eq!(n.iter().next(), Some(&1));

        n.clear();
        assert!(n.is_empty());

        n.push_front(1);
        n.push_back(2);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(it.next(), Some(&1));
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_double_ended_iterator() {
        let m: LinkedList<()> = LinkedList::new();
        assert_eq!(m.iter().next_back(), None);

        let m = list_from(&[0, 1, 2]);
        let mut iter = m.iter();
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.next_back(), Some(&2));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_rev_iterator() {
        let m = list_from(&[5, 4, 3, 2, 1, 0]);
        for (i, elem) in m.iter().rev().enumerate() {
            assert_eq!(i, *elem);
        }

        let mut n = LinkedList::new();
        assert_eq!(n.iter().rev().next(), None);
        n = list_from(&[42, 43, 44]);

        let mut iter = n.iter().rev();
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.next_back(), Some(&42));
        assert_eq!(iter.next(), Some(&44));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next(), Some(&43));
    }

    #[test]
    fn test_mut_iterator() {
        let mut m = list_from(&[0, 1, 2, 3]);
        for elem in m.iter_mut() {
            *elem += 1;
        }

        for (i, elem) in m.iter_mut().enumerate() {
            assert_eq!(*elem, i + 1);
        }

        let mut n = LinkedList::new();
        assert_eq!(n.iter_mut().next(), None);
        n.push_back(1);
        n.push_back(2);
        let mut iter = n.iter_mut();
        assert_eq!(iter.next(), Some(&mut 1));
        assert!(iter.next().is_some());
        assert!(iter.next().is_none());
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_double_ended_mut_iterator() {
        let mut m: LinkedList<()> = LinkedList::new();
        assert_eq!(m.iter_mut().next_back(), None);

        let mut m = list_from(&[0, 1, 2]);
        let mut iter = m.iter_mut();
        assert_eq!(iter.next(), Some(&mut 0));
        assert_eq!(iter.next_back(), Some(&mut 2));
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next_back(), Some(&mut 1));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_eq() {
        let mut m: LinkedList<u8> = list_from(&[]);
        let mut n = list_from(&[]);
        assert!(m == n);
        assert_eq!(m, n);

        m.push_back(1);
        assert!(m != n);

        n.push_front(1);
        assert!(m == n);

        let m = list_from(&[1, 2, 3]);
        let n = list_from(&[1, 2]);
        assert!(m != n);
    }

    #[test]
    fn test_ord() {
        let m = list_from(&[]);
        let n = list_from(&[1]);
        assert!(m < n);
        assert!(n > m);
        assert!(m <= n);
        assert!(n >= m);
    }

    #[test]
    fn test_ord_nan() {
        let nan = 0.0 / 0.0;
        assert!(f64::is_nan(nan));
        let m = list_from(&[nan]);
        let n = list_from(&[nan]);
        assert!(!(m < n));
        assert!(!(m > n));
        assert!(!(m <= n));
        assert!(!(m >= n));

        let one = list_from(&[3.0f64]);
        assert!(!(one < n));
        assert!(!(one > n));
        assert!(!(one <= n));
        assert!(!(one >= n));

        let u = list_from(&[1.0f64, 2.0, nan]);
        let v = list_from(&[1.0f64, 2.0, 3.0]);
        assert!(!(u < v));
        assert!(!(u > v));
        assert!(!(u <= v));
        assert!(!(u >= v));

        let s = list_from(&[1.0f64, 2.0, 4.0, 2.0]);
        let t = list_from(&[1.0f64, 2.0, 3.0, 2.0]);
        assert!(s > t);
        assert!(!(s <= t));
        assert!(t < s);
        assert!(!(t >= s));
    }

    #[test]
    fn test_debug() {
        let m = list_from(&[1, 2, 3]);
        assert_eq!(format!("{m:?}"), "[1, 2, 3]");

        let m: LinkedList<i32> = LinkedList::new();
        assert_eq!(format!("{m:?}"), "[]");

        let m = list_from(&["hello", "world"]);
        assert_eq!(format!("{m:?}"), r#"["hello", "world"]"#);
    }

    #[test]
    fn test_hashmap() {
        let list1 = list_from(&[1, 2, 3]);
        let list2 = list_from(&[1, 2, 4]);

        let mut map = std::collections::HashMap::new();

        assert_eq!(map.insert(list1.clone(), "list1"), None);
        assert_eq!(map.insert(list2.clone(), "list2"), None);

        assert_eq!(map.len(), 2);

        assert_eq!(map.get(&list1), Some(&"list1"));
        assert_eq!(map.get(&list2), Some(&"list2"));

        assert_eq!(map.remove(&list1), Some("list1"));
        assert_eq!(map.insert(list2.clone(), "list2_new"), Some("list2"));
    }

    #[test]
    fn test_variance() {
        fn take_two<T>(_l1: LinkedList<T>, _l2: LinkedList<T>) {}

        let mut list1: LinkedList<&'static str> = LinkedList::new();
        let hello: &'static str = "Hello";
        list1.push_front(hello);
        {
            let world = String::from("World");
            let mut list2: LinkedList<&str> = LinkedList::new();
            list2.push_front(world.as_str());
            take_two(list1, list2);
        }
    }
}
