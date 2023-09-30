use std::ptr;

pub struct List<T> {
    head: Link<T>,
    tail: *mut Node<T>,
}

pub struct Node<T> {
    val: T,
    next: Link<T>,
}

pub type Link<T> = *mut Node<T>;

impl<T> List<T> {
    pub fn new() -> Self {
        List {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
        }
    }

    pub fn push(&mut self, val: T) {
        unsafe {
            let raw_tail = Box::into_raw(Box::new(Node {
                val,
                next: ptr::null_mut(),
            }));
            if !self.tail.is_null() {
                (*self.tail).next = raw_tail;
            } else {
                self.head = raw_tail;
            }
            self.tail = raw_tail;
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        unsafe {
            if !self.head.is_null() {
                let result = Box::from_raw(self.head);
                self.head = result.next;
                if self.head.is_null() {
                    self.tail = self.head;
                }
                Some(result.val)
            } else {
                None
            }
        }
    }

    pub fn peek(&self) -> Option<&T> {
        unsafe { self.head.as_ref().map(|node| &node.val) }
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        unsafe { self.head.as_mut().map(|node| &mut node.val) }
    }

    pub fn iter(&self) -> Iter<T> {
        self.into_iter()
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        self.into_iter()
    }
}

pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.next.take().map(|node| {
                self.next = node.next.as_ref();
                &node.val
            })
        }
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        unsafe {
            Iter {
                next: self.head.as_ref(),
            }
        }
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.next.take().map(|node| {
                self.next = node.next.as_mut();
                &mut node.val
            })
        }
    }
}

impl<'a, T> IntoIterator for &'a mut List<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        unsafe {
            IterMut {
                next: self.head.as_mut(),
            }
        }
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use super::List;

    #[test]
    fn basics() {
        let mut list = List::new();

        assert_eq!(list.pop(), None);

        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), Some(2));

        list.push(4);
        list.push(5);

        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(4));
        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), None);

        list.push(6);
        list.push(7);
        assert_eq!(list.pop(), Some(6));
        assert_eq!(list.pop(), Some(7));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();
        list.push(1);
        list.push(2);
        list.push(3);

        let mut iter = list.into_iter();
        assert_eq!(Some(1), iter.next());
        assert_eq!(Some(2), iter.next());
        assert_eq!(Some(3), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn iter() {
        let mut list = List::new();
        list.push(1);
        list.push(2);

        let mut iter = list.iter();
        assert_eq!(Some(&1), iter.next());
        assert_eq!(Some(&2), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn iter_mut() {
        let mut list = List::new();
        list.push(1);
        list.push(2);

        let mut iter = list.iter_mut();
        assert_eq!(Some(&mut 1), iter.next());
        assert_eq!(Some(&mut 2), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn mix_it() {
        let mut list = List::new();

        list.push(1);
        list.push(2);
        list.push(3);

        assert_eq!(Some(1), list.pop());
        assert_eq!(Some(&2), list.peek());

        list.pop();
        list.push(4);

        assert_eq!(Some(&3), list.peek());
        if let Some(val) = list.peek_mut() {
            *val *= 100;
        }
        assert_eq!(Some(&300), list.peek());
        assert_eq!(Some(300), list.pop());
        list.push(5);

        for val in &mut list {
            *val *= 100;
        }

        let mut iter = list.iter();
        assert_eq!(Some(&400), iter.next());
        assert_eq!(Some(&500), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());

        assert_eq!(Some(400), list.pop());
        if let Some(val) = list.peek_mut() {
            *val *= 10;
        }
        assert_eq!(Some(&5000), list.peek());

        list.push(6000);

        {
            let empty: List<i32> = List::new();
            assert_eq!(None, empty.peek());
            // drop empty
        }
    }
}
