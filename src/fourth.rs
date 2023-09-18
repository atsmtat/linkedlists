use std::{
    cell::{Ref, RefCell, RefMut},
    rc::Rc,
};

pub struct List<T> {
    head: Link<T>,
    tail: Link<T>,
}

type Link<T> = Option<Rc<RefCell<Node<T>>>>;

pub struct Node<T> {
    val: T,
    next: Link<T>,
    prev: Link<T>,
}

impl<T> Node<T> {
    pub fn new(val: T) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Node {
            val,
            next: None,
            prev: None,
        }))
    }
}

// Methods on the List maintains the following invariant:
// Each node should have exactly two pointers pointing to it.
//
// For node in the middle of the list, its predecessor and successor
// will point to it. In case of boundary nodes (head or tail), the
// List object will hold one or both pointers.
impl<T> List<T> {
    pub fn new() -> Self {
        List {
            head: None,
            tail: None,
        }
    }

    pub fn push_front(&mut self, val: T) {
        // new node needs 2 pointers
        let new_head = Node::new(val);

        if let Some(old_head) = self.head.take() {
            old_head.borrow_mut().prev = Some(new_head.clone()); // new head +1
            new_head.borrow_mut().next = Some(old_head.clone()); // old head +1
            self.head = Some(new_head); // new head +1, old head -1
        } else {
            self.head = Some(new_head.clone()); // new head +1
            self.tail = Some(new_head); // new head +1
        }
        // total diff: new head +2, old head 0. OK
    }

    pub fn push_back(&mut self, val: T) {
        // new node needs 2 pointers
        let new_tail = Node::new(val);

        if let Some(old_tail) = self.tail.take() {
            old_tail.borrow_mut().next = Some(new_tail.clone()); // new tail +1
            new_tail.borrow_mut().prev = Some(old_tail.clone()); // old tail +1
            self.tail = Some(new_tail); // new tail +1, old tail -1
        } else {
            self.head = Some(new_tail.clone()); // new tail +1
            self.tail = Some(new_tail); // new tail +1
        }
        // total diff: new tail +2, old tail 0. OK
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|old_head| {
            // old head has 2 pointers, which should drop to 0
            match old_head.borrow_mut().next.take() {
                Some(new_head) => {
                    new_head.borrow_mut().prev = None; // old head -1
                    self.head = Some(new_head); // old head -1
                }
                None => {
                    self.head = None; // old head -1
                    self.tail = None; // old head -1
                }
            }
            // total diff: old head -2. OK
            Rc::into_inner(old_head).unwrap().into_inner().val
        })
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.take().map(|old_tail| {
            // old tail has 2 pointers, which should drop to 0
            match old_tail.borrow_mut().prev.take() {
                Some(new_tail) => {
                    new_tail.borrow_mut().next.take(); // old tail -1
                    self.tail = Some(new_tail); // old tail -1
                }
                None => {
                    self.head.take(); // old tail -1
                    self.tail.take(); // old tail -1
                }
            }
            // total diff: old tail -2. OK
            Rc::into_inner(old_tail).unwrap().into_inner().val
        })
    }

    pub fn peek_front(&self) -> Option<Ref<T>> {
        self.head
            .as_ref()
            .map(|h| Ref::map(h.borrow(), |node| &node.val))
    }

    pub fn peek_front_mut(&mut self) -> Option<RefMut<T>> {
        self.head
            .as_ref()
            .map(|h| RefMut::map(h.borrow_mut(), |node| &mut node.val))
    }

    pub fn peek_back(&self) -> Option<Ref<T>> {
        self.tail
            .as_ref()
            .map(|t| Ref::map(t.borrow(), |node| &node.val))
    }

    pub fn peek_back_mut(&mut self) -> Option<RefMut<T>> {
        self.tail
            .as_ref()
            .map(|t| RefMut::map(t.borrow_mut(), |node| &mut node.val))
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_back()
    }
}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

#[cfg(test)]
mod tests {
    use super::List;

    #[test]
    fn head_ops() {
        let mut list = List::new();

        // empty list pop
        assert_eq!(None, list.pop_front());

        // push a few elems
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);

        // pop some
        assert_eq!(Some(3), list.pop_front());
        assert_eq!(Some(2), list.pop_front());

        // push one more
        list.push_front(4);

        // pop all
        assert_eq!(Some(4), list.pop_front());
        assert_eq!(Some(1), list.pop_front());
    }

    #[test]
    fn tail_ops() {
        let mut list = List::new();

        // empty list pop
        assert_eq!(None, list.pop_back());

        // push a few elems
        list.push_back(1);
        list.push_back(2);
        list.push_back(3);

        // pop some
        assert_eq!(Some(3), list.pop_back());
        assert_eq!(Some(2), list.pop_back());

        // push one more
        list.push_back(4);

        // pop all
        assert_eq!(Some(4), list.pop_back());
        assert_eq!(Some(1), list.pop_back());
    }

    #[test]
    fn peek() {
        let mut list = List::new();
        assert!(list.peek_front().is_none());
        assert!(list.peek_front_mut().is_none());
        assert!(list.peek_back().is_none());
        assert!(list.peek_back_mut().is_none());

        list.push_front(1);
        list.push_back(2);

        assert_eq!(&*list.peek_front().unwrap(), &1);
        assert_eq!(&mut *list.peek_front_mut().unwrap(), &mut 1);
        assert_eq!(&*list.peek_back().unwrap(), &2);
        assert_eq!(&mut *list.peek_back_mut().unwrap(), &mut 2);
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();
        list.push_front(1);
        list.push_back(2);

        let mut iter = list.into_iter();
        assert_eq!(Some(1), iter.next());
        assert_eq!(Some(2), iter.next_back());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
    }
}
