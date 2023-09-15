pub struct List<T> {
    head: Link<T>,
}

struct Node<T> {
    val: T,
    next: Link<T>,
}

type Link<T> = Option<Box<Node<T>>>;

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: None }
    }

    pub fn push(&mut self, val: T) {
        let new_node = Node {
            val,
            next: self.head.take(),
        };
        self.head = Some(Box::new(new_node));
    }

    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.val
        })
    }

    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.val)
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.val)
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
        self.next.take().map(|node| {
            self.next = node.next.as_deref();
            &node.val
        })
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_deref_mut();
            &mut node.val
        })
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            next: self.head.as_deref(),
        }
    }
}

impl<'a, T> IntoIterator for &'a mut List<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            next: self.head.as_deref_mut(),
        }
    }
}

impl<T> Default for List<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Default Drop impl would delete nodes recursively, since Node has to
// be dropped before Box<Node> is deallocated. To avoid unbounded
// recursion, implement iterative Drop.
impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut next = self.head.take();

        while let Some(mut n) = next {
            next = n.next.take();
            // n will be dropped, which is a Box<Node> where Node's
            // next is Empty, so there won't be any recursion.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::List;

    #[test]
    fn basic() {
        let mut list = List::new();

        // empty list pop
        assert_eq!(None, list.pop());

        // push a few elems
        list.push(1);
        list.push(2);
        list.push(3);

        // pop some
        assert_eq!(Some(3), list.pop());
        assert_eq!(Some(2), list.pop());

        // push one more
        list.push(4);

        // pop all
        assert_eq!(Some(4), list.pop());
        assert_eq!(Some(1), list.pop());
    }

    #[test]
    fn peek() {
        let mut list = List::new();

        assert_eq!(None, list.peek());
        assert_eq!(None, list.peek_mut());

        list.push("a");
        list.push("b");

        assert_eq!(Some(&"b"), list.peek());
        assert_eq!(Some(&mut "b"), list.peek_mut());

        if let Some(val) = list.peek_mut() {
            *val = "c";
        }
        assert_eq!(Some(&"c"), list.peek());
        assert_eq!(Some(&mut "c"), list.peek_mut());

        assert_eq!(Some("c"), list.pop());
    }

    #[test]
    fn into_iter() {
        let mut list = List::new();
        list.push(3);
        list.push(2);
        list.push(1);

        let mut iter = (&list).into_iter();
        assert_eq!(Some(&1), iter.next());
        assert_eq!(Some(&2), iter.next());
        assert_eq!(Some(&3), iter.next());
        assert_eq!(None, iter.next());

        let mut iter = list.into_iter();
        assert_eq!(Some(1), iter.next());
        assert_eq!(Some(2), iter.next());
        assert_eq!(Some(3), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn iter() {
        let mut list = List::new();
        list.push(42);

        let mut iter = list.iter();
        assert_eq!(Some(&42), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn iter_mut() {
        let mut list = List::new();
        list.push(1);
        list.push(2);

        let mut iter = list.iter_mut();
        assert_eq!(Some(&mut 2), iter.next());
        assert_eq!(Some(&mut 1), iter.next());
        assert_eq!(None, iter.next());
    }
}
