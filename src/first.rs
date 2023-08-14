use std::mem;

pub struct List {
    head: Link,
}

struct Node {
    val: i32,
    link: Link,
}

enum Link {
    Empty,
    More(Box<Node>),
}

impl List {
    pub fn new() -> Self {
        List { head: Link::Empty }
    }

    pub fn push(&mut self, val: i32) {
        let new_node = Node {
            val,
            link: mem::replace(&mut self.head, Link::Empty),
        };
        self.head = Link::More(Box::new(new_node));
    }

    pub fn pop(&mut self) -> Option<i32> {
        match mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(n) => {
                self.head = n.link;
                Some(n.val)
            }
        }
    }
}

impl Default for List {
    fn default() -> Self {
        Self::new()
    }
}

// Default Drop impl would delete nodes recursively, since Node has to
// be dropped before Box<Node> is deallocated. To avoid unbounded
// recursion, implement iterative Drop.
impl Drop for List {
    fn drop(&mut self) {
        let mut next = mem::replace(&mut self.head, Link::Empty);

        while let Link::More(mut n) = next {
            next = mem::replace(&mut n.link, Link::Empty);
            // n will be dropped, which is a Box<Node> where Node's
            // link is Empty, so there won't be any recursion.
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
}
