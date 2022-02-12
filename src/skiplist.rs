use std::borrow::Borrow;
use std::cmp::Ordering::*;
use std::ptr;

use rand_distr::{Bernoulli, Distribution};

const SKIPLIST_HEIGHT: usize = 16;
struct LinkedList<K, V> {
    head: Link<K, V>,
}

type Link<K, V> = *mut Node<K, V>;

impl<K, V> LinkedList<K, V> {
    fn new() -> Self {
        Self {
            head: ptr::null_mut(),
        }
    }
}
struct Node<K, V> {
    next: [Link<K, V>; SKIPLIST_HEIGHT],
    key: K,
    value: V,
}

impl<K, V> Node<K, V> {
    fn new(key: K, value: V) -> Self {
        Self {
            next: [ptr::null_mut(); SKIPLIST_HEIGHT],
            key,
            value,
        }
    }
}

pub struct SkipList<K, V> {
    lists: Vec<LinkedList<K, V>>,
    len: usize,
}

impl<K, V> SkipList<K, V>
where
    K: Ord ,
{
    pub fn new() -> Self {
        let mut lists = Vec::with_capacity(SKIPLIST_HEIGHT);
        for _ in 0..SKIPLIST_HEIGHT {
            lists.push(LinkedList::new());
        }
        Self {
            lists,
            len: 0,
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        let mut to_update: [Link<K, V>; SKIPLIST_HEIGHT] = [ptr::null_mut(); SKIPLIST_HEIGHT];
        let mut current_node: Link<K, V> = ptr::null_mut();
        for level in (0..SKIPLIST_HEIGHT).rev() {
            if current_node.is_null() {
                if self.lists[level].head.is_null() {
                    continue;
                }
                current_node = self.lists[level].head;
            }
            unsafe {
                match (*current_node).key.cmp(&key) {
                    Equal => {
                        (*current_node).value = value;
                        return;
                    }
                    Greater => continue,
                    _ => {}
                }
                let mut next_node = (*current_node).next[level];
                if next_node.is_null() {
                    to_update[level] = current_node;
                    continue;
                }
                loop {
                    match (*next_node).key.cmp(&key) {
                        Less => {
                            let temp = (*next_node).next[level];
                            if !temp.is_null() {
                                current_node = next_node;
                                next_node = temp;
                            } else {
                                to_update[level] = next_node;
                                break;
                            }
                        }
                        Equal => {
                            (*next_node).value = value;
                            return;
                        }
                        Greater => {
                            if !current_node.is_null() {
                                to_update[level] = current_node;
                            }
                            break;
                        }
                    }
                }
            }
        }
        let node_to_insert = Box::into_raw(Box::new(Node::new(key, value)));
        let height = random_height();
        for (h, node) in to_update.into_iter().enumerate().take(height) {
            if node.is_null() {
                if self.lists[h].head.is_null() {
                    self.lists[h].head = node_to_insert;
                } else {
                    unsafe {
                        (*node_to_insert).next[h] = self.lists[h].head;
                    }
                    self.lists[h].head = node_to_insert;
                }
            } else {
                unsafe {
                    let next_node = (*node).next[h];
                    (*node_to_insert).next[h] = next_node;
                    (*node).next[h] = node_to_insert;
                }
            }
        }
        self.len += 1;
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut current_node: Link<K, V> = ptr::null_mut();
        for level in (0..SKIPLIST_HEIGHT).rev() {
            if current_node.is_null() {
                if self.lists[level].head.is_null() {
                    continue;
                }
                current_node = self.lists[level].head;
            }
            unsafe {
                match (*current_node).key.borrow().cmp(key) {
                    Equal => {
                        return Some(&(*current_node).value);
                    }
                    Greater => {
                        current_node = ptr::null_mut();
                        continue
                    },
                    _ => {}
                }
                let mut next_node = (*current_node).next[level];
                if next_node.is_null() {
                    continue;
                }
                loop {
                    match (*next_node).key.borrow().cmp(key) {
                        Less => {
                            let temp = (*next_node).next[level];
                            if !temp.is_null() {
                                current_node = next_node;
                                next_node = temp;
                            } else {
                                break;
                            }
                        }
                        Equal => return Some(&(*next_node).value),
                        Greater => {
                            break;
                        }
                    }
                }
            }
        }
        None
    }

    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    fn find_ge<Q>(&self, key: &Q) -> Link<K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut current_node: Link<K, V> = ptr::null_mut();
        for level in (0..SKIPLIST_HEIGHT).rev() {
            if current_node.is_null() {
                if self.lists[level].head.is_null() {
                    continue;
                }
                current_node = self.lists[level].head;
            }
            unsafe {
                match (*current_node).key.borrow().cmp(key) {
                    Equal => {
                        return current_node;
                    }
                    Greater => {
                        if level == 0 {
                            return current_node;
                        }
                        current_node = ptr::null_mut();
                        continue
                    }
                    _ => {}
                }
                let mut next_node = (*current_node).next[level];
                if next_node.is_null() {
                    continue;
                }
                loop {
                    match (*next_node).key.borrow().cmp(key) {
                        Less => {
                            let temp = (*next_node).next[level];
                            if !temp.is_null() {
                                current_node = next_node;
                                next_node = temp;
                            } else {
                                break;
                            }
                        }
                        Equal => return next_node,
                        Greater => {
                            if level == 0 {
                                return next_node;
                            }
                            break;
                        }
                    }
                }
            }
        }
        ptr::null_mut()
    }

    pub fn range_iter<'a, Q>(&self, start: &'a Q, end: &'a Q) -> RangeIter<'a, K, V, Q>
    where
        K: Borrow<Q>,
        Q: Ord,
    {
        let next = self.find_ge(start);
        RangeIter { end, next }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K, V> Default for SkipList<K, V>
where
    K: Ord ,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for SkipList<K, V> {
    fn drop(&mut self) {
        let mut node = self.lists[0].head;
        while !node.is_null() {
            unsafe {
                let next = (*node).next[0];
                let _temp = Box::from_raw(node);
                node = next;
            }
        }
    }
}

pub struct RangeIter<'a, K, V, Q> {
    end: &'a Q,
    next: Link<K, V>,
}

impl<'a, K: 'a + Ord + Borrow<Q>, V: 'a, Q: Ord> Iterator for RangeIter<'a, K, V, Q> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> where {
        if self.next.is_null() {
            None
        } else {
            unsafe {
                let current_node = self.next;
                let next = (*current_node).next[0];
                if !next.is_null() {
                    match (*next).key.borrow().cmp(self.end) {
                        Less => self.next = next,
                        Equal | Greater => self.next = ptr::null_mut(),
                    }
                } else {
                    self.next = ptr::null_mut();
                }
                let k = &(*current_node).key;
                let v = &(*current_node).value;
                Some((k, v))
            }
        }
    }
}

fn random_height() -> usize {
    let bin = Bernoulli::new(0.5).unwrap();
    let mut rng = rand::thread_rng();
    let mut height = 1;
    loop {
        if bin.sample(&mut rng) && height < SKIPLIST_HEIGHT {
            height += 1
        } else {
            break;
        }
    }
    height
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_insert() {
        let mut skiplist = SkipList::new();
        skiplist.insert("foo".to_string(), "bar".to_string());
        skiplist.insert("bar".to_string(), "baz".to_string());
        skiplist.insert("hello".to_string(), "there".to_string());
        assert_eq!(skiplist.len(), 3);
        unsafe {
            let ptr = skiplist.lists[0].head;
            assert!(!ptr.is_null());
            println!("{}", (*ptr).key);
            assert_eq!((*ptr).key, "bar");
            assert_eq!((*ptr).value, "baz");
            let ptr = (*ptr).next[0];
            assert!(!ptr.is_null());
            println!("{}", (*ptr).key);
            assert_eq!((*ptr).key, "foo");
            assert_eq!((*ptr).value, "bar");
            let ptr = (*ptr).next[0];
            assert!(!ptr.is_null());
            println!("{}", (*ptr).key);
            assert_eq!((*ptr).key, "hello");
            assert_eq!((*ptr).value, "there");
        }
    }

    #[test]
    fn test_get() {
        let mut skiplist = SkipList::new();
        skiplist.insert("foo".to_string(), "bar".to_string());
        skiplist.insert("bar".to_string(), "baz".to_string());
        skiplist.insert("hello".to_string(), "there".to_string());
        assert_eq!(skiplist.get("foo"), Some(&"bar".to_string()));
        assert_eq!(skiplist.get("bar"), Some(&"baz".to_string()));
        assert_eq!(skiplist.get("hello"), Some(&"there".to_string()));
    }

    #[test]
    fn test_contains() {
        let mut skiplist = SkipList::new();
        skiplist.insert("foo".to_string(), "bar".to_string());
        skiplist.insert("bar".to_string(), "baz".to_string());
        skiplist.insert("hello".to_string(), "there".to_string());
        assert!(skiplist.contains("foo"));
        assert!(skiplist.contains("bar"));
        assert!(skiplist.contains("hello"));
    }

    #[test]
    fn test_range_iter_full() {
        let mut skiplist = SkipList::new();
        skiplist.insert(1, 2);
        skiplist.insert(2, 3);
        skiplist.insert(3, 4);
        let mut iter = skiplist.range_iter(&0, &4);
        assert_eq!(iter.next(), Some((&1, &2)));
        assert_eq!(iter.next(), Some((&2, &3)));
        assert_eq!(iter.next(), Some((&3, &4)));
    }

    #[test]
    fn test_range_iter_limited() {
        let mut skiplist = SkipList::new();
        skiplist.insert(1, 2);
        skiplist.insert(2, 3);
        skiplist.insert(3, 4);
        let mut iter = skiplist.range_iter(&1, &3);
        assert_eq!(iter.next(), Some((&1, &2)));
        assert_eq!(iter.next(), Some((&2, &3)));
        assert_eq!(iter.next(), None);
    }
}
