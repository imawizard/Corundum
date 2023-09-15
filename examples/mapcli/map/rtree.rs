use crate::map::Map;
use corundum::default::*;

use std::{cell::RefCell, collections::BTreeMap};

type P = Allocator;

pub struct RTree<K, V> {
    btree: RefCell<BTreeMap<K, V>>,
}

impl<K, V: Copy> Map<K, V> for RTree<K, V>
where
    K: std::cmp::Ord,
{
    fn clear(&self) {
        self.btree.borrow_mut().clear();
    }
    fn insert(&self, key: K, val: V) {
        self.btree.borrow_mut().insert(key, val);
    }
    fn remove(&self, key: K) {
        self.btree.borrow_mut().remove(&key);
    }
    fn is_empty(&self) -> bool {
        self.btree.borrow().is_empty()
    }
    fn foreach<F: Copy + Fn(&K, &V) -> bool>(&self, f: F) -> bool {
        for (k, v) in self.btree.borrow().iter() {
            f(k, v);
        }
        true
    }
    fn lookup(&self, key: K) -> bool {
        self.btree.borrow().get(&key).is_some()
    }
}

impl<K: std::cmp::Ord, V> Default for RTree<K, V> {
    fn default() -> Self {
        Self {
            btree: RefCell::new(BTreeMap::new()),
        }
    }
}
