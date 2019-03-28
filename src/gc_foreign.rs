//! Wrappers around foreign types so that they work with the gc.

// use std::borrow::Borrow;

use im_rc;
use gc::{Trace, Finalize, custom_trace};

/// A garbage-collectable `im_rc::Vector`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Vector<T: Clone>(pub im_rc::Vector<T>);

impl<T: Trace + Clone> Finalize for Vector<T> {}
unsafe impl<T: Trace + Clone> Trace for Vector<T> {
    custom_trace!(this, {
        for e in this.0.iter() {
            mark(e);
        }
    });
}

impl<T: Clone> Vector<T> {
    pub fn new() -> Vector<T> {
        Vector(im_rc::Vector::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn push_back(&mut self, value: T) {
        self.0.push_back(value)
    }
}

// /// A garbage-collectable `im_rc::OrdMap`.
// #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
// pub struct OrdMap<K: Clone + Ord, V: Clone>(pub im_rc::OrdMap<K, V>);
//
// impl<K: Trace + Clone + Ord, V: Trace + Clone> Finalize for OrdMap<K, V> {}
// unsafe impl<K: Trace + Clone + Ord, V: Trace + Clone> Trace for OrdMap<K, V> {
//     custom_trace!(this, {
//         for e in this.0.iter() {
//             mark(e);
//         }
//     });
// }
//
// impl<K: Ord + Clone, V: Clone> OrdMap<K, V> {
//     pub fn new() -> OrdMap<K, V> {
//         OrdMap(im_rc::OrdMap::new())
//     }
//
//     pub fn get<BK>(&self, key: &BK) -> Option<&V>
//     where
//         BK: Ord + ?Sized,
//         K: Borrow<BK>,
//     {
//         self.0.get(key)
//     }
//
//     #[must_use]
//     pub fn update(&self, key: K, value: V) -> Self {
//         OrdMap(self.0.update(key, value))
//     }
// }
