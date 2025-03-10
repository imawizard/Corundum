use crate::alloc::{MemPool, PoolGuard};
use crate::stm::Journal;
use crate::*;
use lib::cmp::*;
use lib::fmt::{Debug, Display, Formatter};
use lib::ops::Deref;
use lib::panic::RefUnwindSafe;
use lib::panic::UnwindSafe;
use lib::sync::Arc;

/// Root object container
///
/// The return value of pool's [`open()`] function is a `RootCell<T>` which
/// contains a reference to the root object of type `T` and a reference counting
/// object of pool type. When there is no more reference to the `RootCell`, it
/// closes the underlying pool.
///
/// The root object is immutable; modifications to the root object can be
/// provided via interior mutability.
///
/// [`open()`]: ../alloc/trait.MemPool.html#method.open
pub struct RootCell<'a, T: 'a, A: MemPool>(&'a T, Arc<PoolGuard<A>>);

impl<T: ?Sized, A: MemPool> !Sync for RootCell<'_, T, A> {}
unsafe impl<T: PSafe + Send, A: MemPool> Send for RootCell<'_, T, A> {}
unsafe impl<T: PSafe, A: MemPool> TxInSafe for RootCell<'_, T, A> {}
impl<T, A: MemPool> UnwindSafe for RootCell<'_, T, A> {}
impl<T, A: MemPool> RefUnwindSafe for RootCell<'_, T, A> {}
impl<T, A: MemPool> !TxOutSafe for RootCell<'_, T, A> {}
impl<T, A: MemPool> !PSafe for RootCell<'_, T, A> {}

impl<'a, T: 'a + PSafe, A: MemPool> RootCell<'a, T, A> {
    pub fn new(value: &'a T, pool: Arc<PoolGuard<A>>) -> Self {
        Self(value, pool)
    }

    pub fn strong_count(root: &Self) -> usize {
        Arc::strong_count(&root.1)
    }
}

impl<T: PSafe, A: MemPool> Clone for RootCell<'_, T, A> {
    fn clone(&self) -> Self {
        Self(self.0, self.1.clone())
    }
}

impl<T: Ord + PSafe, A: MemPool> Ord for RootCell<'_, T, A> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(&other.deref())
    }
}

impl<T: PSafe + PartialOrd, A: MemPool> PartialOrd for RootCell<'_, T, A> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.deref().partial_cmp(&other.deref())
    }
}

impl<T: PSafe + Eq, A: MemPool> Eq for RootCell<'_, T, A> {}

impl<T: PSafe + PartialEq, A: MemPool> PartialEq for RootCell<'_, T, A> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.deref().eq(other.deref())
    }
}

impl<T: PSafe, A: MemPool> Deref for RootCell<'_, T, A> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T: Debug + PSafe, A: MemPool> Debug for RootCell<'_, T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> lib::fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: Display + PSafe, A: MemPool> Display for RootCell<'_, T, A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> lib::fmt::Result {
        self.deref().fmt(f)
    }
}

/// Creates a default value of the type
///
/// The root type should implement this trait or trait [`Default`] to be able to
/// initialize the root object for the first time. Every type implementing
/// [`Default`] is already implementing `RootObj`, by default.
///
/// [`Default`]: std::default::Default
pub trait RootObj<A: MemPool> {
    fn init(journal: &Journal<A>) -> Self;
}

impl<T: Default, A: MemPool> RootObj<A> for T {
    default fn init(_journal: &Journal<A>) -> Self {
        T::default()
    }
}

impl<T: Default, A: MemPool> RootObj<A> for &[T] {
    default fn init(_journal: &Journal<A>) -> Self {
        <&[T]>::default()
    }
}

impl<T: RootObj<A>, A: MemPool> RootObj<A> for &[T] {
    default fn init(journal: &Journal<A>) -> Self {
        <&[T]>::init(journal)
    }
}

// impl<T: RootObj<A>, Q: RootObj<A>, A: MemPool> RootObj<A> for (T, Q) {
//     fn init(j: &Journal<A>) -> Self {
//         (T::init(j), Q::init(j))
//     }
// }

// use impl_trait_for_tuples::*;

// #[impl_for_tuples(32)]
// impl<A: MemPool> RootObj<A> for Tuple {
//     default fn init(j: &Journal<A>) -> Self {
//         for_tuples!( ( #( Tuple::init(j) ),* ) )
//     }
// }
