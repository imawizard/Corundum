use crate::alloc::MemPool;
use crate::stm::Journal;
use crate::RootObj;
use crate::{PSafe, VSafe};
use lib::cell::UnsafeCell;
use lib::cmp::*;
use lib::fmt::{self, Debug};
use lib::marker::PhantomData;
use lib::mem::*;
use lib::ops::{Deref, DerefMut};

/// A persistent memory location containing a volatile data valid during a
/// single transaction
///
/// The underlying data is valid throughout of the course of a single
/// transaction scope. When the transaction is finished, the data is back to its
/// default value. Type `T` in `TCell<T>` should implement [`Default`] and
/// [`VSafe`].
///
/// # Examples
///
/// ```
/// use corundum::default::*;
/// use std::cell::RefCell;
///
/// type P = Allocator;
///
/// #[derive(Root)]
/// struct Root {
///     v: TCell<RefCell<i32>>
/// }
///
/// let root = P::open::<Root>("foo.pool", O_CF).unwrap();
///
/// P::transaction(|j| {
///   let mut v = root.v.borrow_mut();
///   assert_eq!(*v, i32::default());
///   *v = 20; // This value is volatile and resets when transaction is complete
///   assert_eq!(*v, 20);
/// }).unwrap();
///
/// let v = root.v.borrow();
/// assert_eq!(*v, i32::default()); // It contains the default value outside the transaction
/// ```
///
/// [`Default`]: std::default::Default
/// [`VSafe`]: ../trait.VSafe.html
pub struct TCell<T: Default + VSafe + ?Sized, A: MemPool> {
    gen: u32,
    tx_gen: u32,
    phantom: PhantomData<(A, T)>,
    value: UnsafeCell<T>,
}

/// Not Safe to transfer between thread boundaries
impl<T, A> !Send for TCell<T, A> {}

/// Not Safe to be shared between threads
impl<T, A> !Sync for TCell<T, A> {}

/// Safe to be stored in persistent memory
unsafe impl<T: Default + VSafe + ?Sized, A: MemPool> PSafe for TCell<T, A> {}

impl<T: Default + Debug + VSafe + ?Sized, A: MemPool> Debug for TCell<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{:?}", self.deref())
    }
}

impl<T: Default + VSafe, A: MemPool> TCell<T, A> {
    /// Create a new valid cell
    pub fn new(v: T, j: &Journal<A>) -> Self {
        Self {
            gen: A::gen(),
            tx_gen: j.gen(),
            value: UnsafeCell::new(v),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn as_mut(&self) -> &mut T {
        unsafe { &mut *self.value.get() }
    }

    #[inline]
    /// Create a new invalid cell to be used in const functions
    pub const fn new_invalid(v: T) -> Self {
        Self {
            gen: 0,
            tx_gen: 0,
            value: UnsafeCell::new(v),
            phantom: PhantomData,
        }
    }

    #[inline]
    /// Invalidates the underlying value
    pub fn invalidate(this: &mut Self) {
        this.gen = 0;
    }

    fn force(&mut self) -> &mut T {
        let gen = A::gen();
        unsafe {
            if let Some((j, _)) = Journal::<A>::current(false) {
                let j = &*j;
                let tx_gen = j.gen();
                if self.gen != gen || self.tx_gen != tx_gen {
                    forget(replace(&mut self.value, UnsafeCell::new(T::default())));
                    self.gen = gen;
                    self.tx_gen = tx_gen;
                }
            } else {
                forget(replace(&mut self.value, UnsafeCell::new(T::default())));
                self.gen = gen;
            }
        }
        self.value.get_mut()
    }
}

impl<T: Default + VSafe, A: MemPool> RootObj<A> for TCell<T, A> {
    fn init(j: &Journal<A>) -> Self {
        Self {
            gen: A::gen(),
            tx_gen: j.gen(),
            value: UnsafeCell::new(T::default()),
            phantom: PhantomData,
        }
    }
}

impl<T: Default + VSafe, A: MemPool> Deref for TCell<T, A> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*self.value.get() }
    }
}

impl<T: Default + VSafe, A: MemPool> DerefMut for TCell<T, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.force()
    }
}

impl<T: Default + VSafe + PartialEq + Copy, A: MemPool> PartialEq for TCell<T, A> {
    #[inline]
    fn eq(&self, other: &TCell<T, A>) -> bool {
        unsafe { *self.value.get() == *other.value.get() }
    }
}

impl<T: Default + VSafe + Eq + Copy, A: MemPool> Eq for TCell<T, A> {}

impl<T: Default + VSafe + PartialOrd + Copy, A: MemPool> PartialOrd for TCell<T, A> {
    #[inline]
    fn partial_cmp(&self, other: &TCell<T, A>) -> Option<Ordering> {
        unsafe { (*self.value.get()).partial_cmp(&*other.value.get()) }
    }

    #[inline]
    fn lt(&self, other: &TCell<T, A>) -> bool {
        unsafe { *self.value.get() < *other.value.get() }
    }

    #[inline]
    fn le(&self, other: &TCell<T, A>) -> bool {
        unsafe { *self.value.get() <= *other.value.get() }
    }

    #[inline]
    fn gt(&self, other: &TCell<T, A>) -> bool {
        unsafe { *self.value.get() > *other.value.get() }
    }

    #[inline]
    fn ge(&self, other: &TCell<T, A>) -> bool {
        unsafe { *self.value.get() >= *other.value.get() }
    }
}

impl<T: Default + VSafe + Ord + Copy, A: MemPool> Ord for TCell<T, A> {
    #[inline]
    fn cmp(&self, other: &TCell<T, A>) -> Ordering {
        self.value.get().cmp(&other.value.get())
    }
}

impl<T: Default + VSafe + PartialEq + Copy, A: MemPool> PartialEq<T> for TCell<T, A> {
    #[inline]
    fn eq(&self, other: &T) -> bool {
        unsafe { *self.value.get() == *other }
    }
}

impl<T: Default + VSafe + PartialOrd + Copy, A: MemPool> PartialOrd<T> for TCell<T, A> {
    #[inline]
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        unsafe { (*self.value.get()).partial_cmp(&other) }
    }

    #[inline]
    fn lt(&self, other: &T) -> bool {
        unsafe { *self.value.get() < *other }
    }

    #[inline]
    fn le(&self, other: &T) -> bool {
        unsafe { *self.value.get() <= *other }
    }

    #[inline]
    fn gt(&self, other: &T) -> bool {
        unsafe { *self.value.get() > *other }
    }

    #[inline]
    fn ge(&self, other: &T) -> bool {
        unsafe { *self.value.get() >= *other }
    }
}
