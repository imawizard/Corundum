use crate::alloc::MemPool;
use crate::cell::VCell;
use crate::ptr::Ptr;
use crate::stm::{Journal, Log, Logger, Notifier};
use crate::*;
use lib::cell::Cell;
use lib::cell::UnsafeCell;
use lib::marker::PhantomData;
use lib::ops::{Deref, DerefMut};
use lib::panic::{RefUnwindSafe, UnwindSafe};
use lib::sync::{TryLockError, TryLockResult};

#[allow(unused_imports)]
use lib::{fmt, intrinsics};

/// A transaction-wide recursive mutual exclusion primitive useful for
/// protecting shared data while transaction is open. Further locking in the
/// same thread is non-blocking. Any access to data is serialized. Borrow rules
/// are checked dynamically to prevent multiple mutable dereferencing.
///
/// This mutex will block threads/transactions waiting for the lock to become
/// available. The difference between `Mutex` and [`std`]`::`[`sync`]`::`[`Mutex`]
/// is that it will hold the lock until the transaction commits. For example,
/// consider the following code snippet in which a shared object is protected
/// with [`std`]`::`[`sync`]`::`[`Mutex`]. In this case, data might be lost.
///
/// ```compile_fail
/// use corundum::default::*;
/// use std::sync::Mutex;
///
/// type P = Allocator;
///
/// let obj = P::open::<Parc<Mutex<i32>>>("foo.pool", O_CF).unwrap();
/// //                       ^ std::sync::Mutex is not PSafe
///
/// transaction(|j| {
///     {
///         let obj = obj.lock().unwrap();
///         // Some statements ...
///     } // <-- release the lock here
///
///     // Another thread can work with obj
///
///     {
///         let obj = obj.lock().unwrap();
///         // Some statements ...
///     } // <-- release the lock here
///
///     // A crash may happen here after another thread has used updated data
///     // which leads to an inconsistent state
/// });
/// ```
///
/// The safest way to have a shared object protected from both data-race and
/// data-loss is to wrap it with a transaction-wide `Mutex` as in the following
/// example:
///
/// ```
/// use corundum::default::*;
///
/// type P = Allocator;
///
/// // PMutex<T> = corundum::sync::Mutex<T,P>
/// let obj = P::open::<Parc<PMutex<i32>>>("foo.pool", O_CF).unwrap();
///
/// transaction(|j| {
///     {
///         let obj = obj.lock(j);
///         // Some statements ...
///     }
///
///     // data is still locked.
///
///     {
///         let obj = obj.lock(j); // <-- does not block the current thread
///         // Some statements ...
///     }
///
/// }); // <-- release the lock here after committing or rolling back the transaction
/// ```
///
/// [`new`]: #method.new
/// [`lock`]: #method.lock
/// [`Mutex`]: std::sync::Mutex
/// [`sync`]: std::sync
/// [`std`]: std
///
pub struct PMutex<T, A: MemPool> {
    heap: PhantomData<A>,
    inner: VCell<MutexInner, A>,
    data: UnsafeCell<(u8, T)>,
}

struct MutexInner {
    borrowed: Cell<bool>,

    #[cfg(feature = "pthreads")]
    lock: (bool, libc::pthread_mutex_t, libc::pthread_mutexattr_t),

    #[cfg(not(feature = "pthreads"))]
    lock: (bool, u64),
}

impl Default for MutexInner {
    #[cfg(feature = "pthreads")]
    fn default() -> Self {
        use lib::mem::MaybeUninit;
        let mut attr = MaybeUninit::<libc::pthread_mutexattr_t>::uninit();
        let mut lock = libc::PTHREAD_MUTEX_INITIALIZER;
        unsafe {
            init_lock(&mut lock, attr.as_mut_ptr());
        }
        MutexInner {
            borrowed: Cell::new(false),
            lock: (false, lock, unsafe { attr.assume_init() }),
        }
    }

    #[cfg(not(feature = "pthreads"))]
    fn default() -> Self {
        MutexInner {
            borrowed: Cell::new(false),
            lock: (false, 0),
        }
    }
}

impl MutexInner {
    fn acquire(&self) -> bool {
        if self.borrowed.get() {
            false
        } else {
            self.borrowed.set(true);
            true
        }
    }

    fn release(&self) {
        self.borrowed.set(false);
    }
}

impl<T: ?Sized, A: MemPool> !TxOutSafe for PMutex<T, A> {}
impl<T, A: MemPool> UnwindSafe for PMutex<T, A> {}
impl<T, A: MemPool> RefUnwindSafe for PMutex<T, A> {}

unsafe impl<T, A: MemPool> TxInSafe for PMutex<T, A> {}
unsafe impl<T, A: MemPool> PSafe for PMutex<T, A> {}
unsafe impl<T: Send, A: MemPool> Send for PMutex<T, A> {}
unsafe impl<T: Send, A: MemPool> Sync for PMutex<T, A> {}
unsafe impl<T, A: MemPool> PSend for PMutex<T, A> {}

impl<T, A: MemPool> PMutex<T, A> {
    /// Creates a new `Mutex`
    ///
    /// # Examples
    ///
    /// ```
    /// # use corundum::alloc::heap::*;
    ///
    /// Heap::transaction(|j| {
    ///     let p = Parc::new(PMutex::new(10), j);
    /// }).unwrap();
    /// ```
    pub fn new(data: T) -> PMutex<T, A> {
        PMutex {
            heap: PhantomData,
            inner: VCell::new(MutexInner::default()),
            data: UnsafeCell::new((0, data)),
        }
    }
}

impl<T: PSafe, A: MemPool> PMutex<T, A> {
    #[inline]
    #[allow(clippy::mut_from_ref)]
    #[track_caller]
    /// Takes a log and returns a `&mut T` for interior mutability
    pub(crate) fn get_mut(&self, journal: &Journal<A>) -> &mut T {
        unsafe {
            let inner = &mut *self.data.get();
            if inner.0 == 0 {
                assert!(
                    A::valid(inner),
                    "The object is not in the pool's valid range"
                );
                inner
                    .1
                    .create_log(journal, Notifier::NonAtomic(Ptr::from_ref(&inner.0)));
            }
            &mut inner.1
        }
    }
}

impl<T, A: MemPool> PMutex<T, A> {
    #[inline]
    fn raw_lock(&self, journal: &Journal<A>) {
        unsafe {
            // Log::unlock_on_failure(self.inner.get(), journal);
            let lock = &self.inner.lock.1 as *const _ as *mut _;
            #[cfg(feature = "pthreads")]
            {
                libc::pthread_mutex_lock(lock);
            }
            #[cfg(not(feature = "pthreads"))]
            {
                let tid = lib::thread::current().id().as_u64().get();
                while intrinsics::atomic_cxchg_acqrel_acquire(lock, 0, tid).0 != tid {}
            }
            if self.inner.acquire() {
                Log::unlock_on_commit(&self.inner.lock as *const _ as u64, journal);
            } else {
                #[cfg(feature = "pthreads")]
                libc::pthread_mutex_unlock(lock);

                #[cfg(not(feature = "pthreads"))]
                intrinsics::atomic_store_release(lock, 0);

                panic!("Cannot have multiple instances of MutexGuard");
            }
        }
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to
    /// acquire the mutex. Upon returning, the thread is the only thread with
    /// the lock held. An RAII guard is returned to keep track of borrowing
    /// data. It creates an [`UnlockOnCommit`] log to unlock the mutex when
    /// transaction is done.
    ///
    /// If the local thread already holds the lock, `lock()` does not block it.
    /// The mutex remains locked until the transaction is committed.
    /// Alternatively, [`PMutex`] can be used as a compact form of `Mutex`.
    ///
    /// # Examples
    ///
    /// ```
    /// use corundum::default::*;
    /// use std::thread;
    ///
    /// type P = Allocator;
    ///
    /// let obj = P::open::<Parc<PMutex<i32>>>("foo.pool", O_CF).unwrap();
    ///
    /// // Using short forms in the pool module, there is no need to specify the
    /// // pool type, as follows:
    /// // let obj = P::open::<Parc<PMutex<i32>>>("foo.pool", O_CF).unwrap();
    ///
    /// let obj = Parc::demote(&obj);
    /// thread::spawn(move || {
    ///     transaction(move |j| {
    ///         if let Some(obj) = obj.promote(j) {
    ///             *obj.lock(j) += 1;
    ///         }
    ///     }).unwrap();
    /// }).join().expect("thread::spawn failed");
    /// ```
    ///
    /// [`PMutex`]: ../default/type.PMutex.html
    /// [`UnlockOnCommit`]: ../stm/enum.LogEnum.html#variant.UnlockOnCommit
    ///
    pub fn lock<'a>(&'a self, journal: &'a Journal<A>) -> MutexGuard<'a, T, A> {
        self.raw_lock(journal);
        unsafe { MutexGuard::new(self, journal) }
    }

    #[inline]
    fn raw_trylock(&self, journal: &Journal<A>) -> bool {
        unsafe {
            let lock = &self.inner.lock.1 as *const _ as *mut _;

            #[cfg(feature = "pthreads")]
            let result = libc::pthread_mutex_trylock(lock) == 0;

            #[cfg(not(feature = "pthreads"))]
            let result = {
                let tid = lib::thread::current().id().as_u64().get();
                intrinsics::atomic_cxchg_acqrel_acquire(lock, 0, tid).0 == tid
            };

            if result {
                if self.inner.acquire() {
                    Log::unlock_on_commit(&self.inner.lock as *const _ as u64, journal);
                    true
                } else {
                    #[cfg(feature = "pthreads")]
                    libc::pthread_mutex_unlock(lock);

                    #[cfg(not(feature = "pthreads"))]
                    intrinsics::atomic_store_release(lock, 0);

                    panic!("Cannot have multiple instances of MutexGuard");
                }
            } else {
                false
            }
        }
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then [`Err`] is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// owner transaction ends.
    ///
    /// This function does not block.
    ///
    /// # Errors
    ///
    /// If another user of this mutex holds a guard, then this call will return
    /// failure if the mutex would otherwise be acquired.
    ///
    /// # Examples
    ///
    /// ```
    /// use corundum::default::*;
    /// use std::thread;
    ///
    /// type P = Allocator;
    ///
    /// let obj = P::open::<Parc<PMutex<i32>>>("foo.pool", O_CF).unwrap();
    ///
    /// let a = Parc::demote(&obj);
    /// thread::spawn(move || {
    ///     transaction(|j| {
    ///         if let Some(obj) = a.promote(j) {
    ///             let mut lock = obj.try_lock(j);
    ///             if let Ok(ref mut mutex) = lock {
    ///                 **mutex = 10;
    ///             } else {
    ///                 println!("try_lock failed");
    ///             }
    ///         }
    ///     }).unwrap();
    /// }).join().expect("thread::spawn failed");
    ///
    /// transaction(|j| {
    ///     assert_eq!(*obj.lock(j), 10);
    /// }).unwrap();
    /// ```
    ///
    /// [`PMutex`]: ../default/type.PMutex.html
    pub fn try_lock<'a>(&'a self, journal: &'a Journal<A>) -> TryLockResult<MutexGuard<'a, T, A>> {
        if self.raw_trylock(journal) {
            unsafe { Ok(MutexGuard::new(self, journal)) }
        } else {
            Err(TryLockError::WouldBlock)
        }
    }
}

impl<T: RootObj<A>, A: MemPool> RootObj<A> for PMutex<T, A> {
    fn init(journal: &Journal<A>) -> Self {
        PMutex::new(T::init(journal))
    }
}

impl<T: fmt::Debug, A: MemPool> fmt::Debug for PMutex<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data.fmt(f)
    }
}

pub struct MutexGuard<'a, T: 'a, A: MemPool> {
    lock: &'a PMutex<T, A>,
    journal: *const Journal<A>,
}

impl<T: ?Sized, A: MemPool> !TxOutSafe for MutexGuard<'_, T, A> {}
impl<T: ?Sized, A: MemPool> !Send for MutexGuard<'_, T, A> {}
unsafe impl<T: Sync, A: MemPool> Sync for MutexGuard<'_, T, A> {}

impl<T: fmt::Debug, A: MemPool> fmt::Debug for MutexGuard<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: fmt::Display, A: MemPool> fmt::Display for MutexGuard<'_, T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<'mutex, T, A: MemPool> MutexGuard<'mutex, T, A> {
    unsafe fn new(
        lock: &'mutex PMutex<T, A>,
        journal: &'mutex Journal<A>,
    ) -> MutexGuard<'mutex, T, A> {
        MutexGuard { lock, journal }
    }
}

impl<T, A: MemPool> Deref for MutexGuard<'_, T, A> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &(*self.lock.data.get()).1 }
    }
}

impl<T: PSafe, A: MemPool> DerefMut for MutexGuard<'_, T, A> {
    #[track_caller]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.lock.get_mut(&*self.journal) }
    }
}

impl<T, A: MemPool> Drop for MutexGuard<'_, T, A> {
    fn drop(&mut self) {
        self.lock.inner.release()
    }
}

#[cfg(feature = "pthreads")]
pub unsafe fn init_lock(mutex: *mut libc::pthread_mutex_t, attr: *mut libc::pthread_mutexattr_t) {
    *mutex = libc::PTHREAD_MUTEX_INITIALIZER;
    let result = libc::pthread_mutexattr_init(attr);
    debug_assert_eq!(result, 0);
    let result = libc::pthread_mutexattr_settype(attr, libc::PTHREAD_MUTEX_RECURSIVE);
    debug_assert_eq!(result, 0);
    let result = libc::pthread_mutex_init(mutex, attr);
    debug_assert_eq!(result, 0);
    let result = libc::pthread_mutexattr_destroy(attr);
    debug_assert_eq!(result, 0);
}
