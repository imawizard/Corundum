//! *Corundum* is a crate with an idiomatic persistent memory programming
//! interface and leverages Rust’s type system to statically avoid
//! most common persistent memory programming bugs. Corundum lets programmers
//! develop persistent data structures using familiar Rust constructs and have
//! confidence that they will be free of those bugs.
//!
//! # Statically Prevented Bugs
//! |     Common Bugs     | Explanation  <img width=700/> | Approach |
//! |         ---         |              ---              |    ---   |
//! | Inter-Pool Pointers | A pointer in another pool which is unavailable | Type checking pools in persistent pointers. |
//! | P-to-V Pointers     | A persistent pointer pointing at volatile memory | Persistent pointers accept only [`PSafe`] types and volatile pointers are `!PSafe`. Only, [`VCell`] allows single-execution P-to-V pointers. |
//! | V-to-P Pointers     | A volatile pointer keeping a zero-referenced object alive | Only [`VWeak`] allows V-to-P pointers which is a weak reference and does not keep data alive. |
//! | Unlogged Updates    | An unrecoverable update to persistent data | Modifications are enforced to be inside atomic [`transaction`]s. |
//! | Data Race           | Updating persistent data simultaneously in two threads | Mutable borrowing is limited to [`PMutex`] which uses a transaction-wide lock to provide both atomicity and isolation. |
//! | Locked Mutex        | A persistent mutex remains locked on powerfail | [`PMutex`] uses [`VCell`] which resets at restart. |
//! | Memory Leaks\*      | An allocated memory becomes unreachable | Persistent objects, except the root object, cannot cross transaction boundaries, and memory allocation is available only inside a transaction. Therefore, the allocation can survive only if there is a reference from the root object (or a decedent of it) to the data. <br>\* Cyclic references are not prevented in this version, which lead to a memory leak. Please visit [`this link`] for the information on how to manually resolve that issue. |
//!
//! For more technical details on the implementation, please refer to Corundum's
//! academic [paper] and/or watch the [presentation] 📺.
//!
//! [presentation]: https://www.youtube.com/watch?v=yTk7e_3ZEzk
//! [paper]: http://cseweb.ucsd.edu/~mhoseinzadeh/hoseinzadeh-corundum-asplos21.pdf
//! [`this link`]: ./prc/index.html#cyclic-references
//!
//! # Persistent Objects
//!
//! Persistent objects in Corundum are available through persistent pointers:
//! * [`Pbox`]: A pointer type for persistent memory allocation.
//! * [`Prc`]: A single-threaded reference-counting persistent pointer.
//! * [`Parc`]: A thread-safe reference-counting persistent pointer.
//!
//! # Programming Model
//! Persistent memory is available as a file on a DAX-enable file system such as
//! EXT4-DAX or NOVA. These files are called memory pools. Corundum allows
//! memory pool types rather than memory pool objects to enforce pointer safety
//! while compilation. The trait [`MemPool`] provides the necessary
//! functionalities for the pool type.
//!
//! The first step is to open a memory pool file in the program to be able to
//! work with persistent data. The [`default`] module provides a default memory
//! pool type ([`Allocator`]). To open a pool, we can invoke [`open<T>()`]
//! function which [initializes and] returns a reference to the root object of
//! type `T`.
//!
//! Data modification is provided and allowed only through [`transaction`]al
//! interface. None of the persistent pointers is mutably dereferencing for
//! safety. Mutable objects are allowed via interior mutability of any of the
//! following memory cells:
//!
//! * [`PCell<T,P>`] (or [`PCell<T>`]): An unborrowable, mutable persistent
//! memory location for a value of type `T` in pool `P`.
//! * [`PRefCell<T,P>`] (or [`PRefCell<T>`]): A mutable persistent memory location
//! with dynamically checked borrow rules for a value of type `T` in pool `P`.
//! * [`PMutex<T,P>`] (or [`PMutex<T>`]): A mutual exclusion primitive useful for
//! protecting shared persistent data of type `T` in pool `P`.
//!
//! The following example creates a pool file for a linked-list-based stack, and
//! obtains the root object of type `Node`.
//!
//! ```
//! use corundum::default::*;
//!
//! // Aliasing the pool type for convenience
//! type P = Allocator;
//!
//! #[derive(Root)]
//! struct Node {
//!     value: i32,
//!     next: PRefCell<Option<Prc<Node>>>
//! }
//!
//! fn main() {
//!     let head = P::open::<Node>("foo.pool", O_CF).unwrap();
//!
//!     P::transaction(|j| {
//!         let mut h = head.next.borrow_mut(j);
//!         *h = Some(Prc::new(Node {
//!             value: rand::random(),
//!             next: head.next.pclone(j)
//!         }, j));
//!     }).expect("Unsuccessful transaction");
//! }
//! ```
//!
//! [`PSafe`]: ./trait.PSafe.html
//! [`VCell`]: ./cell/struct.VCell.html
//! [`VWeak`]: ./prc/struct.VWeak.html
//! [`transaction`]:  ./alloc/trait.MemPool.html#method.transaction
//! [`PMutex`]: ./sync/struct.PMutex.html
//! [`Pbox`]: ./boxed/struct.Pbox.html
//! [`Prc`]: ./prc/struct.Prc.html
//! [`Parc`]: ./sync/struct.Parc.html
//! [`MemPool`]: ./alloc/trait.MemPool.html
//! [`default`]: ./alloc/default/index.html
//! [`Allocator`]: ./alloc/default/struct.Allocator.html
//! [`PCell<T,P>`]: ./cell/struct.PCell.html
//! [`PCell<T>`]: ./alloc/default/type.PCell.html
//! [`PRefCell<T,P>`]: ./cell/struct.PRefCell.html
//! [`PRefCell<T>`]: ./alloc/default/type.PRefCell.html
//! [`PMutex<T,P>`]: ./sync/struct.PMutex.html
//! [`PMutex<T>`]: ./alloc/default/type.PMutex.html
//! [`open<T>()`]: ./alloc/struct.MemPool.html#method.open

#![cfg_attr(not(feature = "std"), no_std)]
#![feature(auto_traits)]
#![feature(specialization)]
#![feature(concat_idents)]
#![feature(core_intrinsics)]
// FIXME: needed for std, "unknown feature" when no_std.
// #![cfg_attr(not(feature = "std"), feature(thread_id_value))]
// doesn't work either.
//#![feature(thread_id_value)]
#![feature(negative_impls)]
#![feature(trusted_len)]
#![feature(exact_size_is_empty)]
#![feature(alloc_layout_extra)]
#![feature(dropck_eyepatch)]
#![feature(trivial_bounds)]
#![feature(stmt_expr_attributes)]
#![feature(trait_alias)]
#![feature(slice_concat_trait)]
#![feature(slice_partition_dedup)]
#![feature(type_name_of_val)]
#![feature(pattern)]
#![feature(str_internals)]
#![feature(fn_traits)]
#![feature(unboxed_closures)]
#![feature(let_chains)]
#![feature(c_variadic)]
#![feature(rustc_attrs)]
#![feature(allocator_api)]
#![feature(associated_type_bounds)]
// #![feature(async_stream)]
#![allow(dead_code)]
#![allow(incomplete_features)]
#![allow(type_alias_bounds)]
#![feature(prelude_import)]

#[cfg(all(feature = "std", feature = "no_std"))]
compile_error!("Cannot use both std and no_std");

pub(crate) const PAGE_LOG_SLOTS: usize = 128;

pub mod gen;
pub mod ll;
pub mod prc;
pub mod ptr;
pub mod stat;
#[cfg(feature = "std")]
pub mod stl;
pub mod stm;
pub mod sync;
pub mod utils;

mod alloc;
mod boxed;
mod cell;
mod clone;
mod convert;
mod marker;
mod str;
mod tests;
pub mod vec;

pub use self::str::{String as PString, ToPString, ToPStringSlice};
pub use alloc::*;
pub use boxed::*;
pub use cell::RootObj;
pub use cell::*;
pub use clone::*;
pub use convert::*;
#[cfg(feature = "derive")]
pub use crndm_derive::*;
pub use marker::*;
pub use prc::Prc;
pub use stm::transaction;
pub use stm::Journal;
pub use sync::{PMutex, Parc};
pub use vec::Vec as PVec;

// This is an example of defining a new buddy allocator type
// `Allocator` is the default allocator with Buddy Allocation algorithm
crate::pool!(default);

/// A `Result` type with string error messages
pub mod result {
    pub type Result<T: ?Sized> = lib::result::Result<T, lib::string::String>;
}

#[cfg(not(feature = "std"))]
extern crate alloc as stdalloc;

#[prelude_import]
#[allow(unused_imports)]
use crate::prelude::*;

#[doc(hidden)]
pub mod prelude {
    pub use crate::lib;
    pub use core::prelude::rust_2021::*;

    pub use lib::borrow::ToOwned;
    pub use lib::boxed::Box;
    pub use lib::string::{String, ToString};
    pub use lib::vec::Vec;
    pub use lib::{eprintln, format, print, println, vec};
}

#[doc(hidden)]
pub mod lib {
    #[cfg(feature = "std")]
    mod core {
        pub use std::*;
    }

    #[cfg(not(feature = "std"))]
    mod core {
        pub use core::*;

        pub use stdalloc::{alloc, borrow, boxed, format, rc, string, string::String, vec};

        pub mod collections {
            pub use stdalloc::collections::{BTreeMap as HashMap, BTreeSet as HashSet, *};

            pub mod hash_map {
                pub use super::HashMap;
                pub use siphasher::sip::SipHasher as DefaultHasher;
            }
        }

        pub mod env {
            #[derive(Debug)]
            pub struct OsStr;

            impl OsStr {
                pub fn into_string(self) -> Result<super::String, Self> {
                    Err(self)
                }
            }

            pub fn var(_key: &str) -> Result<super::String, ()> {
                Err(())
            }

            pub fn var_os(_key: &str) -> Option<OsStr> {
                None
            }
        }

        pub mod fs {
            use lib::ffi::{c_void, CString};
            use lib::io::{Error, ErrorKind, Result, Write};

            #[derive(Default)]
            pub struct OpenOptions {
                create: bool,
                truncate: bool,
            }

            impl OpenOptions {
                pub fn new() -> Self {
                    OpenOptions {
                        ..Default::default()
                    }
                }

                pub fn create(&mut self, create: bool) -> &mut Self {
                    self.create = create;
                    self
                }

                pub fn truncate(&mut self, truncate: bool) -> &mut Self {
                    self.truncate = truncate;
                    self
                }

                pub fn read(&mut self, _read: bool) -> &mut Self {
                    self
                }

                pub fn write(&mut self, _write: bool) -> &mut Self {
                    self
                }

                pub fn open(&self, path: &str) -> Result<File> {
                    let filename = CString::new(path).map_err(|_| Error::from(ErrorKind::Other))?;
                    let mode = CString::new(if self.create && self.truncate {
                        "bw+"
                    } else if !self.create && !self.truncate {
                        "br+"
                    } else {
                        "ba+"
                        // rewind(file)
                    })
                    .unwrap();

                    Ok(File {
                        inner: unsafe { ffi::fopen(filename.as_ptr(), mode.as_ptr()) },
                        filename: filename,
                    })
                }
            }

            pub struct File {
                inner: *const c_void,
                pub(crate) filename: CString,
            }

            impl File {
                pub fn options() -> OpenOptions {
                    OpenOptions::new()
                }

                pub fn metadata(&self) -> Result<Metadata> {
                    Ok(Metadata {
                        filename: self.filename.clone(),
                    })
                }

                pub fn set_len(&self, size: u64) -> Result<()> {
                    if unsafe { ffi::truncate(self.filename.as_ptr(), size) } == size {
                        Ok(())
                    } else {
                        Err(Error::from(ErrorKind::Other))
                    }
                }
            }

            impl Drop for File {
                fn drop(&mut self) {
                    unsafe { ffi::fclose(self.inner) }
                }
            }

            impl Write for File {
                fn write(&mut self, data: &[u8]) -> Result<usize> {
                    Ok(unsafe {
                        ffi::fwrite(data.as_ptr() as *const c_void, 1, data.len(), self.inner)
                    })
                }

                fn write_all(&mut self, data: &[u8]) -> Result<()> {
                    if self.write(data)? == data.len() {
                        Ok(())
                    } else {
                        Err(Error::from(ErrorKind::Other))
                    }
                }
            }

            pub struct Metadata {
                filename: CString,
            }

            impl Metadata {
                pub fn is_file(&self) -> bool {
                    true
                }

                pub fn len(&self) -> u64 {
                    unsafe { ffi::size(self.filename.as_ptr()) }
                }
            }

            pub fn metadata(path: &str) -> Result<Metadata> {
                OpenOptions::new().open(path).and_then(|f| f.metadata())
            }

            pub fn remove_file(path: &str) -> Result<()> {
                let filename = match CString::new(path) {
                    Ok(res) => res,
                    Err(_) => return Err(Error::from(ErrorKind::Other)),
                };

                if unsafe { ffi::remove(filename.as_ptr()) } == 0 {
                    Ok(())
                } else {
                    Err(Error::from(ErrorKind::Other))
                }
            }

            pub mod ffi {
                use lib::ffi::{c_char, c_int, c_ulonglong, c_void};

                extern "C" {
                    pub fn fopen(filename: *const c_char, mode: *const c_char) -> *const c_void;
                    pub fn fwrite(
                        buf: *const c_void,
                        size: usize,
                        count: usize,
                        file: *const c_void,
                    ) -> usize;
                    pub fn fclose(file: *const c_void);
                    pub fn remove(filename: *const c_char) -> c_int;
                    pub fn truncate(filename: *const c_char, length: c_ulonglong) -> c_ulonglong;
                    pub fn size(filename: *const c_char) -> c_ulonglong;
                }
            }
        }

        pub mod io {
            use core::{fmt, result};

            pub type Result<T> = result::Result<T, Error>;

            #[derive(Debug)]
            pub struct Error;

            pub enum ErrorKind {
                Other,
            }

            impl Error {
                pub fn from(_kind: ErrorKind) -> Self {
                    Error
                }

                pub fn last_os_error() -> Error {
                    Error
                }
            }

            impl fmt::Display for Error {
                fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {
                    Ok(())
                }
            }

            pub trait Read {}
            pub trait Write {
                fn write(&mut self, data: &[u8]) -> Result<usize>;
                fn write_all(&mut self, data: &[u8]) -> Result<()>;
            }
        }

        pub mod panic {
            pub use core::panic::*;

            pub fn catch_unwind<F: FnOnce() -> R + UnwindSafe, R>(f: F) -> Result<R, ()> {
                Ok(f())
            }
        }

        pub mod path {
            use core::ops;
            use core::ptr;
            use lib::ffi::{c_char, CString};
            use lib::fs::ffi;

            #[repr(transparent)]
            pub struct Path {
                inner: str,
            }

            impl Path {
                pub fn new(s: &str) -> &Path {
                    unsafe { &*(s as *const str as *const Path) }
                }

                pub fn exists(&self) -> bool {
                    let filename = match CString::new(&self.inner) {
                        Ok(res) => res,
                        Err(_) => return false,
                    };

                    let file =
                        unsafe { ffi::fopen(filename.as_ptr(), "r\0".as_ptr() as *const c_char) };
                    if file != ptr::null() {
                        unsafe { ffi::fclose(file) };
                        true
                    } else {
                        false
                    }
                }
            }

            impl ops::Deref for Path {
                type Target = str;

                #[inline]
                fn deref(&self) -> &str {
                    &self.inner
                }
            }

            pub struct PathBuf(String);

            impl PathBuf {
                pub fn new() -> Self {
                    PathBuf(String::new())
                }
            }

            impl From<&str> for PathBuf {
                fn from(value: &str) -> Self {
                    PathBuf(String::from(value))
                }
            }

            impl ops::Deref for PathBuf {
                type Target = Path;

                #[inline]
                fn deref(&self) -> &Path {
                    Path::new(&self.0.as_ref())
                }
            }
        }

        pub mod process {
            pub fn exit(code: i32) -> ! {
                println!("exitcode: {}", code);
                loop {}
            }

            pub fn abort() -> ! {
                eprintln!("abort");
                loop {}
            }
        }

        pub mod sync {
            pub use core::sync::*;
            pub use stdalloc::sync::Arc;

            pub struct Mutex<T>(spin::Mutex<T>);

            pub struct PoisonError<T>(T);

            impl<T> Mutex<T> {
                pub fn new(t: T) -> Mutex<T> {
                    Mutex(spin::Mutex::new(t))
                }

                pub fn lock(
                    &self,
                ) -> Result<spin::MutexGuard<T>, PoisonError<spin::MutexGuard<T>>> {
                    Ok(self.0.lock())
                }
            }

            impl<T> PoisonError<T> {
                pub fn into_inner(self) -> T {
                    self.0
                }
            }

            pub enum TryLockError<T> {
                Poisoned(PoisonError<T>),
                WouldBlock,
            }

            pub type TryLockResult<Guard> = Result<Guard, TryLockError<Guard>>;
        }

        pub mod thread {
            use core::marker::PhantomData;
            use core::num::NonZeroU64;

            pub struct Thread;

            #[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Copy, Debug)]
            pub struct ThreadId {
                inner: NonZeroU64,
            }

            struct JoinInner<T> {
                thread: Thread,
                phantom: PhantomData<T>,
            }

            pub struct JoinHandle<T>(JoinInner<T>);

            pub fn current() -> Thread {
                Thread
            }

            impl Thread {
                pub fn id(&self) -> ThreadId {
                    ThreadId {
                        inner: unsafe { NonZeroU64::new_unchecked(1) },
                    }
                }
            }

            impl ThreadId {
                pub fn as_u64(&self) -> NonZeroU64 {
                    self.inner
                }
            }

            pub fn panicking() -> bool {
                false
            }
        }

        pub mod time {
            pub use core::time::*;

            pub struct Instant {
                t: u64,
            }

            impl Instant {
                pub fn now() -> Instant {
                    Instant { t: 0 }
                }

                pub fn elapsed(&mut self) -> Duration {
                    Duration::new(0, 0)
                }
            }
        }

        #[macro_export]
        macro_rules! println {
            () => { $crate::lib::println!("") };
            ($($arg:tt)*) => {
                let mes = format!("{}\0", format_args!($($arg)*));
                #[allow(unused_unsafe)]
                unsafe { $crate::lib::ffi::puts(mes.as_ptr() as *const $crate::lib::ffi::c_char) }
            };
        }

        #[macro_export]
        macro_rules! eprintln {
            () => { $crate::lib::eprintln!("") };
            ($($arg:tt)*) => {
                let mes = format!("{}\0", format_args!($($arg)*));
                #[allow(unused_unsafe)]
                unsafe { $crate::lib::ffi::perror(mes.as_ptr() as *const $crate::lib::ffi::c_char) }
            };
        }

        #[macro_export]
        macro_rules! print {
            ($($arg:tt)*) => {{
                let mes = format!("{}", format_args!($($arg)*));
                for ch in mes.bytes().into_iter() {
                    #[allow(unused_unsafe)]
                    unsafe { $crate::lib::ffi::putchar(ch as $crate::lib::ffi::c_int) };
                }
            }};
        }

        pub use {eprintln, print, println};

        pub mod ffi {
            pub use core::ffi::*;
            pub use stdalloc::ffi::CString;

            extern "C" {
                pub fn putchar(ch: c_int) -> c_int;
                pub fn puts(s: *const c_char) -> c_int;
                pub fn perror(s: *const c_char);
            }
        }
    }

    pub use self::core::*;
}

#[cfg(feature = "std")]
pub mod memmap {
    pub use ::memmap::*;
}

#[cfg(not(feature = "std"))]
pub mod memmap {
    use lib::ffi::c_void;
    use lib::fs::File;
    use lib::io::*;
    use lib::ops;
    use lib::ptr;

    #[derive(Debug)]
    pub struct MmapOptions {}

    impl MmapOptions {
        pub fn new() -> Self {
            MmapOptions {}
        }

        pub unsafe fn map_mut(&self, file: &File) -> Result<MmapMut> {
            let addr = unsafe { ffi::map(file.filename.as_ptr()) };
            let size = file.metadata().unwrap().len();

            if addr != ptr::null_mut() {
                Ok(MmapMut {
                    address: addr as u64,
                    size,
                })
            } else {
                Err(Error::from(ErrorKind::Other))
            }
        }
    }

    #[derive(Debug)]
    pub struct MmapMut {
        address: u64,
        size: u64,
    }

    impl MmapMut {
        pub fn flush(&self) -> Result<()> {
            Ok(())
        }
    }

    impl ops::Drop for MmapMut {
        fn drop(&mut self) {
            unsafe { ffi::unmap(self.address as *mut c_void) };
        }
    }

    impl ops::Deref for MmapMut {
        type Target = [u8];

        #[inline]
        fn deref(&self) -> &[u8] {
            unsafe { lib::slice::from_raw_parts(self.address as *const u8, self.size as usize) }
        }
    }

    impl ops::DerefMut for MmapMut {
        #[inline]
        fn deref_mut(&mut self) -> &mut [u8] {
            unsafe { lib::slice::from_raw_parts_mut(self.address as *mut u8, self.size as usize) }
        }
    }

    mod ffi {
        use lib::ffi::{c_char, c_int, c_void};

        extern "C" {
            pub fn map(filename: *const c_char) -> *mut c_void;
            pub fn unmap(addr: *mut c_void) -> c_int;
        }
    }
}

#[cfg(not(feature = "std"))]
mod pmem {
    pub fn create(name: &str, size: u64) -> u64 {
        unsafe { ffi::pmem_create(name.as_ptr(), name.len(), size) }
    }

    pub fn destroy(name: &str) -> bool {
        unsafe { ffi::pmem_destroy(name.as_ptr(), name.len()) }
    }

    pub fn get(name: &str) -> Option<ffi::Pmem> {
        let res = unsafe { ffi::pmem_get(name.as_ptr(), name.len()) };

        if res.address != 0 {
            Some(res)
        } else {
            None
        }
    }

    pub fn set_len(name: &str, size: u64) -> u64 {
        unsafe { ffi::pmem_set_len(name.as_ptr(), name.len(), size) }
    }

    mod ffi {
        #[repr(C, packed)]
        pub struct Pmem {
            pub address: u64,
            pub size: u64,
        }

        extern "C" {
            pub fn pmem_create(name: *const u8, name_len: usize, size: u64) -> u64;
            pub fn pmem_destroy(name: *const u8, name_len: usize) -> bool;
            pub fn pmem_get(name: *const u8, name_len: usize) -> Pmem;
            pub fn pmem_set_len(name: *const u8, name_len: usize, size: u64) -> u64;
        }
    }
}
