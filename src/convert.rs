use crate::alloc::MemPool;
use crate::stm::Journal;

/// An equivalent to [`From`] for persistent memory which requires a [`Journal`]
/// to operate
///
/// [`Journal`]: ../stm/journal/struct.Journal.html
pub trait PFrom<T, A: MemPool> {
    fn pfrom(_: T, j: &Journal<A>) -> Self;
}
