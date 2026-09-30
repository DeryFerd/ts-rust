//! Rust-only: the leaked bump arena of a thread, in fixed-size chunks.
//!
//! PERF (rss2): the AST arena (`ast/store.rs`) and the checker arena
//! (`checker/types.rs`) were one `bumpalo::Bump` per thread, with a 1 MiB
//! first chunk. A `Bump` doubles its chunk size each time it grows, so the
//! last chunk of a thread was up to half empty: 1 MiB at the start, then 2,
//! 4 and 8 MiB. Memory that is allocated but never written costs no RSS on
//! 4 KiB pages, but jemalloc gives the heap huge pages (`JEMALLOC_CONF` in
//! `bin/tsgo.rs`), and a huge page is resident as soon as one byte of it is
//! written. That empty tail was 6 MiB of query's peak RSS and 20 MiB of zod's.
//!
//! A `LeakArena` holds one `Bump` of `CHUNK` bytes at a time. Its allocation
//! limit stops it from growing: an allocation that does not fit fails in the
//! `Bump` slow path, and the cold path here leaks a new `Bump` and uses that
//! one. So a thread leaves at most one chunk less than full, and the fast
//! path is the same pointer bump as before.

use bumpalo::Bump;
use std::alloc::Layout;
use std::cell::Cell;
use std::mem::MaybeUninit;

/// The size of each chunk. A thread wastes less than one chunk; a larger
/// chunk costs fewer mallocs (effect: about 800 at 128 KiB).
const CHUNK: usize = 128 << 10;

/// The room to ask of a `Bump` for a malloc block of `CHUNK` bytes: it adds
/// its footer and rounds the block up to whole pages.
const CHUNK_ROOM: usize = CHUNK - 256;

/// A value larger than this does not start a new shared chunk when the
/// current one is full: it gets a chunk of its own, and the current chunk
/// stays in use. So a large value does not throw away the free end of the
/// current chunk.
const OWN_CHUNK_MIN: usize = CHUNK / 4;

/// The leaked bump arena of one thread. Keep it in a thread local as a
/// `&'static LeakArena` (`LeakArena::leak`), so only the reference comes out
/// of `LocalKey::with` and a value is not copied through its closure.
pub struct LeakArena {
    /// The chunk that new values go in.
    current: Cell<&'static Bump>,
}

impl LeakArena {
    /// A new leaked arena with one empty chunk.
    pub fn leak() -> &'static LeakArena {
        Box::leak(Box::new(LeakArena {
            current: Cell::new(new_chunk(CHUNK_ROOM)),
        }))
    }

    /// Puts the value that `make` returns in the arena. `make` runs after
    /// the slot is ready, so a large value is built straight in its slot.
    #[inline(always)]
    pub fn alloc_with<T>(&self, make: impl FnOnce() -> T) -> &'static mut T {
        let slot = match self.current.get().try_alloc_with(MaybeUninit::<T>::uninit) {
            Ok(slot) => slot,
            Err(_) => self.slow_alloc_uninit::<T>(),
        };
        slot.write(make())
    }

    /// Moves `value` into the arena.
    #[inline(always)]
    pub fn alloc<T>(&self, value: T) -> &'static mut T {
        self.alloc_with(move || value)
    }

    /// A copy of `items` in the arena.
    #[inline]
    pub fn alloc_slice_copy<T: Copy>(&self, items: &[T]) -> &'static mut [T] {
        match self.current.get().try_alloc_slice_copy(items) {
            Ok(slice) => slice,
            Err(_) => self
                .chunk_for(Layout::for_value(items))
                .alloc_slice_copy(items),
        }
    }

    /// A slice of the `len` items that `items` yields, in the arena. `items`
    /// runs once, in order.
    #[inline]
    pub fn alloc_slice_fill_iter<T>(
        &self,
        len: usize,
        items: impl Iterator<Item = T>,
    ) -> &'static mut [T] {
        let layout = Layout::array::<T>(len).expect("arena slice size");
        // The check comes before the iterator runs, so a full chunk does not
        // drop items that were already made.
        let bump = if self.current.get().chunk_capacity() >= layout.size() + layout.align() {
            self.current.get()
        } else {
            self.chunk_for(layout)
        };
        let mut items = items;
        let slice = bump.alloc_slice_fill_with(len, |_| {
            items.next().expect("arena slice iterator ended early")
        });
        debug_assert!(items.next().is_none(), "arena slice iterator is longer");
        slice
    }

    /// The slot of a `T` that did not fit in the current chunk.
    #[cold]
    #[inline(never)]
    fn slow_alloc_uninit<T>(&self) -> &'static mut MaybeUninit<T> {
        self.chunk_for(Layout::new::<T>())
            .alloc_with(MaybeUninit::<T>::uninit)
    }

    /// A chunk with room for `layout`: a new current chunk, or a chunk of its
    /// own for a large value (`OWN_CHUNK_MIN`).
    #[cold]
    #[inline(never)]
    fn chunk_for(&self, layout: Layout) -> &'static Bump {
        let need = layout.size() + layout.align();
        if layout.size() > OWN_CHUNK_MIN {
            return new_chunk(need);
        }
        let chunk = new_chunk(CHUNK_ROOM.max(need));
        self.current.set(chunk);
        chunk
    }
}

/// A leaked `Bump` with one chunk of at least `capacity` bytes, which never
/// makes another chunk: its allocation limit is the size of that chunk, so
/// an allocation that does not fit fails instead.
fn new_chunk(capacity: usize) -> &'static Bump {
    let bump = Box::leak(Box::new(Bump::with_capacity(capacity)));
    bump.set_allocation_limit(Some(bump.allocated_bytes()));
    bump
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Values fill a chunk, then go on in a new chunk of the same size; a
    /// large value gets a chunk of its own and the current chunk stays.
    #[test]
    fn chunks_stay_fixed_size() {
        let arena = LeakArena::leak();
        let first = arena.current.get();
        assert!(first.allocated_bytes() <= CHUNK);
        let mut values = Vec::new();
        while std::ptr::eq(arena.current.get(), first) {
            assert!(values.len() <= CHUNK / 64, "the first chunk grew");
            values.push(&*arena.alloc([values.len() as u64; 8]));
        }
        assert!(values.iter().enumerate().all(|(i, v)| v[0] == i as u64));
        let second = arena.current.get();
        assert_eq!(second.allocated_bytes(), first.allocated_bytes());

        let big = arena.alloc_slice_copy(&vec![7u8; CHUNK]);
        assert_eq!(big.len(), CHUNK);
        assert!(std::ptr::eq(arena.current.get(), second));

        let small = arena.alloc_slice_fill_iter(3, [1u32, 2, 3].into_iter());
        assert_eq!(small, &[1, 2, 3]);
    }
}
