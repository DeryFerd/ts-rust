//! Port of Go `core/binarysearch.go`.

use crate::frontend::prelude::*;

// Go: core/binarysearch.go:8 BinarySearchUniqueFunc
/// BinarySearchUniqueFunc works like [slices.BinarySearchFunc], but avoids extra
/// invocations of the comparison function by assuming that only one element
/// in the slice could match the target. Also, unlike [slices.BinarySearchFunc],
/// the comparison function is passed the current index of the element being
/// compared, instead of the target element.
// PORT: Go `int` indexes are `i32` (PORTING `int` -> `i32`). Go passes the
// element by value; here it is cloned (`E: Clone`), which is a plain copy for
// the `Node` and integer slices that the callers search.
pub fn binary_search_unique_func<E: Clone>(
    x: &[E],
    mut cmp: impl FnMut(i32, E) -> i32,
) -> (i32, bool) {
    let n = x.len() as i32;
    if n == 0 {
        return (0, false);
    }
    let (mut low, mut high) = (0i32, n - 1);
    while low <= high {
        let middle = low + ((high - low) >> 1);
        let value = cmp(middle, x[middle as usize].clone());
        if value < 0 {
            low = middle + 1;
        } else if value > 0 {
            high = middle - 1;
        } else {
            return (middle, true);
        }
    }
    (low, false)
}
