//! Go `internal/core` helpers that the language service needs:
//! core/core.go `MapNonNil`, `FirstNonZero`, `MinAllFunc`, `DiffMaps`,
//! `DiffMapsFunc`, `CopyMapInto`, `UnorderedEqual`, `CompareBooleans`;
//! core/typeacquisition.go `TypeAcquisition.Equals`; and
//! collections/ordered_map.go `DiffOrderedMaps`, `DiffOrderedMapsFunc`.

use crate::frontend::prelude::*;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};

// PORT: Go `==` on a `comparable` value. Go compares pointers by address, so
// `Rc` compares with `Rc::ptr_eq` (map-project decision 2), while strings,
// numbers and handles compare by value. `DiffMaps` and `DiffOrderedMaps`
// use it for their values.
pub trait GoComparable {
    fn go_eq(&self, other: &Self) -> bool;
}

macro_rules! go_comparable_by_value {
    ($($t:ty),* $(,)?) => {
        $(
            impl GoComparable for $t {
                fn go_eq(&self, other: &Self) -> bool {
                    self == other
                }
            }
        )*
    };
}

go_comparable_by_value!(
    bool,
    i32,
    i64,
    u32,
    u64,
    usize,
    (),
    String,
    &str,
    crate::frontend::tspath::Path,
    crate::core::Node,
    crate::core::SymbolId,
    crate::core::TypeId,
);

impl<T: ?Sized> GoComparable for Rc<T> {
    fn go_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(self, other)
    }
}

impl<T: GoComparable> GoComparable for Option<T> {
    fn go_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(a), Some(b)) => a.go_eq(b),
            _ => false,
        }
    }
}

// PORT: read access to a Go `map[K]V`. Go has one map type; Rust callers
// hold `FxHashMap` / `HashMap` or `IndexMap` (PORTING "Types"), or
// `Option<..>` with `None` for a nil map. The map helpers below take any of
// them.
pub trait GoMap<K, V> {
    fn go_get(&self, key: &K) -> Option<&V>;
    fn go_range(&self, f: &mut dyn FnMut(&K, &V));
}

impl<K: Eq + Hash, V, S: BuildHasher> GoMap<K, V> for HashMap<K, V, S> {
    fn go_get(&self, key: &K) -> Option<&V> {
        self.get(key)
    }

    fn go_range(&self, f: &mut dyn FnMut(&K, &V)) {
        for (k, v) in self {
            f(k, v);
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> GoMap<K, V> for IndexMap<K, V, S> {
    fn go_get(&self, key: &K) -> Option<&V> {
        self.get(key)
    }

    fn go_range(&self, f: &mut dyn FnMut(&K, &V)) {
        for (k, v) in self {
            f(k, v);
        }
    }
}

impl<K, V, M: GoMap<K, V>> GoMap<K, V> for Option<M> {
    fn go_get(&self, key: &K) -> Option<&V> {
        match self {
            Some(m) => m.go_get(key),
            None => None,
        }
    }

    fn go_range(&self, f: &mut dyn FnMut(&K, &V)) {
        if let Some(m) = self {
            m.go_range(f);
        }
    }
}

// Go: core/core.go:117 MapNonNil
// PORT: Go keeps each result that is not the zero value of `U`. Every Go
// caller maps to a pointer, so `f` returns `Option<U>` and `None` is nil
// (handles: `.get()`). Go returns a nil slice when nothing is kept; the port
// returns an empty `Vec`.
pub fn map_non_nil<T, U>(
    slice: impl IntoIterator<Item = T>,
    mut f: impl FnMut(T) -> Option<U>,
) -> Vec<U> {
    let mut result = Vec::new();
    for value in slice {
        let mapped = f(value);
        if let Some(mapped) = mapped {
            result.push(mapped);
        }
    }
    result
}

// Go: core/core.go:297 FirstNonZero
// PORT: the Go zero value is `T::default()`.
pub fn first_non_zero<T: Default + PartialEq>(values: impl IntoIterator<Item = T>) -> T {
    let zero = T::default();
    for value in values {
        if value != zero {
            return value;
        }
    }
    zero
}

// Go: core/core.go:359 MinAllFunc
// MinAllFunc returns all minimum elements from xs according to the comparison function cmp.
pub fn min_all_func<T: Clone>(xs: &[T], mut cmp: impl FnMut(&T, &T) -> i32) -> Vec<T> {
    if xs.is_empty() {
        return Vec::new();
    }

    let mut m = xs[0].clone();
    let mut mins = vec![m.clone()];

    for x in &xs[1..] {
        let c = cmp(x, &m);
        if c < 0 {
            m = x.clone();
            mins.clear();
            mins.push(x.clone());
        } else if c == 0 {
            mins.push(x.clone());
        }
    }

    mins
}

// Go: core/core.go:726 comparableValuesEqual
pub fn comparable_values_equal<T: GoComparable>(a: &T, b: &T) -> bool {
    a.go_eq(b)
}

// Go: core/core.go:734 DiffMaps
// DiffMaps compares two maps m1 and m2 and calls the provided callbacks for added, removed, and changed entries.
// onAdded is called for each key-value pair that is in m2 but not in m1.
// onRemoved is called for each key-value pair that is in m1 but not in m2.
// onChanged is called for each key where the value in m1 differs from the value in m2.
pub fn diff_maps<K, V: GoComparable>(
    m1: &dyn GoMap<K, V>,
    m2: &dyn GoMap<K, V>,
    on_added: Option<&mut dyn FnMut(&K, &V)>,
    on_removed: Option<&mut dyn FnMut(&K, &V)>,
    on_changed: Option<&mut dyn FnMut(&K, &V, &V)>,
) {
    diff_maps_func(
        m1,
        m2,
        comparable_values_equal::<V>,
        on_added,
        on_removed,
        on_changed,
    );
}

// Go: core/core.go:742 DiffMapsFunc
// DiffMapsFunc compares two maps m1 and m2 and calls the provided callbacks for added, removed, and changed entries.
// onAdded is called for each key-value pair that is in m2 but not in m1.
// onRemoved is called for each key-value pair that is in m1 but not in m2.
// onChanged is called for each key where the value in m1 differs from the value in m2.
// PORT: nil callbacks are `None`. The callbacks can not change `m1` or `m2`
// while they are borrowed. Iteration follows the Rust map order (PORT: Go
// map order is random).
pub fn diff_maps_func<K, V1, V2>(
    m1: &dyn GoMap<K, V1>,
    m2: &dyn GoMap<K, V2>,
    mut equal_values: impl FnMut(&V1, &V2) -> bool,
    mut on_added: Option<&mut dyn FnMut(&K, &V2)>,
    mut on_removed: Option<&mut dyn FnMut(&K, &V1)>,
    mut on_changed: Option<&mut dyn FnMut(&K, &V1, &V2)>,
) {
    if let Some(on_added) = on_added.as_mut() {
        m2.go_range(&mut |k, v2| {
            if m1.go_get(k).is_none() {
                on_added(k, v2);
            }
        });
    }
    if on_changed.is_none() && on_removed.is_none() {
        return;
    }
    m1.go_range(&mut |k, v1| {
        if let Some(v2) = m2.go_get(k) {
            if let Some(on_changed) = on_changed.as_mut() {
                if !equal_values(v1, v2) {
                    on_changed(k, v1, v2);
                }
            }
        } else {
            // PORT: Go calls onRemoved here even when it is nil, which panics.
            let on_removed = on_removed
                .as_mut()
                .expect("nil pointer dereference: onRemoved");
            on_removed(k, v1);
        }
    });
}

// Go: core/core.go:766 CopyMapInto
// CopyMapInto is maps.Copy, unless dst is nil, in which case it clones and returns src.
// Use CopyMapInto anywhere you would use maps.Copy preceded by a nil check and map initialization.
// PORT: a nil `dst` is `None`. `M` is any owned map or set (`FxHashMap`,
// `FxHashSet` for Go `map[K]struct{}`, `IndexMap`, ...).
pub fn copy_map_into<M>(dst: Option<M>, src: &M) -> M
where
    M: Clone + IntoIterator + Extend<<M as IntoIterator>::Item>,
{
    match dst {
        None => src.clone(),
        Some(mut dst) => {
            // Go: maps.Copy(dst, src)
            dst.extend(src.clone());
            dst
        }
    }
}

// Go: core/core.go:775 UnorderedEqual
// UnorderedEqual returns true if s1 and s2 contain the same elements, regardless of order.
pub fn unordered_equal<T: Eq + Hash>(s1: &[T], s2: &[T]) -> bool {
    if s1.len() != s2.len() {
        return false;
    }
    let mut counts: FxHashMap<&T, i32> = FxHashMap::default();
    for v in s1 {
        *counts.entry(v).or_insert(0) += 1;
    }
    for v in s2 {
        let count = counts.entry(v).or_insert(0);
        *count -= 1;
        if *count < 0 {
            return false;
        }
    }
    true
}

// Go: core/core.go:830 CompareBooleans
// CompareBooleans treats true as greater than false.
pub fn compare_booleans(a: bool, b: bool) -> i32 {
    if a && !b {
        return 1;
    } else if !a && b {
        return -1;
    }
    0
}

impl crate::frontend::core_ext::TypeAcquisition {
    // Go: core/typeacquisition.go:12 Equals
    // PORT: Go has a nil-able pointer receiver and argument, so both are
    // `Option` (as PORTING maps `(v *X) resolve()` to
    // `X::resolve(v: Option<&X>)`). Call it as
    // `TypeAcquisition::equals(a.as_ref(), b.as_ref())`.
    pub fn equals(ta: Option<&Self>, other: Option<&Self>) -> bool {
        // Go: if ta == other (pointer compare)
        match (ta, other) {
            (None, None) => return true,
            (Some(a), Some(b)) if std::ptr::eq(a, b) => return true,
            _ => {}
        }
        let (Some(ta), Some(other)) = (ta, other) else {
            return false;
        };

        // Go: slices.Equal treats nil and empty slices as equal, as `Vec` `==` does.
        ta.enable == other.enable
            && ta.include == other.include
            && ta.exclude == other.exclude
            && ta.disable_filename_based_type_acquisition
                == other.disable_filename_based_type_acquisition
    }
}

// Go: collections/ordered_map.go:295 DiffOrderedMaps
// PORT: Go `*OrderedMap` is `IndexMap`. Values compare with Go `==`
// (`GoComparable`: `Rc` by pointer).
pub fn diff_ordered_maps<K: Eq + Hash, V: GoComparable, S: BuildHasher>(
    m1: &IndexMap<K, V, S>,
    m2: &IndexMap<K, V, S>,
    on_added: impl FnMut(&K, &V),
    on_removed: impl FnMut(&K, &V),
    on_modified: impl FnMut(&K, &V, &V),
) {
    diff_ordered_maps_func(m1, m2, |a, b| a.go_eq(b), on_added, on_removed, on_modified);
}

// Go: collections/ordered_map.go:301 DiffOrderedMapsFunc
// PORT: the callbacks can not change `m1` or `m2` while they are borrowed,
// so the Go re-read of the key count on each step changes nothing.
pub fn diff_ordered_maps_func<K: Eq + Hash, V, S: BuildHasher>(
    m1: &IndexMap<K, V, S>,
    m2: &IndexMap<K, V, S>,
    mut equal_values: impl FnMut(&V, &V) -> bool,
    mut on_added: impl FnMut(&K, &V),
    mut on_removed: impl FnMut(&K, &V),
    mut on_modified: impl FnMut(&K, &V, &V),
) {
    for (k, v2) in m2 {
        if m1.get(k).is_none() {
            on_added(k, v2);
        }
    }
    for (k, v1) in m1 {
        if let Some(v2) = m2.get(k) {
            if !equal_values(v1, v2) {
                on_modified(k, v1, v2);
            }
        } else {
            on_removed(k, v1);
        }
    }
}
