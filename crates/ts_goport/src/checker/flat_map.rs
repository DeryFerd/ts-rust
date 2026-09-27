//! PORT: perf. Not in Go. A small open-addressing hash map for hot checker
//! caches (`Relation::results`, `InferenceState::visited`, `InferenceStack::top`).
//!
//! All slots are `(key, value)` pairs in one array, with linear probing and a
//! power-of-two capacity. A probe reads the key from the same cache line as
//! its value; hashbrown reads a control group first and then the slot, which
//! costs one more cache miss on a large table.
//!
//! `K::default()` marks an empty slot. A real key equal to `K::default()` is
//! kept in a side slot. `remove` uses backward-shift deletion, so the map
//! never needs tombstones. There is no iteration, so its layout cannot change
//! any output.
//!
//! The API is the subset of `std::collections::HashMap` that the users need,
//! with the same signatures, so a type alias can switch a map back to
//! hashbrown for an A/B run.

/// A key for `FlatMap`. `flat_hash` must be well mixed in its low bits,
/// because the table index is `flat_hash() & (capacity - 1)`.
pub trait FlatKey: Copy + Eq + Default {
    fn flat_hash(&self) -> u64;
}

/// Growth load: the table grows before more than
/// `slots * MAX_LOAD_NUM / MAX_LOAD_DEN` keys are in it.
const MAX_LOAD_NUM: usize = 1;
const MAX_LOAD_DEN: usize = 2;
/// Slot count of the first allocation.
const MIN_SLOTS: usize = 8;

#[derive(Clone, Debug, Default)]
pub struct FlatMap<K, V> {
    /// Empty (no allocation) until the first insert; else a power of two.
    slots: Box<[(K, V)]>,
    /// Keys in `slots`. The side slot is not counted.
    used: usize,
    /// Value of the key that equals `K::default()`.
    zero: Option<V>,
}

#[allow(clippy::len_without_is_empty)]
impl<K: FlatKey, V: Copy + Default> FlatMap<K, V> {
    /// An empty map that holds `n` keys before it grows, like
    /// `HashMap::with_capacity`. It has the smallest power-of-two slot count
    /// that holds `n` keys under the load rule, and no allocation for 0.
    #[must_use]
    pub fn with_capacity(n: usize) -> Self {
        let mut map = Self::default();
        if n > 0 {
            map.slots = empty_slots(slots_for(n));
        }
        map
    }

    /// Makes room for `additional` more keys, like `HashMap::reserve`. The
    /// keys move at most once, to a table sized as by `with_capacity`.
    pub fn reserve(&mut self, additional: usize) {
        let n = self.used + additional;
        if n > self.max_used() {
            self.rehash(slots_for(n));
        }
    }

    #[inline]
    #[must_use]
    pub fn get(&self, key: &K) -> Option<&V> {
        if *key == K::default() {
            return self.zero.as_ref();
        }
        if self.slots.is_empty() {
            return None;
        }
        let mask = self.slots.len() - 1;
        let mut i = (key.flat_hash() as usize) & mask;
        loop {
            let slot = &self.slots[i];
            if slot.0 == *key {
                return Some(&slot.1);
            }
            if slot.0 == K::default() {
                return None;
            }
            i = (i + 1) & mask;
        }
    }

    /// Inserts or overwrites. Returns the old value, like `HashMap::insert`.
    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if key == K::default() {
            return self.zero.replace(value);
        }
        if !self.slots.is_empty() {
            let max_used = self.max_used();
            let mask = self.slots.len() - 1;
            let mut i = (key.flat_hash() as usize) & mask;
            loop {
                let slot = &mut self.slots[i];
                if slot.0 == key {
                    return Some(std::mem::replace(&mut slot.1, value));
                }
                if slot.0 == K::default() {
                    if self.used < max_used {
                        *slot = (key, value);
                        self.used += 1;
                        return None;
                    }
                    break;
                }
                i = (i + 1) & mask;
            }
        }
        // The key is absent and the table is empty or full to its load.
        self.grow();
        self.insert_absent(key, value);
        self.used += 1;
        None
    }

    /// Removes a key. Returns its value, like `HashMap::remove`.
    ///
    /// Backward-shift deletion: each later key of the probe run moves back
    /// into the hole when its home slot is not between the hole and its
    /// slot, so every key stays reachable from its home slot and no
    /// tombstone is needed.
    #[inline]
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if *key == K::default() {
            return self.zero.take();
        }
        if self.slots.is_empty() {
            return None;
        }
        let mask = self.slots.len() - 1;
        let mut i = (key.flat_hash() as usize) & mask;
        loop {
            let slot = self.slots[i];
            if slot.0 == *key {
                break;
            }
            if slot.0 == K::default() {
                return None;
            }
            i = (i + 1) & mask;
        }
        let value = self.slots[i].1;
        let mut hole = i;
        let mut j = (i + 1) & mask;
        // The load rule keeps an empty slot, so the run ends.
        loop {
            let slot = self.slots[j];
            if slot.0 == K::default() {
                break;
            }
            let home = (slot.0.flat_hash() as usize) & mask;
            // The key at `j` can fill the hole when the hole is on its probe
            // path, which is `home..=j` with wrap.
            if (j.wrapping_sub(home) & mask) >= (j.wrapping_sub(hole) & mask) {
                self.slots[hole] = slot;
                hole = j;
            }
            j = (j + 1) & mask;
        }
        self.slots[hole] = (K::default(), V::default());
        self.used -= 1;
        Some(value)
    }

    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.used + usize::from(self.zero.is_some())
    }

    /// Removes all keys and keeps the allocation.
    pub fn clear(&mut self) {
        if self.used != 0 {
            self.slots.fill((K::default(), V::default()));
            self.used = 0;
        }
        self.zero = None;
    }

    /// Keys the map can hold before it grows, like `HashMap::capacity`.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.max_used()
    }

    #[inline]
    fn max_used(&self) -> usize {
        self.slots.len() * MAX_LOAD_NUM / MAX_LOAD_DEN
    }

    /// Doubles the slot count and puts every key back.
    #[cold]
    fn grow(&mut self) {
        self.rehash((self.slots.len() * 2).max(MIN_SLOTS));
    }

    /// Moves every key to a new table of `new_len` slots.
    #[cold]
    fn rehash(&mut self, new_len: usize) {
        let old = std::mem::replace(&mut self.slots, empty_slots(new_len));
        for &(k, v) in &*old {
            if k != K::default() {
                self.insert_absent(k, v);
            }
        }
    }

    /// Writes a key that is not in `slots` into its first empty slot. The
    /// caller keeps `used` and makes sure an empty slot exists.
    #[inline]
    fn insert_absent(&mut self, key: K, value: V) {
        let mask = self.slots.len() - 1;
        let mut i = (key.flat_hash() as usize) & mask;
        while self.slots[i].0 != K::default() {
            i = (i + 1) & mask;
        }
        self.slots[i] = (key, value);
    }
}

/// The smallest power-of-two slot count that holds `n` keys under the load
/// rule.
fn slots_for(n: usize) -> usize {
    (n * MAX_LOAD_DEN)
        .div_ceil(MAX_LOAD_NUM)
        .next_power_of_two()
}

fn empty_slots<K: FlatKey, V: Copy + Default>(len: usize) -> Box<[(K, V)]> {
    vec![(K::default(), V::default()); len].into_boxed_slice()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
    struct Key(u64);

    impl FlatKey for Key {
        // A weak hash on purpose, so keys collide and probe runs wrap.
        fn flat_hash(&self) -> u64 {
            self.0 % 5
        }
    }

    #[test]
    fn matches_hash_map() {
        let mut flat: FlatMap<Key, u32> = FlatMap::default();
        let mut std_map = std::collections::HashMap::new();
        for n in 0..2000u64 {
            let k = Key((n * 7919) % 613);
            let v = n as u32;
            assert_eq!(flat.insert(k, v), std_map.insert(k, v));
            assert_eq!(flat.len(), std_map.len());
            assert!(flat.len() <= flat.capacity() + 1);
        }
        for n in 0..700u64 {
            assert_eq!(flat.get(&Key(n)), std_map.get(&Key(n)));
        }
        assert!(flat.get(&Key(0)).is_some());
        flat.clear();
        assert_eq!(flat.len(), 0);
        assert_eq!(flat.get(&Key(0)), None);
        assert_eq!(flat.get(&Key(1)), None);
        assert_eq!(flat.insert(Key(1), 3), None);
        assert_eq!(flat.get(&Key(1)), Some(&3));
    }

    /// A key whose even values start probing in the last 5 slots and odd
    /// values in the first 5, so runs wrap the table end and mix with keys
    /// that start at 0.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
    struct WrapKey(u64);

    impl FlatKey for WrapKey {
        fn flat_hash(&self) -> u64 {
            if self.0 % 2 == 0 {
                !(self.0 % 5)
            } else {
                self.0 % 5
            }
        }
    }

    #[test]
    fn remove_matches_hash_map() {
        let mut flat: FlatMap<WrapKey, u32> = FlatMap::default();
        let mut std_map = std::collections::HashMap::new();
        assert_eq!(flat.remove(&WrapKey(3)), None);
        let mut rng: u64 = 0x9e37_79b9_7f4a_7c15;
        for n in 0..20_000u32 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            // Few keys (0 among them), so removes often hit.
            let k = WrapKey((rng >> 8) % 41);
            if rng % 3 == 0 {
                assert_eq!(flat.remove(&k), std_map.remove(&k));
            } else {
                assert_eq!(flat.insert(k, n), std_map.insert(k, n));
            }
            assert_eq!(flat.len(), std_map.len());
            for m in 0..41 {
                assert_eq!(flat.get(&WrapKey(m)), std_map.get(&WrapKey(m)));
            }
        }
        let keys: Vec<WrapKey> = std_map.keys().copied().collect();
        for k in keys {
            assert_eq!(flat.remove(&k), std_map.remove(&k));
        }
        assert_eq!(flat.len(), 0);
        assert!(flat.slots.iter().all(|s| *s == (WrapKey(0), 0)));
    }

    #[test]
    fn with_capacity_and_reserve() {
        assert_eq!(FlatMap::<Key, u32>::with_capacity(0).capacity(), 0);
        for n in 1..300 {
            let cap = FlatMap::<Key, u32>::with_capacity(n).capacity();
            assert!(cap >= n && cap / 2 < n, "n {n} capacity {cap}");
        }
        let mut flat: FlatMap<Key, u32> = FlatMap::default();
        for n in 1..20u64 {
            flat.insert(Key(n), n as u32);
        }
        flat.reserve(1000);
        let cap = flat.capacity();
        assert!(cap >= 1019);
        for n in 20..1020u64 {
            flat.insert(Key(n), n as u32);
        }
        assert_eq!(flat.capacity(), cap);
        for n in 1..1020u64 {
            assert_eq!(flat.get(&Key(n)), Some(&(n as u32)));
        }
    }
}
