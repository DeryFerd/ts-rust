//! Go `unicode` functions (go1.26.8 `src/unicode/letter.go`) over the
//! Unicode 15.0.0 tables of `unicode_tables`. The Rust `char` methods use
//! the tables of the Rust version, which can be newer.

use super::unicode_tables::{LU, Range16, Range32, RangeTable};

// Go: unicode/letter.go:13 MaxLatin1
const MAX_LATIN1: u32 = 0xFF;

// Go: unicode/letter.go:88 linearMax
/// linearMax is the maximum size table for linear search for non-Latin1 rune.
const LINEAR_MAX: usize = 18;

// Go: unicode/letter.go:91 is16
/// is16 reports whether r is in the sorted slice of 16-bit ranges.
fn is16(ranges: &[Range16], r: u16) -> bool {
    if ranges.len() <= LINEAR_MAX || u32::from(r) <= MAX_LATIN1 {
        for &(lo, hi, stride) in ranges {
            if r < lo {
                return false;
            }
            if r <= hi {
                return stride == 1 || (r - lo) % stride == 0;
            }
        }
        return false;
    }

    // binary search over ranges
    let (mut lo, mut hi) = (0, ranges.len());
    while lo < hi {
        let m = (lo + hi) / 2;
        let (range_lo, range_hi, stride) = ranges[m];
        if range_lo <= r && r <= range_hi {
            return stride == 1 || (r - range_lo) % stride == 0;
        }
        if r < range_lo {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    false
}

// Go: unicode/letter.go:124 is32
/// is32 reports whether r is in the sorted slice of 32-bit ranges.
fn is32(ranges: &[Range32], r: u32) -> bool {
    if ranges.len() <= LINEAR_MAX {
        for &(lo, hi, stride) in ranges {
            if r < lo {
                return false;
            }
            if r <= hi {
                return stride == 1 || (r - lo) % stride == 0;
            }
        }
        return false;
    }

    // binary search over ranges
    let (mut lo, mut hi) = (0, ranges.len());
    while lo < hi {
        let m = (lo + hi) / 2;
        let (range_lo, range_hi, stride) = ranges[m];
        if range_lo <= r && r <= range_hi {
            return stride == 1 || (r - range_lo) % stride == 0;
        }
        if r < range_lo {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    false
}

// Go: unicode/letter.go:170 isExcludingLatin
fn is_excluding_latin(range_tab: &RangeTable, r: u32) -> bool {
    let r16 = range_tab.r16;
    let off = range_tab.latin_offset;
    if let Some(&(_, hi, _)) = r16.last()
        && r16.len() > off
        && r <= u32::from(hi)
    {
        return is16(&r16[off..], r as u16);
    }
    let r32 = range_tab.r32;
    if let Some(&(lo, _, _)) = r32.first()
        && r >= lo
    {
        return is32(r32, r);
    }
    false
}

// Go: unicode/letter.go:184 IsUpper
/// IsUpper reports whether the rune is an upper case letter.
// PORT: Go reads the Latin-1 `properties` table (go1.26.8
// unicode/tables.go). Its `pLu` entries are A-Z, U+00C0-U+00D6 and
// U+00D8-U+00DE.
pub fn is_upper(r: char) -> bool {
    let r = u32::from(r);
    if r <= MAX_LATIN1 {
        return matches!(r, 0x41..=0x5A | 0xC0..=0xD6 | 0xD8..=0xDE);
    }
    is_excluding_latin(&LU, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Unicode 15.0.0 has U+A7C0 (Lu), U+A7C9 (Lu) and U+A7D0 (Lu). U+A7CB
    // and the Garay capitals (U+10D50) are Lu from Unicode 16.0, so Go
    // 1.26 says false for them. Roman numerals (U+2160) and circled letters
    // (U+24B6) are `Other_Uppercase`, not Lu.
    #[test]
    fn is_upper_uses_unicode_15() {
        for c in "AZ\u{C0}\u{DE}\u{100}\u{A7C0}\u{A7C9}\u{A7D0}".chars() {
            assert!(is_upper(c), "{c:?}");
        }
        for c in "a_\u{D7}\u{DF}\u{FF}\u{2160}\u{24B6}\u{A7CB}\u{10D50}".chars() {
            assert!(!is_upper(c), "{c:?}");
        }
        // go1.26.8: the count and the sum of the runes with IsUpper true.
        let upper = || (0..=0x10FFFF).filter(|&r| char::from_u32(r).is_some_and(is_upper));
        assert_eq!(upper().count(), 1831);
        assert_eq!(upper().map(u64::from).sum::<u64>(), 85_228_200);
    }
}
