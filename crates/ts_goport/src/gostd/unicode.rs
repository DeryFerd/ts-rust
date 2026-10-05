//! Go `unicode` functions (go1.27.1 `src/unicode/letter.go`) over the
//! Unicode 17.0.0 tables of `unicode_tables`. The Rust `char` methods use
//! the tables of the Rust version, which can be newer or older.

use super::unicode_tables::{CASE_RANGES, CaseRange, LL, LU, Range16, Range32, RangeTable};

// Go: unicode/letter.go:10 MaxRune
const MAX_RUNE: i32 = 0x10FFFF;

// Go: unicode/letter.go:12 MaxASCII
const MAX_ASCII: u32 = 0x7F;

// Go: unicode/letter.go:13 MaxLatin1
const MAX_LATIN1: u32 = 0xFF;

// Go: unicode/letter.go:71 UpperCase
/// Index into the Delta arrays inside CaseRanges for case mapping.
const UPPER_CASE: usize = 0;

// Go: unicode/letter.go:72 LowerCase
const LOWER_CASE: usize = 1;

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
// PORT: Go reads the Latin-1 `properties` table (go1.27.1
// unicode/tables.go). Its `pLu` entries are A-Z, U+00C0-U+00D6 and
// U+00D8-U+00DE.
pub fn is_upper(r: char) -> bool {
    let r = u32::from(r);
    if r <= MAX_LATIN1 {
        return matches!(r, 0x41..=0x5A | 0xC0..=0xD6 | 0xD8..=0xDE);
    }
    is_excluding_latin(&LU, r)
}

// Go: unicode/letter.go:193 IsLower
/// IsLower reports whether the rune is a lower case letter.
// PORT: Go reads the Latin-1 `properties` table (go1.27.1
// unicode/tables.go). Its `pLl` entries are a-z, U+00B5, U+00DF-U+00F6 and
// U+00F8-U+00FF.
pub fn is_lower(r: char) -> bool {
    let r = u32::from(r);
    if r <= MAX_LATIN1 {
        return matches!(r, 0x61..=0x7A | 0xB5 | 0xDF..=0xF6 | 0xF8..=0xFF);
    }
    is_excluding_latin(&LL, r)
}

// Go: unicode/letter.go:211 lookupCaseRange
/// lookupCaseRange returns the CaseRange mapping for rune r or nil if no
/// mapping exists for r.
fn lookup_case_range(r: u32, case_range: &[CaseRange]) -> Option<&CaseRange> {
    // binary search over ranges
    let (mut lo, mut hi) = (0, case_range.len());
    while lo < hi {
        let m = (lo + hi) / 2;
        let cr = &case_range[m];
        if cr.0 <= r && r <= cr.1 {
            return Some(cr);
        }
        if r < cr.0 {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    None
}

// Go: unicode/letter.go:231 convertCase
/// convertCase converts r to _case using CaseRange cr.
fn convert_case(case: usize, r: u32, cr: &CaseRange) -> u32 {
    let delta = cr.2[case];
    if delta > MAX_RUNE {
        // In an Upper-Lower sequence, which always starts with
        // an UpperCase letter, the real deltas always look like:
        //     {0, 1, 0}    UpperCase (Lower is next)
        //     {-1, 0, -1}  LowerCase (Upper, Title are previous)
        // The characters at even offsets from the beginning of the
        // sequence are upper case; the ones at odd offsets are lower.
        // The correct mapping can be done by clearing or setting the low
        // bit in the sequence offset.
        // The constants UpperCase and TitleCase are even while LowerCase
        // is odd so we take the low bit from _case.
        return cr.0 + (((r - cr.0) & !1) | (case as u32 & 1));
    }
    r.wrapping_add_signed(delta)
}

// Go: unicode/letter.go:251 to
/// to maps the rune using the specified case mapping.
// PORT: the callers pass UpperCase or LowerCase, so the `_case` range check
// is not ported. Go also reports whether caseRange had a mapping; Go `To`
// drops that result, so the port does not return it.
fn to(case: usize, r: u32, case_range: &[CaseRange]) -> u32 {
    match lookup_case_range(r, case_range) {
        Some(cr) => convert_case(case, r, cr),
        None => r,
    }
}

// Go: unicode/letter.go:262 To
/// To maps the rune to the specified case: UpperCase or LowerCase.
// PORT: CaseRanges maps each char to a char (the test checks every char),
// so the `unwrap_or` never applies.
fn to_case(case: usize, r: char) -> char {
    char::from_u32(to(case, u32::from(r), CASE_RANGES)).unwrap_or(r)
}

// Go: unicode/letter.go:268 ToUpper
/// ToUpper maps the rune to upper case.
// PORT: Go's simple mapping (one rune to one rune) over the Unicode 17.0.0
// CaseRanges. Rust `char::to_uppercase` is the full mapping of the Rust
// Unicode version.
pub fn to_upper(r: char) -> char {
    if u32::from(r) <= MAX_ASCII {
        return r.to_ascii_uppercase();
    }
    to_case(UPPER_CASE, r)
}

// Go: unicode/letter.go:279 ToLower
/// ToLower maps the rune to lower case.
// PORT: Go's simple mapping (one rune to one rune) over the Unicode 17.0.0
// CaseRanges. Rust `char::to_lowercase` is the full mapping of the Rust
// Unicode version.
pub fn to_lower(r: char) -> char {
    if u32::from(r) <= MAX_ASCII {
        return r.to_ascii_lowercase();
    }
    to_case(LOWER_CASE, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    // PORT: the test names are from the Unicode 15.0.0 tables (go1.26.8).
    // They stay for the protected test set; the values are go1.27.1
    // (Unicode 17.0.0), the toolchain of the pin N oracle.

    // U+A7C0, U+A7C9 and U+A7D0 are Lu. U+A7CB and the Garay capitals
    // (U+10D50) are Lu from Unicode 16.0, so go1.27.1 says true for them
    // (go1.26.8 said false). Roman numerals (U+2160) and circled letters
    // (U+24B6) are `Other_Uppercase`, not Lu.
    #[test]
    fn is_upper_uses_unicode_15() {
        assert_eq!(crate::gostd::unicode_tables::VERSION, "17.0.0");
        for c in "AZ\u{C0}\u{DE}\u{100}\u{A7C0}\u{A7C9}\u{A7D0}\u{A7CB}\u{10D50}".chars() {
            assert!(is_upper(c), "{c:?}");
        }
        for c in "a_\u{D7}\u{DF}\u{FF}\u{2160}\u{24B6}".chars() {
            assert!(!is_upper(c), "{c:?}");
        }
        // go1.27.1: the count and the sum of the runes with IsUpper true
        // (go1.26.8: 1831 and 85_228_200).
        let upper = || (0..=0x10FFFF).filter(|&r| char::from_u32(r).is_some_and(is_upper));
        assert_eq!(upper().count(), 1886);
        assert_eq!(upper().map(u64::from).sum::<u64>(), 89_399_941);
    }

    // U+0295 is Ll in Unicode 15.0.0 and Lo from Unicode 16.0, so go1.27.1
    // says false for it. U+A7CD and the Garay small letters (U+10D70) are Ll
    // from Unicode 16.0. U+00AA and U+2170 are `Other_Lowercase`, not Ll.
    #[test]
    fn is_lower_uses_unicode_15() {
        for c in "az\u{B5}\u{DF}\u{F8}\u{FF}\u{101}\u{A7CD}\u{10D70}".chars() {
            assert!(is_lower(c), "{c:?}");
        }
        for c in "A_\u{AA}\u{BA}\u{F7}\u{2170}\u{295}".chars() {
            assert!(!is_lower(c), "{c:?}");
        }
        // go1.27.1: the count and the sum of the runes with IsLower true
        // (go1.26.8: 2233 and 103_102_186).
        let lower = || (0..=0x10FFFF).filter(|&r| char::from_u32(r).is_some_and(is_lower));
        assert_eq!(lower().count(), 2283);
        assert_eq!(lower().map(u64::from).sum::<u64>(), 107_102_796);
    }

    // Go uses the simple mapping of Unicode 17.0.0: U+0130 lowers to 'i',
    // U+00DF has no upper case, U+1FB3 uppers to U+1FBC, and the Unicode 16.0
    // and 17.0 pairs (U+A7CB and U+0264, U+A7DC and U+019B, U+1C89 and
    // U+1C8A, U+10D50 and U+10D70, U+16EA0 and U+16EBB) map to each other.
    #[test]
    fn case_mapping_uses_unicode_15() {
        let lower = [
            ('A', 'a'),
            ('\u{C0}', '\u{E0}'),
            ('\u{100}', '\u{101}'),
            ('\u{101}', '\u{101}'),
            ('\u{130}', 'i'),
            ('\u{1E9E}', '\u{DF}'),
            ('\u{212A}', 'k'),
            ('\u{A7CB}', '\u{264}'),
            ('\u{A7DC}', '\u{19B}'),
            ('\u{1C89}', '\u{1C8A}'),
            ('\u{10D50}', '\u{10D70}'),
            ('\u{16EA0}', '\u{16EBB}'),
        ];
        for (c, want) in lower {
            assert_eq!(to_lower(c), want, "{c:?}");
        }
        let upper = [
            ('a', 'A'),
            ('\u{DF}', '\u{DF}'),
            ('\u{FF}', '\u{178}'),
            ('\u{101}', '\u{100}'),
            ('\u{131}', 'I'),
            ('\u{17F}', 'S'),
            ('\u{1FB3}', '\u{1FBC}'),
            ('\u{264}', '\u{A7CB}'),
            ('\u{19B}', '\u{A7DC}'),
            ('\u{1C8A}', '\u{1C89}'),
            ('\u{10D70}', '\u{10D50}'),
            ('\u{16EBB}', '\u{16EA0}'),
        ];
        for (c, want) in upper {
            assert_eq!(to_upper(c), want, "{c:?}");
        }
        // CaseRanges maps each char to a char.
        let chars = || (0..=0x10FFFF).filter_map(char::from_u32);
        for c in chars() {
            for case in [UPPER_CASE, LOWER_CASE] {
                let m = to(case, u32::from(c), CASE_RANGES);
                assert!(char::from_u32(m).is_some(), "{c:?}");
            }
        }
        // go1.27.1: the count of the runes that ToLower (ToUpper) changes,
        // and the sum of the results (go1.26.8: (1433, 34_914_171) and
        // (1450, 32_256_850)).
        let changed = |f: fn(char) -> char| {
            let mapped = || chars().filter_map(|c| Some(f(c)).filter(|&m| m != c));
            (mapped().count(), mapped().map(u64::from).sum::<u64>())
        };
        assert_eq!(changed(to_lower), (1488, 39_002_393));
        assert_eq!(changed(to_upper), (1505, 36_428_591));
    }
}
