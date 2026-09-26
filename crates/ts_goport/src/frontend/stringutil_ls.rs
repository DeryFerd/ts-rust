//! Port of Go `stringutil/compare.go` (whole file) and
//! `stringutil/util.go:256-273` (`TruncateByRunes`) for the language service.
//!
//! PORT: Go strings can hold invalid UTF-8; Rust `&str` cannot. Go decodes
//! runes with `utf8.DecodeRuneInString`, which gives U+FFFD for an invalid
//! byte. Over a `&str` that case only happens where Go slices bytes inside a
//! rune (`HasPrefix`, `HasSuffix`), so those compare byte slices with
//! `equal_fold` below.

use crate::frontend::prelude::*;

// Go: stringutil/compare.go:9 EquateStringCaseInsensitive
pub fn equate_string_case_insensitive(a: &str, b: &str) -> bool {
    // !!!
    // return a == b || strings.ToUpper(a) == strings.ToUpper(b)
    equal_fold(a.as_bytes(), b.as_bytes())
}

// Go: stringutil/compare.go:15 EquateStringCaseSensitive
pub fn equate_string_case_sensitive(a: &str, b: &str) -> bool {
    a == b
}

// Go: stringutil/compare.go:19 GetStringEqualityComparer
pub fn get_string_equality_comparer(ignore_case: bool) -> fn(&str, &str) -> bool {
    if ignore_case {
        return equate_string_case_insensitive;
    }
    equate_string_case_sensitive
}

// Go: stringutil/compare.go:26 Comparison
pub type Comparison = i32;

// Go: stringutil/compare.go:29 ComparisonLessThan
pub const COMPARISON_LESS_THAN: Comparison = -1;
// Go: stringutil/compare.go:30 ComparisonEqual
pub const COMPARISON_EQUAL: Comparison = 0;
// Go: stringutil/compare.go:31 ComparisonGreaterThan
pub const COMPARISON_GREATER_THAN: Comparison = 1;

// Go: stringutil/compare.go:34 CompareStringsCaseInsensitive
pub fn compare_strings_case_insensitive(a: &str, b: &str) -> Comparison {
    if a == b {
        return COMPARISON_EQUAL;
    }
    let mut a = a;
    let mut b = b;
    loop {
        let (ca, sa) = decode_rune_in_string(a);
        let (cb, sb) = decode_rune_in_string(b);
        if sa == 0 {
            if sb == 0 {
                return COMPARISON_EQUAL;
            }
            return COMPARISON_LESS_THAN;
        }
        if sb == 0 {
            return COMPARISON_GREATER_THAN;
        }
        let lca = unicode_to_lower(ca);
        let lcb = unicode_to_lower(cb);
        if lca != lcb {
            if lca < lcb {
                return COMPARISON_LESS_THAN;
            }
            return COMPARISON_GREATER_THAN;
        }
        a = &a[sa..];
        b = &b[sb..];
    }
}

// Go: stringutil/compare.go:63 CompareStringsCaseSensitive
// PORT: Go `strings.Compare` is a byte-wise comparison, like `str::cmp`.
pub fn compare_strings_case_sensitive(a: &str, b: &str) -> Comparison {
    a.cmp(b) as Comparison
}

// Go: stringutil/compare.go:67 GetStringComparer
pub fn get_string_comparer(ignore_case: bool) -> fn(&str, &str) -> Comparison {
    if ignore_case {
        return compare_strings_case_insensitive;
    }
    compare_strings_case_sensitive
}

// Go: stringutil/compare.go:74 HasPrefix
pub fn has_prefix(s: &str, prefix: &str, case_sensitive: bool) -> bool {
    if case_sensitive {
        return s.starts_with(prefix);
    }
    if prefix.len() > s.len() {
        return false;
    }
    // PORT: Go `s[0:len(prefix)]` can end inside a rune; compare bytes.
    equal_fold(&s.as_bytes()[0..prefix.len()], prefix.as_bytes())
}

// Go: stringutil/compare.go:84 HasSuffix
pub fn has_suffix(s: &str, suffix: &str, case_sensitive: bool) -> bool {
    if case_sensitive {
        return s.ends_with(suffix);
    }
    if suffix.len() > s.len() {
        return false;
    }
    // PORT: Go `s[len(s)-len(suffix):]` can start inside a rune; compare bytes.
    equal_fold(&s.as_bytes()[s.len() - suffix.len()..], suffix.as_bytes())
}

// Go: stringutil/compare.go:94 HasPrefixAndSuffixWithoutOverlap
pub fn has_prefix_and_suffix_without_overlap(
    s: &str,
    prefix: &str,
    suffix: &str,
    case_sensitive: bool,
) -> bool {
    if prefix.len() + suffix.len() > s.len() {
        return false;
    }

    has_prefix(s, prefix, case_sensitive) && has_suffix(s, suffix, case_sensitive)
}

// Go: stringutil/compare.go:102 CompareStringsCaseInsensitiveThenSensitive
pub fn compare_strings_case_insensitive_then_sensitive(a: &str, b: &str) -> Comparison {
    let cmp = compare_strings_case_insensitive(a, b);
    if cmp != COMPARISON_EQUAL {
        return cmp;
    }
    compare_strings_case_sensitive(a, b)
}

// Go: stringutil/compare.go:121 CompareStringsCaseInsensitiveEslintCompatible
/// CompareStringsCaseInsensitiveEslintCompatible performs a case-insensitive comparison
/// using toLowerCase() instead of toUpperCase() for ESLint compatibility.
///
/// `CompareStringsCaseInsensitive` transforms letters to uppercase for unicode reasons,
/// while eslint's `sort-imports` rule transforms letters to lowercase. Which one you choose
/// affects the relative order of letters and ASCII characters 91-96, of which `_` is a
/// valid character in an identifier. So if we used `CompareStringsCaseInsensitive` for
/// import sorting, TypeScript and eslint would disagree about the correct case-insensitive
/// sort order for `__String` and `Foo`. Since eslint's whole job is to create consistency
/// by enforcing nitpicky details like this, it makes way more sense for us to just adopt
/// their convention so users can have auto-imports without making eslint angry.
pub fn compare_strings_case_insensitive_eslint_compatible(a: &str, b: &str) -> Comparison {
    if a == b {
        return COMPARISON_EQUAL;
    }
    let a = strings_to_lower(a);
    let b = strings_to_lower(b);
    compare_strings_case_sensitive(&a, &b)
}

// Go: stringutil/util.go:256 TruncateByRunes
pub fn truncate_by_runes(str: &str, max_length: i32) -> String {
    if (str.len() as i32) < max_length {
        return str.to_string();
    }
    if max_length <= 0 {
        return String::new();
    }
    let mut rune_count: i32 = 0;
    // Go: for i := range str (byte index of each rune start)
    for (i, _) in str.char_indices() {
        rune_count += 1;
        if rune_count > max_length {
            return str[..i].to_string();
        }
    }
    str.to_string()
}

// ---------------------------------------------------------------------------
// Go standard library helpers (`unicode`, `unicode/utf8`, `strings`).
// ---------------------------------------------------------------------------

/// Go `utf8.DecodeRuneInString` on a valid `&str`: `(RuneError, 0)` when empty.
fn decode_rune_in_string(s: &str) -> (char, usize) {
    match s.chars().next() {
        Some(c) => (c, c.len_utf8()),
        None => (char::REPLACEMENT_CHARACTER, 0),
    }
}

/// Go `utf8.DecodeRune` on bytes. An invalid or truncated sequence gives
/// U+FFFD with width 1, like Go. `s` is not empty at the call sites.
fn decode_rune_bytes(s: &[u8]) -> (char, usize) {
    let head = &s[..s.len().min(4)];
    let valid = match std::str::from_utf8(head) {
        Ok(v) => v,
        // `valid_up_to` marks the valid UTF-8 prefix.
        Err(e) => std::str::from_utf8(&head[..e.valid_up_to()]).unwrap_or(""),
    };
    match valid.chars().next() {
        Some(c) => (c, c.len_utf8()),
        None => (char::REPLACEMENT_CHARACTER, 1),
    }
}

/// Go `unicode.ToLower` (simple case mapping).
// PORT: Rust `char::to_lowercase` gives the full mapping. The only rune with
// a multi-rune full lowercase is U+0130, whose first rune ('i') is also the
// Go simple lowercase. So the first rune is the Go result.
fn unicode_to_lower(c: char) -> char {
    c.to_lowercase().next().unwrap_or(c)
}

/// Go `unicode.ToUpper` (simple case mapping). A multi-rune full uppercase
/// has no simple mapping, so the rune stays the same.
fn unicode_to_upper(c: char) -> char {
    let mut u = c.to_uppercase();
    match (u.next(), u.next()) {
        (Some(single), None) => single,
        _ => c,
    }
}

/// Go `strings.ToLower`: `unicode.ToLower` on each rune.
// PORT: not `str::to_lowercase`, which maps a final sigma to U+03C2 and
// U+0130 to two runes. Go maps each rune on its own.
fn strings_to_lower(s: &str) -> String {
    s.chars().map(unicode_to_lower).collect()
}

/// Simple case fold key. Two runes are in the same Go `unicode.SimpleFold`
/// orbit when their keys are equal.
// PORT: the same approach as the tspath and vfsmatch private helpers. The
// key is lower(upper(c)) with simple mappings. U+0131 (dotless i) has only a
// Turkic fold entry, so its orbit is itself, like Go. Rust and Go can use
// different Unicode versions; this matters only for runes added between
// those versions.
fn simple_fold_key(c: char) -> char {
    if c == '\u{0131}' {
        return c;
    }
    let u = unicode_to_upper(c);
    let mut l = u.to_lowercase();
    match (l.next(), l.next()) {
        (Some(single), None) => single,
        _ => u,
    }
}

/// Go `strings.EqualFold` on byte strings.
// PORT: runes are decoded like Go (see `decode_rune_bytes`). Each rune pair
// must be equal, ASCII case equal, or in the same simple fold orbit (see
// `simple_fold_key`), as in the Go loop over `unicode.SimpleFold`.
fn equal_fold(s: &[u8], t: &[u8]) -> bool {
    let (mut i, mut j) = (0usize, 0usize);
    while i < s.len() && j < t.len() {
        let (sr, sn) = decode_rune_bytes(&s[i..]);
        let (tr, tn) = decode_rune_bytes(&t[j..]);
        i += sn;
        j += tn;
        if sr == tr {
            continue;
        }
        // Make sr < tr to simplify what follows.
        let (sr, tr) = if tr < sr { (tr, sr) } else { (sr, tr) };
        if (tr as u32) < 0x80 {
            // ASCII only, sr/tr must be upper/lower case
            if sr.is_ascii_uppercase() && tr as u32 == sr as u32 + ('a' as u32 - 'A' as u32) {
                continue;
            }
            return false;
        }
        // General case.
        if simple_fold_key(sr) == simple_fold_key(tr) {
            continue;
        }
        return false;
    }
    i == s.len() && j == t.len()
}
