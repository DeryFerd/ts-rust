//! Go `strconv.Quote` and its helpers (go1.27.1 `src/strconv/quote.go` and
//! `src/strconv/isprint.go`, Unicode 17.0.0, the toolchain of the pin N
//! oracle). Go `%q` of a string is `quote(s)`.
//!
//! The `IsPrint` tables are generated from Go's `isprint.go`
//! (`strconv_isprint.rs`, `scripts/goport/gen/unicode/gen.sh`), so the
//! result equals Go's for every rune.
//!
//! PORT: Go strings may hold invalid UTF-8, which `Quote` writes as `\x..`.
//! A Rust `&str` is always valid UTF-8, so that branch cannot run.

use crate::prelude::*;

#[path = "strconv_isprint.rs"]
mod isprint;
use isprint::{IS_GRAPHIC, IS_NOT_PRINT16, IS_NOT_PRINT32, IS_PRINT16, IS_PRINT32};

const LOWERHEX: &[u8; 16] = b"0123456789abcdef";

/// Go `utf8.RuneSelf`.
const RUNE_SELF: u32 = 0x80;

// Go: strconv/quote.go:23 quoteWith
fn quote_with(s: &str, quote: u8, ascii_only: bool, graphic_only: bool) -> String {
    let buf = append_quoted_with(
        Vec::with_capacity(3 * s.len() / 2),
        s,
        quote,
        ascii_only,
        graphic_only,
    );
    String::from_utf8(buf).expect("quote writes UTF-8")
}

// Go: strconv/quote.go:27 quoteRuneWith
fn quote_rune_with(r: char, quote: u8, ascii_only: bool, graphic_only: bool) -> String {
    let buf = append_quoted_rune_with(Vec::new(), r, quote, ascii_only, graphic_only);
    String::from_utf8(buf).expect("quote writes UTF-8")
}

// Go: strconv/quote.go:31 appendQuotedWith
fn append_quoted_with(
    mut buf: Vec<u8>,
    s: &str,
    quote: u8,
    ascii_only: bool,
    graphic_only: bool,
) -> Vec<u8> {
    // Often called with big strings, so preallocate. If there's quoting,
    // this is conservative but still helps a lot.
    buf.reserve(1 + s.len() + 1);
    buf.push(quote);
    for r in s.chars() {
        // PORT: Go writes `\x` and two hex digits for a byte that is not
        // valid UTF-8 (`width == 1 && r == utf8.RuneError`); a &str has none.
        buf = append_escaped_rune(buf, r, quote, ascii_only, graphic_only);
    }
    buf.push(quote);
    buf
}

// Go: strconv/quote.go:54 appendQuotedRuneWith
// PORT: a Rust `char` is always a valid rune, so Go's `utf8.ValidRune` check
// is always true.
fn append_quoted_rune_with(
    mut buf: Vec<u8>,
    r: char,
    quote: u8,
    ascii_only: bool,
    graphic_only: bool,
) -> Vec<u8> {
    buf.push(quote);
    buf = append_escaped_rune(buf, r, quote, ascii_only, graphic_only);
    buf.push(quote);
    buf
}

// Go: strconv/quote.go:64 appendEscapedRune
fn append_escaped_rune(
    mut buf: Vec<u8>,
    r: char,
    quote: u8,
    ascii_only: bool,
    graphic_only: bool,
) -> Vec<u8> {
    if r == quote as char || r == '\\' {
        // always backslashed
        buf.push(b'\\');
        buf.push(r as u8);
        return buf;
    }
    if ascii_only {
        if (r as u32) < RUNE_SELF && is_print(r) {
            buf.push(r as u8);
            return buf;
        }
    } else if is_print(r) || graphic_only && is_in_graphic_list(r) {
        let mut tmp = [0u8; 4];
        buf.extend_from_slice(r.encode_utf8(&mut tmp).as_bytes());
        return buf;
    }
    match r {
        '\x07' => buf.extend_from_slice(b"\\a"),
        '\x08' => buf.extend_from_slice(b"\\b"),
        '\x0c' => buf.extend_from_slice(b"\\f"),
        '\n' => buf.extend_from_slice(b"\\n"),
        '\r' => buf.extend_from_slice(b"\\r"),
        '\t' => buf.extend_from_slice(b"\\t"),
        '\x0b' => buf.extend_from_slice(b"\\v"),
        _ => {
            let r = r as u32;
            if r < ' ' as u32 || r == 0x7f {
                buf.extend_from_slice(b"\\x");
                buf.push(LOWERHEX[((r as u8) >> 4) as usize]);
                buf.push(LOWERHEX[((r as u8) & 0xF) as usize]);
            } else if r < 0x10000 {
                // PORT: Go's `!utf8.ValidRune(r)` case (write U+FFFD) cannot
                // occur for a char.
                buf.extend_from_slice(b"\\u");
                let mut s: i32 = 12;
                while s >= 0 {
                    buf.push(LOWERHEX[((r >> s as u32) & 0xF) as usize]);
                    s -= 4;
                }
            } else {
                buf.extend_from_slice(b"\\U");
                let mut s: i32 = 28;
                while s >= 0 {
                    buf.push(LOWERHEX[((r >> s as u32) & 0xF) as usize]);
                    s -= 4;
                }
            }
        }
    }
    buf
}

// Go: strconv/quote.go:121 Quote
/// Quote returns a double-quoted Go string literal representing s. The
/// returned string uses Go escape sequences (\t, \n, \xFF, Ā) for
/// control characters and non-printable characters as defined by
/// [IsPrint].
pub fn quote(s: &str) -> String {
    quote_with(s, b'"', false, false)
}

// Go: strconv/quote.go:134 QuoteToASCII
/// QuoteToASCII returns a double-quoted Go string literal representing s.
/// The returned string uses Go escape sequences (\t, \n, \xFF, Ā) for
/// non-ASCII characters and non-printable characters as defined by [IsPrint].
pub fn quote_to_ascii(s: &str) -> String {
    quote_with(s, b'"', true, false)
}

// Go: strconv/quote.go:148 QuoteToGraphic
/// QuoteToGraphic returns a double-quoted Go string literal representing s.
/// The returned string leaves Unicode graphic characters, as defined by
/// [IsGraphic], unchanged and uses Go escape sequences (\t, \n, \xFF, Ā)
/// for non-graphic characters.
pub fn quote_to_graphic(s: &str) -> String {
    quote_with(s, b'"', false, true)
}

// Go: strconv/quote.go:163 QuoteRune
/// QuoteRune returns a single-quoted Go character literal representing the
/// rune. The returned string uses Go escape sequences (\t, \n, \xFF, Ā)
/// for control characters and non-printable characters as defined by [IsPrint].
pub fn quote_rune(r: char) -> String {
    quote_rune_with(r, b'\'', false, false)
}

// Go: strconv/quote.go:179 QuoteRuneToASCII
/// QuoteRuneToASCII returns a single-quoted Go character literal representing
/// the rune. The returned string uses Go escape sequences (\t, \n, \xFF,
/// Ā) for non-ASCII characters and non-printable characters as defined
/// by [IsPrint].
pub fn quote_rune_to_ascii(r: char) -> String {
    quote_rune_with(r, b'\'', true, false)
}

// Go: strconv/quote.go:195 QuoteRuneToGraphic
/// QuoteRuneToGraphic returns a single-quoted Go character literal representing
/// the rune. If the rune is not a Unicode graphic character,
/// as defined by [IsGraphic], the returned string will use a Go escape sequence
/// (\t, \n, \xFF, Ā).
pub fn quote_rune_to_graphic(r: char) -> String {
    quote_rune_with(r, b'\'', false, true)
}

// Go: strconv/quote.go:495 bsearch
/// bsearch is semantically the same as [slices.BinarySearch] (without NaN checks)
/// We copied this function because we can not import "slices" here.
fn bsearch<E: Ord + Copy>(s: &[E], v: E) -> (usize, bool) {
    let n = s.len();
    let (mut i, mut j) = (0usize, n);
    while i < j {
        let h = i + (j - i) / 2;
        if s[h] < v {
            i = h + 1;
        } else {
            j = h;
        }
    }
    (i, i < n && s[i] == v)
}

// Go: strconv/quote.go:518 IsPrint
/// IsPrint reports whether the rune is defined as printable by Go, with
/// the same definition as [unicode.IsPrint]: letters, numbers, punctuation,
/// symbols and ASCII space.
pub fn is_print(r: char) -> bool {
    let r = r as u32;
    // Fast check for Latin-1
    if r <= 0xFF {
        if 0x20 <= r && r <= 0x7E {
            // All the ASCII is printable from space through DEL-1.
            return true;
        }
        if 0xA1 <= r && r <= 0xFF {
            // Similarly for ¡ through ÿ...
            return r != 0xAD; // ...except for the bizarre soft hyphen.
        }
        return false;
    }

    // Same algorithm, either on uint16 or uint32 value.
    // First, find first i such that isPrint[i] >= x.
    // This is the index of either the start or end of a pair that might span x.
    // The start is even (isPrint[i&^1]) and the end is odd (isPrint[i|1]).
    // If we find x in a range, make sure x is not in isNotPrint list.

    if r < 1 << 16 {
        let (rr, is_print, is_not_print) = (r as u16, &IS_PRINT16[..], &IS_NOT_PRINT16[..]);
        let (i, _) = bsearch(is_print, rr);
        if i >= is_print.len() || rr < is_print[i & !1] || is_print[i | 1] < rr {
            return false;
        }
        let (_, found) = bsearch(is_not_print, rr);
        return !found;
    }

    let (rr, is_print, is_not_print) = (r, &IS_PRINT32[..], &IS_NOT_PRINT32[..]);
    let (i, _) = bsearch(is_print, rr);
    if i >= is_print.len() || rr < is_print[i & !1] || is_print[i | 1] < rr {
        return false;
    }
    if r >= 0x20000 {
        return true;
    }
    let r = r - 0x10000;
    let (_, found) = bsearch(is_not_print, r as u16);
    !found
}

// Go: strconv/quote.go:564 IsGraphic
/// IsGraphic reports whether the rune is defined as a Graphic by Unicode. Such
/// characters include letters, marks, numbers, punctuation, symbols, and
/// spaces, from categories L, M, N, P, S, and Zs.
pub fn is_graphic(r: char) -> bool {
    if is_print(r) {
        return true;
    }
    is_in_graphic_list(r)
}

// Go: strconv/quote.go:574 isInGraphicList
/// isInGraphicList reports whether the rune is in the isGraphic list. This separation
/// from IsGraphic allows quoteWith to avoid two calls to IsPrint.
/// Should be called only if IsPrint fails.
fn is_in_graphic_list(r: char) -> bool {
    // We know r must fit in 16 bits - see makeisprint.go.
    let r = r as u32;
    if r > 0xFFFF {
        return false;
    }
    let (_, found) = bsearch(&IS_GRAPHIC[..], r as u16);
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    // go1.27.1 (Unicode 17.0.0): the count and the sum of the runes with
    // IsPrint (IsGraphic) true. go1.26.8 (Unicode 15.0.0) gave 148998 and
    // 15_750_900_724 (149014 and 15_751_025_625).
    #[test]
    fn is_print_uses_unicode_17() {
        let chars = || (0..=0x10FFFF).filter_map(char::from_u32);
        let count = |f: fn(char) -> bool| {
            let hits = || chars().filter(|&c| f(c));
            (hits().count(), hits().map(u64::from).sum::<u64>())
        };
        assert_eq!(count(is_print), (159_613, 17_258_563_829));
        assert_eq!(count(is_graphic), (159_629, 17_258_688_730));
    }

    // go1.27.1 strconv.Quote writes the Unicode 16.0 and 17.0 letters as they
    // are; go1.26.8 wrote "\ua7cb", "\U00010d50" and "\U00016ea0".
    #[test]
    fn quote_keeps_unicode_17_letters() {
        assert_eq!(quote("\u{A7CB}"), "\"\u{A7CB}\"");
        assert_eq!(quote("\u{10D50}"), "\"\u{10D50}\"");
        assert_eq!(quote("\u{16EA0}"), "\"\u{16EA0}\"");
        assert_eq!(quote("a\u{378}b"), "\"a\\u0378b\"");
    }
}
