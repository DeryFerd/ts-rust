//! Go: `internal/fswatch/fsevents_darwin_nfd_test.go`, the three tests of
//! the NFC helpers (`TestNormalizeNFC`, `TestNormalizeNFCASCIIFastPath`,
//! `TestIsASCII`).
//!
//! PORT: Go builds these tests on darwin only, because `normalizeNFC`
//! calls CoreFoundation there. The port's helpers (canonicalize_darwin.rs)
//! build on every target, so the tests run on Linux. The other tests of the
//! file watch FSEvents and are not ported (the FSEvents backend is not).

use super::Failures;
use ts_goport::fswatch::{is_ascii, normalize_nfc};

// "é"
// Go: fsevents_darwin_nfd_test.go:21
const NFC_E: &str = "\u{00e9}"; // U+00E9
const NFD_E: &str = "e\u{0301}"; // U+0065 U+0301

// Go: fsevents_darwin_nfd_test.go:30 TestNormalizeNFC
// TestNormalizeNFC exercises the CoreFoundation-backed normalizer directly
// (without going through FSEvents) so a regression in the FFI plumbing is
// caught even if the end-to-end FSEvents tests are skipped.
#[test]
fn test_normalize_nfc() {
    // Latin combining marks (BMP, one combining mark per base).
    let nfc_cafe = format!("caf{NFC_E}");
    let nfd_cafe = format!("caf{NFD_E}");
    // Hangul: composition is algorithmic, not table-driven.
    // "한" (U+D55C) decomposes to ᄒ ᅡ ᆫ (U+1112 U+1161 U+11AB).
    let nfc_han = "\u{D55C}";
    let nfd_han = "\u{1112}\u{1161}\u{11AB}";
    // Multi-codepoint compose: "ệ" (U+1EC7) ⇄ "ệ" (also valid as
    // ệ due to canonical ordering; CFStringNormalize handles both).
    let nfc_e_hook = "\u{1EC7}";
    let nfd_e_hook = "e\u{0323}\u{0302}";

    let tests: Vec<(&str, String, String)> = vec![
        ("empty", String::new(), String::new()),
        (
            "ascii",
            "/var/folders/abc/hello.txt".into(),
            "/var/folders/abc/hello.txt".into(),
        ),
        (
            "ascii-only-high-bit-edge",
            "/\x7f/path".into(),
            "/\x7f/path".into(),
        ),
        ("already-NFC-latin", nfc_cafe.clone(), nfc_cafe.clone()),
        ("NFD-to-NFC-latin", nfd_cafe.clone(), nfc_cafe.clone()),
        ("already-NFC-hangul", nfc_han.into(), nfc_han.into()),
        ("NFD-to-NFC-hangul", nfd_han.into(), nfc_han.into()),
        (
            "already-NFC-multi-mark",
            nfc_e_hook.into(),
            nfc_e_hook.into(),
        ),
        (
            "NFD-to-NFC-multi-mark",
            nfd_e_hook.into(),
            nfc_e_hook.into(),
        ),
        (
            "mixed-ascii-and-NFD",
            format!("/tmp/{nfd_cafe}/file.txt"),
            format!("/tmp/{nfc_cafe}/file.txt"),
        ),
        (
            "non-bmp-passthrough",
            "/tmp/\u{1F600}.txt".into(),
            "/tmp/\u{1F600}.txt".into(),
        ),
    ];

    let mut f = Failures::new("TestNormalizeNFC");
    for (name, input, want) in &tests {
        f.check_eq(name, normalize_nfc(input), want.clone());
    }
    f.finish();
}

// Go: fsevents_darwin_nfd_test.go:79 TestNormalizeNFCASCIIFastPath
// TestNormalizeNFCASCIIFastPath verifies the ASCII fast path returns the
// input unchanged with no Unicode round-trip.
#[test]
fn test_normalize_nfc_ascii_fast_path() {
    let input = "/var/folders/abc/def/hello.txt";
    let out = normalize_nfc(input);
    assert_eq!(out, input, "ascii input mutated");
}

// Go: fsevents_darwin_nfd_test.go:89 TestIsASCII
// PORT: Go's "\x80" is one byte that is not UTF-8; the Rust case is U+0080
// (bytes C2 80, also not ASCII). Go's last case, the bytes C2 A9, is "a©".
#[test]
fn test_is_ascii() {
    let tests: [(&str, bool); 8] = [
        ("", true),
        ("hello", true),
        ("/tmp/file.txt", true),
        ("\x7f", true),          // DEL is the last ASCII byte
        ("\u{80}", false),       // first non-ASCII byte
        ("caf\u{00e9}", false),  // NFC é
        ("cafe\u{0301}", false), // NFD é (combining mark is also non-ASCII)
        ("a\u{00A9}", false),    // © (U+00A9)
    ];
    let mut f = Failures::new("TestIsASCII");
    for (input, want) in tests {
        f.check_eq(&format!("isASCII({input:?})"), is_ascii(input), want);
    }
    f.finish();
}
