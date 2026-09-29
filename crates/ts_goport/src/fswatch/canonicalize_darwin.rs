//! Go: internal/fswatch/canonicalize_darwin.go, and `isASCII` and
//! `normalizeNFC` of fsevents_darwin_ffi.go.
//!
//! PORT: Go builds these files on darwin (amd64 and arm64) only, and
//! `normalizeNFC` calls CoreFoundation (CFStringNormalize with
//! kCFStringNormalizationFormC). The port normalizes with the
//! `unicode-normalization` crate (Unicode NFC, safe code). `is_ascii` and
//! `normalize_nfc` build on every target, so their Go unit tests
//! (fsevents_darwin_nfd_test.go) run on Linux; `canonicalize_path` builds on
//! darwin only, and the other targets use canonicalize_other.rs.

use crate::fswatch::prelude::*;

use unicode_normalization::UnicodeNormalization;

// Go: canonicalize_darwin.go:14 canonicalizePath
/// canonicalizePath returns the path in the form the library uses for
/// internal bookkeeping and event delivery. On macOS, paths from FSEvents
/// arrive using whatever Unicode normalization form is stored on disk;
/// usually NFC, but sometimes NFD (e.g. files created on legacy HFS+
/// volumes or copied from systems that use NFD). APFS resolves either form
/// to the same inode, but raw string comparisons against caller-supplied
/// paths (typically NFC) silently break. Normalizing every path the
/// library ingests to NFC keeps watch keys, dirWatch lookups, WatchFile
/// filters, and event paths all in one consistent form.
#[cfg(all(
    any(target_os = "macos", target_os = "ios"),
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
pub fn canonicalize_path(p: &str) -> String {
    normalize_nfc(p)
}

// Go: fsevents_darwin_ffi.go:217 isASCII
/// isASCII reports whether every byte in s is below 0x80. Pure-ASCII paths
/// are identical in every Unicode normalization form, so we can skip the
/// CoreFoundation round-trip entirely, which is the overwhelming common case.
pub fn is_ascii(s: &str) -> bool {
    s.bytes().all(|b| b < 0x80)
}

// Go: fsevents_darwin_ffi.go:274 normalizeNFC
/// normalizeNFC returns s in Unicode NFC (canonical composed) form. ASCII
/// inputs are returned unchanged. Non-ASCII inputs go through CoreFoundation;
/// if any step fails (e.g. invalid UTF-8 from a corrupt path), the original
/// string is returned so the caller still sees *something* rather than nothing.
///
/// PORT: `s` is in the port form of a Go string (`scanner_util`). Its Go
/// bytes are normalized; when they are not UTF-8, CFStringCreate fails in
/// Go and `s` is returned unchanged, as here.
pub fn normalize_nfc(s: &str) -> String {
    if is_ascii(s) {
        return s.to_string();
    }
    let bytes = crate::scanner_util::go_string_bytes(s);
    let Ok(text) = std::str::from_utf8(&bytes) else {
        return s.to_string();
    };
    crate::scanner_util::go_string_from_utf8(text.nfc().collect())
}
