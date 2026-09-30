//! Go: internal/fswatch/pathcompare.go (ts#64210).
//!
//! PORT: paths are Go strings in the port form (see `gostring`): a byte
//! that is not valid UTF-8 is a marker unit of non-ASCII chars. The byte
//! loops see such a unit as non-ASCII, as Go sees the byte, and equal port
//! forms are equal Go strings. Go `*comparisonCache` (a pointer to a map
//! that one synchronous pass shares) is `Option<&Mutex<ComparisonCache>>`:
//! prepared paths are stored in callbacks, which cross threads, so the
//! borrow must be `Send`. Go allocates the nil map on first use; the port's
//! mutex holds an empty map.

use crate::fswatch::prelude::*;

use std::sync::Mutex;

// Go: pathcompare.go:8 pathComparer
// PORT: Go also has the exported `PathComparer` (pathkey.go); it is
// `PathComparerExported` (PORTING "Names").
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct PathComparer {
    pub ignore_case: bool,
}

// Go: pathcompare.go:14 comparisonPath
/// Watch roots are prepared before publication and are immutable thereafter.
/// Event paths are local to one routing operation and folded only on demand.
#[derive(Clone, Debug, Default)]
pub struct ComparisonPath<'c> {
    pub path: String,
    pub folded: String,
    pub ready: bool,
    pub cache: Option<&'c Mutex<ComparisonCache>>,
}

// Go: pathcompare.go:23 comparisonCache
/// Shared only within a synchronous callback/termination pass, never published
/// to a subscriber or stored on a watch.
pub type ComparisonCache = FxHashMap<String, String>;

impl PathComparer {
    // Go: pathcompare.go:25 pathComparer.prepare
    pub fn prepare(&self, path: &str) -> ComparisonPath<'static> {
        let mut p = ComparisonPath {
            path: path.to_string(),
            ..Default::default()
        };
        if self.ignore_case && NATIVE_PATH_FOLDING {
            p.fold();
        }
        p
    }
}

impl ComparisonPath<'_> {
    // Go: pathcompare.go:33 comparisonPath.fold
    pub fn fold(&mut self) -> String {
        if !self.ready {
            if let Some(cache) = self.cache {
                if let Some(folded) = cache.lock().unwrap().get(&self.path) {
                    self.folded = folded.clone();
                    self.ready = true;
                    return self.folded.clone();
                }
            }
            self.folded = fold_native_path(&self.path);
            self.ready = true;
            if let Some(cache) = self.cache {
                cache
                    .lock()
                    .unwrap()
                    .insert(self.path.clone(), self.folded.clone());
            }
        }
        self.folded.clone()
    }
}

impl PathComparer {
    // Go: pathcompare.go:54 pathComparer.suffix
    /// suffix returns the part of path below root, respecting directory boundaries.
    pub fn suffix(&self, root: &str, path: &str) -> (String, bool) {
        let mut p = ComparisonPath {
            path: path.to_string(),
            ..Default::default()
        };
        self.suffix_prepared(
            &ComparisonPath {
                path: root.to_string(),
                ..Default::default()
            },
            &mut p,
        )
    }

    // Go: pathcompare.go:59 pathComparer.suffixPrepared
    // PORT: Go passes `root` by value; the port borrows it (suffixUnicode
    // folds a copy, as Go does).
    pub fn suffix_prepared(
        &self,
        root: &ComparisonPath<'_>,
        path: &mut ComparisonPath<'_>,
    ) -> (String, bool) {
        if is_in_directory_or_self(&root.path, &path.path) {
            return (path.path[root.path.len()..].to_string(), true);
        }
        if !self.ignore_case || root.path.is_empty() {
            return (String::new(), false);
        }
        let (suffix, ok, unicode) = path_suffix_ascii(&root.path, &path.path);
        if !unicode {
            return (suffix, ok);
        }
        self.suffix_unicode(root, path)
    }

    // Go: pathcompare.go:73 pathComparer.suffixUnicode
    pub fn suffix_unicode(
        &self,
        root: &ComparisonPath<'_>,
        path: &mut ComparisonPath<'_>,
    ) -> (String, bool) {
        if !NATIVE_PATH_FOLDING {
            return path_suffix_fold_unicode(&root.path, &path.path);
        }
        // Go: `root` is a copy, so its fold stays local.
        let mut root = root.clone();
        let (a, b) = (root.fold(), path.fold());
        if a.is_empty() || b.is_empty() {
            // CFString cannot represent invalid UTF-8. Retain the simple-fold
            // behavior for malformed paths rather than truncating or losing bytes.
            return path_suffix_fold_unicode(&root.path, &path.path);
        }
        if !is_in_directory_or_self(&a, &b) {
            return (String::new(), false);
        }
        if a == b {
            return (String::new(), true);
        }
        // Folding and canonical normalization preserve separators, but not byte
        // lengths. Find the matching boundary in the original event, not its fold.
        let mut offset = 0;
        let mut separators = root.path.bytes().filter(|&c| c == b'/').count();
        let trailing_separator = root.path.as_bytes()[root.path.len() - 1] == b'/';
        if !trailing_separator {
            separators += 1;
        }
        for _ in 0..separators {
            let Some(i) = path.path.as_bytes()[offset..]
                .iter()
                .position(|&c| c == b'/')
            else {
                panic!("fswatch: folded path lost a directory boundary");
            };
            offset += i + 1;
        }
        if trailing_separator {
            return (path.path[offset..].to_string(), true);
        }
        (path.path[offset - 1..].to_string(), true)
    }
}

// Go: pathcompare.go:112 pathSuffixASCII
/// The third result requests Unicode comparison; an ASCII rejection must not
/// reject an expanding alias just because the other spelling is ASCII.
// PORT: Go compares string slices; the port compares bytes, and slices the
// path only at an ASCII separator or its end (a char boundary).
pub fn path_suffix_ascii(root: &str, path: &str) -> (String, bool, bool) {
    // Go: utf8.RuneSelf
    const RUNE_SELF: u8 = 0x80;
    let (rb, pb) = (root.as_bytes(), path.as_bytes());
    let mut i = 0;
    // Skip shared prefixes a word at a time, which is common when routing an
    // event past sibling watches. String slice comparisons do not allocate.
    while i + 8 <= rb.len() && i + 8 <= pb.len() && rb[i..i + 8] == pb[i..i + 8] {
        i += 8;
    }
    while i < rb.len() && i < pb.len() {
        let (mut a, mut b) = (rb[i], pb[i]);
        if a >= RUNE_SELF || b >= RUNE_SELF {
            return (String::new(), false, true);
        }
        if a == b {
            i += 1;
            continue;
        }
        a |= 0x20;
        b |= 0x20;
        if a != b || !a.is_ascii_lowercase() {
            return (String::new(), false, false);
        }
        i += 1;
    }
    if i == rb.len() && (i == pb.len() || pb[i] == b'/') {
        return (path[i..].to_string(), true, false);
    }
    (
        String::new(),
        false,
        (i < rb.len() && rb[i] >= RUNE_SELF) || (i < pb.len() && pb[i] >= RUNE_SELF),
    )
}

// Go: pathcompare.go:141 pathSuffixFoldUnicode
/// Comparing the remaining components avoids assuming case-equivalent UTF-8
/// strings have the same byte length (for example, s and long s).
pub fn path_suffix_fold_unicode(root: &str, path: &str) -> (String, bool) {
    // Go: strings.Cut(s, "/")
    fn cut(s: &str) -> (&str, &str, bool) {
        match s.split_once('/') {
            Some((before, after)) => (before, after, true),
            None => (s, "", false),
        }
    }
    let (mut root, mut path) = (root, path);
    loop {
        let (root_part, root_rest, root_more) = cut(root);
        let (path_part, path_rest, path_more) = cut(path);
        if !equal_fold(root_part, path_part) {
            return (String::new(), false);
        }
        if !root_more {
            if path_more {
                return (path[path_part.len()..].to_string(), true);
            }
            return (String::new(), true);
        }
        if !path_more {
            return (String::new(), false);
        }
        root = root_rest;
        path = path_rest;
    }
}

impl PathComparer {
    // Go: pathcompare.go:161 pathComparer.contains
    pub fn contains(&self, root: &str, path: &str) -> bool {
        let (_, ok) = self.suffix(root, path);
        ok
    }

    // Go: pathcompare.go:166 pathComparer.rebase
    pub fn rebase(&self, path: &str, from: &str, to: &str) -> (String, bool) {
        let mut p = ComparisonPath {
            path: path.to_string(),
            ..Default::default()
        };
        self.rebase_prepared(
            &mut p,
            &ComparisonPath {
                path: from.to_string(),
                ..Default::default()
            },
            to,
        )
    }

    // Go: pathcompare.go:171 pathComparer.rebasePrepared
    // PORT: Go passes `from` by value; the port borrows it.
    pub fn rebase_prepared(
        &self,
        path: &mut ComparisonPath<'_>,
        from: &ComparisonPath<'_>,
        to: &str,
    ) -> (String, bool) {
        if is_in_directory_or_self(&from.path, &path.path) {
            return (rebase_path(&path.path, &from.path, to), true);
        }
        if !self.ignore_case || from.path.is_empty() {
            return (String::new(), false);
        }
        let (mut suffix, mut ok, unicode) = path_suffix_ascii(&from.path, &path.path);
        if unicode {
            (suffix, ok) = self.suffix_unicode(from, path);
        }
        if !ok {
            return (String::new(), false);
        }
        (join_path_suffix(to, &suffix), true)
    }
}

/// Go `strings.EqualFold`.
// PORT: the same approach as the tspath, vfsmatch and stringutil private
// helpers: two runes match when they are equal, ASCII case equal, or in the
// same simple fold orbit (see `simple_fold_key`), as in the Go loop over
// `unicode.SimpleFold`. The runes are Go's (`go_runes`: an invalid byte is
// U+FFFD). Public for the fswatch tests, which compare with Go
// `strings.EqualFold`.
pub fn equal_fold(s: &str, t: &str) -> bool {
    let (s, t) = (
        crate::scanner_util::go_runes(s),
        crate::scanner_util::go_runes(t),
    );
    let (mut s, mut t) = (s.into_iter(), t.into_iter());
    loop {
        let (sr, tr) = match (s.next(), t.next()) {
            (None, None) => return true,
            (Some(sr), Some(tr)) => (sr, tr),
            _ => return false,
        };
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
}

/// Simple case fold key. Two runes are in the same Go `unicode.SimpleFold`
/// orbit when their keys are equal.
// PORT: the key is lower(upper(c)) with single-char mappings. U+0131
// (dotless i) has only a Turkic fold entry, so its orbit is itself, as in Go.
// Rust and Go can use different Unicode versions; this matters only for runes
// added between those versions.
fn simple_fold_key(c: char) -> char {
    if c == '\u{0131}' {
        return c;
    }
    let mut upper = c.to_uppercase();
    let u = match (upper.next(), upper.next()) {
        (Some(single), None) => single,
        _ => c,
    };
    let mut lower = u.to_lowercase();
    match (lower.next(), lower.next()) {
        (Some(single), None) => single,
        _ => u,
    }
}
