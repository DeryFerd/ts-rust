use crate::ls::autoimport::prelude::*;

use crate::gostd::unicode;

// Port of Go `ls/autoimport/index.go`.
//
// PORT: Go `rune` keys are `char`. Names are Go strings in the port form
// (see `scanner_util::GO_STRING_MARKER`). Go reads each byte that is not
// valid UTF-8 as `utf8.RuneError`, for example the byte 0xFE that starts Go
// internal symbol names (`INTERNAL_SYMBOL_NAME_PREFIX`). The helpers below
// read the units of the port form: `decode_rune_in_string`, `go_runes`
// (Go `range`) and `go_map_runes` (Go `strings.Map`), which the crate
// prelude exports from `scanner_util`.

// Go: ls/autoimport/index.go:12 Named
// Named is a constraint for types that can provide their name.
pub trait Named {
    fn name(&self) -> String;
}

impl Named for Rc<Export> {
    fn name(&self) -> String {
        Export::name(self)
    }
}

// Go: ls/autoimport/index.go:19 Index
// Index stores entries with an index mapping uppercase letters to entries whose name
// starts with that letter, and lowercase letters to entries whose name contains a
// word starting with that letter.
// PORT: Go `map[rune][]int` is `FxHashMap<char, Vec<i32>>`; a Go nil map is
// an empty map. The owning bucket holds a shared index as
// `Rc<RefCell<Index<Rc<Export>>>>` (see `RegistryBucket`).
#[derive(Clone, Debug)]
pub struct Index<T: Named> {
    pub entries: Vec<T>,
    pub index: FxHashMap<char, Vec<i32>>,
}

impl<T: Named> Default for Index<T> {
    fn default() -> Self {
        Index {
            entries: Vec::new(),
            index: FxHashMap::default(),
        }
    }
}

impl<T: Named + Clone> Index<T> {
    // Go: ls/autoimport/index.go:24 Find
    // PORT: Go returns a nil slice for no results; that is an empty `Vec`.
    pub fn find(&self, name: &str, case_sensitive: bool) -> Vec<T> {
        if self.entries.is_empty() || name.is_empty() {
            return Vec::new();
        }
        let first_rune = decode_rune_in_string(name, 0).0;
        if first_rune == char::REPLACEMENT_CHARACTER {
            return Vec::new();
        }
        let first_rune_upper = unicode::to_upper(first_rune);
        let Some(candidates) = self.index.get(&first_rune_upper) else {
            return Vec::new();
        };

        let mut results: Vec<T> = Vec::new();
        for &entry_index in candidates {
            let entry = &self.entries[entry_index as usize];
            let entry_name = entry.name();
            // PORT: Go `strings.EqualFold` is `stringutil_ls::equate_string_case_insensitive`
            // (Go `stringutil.EquateStringCaseInsensitive` is `strings.EqualFold`).
            if (case_sensitive && entry_name == name)
                || (!case_sensitive
                    && crate::frontend::stringutil_ls::equate_string_case_insensitive(
                        &entry_name,
                        name,
                    ))
            {
                results.push(entry.clone());
            }
        }

        results
    }

    // Go: ls/autoimport/index.go:54 SearchWordPrefix
    // SearchWordPrefix returns each entry whose name contains a word beginning with
    // the first character of 'prefix', and whose name contains all characters
    // of 'prefix' in order (case-insensitive). If 'filter' is provided, only entries
    // for which filter(entry) returns true are included.
    // PORT: Go returns the shared `idx.entries` slice for an empty prefix; the
    // port returns a copy. Go nil results are an empty `Vec`.
    pub fn search_word_prefix(&self, prefix: &str) -> Vec<T> {
        if self.entries.is_empty() {
            return Vec::new();
        }

        if prefix.is_empty() {
            return self.entries.clone();
        }

        let prefix = strings_to_lower(prefix);
        let (first_rune, _) = decode_rune_in_string(&prefix, 0);
        if first_rune == char::REPLACEMENT_CHARACTER {
            return Vec::new();
        }

        let first_rune_upper = unicode::to_upper(first_rune);
        let first_rune_lower = unicode::to_lower(first_rune);

        // Look up entries that have words starting with this letter
        let mut word_starts: &[i32] = &[];
        let name_starts: &[i32] = self
            .index
            .get(&first_rune_upper)
            .map_or(&[][..], |v| v.as_slice());
        if first_rune_upper != first_rune_lower {
            word_starts = self
                .index
                .get(&first_rune_lower)
                .map_or(&[][..], |v| v.as_slice());
        }
        let count = name_starts.len() + word_starts.len();
        if count == 0 {
            return Vec::new();
        }

        // Filter entries by checking if they contain all characters in order
        let mut results: Vec<T> = Vec::with_capacity(count);
        for starts in [name_starts, word_starts] {
            for &i in starts {
                let entry = &self.entries[i as usize];
                if contains_chars_in_order(&entry.name(), &prefix) {
                    results.push(entry.clone());
                }
            }
        }
        results
    }

    // Go: ls/autoimport/index.go:114 insertAsWords
    // insertAsWords adds a value to the index keyed by the first letter of each word in its name.
    pub fn insert_as_words(&mut self, value: T) {
        // Go: `if idx.index == nil { idx.index = make(map[rune][]int) }`. The
        // port's map always exists.

        let name = value.name();
        if name.is_empty() {
            crate::core::go_panic("Cannot index entry with empty name".to_string());
        }
        let entry_index = self.entries.len() as i32;
        self.entries.push(value);

        let indices = word_indices(&name);
        let mut seen_runes: FxHashMap<char, bool> = FxHashMap::default();

        for (i, &start) in indices.iter().enumerate() {
            // Go: substr := name[start:]; utf8.DecodeRuneInString(substr)
            let (mut first_rune, _) = decode_rune_in_string(&name, start as usize);
            if first_rune == char::REPLACEMENT_CHARACTER {
                continue;
            }
            if i == 0 {
                // Name start keyed by uppercase
                first_rune = unicode::to_upper(first_rune);
                self.index.entry(first_rune).or_default().push(entry_index);
                seen_runes.insert(first_rune, true); // (Still set seenRunes in case first character is non-alphabetic)
            } else {
                // Subsequent word starts keyed by lowercase
                first_rune = unicode::to_lower(first_rune);
                if !seen_runes.get(&first_rune).copied().unwrap_or(false) {
                    self.index.entry(first_rune).or_default().push(entry_index);
                    seen_runes.insert(first_rune, true);
                }
            }
        }
    }

    // Go: ls/autoimport/index.go:152 Clone
    // Clone creates a new Index containing only entries for which filter returns true.
    // PORT: Go allows a nil receiver (`idx == nil` returns nil); `idx` is
    // `None` for it, and the nil result is `None`. `clone_` because
    // `Clone::clone` is taken.
    pub fn clone_(idx: Option<&Index<T>>, filter: &mut dyn FnMut(&T) -> bool) -> Option<Index<T>> {
        let idx = idx?;

        let mut new_idx = Index {
            entries: Vec::with_capacity(idx.entries.len()),
            index: FxHashMap::default(),
        };
        new_idx.index.reserve(idx.index.len());

        // Build mapping from old index to new index for filtered entries
        let mut old_to_new: FxHashMap<i32, i32> = FxHashMap::default();
        old_to_new.reserve(idx.entries.len());
        for (old_index, entry) in idx.entries.iter().enumerate() {
            if filter(entry) {
                let new_index = new_idx.entries.len() as i32;
                new_idx.entries.push(entry.clone());
                old_to_new.insert(old_index as i32, new_index);
            }
        }

        // Rebuild the index with remapped indices
        for (r, old_indices) in &idx.index {
            let mut new_indices: Vec<i32> = Vec::with_capacity(old_indices.len());
            for old_index in old_indices {
                if let Some(&new_index) = old_to_new.get(old_index) {
                    new_indices.push(new_index);
                }
            }
            if !new_indices.is_empty() {
                new_idx.index.insert(*r, new_indices);
            }
        }

        Some(new_idx)
    }
}

// Go: ls/autoimport/index.go:97 containsCharsInOrder
// containsCharsInOrder checks if str contains all characters from pattern in order (case-insensitive).
pub fn contains_chars_in_order(str: &str, pattern: &str) -> bool {
    let str = strings_to_lower(str);
    let pattern = strings_to_lower(pattern);

    let mut pattern_idx: usize = 0;
    // PORT: Go `range str` reads runes; `go_runes` reads the port form units.
    for ch in go_runes(&str) {
        if pattern_idx < pattern.len() {
            let (pattern_rune, size) = decode_rune_in_string(&pattern, pattern_idx);
            if ch == pattern_rune {
                pattern_idx += size;
            }
        }
    }
    pattern_idx == pattern.len()
}

/// Go `utf8.DecodeRuneInString(s[pos:])` as a `char` and a byte width.
// PORT: `s` is the port form of a Go string (see
// `scanner_util::GO_STRING_MARKER`) and `pos` a unit boundary. Go decodes an
// invalid byte, such as the 0xFE of an internal symbol name, as
// `utf8.RuneError`. `GoUnit::InvalidByte` and `GoUnit::Surrogate` (3 invalid
// bytes in Go) give U+FFFD here. The width is the size of the unit in `s`,
// so the caller stays on a unit boundary; each caller reads only the rune of
// a surrogate unit, never the Go width of 1.
fn decode_rune_in_string(s: &str, pos: usize) -> (char, usize) {
    // Go returns `(RuneError, 0)` for an empty input.
    if pos >= s.len() {
        return (char::REPLACEMENT_CHARACTER, 0);
    }
    match go_unit_at(s, pos) {
        (GoUnit::Char(c), size) => (c, size),
        (GoUnit::InvalidByte(_) | GoUnit::Surrogate(_), size) => {
            (char::REPLACEMENT_CHARACTER, size)
        }
    }
}

/// Go `strings.ToLower`: `unicode.ToLower` on each rune.
// PORT: not `str::to_lowercase`, which maps a final sigma to U+03C2 and
// U+0130 to two runes. Go maps each rune on its own. Go `strings.ToLower`
// of a non-ASCII string is `strings.Map(unicode.ToLower, s)`, which writes
// U+FFFD for each invalid byte; `go_map_runes` does that on the port form.
fn strings_to_lower(s: &str) -> String {
    go_map_runes(s, unicode::to_lower)
}
