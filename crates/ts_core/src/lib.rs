//! Shared compiler primitives.

use std::fmt;

/// A JavaScript string represented as UTF-16 code units. Unlike Rust `String`,
/// this preserves lone surrogates produced by escape sequences.
#[derive(Clone, Default, Eq, Hash, PartialEq)]
pub struct JsString(Vec<u16>);

impl JsString {
    #[must_use]
    pub fn from_utf8(value: &str) -> Self {
        Self(value.encode_utf16().collect())
    }

    #[must_use]
    pub fn from_units(units: Vec<u16>) -> Self {
        Self(units)
    }

    #[must_use]
    pub fn as_units(&self) -> &[u16] {
        &self.0
    }

    pub fn push_char(&mut self, ch: char) {
        let mut units = [0; 2];
        self.0.extend_from_slice(ch.encode_utf16(&mut units));
    }

    pub fn push_unit(&mut self, unit: u16) {
        self.0.push(unit);
    }

    #[must_use]
    pub fn to_string_lossy(&self) -> String {
        char::decode_utf16(self.0.iter().copied())
            .map(|result| result.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect()
    }
}

impl fmt::Debug for JsString {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_tuple("JsString").field(&self.0).finish()
    }
}

/// A source position measured in UTF-8 bytes, matching the native compiler.
#[derive(Clone, Copy, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct TextPos(u32);

impl TextPos {
    #[must_use]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

impl fmt::Debug for TextPos {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A half-open source range measured in UTF-8 bytes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TextRange {
    pub start: TextPos,
    pub end: TextPos,
}

impl TextRange {
    #[must_use]
    pub const fn new(start: TextPos, end: TextPos) -> Self {
        Self { start, end }
    }

    #[must_use]
    pub const fn len(self) -> u32 {
        self.end.get() - self.start.get()
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start.get() == self.end.get()
    }
}

/// A compiler diagnostic independent of rendering and localization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub range: TextRange,
    pub message: String,
}

/// Bidirectional mapping between native UTF-8 byte offsets and JavaScript
/// UTF-16 code-unit offsets.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PositionMap {
    entries: Vec<PositionMapEntry>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PositionMapEntry {
    utf8_pos: usize,
    delta: usize,
}

impl PositionMap {
    #[must_use]
    pub fn new(text: &str) -> Self {
        let mut entries = Vec::new();
        let mut delta = 0;
        for (start, ch) in text.char_indices() {
            let utf8_size = ch.len_utf8();
            let utf16_size = ch.len_utf16();
            if utf8_size != utf16_size {
                delta += utf8_size - utf16_size;
                entries.push(PositionMapEntry {
                    utf8_pos: start + utf8_size,
                    delta,
                });
            }
        }
        Self { entries }
    }

    #[must_use]
    pub fn is_ascii_only(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub fn utf8_to_utf16(&self, utf8_offset: usize) -> usize {
        let index = self
            .entries
            .partition_point(|entry| entry.utf8_pos <= utf8_offset);
        index
            .checked_sub(1)
            .map_or(utf8_offset, |index| utf8_offset - self.entries[index].delta)
    }

    #[must_use]
    pub fn utf16_to_utf8(&self, utf16_offset: usize) -> usize {
        let index = self
            .entries
            .partition_point(|entry| entry.utf8_pos - entry.delta <= utf16_offset);
        index.checked_sub(1).map_or(utf16_offset, |index| {
            utf16_offset + self.entries[index].delta
        })
    }
}

impl Diagnostic {
    #[must_use]
    pub fn new(range: TextRange, message: impl Into<String>) -> Self {
        Self {
            range,
            message: message.into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{JsString, PositionMap, TextPos, TextRange};

    #[test]
    fn ranges_are_half_open() {
        let range = TextRange::new(TextPos::new(2), TextPos::new(7));
        assert_eq!(range.len(), 5);
        assert!(!range.is_empty());
    }

    #[test]
    fn maps_ascii_without_allocated_entries() {
        let map = PositionMap::new("const answer = 42");
        assert!(map.is_ascii_only());
        assert_eq!(map.utf8_to_utf16(10), 10);
        assert_eq!(map.utf16_to_utf8(10), 10);
    }

    #[test]
    fn maps_bmp_and_astral_characters() {
        let text = "aé😀b";
        let map = PositionMap::new(text);
        assert!(!map.is_ascii_only());
        assert_eq!(map.utf8_to_utf16(text.find('b').unwrap()), 4);
        assert_eq!(map.utf16_to_utf8(4), text.find('b').unwrap());
        for utf16_offset in 0..=5 {
            assert_eq!(
                map.utf8_to_utf16(map.utf16_to_utf8(utf16_offset)),
                utf16_offset
            );
        }
    }

    #[test]
    fn javascript_strings_preserve_lone_surrogates() {
        let value = JsString::from_units(vec![0xd83e, 0xdd80, 0xd800]);
        assert_eq!(value.as_units(), &[0xd83e, 0xdd80, 0xd800]);
        assert_eq!(value.to_string_lossy(), "🦀�");
    }
}
