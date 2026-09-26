//! Port of Go `sourcemap/decoder.go`, plus the Go JSON v2 default decoding
//! of `RawSourceMap` (Go decodes it by reflection).

use crate::prelude::*;

use crate::frontend::json::{JsonDecoder, JsonError, JsonToken, UnmarshalerFrom};
use crate::gostd::GoError;
use crate::sourcemap::generator::{NameIndex, RawSourceMap, SourceIndex};

// Go: sourcemap/decoder.go:10 Mapping
// PORT: Go `int` and `core.UTF16Offset` (also `int`) fields are `i32`, like
// the generator. The decoder keeps Go `int` (64-bit) state and truncates
// when it captures a mapping, which only a corrupt map reaches.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Mapping {
    pub generated_line: i32,
    pub generated_character: i32,
    pub source_index: SourceIndex,
    pub source_line: i32,
    pub source_character: i32,
    pub name_index: NameIndex,
}

impl Mapping {
    // Go: sourcemap/decoder.go:19 Equals
    #[must_use]
    pub fn equals(&self, other: &Mapping) -> bool {
        std::ptr::eq(self, other)
            || self.generated_line == other.generated_line
                && self.generated_character == other.generated_character
                && self.source_index == other.source_index
                && self.source_line == other.source_line
                && self.source_character == other.source_character
                && self.name_index == other.name_index
    }

    // Go: sourcemap/decoder.go:28 IsSourceMapping
    #[must_use]
    pub fn is_source_mapping(&self) -> bool {
        self.source_index != MISSING_SOURCE
            && self.source_line != MISSING_LINE_OR_COLUMN
            && self.source_character != MISSING_UTF16_COLUMN
    }
}

// Go: sourcemap/decoder.go:34 MissingSource, MissingName, MissingLineOrColumn, MissingUTF16Column
pub const MISSING_SOURCE: SourceIndex = -1;
pub const MISSING_NAME: NameIndex = -1;
pub const MISSING_LINE_OR_COLUMN: i32 = -1;
pub const MISSING_UTF16_COLUMN: i32 = -1;

// Go: sourcemap/decoder.go:41 MappingsDecoder
// PORT: the running values are Go `int` (64-bit) as `i64`, so the sign checks
// and wrap-around match Go. `pos` indexes the bytes of `mappings`. Go
// `mappingArena` only allocates the returned mappings; they are returned by
// value here.
#[derive(Clone, Debug, Default)]
pub struct MappingsDecoder {
    mappings: String,
    done: bool,
    pos: usize,
    generated_line: i64,
    generated_character: i64,
    source_index: i64,
    source_line: i64,
    source_character: i64,
    name_index: i64,
    error: Option<GoError>,
}

// Go: sourcemap/decoder.go:55 DecodeMappings
#[must_use]
pub fn decode_mappings(mappings: &str) -> MappingsDecoder {
    MappingsDecoder {
        mappings: mappings.to_string(),
        ..MappingsDecoder::default()
    }
}

impl MappingsDecoder {
    // Go: sourcemap/decoder.go:59 MappingsString
    #[must_use]
    pub fn mappings_string(&self) -> &str {
        &self.mappings
    }

    // Go: sourcemap/decoder.go:63 Pos
    #[must_use]
    pub fn pos(&self) -> i32 {
        self.pos as i32
    }

    // Go: sourcemap/decoder.go:67 Error
    #[must_use]
    pub fn error(&self) -> Option<GoError> {
        self.error.clone()
    }

    // Go: sourcemap/decoder.go:71 State
    pub fn state(&self) -> Mapping {
        self.capture_mapping(true /*hasSource*/, true /*hasName*/)
    }

    // Go: sourcemap/decoder.go:75 Values
    // PORT: Go returns an `iter.Seq`; here an iterator over `next`.
    pub fn values(&mut self) -> impl Iterator<Item = Mapping> + '_ {
        std::iter::from_fn(move || {
            let (value, done) = self.next();
            if done { None } else { value }
        })
    }

    // Go: sourcemap/decoder.go:85 Next
    // PORT: Go returns `(*Mapping, done)`; a nil mapping is `None`.
    pub fn next(&mut self) -> (Option<Mapping>, bool) {
        while !self.done && self.pos < self.mappings.len() {
            let ch = self.mappings.as_bytes()[self.pos];
            if ch == b';' {
                // new line
                self.generated_line = self.generated_line.wrapping_add(1);
                self.generated_character = 0;
                self.pos += 1;
                continue;
            }

            if ch == b',' {
                // Next entry is on same line - no action needed
                self.pos += 1;
                continue;
            }

            let mut has_source = false;
            let mut has_name = false;
            let value = self.base64_vlq_format_decode();
            self.generated_character = self.generated_character.wrapping_add(value);
            if self.has_reported_error() {
                return self.stop_iterating();
            }
            if self.generated_character < 0 {
                return self.set_error_and_stop_iterating("Invalid generatedCharacter found");
            }

            if !self.is_source_mapping_segment_end() {
                has_source = true;

                let value = self.base64_vlq_format_decode();
                self.source_index = self.source_index.wrapping_add(value);
                if self.has_reported_error() {
                    return self.stop_iterating();
                }
                if self.source_index < 0 {
                    return self.set_error_and_stop_iterating("Invalid sourceIndex found");
                }
                if self.is_source_mapping_segment_end() {
                    return self.set_error_and_stop_iterating(
                        "Unsupported Format: No entries after sourceIndex",
                    );
                }

                let value = self.base64_vlq_format_decode();
                self.source_line = self.source_line.wrapping_add(value);
                if self.has_reported_error() {
                    return self.stop_iterating();
                }
                if self.source_line < 0 {
                    return self.set_error_and_stop_iterating("Invalid sourceLine found");
                }
                if self.is_source_mapping_segment_end() {
                    return self.set_error_and_stop_iterating(
                        "Unsupported Format: No entries after sourceLine",
                    );
                }

                let value = self.base64_vlq_format_decode();
                self.source_character = self.source_character.wrapping_add(value);
                if self.has_reported_error() {
                    return self.stop_iterating();
                }
                if self.source_character < 0 {
                    return self.set_error_and_stop_iterating("Invalid sourceCharacter found");
                }

                if !self.is_source_mapping_segment_end() {
                    has_name = true;
                    let value = self.base64_vlq_format_decode();
                    self.name_index = self.name_index.wrapping_add(value);
                    if self.has_reported_error() {
                        return self.stop_iterating();
                    }
                    if self.name_index < 0 {
                        return self.set_error_and_stop_iterating("Invalid nameIndex found");
                    }

                    if !self.is_source_mapping_segment_end() {
                        return self.set_error_and_stop_iterating(
                            "Unsupported Error Format: Entries after nameIndex",
                        );
                    }
                }
            }

            return (Some(self.capture_mapping(has_source, has_name)), false);
        }

        self.stop_iterating()
    }

    // Go: sourcemap/decoder.go:167 captureMapping
    fn capture_mapping(&self, has_source: bool, has_name: bool) -> Mapping {
        Mapping {
            generated_line: self.generated_line as i32,
            generated_character: self.generated_character as i32,
            source_index: if has_source {
                self.source_index as SourceIndex
            } else {
                MISSING_SOURCE
            },
            source_line: if has_source {
                self.source_line as i32
            } else {
                MISSING_LINE_OR_COLUMN
            },
            source_character: if has_source {
                self.source_character as i32
            } else {
                MISSING_UTF16_COLUMN
            },
            name_index: if has_name {
                self.name_index as NameIndex
            } else {
                MISSING_NAME
            },
        }
    }

    // Go: sourcemap/decoder.go:178 stopIterating
    fn stop_iterating(&mut self) -> (Option<Mapping>, bool) {
        self.done = true;
        (None, true)
    }

    // Go: sourcemap/decoder.go:183 setError
    fn set_error(&mut self, err: &str) {
        self.error = Some(crate::gostd::errors::new(err));
    }

    // Go: sourcemap/decoder.go:187 setErrorAndStopIterating
    fn set_error_and_stop_iterating(&mut self, err: &str) -> (Option<Mapping>, bool) {
        self.set_error(err);
        self.stop_iterating()
    }

    // Go: sourcemap/decoder.go:192 hasReportedError
    fn has_reported_error(&self) -> bool {
        self.error.is_some()
    }

    // Go: sourcemap/decoder.go:196 isSourceMappingSegmentEnd
    fn is_source_mapping_segment_end(&self) -> bool {
        let b = self.mappings.as_bytes();
        self.pos == b.len() || b[self.pos] == b',' || b[self.pos] == b';'
    }

    // Go: sourcemap/decoder.go:200 base64VLQFormatDecode
    // PORT: Go `int` is `i64`. A Go shift by 64 or more gives 0.
    fn base64_vlq_format_decode(&mut self) -> i64 {
        let mut more_digits = true;
        let mut shift_count: u32 = 0;
        let mut value: i64 = 0;
        while more_digits {
            if self.pos >= self.mappings.len() {
                self.set_error("Error in decoding base64VLQFormatDecode, past the mapping string");
                return -1;
            }

            // 6 digit number
            let current_byte = base64_format_decode(self.mappings.as_bytes()[self.pos]);
            if current_byte == -1 {
                self.set_error("Invalid character in VLQ");
                return -1;
            }

            // If msb is set, we still have more bits to continue
            more_digits = (current_byte & 32) != 0;

            // least significant 5 bits are the next msbs in the final value.
            value |= (current_byte & 31).checked_shl(shift_count).unwrap_or(0);
            shift_count = shift_count.saturating_add(5);

            // Go: the `d.pos++` post statement of the for loop.
            self.pos += 1;
        }

        // Least significant bit if 1 represents negative and rest of the msb is actual absolute value
        if (value & 1) == 0 {
            // + number
            value >>= 1;
        } else {
            // - number
            value >>= 1;
            value = value.wrapping_neg();
        }

        value
    }
}

// Go: sourcemap/decoder.go:238 base64FormatDecode
fn base64_format_decode(ch: u8) -> i64 {
    match ch {
        b'A'..=b'Z' => i64::from(ch - b'A'),
        b'a'..=b'z' => i64::from(ch - b'a' + 26),
        b'0'..=b'9' => i64::from(ch - b'0' + 52),
        b'+' => 62,
        b'/' => 63,
        _ => -1,
    }
}

// Go JSON v2 default struct decoding of `RawSourceMap` (Go
// `json.Unmarshal(contents, &RawSourceMap{})` in source_mapper.go).
// PORT: Go decodes the struct by reflection. The v2 default rules: `null`
// sets the zero value; an object sets fields by exact (case-sensitive) name
// and skips unknown names; any duplicate member name is an error (the
// decoder's name check covers known and unknown names, as Go's `seenIdxs`
// and namespace checks do); any other kind is an error. Every error is
// fatal. Field values use the default arshalers: `version` is an integer
// (`i32`, integer syntax and range checked; a value outside `i32` is an
// error, which callers treat like Go's `Version != 3`), `sources` and
// `names` are string slices (`null` gives an empty slice), and
// `sourcesContent` is `[]*string` (`null` gives `None`).
impl UnmarshalerFrom for RawSourceMap {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let tok = dec.read_token()?;
        match tok {
            JsonToken::Null => {
                *self = RawSourceMap::default();
                Ok(())
            }
            JsonToken::BeginObject => {
                while dec.peek_kind() != b'}' {
                    // Process the object member name.
                    let JsonToken::String(name) = dec.read_token()? else {
                        return Err(JsonError {
                            message: "object member name must be a string".to_string(),
                        });
                    };
                    // Process the object member value.
                    match name.as_str() {
                        "version" => self.version.unmarshal_json_from(dec)?,
                        "file" => self.file.unmarshal_json_from(dec)?,
                        "sourceRoot" => self.source_root.unmarshal_json_from(dec)?,
                        "sources" => self.sources.unmarshal_json_from(dec)?,
                        "names" => self.names.unmarshal_json_from(dec)?,
                        "mappings" => self.mappings.unmarshal_json_from(dec)?,
                        "sourcesContent" => self.sources_content.unmarshal_json_from(dec)?,
                        // Skip unknown value since we have no place to store it.
                        _ => dec.skip_value()?,
                    }
                }
                dec.read_token()?;
                Ok(())
            }
            _ => {
                // Go `newUnmarshalErrorAfterWithSkipping`.
                if tok == JsonToken::BeginArray {
                    while dec.peek_kind() != b']' {
                        dec.skip_value()?;
                    }
                    dec.read_token()?;
                }
                Err(JsonError {
                    message: "cannot unmarshal JSON value into Go sourcemap.RawSourceMap"
                        .to_string(),
                })
            }
        }
    }
}
