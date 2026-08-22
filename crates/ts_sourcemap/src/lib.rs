//! Source Map v3 generation with Base64 VLQ mappings.

use std::{error::Error, fmt};

/// A generated Source Map v3 payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceMap {
    pub version: u8,
    pub file: Option<String>,
    pub sources: Vec<String>,
    pub names: Vec<String>,
    pub mappings: String,
    pub sources_content: Option<Vec<String>>,
}

/// Error returned when mappings are invalid or generated positions are out of order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MappingOrderError;

impl fmt::Display for MappingOrderError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("source map mappings must be valid and generated positions monotonic")
    }
}

impl Error for MappingOrderError {}

/// Incrementally builds delta-encoded Source Map v3 mappings.
#[derive(Clone, Debug, Default)]
pub struct SourceMapBuilder {
    mappings: String,
    generated_line: u32,
    generated_column: u32,
    previous_source: i64,
    previous_original_line: i64,
    previous_original_column: i64,
    has_segment_on_line: bool,
    has_mapping: bool,
    previous_mapping_has_source: bool,
    pending: Option<PendingMapping>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PendingMapping {
    generated_line: u32,
    generated_column: u32,
    source: Option<SourcePosition>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourcePosition {
    source: u32,
    original_line: u32,
    original_column: u32,
}

impl SourceMapBuilder {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            mappings: String::new(),
            generated_line: 0,
            generated_column: 0,
            previous_source: 0,
            previous_original_line: 0,
            previous_original_column: 0,
            has_segment_on_line: false,
            has_mapping: false,
            previous_mapping_has_source: false,
            pending: None,
        }
    }

    /// Adds a generated position that does not identify an original source.
    ///
    /// # Errors
    ///
    /// Returns an error if generated positions are not monotonic.
    pub fn add_generated_mapping(
        &mut self,
        generated_line: u32,
        generated_column: u32,
    ) -> Result<(), MappingOrderError> {
        self.add_pending_mapping(generated_line, generated_column, None)
    }

    /// Adds one mapping segment.
    ///
    /// # Errors
    ///
    /// Returns an error if generated positions are not monotonic.
    pub fn add_mapping(
        &mut self,
        generated_line: u32,
        generated_column: u32,
        source: u32,
        original_line: u32,
        original_column: u32,
    ) -> Result<(), MappingOrderError> {
        self.add_pending_mapping(
            generated_line,
            generated_column,
            Some(SourcePosition {
                source,
                original_line,
                original_column,
            }),
        )
    }

    fn add_pending_mapping(
        &mut self,
        generated_line: u32,
        generated_column: u32,
        source: Option<SourcePosition>,
    ) -> Result<(), MappingOrderError> {
        let previous = self
            .pending
            .map(|mapping| (mapping.generated_line, mapping.generated_column))
            .or_else(|| {
                self.has_mapping
                    .then_some((self.generated_line, self.generated_column))
            });
        if previous.is_some_and(|position| (generated_line, generated_column) < position) {
            return Err(MappingOrderError);
        }

        if let Some(pending) = self.pending {
            let changed_position = pending.generated_line != generated_line
                || pending.generated_column != generated_column;
            let backtracked_source = source.zip(pending.source).is_some_and(|(next, previous)| {
                next.source == previous.source
                    && (next.original_line, next.original_column)
                        < (previous.original_line, previous.original_column)
            });
            if changed_position || backtracked_source {
                self.commit_pending_mapping();
            } else {
                if let Some(source) = source {
                    self.pending
                        .as_mut()
                        .expect("pending mapping exists")
                        .source = Some(source);
                }
                return Ok(());
            }
        }

        self.pending = Some(PendingMapping {
            generated_line,
            generated_column,
            source,
        });
        Ok(())
    }

    fn commit_pending_mapping(&mut self) {
        let Some(pending) = self.pending.take() else {
            return;
        };
        let duplicates_previous = self.has_mapping
            && pending.generated_line == self.generated_line
            && pending.generated_column == self.generated_column
            && match pending.source {
                None => !self.previous_mapping_has_source,
                Some(source) => {
                    self.previous_mapping_has_source
                        && i64::from(source.source) == self.previous_source
                        && i64::from(source.original_line) == self.previous_original_line
                        && i64::from(source.original_column) == self.previous_original_column
                }
            };
        if duplicates_previous {
            return;
        }

        while self.generated_line < pending.generated_line {
            self.mappings.push(';');
            self.generated_line += 1;
            self.generated_column = 0;
            self.has_segment_on_line = false;
        }
        if self.has_segment_on_line {
            self.mappings.push(',');
        }
        encode_vlq(
            i64::from(pending.generated_column) - i64::from(self.generated_column),
            &mut self.mappings,
        );
        if let Some(source) = pending.source {
            encode_vlq(
                i64::from(source.source) - self.previous_source,
                &mut self.mappings,
            );
            encode_vlq(
                i64::from(source.original_line) - self.previous_original_line,
                &mut self.mappings,
            );
            encode_vlq(
                i64::from(source.original_column) - self.previous_original_column,
                &mut self.mappings,
            );
            self.previous_source = i64::from(source.source);
            self.previous_original_line = i64::from(source.original_line);
            self.previous_original_column = i64::from(source.original_column);
        }
        self.generated_column = pending.generated_column;
        self.has_segment_on_line = true;
        self.has_mapping = true;
        self.previous_mapping_has_source = pending.source.is_some();
    }

    /// Appends delta-encoded mappings at a generated-line and source-index offset.
    ///
    /// # Errors
    ///
    /// Returns an error if a mapping is malformed or its generated position moves backward.
    pub fn append_mappings(
        &mut self,
        mappings: &str,
        generated_line_offset: u32,
        source_offset: u32,
    ) -> Result<(), MappingOrderError> {
        let mut source = 0_i64;
        let mut original_line = 0_i64;
        let mut original_column = 0_i64;
        for (line_index, line) in mappings.split(';').enumerate() {
            let mut generated_column = 0_i64;
            for segment in line.split(',').filter(|segment| !segment.is_empty()) {
                let values = decode_segment(segment).ok_or(MappingOrderError)?;
                let generated_delta = *values.first().ok_or(MappingOrderError)?;
                generated_column = generated_column
                    .checked_add(generated_delta)
                    .ok_or(MappingOrderError)?;
                let generated_line = generated_line_offset
                    .checked_add(u32::try_from(line_index).map_err(|_| MappingOrderError)?)
                    .ok_or(MappingOrderError)?;
                let generated_column =
                    u32::try_from(generated_column).map_err(|_| MappingOrderError)?;

                match values.as_slice() {
                    [_] => self.add_generated_mapping(generated_line, generated_column)?,
                    [_, source_delta, line_delta, column_delta]
                    | [_, source_delta, line_delta, column_delta, _] => {
                        source = source.checked_add(*source_delta).ok_or(MappingOrderError)?;
                        original_line = original_line
                            .checked_add(*line_delta)
                            .ok_or(MappingOrderError)?;
                        original_column = original_column
                            .checked_add(*column_delta)
                            .ok_or(MappingOrderError)?;
                        let source_index = i64::from(source_offset)
                            .checked_add(source)
                            .ok_or(MappingOrderError)?;
                        self.add_mapping(
                            generated_line,
                            generated_column,
                            u32::try_from(source_index).map_err(|_| MappingOrderError)?,
                            u32::try_from(original_line).map_err(|_| MappingOrderError)?,
                            u32::try_from(original_column).map_err(|_| MappingOrderError)?,
                        )?;
                    }
                    _ => return Err(MappingOrderError),
                }
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn finish(mut self, file: Option<String>, sources: Vec<String>) -> SourceMap {
        self.commit_pending_mapping();
        SourceMap {
            version: 3,
            file,
            sources,
            names: Vec::new(),
            mappings: self.mappings,
            sources_content: None,
        }
    }
}

const BASE64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn encode_vlq(value: i64, output: &mut String) {
    let mut value = if value < 0 {
        value.unsigned_abs().saturating_mul(2).saturating_add(1)
    } else {
        value.unsigned_abs().saturating_mul(2)
    };
    loop {
        let mut digit = value & 31;
        value >>= 5;
        if value != 0 {
            digit |= 32;
        }
        let index = usize::try_from(digit).expect("VLQ digit is at most 63");
        output.push(char::from(BASE64[index]));
        if value == 0 {
            break;
        }
    }
}

fn decode_segment(segment: &str) -> Option<Vec<i64>> {
    let mut values = Vec::new();
    let mut value = 0_u64;
    let mut shift = 0_u32;
    let mut continued = false;

    for byte in segment.bytes() {
        let digit = u64::try_from(BASE64.iter().position(|candidate| *candidate == byte)?).ok()?;
        let payload = digit & 31;
        let shifted = payload.checked_shl(shift)?;
        if shifted.checked_shr(shift)? != payload {
            return None;
        }
        value |= shifted;
        if digit & 32 == 0 {
            let magnitude = i64::try_from(value >> 1).ok()?;
            values.push(if value & 1 == 0 {
                magnitude
            } else {
                -magnitude
            });
            value = 0;
            shift = 0;
            continued = false;
        } else {
            shift = shift.checked_add(5)?;
            continued = true;
        }
    }

    (!continued).then_some(values)
}

#[cfg(test)]
mod tests {
    use super::{MappingOrderError, SourceMapBuilder};

    #[test]
    fn emits_known_vlq_segments_and_line_deltas() {
        let mut builder = SourceMapBuilder::new();
        builder.add_mapping(0, 0, 0, 0, 0).unwrap();
        builder.add_mapping(0, 10, 0, 0, 5).unwrap();
        builder.add_mapping(2, 0, 0, 1, 0).unwrap();
        let map = builder.finish(Some("out.js".into()), vec!["in.ts".into()]);
        assert_eq!(map.version, 3);
        assert_eq!(map.mappings, "AAAA,UAAK;;AACL");
    }

    #[test]
    fn rejects_non_monotonic_generated_positions() {
        let mut builder = SourceMapBuilder::new();
        builder.add_mapping(1, 4, 0, 0, 0).unwrap();
        assert_eq!(builder.add_mapping(1, 3, 0, 0, 0), Err(MappingOrderError));
        assert_eq!(builder.add_mapping(0, 9, 0, 0, 0), Err(MappingOrderError));
    }

    #[test]
    fn appends_existing_mappings_with_offsets() {
        let mut builder = SourceMapBuilder::new();
        builder.append_mappings("AAAA,IAAI;AACJ", 2, 3).unwrap();
        let map = builder.finish(None, vec![]);
        assert_eq!(map.mappings, ";;AGAA,IAAI;AACJ");
    }

    #[test]
    fn replaces_forward_source_positions_at_the_same_generated_position() {
        let mut builder = SourceMapBuilder::new();
        builder.add_mapping(0, 0, 0, 0, 0).unwrap();
        builder.add_mapping(0, 0, 0, 0, 1).unwrap();
        builder.add_mapping(0, 0, 0, 0, 2).unwrap();

        assert_eq!(builder.finish(None, vec![]).mappings, "AAAE");
    }

    #[test]
    fn preserves_backtracking_source_positions_at_the_same_generated_position() {
        let mut builder = SourceMapBuilder::new();
        builder.add_mapping(0, 0, 0, 0, 1).unwrap();
        builder.add_mapping(0, 0, 0, 0, 0).unwrap();

        assert_eq!(builder.finish(None, vec![]).mappings, "AAAC,AAAD");
    }

    #[test]
    fn preserves_generated_only_segments_when_appending_mappings() {
        let mut builder = SourceMapBuilder::new();
        builder.append_mappings("A,CAAA;A", 1, 2).unwrap();

        assert_eq!(builder.finish(None, vec![]).mappings, ";A,CEAA;A");
    }

    #[test]
    fn rejects_invalid_or_overflowing_mapping_segments() {
        for mappings in ["!", "g", "AAA", "D", "ggggggggggggggA"] {
            let mut builder = SourceMapBuilder::new();
            assert_eq!(
                builder.append_mappings(mappings, 0, 0),
                Err(MappingOrderError),
                "{mappings}"
            );
        }
    }
}
