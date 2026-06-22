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
}

/// Error returned when generated mappings are added out of order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MappingOrderError;

impl fmt::Display for MappingOrderError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("source map generated positions must be monotonic")
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
        }
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
        if generated_line < self.generated_line
            || (self.has_mapping
                && generated_line == self.generated_line
                && generated_column < self.generated_column)
        {
            return Err(MappingOrderError);
        }
        while self.generated_line < generated_line {
            self.mappings.push(';');
            self.generated_line += 1;
            self.generated_column = 0;
            self.has_segment_on_line = false;
        }
        if self.has_segment_on_line {
            self.mappings.push(',');
        }
        encode_vlq(
            i64::from(generated_column) - i64::from(self.generated_column),
            &mut self.mappings,
        );
        encode_vlq(i64::from(source) - self.previous_source, &mut self.mappings);
        encode_vlq(
            i64::from(original_line) - self.previous_original_line,
            &mut self.mappings,
        );
        encode_vlq(
            i64::from(original_column) - self.previous_original_column,
            &mut self.mappings,
        );
        self.generated_column = generated_column;
        self.previous_source = i64::from(source);
        self.previous_original_line = i64::from(original_line);
        self.previous_original_column = i64::from(original_column);
        self.has_segment_on_line = true;
        self.has_mapping = true;
        Ok(())
    }

    #[must_use]
    pub fn finish(self, file: Option<String>, sources: Vec<String>) -> SourceMap {
        SourceMap {
            version: 3,
            file,
            sources,
            names: Vec::new(),
            mappings: self.mappings,
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
}
