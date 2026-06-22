//! Parsing for TypeScript's directive-based compiler test fixtures.
//!
//! A fixture can describe one source file directly, or several virtual files
//! separated by `// @filename: path` directives. Other directives are retained
//! as name/value metadata for the compiler harness.

use std::{fmt, ops::Range, path::PathBuf};

/// A parsed compiler test case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Case {
    /// Path of the fixture containing the test case.
    pub path: PathBuf,
    /// Exact, unmodified contents of the fixture.
    pub source_text: String,
    /// Directives in source order, including `filename` directives.
    pub directives: Vec<Directive>,
    /// Source units in compilation order.
    pub units: Vec<Unit>,
}

impl Case {
    /// Parses one compiler test fixture.
    ///
    /// # Errors
    ///
    /// Returns an error when a `filename` directive has an empty value.
    pub fn parse(
        path: impl Into<PathBuf>,
        source_text: impl Into<String>,
    ) -> Result<Self, ParseError> {
        let path = path.into();
        let source_text = source_text.into();
        let mut directives = Vec::new();
        let mut units = Vec::new();
        let mut current = UnitBuilder::new(path.clone(), 1, false);
        let mut byte_offset = 0;

        for (line_index, line_with_ending) in source_text.split_inclusive('\n').enumerate() {
            let line_number = line_index + 1;
            let line = line_with_ending
                .strip_suffix('\n')
                .unwrap_or(line_with_ending)
                .strip_suffix('\r')
                .unwrap_or_else(|| {
                    line_with_ending
                        .strip_suffix('\n')
                        .unwrap_or(line_with_ending)
                });

            if let Some((name, value)) = parse_directive_line(line) {
                let directive = Directive {
                    name: name.to_owned(),
                    value: value.to_owned(),
                    line: line_number,
                    byte_range: byte_offset..byte_offset + line.len(),
                    raw_text: line.to_owned(),
                };

                if directive.is_filename() {
                    if directive.value.is_empty() {
                        return Err(ParseError::EmptyFileName { line: line_number });
                    }

                    if current.explicit || current.has_source() {
                        units.push(current.finish());
                    }
                    current = UnitBuilder::new(
                        PathBuf::from(&directive.value),
                        line_number.saturating_add(1),
                        true,
                    );
                }
                directives.push(directive);
            } else {
                current.source_text.push_str(line_with_ending);
            }

            byte_offset += line_with_ending.len();
        }

        // `split_inclusive` yields no item for an empty source. It also handles a
        // final non-newline-terminated line, so no separate tail pass is needed.
        if current.explicit || current.has_source() || units.is_empty() {
            units.push(current.finish());
        }

        Ok(Self {
            path,
            source_text,
            directives,
            units,
        })
    }

    /// Returns all values of a directive, matching names case-insensitively.
    pub fn directive_values<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a str> + 'a {
        self.directives
            .iter()
            .filter(move |directive| directive.name.eq_ignore_ascii_case(name))
            .map(|directive| directive.value.as_str())
    }
}

/// One virtual source file declared by a fixture.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unit {
    /// Virtual path used by the compiler harness.
    pub path: PathBuf,
    /// Source text with harness directive lines removed. Line endings and all
    /// other bytes are preserved.
    pub source_text: String,
    /// One-based fixture line at which this unit's source begins.
    pub start_line: usize,
}

/// One `// @name: value` compiler test directive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Directive {
    /// Directive name as written, without `@`.
    pub name: String,
    /// Trimmed directive value.
    pub value: String,
    /// One-based line number in the fixture.
    pub line: usize,
    /// Half-open byte range of the directive line, excluding its line ending.
    pub byte_range: Range<usize>,
    /// Exact directive line, excluding its line ending.
    pub raw_text: String,
}

impl Directive {
    /// Whether this directive starts a new virtual source file.
    #[must_use]
    pub fn is_filename(&self) -> bool {
        self.name.eq_ignore_ascii_case("filename")
    }
}

/// A malformed fixture directive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    /// A `filename` directive did not specify a virtual path.
    EmptyFileName { line: usize },
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyFileName { line } => {
                write!(formatter, "empty @filename directive on line {line}")
            }
        }
    }
}

impl std::error::Error for ParseError {}

struct UnitBuilder {
    path: PathBuf,
    source_text: String,
    start_line: usize,
    explicit: bool,
}

impl UnitBuilder {
    fn new(path: PathBuf, start_line: usize, explicit: bool) -> Self {
        Self {
            path,
            source_text: String::new(),
            start_line,
            explicit,
        }
    }

    fn has_source(&self) -> bool {
        !self.source_text.trim().is_empty()
    }

    fn finish(self) -> Unit {
        Unit {
            path: self.path,
            source_text: self.source_text,
            start_line: self.start_line,
        }
    }
}

fn parse_directive_line(line: &str) -> Option<(&str, &str)> {
    let comment = line.trim_start().strip_prefix("//")?.trim_start();
    let directive = comment.strip_prefix('@')?;
    let (name, value) = directive.split_once(':')?;
    let name = name.trim();
    if name.is_empty() || !name.chars().all(is_directive_name_character) {
        return None;
    }
    Some((name, value.trim()))
}

fn is_directive_name_character(character: char) -> bool {
    character.is_ascii_alphanumeric() || matches!(character, '_' | '-')
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{Case, ParseError};

    #[test]
    fn parses_single_file_and_preserves_original_source() {
        let source = "// @target: esnext\r\n// @strict: true\r\n\r\nconst answer = 42;\r\n";
        let case = Case::parse("tests/cases/compiler/simple.ts", source).unwrap();

        assert_eq!(case.path, Path::new("tests/cases/compiler/simple.ts"));
        assert_eq!(case.source_text, source);
        assert_eq!(case.units.len(), 1);
        assert_eq!(case.units[0].path, case.path);
        assert_eq!(case.units[0].source_text, "\r\nconst answer = 42;\r\n");
        assert_eq!(
            case.directive_values("TARGET").collect::<Vec<_>>(),
            ["esnext"]
        );
        assert_eq!(case.directives[1].line, 2);
        assert_eq!(case.directives[1].raw_text, "// @strict: true");
    }

    #[test]
    fn parses_multiple_virtual_files_and_options() {
        let source = concat!(
            "// @target: esnext\n",
            "// @module: preserve, commonjs\n",
            "\n",
            "// @filename: /src/fileA.ts\n",
            "export interface Person { name: string }\n",
            "// @Filename: ./fileB.js\n",
            "/** @param {import('./fileA').Person} person */\n",
            "export function greet(person) {}\n",
        );
        let case = Case::parse("multiFile.ts", source).unwrap();

        assert_eq!(case.units.len(), 2);
        assert_eq!(case.units[0].path, Path::new("/src/fileA.ts"));
        assert_eq!(
            case.units[0].source_text,
            "export interface Person { name: string }\n"
        );
        assert_eq!(case.units[0].start_line, 5);
        assert_eq!(case.units[1].path, Path::new("./fileB.js"));
        assert_eq!(
            case.units[1].source_text,
            "/** @param {import('./fileA').Person} person */\nexport function greet(person) {}\n"
        );
        assert_eq!(case.units[1].start_line, 7);
        assert_eq!(case.directives.len(), 4);
        assert!(case.directives[2].is_filename());
    }

    #[test]
    fn retains_substantive_implicit_unit_before_named_units() {
        let source = "const implicit = 1;\n// @filename: named.ts\nconst named = 2;";
        let case = Case::parse("mixed.ts", source).unwrap();

        assert_eq!(case.units.len(), 2);
        assert_eq!(case.units[0].path, Path::new("mixed.ts"));
        assert_eq!(case.units[0].source_text, "const implicit = 1;\n");
        assert_eq!(case.units[1].path, Path::new("named.ts"));
        assert_eq!(case.units[1].source_text, "const named = 2;");
    }

    #[test]
    fn ignores_comment_text_that_is_not_a_directive() {
        let source = "// @not a directive\n// ordinary comment\nconst value = 1;";
        let case = Case::parse("comments.ts", source).unwrap();

        assert!(case.directives.is_empty());
        assert_eq!(case.units[0].source_text, source);
    }

    #[test]
    fn rejects_an_empty_virtual_filename() {
        let error = Case::parse("bad.ts", "// @filename:   \nconst value = 1;").unwrap_err();

        assert_eq!(error, ParseError::EmptyFileName { line: 1 });
        assert_eq!(error.to_string(), "empty @filename directive on line 1");
    }

    #[test]
    fn represents_an_empty_case_as_one_empty_unit() {
        let case = Case::parse("empty.ts", "").unwrap();

        assert_eq!(case.units.len(), 1);
        assert_eq!(case.units[0].path, Path::new("empty.ts"));
        assert!(case.units[0].source_text.is_empty());
    }
}
