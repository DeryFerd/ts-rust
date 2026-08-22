//! TypeScript diagnostic messages and rendered diagnostic instances.

mod catalog;

use std::{error::Error, fmt};

pub use catalog::CATALOG;

/// TypeScript's four diagnostic severity categories.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Category {
    Warning = 0,
    Error = 1,
    Suggestion = 2,
    Message = 3,
}

impl Category {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Warning => "warning",
            Self::Error => "error",
            Self::Suggestion => "suggestion",
            Self::Message => "message",
        }
    }
}

impl fmt::Display for Category {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

/// A catalog entry from TypeScript's diagnosticMessages.json.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Message {
    code: u32,
    category: Category,
    key: &'static str,
    text: &'static str,
    reports_unnecessary: bool,
    elided_in_compatibility_pyramid: bool,
    reports_deprecated: bool,
}

impl Message {
    #[doc(hidden)]
    #[must_use]
    pub const fn new(
        code: u32,
        category: Category,
        key: &'static str,
        text: &'static str,
        reports_unnecessary: bool,
        elided_in_compatibility_pyramid: bool,
        reports_deprecated: bool,
    ) -> Self {
        Self {
            code,
            category,
            key,
            text,
            reports_unnecessary,
            elided_in_compatibility_pyramid,
            reports_deprecated,
        }
    }

    #[must_use]
    pub const fn code(self) -> u32 {
        self.code
    }

    #[must_use]
    pub const fn category(self) -> Category {
        self.category
    }

    #[must_use]
    pub const fn key(self) -> &'static str {
        self.key
    }

    #[must_use]
    pub const fn text(self) -> &'static str {
        self.text
    }

    #[must_use]
    pub const fn reports_unnecessary(self) -> bool {
        self.reports_unnecessary
    }

    #[must_use]
    pub const fn elided_in_compatibility_pyramid(self) -> bool {
        self.elided_in_compatibility_pyramid
    }

    #[must_use]
    pub const fn reports_deprecated(self) -> bool {
        self.reports_deprecated
    }

    /// Formats numbered placeholders such as {0} and {1}.
    ///
    /// # Errors
    ///
    /// Returns an error if the message references an argument that was not supplied.
    pub fn format(self, arguments: &[String]) -> Result<String, FormatError> {
        if arguments.is_empty() {
            return Ok(self.text.to_owned());
        }

        let mut output = String::with_capacity(self.text.len());
        let mut remaining = self.text;
        while let Some(open) = remaining.find('{') {
            output.push_str(&remaining[..open]);
            remaining = &remaining[open + 1..];
            let digits = remaining.bytes().take_while(u8::is_ascii_digit).count();
            if digits == 0 || remaining.as_bytes().get(digits) != Some(&b'}') {
                output.push('{');
                continue;
            }

            let index_text = &remaining[..digits];
            let Ok(index) = index_text.parse::<usize>() else {
                output.push('{');
                continue;
            };
            let Some(argument) = arguments.get(index) else {
                return Err(FormatError {
                    code: self.code,
                    argument_index: index,
                });
            };
            output.push_str(argument);
            remaining = &remaining[digits + 1..];
        }
        output.push_str(remaining);
        Ok(output)
    }
}

/// One diagnostic occurrence with formatting arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub message: &'static Message,
    pub arguments: Vec<String>,
    pub details: Vec<String>,
}

impl Diagnostic {
    #[must_use]
    pub const fn new(message: &'static Message) -> Self {
        Self {
            message,
            arguments: Vec::new(),
            details: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_arguments(
        message: &'static Message,
        arguments: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self {
            message,
            arguments: arguments.into_iter().map(Into::into).collect(),
            details: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_details(mut self, details: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.details = details.into_iter().map(Into::into).collect();
        self
    }

    #[must_use]
    pub const fn code(&self) -> u32 {
        self.message.code()
    }

    #[must_use]
    pub const fn category(&self) -> Category {
        self.message.category()
    }

    /// Renders the diagnostic's English text.
    ///
    /// # Errors
    ///
    /// Returns an error when a required formatting argument is absent.
    pub fn render(&self) -> Result<String, FormatError> {
        let mut rendered = self.message.format(&self.arguments)?;
        for detail in &self.details {
            rendered.push('\n');
            rendered.push_str(detail);
        }
        Ok(rendered)
    }
}

/// A missing numbered diagnostic formatting argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FormatError {
    pub code: u32,
    pub argument_index: usize,
}

impl fmt::Display for FormatError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "diagnostic TS{} requires formatting argument {}",
            self.code, self.argument_index
        )
    }
}

impl Error for FormatError {}

/// Looks up a diagnostic message by its stable TypeScript code.
#[must_use]
pub fn message_by_code(code: u32) -> Option<&'static Message> {
    CATALOG
        .binary_search_by_key(&code, |message| message.code())
        .ok()
        .map(|index| &CATALOG[index])
}

/// Looks up a diagnostic message by its generated localization key.
#[must_use]
pub fn message_by_key(key: &str) -> Option<&'static Message> {
    CATALOG.iter().find(|message| message.key() == key)
}

#[cfg(test)]
mod tests {
    use super::{CATALOG, Category, Diagnostic, message_by_code, message_by_key};

    #[test]
    fn generated_catalog_is_complete_and_sorted() {
        assert_eq!(CATALOG.len(), 2_153);
        assert!(
            CATALOG
                .windows(2)
                .all(|pair| pair[0].code() < pair[1].code())
        );
    }

    #[test]
    fn representative_catalog_entries_match_typescript() {
        let unterminated = message_by_code(1002).unwrap();
        assert_eq!(unterminated.category(), Category::Error);
        assert_eq!(unterminated.text(), "Unterminated string literal.");
        assert_eq!(unterminated.key(), "Unterminated_string_literal_1002");

        let unused = message_by_code(6133).unwrap();
        assert_eq!(
            unused.text(),
            "'{0}' is declared but its value is never read."
        );
        assert!(unused.reports_unnecessary());

        let deprecated = message_by_code(6385).unwrap();
        assert_eq!(deprecated.category(), Category::Suggestion);
        assert!(deprecated.reports_deprecated());

        let native = message_by_code(100_000).unwrap();
        assert_eq!(native.category(), Category::Message);
        assert_eq!(native.text(), "Do not print diagnostics.");
    }

    #[test]
    fn diagnostics_render_numbered_arguments() {
        let message = message_by_code(1007).unwrap();
        let diagnostic = Diagnostic::with_arguments(message, ["{", "}"]);
        assert_eq!(
            diagnostic.render().unwrap(),
            "The parser expected to find a '}' to match the '{' token here."
        );
        assert_eq!(diagnostic.code(), 1007);
    }

    #[test]
    fn diagnostics_render_placeholders_inside_literal_braces() {
        let diagnostic =
            Diagnostic::with_arguments(message_by_code(2613).unwrap(), ["./module", "namedExport"]);
        assert_eq!(
            diagnostic.render().unwrap(),
            "Module './module' has no default export. Did you mean to use 'import { namedExport } from ./module' instead?"
        );
    }

    #[test]
    fn diagnostics_report_missing_numbered_arguments() {
        let diagnostic = Diagnostic::with_arguments(message_by_code(1007).unwrap(), ["{"]);
        let error = diagnostic.render().unwrap_err();
        assert_eq!(error.code, 1007);
        assert_eq!(error.argument_index, 1);
    }

    #[test]
    fn diagnostics_render_indented_message_details() {
        let message = message_by_code(2322).unwrap();
        let diagnostic = Diagnostic::with_arguments(message, ["source", "target"])
            .with_details(["  Types of parameters are incompatible."]);
        assert_eq!(
            diagnostic.render().unwrap(),
            concat!(
                "Type 'source' is not assignable to type 'target'.\n",
                "  Types of parameters are incompatible.",
            )
        );
    }

    #[test]
    fn lookup_by_key_uses_generated_key() {
        assert_eq!(
            message_by_key("Identifier_expected_1003").unwrap().code(),
            1003
        );
        assert!(message_by_code(u32::MAX).is_none());
    }
}
