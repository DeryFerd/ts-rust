//! Port of Go `ls/lsconv/converters.go`.

use crate::ls::lsconv::prelude::*;

use crate::frontend::bundled::is_bundled;
use crate::frontend::core_textchange::TextChange;
use crate::frontend::scanner::scanner_p1::{RUNE_ERROR, utf8_decode_rune_in_string};
use crate::frontend::tspath;
use crate::gostd;
use crate::locale;
use crate::lsp::lsproto;
use std::sync::LazyLock;

// Go: ls/lsconv/converters.go:23 Converters
// PORT: Go `getLineMap func(fileName string) *LSPLineMap`; a nil map is `None`.
pub struct Converters {
    get_line_map: Box<dyn Fn(&str) -> Option<Rc<LSPLineMap>>>,
    position_encoding: lsproto::PositionEncodingKind,
}

// Go: ls/lsconv/converters.go:28 Script
pub trait Script {
    fn file_name(&self) -> &str;
    fn text(&self) -> &str;
}

// PORT: Go `*ast.SourceFile` implements Script through its `FileName` and
// `Text` methods. Here the file is its root `Node`. The inherent
// `Node::text` (Go `Node.Text`) wins in method syntax, so pass a file as
// `&dyn Script` (or call `Script::text(&file)`), as Go passes it as a Script.
impl Script for Node {
    fn file_name(&self) -> &str {
        source_file_file_name(*self)
    }

    fn text(&self) -> &str {
        source_file_text(*self)
    }
}

// Go: ls/lsconv/converters.go:33 NewConverters
// PORT: Go returns `*Converters`, which the session, snapshots and language
// services share; here `Rc<Converters>`.
pub fn new_converters(
    position_encoding: lsproto::PositionEncodingKind,
    get_line_map: impl Fn(&str) -> Option<Rc<LSPLineMap>> + 'static,
) -> Rc<Converters> {
    Rc::new(Converters {
        get_line_map: Box::new(get_line_map),
        position_encoding,
    })
}

impl Converters {
    /// Go `c.getLineMap(fileName)` followed by a dereference.
    // PORT: Go dereferences the returned pointer, which panics when it is nil.
    fn line_map_of(&self, file_name: &str) -> Rc<LSPLineMap> {
        (self.get_line_map)(file_name).expect("invalid memory address or nil pointer dereference")
    }

    // Go: ls/lsconv/converters.go:40 ToLSPRange
    pub fn to_lsp_range(&self, script: &dyn Script, text_range: TextRange) -> lsproto::Range {
        lsproto::Range {
            start: self.position_to_line_and_character(script, text_range.pos()),
            end: self.position_to_line_and_character(script, text_range.end()),
        }
    }

    // Go: ls/lsconv/converters.go:47 FromLSPRange
    // PORT: Go passes the range by value; here by reference.
    pub fn from_lsp_range(&self, script: &dyn Script, text_range: &lsproto::Range) -> TextRange {
        TextRange::new(
            self.line_and_character_to_position(script, &text_range.start),
            self.line_and_character_to_position(script, &text_range.end),
        )
    }

    // Go: ls/lsconv/converters.go:54 FromLSPTextChange
    pub fn from_lsp_text_change(
        &self,
        script: &dyn Script,
        change: &lsproto::TextDocumentContentChangePartial,
    ) -> TextChange {
        TextChange {
            text_range: self.from_lsp_range(script, &change.range),
            new_text: change.text.clone(),
        }
    }

    // Go: ls/lsconv/converters.go:61 ToLSPLocation
    pub fn to_lsp_location(&self, script: &dyn Script, rng: TextRange) -> lsproto::Location {
        lsproto::Location {
            uri: file_name_to_document_uri(script.file_name()),
            range: self.to_lsp_range(script, rng),
        }
    }
}

// Go: ls/lsconv/converters.go:68 LanguageKindToScriptKind
// PORT: Go passes the string value; here by reference.
#[must_use]
pub fn language_kind_to_script_kind(language_id: &lsproto::LanguageKind) -> ScriptKind {
    match &*language_id.0 {
        "typescript" => ScriptKind::TS,
        "typescriptreact" => ScriptKind::TSX,
        "javascript" => ScriptKind::JS,
        "javascriptreact" => ScriptKind::JSX,
        "json" => ScriptKind::JSON,
        _ => ScriptKind::UNKNOWN,
    }
}

// Go: ls/lsconv/converters.go:86 extraEscapeReplacer
// https://github.com/microsoft/vscode-uri/blob/edfdccd976efaf4bb8fdeca87e97c47257721729/src/uri.ts#L455
// PORT: Go `strings.NewReplacer` with one-byte old strings (Go picks its byte
// replacer). The pairs are kept in Go order; `extra_escape_replacer_replace`
// is `Replace`.
const EXTRA_ESCAPE_REPLACER: [(u8, &str); 19] = [
    (b':', "%3A"),
    (b'/', "%2F"),
    (b'?', "%3F"),
    (b'#', "%23"),
    (b'[', "%5B"),
    (b']', "%5D"),
    (b'@', "%40"),
    //
    (b'!', "%21"),
    (b'$', "%24"),
    (b'&', "%26"),
    (b'\'', "%27"),
    (b'(', "%28"),
    (b')', "%29"),
    (b'*', "%2A"),
    (b'+', "%2B"),
    (b',', "%2C"),
    (b';', "%3B"),
    (b'=', "%3D"),
    //
    (b' ', "%20"),
];

/// Go `extraEscapeReplacer.Replace(s)`.
fn extra_escape_replacer_replace(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        let replacement = if ch.is_ascii() {
            EXTRA_ESCAPE_REPLACER
                .iter()
                .find(|(old, _)| *old == ch as u8)
                .map(|(_, new)| *new)
        } else {
            None
        };
        match replacement {
            Some(new) => out.push_str(new),
            None => out.push(ch),
        }
    }
    out
}

// Go: ls/lsconv/converters.go:110 FileNameToDocumentURI
#[must_use]
pub fn file_name_to_document_uri(file_name: &str) -> lsproto::DocumentUri {
    if is_bundled(file_name) {
        return lsproto::DocumentUri(file_name.to_string());
    }
    if tspath::is_dynamic_file_name(file_name) {
        let Some((scheme, rest)) = file_name[2..].split_once('/') else {
            panic!("invalid file name: {file_name}");
        };
        let Some((authority, path)) = rest.split_once('/') else {
            panic!("invalid file name: {file_name}");
        };
        if authority == "ts-nul-authority" {
            return lsproto::DocumentUri(format!("{scheme}:{path}"));
        }
        return lsproto::DocumentUri(format!("{scheme}://{authority}/{path}"));
    }

    let (mut volume, file_name, _) = tspath::split_volume_path(file_name);
    if !volume.is_empty() {
        volume = format!("/{}", extra_escape_replacer_replace(&volume));
    }

    let file_name = file_name.strip_prefix("//").unwrap_or(file_name);

    let parts: Vec<String> = file_name
        .split('/')
        .map(|part| extra_escape_replacer_replace(&gostd::url::path_escape(part)))
        .collect();

    lsproto::DocumentUri(format!("file://{volume}{}", parts.join("/")))
}

/// Go `utf16.RuneLen(r)`.
// Go: unicode/utf16/utf16.go RuneLen
fn utf16_rune_len(r: i32) -> i32 {
    if (0..0xD800).contains(&r) || (0xE000..0x10000).contains(&r) {
        1
    } else if (0x10000..=0x10FFFF).contains(&r) {
        2
    } else {
        -1
    }
}

// PORT (WTF-8): Go text may hold invalid UTF-8. Go decodes each invalid byte
// as a one-byte `RuneError`, which counts as one UTF-16 unit. The port holds
// such text in the port form (see `scanner_util::GO_STRING_MARKER`): each
// invalid byte (also each byte of a WTF-8 lone surrogate in source text) is
// a 7-byte unit, and a real U+FDD0 is a 6-byte unit.
// `utf8_decode_rune_in_string` reads a unit as one rune (`RuneError` for an
// invalid byte) with its size in the port text, so UTF-16 characters match
// Go. Byte offsets after a unit are port offsets, not Go offsets, so with
// the UTF-8 position encoding the character after a unit on a line differs
// from Go. Otherwise the decoder follows Go `utf8.DecodeRuneInString`, also
// at a position inside a character.
impl Converters {
    // Go: ls/lsconv/converters.go:144 LineAndCharacterToPosition
    // PORT: Go passes the position by value; here by reference.
    pub fn line_and_character_to_position(
        &self,
        script: &dyn Script,
        line_and_character: &lsproto::Position,
    ) -> i32 {
        // UTF-8/16 0-indexed line and character to UTF-8 offset

        let line_map = self.line_map_of(script.file_name());

        // PORT: Go `core.TextPos(uint32)` keeps the low 32 bits.
        let line = line_and_character.line as i32;
        let char = line_and_character.character as i32;

        let text_len = script.text().len() as i32;

        // Clamp line to valid range.
        if i64::from(line) >= line_map.line_starts.len() as i64 {
            return text_len;
        }

        let start = line_map.line_starts[line as usize];

        // Determine the end of this line (start of next line, or end of text).
        let line_end = if i64::from(line) + 1 < line_map.line_starts.len() as i64 {
            line_map.line_starts[(line + 1) as usize]
        } else {
            text_len
        };

        if line_map.ascii_only || self.position_encoding == lsproto::PositionEncodingKind::UTF8 {
            return start.max(start.wrapping_add(char).min(line_end));
        }

        // Scan from line start counting UTF-16 code units to find the byte position.
        // Uses DecodeRuneInString (not range + RuneLen) so that invalid UTF-8 bytes
        // advance by their actual size (1) rather than RuneLen(RuneError) == 3.
        // This matches the approach in scanner.ComputePositionOfLineAndUTF16Character.
        let mut utf16_char: i32 = 0;
        let mut pos = start as usize;
        let end = line_end as usize;
        let text = script.text();
        while pos < end {
            // Go `text[pos:]` panics past the end of the text.
            assert!(pos <= text.len(), "slice bounds out of range");
            let (r, size) = utf8_decode_rune_in_string(text, pos);
            let u16_len = utf16_rune_len(r);
            if utf16_char + u16_len > char {
                break;
            }
            utf16_char += u16_len;
            pos += size as usize;
        }

        pos as i32
    }

    // Go: ls/lsconv/converters.go:194 PositionToLineAndCharacter
    pub fn position_to_line_and_character(
        &self,
        script: &dyn Script,
        position: i32,
    ) -> lsproto::Position {
        // UTF-8 offset to UTF-8/16 0-indexed line and character

        let position = i32::max(0, position.min(script.text().len() as i32));

        let line_map = self.line_map_of(script.file_name());

        // PORT: Go `slices.BinarySearch` is `BinarySearchFunc` with
        // `cmp.Compare`. Go `int` math is `i64` here.
        let (found, is_line_start) = gostd::slices::binary_search_func(
            &line_map.line_starts,
            position,
            |p: &i32, t: &i32| p.cmp(t) as i32,
        );
        let mut line = found as i64;
        if !is_line_start {
            line -= 1;
        }
        line = i64::max(0, line.min(line_map.line_starts.len() as i64 - 1));

        // The current line ranges from lineMap.LineStarts[line] (or 0) to lineMap.LineStarts[line+1] (or len(text)).

        let start = line_map.line_starts[line as usize];

        let mut character: i32 = 0;
        if line_map.ascii_only || self.position_encoding == lsproto::PositionEncodingKind::UTF8 {
            character = position - start;
        } else {
            // We need to rescan the text as UTF-16 to find the character offset.
            // PORT: Go ranges over `text[start:position]`. A character cut by
            // the slice end decodes as one-byte `RuneError`s, as in Go.
            let text = script.text();
            assert!(start <= position, "slice bounds out of range");
            let slice_end = position as usize;
            let mut pos = start as usize;
            while pos < slice_end {
                let (mut r, mut size) = utf8_decode_rune_in_string(text, pos);
                if pos + size as usize > slice_end {
                    r = RUNE_ERROR;
                    size = 1;
                }
                character += utf16_rune_len(r);
                pos += size as usize;
            }
        }

        lsproto::Position {
            line: line as u32,
            character: character as u32,
        }
    }
}

// Go: ls/lsconv/converters.go:227 diagnosticOptions
struct DiagnosticOptions {
    report_style_checks_as_warnings: bool,
    related_information: bool,
    tag_value_set: Vec<lsproto::DiagnosticTag>,
    visual_studio: bool,
}

// Go: ls/lsconv/converters.go:235 DiagnosticToLSPPull
// DiagnosticToLSPPull converts a diagnostic for pull diagnostics (textDocument/diagnostic)
pub fn diagnostic_to_lsp_pull(
    ctx: &Context,
    converters: &Converters,
    diagnostic: &Diagnostic,
    report_style_checks_as_warnings: bool,
) -> lsproto::Diagnostic {
    let client_caps = lsproto::get_client_capabilities(ctx);
    let client_diagnostic_caps = &client_caps.text_document.diagnostic;
    diagnostic_to_lsp(
        ctx,
        converters,
        diagnostic,
        DiagnosticOptions {
            report_style_checks_as_warnings, // !!! get through context UserPreferences
            related_information: client_diagnostic_caps.related_information,
            tag_value_set: client_diagnostic_caps.tag_support.value_set.clone(),
            visual_studio: client_caps.vs_supports_visual_studio_extensions,
        },
    )
}

// Go: ls/lsconv/converters.go:247 DiagnosticToLSPPush
// DiagnosticToLSPPush converts a diagnostic for push diagnostics (textDocument/publishDiagnostics)
pub fn diagnostic_to_lsp_push(
    ctx: &Context,
    converters: &Converters,
    diagnostic: &Diagnostic,
) -> lsproto::Diagnostic {
    let client_caps = lsproto::get_client_capabilities(ctx);
    let client_diagnostic_caps = &client_caps.text_document.publish_diagnostics;
    diagnostic_to_lsp(
        ctx,
        converters,
        diagnostic,
        DiagnosticOptions {
            report_style_checks_as_warnings: false,
            related_information: client_diagnostic_caps.related_information,
            tag_value_set: client_diagnostic_caps.tag_support.value_set.clone(),
            visual_studio: client_caps.vs_supports_visual_studio_extensions,
        },
    )
}

// Go: ls/lsconv/converters.go:258 styleCheckDiagnostics
// https://github.com/microsoft/vscode/blob/93e08afe0469712706ca4e268f778cfadf1a43ef/extensions/typescript-language-features/src/typeScriptServiceClientHost.ts#L40C7-L40C29
static STYLE_CHECK_DIAGNOSTICS: LazyLock<FxHashSet<i32>> = LazyLock::new(|| {
    [
        diag::X_0_is_declared_but_never_used.code() as i32,
        diag::X_0_is_declared_but_its_value_is_never_read.code() as i32,
        diag::Property_0_is_declared_but_its_value_is_never_read.code() as i32,
        diag::All_imports_in_import_declaration_are_unused.code() as i32,
        diag::Unreachable_code_detected.code() as i32,
        diag::Unused_label.code() as i32,
        diag::Fallthrough_case_in_switch.code() as i32,
        diag::Not_all_code_paths_return_a_value.code() as i32,
    ]
    .into_iter()
    .collect()
});

// Go: ls/lsconv/converters.go:269 diagnosticToLSP
fn diagnostic_to_lsp(
    ctx: &Context,
    converters: &Converters,
    diagnostic: &Diagnostic,
    opts: DiagnosticOptions,
) -> lsproto::Diagnostic {
    let locale = locale::from_context(ctx);
    let mut severity = match diagnostic.category() {
        ts_diagnostics::Category::Suggestion => lsproto::DiagnosticSeverity::HINT,
        ts_diagnostics::Category::Message => lsproto::DiagnosticSeverity::INFORMATION,
        ts_diagnostics::Category::Warning => lsproto::DiagnosticSeverity::WARNING,
        _ => lsproto::DiagnosticSeverity::ERROR,
    };

    if opts.report_style_checks_as_warnings
        && severity == lsproto::DiagnosticSeverity::ERROR
        && STYLE_CHECK_DIAGNOSTICS.contains(&diagnostic.code())
    {
        severity = lsproto::DiagnosticSeverity::WARNING;
    }

    let mut related_information: Vec<lsproto::DiagnosticRelatedInformation> = Vec::new();
    if opts.related_information {
        related_information = Vec::with_capacity(diagnostic.related_information().len());
        for related in diagnostic.related_information() {
            related_information.push(lsproto::DiagnosticRelatedInformation {
                location: lsproto::Location {
                    uri: file_name_to_document_uri(source_file_file_name(related.file())),
                    range: converters.to_lsp_range(&related.file(), related.loc()),
                },
                message: related.localize(&locale),
            });
        }
    }

    let mut tags: Vec<lsproto::DiagnosticTag> = Vec::new();
    if !opts.tag_value_set.is_empty()
        && (diagnostic.reports_unnecessary() || diagnostic.reports_deprecated())
    {
        tags = Vec::with_capacity(2);
        if diagnostic.reports_unnecessary()
            && opts
                .tag_value_set
                .contains(&lsproto::DiagnosticTag::UNNECESSARY)
        {
            tags.push(lsproto::DiagnosticTag::UNNECESSARY);
        }
        if diagnostic.reports_deprecated()
            && opts
                .tag_value_set
                .contains(&lsproto::DiagnosticTag::DEPRECATED)
        {
            tags.push(lsproto::DiagnosticTag::DEPRECATED);
        }
    }

    // For diagnostics without a file (e.g., program diagnostics), use a zero range
    let mut lsp_range = lsproto::Range::default();
    if diagnostic.file().is_some() {
        lsp_range = converters.to_lsp_range(&diagnostic.file(), diagnostic.loc());
    }

    let code: Option<lsproto::IntegerOrString>;
    let mut source: Option<String> = None;
    if opts.visual_studio {
        code = Some(lsproto::IntegerOrString {
            string: Some(format!("TS{}", diagnostic.code())),
            ..Default::default()
        });
    } else {
        code = Some(lsproto::IntegerOrString {
            integer: Some(diagnostic.code()),
            ..Default::default()
        });
        source = Some("ts".to_string());
    }

    lsproto::Diagnostic {
        range: lsp_range,
        code,
        severity: Some(severity),
        message: lsproto::StringOrMarkupContent {
            string: Some(message_chain_to_string(diagnostic, &locale)),
            ..Default::default()
        },
        source,
        related_information: ptr_to_slice_if_non_empty(related_information),
        tags: ptr_to_slice_if_non_empty(tags),
        ..Default::default()
    }
}

// Go: ls/lsconv/converters.go:342 messageChainToString
fn message_chain_to_string(diagnostic: &Diagnostic, locale: &locale::Locale) -> String {
    if diagnostic.message_chain().is_empty() {
        return diagnostic.localize(locale);
    }
    let mut b = String::new();
    write_flattened_ast_diagnostic_message(&mut b, diagnostic, "\n", locale);
    b
}

// Go: ls/lsconv/converters.go:351 ptrToSliceIfNonEmpty
fn ptr_to_slice_if_non_empty<T>(s: Vec<T>) -> Option<Vec<T>> {
    if s.is_empty() {
        return None;
    }
    Some(s)
}

// Go: diagnosticwriter/diagnosticwriter.go:259 WriteFlattenedASTDiagnosticMessage
// PORT: Go package `diagnosticwriter`. The `String` writer version in
// program.rs is private, and the execute/tsc version writes to its own
// `Writer`, so the three Go functions are ported here for a `String`.
// Only English messages exist; `localize` drops the locale.
fn write_flattened_ast_diagnostic_message(
    writer: &mut String,
    diagnostic: &Diagnostic,
    newline: &str,
    locale: &locale::Locale,
) {
    // PORT: Go wraps the diagnostic (`WrapASTDiagnostic`); the wrapper only
    // forwards `Localize` and `MessageChain`.
    write_flattened_diagnostic_message(writer, diagnostic, newline, locale);
}

// Go: diagnosticwriter/diagnosticwriter.go:263 WriteFlattenedDiagnosticMessage
fn write_flattened_diagnostic_message(
    writer: &mut String,
    diagnostic: &Diagnostic,
    newline: &str,
    locale: &locale::Locale,
) {
    writer.push_str(&diagnostic.localize(locale));

    for chain in diagnostic.message_chain() {
        flatten_diagnostic_message_chain(writer, chain, newline, locale, 1 /*level*/);
    }
}

// Go: diagnosticwriter/diagnosticwriter.go:271 flattenDiagnosticMessageChain
fn flatten_diagnostic_message_chain(
    writer: &mut String,
    chain: &Diagnostic,
    new_line: &str,
    locale: &locale::Locale,
    level: i32,
) {
    writer.push_str(new_line);
    for _ in 0..level {
        writer.push_str("  ");
    }

    writer.push_str(&chain.localize(locale));
    for child in chain.message_chain() {
        flatten_diagnostic_message_chain(writer, child, new_line, locale, level + 1);
    }
}
