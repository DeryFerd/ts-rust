use crate::format::prelude::*;

use crate::flags_macros::go_enum;
use crate::frontend::core_textchange::TextChange;
use crate::frontend::scanner::scanner_p1::{rune_to_char, utf8_decode_rune_in_string};
use crate::gostd::context::{ContextKey, with_value};
use std::sync::Arc;

// Go: format/api.go:14 FormatRequestKind
go_enum!(FormatRequestKind, i32 {
    FORMAT_DOCUMENT = 0; // FormatRequestKindFormatDocument
    FORMAT_SELECTION = 1; // FormatRequestKindFormatSelection
    FORMAT_ON_ENTER = 2; // FormatRequestKindFormatOnEnter
    FORMAT_ON_SEMICOLON = 3; // FormatRequestKindFormatOnSemicolon
    FORMAT_ON_OPENING_CURLY_BRACE = 4; // FormatRequestKindFormatOnOpeningCurlyBrace
    FORMAT_ON_CLOSING_CURLY_BRACE = 5; // FormatRequestKindFormatOnClosingCurlyBrace
});

// Go: format/api.go:25 formatContextKey
// PORT: Go keys both values with one int type (`formatOptionsKey`,
// `formatNewlineKey`). gostd context keys are typed, so each Go key value is
// its own static with the type of the value stored under it.
pub static FORMAT_OPTIONS_KEY: ContextKey<lsutil::FormatCodeSettings> =
    ContextKey::new("formatOptionsKey");
pub static FORMAT_NEWLINE_KEY: ContextKey<String> = ContextKey::new("formatNewlineKey");

// Go: format/api.go:32 WithFormatCodeSettings
pub fn with_format_code_settings(
    ctx: &Context,
    options: &lsutil::FormatCodeSettings,
    new_line: &str,
) -> Context {
    let ctx = with_value(ctx, &FORMAT_OPTIONS_KEY, options.clone());
    let ctx = with_value(&ctx, &FORMAT_NEWLINE_KEY, new_line.to_string());
    // In strada, the rules map was both globally cached *and* cached into the context, for some reason. We skip that here and just use the global one.
    ctx
}

// Go: format/api.go:39 GetFormatCodeSettingsFromContext
// PORT: Go returns the settings by value; the context holds them in an Arc.
pub fn get_format_code_settings_from_context(ctx: &Context) -> Arc<lsutil::FormatCodeSettings> {
    if let Some(opt) = ctx.value(&FORMAT_OPTIONS_KEY) {
        return opt;
    }
    Arc::new(lsutil::get_default_format_code_settings())
}

// Go: format/api.go:46 GetNewLineOrDefaultFromContext
pub fn get_new_line_or_default_from_context(ctx: &Context) -> String {
    // TODO: Move into broader LS - more than just the formatter uses the newline editor setting/host new line
    let opt = get_format_code_settings_from_context(ctx);
    if !opt.editor_settings.new_line_character.is_empty() {
        return opt.editor_settings.new_line_character.clone();
    }
    // PORT: Go `ctx.Value(formatNewlineKey).(string)` panics when the key is
    // missing.
    let host = ctx
        .value(&FORMAT_NEWLINE_KEY)
        .expect("interface conversion: interface {} is nil, not string");
    if !host.is_empty() {
        return (*host).clone();
    }
    "\n".to_string()
}

// Go: format/api.go:58 FormatSpan
pub fn format_span(
    ctx: &Context,
    span: TextRange,
    file: Node,
    kind: FormatRequestKind,
) -> Vec<TextChange> {
    // find the smallest node that fully wraps the range and compute the initial indentation for the node
    let enclosing_node = find_enclosing_node(span, file);
    let opts = get_format_code_settings_from_context(ctx);

    new_formatting_scanner(
        source_file_text(file),
        source_file_language_variant(file),
        get_scan_start_position(enclosing_node, span, file),
        span.end(),
        new_format_span_worker(
            ctx,
            span,
            enclosing_node,
            get_indentation_for_node(enclosing_node, Some(&span), file, &opts),
            get_own_or_inherited_delta(enclosing_node, &opts, file),
            kind,
            prepare_range_contains_error_function(source_file_diagnostics(file), span),
            file,
        ),
    )
}

// Go: format/api.go:81 FormatNodeGivenIndentation
pub fn format_node_given_indentation(
    ctx: &Context,
    node: Node,
    file: Node,
    language_variant: LanguageVariant,
    initial_indentation: i32,
    delta: i32,
) -> Vec<TextChange> {
    let text_range = TextRange::new(node.pos(), node.end());
    new_formatting_scanner(
        source_file_text(file),
        language_variant,
        text_range.pos(),
        text_range.end(),
        new_format_span_worker(
            ctx,
            text_range,
            node,
            initial_indentation,
            delta,
            FormatRequestKind::FORMAT_SELECTION,
            Box::new(|_: TextRange| false), // assume that node does not have any errors
            file,
        ),
    )
}

// Go: format/api.go:101 formatNodeLines
pub fn format_node_lines(
    ctx: &Context,
    source_file: Node,
    node: Node,
    request_kind: FormatRequestKind,
) -> Vec<TextChange> {
    if node.is_nil() {
        return Vec::new();
    }
    let token_start = get_token_pos_of_node(node, source_file, false);
    let line_start = get_line_start_position_for_position(token_start, source_file);
    let span = TextRange::new(line_start, node.end());
    format_span(ctx, span, source_file, request_kind)
}

// Go: format/api.go:111 FormatDocument
pub fn format_document(ctx: &Context, source_file: Node) -> Vec<TextChange> {
    format_span(
        ctx,
        TextRange::new(0, source_file.end()),
        source_file,
        FormatRequestKind::FORMAT_DOCUMENT,
    )
}

// Go: format/api.go:115 FormatSelection
pub fn format_selection(ctx: &Context, source_file: Node, start: i32, end: i32) -> Vec<TextChange> {
    format_span(
        ctx,
        TextRange::new(
            get_line_start_position_for_position(start, source_file),
            end,
        ),
        source_file,
        FormatRequestKind::FORMAT_SELECTION,
    )
}

// Go: format/api.go:119 FormatOnOpeningCurly
pub fn format_on_opening_curly(ctx: &Context, source_file: Node, position: i32) -> Vec<TextChange> {
    let opening_curly =
        find_immediately_preceding_token_of_kind(position, SyntaxKind::OpenBraceToken, source_file);
    if opening_curly.is_nil() {
        return Vec::new();
    }
    let curly_brace_range = opening_curly.parent();
    let outermost_node = find_outermost_node_within_list_level(curly_brace_range);
    /*
     * We limit the span to end at the opening curly to handle the case where
     * the brace matched to that just typed will be incorrect after further edits.
     * For example, we could type the opening curly for the following method
     * body without brace-matching activated:
     * ```
     * class C {
     *     foo()
     * }
     * ```
     * and we wouldn't want to move the closing brace.
     */
    let text_range = TextRange::new(
        get_line_start_position_for_position(
            get_token_pos_of_node(outermost_node, source_file, false),
            source_file,
        ),
        position,
    );
    format_span(
        ctx,
        text_range,
        source_file,
        FormatRequestKind::FORMAT_ON_OPENING_CURLY_BRACE,
    )
}

// Go: format/api.go:142 FormatOnClosingCurly
pub fn format_on_closing_curly(ctx: &Context, source_file: Node, position: i32) -> Vec<TextChange> {
    let preceding_token = find_immediately_preceding_token_of_kind(
        position,
        SyntaxKind::CloseBraceToken,
        source_file,
    );
    format_node_lines(
        ctx,
        source_file,
        find_outermost_node_within_list_level(preceding_token),
        FormatRequestKind::FORMAT_ON_CLOSING_CURLY_BRACE,
    )
}

// Go: format/api.go:147 FormatOnSemicolon
pub fn format_on_semicolon(ctx: &Context, source_file: Node, position: i32) -> Vec<TextChange> {
    let semicolon =
        find_immediately_preceding_token_of_kind(position, SyntaxKind::SemicolonToken, source_file);
    format_node_lines(
        ctx,
        source_file,
        find_outermost_node_within_list_level(semicolon),
        FormatRequestKind::FORMAT_ON_SEMICOLON,
    )
}

// Go: format/api.go:152 FormatOnEnter
pub fn format_on_enter(ctx: &Context, source_file: Node, position: i32) -> Vec<TextChange> {
    let line = get_ecma_line_of_position(source_file, position);
    if line == 0 {
        return Vec::new();
    }
    // get start position for the previous line
    let start_pos = get_ecma_line_starts(source_file)[(line - 1) as usize];
    // After the enter key, the cursor is now at a new line. The new line may or may not contain non-whitespace characters.
    // If the new line has only whitespaces, we won't want to format this line, because that would remove the indentation as
    // trailing whitespaces. So the end of the formatting span should be the later one between:
    //  1. the end of the previous line
    //  2. the last non-whitespace character in the current line
    let text = source_file_text(source_file);
    let mut end_of_format_span = get_ecma_end_line_position(source_file, line);
    while end_of_format_span > start_pos {
        let (ch, s) = utf8_decode_rune_in_string(text, end_of_format_span as usize);
        if s == 0 || is_white_space_single_line(rune_to_char(ch)) {
            // on multibyte character keep backing up
            end_of_format_span -= 1;
            continue;
        }
        break;
    }

    // if the character at the end of the span is a line break, we shouldn't include it, because it indicates we don't want to
    // touch the current line at all. Also, on some OSes the line break consists of two characters (\r\n), we should test if the
    // previous character before the end of format span is line break character as well.
    let (ch, _) = utf8_decode_rune_in_string(text, end_of_format_span as usize);
    if is_line_break(rune_to_char(ch)) {
        end_of_format_span -= 1;
    }

    let span = TextRange::new(
        start_pos,
        // end value is exclusive so add 1 to the result
        end_of_format_span + 1,
    );

    format_span(ctx, span, source_file, FormatRequestKind::FORMAT_ON_ENTER)
}
