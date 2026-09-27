use crate::ls::prelude::*;

// Go `internal/ls/format.go`: the formatting requests and
// `getRangeOfEnclosingComment`.
//
// PORT: Go package `format` is written `crate::format` here, because this
// file is the module `ls::format`.

use crate::frontend::core_textchange::TextChange;
use crate::frontend::scanner::get_trailing_comment_ranges;

impl LanguageService {
    // Go: ls/format.go:16 toLSProtoTextEdits
    fn to_ls_proto_text_edits(&self, file: Node, changes: &[TextChange]) -> Vec<lsproto::TextEdit> {
        let mut result = Vec::with_capacity(changes.len());
        for c in changes {
            result.push(lsproto::TextEdit {
                new_text: c.new_text.clone(),
                range: self.create_lsp_range_from_bounds(c.pos(), c.end(), file),
            });
        }
        result
    }

    // Go: ls/format.go:27 ProvideFormatDocument
    pub fn provide_format_document(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        options: &lsproto::FormattingOptions,
    ) -> Result<lsproto::DocumentFormattingResponse, GoError> {
        if self.user_preferences().enable_formatting.is_false() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let (_, file) = self.get_program_and_file(document_uri);
        let format_opts = lsutil::from_ls_format_options(&self.format_options(), options);
        let edits = self.to_ls_proto_text_edits(
            file,
            &self.get_formatting_edits_for_document(ctx, file, &format_opts),
        );
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    // Go: ls/format.go:42 ProvideFormatDocumentRange
    pub fn provide_format_document_range(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        options: &lsproto::FormattingOptions,
        r: lsproto::Range,
    ) -> Result<lsproto::DocumentRangeFormattingResponse, GoError> {
        if self.user_preferences().enable_formatting.is_false() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let (_, file) = self.get_program_and_file(document_uri);
        let format_opts = lsutil::from_ls_format_options(&self.format_options(), options);
        let edits = self.to_ls_proto_text_edits(
            file,
            &self.get_formatting_edits_for_range(
                ctx,
                file,
                &format_opts,
                self.converters.from_lsp_range(&file, &r),
            ),
        );
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    // Go: ls/format.go:59 ProvideFormatDocumentOnType
    pub fn provide_format_document_on_type(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
        options: &lsproto::FormattingOptions,
        position: lsproto::Position,
        character: &str,
    ) -> Result<lsproto::DocumentOnTypeFormattingResponse, GoError> {
        if self.user_preferences().enable_formatting.is_false() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let (_, file) = self.get_program_and_file(document_uri);
        let format_opts = lsutil::from_ls_format_options(&self.format_options(), options);
        let edits = self.to_ls_proto_text_edits(
            file,
            &self.get_formatting_edits_after_keystroke(
                ctx,
                file,
                &format_opts,
                self.converters
                    .line_and_character_to_position(&file, &position),
                character,
            ),
        );
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    // Go: ls/format.go:78 getFormattingEditsForRange
    fn get_formatting_edits_for_range(
        &self,
        ctx: &Context,
        file: Node,
        options: &lsutil::FormatCodeSettings,
        r: TextRange,
    ) -> Vec<TextChange> {
        let ctx = &crate::format::with_format_code_settings(
            ctx,
            options,
            &options.editor_settings.new_line_character,
        );
        crate::format::format_selection(ctx, file, r.pos(), r.end())
    }

    // Go: ls/format.go:88 getFormattingEditsForDocument
    fn get_formatting_edits_for_document(
        &self,
        ctx: &Context,
        file: Node,
        options: &lsutil::FormatCodeSettings,
    ) -> Vec<TextChange> {
        let ctx = &crate::format::with_format_code_settings(
            ctx,
            options,
            &options.editor_settings.new_line_character,
        );
        crate::format::format_document(ctx, file)
    }

    // Go: ls/format.go:97 getFormattingEditsAfterKeystroke
    fn get_formatting_edits_after_keystroke(
        &self,
        ctx: &Context,
        file: Node,
        options: &lsutil::FormatCodeSettings,
        position: i32,
        key: &str,
    ) -> Vec<TextChange> {
        let ctx = &crate::format::with_format_code_settings(
            ctx,
            options,
            &options.editor_settings.new_line_character,
        );

        let token_at_position = astnav::get_token_at_position(file, position);
        if is_in_comment(file, position, token_at_position).is_none() {
            match key {
                "{" => return crate::format::format_on_opening_curly(ctx, file, position),
                "}" => return crate::format::format_on_closing_curly(ctx, file, position),
                ";" => return crate::format::format_on_semicolon(ctx, file, position),
                "\n" => return crate::format::format_on_enter(ctx, file, position),
                _ => return Vec::new(),
            }
        }
        Vec::new()
    }
}

// Go: ls/format.go:128 getRangeOfEnclosingComment
// Unlike the TS implementation, this function *will not* compute default values for
// `precedingToken` and `tokenAtPosition`.
// It is the caller's responsibility to call `astnav.GetTokenAtPosition` to compute a default `tokenAtPosition`,
// or `astnav.FindPrecedingToken` to compute a default `precedingToken`.
pub fn get_range_of_enclosing_comment(
    file: Node,
    position: i32,
    preceding_token: Node,
    token_at_position: Node,
) -> Option<CommentRange> {
    let mut token_at_position = token_at_position;
    // PORT: Go passes the method expression `(*ast.Node).IsJSDoc`. It has the
    // same body as `ast.IsJSDoc` (kind is KindJSDoc).
    let jsdoc = find_ancestor(token_at_position, is_js_doc);
    if jsdoc.is_some() {
        token_at_position = jsdoc.parent();
    }
    let token_start =
        astnav::get_start_of_node(token_at_position, file, false /*includeJSDoc*/);
    if token_start <= position && position < token_at_position.end() {
        return None;
    }

    // Between two consecutive tokens, all comments are either trailing on the former
    // or leading on the latter (and none are in both lists).
    // PORT: Go keeps a nil `iter.Seq` when there is no preceding token; an
    // empty Vec yields the same (no) items.
    let mut trailing_ranges_of_previous_token: Vec<CommentRange> = Vec::new();
    if preceding_token.is_some() {
        trailing_ranges_of_previous_token = get_trailing_comment_ranges(
            &NodeFactory::default(),
            source_file_text(file),
            preceding_token.end(),
        );
    }
    let leading_ranges_of_next_token = get_leading_comment_ranges_of_node(token_at_position, file);
    // PORT: Go `core.ConcatenateSeq`.
    let comment_ranges = trailing_ranges_of_previous_token
        .into_iter()
        .chain(leading_ranges_of_next_token);
    for comment_range in comment_ranges {
        // The end marker of a single-line comment does not include the newline character.
        // In the following case where the cursor is at `^`, we are inside a comment:
        //
        //    // asdf   ^\n
        //
        // But for closed multi-line comments, we don't want to be inside the comment in the following case:
        //
        //    /* asdf */^
        //
        // Internally, we represent the end of the comment prior to the newline and at the '/', respectively.
        //
        // However, unterminated multi-line comments lack a `/`, end at the end of the file, and *do* contain their end.
        //
        if comment_range.text_range.contains_exclusive(position)
            || position == comment_range.end()
                && (comment_range.kind == SyntaxKind::SingleLineCommentTrivia
                    || position == source_file_text(file).len() as i32)
        {
            return Some(comment_range);
        }
    }
    None
}
