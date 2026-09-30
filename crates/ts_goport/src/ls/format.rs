use crate::ls::prelude::*;

// Go `internal/ls/format.go`: the formatting requests and
// `getRangeOfEnclosingComment`.
//
// PORT: Go package `format` is written `crate::format` here, because this
// file is the module `ls::format`.

use crate::frontend::core_textchange::TextChange;
use crate::frontend::scanner::get_trailing_comment_ranges;
use crate::spanmap;
use crate::spanmap::{Feature, SpanMap};

impl LanguageService {
    // Go: ls/format.go:18 toLSProtoTextEdits
    // PORT: Go returns a nil slice when an edit does not map exactly; that
    // is an empty `Vec`. The callers put `&edits` in the response, and Go
    // JSON (v2) writes a nil slice as `[]`, as for an empty one.
    fn to_ls_proto_text_edits(&self, file: Node, changes: &[TextChange]) -> Vec<lsproto::TextEdit> {
        let mut result = Vec::with_capacity(changes.len());
        for c in changes {
            let (lsp_range, fidelity) = self
                .converters
                .to_lsp_range(&file, TextRange::new(c.pos(), c.end()));
            if !fidelity.is_exact() {
                return Vec::new();
            }
            result.push(lsproto::TextEdit {
                new_text: c.new_text.clone(),
                range: lsp_range,
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
        let edits = if source_file_content_mapper(file).is_empty() {
            self.to_ls_proto_text_edits(
                file,
                &self.get_formatting_edits_for_document(ctx, file, &format_opts),
            )
        } else {
            self.get_formatting_edits_for_mapped_range(
                ctx,
                file,
                &format_opts,
                TextRange::new(0, source_file_original_text(file).len() as i32),
            )
        };
        Ok(lsproto::TextEditsOrNull {
            text_edits: Some(edits),
        })
    }

    // Go: ls/format.go:54 getFormattingEditsForMappedRange
    // getFormattingEditsForMappedRange formats each formatting-enabled verbatim intersection with originalRange.
    // Duplicate formatting projections are unsupported. If mappings overlap anyway, each original-text position
    // is formatted only once, preferring the earliest and then longest applicable mapping.
    fn get_formatting_edits_for_mapped_range(
        &self,
        ctx: &Context,
        file: Node,
        options: &lsutil::FormatCodeSettings,
        original_range: TextRange,
    ) -> Vec<lsproto::TextEdit> {
        let mut projections = vec![file];
        projections.extend_from_slice(source_file_supplemental_source_files(file));
        let mut candidates: Vec<MappedFormattingRange> = Vec::new();
        for projection in projections {
            let Some(span_map) = source_file_span_map(projection) else {
                continue;
            };
            for segment in SpanMap::segments(Some(span_map)) {
                if segment.kind != spanmap::Kind::VERBATIM
                    || !segment.features.intersects(Feature::FORMATTING)
                {
                    continue;
                }
                let original_start = original_range.pos().max(segment.original_start);
                let original_end = original_range.end().min(segment.original_end);
                if original_start >= original_end {
                    continue;
                }
                candidates.push(MappedFormattingRange {
                    projection,
                    segment,
                    original_range: TextRange::new(original_start, original_end),
                });
            }
        }

        let mut edits: Vec<lsproto::TextEdit> = Vec::new();
        for candidate in non_overlapping_formatting_ranges(&candidates) {
            let virtual_range = TextRange::new(
                candidate.segment.virtual_start + candidate.original_range.pos()
                    - candidate.segment.original_start,
                candidate.segment.virtual_start + candidate.original_range.end()
                    - candidate.segment.original_start,
            );
            for change in self.get_formatting_edits_for_range(
                ctx,
                candidate.projection,
                options,
                virtual_range,
            ) {
                if change.pos() < virtual_range.pos() || change.end() > virtual_range.end() {
                    continue;
                }
                let (lsp_range, fidelity) = self.converters.to_lsp_range_for_feature(
                    &candidate.projection,
                    TextRange::new(change.pos(), change.end()),
                    Feature::FORMATTING,
                );
                if !fidelity.is_exact() {
                    continue;
                }
                edits.push(lsproto::TextEdit {
                    range: lsp_range,
                    new_text: change.new_text,
                });
            }
        }
        crate::gostd::slices::sort_stable_func(&mut edits, |a, b| {
            let c = lsproto::compare_ranges(a.range, b.range);
            if c != 0 {
                return c;
            }
            a.new_text.cmp(&b.new_text) as i32
        });
        edits
    }
}

// Go: ls/format.go:106 mappedFormattingRange
#[derive(Clone, Debug)]
struct MappedFormattingRange {
    projection: Node,
    segment: spanmap::Segment,
    original_range: TextRange,
}

// Go: ls/format.go:130 nonOverlappingFormattingRanges
// nonOverlappingFormattingRanges chooses at most one formatting projection for each original-text position.
// Candidates are ordered by original start and then descending end, so a longer mapping wins when several
// mappings start together:
//
//	candidates:  [---------- A ----------)
//	             [---- B ----)
//	result:      [---------- A ----------)
//
// Since starts are ordered, a candidate can only overlap the end of the last accepted range. Its start is
// trimmed to that end, preserving any uncovered suffix:
//
//	candidates:  [------- A -------)
//	                    [------- B ----------)
//	result:      [------- A -------)[-- B' --)
//
// Fully covered candidates have no suffix and are discarded. The segment itself is retained so callers can
// translate a trimmed original range to the corresponding offset in its virtual projection.
fn non_overlapping_formatting_ranges(
    candidates: &[MappedFormattingRange],
) -> Vec<MappedFormattingRange> {
    let mut candidates = candidates.to_vec();
    crate::gostd::slices::sort_stable_func(&mut candidates, |a, b| {
        let c = a.original_range.pos().cmp(&b.original_range.pos()) as i32;
        if c != 0 {
            return c;
        }
        b.original_range.end().cmp(&a.original_range.end()) as i32
    });

    let mut result: Vec<MappedFormattingRange> = Vec::with_capacity(candidates.len());
    for mut candidate in candidates {
        if let Some(last) = result.last() {
            candidate.original_range = candidate.original_range.with_pos(
                candidate
                    .original_range
                    .pos()
                    .max(last.original_range.end()),
            );
        }
        if candidate.original_range.len() > 0 {
            result.push(candidate);
        }
    }
    result
}

impl LanguageService {
    // Go: ls/format.go:152 ProvideFormatDocumentRange
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
        if !source_file_content_mapper(file).is_empty() {
            let edits = self.get_formatting_edits_for_mapped_range(
                ctx,
                file,
                &format_opts,
                lsconv::from_lsp_range_to_original(&self.converters, &file, r),
            );
            return Ok(lsproto::TextEditsOrNull {
                text_edits: Some(edits),
            });
        }
        let ranges =
            lsconv::from_lsp_range_for_source_file(&self.converters, file, r, Feature::FORMATTING);
        if ranges.len() != 1 || !ranges[0].fidelity.is_exact() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let file = ranges[0].script;
        let edits = self.to_ls_proto_text_edits(
            file,
            &self.get_formatting_edits_for_range(ctx, file, &format_opts, ranges[0].span),
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
        let positions = lsconv::from_lsp_position_for_source_file(
            &self.converters,
            file,
            position,
            Feature::FORMATTING,
        );
        if positions.len() != 1 || !positions[0].fidelity.is_exact() {
            return Ok(lsproto::TextEditsOrNull::default());
        }
        let file = positions[0].script;
        let edits = self.to_ls_proto_text_edits(
            file,
            &self.get_formatting_edits_after_keystroke(
                ctx,
                file,
                &format_opts,
                positions[0].position,
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
            &source_file_text(file),
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

// Go: ls/format_test.go
#[cfg(test)]
mod tests {
    use super::*;

    // Go: ls/format_test.go:15 TestNonOverlappingFormattingRanges
    #[test]
    fn test_non_overlapping_formatting_ranges() {
        let tests: &[(&str, &[TextRange], &[TextRange])] = &[
            (
                "sorts disjoint ranges",
                &[TextRange::new(10, 15), TextRange::new(0, 5)],
                &[TextRange::new(0, 5), TextRange::new(10, 15)],
            ),
            (
                "prefers longest range with same start",
                &[TextRange::new(0, 10), TextRange::new(0, 20)],
                &[TextRange::new(0, 20)],
            ),
            (
                "discards fully covered range",
                &[TextRange::new(5, 15), TextRange::new(0, 20)],
                &[TextRange::new(0, 20)],
            ),
            (
                "trims overlapping prefix",
                &[TextRange::new(5, 15), TextRange::new(0, 10)],
                &[TextRange::new(0, 10), TextRange::new(10, 15)],
            ),
        ];
        for (name, candidates, want) in tests {
            let candidates: Vec<MappedFormattingRange> = candidates
                .iter()
                .map(|&r| MappedFormattingRange {
                    projection: Node::NIL,
                    segment: spanmap::Segment::default(),
                    original_range: r,
                })
                .collect();
            let result: Vec<TextRange> = non_overlapping_formatting_ranges(&candidates)
                .into_iter()
                .map(|r| r.original_range)
                .collect();
            assert_eq!(&result, want, "{name}");
        }
    }
}
