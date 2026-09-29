//! Port of Go `ls/change/trackerimpl.go`.

use crate::ls::change::prelude::*;

use crate::frontend::core_textchange::apply_bulk_edits;
use crate::frontend::parser::utilities::get_js_doc_comment_ranges;
use crate::frontend::scanner::scanner_p1::{rune_to_char, utf8_decode_rune_in_string};
use crate::frontend::scanner::{get_leading_comment_ranges, get_trailing_comment_ranges};
use crate::spanmap::Feature;

impl Tracker {
    // Go: ls/change/trackerimpl.go:23 getTextChangesFromChanges
    // PORT: Go ranges over the MultiMap's Go map (random order) and sorts
    // each file's slice in place. The IndexMap walks files in insertion
    // order; the map is taken out for the loop (the edits are mutated) and
    // put back, so the tracker keeps the sorted edits as in Go.
    pub fn get_text_changes_from_changes(&mut self) -> IndexMap<String, Vec<lsproto::TextEdit>> {
        let mut changes: IndexMap<String, Vec<lsproto::TextEdit>> = IndexMap::new();
        let mut tracker_changes = std::mem::take(&mut self.changes);
        for (&source_file, changes_in_file) in tracker_changes.iter_mut() {
            if self
                .unmappable_files
                .contains(source_file_original_file_name(source_file))
            {
                continue;
            }
            // order changes by start position
            // If the start position is the same, put the shorter range first, since an empty range (x, x) may precede (x, y) but not vice-versa.
            // Go: ls/change/trackerimpl.go:31 slices.SortStableFunc(changesInFile, lsproto.CompareRanges on the ranges)
            crate::gostd::slices::sort_stable_func(changes_in_file, |a, b| {
                lsproto::compare_ranges(a.range, b.range)
            });
            // verify that change intervals do not overlap, except possibly at end points.
            for i in 0..(changes_in_file.len() as i32 - 1).max(0) as usize {
                if lsproto::compare_positions(
                    changes_in_file[i].range.end,
                    changes_in_file[i + 1].range.start,
                ) > 0
                {
                    // assert change[i].End <= change[i + 1].Start
                    // PORT: Go `%v` of a Range prints `{{l c} {l c}}`; this
                    // prints the Rust Debug text. Panic text only.
                    panic!(
                        "changes overlap: {:?} and {:?}",
                        changes_in_file[i].range,
                        changes_in_file[i + 1].range
                    );
                }
            }

            // PORT: Go `core.MapNonNil`; the callback never returns nil.
            let text_changes: Vec<lsproto::TextEdit> = changes_in_file
                .iter()
                .map(|change| {
                    // !!! targetSourceFile

                    let new_text = self.compute_new_text(change, source_file, source_file);
                    // span := createTextSpanFromRange(c.Range)
                    // !!!
                    // Filter out redundant changes.
                    // if (span.length == newText.length && stringContainsAt(targetSourceFile.text, newText, span.start)) { return nil }

                    lsproto::TextEdit {
                        new_text,
                        range: change.range,
                    }
                })
                .collect();

            if !text_changes.is_empty() {
                let file_name = source_file_original_file_name(source_file);
                if self.unmappable_files.contains(file_name) {
                    continue;
                }
                changes
                    .entry(file_name.to_string())
                    .or_default()
                    .extend(text_changes);
            }
        }
        self.changes = tracker_changes;
        changes
    }

    // Go: ls/change/trackerimpl.go:66 computeNewText
    // PORT: Go takes `change *trackerEdit` and only reads it.
    fn compute_new_text(
        &mut self,
        change: &TrackerEdit,
        target_source_file: Node,
        source_file: Node,
    ) -> String {
        match change.kind {
            TrackerEditKind::REMOVE => return String::new(),
            TrackerEditKind::TEXT => return change.new_text.clone(),
            _ => {}
        }

        let positions = lsconv::from_lsp_position_for_source_file(
            &self.converters,
            source_file,
            change.range.start,
            Feature::ALL,
        );
        let mut result = String::new();
        let mut found = false;
        // The original range may have multiple verbatim copies; it is safe to lose their identity only when
        // formatting at every exact projection produces the same edit.
        for mapped in positions {
            if !mapped.fidelity.is_exact() {
                continue;
            }
            let projection = mapped.script;
            let pos = mapped.position;
            let format_node = |n: Node| -> String {
                self.get_formatted_text_of_node(
                    n,
                    target_source_file,
                    projection,
                    pos,
                    &change.options,
                )
            };

            let text: String = match change.kind {
                TrackerEditKind::REPLACE_WITH_MULTIPLE_NODES => {
                    let mut joiner = change.options.joiner.as_str();
                    if joiner.is_empty() {
                        joiner = self.new_line.as_str();
                    }
                    let parts: Vec<String> = change
                        .nodes
                        .iter()
                        .map(|&n| {
                            let formatted = format_node(n);
                            formatted
                                .strip_suffix(self.new_line.as_str())
                                .unwrap_or(&formatted)
                                .to_string()
                        })
                        .collect();
                    parts.join(joiner)
                }
                TrackerEditKind::REPLACE_WITH_SINGLE_NODE => format_node(change.node),
                _ => {
                    panic!(
                        "change kind {} should have been handled earlier",
                        change.kind.0
                    );
                }
            };
            // Strip initial indentation if text will be inserted in the middle of the line.
            let mut no_indent: &str = &text;
            if !(change.options.indentation.is_some()
                || format::get_line_start_position_for_position(pos, projection) == pos)
            {
                // PORT: Go `strings.TrimLeftFunc(text, unicode.IsSpace)`. Rust
                // `char::is_whitespace` is the Unicode White_Space set, which is
                // Go's `unicode.IsSpace` set (including U+0085 and U+00A0).
                no_indent = text.trim_start_matches(char::is_whitespace);
            }
            let suffix = if no_indent.ends_with(change.options.suffix.as_str()) {
                ""
            } else {
                change.options.suffix.as_str()
            };
            let candidate = change.options.prefix.clone() + no_indent + suffix;
            if found && candidate != result {
                self.unmappable_files
                    .insert(source_file_original_file_name(source_file).to_string());
                return String::new();
            }
            result = candidate;
            found = true;
        }
        if !found {
            self.unmappable_files
                .insert(source_file_original_file_name(source_file).to_string());
        }
        result
    }

    // Go: ls/change/trackerimpl.go:122 getFormattedTextOfNode
    /** Note: this may mutate `nodeIn`. */
    // PORT: Go passes `options NodeOptions` by value; it is only read, so it
    // is passed by reference.
    fn get_formatted_text_of_node(
        &self,
        node_in: Node,
        target_source_file: Node,
        source_file: Node,
        pos: i32,
        options: &NodeOptions,
    ) -> String {
        let (text, source_file_like) = self.get_nonformatted_text(node_in, target_source_file);
        // !!! if (validate) validate(node, text);
        let format_options =
            get_format_code_settings_for_writing(self.format_settings.clone(), target_source_file);

        let initial_indentation: i32;
        let mut delta: i32 = 0;
        match options.indentation {
            None => {
                initial_indentation = format::get_indentation(
                    pos,
                    source_file,
                    &format_options,
                    options.prefix == self.new_line
                        || format::get_line_start_position_for_position(pos, source_file) == pos,
                );
            }
            Some(indentation) => {
                initial_indentation = indentation;
            }
        }

        if let Some(options_delta) = options.delta {
            delta = options_delta;
        } else if format_options.editor_settings.indent_size != 0
            && format::should_indent_child_node(&format_options, node_in, Node::NIL, Node::NIL, &[])
        {
            delta = format_options.editor_settings.indent_size;
        }

        let changes = format::format_node_given_indentation(
            &self.ctx,
            source_file_like,
            source_file_like,
            source_file_info(target_source_file).language_variant,
            initial_indentation,
            delta,
        );
        apply_bulk_edits(&text, &changes)
    }
}

// Go: ls/change/trackerimpl.go:114 GetFormatCodeSettingsForWriting
pub fn get_format_code_settings_for_writing(
    options: lsutil::FormatCodeSettings,
    source_file: Node,
) -> lsutil::FormatCodeSettings {
    let mut options = options;
    let should_auto_detect_semicolon_preference =
        options.semicolons == lsutil::SemicolonPreference::IGNORE;
    let should_remove_semicolons = options.semicolons == lsutil::SemicolonPreference::REMOVE
        || should_auto_detect_semicolon_preference
            && !lsutil::probably_uses_semicolons(source_file);
    if should_remove_semicolons {
        options.semicolons = lsutil::SemicolonPreference::REMOVE;
    }

    options
}

impl Tracker {
    // Go: ls/change/trackerimpl.go:124 getNonformattedText
    fn get_nonformatted_text(&self, node: Node, source_file: Node) -> (String, Node) {
        let (text, node_out) = print_and_position_node(
            self.node_factory(),
            node,
            source_file,
            &self.new_line,
            self.format_settings.editor_settings.indent_size,
            Some(Rc::clone(&self.emit_context)),
        );
        // PORT: Go passes `ast.SourceFileParseOptions{FileName, Path}`; the
        // Rust function takes the file name and path (see its PORT note).
        let source_file_like = create_synthetic_source_file(
            self.node_factory(),
            node_out,
            &text,
            source_file_file_name(source_file),
            &source_file_info(source_file).path,
        );
        (text, source_file_like)
    }

    // Go: ls/change/trackerimpl.go:167 GetAdjustedRange
    // method on the changeTracker because use of converters
    /// GetAdjustedRange computes the adjusted range for a node in a source file, accounting for trivia.
    pub fn get_adjusted_range(
        &mut self,
        source_file: Node,
        start_node: Node,
        end_node: Node,
        leading_option: LeadingTriviaOption,
        trailing_option: TrailingTriviaOption,
    ) -> lsproto::Range {
        let text_range = TextRange::new(
            self.get_adjusted_start_position(source_file, start_node, leading_option, false),
            self.get_adjusted_end_position(source_file, end_node, trailing_option),
        );
        self.to_lsp_edit_range(source_file, text_range)
    }

    // Go: ls/change/trackerimpl.go:172 getAdjustedStartPosition
    // method on the changeTracker because use of converters
    pub fn get_adjusted_start_position(
        &self,
        source_file: Node,
        node: Node,
        leading_option: LeadingTriviaOption,
        has_trailing_comment: bool,
    ) -> i32 {
        let text = source_file_text(source_file);
        if leading_option == LeadingTriviaOption::JS_DOC {
            let js_doc_comments =
                get_js_doc_comment_ranges(self.node_factory(), Vec::new(), node, text);
            if !js_doc_comments.is_empty() {
                return format::get_line_start_position_for_position(
                    js_doc_comments[0].pos(),
                    source_file,
                );
            }
        }

        let start = astnav::get_start_of_node(node, source_file, false);
        let start_of_line_pos = format::get_line_start_position_for_position(start, source_file);

        match leading_option {
            LeadingTriviaOption::EXCLUDE => return start,
            LeadingTriviaOption::START_LINE => {
                if node.loc().contains_inclusive(start_of_line_pos) {
                    return start_of_line_pos;
                }
                return start;
            }
            _ => {}
        }

        let full_start = node.pos();
        if full_start == start {
            return start;
        }
        let line_starts = &*get_ecma_line_starts(source_file);
        let full_start_line_index = compute_line_of_position(line_starts, full_start);
        let full_start_line_pos = line_starts[full_start_line_index as usize];
        if start_of_line_pos == full_start_line_pos {
            // full start and start of the node are on the same line
            //   a,     b;
            //    ^     ^
            //    |   start
            // fullstart
            // when b is replaced - we usually want to keep the leading trvia
            // when b is deleted - we delete it
            if leading_option == LeadingTriviaOption::INCLUDE_ALL {
                return full_start;
            }
            return start;
        }

        // if node has a trailing comments, use comment end position as the text has already been included.
        if has_trailing_comment {
            // Check first for leading comments as if the node is the first import, we want to exclude the trivia;
            // otherwise we get the trailing comments.
            let mut comments = get_leading_comment_ranges(self.node_factory(), text, full_start);
            if comments.is_empty() {
                comments = get_trailing_comment_ranges(self.node_factory(), text, full_start);
            }
            if !comments.is_empty() {
                return skip_trivia_ex(
                    text,
                    comments[0].end(),
                    Some(&SkipTriviaOptions {
                        stop_after_line_break: true,
                        stop_at_comments: true,
                        ..SkipTriviaOptions::default()
                    }),
                );
            }
        }

        // get start position of the line following the line that contains fullstart position
        // (but only if the fullstart isn't the very beginning of the file)
        let next_line_start: i32 = if full_start > 0 { 1 } else { 0 };
        let mut adjusted_start_position =
            line_starts[(full_start_line_index + next_line_start) as usize];
        // skip whitespaces/newlines
        adjusted_start_position = skip_trivia_ex(
            text,
            adjusted_start_position,
            Some(&SkipTriviaOptions {
                stop_at_comments: true,
                ..SkipTriviaOptions::default()
            }),
        );
        line_starts[compute_line_of_position(line_starts, adjusted_start_position) as usize]
    }

    // Go: ls/change/trackerimpl.go:237 getEndPositionOfMultilineTrailingComment
    // method on the changeTracker because of converters
    // Return the end position of a multiline comment of it is on another line; otherwise returns `undefined`;
    fn get_end_position_of_multiline_trailing_comment(
        &self,
        source_file: Node,
        node: Node,
        trailing_opt: TrailingTriviaOption,
    ) -> i32 {
        if trailing_opt == TrailingTriviaOption::INCLUDE {
            // If the trailing comment is a multiline comment that extends to the next lines,
            // return the end of the comment and track it for the next nodes to adjust.
            let line_starts = &*get_ecma_line_starts(source_file);
            let node_end_line = compute_line_of_position(line_starts, node.end());
            let text = source_file_text(source_file);
            for comment in get_trailing_comment_ranges(self.node_factory(), text, node.end()) {
                // Single line can break the loop as trivia will only be this line.
                // Comments on subsequent lines are also ignored.
                if comment.kind == SyntaxKind::SingleLineCommentTrivia
                    || compute_line_of_position(line_starts, comment.pos()) > node_end_line
                {
                    break;
                }

                // Get the end line of the comment and compare against the end line of the node.
                // If the comment end line position and the multiline comment extends to multiple lines,
                // then is safe to return the end position.
                let comment_end_line = compute_line_of_position(line_starts, comment.end());
                if comment_end_line > node_end_line {
                    return skip_trivia_ex(
                        text,
                        comment.end(),
                        Some(&SkipTriviaOptions {
                            stop_after_line_break: true,
                            stop_at_comments: true,
                            ..SkipTriviaOptions::default()
                        }),
                    );
                }
            }
        }

        0
    }

    // Go: ls/change/trackerimpl.go:263 getAdjustedEndPosition
    // method on the changeTracker because of converters
    pub fn get_adjusted_end_position(
        &self,
        source_file: Node,
        node: Node,
        trailing_trivia_option: TrailingTriviaOption,
    ) -> i32 {
        if trailing_trivia_option == TrailingTriviaOption::EXCLUDE {
            return node.end();
        }
        let text = source_file_text(source_file);
        if trailing_trivia_option == TrailingTriviaOption::EXCLUDE_WHITESPACE {
            let mut comments = get_trailing_comment_ranges(self.node_factory(), text, node.end());
            comments.extend(get_leading_comment_ranges(
                self.node_factory(),
                text,
                node.end(),
            ));
            if !comments.is_empty() {
                let real_end = comments[comments.len() - 1].end();
                if real_end != 0 {
                    return real_end;
                }
            }
            return node.end();
        }

        let multiline_end_position = self.get_end_position_of_multiline_trailing_comment(
            source_file,
            node,
            trailing_trivia_option,
        );
        if multiline_end_position != 0 {
            return multiline_end_position;
        }

        let new_end = skip_trivia_ex(
            text,
            node.end(),
            Some(&SkipTriviaOptions {
                stop_after_line_break: true,
                ..SkipTriviaOptions::default()
            }),
        );

        if new_end != node.end()
            && (trailing_trivia_option == TrailingTriviaOption::INCLUDE
                || is_line_break(char::from(text.as_bytes()[(new_end - 1) as usize])))
        {
            return new_end;
        }
        node.end()
    }
}

// ============= utilities =============

// Go: ls/change/trackerimpl.go:293 hasCommentsBeforeLineBreak
pub fn has_comments_before_line_break(text: &str, start: i32) -> bool {
    // PORT: Go `[]rune(text[start:])` decodes runes from byte `start`
    // (invalid bytes become U+FFFD). Go `text[start:]` panics past the end.
    let mut pos = start as usize;
    assert!(pos <= text.len(), "slice bounds out of range");
    while pos < text.len() {
        let (r, size) = utf8_decode_rune_in_string(text, pos);
        let ch = rune_to_char(r);
        if !is_white_space_single_line(ch) {
            return ch == '/';
        }
        pos += size as usize;
    }
    false
}

// Go: ls/change/trackerimpl.go:302 needSemicolonBetween
pub fn need_semicolon_between(a: Node, b: Node) -> bool {
    (is_property_signature_declaration(a) || is_property_declaration(a))
        && is_class_or_type_element(b)
        && b.name().kind() == SyntaxKind::ComputedPropertyName
        || is_statement_but_not_declaration(a) && is_statement_but_not_declaration(b) // TODO: only if b would start with a `(` or `[`
}

impl Tracker {
    // Go: ls/change/trackerimpl.go:310 getInsertionPositionAtSourceFileTop
    pub fn get_insertion_position_at_source_file_top(&self, source_file: Node) -> i32 {
        let mut last_prologue = Node::NIL;
        for node in source_file.statements() {
            if is_prologue_directive(node) {
                last_prologue = node;
            } else {
                break;
            }
        }

        let mut position: i32 = 0;
        let text = source_file_text(source_file);
        // PORT: Go `advancePastLineBreak` is a closure over `position`; here a
        // nested fn that takes it by reference.
        fn advance_past_line_break(position: &mut i32, text: &str) {
            let bytes = text.as_bytes();
            if *position as usize >= bytes.len() {
                return;
            }
            let char = char::from(bytes[*position as usize]);
            if is_line_break(char) {
                *position += 1;
                if (*position as usize) < bytes.len()
                    && char == '\r'
                    && char::from(bytes[*position as usize]) == '\n'
                {
                    *position += 1;
                }
            }
        }
        if last_prologue.is_some() {
            position = last_prologue.end();
            advance_past_line_break(&mut position, text);
            return position;
        }

        let shebang = get_shebang(text);
        if !shebang.is_empty() {
            position = shebang.len() as i32;
            advance_past_line_break(&mut position, text);
        }

        let ranges = get_leading_comment_ranges(self.node_factory(), text, position);
        if ranges.is_empty() {
            return position;
        }
        // Find the first attached comment to the first node and add before it
        let mut last_comment: Option<CommentRange> = None;
        let mut pinned_or_triple_slash = false;
        let mut first_node_line: i32 = -1;

        let len_statements = source_file.statements().len();
        let line_map = &*get_ecma_line_starts(source_file);
        for r in ranges {
            if r.kind == SyntaxKind::MultiLineCommentTrivia {
                if is_pinned_comment(text, r) {
                    last_comment = Some(r);
                    pinned_or_triple_slash = true;
                    continue;
                }
            } else if is_recognized_triple_slash_comment(text, r) {
                last_comment = Some(r);
                pinned_or_triple_slash = true;
                continue;
            }

            if let Some(last_comment) = last_comment {
                // Always insert after pinned or triple slash comments
                if pinned_or_triple_slash {
                    break;
                }

                // There was a blank line between the last comment and this comment.
                // This comment is not part of the copyright comments
                let comment_line = compute_line_of_position(line_map, r.pos());
                let last_comment_end_line = compute_line_of_position(line_map, last_comment.end());
                if comment_line >= last_comment_end_line + 2 {
                    break;
                }
            }

            if len_statements > 0 {
                if first_node_line == -1 {
                    first_node_line = compute_line_of_position(
                        line_map,
                        astnav::get_start_of_node(
                            source_file.statements().get(0),
                            source_file,
                            false,
                        ),
                    );
                }
                let comment_end_line = compute_line_of_position(line_map, r.end());
                if first_node_line < comment_end_line + 2 {
                    break;
                }
            }
            last_comment = Some(r);
            pinned_or_triple_slash = false;
        }

        if let Some(last_comment) = last_comment {
            position = last_comment.end();
            advance_past_line_break(&mut position, text);
        }
        position
    }
}
