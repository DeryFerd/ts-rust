use crate::ls::prelude::*;

// Go `internal/ls/folding.go`: textDocument/foldingRange.

use crate::frontend::scanner::get_leading_comment_ranges;

impl LanguageService {
    // Go: ls/folding.go:18 ProvideFoldingRange
    pub fn provide_folding_range(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
    ) -> Result<lsproto::FoldingRangeResponse, GoError> {
        let (_, source_file) = self.get_program_and_file(document_uri);
        let mut res = self.add_node_outlining_spans(ctx, source_file);
        res.extend(self.add_region_outlining_spans(ctx, source_file));
        if lsproto::get_client_capabilities(ctx)
            .text_document
            .folding_range
            .line_folding_only
        {
            res = self.adjust_folding_end(res, source_file);
        }
        crate::gostd::slices::sort_func(&mut res, |a, b| {
            let c = a.start_line.cmp(&b.start_line) as i32;
            if c != 0 {
                return c;
            }
            // PORT: Go dereferences `*a.StartCharacter`; a nil pointer panics
            // there as `unwrap` panics here. Every range made in this file
            // sets it.
            a.start_character.unwrap().cmp(&b.start_character.unwrap()) as i32
        });
        Ok(lsproto::FoldingRangesOrNull {
            folding_ranges: Some(res),
        })
    }

    // Go: ls/folding.go:38 adjustFoldingEnd
    // adjustFoldingEnd adjusts the end line of folding ranges when the client signals lineFoldingOnly.
    // This mirrors the behavior of VS Code's built-in TypeScript extension (workaround for vscode#47240).
    // When lineFoldingOnly is true, we hide lines from startLine+1 to endLine. And to keep closing
    // brackets/braces visible, we subtract 1 from endLine when the range ends with a closing pair character.
    // PORT: Go mutates the shared `*FoldingRange` values; the Rust ranges are
    // owned, so the adjusted values are moved into the result.
    fn adjust_folding_end(
        &self,
        ranges: Vec<lsproto::FoldingRange>,
        source_file: Node,
    ) -> Vec<lsproto::FoldingRange> {
        let source_text = source_file_text(source_file);
        let mut result = Vec::with_capacity(ranges.len());
        for mut r in ranges {
            if r.end_character.is_some() && r.end_character.unwrap() > 0 {
                let end_offset = self.converters.line_and_character_to_position(
                    &source_file,
                    &lsproto::Position {
                        line: r.end_line,
                        character: r.end_character.unwrap(),
                    },
                );
                if end_offset > 0 && end_offset as usize <= source_text.len() {
                    let fold_end_char = source_text.as_bytes()[(end_offset - 1) as usize];
                    if fold_end_char == b'}'
                        || fold_end_char == b']'
                        || fold_end_char == b')'
                        || fold_end_char == b'`'
                        || fold_end_char == b'>'
                    {
                        if r.end_line > r.start_line {
                            r.end_line -= 1;
                        }
                    }
                }
            }
            result.push(r);
        }
        result
    }

    // Go: ls/folding.go:61 addNodeOutliningSpans
    fn add_node_outlining_spans(
        &self,
        ctx: &Context,
        source_file: Node,
    ) -> Vec<lsproto::FoldingRange> {
        let depth_remaining = 40;
        let mut current = 0;

        let statements = source_file.statements();
        let n = statements.len();
        let mut folding_range = Vec::with_capacity(40);
        while current < n {
            while current < n && !is_any_import_syntax(statements.get(current)) {
                folding_range.extend(visit_node(
                    ctx,
                    statements.get(current),
                    depth_remaining,
                    source_file,
                    self,
                ));
                current += 1;
            }
            if current == n {
                break;
            }
            let first_import = current;
            while current < n && is_any_import_syntax(statements.get(current)) {
                folding_range.extend(visit_node(
                    ctx,
                    statements.get(current),
                    depth_remaining,
                    source_file,
                    self,
                ));
                current += 1;
            }
            let last_import = current - 1;
            if last_import != first_import {
                let folding_range_kind = lsproto::FoldingRangeKind::IMPORTS;
                folding_range.push(create_folding_range_from_bounds(
                    ctx,
                    astnav::get_start_of_node(
                        astnav::find_child_of_kind(
                            statements.get(first_import),
                            SyntaxKind::ImportKeyword,
                            source_file,
                        ),
                        source_file,
                        false, /*includeJSDoc*/
                    ),
                    statements.get(last_import).end(),
                    folding_range_kind,
                    source_file,
                    self,
                ));
            }
        }

        // Visit the EOF Token so that comments which aren't attached to statements are included.
        folding_range.extend(visit_node(
            ctx,
            source_file.end_of_file_token(),
            depth_remaining,
            source_file,
            self,
        ));
        folding_range
    }

    // Go: ls/folding.go:101 addRegionOutliningSpans
    fn add_region_outlining_spans(
        &self,
        ctx: &Context,
        source_file: Node,
    ) -> Vec<lsproto::FoldingRange> {
        let mut regions: Vec<lsproto::FoldingRange> = Vec::with_capacity(40);
        let mut out = Vec::with_capacity(40);
        let line_starts = &*get_ecma_line_starts(source_file);
        for &current_line_start in line_starts {
            let line_end = get_line_end_of_position(source_file, current_line_start);
            // PORT: Go slices the text by bytes. A line that ends in a
            // multi-byte line terminator (U+2028, U+2029) leaves a partial
            // rune at `lineEnd`. Go keeps those invalid bytes; Rust cannot
            // hold them in a `&str`, so the line text is decoded lossily
            // (U+FFFD). Byte positions below use `line_bytes`.
            let line_bytes = &source_file_text(source_file).as_bytes()
                [current_line_start as usize..line_end as usize];
            let line_text = String::from_utf8_lossy(line_bytes);
            let result = parse_region_delimiter(&line_text);
            if result.is_none()
                || is_in_comment(
                    source_file,
                    current_line_start,
                    astnav::get_token_at_position(source_file, current_line_start),
                )
                .is_some()
            {
                continue;
            }
            let result = result.unwrap();

            if result.is_start {
                // PORT: Go `strings.Index(line, "//")`, a byte index or -1.
                let comment_index = line_bytes
                    .windows(2)
                    .position(|w| w == b"//")
                    .map_or(-1, |i| i as i32);
                let comment_start =
                    self.create_lsp_position(comment_index + current_line_start, source_file);
                let folding_range_kind_region = lsproto::FoldingRangeKind::REGION;
                let mut region = lsproto::FoldingRange {
                    start_line: comment_start.line,
                    start_character: Some(comment_start.character),
                    kind: Some(folding_range_kind_region),
                    ..Default::default()
                };
                if supports_collapsed_text(ctx) {
                    let mut collapsed_text = "#region".to_string();
                    if !result.name.is_empty() {
                        collapsed_text = result.name.clone();
                    }
                    region.collapsed_text = Some(collapsed_text);
                }
                // Our spans start out with some initial data.
                // On every `#endregion`, we'll come back to these `FoldingRange`s
                // and fill in their EndLine/EndCharacter.
                regions.push(region);
            } else {
                if !regions.is_empty() {
                    let mut region = regions.pop().unwrap();
                    let ending_position = self.create_lsp_position(line_end, source_file);
                    region.end_line = ending_position.line;
                    region.end_character = Some(ending_position.character);
                    out.push(region);
                }
            }
        }
        out
    }
}

// Go: ls/folding.go:146 visitNode
fn visit_node(
    ctx: &Context,
    n: Node,
    depth_remaining: i32,
    source_file: Node,
    l: &LanguageService,
) -> Vec<lsproto::FoldingRange> {
    let mut depth_remaining = depth_remaining;
    if n.flags().intersects(NodeFlags::REPARSED) || depth_remaining == 0 || ctx.err().is_some() {
        return Vec::new();
    }
    let mut folding_range = Vec::with_capacity(40);
    if (!is_binary_expression(n) && is_declaration(n))
        || is_variable_statement(n)
        || is_return_statement(n)
        || is_call_or_new_expression(n)
        || n.kind() == SyntaxKind::EndOfFile
    {
        folding_range.extend(add_outlining_for_leading_comments_for_node(
            ctx,
            n,
            source_file,
            l,
        ));
    }
    if is_function_like(n)
        && n.parent().is_some()
        && is_binary_expression(n.parent())
        && n.parent().left().is_some()
        && is_property_access_expression(n.parent().left())
    {
        folding_range.extend(add_outlining_for_leading_comments_for_node(
            ctx,
            n.parent().left(),
            source_file,
            l,
        ));
    }
    if is_block(n) {
        let statements = n.statement_list();
        if statements.is_some() {
            folding_range.extend(add_outlining_for_leading_comments_for_pos(
                ctx,
                statements.end(),
                source_file,
                l,
            ));
        }
    }
    if is_module_block(n) {
        let statements = n.statement_list();
        if statements.is_some() {
            folding_range.extend(add_outlining_for_leading_comments_for_pos(
                ctx,
                statements.end(),
                source_file,
                l,
            ));
        }
    }
    if is_class_like(n) || is_interface_declaration(n) {
        // PORT: Go reads the `Members` field of ClassDeclaration,
        // ClassExpression or InterfaceDeclaration; `member_list()` is that
        // field for each of them.
        let members;
        if is_class_declaration(n) {
            members = n.member_list();
        } else if is_class_expression(n) {
            members = n.member_list();
        } else {
            members = n.member_list();
        }
        if members.is_some() {
            folding_range.extend(add_outlining_for_leading_comments_for_pos(
                ctx,
                members.end(),
                source_file,
                l,
            ));
        }
    }

    let span = get_outlining_span_for_node(ctx, n, source_file, l);
    if let Some(span) = span {
        folding_range.push(span);
    }

    depth_remaining -= 1;
    if is_call_expression(n) {
        depth_remaining += 1;
        let expression_nodes = visit_node(ctx, n.expression(), depth_remaining, source_file, l);
        // PORT: Go `if expressionNodes != nil`; appending an empty slice is a no-op.
        if !expression_nodes.is_empty() {
            folding_range.extend(expression_nodes);
        }
        depth_remaining -= 1;
        for arg in n.arguments() {
            if arg.is_some() {
                folding_range.extend(visit_node(ctx, arg, depth_remaining, source_file, l));
            }
        }
        let type_arguments = n.type_arguments();
        for type_arg in type_arguments {
            if type_arg.is_some() {
                folding_range.extend(visit_node(ctx, type_arg, depth_remaining, source_file, l));
            }
        }
    } else if is_if_statement(n)
        && n.else_statement().is_some()
        && is_if_statement(n.else_statement())
    {
        // Consider an 'else if' to be on the same depth as the 'if'.
        let if_statement = n;
        let expression_nodes = visit_node(ctx, n.expression(), depth_remaining, source_file, l);
        if !expression_nodes.is_empty() {
            folding_range.extend(expression_nodes);
        }
        let then_node = visit_node(
            ctx,
            if_statement.then_statement(),
            depth_remaining,
            source_file,
            l,
        );
        if !then_node.is_empty() {
            folding_range.extend(then_node);
        }
        depth_remaining += 1;
        let else_node = visit_node(
            ctx,
            if_statement.else_statement(),
            depth_remaining,
            source_file,
            l,
        );
        if !else_node.is_empty() {
            folding_range.extend(else_node);
        }
        // Go decrements depthRemaining here; nothing reads it after this.
    } else {
        n.for_each_child(|node| {
            let child_node = visit_node(ctx, node, depth_remaining, source_file, l);
            if !child_node.is_empty() {
                folding_range.extend(child_node);
            }
            false
        });
    }
    // PORT: Go `depthRemaining++` here; the value is not read again.
    folding_range
}

// Go: ls/folding.go:238 addOutliningForLeadingCommentsForNode
fn add_outlining_for_leading_comments_for_node(
    ctx: &Context,
    n: Node,
    source_file: Node,
    l: &LanguageService,
) -> Vec<lsproto::FoldingRange> {
    if is_jsx_text(n) {
        return Vec::new();
    }
    add_outlining_for_leading_comments_for_pos(ctx, n.pos(), source_file, l)
}

// Go: ls/folding.go:245 addOutliningForLeadingCommentsForPos
fn add_outlining_for_leading_comments_for_pos(
    ctx: &Context,
    pos: i32,
    source_file: Node,
    l: &LanguageService,
) -> Vec<lsproto::FoldingRange> {
    let p = Rc::new(EmitContext::default());
    let mut folding_range = Vec::with_capacity(40);
    let mut first_single_line_comment_start = -1;
    let mut last_single_line_comment_end = -1;
    let mut single_line_comment_count = 0;
    let folding_range_kind_comment = lsproto::FoldingRangeKind::COMMENT;

    // PORT: the Go closure reads the three counters above. Rust passes them
    // in, so the loop can still update them.
    let combine_and_add_multiple_single_line_comments = |single_line_comment_count: i32,
                                                         first_single_line_comment_start: i32,
                                                         last_single_line_comment_end: i32|
     -> Option<lsproto::FoldingRange> {
        // Only outline spans of two or more consecutive single line comments
        if single_line_comment_count > 1 {
            return Some(create_folding_range_from_bounds(
                ctx,
                first_single_line_comment_start,
                last_single_line_comment_end,
                folding_range_kind_comment.clone(),
                source_file,
                l,
            ));
        }
        None
    };

    let source_text = source_file_text(source_file);
    let factory = crate::printer::factory::NodeFactory::new(&p);
    for comment in get_leading_comment_ranges(factory.as_node_factory(), source_text, pos) {
        let comment_pos = comment.pos();
        let comment_end = comment.end();

        if ctx.err().is_some() {
            return Vec::new();
        }
        match comment.kind {
            SyntaxKind::SingleLineCommentTrivia => {
                // never fold region delimiters into single-line comment regions
                let comment_text = &source_text[comment_pos as usize..comment_end as usize];
                if parse_region_delimiter(comment_text).is_some() {
                    let comments = combine_and_add_multiple_single_line_comments(
                        single_line_comment_count,
                        first_single_line_comment_start,
                        last_single_line_comment_end,
                    );
                    if let Some(comments) = comments {
                        folding_range.push(comments);
                    }
                    single_line_comment_count = 0;
                    // PORT: Go `break` leaves the switch; nothing follows it in the loop body.
                    continue;
                }

                // For single line comments, combine consecutive ones (2 or more) into
                // a single span from the start of the first till the end of the last
                if single_line_comment_count == 0 {
                    first_single_line_comment_start = comment_pos;
                }
                last_single_line_comment_end = comment_end;
                single_line_comment_count += 1;
            }
            SyntaxKind::MultiLineCommentTrivia => {
                let comments = combine_and_add_multiple_single_line_comments(
                    single_line_comment_count,
                    first_single_line_comment_start,
                    last_single_line_comment_end,
                );
                if let Some(comments) = comments {
                    folding_range.push(comments);
                }
                folding_range.push(create_folding_range_from_bounds(
                    ctx,
                    comment_pos,
                    comment_end,
                    folding_range_kind_comment.clone(),
                    source_file,
                    l,
                ));
                single_line_comment_count = 0;
            }
            _ => crate::gostd::debug::assert_never(
                &crate::gostd::debug::kind_string(comment.kind),
                None,
            ),
        }
    }
    let added_comments = combine_and_add_multiple_single_line_comments(
        single_line_comment_count,
        first_single_line_comment_start,
        last_single_line_comment_end,
    );
    if let Some(added_comments) = added_comments {
        folding_range.push(added_comments);
    }
    folding_range
}

// Go: ls/folding.go:309 regionDelimiterResult
struct RegionDelimiterResult {
    is_start: bool,
    name: String,
}

// Go: ls/folding.go:314 parseRegionDelimiter
fn parse_region_delimiter(line_text: &str) -> Option<RegionDelimiterResult> {
    // We trim the leading whitespace and // without the regex since the
    // multiple potential whitespace matches can make for some gnarly backtracking behavior
    // PORT: Go `unicode.IsSpace` and Rust `char::is_whitespace` are both the
    // Unicode White_Space set; Go `strings.TrimSpace` is Rust `trim`.
    let mut line_text = line_text.trim_start_matches(char::is_whitespace);
    if !line_text.starts_with("//") {
        return None;
    }
    line_text = line_text[2..].trim();
    line_text = line_text.strip_suffix('\r').unwrap_or(line_text);
    if !line_text.starts_with('#') {
        return None;
    }
    line_text = &line_text[1..];
    let mut is_start = true;
    if line_text.starts_with("end") {
        is_start = false;
        line_text = &line_text[3..];
    }
    if !line_text.starts_with("region") {
        return None;
    }
    line_text = &line_text[6..];
    Some(RegionDelimiterResult {
        is_start,
        name: line_text.trim().to_string(),
    })
}

// Go: ls/folding.go:342 getOutliningSpanForNode
fn get_outlining_span_for_node(
    ctx: &Context,
    n: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    match n.kind() {
        SyntaxKind::Block => {
            if is_function_like(n.parent()) {
                return function_span(ctx, n.parent(), n, source_file, l);
            }
            // Check if the block is standalone, or 'attached' to some parent statement.
            // If the latter, we want to collapse the block, but consider its hint span
            // to be the entire span of the parent.
            match n.parent().kind() {
                SyntaxKind::DoStatement
                | SyntaxKind::ForInStatement
                | SyntaxKind::ForOfStatement
                | SyntaxKind::ForStatement
                | SyntaxKind::IfStatement
                | SyntaxKind::WhileStatement
                | SyntaxKind::WithStatement
                | SyntaxKind::CatchClause => {
                    return span_for_node(
                        ctx,
                        n,
                        SyntaxKind::OpenBraceToken,
                        true, /*useFullStart*/
                        source_file,
                        l,
                    );
                }
                SyntaxKind::TryStatement => {
                    // Could be the try-block, or the finally-block.
                    let try_statement = n.parent();
                    if try_statement.try_block() == n {
                        return span_for_node(
                            ctx,
                            n,
                            SyntaxKind::OpenBraceToken,
                            true, /*useFullStart*/
                            source_file,
                            l,
                        );
                    } else if try_statement.finally_block() == n {
                        if let Some(span) = span_for_node(
                            ctx,
                            n,
                            SyntaxKind::OpenBraceToken,
                            true, /*useFullStart*/
                            source_file,
                            l,
                        ) {
                            return Some(span);
                        }
                    }
                    // PORT: Go `fallthrough` into the default case.
                    // Block was a standalone block.  In this case we want to only collapse
                    // the span of the block, independent of any parent span.
                    return Some(create_folding_range(
                        ctx,
                        l.create_lsp_range_from_node(n, source_file),
                        lsproto::FoldingRangeKind::default(),
                        "",
                    ));
                }
                _ => {
                    // Block was a standalone block.  In this case we want to only collapse
                    // the span of the block, independent of any parent span.
                    return Some(create_folding_range(
                        ctx,
                        l.create_lsp_range_from_node(n, source_file),
                        lsproto::FoldingRangeKind::default(),
                        "",
                    ));
                }
            }
        }
        SyntaxKind::ModuleBlock => {
            return span_for_node(
                ctx,
                n,
                SyntaxKind::OpenBraceToken,
                true, /*useFullStart*/
                source_file,
                l,
            );
        }
        SyntaxKind::ClassDeclaration
        | SyntaxKind::ClassExpression
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::CaseBlock
        | SyntaxKind::TypeLiteral
        | SyntaxKind::ObjectBindingPattern => {
            return span_for_node(
                ctx,
                n,
                SyntaxKind::OpenBraceToken,
                true, /*useFullStart*/
                source_file,
                l,
            );
        }
        SyntaxKind::TupleType => {
            return span_for_node(
                ctx,
                n,
                SyntaxKind::OpenBracketToken,
                !is_tuple_type_node(n.parent()), /*useFullStart*/
                source_file,
                l,
            );
        }
        SyntaxKind::CaseClause | SyntaxKind::DefaultClause => {
            return span_for_node_array(ctx, n.statement_list(), source_file, l);
        }
        SyntaxKind::ObjectLiteralExpression => {
            return span_for_node(
                ctx,
                n,
                SyntaxKind::OpenBraceToken,
                !is_array_literal_expression(n.parent()) && !is_call_expression(n.parent()), /*useFullStart*/
                source_file,
                l,
            );
        }
        SyntaxKind::ArrayLiteralExpression => {
            return span_for_node(
                ctx,
                n,
                SyntaxKind::OpenBracketToken,
                !is_array_literal_expression(n.parent()) && !is_call_expression(n.parent()), /*useFullStart*/
                source_file,
                l,
            );
        }
        SyntaxKind::JsxElement | SyntaxKind::JsxFragment => {
            return Some(span_for_jsx_element(ctx, n, source_file, l));
        }
        SyntaxKind::JsxSelfClosingElement | SyntaxKind::JsxOpeningElement => {
            return span_for_jsx_attributes(ctx, n, source_file, l);
        }
        SyntaxKind::TemplateExpression | SyntaxKind::NoSubstitutionTemplateLiteral => {
            return span_for_template_literal(ctx, n, source_file, l);
        }
        SyntaxKind::ArrayBindingPattern => {
            return span_for_node(
                ctx,
                n,
                SyntaxKind::OpenBracketToken,
                !is_binding_element(n.parent()), /*useFullStart*/
                source_file,
                l,
            );
        }
        SyntaxKind::ArrowFunction => {
            return span_for_arrow_function(ctx, n, source_file, l);
        }
        SyntaxKind::CallExpression => {
            return span_for_call_expression(ctx, n, source_file, l);
        }
        SyntaxKind::ParenthesizedExpression => {
            return span_for_parenthesized_expression(ctx, n, source_file, l);
        }
        SyntaxKind::NamedImports | SyntaxKind::NamedExports | SyntaxKind::ImportAttributes => {
            return span_for_import_export_elements(ctx, n, source_file, l);
        }
        _ => {}
    }
    None
}

// Go: ls/folding.go:402 spanForImportExportElements
fn span_for_import_export_elements(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    let mut elements = NodeList::NIL;
    match node.kind() {
        SyntaxKind::NamedImports => elements = node.element_list(),
        SyntaxKind::NamedExports => elements = node.element_list(),
        SyntaxKind::ImportAttributes => elements = node.attribute_list(),
        _ => {}
    }
    if elements.is_nil() || elements.nodes().is_empty() {
        return None;
    }
    let open_token = astnav::find_child_of_kind(node, SyntaxKind::OpenBraceToken, source_file);
    let close_token = astnav::find_child_of_kind(node, SyntaxKind::CloseBraceToken, source_file);
    if open_token.is_nil()
        || close_token.is_nil()
        || crate::printer::positions_are_on_same_line(
            open_token.pos(),
            close_token.pos(),
            source_file,
        )
    {
        return None;
    }
    Some(range_between_tokens(
        ctx,
        open_token,
        close_token,
        source_file,
        false, /*useFullStart*/
        l,
    ))
}

// Go: ls/folding.go:423 spanForParenthesizedExpression
fn span_for_parenthesized_expression(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    let start = astnav::get_start_of_node(node, source_file, false /*includeJSDoc*/);
    if crate::printer::positions_are_on_same_line(start, node.end(), source_file) {
        return None;
    }
    let text_range = l.create_lsp_range_from_bounds(start, node.end(), source_file);
    Some(create_folding_range(
        ctx,
        text_range,
        lsproto::FoldingRangeKind::default(),
        "",
    ))
}

// Go: ls/folding.go:432 spanForCallExpression
fn span_for_call_expression(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    if node.argument_list().is_nil() || node.argument_list().nodes().is_empty() {
        return None;
    }
    let open_token = astnav::find_child_of_kind(node, SyntaxKind::OpenParenToken, source_file);
    let close_token = astnav::find_child_of_kind(node, SyntaxKind::CloseParenToken, source_file);
    if open_token.is_nil()
        || close_token.is_nil()
        || crate::printer::positions_are_on_same_line(
            open_token.pos(),
            close_token.pos(),
            source_file,
        )
    {
        return None;
    }

    Some(range_between_tokens(
        ctx,
        open_token,
        close_token,
        source_file,
        true, /*useFullStart*/
        l,
    ))
}

// Go: ls/folding.go:445 spanForArrowFunction
fn span_for_arrow_function(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    let arrow_function_node = node;
    if is_block(arrow_function_node.body())
        || is_parenthesized_expression(arrow_function_node.body())
        || crate::printer::positions_are_on_same_line(
            arrow_function_node.body().pos(),
            arrow_function_node.body().end(),
            source_file,
        )
    {
        return None;
    }
    let text_range = l.create_lsp_range_from_bounds(
        arrow_function_node.body().pos(),
        arrow_function_node.body().end(),
        source_file,
    );
    Some(create_folding_range(
        ctx,
        text_range,
        lsproto::FoldingRangeKind::default(),
        "",
    ))
}

// Go: ls/folding.go:454 spanForTemplateLiteral
fn span_for_template_literal(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    if node.kind() == SyntaxKind::NoSubstitutionTemplateLiteral && node.text().is_empty() {
        return None;
    }
    Some(create_folding_range_from_bounds(
        ctx,
        astnav::get_start_of_node(node, source_file, false /*includeJSDoc*/),
        node.end(),
        lsproto::FoldingRangeKind::default(),
        source_file,
        l,
    ))
}

// Go: ls/folding.go:461 spanForJSXElement
// PORT: Go returns a `*FoldingRange` that is never nil, so this returns the value.
fn span_for_jsx_element(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> lsproto::FoldingRange {
    if node.kind() == SyntaxKind::JsxElement {
        let jsx_element = node;
        let text_range = l.create_lsp_range_from_bounds(
            astnav::get_start_of_node(
                jsx_element.opening_element(),
                source_file,
                false, /*includeJSDoc*/
            ),
            jsx_element.closing_element().end(),
            source_file,
        );
        let tag_name = get_text_of_node(jsx_element.opening_element().tag_name());
        let banner_text = format!("<{tag_name}>...</{tag_name}>");
        return create_folding_range(
            ctx,
            text_range,
            lsproto::FoldingRangeKind::default(),
            &banner_text,
        );
    }
    // JsxFragment
    let jsx_fragment = node;
    let text_range = l.create_lsp_range_from_bounds(
        astnav::get_start_of_node(
            jsx_fragment.opening_fragment(),
            source_file,
            false, /*includeJSDoc*/
        ),
        jsx_fragment.closing_fragment().end(),
        source_file,
    );
    create_folding_range(
        ctx,
        text_range,
        lsproto::FoldingRangeKind::default(),
        "<>...</>",
    )
}

// Go: ls/folding.go:475 spanForJSXAttributes
fn span_for_jsx_attributes(
    ctx: &Context,
    node: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    let attributes;
    if node.kind() == SyntaxKind::JsxSelfClosingElement {
        attributes = node.attributes();
    } else {
        attributes = node.attributes();
    }
    if attributes.properties().is_empty() {
        return None;
    }
    Some(create_folding_range_from_bounds(
        ctx,
        astnav::get_start_of_node(node, source_file, false /*includeJSDoc*/),
        node.end(),
        lsproto::FoldingRangeKind::default(),
        source_file,
        l,
    ))
}

// Go: ls/folding.go:488 spanForNodeArray
fn span_for_node_array(
    ctx: &Context,
    statements: NodeList,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    if statements.is_some() && !statements.nodes().is_empty() {
        return Some(create_folding_range(
            ctx,
            l.create_lsp_range_from_bounds(statements.pos(), statements.end(), source_file),
            lsproto::FoldingRangeKind::default(),
            "",
        ));
    }
    None
}

// Go: ls/folding.go:495 spanForNode
fn span_for_node(
    ctx: &Context,
    node: Node,
    open: SyntaxKind,
    use_full_start: bool,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    let mut close_brace = SyntaxKind::CloseBraceToken;
    if open != SyntaxKind::OpenBraceToken {
        close_brace = SyntaxKind::CloseBracketToken;
    }
    let open_token = astnav::find_child_of_kind(node, open, source_file);
    let close_token = astnav::find_child_of_kind(node, close_brace, source_file);
    if open_token.is_some() && close_token.is_some() {
        return Some(range_between_tokens(
            ctx,
            open_token,
            close_token,
            source_file,
            use_full_start,
            l,
        ));
    }
    None
}

// Go: ls/folding.go:508 rangeBetweenTokens
// PORT: Go returns a `*FoldingRange` that is never nil, so this returns the value.
fn range_between_tokens(
    ctx: &Context,
    open_token: Node,
    close_token: Node,
    source_file: Node,
    use_full_start: bool,
    l: &LanguageService,
) -> lsproto::FoldingRange {
    let text_range;
    if use_full_start {
        text_range =
            l.create_lsp_range_from_bounds(open_token.pos(), close_token.end(), source_file);
    } else {
        text_range = l.create_lsp_range_from_bounds(
            astnav::get_start_of_node(open_token, source_file, false /*includeJSDoc*/),
            close_token.end(),
            source_file,
        );
    }
    create_folding_range(ctx, text_range, lsproto::FoldingRangeKind::default(), "")
}

// Go: ls/folding.go:518 supportsCollapsedText
fn supports_collapsed_text(ctx: &Context) -> bool {
    lsproto::get_client_capabilities(ctx)
        .text_document
        .folding_range
        .folding_range
        .collapsed_text
}

// Go: ls/folding.go:522 createFoldingRange
// PORT: Go returns a `*FoldingRange` that is never nil, so this returns the
// value. The Go empty kind `""` is `FoldingRangeKind::default()`.
fn create_folding_range(
    ctx: &Context,
    text_range: lsproto::Range,
    folding_range_kind: lsproto::FoldingRangeKind,
    collapsed_text: &str,
) -> lsproto::FoldingRange {
    let mut kind = None;
    if !folding_range_kind.0.is_empty() {
        kind = Some(folding_range_kind);
    }
    let mut result = lsproto::FoldingRange {
        start_line: text_range.start.line,
        start_character: Some(text_range.start.character),
        end_line: text_range.end.line,
        end_character: Some(text_range.end.character),
        kind,
        ..Default::default()
    };
    if !collapsed_text.is_empty() && supports_collapsed_text(ctx) {
        result.collapsed_text = Some(collapsed_text.to_string());
    }
    result
}

// Go: ls/folding.go:540 createFoldingRangeFromBounds
// PORT: Go returns a `*FoldingRange` that is never nil, so this returns the value.
fn create_folding_range_from_bounds(
    ctx: &Context,
    pos: i32,
    end: i32,
    folding_range_kind: lsproto::FoldingRangeKind,
    source_file: Node,
    l: &LanguageService,
) -> lsproto::FoldingRange {
    create_folding_range(
        ctx,
        l.create_lsp_range_from_bounds(pos, end, source_file),
        folding_range_kind,
        "",
    )
}

// Go: ls/folding.go:544 functionSpan
fn function_span(
    ctx: &Context,
    node: Node,
    body: Node,
    source_file: Node,
    l: &LanguageService,
) -> Option<lsproto::FoldingRange> {
    let open_token = try_get_function_open_token(node, body, source_file);
    let close_token = astnav::find_child_of_kind(body, SyntaxKind::CloseBraceToken, source_file);
    if open_token.is_some() && close_token.is_some() {
        return Some(range_between_tokens(
            ctx,
            open_token,
            close_token,
            source_file,
            true, /*useFullStart*/
            l,
        ));
    }
    None
}

// Go: ls/folding.go:553 tryGetFunctionOpenToken
fn try_get_function_open_token(node: Node, body: Node, source_file: Node) -> Node {
    if is_node_array_multi_line(&node.parameters().to_vec(), source_file) {
        let open_paren_token =
            astnav::find_child_of_kind(node, SyntaxKind::OpenParenToken, source_file);
        if open_paren_token.is_some() {
            return open_paren_token;
        }
    }
    astnav::find_child_of_kind(body, SyntaxKind::OpenBraceToken, source_file)
}

// Go: ls/folding.go:563 isNodeArrayMultiLine
fn is_node_array_multi_line(list: &[Node], source_file: Node) -> bool {
    if list.is_empty() {
        return false;
    }
    !crate::printer::positions_are_on_same_line(
        list[0].pos(),
        list[list.len() - 1].end(),
        source_file,
    )
}
