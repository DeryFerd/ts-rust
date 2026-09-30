use crate::ls::prelude::*;

// Port of Go `internal/ls/jsdoc_snippet.go` (tsgo#4505): the `/** */`
// completion and its doc comment template.
//
// PORT: Go decodes runes with `stringutil.DecodeJSStringRune` and tests them
// with `stringutil.IsWhiteSpace*`. A Go rune can be a lone surrogate, which
// is not a Rust `char`; it is not white space, so `char::from_u32` failing
// counts as "not white space".

// Go: ls/jsdoc_snippet.go:19 docCommentTemplate
struct DocCommentTemplate {
    new_text: String,
}

// Go: ls/jsdoc_snippet.go:23 commentOwnerInfo
struct CommentOwnerInfo {
    comment_owner: Node,
    parameters: Vec<Node>,
    has_return: bool,
}

impl LanguageService {
    // Go: ls/jsdoc_snippet.go:29 getJSDocSnippetCompletion
    pub fn get_js_doc_snippet_completion(
        &self,
        ctx: &Context,
        file: Node,
        position: i32,
    ) -> Option<CompletionList> {
        if self.user_preferences().enable_js_doc_completions.is_false() {
            return None;
        }
        if !is_potentially_valid_js_doc_snippet_completion_position(file, position) {
            return None;
        }
        let mut new_line = self.format_options().editor_settings.new_line_character;
        if new_line.is_empty() {
            new_line = "\n".to_string();
        }
        let template = get_doc_comment_template_at_position(
            file,
            position,
            self.user_preferences()
                .generate_return_in_doc_template
                .is_true(),
            &new_line,
            &self.get_program().get_current_directory(),
        )?;

        let mut insert_text = template.new_text;
        let mut insert_text_format = None;
        if client_supports_item_snippet(ctx) {
            insert_text = template_to_snippet(&insert_text, &new_line);
            insert_text_format = Some(lsproto::InsertTextFormat::SNIPPET);
        }

        let edit_range =
            self.get_js_doc_snippet_completion_range(ctx, file, position, &insert_text);
        let mut commit_characters = None;
        if client_supports_item_commit_characters(ctx) {
            commit_characters = Some(Vec::new());
        }
        let item = CompletionItem {
            completion_item: lsproto::CompletionItem {
                label: "/** */".to_string(),
                kind: Some(lsproto::CompletionItemKind::TEXT),
                detail: Some(crate::diagnostics_loc::message_localize(
                    diag::JSDoc_comment,
                    &locale::from_context(ctx),
                    &[],
                )),
                sort_text: Some("\u{0}".to_string()),
                insert_text_format,
                text_edit: edit_range,
                commit_characters,
                ..Default::default()
            },
            ..Default::default()
        };
        Some(CompletionList {
            is_incomplete: false,
            items: vec![item],
            ..Default::default()
        })
    }

    // Go: ls/jsdoc_snippet.go:86 getJSDocSnippetCompletionRange
    // PORT: Go returns `*lsproto.TextEditOrInsertReplaceEdit`; nil is `None`.
    fn get_js_doc_snippet_completion_range(
        &self,
        ctx: &Context,
        file: Node,
        position: i32,
        new_text: &str,
    ) -> Option<lsproto::TextEditOrInsertReplaceEdit> {
        let text = source_file_text(file);
        let line_start = crate::format::get_line_start_position_for_position(position, file);
        let prefix = go_text_slice(&text, line_start, position);
        let mut start = position;
        if let Some(prefix_start) = get_js_doc_snippet_prefix_start(prefix) {
            start = line_start + prefix_start as i32;
        }

        let line_end = get_line_end_of_position(file, position);
        let suffix = go_text_slice(&text, position, line_end);
        let mut end = position;
        if let Some(suffix_end) = get_js_doc_snippet_suffix_end(suffix) {
            end += suffix_end as i32;
        }

        let (replacement_range, fidelity) = self.create_lsp_range_from_bounds(start, end, file);
        if !fidelity.is_exact() {
            return None;
        }
        if client_supports_item_insert_replace(ctx) {
            return Some(lsproto::TextEditOrInsertReplaceEdit {
                insert_replace_edit: Some(lsproto::InsertReplaceEdit {
                    new_text: new_text.to_string(),
                    insert: replacement_range,
                    replace: replacement_range,
                }),
                ..Default::default()
            });
        }
        Some(lsproto::TextEditOrInsertReplaceEdit {
            text_edit: Some(lsproto::TextEdit {
                new_text: new_text.to_string(),
                range: replacement_range,
            }),
            ..Default::default()
        })
    }
}

// Go: ls/jsdoc_snippet.go:73 isPotentiallyValidJSDocSnippetCompletionPosition
pub fn is_potentially_valid_js_doc_snippet_completion_position(file: Node, position: i32) -> bool {
    let text = source_file_text(file);
    let line_start = crate::format::get_line_start_position_for_position(position, file);
    let prefix = go_text_slice(&text, line_start, position);
    if !is_js_doc_snippet_prefix(prefix) {
        return false;
    }

    let line_end = get_line_end_of_position(file, position);
    let suffix = go_text_slice(&text, position, line_end);
    is_js_doc_snippet_suffix(suffix)
}

// Go `text[lo:hi]` on a string, with the Go runtime panic text when a bound
// is out of range. Go checks `hi` against the length first, then `lo`
// against `hi`; a negative bound is printed alone. A content-mapped file
// reaches the snippet checks with empty text in Go at B too, so the panic
// text must be Go's (the LSP error response carries it).
fn go_text_slice(text: &str, lo: i32, hi: i32) -> &str {
    let len = text.len();
    if hi < 0 {
        crate::core::go_panic(format!("runtime error: slice bounds out of range [:{hi}]"));
    }
    if hi as usize > len {
        crate::core::go_panic(format!(
            "runtime error: slice bounds out of range [:{hi}] with length {len}"
        ));
    }
    if lo < 0 {
        crate::core::go_panic(format!("runtime error: slice bounds out of range [{lo}:]"));
    }
    if lo > hi {
        crate::core::go_panic(format!(
            "runtime error: slice bounds out of range [{lo}:{hi}]"
        ));
    }
    &text[lo as usize..hi as usize]
}

// Go: ls/jsdoc_snippet.go:118 getDocCommentTemplateAtPosition
// PORT: Go reads the reparse like any parsed file, with lazy JSDoc. Here a
// lazy JSDoc read of a published file asks the current program for the
// parser input, and the language service program has none for a file that
// is in no program ("not a Go frontend program file"). So the reparse is
// read before it is published: its node and JSDoc reads use its store (as
// for a parse cache file or in the astnav tests). It is published after the
// reads, so no unpublished store stays on this thread. `cwd` is the current
// directory of the language service program, which the publish needs.
fn get_doc_comment_template_at_position(
    source_file: Node,
    position: i32,
    generate_return_in_doc_template: bool,
    new_line: &str,
    cwd: &str,
) -> Option<DocCommentTemplate> {
    let mut token_at_pos = astnav::get_token_at_position(source_file, position);
    if token_at_pos.is_nil() {
        return None;
    }

    let existing_doc_comment = find_ancestor(token_at_pos, is_js_doc);
    let (doc_comment_end, has_doc_comment_at_position, has_closing_doc_comment_at_position) =
        get_doc_comment_end_at_position(source_file, position);
    let is_in_empty_doc_comment = existing_doc_comment.is_some() || has_doc_comment_at_position;
    if is_non_empty_js_doc(existing_doc_comment)
        && has_doc_comment_at_position
        && !has_closing_doc_comment_at_position
    {
        let text = source_file_text(source_file);
        // The reparse is published for good (and its lazy JSDoc is cached
        // before that), so its nodes belong to the thread.
        let _base = crate::ast::enter_base_synthetic_owner();
        // PORT: the reparse is published static (never freed), so its text is
        // leaked with its store.
        let reparse_text: &'static str = Box::leak(
            format!(
                "{} */{}",
                &text[..position as usize],
                &text[position as usize..]
            )
            .into_boxed_str(),
        );
        // PORT: a port-only lookup (Go reads the file itself), so a miss is
        // a port panic, not a Go nil read.
        let parsed = ls_program::parsed_source_file(source_file)
            .expect("invalid memory address or nil pointer dereference");
        let reparse = Rc::new(crate::frontend::parser::parse_source_file(
            parsed.parse_options(),
            reparse_text,
            parsed.script_kind,
        ));
        crate::program::note_parsed_source_file(&reparse);
        let template = get_doc_comment_template_at_position(
            reparse.root,
            position,
            generate_return_in_doc_template,
            new_line,
            cwd,
        );
        crate::program::publish_parsed_files(cwd);
        return template;
    }
    if is_non_empty_js_doc(existing_doc_comment) {
        return None;
    }
    if existing_doc_comment.is_nil() && has_doc_comment_at_position {
        token_at_pos = astnav::get_token_at_position(
            source_file,
            skip_whitespace(&source_file_text(source_file), doc_comment_end),
        );
        if token_at_pos.is_nil() {
            return None;
        }
    }
    let token_start =
        astnav::get_start_of_node(token_at_pos, source_file, false /*includeJSDoc*/);
    if !is_in_empty_doc_comment && token_start < position {
        return None;
    }

    let comment_owner_info = get_comment_owner_info(token_at_pos, generate_return_in_doc_template)?;

    let comment_owner = comment_owner_info.comment_owner;
    let last_js_doc = comment_owner
        .js_doc(source_file)
        .last()
        .unwrap_or(Node::NIL);
    let comment_owner_start =
        astnav::get_start_of_node(comment_owner, source_file, false /*includeJSDoc*/);
    if comment_owner_start < position
        || last_js_doc.is_some()
            && existing_doc_comment.is_some()
            && last_js_doc != existing_doc_comment
    {
        return None;
    }

    let indentation = &*get_indentation_string_at_position(source_file, position);
    let mut tags = parameter_doc_comments(
        &comment_owner_info.parameters,
        is_template_source_file_js(source_file),
        indentation,
        new_line,
    );
    if comment_owner_info.has_return {
        tags += &returns_doc_comment(indentation, new_line);
    }

    if !tags.is_empty() && !has_js_doc_tags(comment_owner, source_file) {
        let preamble = format!("/**{new_line}{indentation} * ");
        let mut end_line = String::new();
        if token_start == position {
            end_line = format!("{new_line}{indentation}");
        }
        return Some(DocCommentTemplate {
            new_text: format!("{preamble}{new_line}{tags}{indentation} */{end_line}"),
        });
    }
    Some(DocCommentTemplate {
        new_text: "/** */".to_string(),
    })
}

// Go: ast.IsSourceFileJS(sourceFile) in getDocCommentTemplateAtPosition
// PORT: the reparse is read before it is published (see
// `get_doc_comment_template_at_position`), and a file that is not published
// has no `SourceFileInfo`. Its recorded parse has the script kind.
fn is_template_source_file_js(source_file: Node) -> bool {
    if !is_file_store_before_program(source_file.file_index()) {
        return is_source_file_js(source_file);
    }
    // PORT: a port-only lookup (Go reads `sourceFile.ScriptKind`), so a miss
    // is a port panic, not a Go nil read.
    let script_kind = ls_program::parsed_source_file(source_file)
        .expect("invalid memory address or nil pointer dereference")
        .script_kind;
    script_kind == ScriptKind::JS || script_kind == ScriptKind::JSX
}

// Go: ls/jsdoc_snippet.go:177 getDocCommentEndAtPosition
fn get_doc_comment_end_at_position(file: Node, position: i32) -> (i32, bool, bool) {
    let text = source_file_text(file);
    let line_start = crate::format::get_line_start_position_for_position(position, file);
    let line_end = get_line_end_of_position(file, position);
    let prefix = go_text_slice(&text, line_start, position);
    let suffix = go_text_slice(&text, position, line_end);
    if !trim_right_single_line_whitespace(prefix).ends_with("/**") {
        return (0, false, false);
    }
    // PORT: Go `getJSDocSnippetSuffixEnd` gives `(0, false)` for no closing.
    let suffix_end = get_js_doc_snippet_suffix_end(suffix);
    (
        position + suffix_end.unwrap_or(0) as i32,
        true,
        suffix_end.is_some(),
    )
}

// Go: ls/jsdoc_snippet.go:190 skipWhitespace
fn skip_whitespace(text: &str, mut position: i32) -> i32 {
    while (position as usize) < text.len() {
        let (ch, size) = decode_js_string_rune(&text[position as usize..]);
        if size == 0 {
            break;
        }
        if !char::from_u32(ch).is_some_and(is_white_space_like) {
            break;
        }
        position += size;
    }
    position
}

// Go: ls/jsdoc_snippet.go:204 getCommentOwnerInfo
fn get_comment_owner_info(
    token_at_pos: Node,
    generate_return_in_doc_template: bool,
) -> Option<CommentOwnerInfo> {
    let mut node = token_at_pos;
    while node.is_some() {
        let (info, quit) = get_comment_owner_info_worker(node, generate_return_in_doc_template);
        if info.is_some() || quit {
            return info;
        }
        node = node.parent();
    }
    None
}

// Go: ls/jsdoc_snippet.go:214 getCommentOwnerInfoWorker
fn get_comment_owner_info_worker(
    comment_owner: Node,
    generate_return_in_doc_template: bool,
) -> (Option<CommentOwnerInfo>, bool) {
    if comment_owner.is_nil() {
        return (None, false);
    }
    let owner_only = || CommentOwnerInfo {
        comment_owner,
        parameters: Vec::new(),
        has_return: false,
    };
    let with_signature = |host: Node| CommentOwnerInfo {
        comment_owner,
        parameters: host.parameters().to_vec(),
        has_return: has_return(host, generate_return_in_doc_template),
    };
    match comment_owner.kind() {
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::Constructor
        | SyntaxKind::MethodSignature
        | SyntaxKind::ArrowFunction => (Some(with_signature(comment_owner)), false),
        SyntaxKind::PropertyAssignment => get_comment_owner_info_worker(
            comment_owner.initializer(),
            generate_return_in_doc_template,
        ),
        SyntaxKind::ClassDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::EnumMember
        | SyntaxKind::TypeAliasDeclaration => (Some(owner_only()), false),
        SyntaxKind::PropertySignature => {
            let type_node = comment_owner.type_();
            if type_node.is_some() && is_function_type_node(type_node) {
                return (Some(with_signature(type_node)), false);
            }
            (Some(owner_only()), false)
        }
        SyntaxKind::VariableStatement => {
            let declarations = comment_owner.declaration_list().declarations().nodes();
            if declarations.len() == 1 {
                let initializer = declarations.get(0).initializer();
                if initializer.is_some() {
                    let host = get_right_hand_side_of_assignment(initializer);
                    if host.is_some() {
                        return (Some(with_signature(host)), false);
                    }
                }
            }
            (Some(owner_only()), false)
        }
        SyntaxKind::SourceFile => (None, true),
        SyntaxKind::ModuleDeclaration => {
            if comment_owner.parent().kind() == SyntaxKind::ModuleDeclaration {
                return (None, false);
            }
            (Some(owner_only()), false)
        }
        SyntaxKind::ExpressionStatement => get_comment_owner_info_worker(
            comment_owner.expression(),
            generate_return_in_doc_template,
        ),
        SyntaxKind::BinaryExpression => {
            if get_assignment_declaration_kind(comment_owner) == JSDeclarationKind::NONE {
                return (None, true);
            }
            let right = comment_owner.right();
            if is_function_like(right) {
                return (Some(with_signature(right)), false);
            }
            (Some(owner_only()), false)
        }
        SyntaxKind::PropertyDeclaration => {
            let initializer = comment_owner.initializer();
            if initializer.is_some() && is_function_expression_or_arrow_function(initializer) {
                return (Some(with_signature(initializer)), false);
            }
            (None, false)
        }
        _ => (None, false),
    }
}

// Go: ls/jsdoc_snippet.go:268 hasReturn
fn has_return(node: Node, generate_return_in_doc_template: bool) -> bool {
    if !generate_return_in_doc_template {
        return false;
    }
    if is_function_type_node(node) {
        return true;
    }
    if is_arrow_function(node) {
        let body = node.body();
        if body.is_some() && is_expression(body) {
            return true;
        }
    }
    is_function_like_declaration(node)
        && node.body().is_some()
        && is_block(node.body())
        && for_each_return_statement(node.body(), |_| true)
}

// Go: ls/jsdoc_snippet.go:285 getRightHandSideOfAssignment
fn get_right_hand_side_of_assignment(right_hand_side: Node) -> Node {
    if right_hand_side.is_nil() {
        return Node::NIL;
    }
    let mut right_hand_side = right_hand_side;
    while right_hand_side.kind() == SyntaxKind::ParenthesizedExpression {
        right_hand_side = right_hand_side.expression();
    }
    match right_hand_side.kind() {
        SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction => right_hand_side,
        SyntaxKind::ClassExpression => right_hand_side
            .members()
            .iter()
            .find(|&m| is_constructor_declaration(m))
            .unwrap_or(Node::NIL),
        _ => Node::NIL,
    }
}

// Go: ls/jsdoc_snippet.go:301 parameterDocComments
fn parameter_doc_comments(
    parameters: &[Node],
    is_java_script_file: bool,
    indentation: &str,
    new_line: &str,
) -> String {
    let mut b = String::new();
    for (i, &parameter) in parameters.iter().enumerate() {
        let mut param_name = format!("param{i}");
        if is_identifier(parameter.name()) {
            param_name = parameter.name().text().to_string();
        }
        let mut param_type = "";
        if is_java_script_file {
            if parameter.dot_dot_dot_token().is_some() {
                param_type = "{...any} ";
            } else {
                param_type = "{any} ";
            }
        }
        b.push_str(indentation);
        b.push_str(" * @param ");
        b.push_str(param_type);
        b.push_str(&param_name);
        b.push_str(new_line);
    }
    b
}

// Go: ls/jsdoc_snippet.go:325 returnsDocComment
fn returns_doc_comment(indentation: &str, new_line: &str) -> String {
    format!("{indentation} * @returns{new_line}")
}

// Go: ls/jsdoc_snippet.go:329 getIndentationStringAtPosition
fn get_indentation_string_at_position(source_file: Node, position: i32) -> String {
    let text = source_file_text(source_file);
    let line_start = crate::format::get_line_start_position_for_position(position, source_file);
    let mut pos = line_start;
    while pos < position {
        let (ch, size) = decode_js_string_rune(&text[pos as usize..]);
        if size == 0 {
            break;
        }
        if !char::from_u32(ch).is_some_and(is_white_space_single_line) {
            break;
        }
        pos += size;
    }
    text[line_start as usize..pos as usize].to_string()
}

// Go: ls/jsdoc_snippet.go:346 isNonEmptyJSDoc
fn is_non_empty_js_doc(jsdoc: Node) -> bool {
    if jsdoc.is_nil() {
        return false;
    }
    let comment = jsdoc.comment_list();
    let tags = jsdoc.tags();
    comment.is_some() && !comment.nodes().is_empty() || tags.is_some() && !tags.nodes().is_empty()
}

// Go: ls/jsdoc_snippet.go:354 hasJSDocTags
fn has_js_doc_tags(node: Node, file: Node) -> bool {
    let jsdocs = node.js_doc(file);
    if jsdocs.is_empty() {
        return false;
    }
    let tags = jsdocs.get(jsdocs.len() - 1).tags();
    tags.is_some() && !tags.nodes().is_empty()
}

// Go: ls/jsdoc_snippet.go:363 templateToSnippet
fn template_to_snippet(template: &str, new_line: &str) -> String {
    if template == "/** */" {
        return format!("/**{new_line} * $0{new_line} */");
    }

    let mut snippet_index = 1;
    let template = escape_snippet_text(template);
    let template = strip_js_doc_template_indentation(&template, new_line);
    transform_js_doc_template_lines(&template, new_line, &mut snippet_index)
}

// Go: ls/jsdoc_snippet.go:374 stripJSDocTemplateIndentation
fn strip_js_doc_template_indentation(template: &str, new_line: &str) -> String {
    let mut lines: Vec<String> = template.split(new_line).map(str::to_string).collect();
    for line in &mut lines {
        let trimmed = line.trim_start_matches([' ', '\t']).to_string();
        if trimmed.starts_with('/') {
            *line = trimmed;
        } else if trimmed.starts_with('*') {
            *line = format!(" {trimmed}");
        }
    }
    lines.join(new_line)
}

// Go: ls/jsdoc_snippet.go:387 transformJSDocTemplateLines
fn transform_js_doc_template_lines(
    template: &str,
    new_line: &str,
    snippet_index: &mut i32,
) -> String {
    let mut lines: Vec<String> = template.split(new_line).map(str::to_string).collect();
    for i in 0..lines.len() {
        if i > 0 && lines[i - 1].starts_with("/**") && line_has_only_js_doc_asterisk(&lines[i]) {
            lines[i].push_str("$0");
            continue;
        }
        if let Some(transformed) = transform_js_doc_param_line(&lines[i], snippet_index) {
            lines[i] = transformed;
            continue;
        }
        if let Some(transformed) = transform_js_doc_returns_line(&lines[i], snippet_index) {
            lines[i] = transformed;
        }
    }
    lines.join(new_line)
}

// Go: ls/jsdoc_snippet.go:405 lineHasOnlyJSDocAsterisk
fn line_has_only_js_doc_asterisk(line: &str) -> bool {
    let line = line.trim_start_matches([' ', '\t']);
    line.starts_with('*') && is_only_spaces_or_tabs(&line[1..])
}

// Go: ls/jsdoc_snippet.go:410 transformJSDocParamLine
fn transform_js_doc_param_line(line: &str, snippet_index: &mut i32) -> Option<String> {
    let mut prefix = "";
    let mut rest = line;
    if rest.starts_with(' ') {
        prefix = " ";
        rest = &rest[1..];
    }
    if !rest.starts_with("* @param") {
        return None;
    }
    rest = &rest["* @param".len()..];
    if !starts_with_single_line_whitespace(rest) {
        return None;
    }
    rest = rest.trim_start_matches([' ', '\t']);

    let mut type_text = String::new();
    if rest.starts_with('{') {
        let close_brace = rest.find('}')?;
        type_text = format!(" {}", &rest[..close_brace + 1]);
        rest = &rest[close_brace + 1..];
        if !starts_with_single_line_whitespace(rest) {
            return None;
        }
        rest = rest.trim_start_matches([' ', '\t']);
    }

    let (param_name, rest, ok) = scan_non_whitespace(rest);
    if !ok || !is_only_spaces_or_tabs(rest) {
        return None;
    }

    let mut out = format!("{prefix}* @param ");
    if type_text == " {any}" || type_text == " {*}" {
        out += &format!("{{${{{}:*}}}} ", *snippet_index);
        *snippet_index += 1;
    } else if !type_text.is_empty() {
        out += &type_text;
        out.push(' ');
    }
    out += &format!("{param_name} ${{{}}}", *snippet_index);
    *snippet_index += 1;
    Some(out)
}

// Go: ls/jsdoc_snippet.go:454 transformJSDocReturnsLine
fn transform_js_doc_returns_line(line: &str, snippet_index: &mut i32) -> Option<String> {
    let mut prefix = "";
    let mut rest = line;
    if rest.starts_with(' ') {
        prefix = " ";
        rest = &rest[1..];
    }
    if !rest.starts_with("* @returns") || !is_only_spaces_or_tabs(&rest["* @returns".len()..]) {
        return None;
    }
    let text = format!("{prefix}* @returns ${{{}}}", *snippet_index);
    *snippet_index += 1;
    Some(text)
}

// Go: ls/jsdoc_snippet.go:469 scanNonWhitespace
fn scan_non_whitespace(text: &str) -> (&str, &str, bool) {
    if text.is_empty() {
        return ("", "", false);
    }
    let mut i = 0usize;
    while i < text.len() {
        let (ch, size) = decode_js_string_rune(&text[i..]);
        if size == 0 || char::from_u32(ch).is_some_and(is_white_space_like) {
            if i == 0 {
                return ("", "", false);
            }
            return (&text[..i], &text[i..], true);
        }
        i += size as usize;
    }
    (text, "", true)
}

// Go: ls/jsdoc_snippet.go:485 isJSDocSnippetPrefix
fn is_js_doc_snippet_prefix(prefix: &str) -> bool {
    let trimmed = trim_right_single_line_whitespace(prefix);
    if trimmed.ends_with("/**") {
        return true;
    }
    let start = skip_single_line_whitespace(prefix, 0);
    let bytes = trimmed.as_bytes();
    if start >= bytes.len() || bytes[start] != b'/' {
        return false;
    }
    if start + 3 > bytes.len() {
        return false;
    }
    for &b in &bytes[start + 1..] {
        if b != b'*' {
            return false;
        }
    }
    bytes.len() - start >= 3
}

// Go: ls/jsdoc_snippet.go:504 getJSDocSnippetPrefixStart
// PORT: Go returns `(int, bool)`; `None` is `false`.
fn get_js_doc_snippet_prefix_start(prefix: &str) -> Option<usize> {
    let trimmed = trim_right_single_line_whitespace(prefix).as_bytes();
    let mut i = trimmed.len();
    while i > 0 && trimmed[i - 1] == b'*' {
        // PORT: Go loops `i` down from `len-1`; this `i` is Go `i + 1`.
        if i - 1 > 0 && trimmed[i - 2] == b'/' {
            return Some(i - 2);
        }
        i -= 1;
    }
    if trimmed.ends_with(b"/") {
        return Some(trimmed.len() - 1);
    }
    None
}

// Go: ls/jsdoc_snippet.go:517 isJSDocSnippetSuffix
fn is_js_doc_snippet_suffix(suffix: &str) -> bool {
    let trimmed =
        trim_right_single_line_whitespace(&suffix[skip_single_line_whitespace(suffix, 0)..]);
    if trimmed.is_empty() {
        return true;
    }
    if !trimmed.ends_with('/') {
        return false;
    }
    trimmed.as_bytes()[..trimmed.len() - 1]
        .iter()
        .all(|&b| b == b'*')
}

// Go: ls/jsdoc_snippet.go:533 getJSDocSnippetSuffixEnd
// PORT: Go returns `(int, bool)`; `None` is `(0, false)`.
fn get_js_doc_snippet_suffix_end(suffix: &str) -> Option<usize> {
    let bytes = suffix.as_bytes();
    let mut pos = skip_single_line_whitespace(suffix, 0);
    while pos < bytes.len() && bytes[pos] == b'*' {
        pos += 1;
    }
    if pos < bytes.len() && bytes[pos] == b'/' {
        return Some(pos + 1);
    }
    None
}

// Go: ls/jsdoc_snippet.go:545 trimRightSingleLineWhitespace
fn trim_right_single_line_whitespace(text: &str) -> &str {
    let mut end = 0usize;
    let mut pos = 0usize;
    while pos < text.len() {
        let (ch, size) = decode_js_string_rune(&text[pos..]);
        if size == 0 {
            break;
        }
        pos += size as usize;
        if !char::from_u32(ch).is_some_and(is_white_space_single_line) {
            end = pos;
        }
    }
    &text[..end]
}

// Go: ls/jsdoc_snippet.go:560 skipSingleLineWhitespace
fn skip_single_line_whitespace(text: &str, mut pos: usize) -> usize {
    while pos < text.len() {
        let (ch, size) = decode_js_string_rune(&text[pos..]);
        if size == 0 || !char::from_u32(ch).is_some_and(is_white_space_single_line) {
            break;
        }
        pos += size as usize;
    }
    pos
}

// Go: ls/jsdoc_snippet.go:571 isOnlySingleLineWhitespace
fn is_only_single_line_whitespace(text: &str) -> bool {
    skip_single_line_whitespace(text, 0) == text.len()
}

// Go: ls/jsdoc_snippet.go:575 startsWithSingleLineWhitespace
fn starts_with_single_line_whitespace(text: &str) -> bool {
    if text.is_empty() {
        return false;
    }
    let (ch, size) = decode_js_string_rune(text);
    size != 0 && char::from_u32(ch).is_some_and(is_white_space_single_line)
}

// Go: ls/jsdoc_snippet.go:583 isOnlySpacesOrTabs
fn is_only_spaces_or_tabs(text: &str) -> bool {
    text.bytes().all(|b| b == b' ' || b == b'\t')
}
