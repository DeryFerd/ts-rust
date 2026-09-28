use crate::format::prelude::*;

use crate::flags_macros::go_enum;
use crate::frontend::scanner::scanner_p1::{rune_to_char, utf8_decode_rune_in_string};
use crate::frontend::scanner::{get_leading_comment_ranges, get_trailing_comment_ranges};

// Go: format/indent.go:17 GetIndentationForNode
pub fn get_indentation_for_node(
    n: Node,
    ignore_actual_indentation_range: Option<&TextRange>,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    let (startline, startpos) = get_ecma_line_and_byte_offset_of_position(
        source_file,
        get_token_pos_of_node(n, source_file, false),
    );
    get_indentation_for_node_worker(
        n,
        startline,
        startpos,
        ignore_actual_indentation_range,
        0, /*indentationDelta*/
        source_file,
        false, /*isNextChild*/
        options,
    )
}

// Go: format/indent.go:24 GetIndentation
// GetIndentation computes the expected indentation for a position in a source file.
// This is the Go port of SmartIndenter.getIndentation from TypeScript.
pub fn get_indentation(
    position: i32,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
    assume_new_line_before_close_brace: bool,
) -> i32 {
    if position > source_file_text(source_file).len() as i32 {
        return options.editor_settings.base_indent_size; // past EOF
    }

    // no indentation when the indent style is set to none,
    // so we can return fast
    if options.editor_settings.indent_style == lsutil::IndentStyle::NONE {
        return 0;
    }

    let preceding_token = astnav::find_preceding_token_ex(
        source_file,
        position,
        Node::NIL, /*startNode*/
        true,      /*excludeJSDoc*/
    );

    let enclosing_comment_range =
        get_range_of_enclosing_comment(source_file, position, preceding_token);
    if let Some(enclosing_comment_range) = &enclosing_comment_range
        && enclosing_comment_range.kind == SyntaxKind::MultiLineCommentTrivia
    {
        return get_comment_indent(source_file, position, options, enclosing_comment_range);
    }

    if preceding_token.is_nil() {
        return options.editor_settings.base_indent_size;
    }

    // no indentation in string/regex/template literals
    if is_string_or_regular_expression_or_template_literal(preceding_token.kind()) {
        let token_start = get_token_pos_of_node(preceding_token, source_file, false);
        if token_start <= position && position < preceding_token.end() {
            return 0;
        }
    }

    let line_at_position = get_ecma_line_of_position(source_file, position);

    // indentation is first non-whitespace character in a previous line
    // for block indentation, we should look for a line which contains something that's not
    // whitespace.
    let current_token = astnav::get_token_at_position(source_file, position);
    // For object literals, we want indentation to work just like with blocks.
    // If the `{` starts in any position (even in the middle of a line), then
    // the following indentation should treat `{` as the start of that line (including leading whitespace).
    // ```
    //     const a: { x: undefined, y: undefined } = {}       // leading 4 whitespaces and { starts in the middle of line
    // ->
    //     const a: { x: undefined, y: undefined } = {
    //         x: undefined,
    //         y: undefined,
    //     }
    // ---------------------
    //     const a: {x : undefined, y: undefined } =
    //      {}
    // ->
    //     const a: { x: undefined, y: undefined } =
    //      {                                                  // leading 5 whitespaces and { starts at 6 column
    //          x: undefined,
    //          y: undefined,
    //      }
    // ```
    let is_object_literal = current_token.kind() == SyntaxKind::OpenBraceToken
        && current_token.parent().is_some()
        && current_token.parent().kind() == SyntaxKind::ObjectLiteralExpression;
    if options.editor_settings.indent_style == lsutil::IndentStyle::BLOCK || is_object_literal {
        return get_block_indent(source_file, position, options);
    }

    if preceding_token.kind() == SyntaxKind::CommaToken
        && preceding_token.parent().is_some()
        && preceding_token.parent().kind() != SyntaxKind::BinaryExpression
    {
        // previous token is comma that separates items in list - find the previous item and try to derive indentation from it
        let actual_indentation = get_actual_indentation_for_list_item_before_comma(
            preceding_token,
            source_file,
            options,
        );
        if actual_indentation != -1 {
            return actual_indentation;
        }
    }

    let container_list = get_list_by_position(position, preceding_token.parent(), source_file);
    // use list position if the preceding token is before any list items
    if container_list.is_some() && !preceding_token.loc().contained_by(container_list.loc()) {
        let use_the_same_base_indentation = current_token.parent().is_some()
            && (current_token.parent().kind() == SyntaxKind::FunctionExpression
                || current_token.parent().kind() == SyntaxKind::ArrowFunction);
        let mut indent_size = 0;
        if !use_the_same_base_indentation {
            indent_size = options.editor_settings.indent_size;
        }
        let res = get_actual_indentation_for_list_start_line(container_list, source_file, options);
        if res == -1 {
            return indent_size;
        }
        return res + indent_size;
    }

    get_smart_indent(
        source_file,
        position,
        preceding_token,
        line_at_position,
        assume_new_line_before_close_brace,
        options,
    )
}

// Go: format/indent.go:111 getCommentIndent
pub fn get_comment_indent(
    source_file: Node,
    position: i32,
    options: &lsutil::FormatCodeSettings,
    enclosing_comment_range: &CommentRange,
) -> i32 {
    let previous_line = get_ecma_line_of_position(source_file, position) - 1;
    let comment_start_line = get_ecma_line_of_position(source_file, enclosing_comment_range.pos());

    crate::go_assert!(comment_start_line >= 0, "commentStartLine >= 0");

    if previous_line <= comment_start_line {
        let line_starts = get_ecma_line_starts(source_file);
        return find_first_non_whitespace_column(
            line_starts[comment_start_line as usize],
            position,
            source_file,
            options,
        );
    }

    let line_starts = get_ecma_line_starts(source_file);
    let start_position_of_line = line_starts[previous_line as usize];
    let (character, column) = find_first_non_whitespace_character_and_column(
        start_position_of_line,
        position,
        source_file,
        options,
    );

    if column == 0 {
        return column;
    }

    let first_non_whitespace_character_code =
        source_file_text(source_file).as_bytes()[(start_position_of_line + character) as usize];
    if first_non_whitespace_character_code == b'*' {
        return column - 1;
    }
    column
}

// Go: format/indent.go:137 getLeadingCommentRangesOfNode
// PORT: Go returns an `iter.Seq` (nil for JSX text); this returns a Vec
// (empty for JSX text).
pub fn get_leading_comment_ranges_of_node(node: Node, file: Node) -> Vec<CommentRange> {
    if node.kind() == SyntaxKind::JsxText {
        return Vec::new();
    }
    get_leading_comment_ranges(&NodeFactory::default(), source_file_text(file), node.pos())
}

// Go: format/indent.go:144 getRangeOfEnclosingComment
pub fn get_range_of_enclosing_comment(
    source_file: Node,
    position: i32,
    preceding_token: Node,
) -> Option<CommentRange> {
    let mut token_at_position = astnav::get_token_at_position(source_file, position);
    let jsdoc = find_ancestor(token_at_position, is_js_doc);
    if jsdoc.is_some() {
        token_at_position = jsdoc.parent();
    }
    let token_start =
        astnav::get_start_of_node(token_at_position, source_file, false /*includeJSDoc*/);
    if token_start <= position && position < token_at_position.end() {
        return None;
    }

    // Between two consecutive tokens, all comments are either trailing on the former
    // or leading on the latter (and none are in both lists).
    let mut trailing_ranges_of_previous_token: Vec<CommentRange> = Vec::new();
    if preceding_token.is_some() {
        trailing_ranges_of_previous_token = get_trailing_comment_ranges(
            &NodeFactory::default(),
            source_file_text(source_file),
            preceding_token.end(),
        );
    }
    let leading_ranges_of_next_token =
        get_leading_comment_ranges_of_node(token_at_position, source_file);
    let comment_ranges = trailing_ranges_of_previous_token
        .into_iter()
        .chain(leading_ranges_of_next_token);
    for comment_range in comment_ranges {
        if comment_range.text_range.contains_exclusive(position)
            || position == comment_range.end()
                && (comment_range.kind == SyntaxKind::SingleLineCommentTrivia
                    || position == source_file_text(source_file).len() as i32)
        {
            return Some(comment_range);
        }
    }
    None
}

// Go: format/indent.go:177 getBlockIndent
pub fn get_block_indent(
    source_file: Node,
    position: i32,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    // move backwards until we find a line with a non-whitespace character,
    // then find the first non-whitespace character for that line.
    let mut current = position;
    let text = source_file_text(source_file);
    while current > 0 {
        let (ch, size) = utf8_decode_rune_in_string(text, current as usize);
        if !is_white_space_like(rune_to_char(ch)) {
            break;
        }
        current -= size;
    }

    let line_start = get_line_start_position_for_position(current, source_file);
    find_first_non_whitespace_column(line_start, current, source_file, options)
}

// Go: format/indent.go:193 getActualIndentationForListItemBeforeComma
pub fn get_actual_indentation_for_list_item_before_comma(
    comma_token: Node,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    // previous token is comma that separates items in list - find the previous item and try to derive indentation from it
    if comma_token.parent().is_nil() {
        return -1;
    }
    let containing_list = get_containing_list(comma_token, source_file);
    if containing_list.is_nil() {
        return -1;
    }
    let comma_index = containing_list
        .nodes()
        .iter()
        .position(|n| n == comma_token)
        .map_or(-1, |i| i as i32);
    if comma_index > 0 {
        return derive_actual_indentation_from_list(
            containing_list,
            comma_index - 1,
            source_file,
            options,
        );
    }
    -1
}

// Go: format/indent.go:209 nextTokenKind
go_enum!(NextTokenKind, i32 {
    UNKNOWN = 0; // nextTokenKindUnknown
    OPEN_BRACE = 1; // nextTokenKindOpenBrace
    CLOSE_BRACE = 2; // nextTokenKindCloseBrace
});

// Go: format/indent.go:217 nextTokenIsCurlyBraceOnSameLineAsCursor
pub fn next_token_is_curly_brace_on_same_line_as_cursor(
    preceding_token: Node,
    current: Node,
    line_at_position: i32,
    source_file: Node,
) -> NextTokenKind {
    let next_token = astnav::find_next_token(preceding_token, current, source_file);
    if next_token.is_nil() {
        return NextTokenKind::UNKNOWN;
    }

    if next_token.kind() == SyntaxKind::OpenBraceToken {
        // open braces are always indented at the parent level
        return NextTokenKind::OPEN_BRACE;
    } else if next_token.kind() == SyntaxKind::CloseBraceToken {
        // close braces are indented at the parent level if they are located on the same line with cursor
        let next_token_start_line = get_start_line_for_node(next_token, source_file);
        if line_at_position == next_token_start_line {
            return NextTokenKind::CLOSE_BRACE;
        }
        return NextTokenKind::UNKNOWN;
    }

    NextTokenKind::UNKNOWN
}

// Go: format/indent.go:238 getSmartIndent
pub fn get_smart_indent(
    source_file: Node,
    position: i32,
    preceding_token: Node,
    line_at_position: i32,
    assume_new_line_before_close_brace: bool,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    // try to find node that can contribute to indentation and includes 'position' starting from 'precedingToken'
    // if such node is found - compute initial indentation for 'position' inside this node
    let mut previous = Node::NIL;
    let mut current = preceding_token;

    while current.is_some() {
        if lsutil::position_belongs_to_node(current, position, source_file)
            && should_indent_child_node(options, current, previous, source_file, &[true])
        {
            let (current_start_line, current_start_char) =
                get_start_line_and_character_for_node(current, source_file);
            let ntk = next_token_is_curly_brace_on_same_line_as_cursor(
                preceding_token,
                current,
                line_at_position,
                source_file,
            );
            let mut indentation_delta = 0;
            if ntk != NextTokenKind::UNKNOWN {
                // handle cases when codefix is about to be inserted before the close brace
                if assume_new_line_before_close_brace && ntk == NextTokenKind::CLOSE_BRACE {
                    indentation_delta = options.editor_settings.indent_size;
                }
                // else 0
            } else if line_at_position != current_start_line {
                indentation_delta = options.editor_settings.indent_size;
            }
            return get_indentation_for_node_worker(
                current,
                current_start_line,
                current_start_char,
                None,
                indentation_delta,
                source_file,
                true,
                options,
            );
        }

        // check if current node is a list item - if yes, take indentation from it
        // do not consider parent-child line sharing yet:
        // function foo(a
        //    | preceding node 'a' does share line with its parent but indentation is expected
        let actual_indentation = get_actual_indentation_for_list_item(
            current,
            source_file,
            options,
            true, /*listIndentsChild*/
        );
        if actual_indentation != -1 {
            return actual_indentation;
        }

        previous = current;
        current = current.parent();
    }
    // no parent was found - return the base indentation of the SourceFile
    options.editor_settings.base_indent_size
}

// Go: format/indent.go:279 getIndentationForNodeWorker
pub fn get_indentation_for_node_worker(
    mut current: Node,
    mut current_start_line: i32,
    mut current_start_character: i32,
    ignore_actual_indentation_range: Option<&TextRange>,
    mut indentation_delta: i32,
    source_file: Node,
    is_next_child: bool,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    let mut parent = current.parent();

    // Walk up the tree and collect indentation for parent-child node pairs. Indentation is not added if
    // * parent and child nodes start on the same line, or
    // * parent is an IfStatement and child starts on the same line as an 'else clause'.
    while parent.is_some() {
        let mut use_actual_indentation = true;
        if let Some(ignore_actual_indentation_range) = ignore_actual_indentation_range {
            let start = get_token_pos_of_node(current, source_file, false);
            use_actual_indentation = start < ignore_actual_indentation_range.pos()
                || start > ignore_actual_indentation_range.end();
        }

        let (containing_list_or_parent_start_line, containing_list_or_parent_start_character) =
            get_containing_list_or_parent_start(parent, current, source_file);
        let parent_and_child_share_line = containing_list_or_parent_start_line
            == current_start_line
            || child_starts_on_the_same_line_with_else_in_if_statement(
                parent,
                current,
                current_start_line,
                source_file,
            );

        if use_actual_indentation {
            // check if current node is a list item - if yes, take indentation from it
            let mut first_list_child = Node::NIL;
            let container_list = get_containing_list(current, source_file);
            if container_list.is_some() {
                first_list_child = container_list.nodes().first().unwrap_or(Node::NIL);
            }
            // A list indents its children if the children begin on a later line than the list itself:
            //
            // f1(               L0 - List start
            //   {               L1 - First child start: indented, along with all other children
            //     prop: 0
            //   },
            //   {
            //     prop: 1
            //   }
            // )
            //
            // f2({             L0 - List start and first child start: children are not indented.
            //   prop: 0             Object properties are indented only one level, because the list
            // }, {                  itself contributes nothing.
            //   prop: 1        L3 - The indentation of the second object literal is best understood by
            // })                    looking at the relationship between the list and *first* list item.
            let mut list_indents_child = false;
            if first_list_child.is_some() {
                let list_line = get_start_line_for_node(first_list_child, source_file);
                list_indents_child = list_line > containing_list_or_parent_start_line;
            }
            let mut actual_indentation = get_actual_indentation_for_list_item(
                current,
                source_file,
                options,
                list_indents_child,
            );
            if actual_indentation != -1 {
                return actual_indentation + indentation_delta;
            }

            // try to fetch actual indentation for current node from source text
            actual_indentation = get_actual_indentation_for_node(
                current,
                parent,
                current_start_line,
                current_start_character,
                parent_and_child_share_line,
                source_file,
                options,
            );
            if actual_indentation != -1 {
                return actual_indentation + indentation_delta;
            }
        }

        // increase indentation if parent node wants its content to be indented and parent and child nodes don't start on the same line
        if should_indent_child_node(options, parent, current, source_file, &[is_next_child])
            && !parent_and_child_share_line
        {
            indentation_delta += options.editor_settings.indent_size;
        }

        // In our AST, a call argument's `parent` is the call-expression, not the argument list.
        // We would like to increase indentation based on the relationship between an argument and its argument-list,
        // so we spoof the starting position of the (parent) call-expression to match the (non-parent) argument-list.
        // But, the spoofed start-value could then cause a problem when comparing the start position of the call-expression
        // to *its* parent (in the case of an iife, an expression statement), adding an extra level of indentation.
        //
        // Instead, when at an argument, we unspoof the starting position of the enclosing call expression
        // *after* applying indentation for the argument.

        let use_true_start = is_argument_and_start_line_overlaps_expression_being_called(
            parent,
            current,
            current_start_line,
            source_file,
        );

        current = parent;
        parent = current.parent();

        if use_true_start {
            (current_start_line, current_start_character) =
                get_ecma_line_and_byte_offset_of_position(
                    source_file,
                    get_token_pos_of_node(current, source_file, false),
                );
        } else {
            current_start_line = containing_list_or_parent_start_line;
            current_start_character = containing_list_or_parent_start_character;
        }
    }

    indentation_delta + options.editor_settings.base_indent_size
}

// Go: format/indent.go:378 getActualIndentationForNode
/*
 * Function returns -1 if actual indentation for node should not be used (i.e because node is nested expression)
 */
pub fn get_actual_indentation_for_node(
    current: Node,
    parent: Node,
    cuurent_line: i32,
    current_char: i32,
    parent_and_child_share_line: bool,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    // actual indentation is used for statements\declarations if one of cases below is true:
    // - parent is SourceFile - by default immediate children of SourceFile are not indented except when user indents them manually
    // - parent and child are not on the same line
    let use_actual_indentation = (is_declaration(current)
        || is_statement_but_not_declaration(current))
        && (parent.kind() == SyntaxKind::SourceFile || !parent_and_child_share_line);

    if !use_actual_indentation {
        return -1;
    }

    find_column_for_first_non_whitespace_character_in_line(
        cuurent_line,
        current_char,
        source_file,
        options,
    )
}

// Go: format/indent.go:391 isArgumentAndStartLineOverlapsExpressionBeingCalled
pub fn is_argument_and_start_line_overlaps_expression_being_called(
    parent: Node,
    child: Node,
    child_start_line: i32,
    source_file: Node,
) -> bool {
    if !(is_call_expression(parent) && parent.arguments().iter().any(|a| a == child)) {
        return false;
    }
    let expression_of_call_expression_end = parent.expression().end();
    let expression_of_call_expression_end_line =
        get_ecma_line_of_position(source_file, expression_of_call_expression_end);
    expression_of_call_expression_end_line == child_start_line
}

// Go: format/indent.go:400 getActualIndentationForListItem
pub fn get_actual_indentation_for_list_item(
    node: Node,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
    list_indents_child: bool,
) -> i32 {
    if node.parent().is_some() && node.parent().kind() == SyntaxKind::VariableDeclarationList {
        // VariableDeclarationList has no wrapping tokens
        return -1;
    }
    let containing_list = get_containing_list(node, source_file);
    if containing_list.is_some() {
        let index = containing_list
            .nodes()
            .iter()
            .position(|e| e == node)
            .map_or(-1, |i| i as i32);
        if index != -1 {
            let result =
                derive_actual_indentation_from_list(containing_list, index, source_file, options);
            if result != -1 {
                return result;
            }
        }
        let mut delta = 0;
        if list_indents_child {
            delta = options.editor_settings.indent_size;
        }
        let res = get_actual_indentation_for_list_start_line(containing_list, source_file, options);
        if res == -1 {
            return delta;
        }
        return res + delta;
    }
    -1
}

// Go: format/indent.go:427 getActualIndentationForListStartLine
pub fn get_actual_indentation_for_list_start_line(
    list: NodeList,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    if list.is_nil() {
        return -1;
    }
    let (line, char) = get_ecma_line_and_byte_offset_of_position(source_file, list.loc().pos());
    find_column_for_first_non_whitespace_character_in_line(line, char, source_file, options)
}

// Go: format/indent.go:435 deriveActualIndentationFromList
pub fn derive_actual_indentation_from_list(
    list: NodeList,
    index: i32,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    crate::go_assert!(list.is_some() && index >= 0 && (index as usize) < list.nodes().len());

    let nodes = list.nodes();
    let node = nodes.get(index as usize);

    // walk toward the start of the list starting from current node and check if the line is the same for all items.
    // if end line for item [i - 1] differs from the start line for item [i] - find column of the first non-whitespace character on the line of item [i]

    let (mut line, mut char) = get_start_line_and_character_for_node(node, source_file);

    let mut i = index;
    while i >= 0 {
        let item = nodes.get(i as usize);
        if item.kind() == SyntaxKind::CommaToken {
            i -= 1;
            continue;
        }
        // skip list items that ends on the same line with the current list element
        let prev_end_line = get_ecma_line_of_position(source_file, item.end());
        if prev_end_line != line {
            return find_column_for_first_non_whitespace_character_in_line(
                line,
                char,
                source_file,
                options,
            );
        }

        (line, char) = get_start_line_and_character_for_node(item, source_file);
        i -= 1;
    }
    -1
}

// Go: format/indent.go:460 findColumnForFirstNonWhitespaceCharacterInLine
pub fn find_column_for_first_non_whitespace_character_in_line(
    line: i32,
    char: i32,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    let line_start = scanner_ls::get_ecma_position_of_line_and_byte_offset(source_file, line, 0);
    find_first_non_whitespace_column(line_start, line_start + char, source_file, options)
}

// Go: format/indent.go:465 FindFirstNonWhitespaceColumn
pub fn find_first_non_whitespace_column(
    start_pos: i32,
    end_pos: i32,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> i32 {
    let (_, col) =
        find_first_non_whitespace_character_and_column(start_pos, end_pos, source_file, options);
    col
}

// Go: format/indent.go:477 findFirstNonWhitespaceCharacterAndColumn
/**
 * Character is the actual index of the character since the beginning of the line.
 * Column - position of the character after expanding tabs to spaces.
 * "0\t2$"
 * value of 'character' for '$' is 3
 * value of 'column' for '$' is 6 (assuming that tab size is 4)
 */
pub fn find_first_non_whitespace_character_and_column(
    start_pos: i32,
    end_pos: i32,
    source_file: Node,
    options: &lsutil::FormatCodeSettings,
) -> (i32, i32) {
    let mut column = 0;
    let text = source_file_text(source_file);
    let mut pos = start_pos;
    while pos < end_pos {
        let (ch, size) = utf8_decode_rune_in_string(text, pos as usize);
        if !is_white_space_single_line(rune_to_char(ch)) {
            break;
        }

        if ch == '\t' as i32 {
            if options.editor_settings.tab_size > 0 {
                column +=
                    options.editor_settings.tab_size + (column % options.editor_settings.tab_size);
            }
        } else {
            column += 1;
        }

        pos += size;
    }
    (pos - start_pos, column)
}

// Go: format/indent.go:500 childStartsOnTheSameLineWithElseInIfStatement
pub fn child_starts_on_the_same_line_with_else_in_if_statement(
    parent: Node,
    child: Node,
    child_start_line: i32,
    source_file: Node,
) -> bool {
    if parent.kind() == SyntaxKind::IfStatement && parent.else_statement() == child {
        let else_keyword = astnav::find_preceding_token(source_file, child.pos());
        crate::go_assert!(else_keyword.is_some());
        let else_keyword_start_line = get_start_line_for_node(else_keyword, source_file);
        return else_keyword_start_line == child_start_line;
    }
    false
}

// Go: format/indent.go:510 getStartLineAndCharacterForNode
pub fn get_start_line_and_character_for_node(n: Node, source_file: Node) -> (i32, i32) {
    get_ecma_line_and_byte_offset_of_position(
        source_file,
        get_token_pos_of_node(n, source_file, false),
    )
}

// Go: format/indent.go:514 getStartLineForNode
pub fn get_start_line_for_node(n: Node, source_file: Node) -> i32 {
    get_ecma_line_of_position(source_file, get_token_pos_of_node(n, source_file, false))
}

// Go: format/indent.go:518 GetContainingList
pub fn get_containing_list(node: Node, source_file: Node) -> NodeList {
    if node.parent().is_nil() {
        return NodeList::NIL;
    }
    get_list_by_range(
        get_token_pos_of_node(node, source_file, false),
        node.end(),
        node.parent(),
        source_file,
    )
}

// Go: format/indent.go:525 getListByPosition
pub fn get_list_by_position(pos: i32, node: Node, source_file: Node) -> NodeList {
    if node.is_nil() {
        return NodeList::NIL;
    }
    get_list_by_range(pos, pos, node, source_file)
}

// Go: format/indent.go:532 getListByRange
pub fn get_list_by_range(start: i32, end: i32, node: Node, source_file: Node) -> NodeList {
    let r = TextRange::new(start, end);
    match node.kind() {
        SyntaxKind::TypeReference => {
            return get_list(node.type_argument_list(), r, node, source_file);
        }
        SyntaxKind::ObjectLiteralExpression => {
            return get_list(node.property_list(), r, node, source_file);
        }
        SyntaxKind::ArrayLiteralExpression => {
            return get_list(node.element_list(), r, node, source_file);
        }
        SyntaxKind::TypeLiteral => {
            return get_list(node.member_list(), r, node, source_file);
        }
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::MethodSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::Constructor
        | SyntaxKind::ConstructorType
        | SyntaxKind::ConstructSignature => {
            let tpl = get_list(node.type_parameter_list(), r, node, source_file);
            if tpl.is_some() {
                return tpl;
            }
            return get_list(node.parameter_list(), r, node, source_file);
        }
        SyntaxKind::GetAccessor => {
            return get_list(node.parameter_list(), r, node, source_file);
        }
        SyntaxKind::ClassDeclaration
        | SyntaxKind::ClassExpression
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::TypeAliasDeclaration
        | SyntaxKind::JsDocTemplateTag => {
            return get_list(node.type_parameter_list(), r, node, source_file);
        }
        SyntaxKind::NewExpression | SyntaxKind::CallExpression => {
            let l = get_list(node.type_argument_list(), r, node, source_file);
            if l.is_some() {
                return l;
            }
            return get_list(node.argument_list(), r, node, source_file);
        }
        SyntaxKind::VariableDeclarationList => {
            return get_list(node.declarations(), r, node, source_file);
        }
        SyntaxKind::ObjectBindingPattern
        | SyntaxKind::ArrayBindingPattern
        | SyntaxKind::NamedImports
        | SyntaxKind::NamedExports => {
            return get_list(node.element_list(), r, node, source_file);
        }
        _ => {}
    }
    NodeList::NIL // TODO: should this be a panic? It isn't in strada.
}

// Go: format/indent.go:579 getList
pub fn get_list(list: NodeList, r: TextRange, node: Node, source_file: Node) -> NodeList {
    if list.is_nil() {
        return NodeList::NIL;
    }
    if r.contained_by(get_visual_list_range(node, list.loc(), source_file)) {
        return list;
    }
    NodeList::NIL
}

// Go: format/indent.go:589 getVisualListRange
pub fn get_visual_list_range(node: Node, list: TextRange, source_file: Node) -> TextRange {
    // In strada, this relied on the services .getChildren method, which manifested synthetic token nodes
    // _however_, the logic boils down to "find the child with the matching span and adjust its start to the
    // previous (possibly token) child's end and its end to the token start of the following element" - basically
    // expanding the range to encompass all the neighboring non-token trivia
    // Now, we perform that logic with the scanner instead
    let prior = astnav::find_preceding_token(source_file, list.pos());
    let prior_end = if prior.is_nil() {
        list.pos()
    } else {
        prior.end()
    };
    // Find the token that starts at or after list.End() using the scanner
    let scan = scanner_ls::get_scanner_for_source_file(source_file, list.end());
    let next_start = if scan.token() == SyntaxKind::EndOfFile {
        list.end()
    } else {
        scan.token_start()
    };
    TextRange::new(prior_end, next_start)
}

// Go: format/indent.go:613 getContainingListOrParentStart
pub fn get_containing_list_or_parent_start(
    parent: Node,
    child: Node,
    source_file: Node,
) -> (i32, i32) {
    let containing_list = get_containing_list(child, source_file);
    let start_pos = if containing_list.is_some() {
        containing_list.loc().pos()
    } else {
        get_token_pos_of_node(parent, source_file, false)
    };
    get_ecma_line_and_byte_offset_of_position(source_file, start_pos)
}

// Go: format/indent.go:624 isControlFlowEndingStatement
pub fn is_control_flow_ending_statement(kind: SyntaxKind, parent_kind: SyntaxKind) -> bool {
    match kind {
        SyntaxKind::ReturnStatement
        | SyntaxKind::ThrowStatement
        | SyntaxKind::ContinueStatement
        | SyntaxKind::BreakStatement => parent_kind != SyntaxKind::Block,
        _ => false,
    }
}

// Go: format/indent.go:637 ShouldIndentChildNode
/**
 * True when the parent node should indent the given child by an explicit rule.
 * @param isNextChild If true, we are judging indent of a hypothetical child *after* this one, not the current child.
 */
// PORT: Go `isNextChildArg ...bool` is a slice; only the first value is read.
pub fn should_indent_child_node(
    settings: &lsutil::FormatCodeSettings,
    parent: Node,
    child: Node,
    source_file: Node,
    is_next_child_arg: &[bool],
) -> bool {
    let mut is_next_child = false;
    if !is_next_child_arg.is_empty() {
        is_next_child = is_next_child_arg[0];
    }

    node_will_indent_child(settings, parent, child, source_file, false)
        && !(is_next_child
            && child.is_some()
            && is_control_flow_ending_statement(child.kind(), parent.kind()))
}

// Go: format/indent.go:646 NodeWillIndentChild
pub fn node_will_indent_child(
    settings: &lsutil::FormatCodeSettings,
    parent: Node,
    child: Node,
    source_file: Node,
    indent_by_default: bool,
) -> bool {
    let mut child_kind = SyntaxKind::Unknown;
    if child.is_some() {
        child_kind = child.kind();
    }

    match parent.kind() {
        SyntaxKind::ExpressionStatement
        | SyntaxKind::ClassDeclaration
        | SyntaxKind::ClassExpression
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::TypeAliasDeclaration
        | SyntaxKind::ArrayLiteralExpression
        | SyntaxKind::Block
        | SyntaxKind::ModuleBlock
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::TypeLiteral
        | SyntaxKind::MappedType
        | SyntaxKind::TupleType
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::CallExpression
        | SyntaxKind::NewExpression
        | SyntaxKind::VariableStatement
        | SyntaxKind::ExportAssignment
        | SyntaxKind::ReturnStatement
        | SyntaxKind::ConditionalExpression
        | SyntaxKind::ArrayBindingPattern
        | SyntaxKind::ObjectBindingPattern
        | SyntaxKind::JsxOpeningElement
        | SyntaxKind::JsxOpeningFragment
        | SyntaxKind::JsxSelfClosingElement
        | SyntaxKind::JsxExpression
        | SyntaxKind::MethodSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::ConstructSignature
        | SyntaxKind::Parameter
        | SyntaxKind::FunctionType
        | SyntaxKind::ConstructorType
        | SyntaxKind::ParenthesizedType
        | SyntaxKind::TaggedTemplateExpression
        | SyntaxKind::AwaitExpression
        | SyntaxKind::NamedExports
        | SyntaxKind::NamedImports
        | SyntaxKind::ExportSpecifier
        | SyntaxKind::ImportSpecifier
        | SyntaxKind::PropertyDeclaration
        | SyntaxKind::CaseClause
        | SyntaxKind::DefaultClause => {
            return true;
        }
        SyntaxKind::CaseBlock => {
            return settings.indent_switch_case.is_true_or_unknown();
        }
        SyntaxKind::VariableDeclaration
        | SyntaxKind::PropertyAssignment
        | SyntaxKind::BinaryExpression => {
            if settings
                .indent_multi_line_object_literal_beginning_on_blank_line
                .is_false_or_unknown()
                && source_file.is_some()
                && child_kind == SyntaxKind::ObjectLiteralExpression
            {
                return range_is_on_one_line(child.loc(), source_file);
            }
            if parent.kind() == SyntaxKind::BinaryExpression
                && source_file.is_some()
                && child_kind == SyntaxKind::JsxElement
            {
                let parent_start_line = get_ecma_line_of_position(
                    source_file,
                    skip_trivia(source_file_text(source_file), parent.pos()),
                );
                let child_start_line = get_ecma_line_of_position(
                    source_file,
                    skip_trivia(source_file_text(source_file), child.pos()),
                );
                return parent_start_line != child_start_line;
            }
            if parent.kind() != SyntaxKind::BinaryExpression {
                return true;
            }
            return indent_by_default;
        }
        SyntaxKind::DoStatement
        | SyntaxKind::WhileStatement
        | SyntaxKind::ForInStatement
        | SyntaxKind::ForOfStatement
        | SyntaxKind::ForStatement
        | SyntaxKind::IfStatement
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::Constructor
        | SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor => {
            return child_kind != SyntaxKind::Block;
        }
        SyntaxKind::ArrowFunction => {
            if source_file.is_some() && child_kind == SyntaxKind::ParenthesizedExpression {
                return range_is_on_one_line(child.loc(), source_file);
            }
            return child_kind != SyntaxKind::Block;
        }
        SyntaxKind::ExportDeclaration => {
            return child_kind != SyntaxKind::NamedExports;
        }
        SyntaxKind::ImportDeclaration => {
            return child_kind != SyntaxKind::ImportClause
                || (child.named_bindings().is_some()
                    && child.named_bindings().kind() != SyntaxKind::NamedImports);
        }
        SyntaxKind::JsxElement => {
            return child_kind != SyntaxKind::JsxClosingElement;
        }
        SyntaxKind::JsxFragment => {
            return child_kind != SyntaxKind::JsxClosingFragment;
        }
        SyntaxKind::IntersectionType | SyntaxKind::UnionType | SyntaxKind::SatisfiesExpression => {
            if child_kind == SyntaxKind::TypeLiteral
                || child_kind == SyntaxKind::TupleType
                || child_kind == SyntaxKind::MappedType
            {
                return false;
            }
            return indent_by_default;
        }
        SyntaxKind::TryStatement => {
            if child_kind == SyntaxKind::Block {
                return false;
            }
            return indent_by_default;
        }
        _ => {}
    }

    // No explicit rule for given nodes so the result will follow the default value argument
    indent_by_default
}

// Go: format/indent.go:779 childIsUnindentedBranchOfConditionalExpression
// A multiline conditional typically increases the indentation of its whenTrue and whenFalse children:
//
// condition
//
//	? whenTrue
//	: whenFalse;
//
// However, that indentation does not apply if the subexpressions themselves span multiple lines,
// applying their own indentation:
//
//	(() => {
//	  return complexCalculationForCondition();
//	})() ? {
//
//	  whenTrue: 'multiline object literal'
//	} : (
//
//	whenFalse('multiline parenthesized expression')
//
// );
//
// In these cases, we must discard the indentation increase that would otherwise be applied to the
// whenTrue and whenFalse children to avoid double-indenting their contents. To identify this scenario,
// we check for the whenTrue branch beginning on the line that the condition ends, and the whenFalse
// branch beginning on the line that the whenTrue branch ends.
pub fn child_is_unindented_branch_of_conditional_expression(
    parent: Node,
    child: Node,
    child_start_line: i32,
    source_file: Node,
) -> bool {
    if parent.kind() == SyntaxKind::ConditionalExpression
        && (child == parent.when_true() || child == parent.when_false())
    {
        let condition_end_line = get_ecma_line_of_position(source_file, parent.condition().end());
        if child == parent.when_true() {
            return child_start_line == condition_end_line;
        } else {
            // On the whenFalse side, we have to look at the whenTrue side, because if that one was
            // indented, whenFalse must also be indented:
            //
            // const y = true
            //   ? 1 : (          L1: whenTrue indented because it's on a new line
            //     0              L2: indented two stops, one because whenTrue was indented
            //   );                   and one because of the parentheses spanning multiple lines
            let true_start_line = get_start_line_for_node(parent.when_true(), source_file);
            let true_end_line = get_ecma_line_of_position(source_file, parent.when_true().end());
            return condition_end_line == true_start_line && true_end_line == child_start_line;
        }
    }
    false
}

// Go: format/indent.go:800 argumentStartsOnSameLineAsPreviousArgument
pub fn argument_starts_on_same_line_as_previous_argument(
    parent: Node,
    child: Node,
    child_start_line: i32,
    source_file: Node,
) -> bool {
    if is_call_expression(parent) || is_new_expression(parent) {
        if parent.arguments().is_empty() {
            return false;
        }
        let current_index = parent
            .arguments()
            .iter()
            .position(|n| n == child)
            .map_or(-1, |i| i as i32);
        if current_index == -1 {
            // If it's not one of the arguments, don't look past this
            return false;
        }
        if current_index == 0 {
            return false; // Can't look at previous node if first
        }

        let previous_node = parent.arguments().get((current_index - 1) as usize);
        let line_of_previous_node = get_ecma_line_of_position(source_file, previous_node.end());
        if child_start_line == line_of_previous_node {
            return true;
        }
    }
    false
}
