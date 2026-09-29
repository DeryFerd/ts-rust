use crate::format::prelude::*;

// Go: format/util.go:12 rangeIsOnOneLine
pub fn range_is_on_one_line(node: TextRange, file: Node) -> bool {
    let start_line = get_ecma_line_of_position(file, node.pos());
    let end_line = get_ecma_line_of_position(file, node.end());
    start_line == end_line
}

// Go: format/util.go:18 getOpenTokenForList
pub fn get_open_token_for_list(node: Node, list: NodeList) -> SyntaxKind {
    match node.kind() {
        SyntaxKind::Constructor
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::MethodSignature
        | SyntaxKind::ArrowFunction
        | SyntaxKind::CallSignature
        | SyntaxKind::ConstructSignature
        | SyntaxKind::FunctionType
        | SyntaxKind::ConstructorType
        | SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor => {
            if node.type_parameter_list() == list {
                return SyntaxKind::LessThanToken;
            } else if node.parameter_list() == list {
                return SyntaxKind::OpenParenToken;
            }
        }
        SyntaxKind::CallExpression | SyntaxKind::NewExpression => {
            if node.type_argument_list() == list {
                return SyntaxKind::LessThanToken;
            } else if node.argument_list() == list {
                return SyntaxKind::OpenParenToken;
            }
        }
        SyntaxKind::ClassDeclaration
        | SyntaxKind::ClassExpression
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::TypeAliasDeclaration => {
            if node.type_parameter_list() == list {
                return SyntaxKind::LessThanToken;
            }
        }
        SyntaxKind::TypeReference
        | SyntaxKind::TaggedTemplateExpression
        | SyntaxKind::TypeQuery
        | SyntaxKind::ExpressionWithTypeArguments
        | SyntaxKind::ImportType => {
            if node.type_argument_list() == list {
                return SyntaxKind::LessThanToken;
            }
        }
        SyntaxKind::TypeLiteral => {
            return SyntaxKind::OpenBraceToken;
        }
        _ => {}
    }

    SyntaxKind::Unknown
}

// Go: format/util.go:65 getCloseTokenForOpenToken
pub fn get_close_token_for_open_token(kind: SyntaxKind) -> SyntaxKind {
    // TODO: matches strada - seems like it could handle more pairs of braces, though? [] notably missing
    match kind {
        SyntaxKind::OpenParenToken => return SyntaxKind::CloseParenToken,
        SyntaxKind::LessThanToken => return SyntaxKind::GreaterThanToken,
        SyntaxKind::OpenBraceToken => return SyntaxKind::CloseBraceToken,
        _ => {}
    }
    SyntaxKind::Unknown
}

// Go: format/util.go:78 GetLineStartPositionForPosition
pub fn get_line_start_position_for_position(position: i32, source_file: Node) -> i32 {
    let line_starts = &*get_ecma_line_starts(source_file);
    let line = get_ecma_line_of_position(source_file, position);
    line_starts[line as usize]
}

/**
 * Tests whether `child` is a grammar error on `parent`.
 * In strada, this also checked node arrays, but it is never actually called with one in practice.
 */
// Go: format/util.go:88 isGrammarError
pub fn is_grammar_error(parent: Node, child: Node) -> bool {
    if is_type_parameter_declaration(parent) {
        // PORT: Go `parent.AsTypeParameterDeclaration().Expression`; the
        // `Node::expression` accessor reads that field for this kind.
        return child == parent.expression();
    }
    if is_property_signature_declaration(parent) {
        return child == parent.initializer();
    }
    if is_property_declaration(parent) {
        return is_auto_accessor_property_declaration(parent)
            && child == parent.postfix_token()
            && child.kind() == SyntaxKind::QuestionToken;
    }
    if is_property_assignment(parent) {
        let mods = parent.modifiers();
        return child == parent.postfix_token()
            || (mods.is_some()
                && is_grammar_error_element(mods.node_list(), child, is_modifier_like));
    }
    if is_shorthand_property_assignment(parent) {
        let mods = parent.modifiers();
        return child == parent.equals_token()
            || child == parent.postfix_token()
            || (mods.is_some()
                && is_grammar_error_element(mods.node_list(), child, is_modifier_like));
    }
    if is_method_declaration(parent) {
        return child == parent.postfix_token() && child.kind() == SyntaxKind::ExclamationToken;
    }
    if is_constructor_declaration(parent) {
        // PORT: Go `parent.AsConstructorDeclaration().Type`; `Node::type_`
        // reads that field for this kind.
        return child == parent.type_()
            || is_grammar_error_element(
                parent.type_parameter_list(),
                child,
                is_type_parameter_declaration,
            );
    }
    if is_get_accessor_declaration(parent) {
        return is_grammar_error_element(
            parent.type_parameter_list(),
            child,
            is_type_parameter_declaration,
        );
    }
    if is_set_accessor_declaration(parent) {
        // PORT: Go `parent.AsSetAccessorDeclaration().Type`; `Node::type_`
        // reads that field for this kind.
        return child == parent.type_()
            || is_grammar_error_element(
                parent.type_parameter_list(),
                child,
                is_type_parameter_declaration,
            );
    }
    if is_namespace_export_declaration(parent) {
        let mods = parent.modifiers();
        return mods.is_some()
            && is_grammar_error_element(mods.node_list(), child, is_modifier_like);
    }
    false
}

// Go: format/util.go:127 isGrammarErrorElement
pub fn is_grammar_error_element(
    list: NodeList,
    child: Node,
    is_possible_element: fn(Node) -> bool,
) -> bool {
    if list.is_nil() || list.nodes().is_empty() {
        return false;
    }
    if !is_possible_element(child) {
        return false;
    }
    list.nodes().iter().any(|n| n == child)
}

/**
 * Validating `expectedTokenKind` ensures the token was typed in the context we expect (eg: not a comment).
 * @param expectedTokenKind The kind of the last token constituting the desired parent node.
 */
// Go: format/util.go:141 findImmediatelyPrecedingTokenOfKind
pub fn find_immediately_preceding_token_of_kind(
    end: i32,
    expected_token_kind: SyntaxKind,
    source_file: Node,
) -> Node {
    let preceding_token = astnav::find_preceding_token(source_file, end);
    if preceding_token.is_nil()
        || preceding_token.kind() != expected_token_kind
        || preceding_token.end() != end
    {
        return Node::NIL;
    }
    preceding_token
}

/**
 * Finds the highest node enclosing `node` at the same list level as `node`
 * and whose end does not exceed `node.end`.
 *
 * Consider typing the following
 * ```text
 * let x = 1;
 * while (true) {
 * }
 * ```
 * Upon typing the closing curly, we want to format the entire `while`-statement, but not the preceding
 * variable declaration.
 */
// Go: format/util.go:162 findOutermostNodeWithinListLevel
pub fn find_outermost_node_within_list_level(node: Node) -> Node {
    let mut current = node;
    while current.is_some()
        && current.parent().is_some()
        && current.parent().end() == node.end()
        && !is_list_element(current.parent(), current)
    {
        current = current.parent();
    }

    current
}

// Returns true if node is a element in some list in parent
// i.e. parent is class declaration with the list of members and node is one of members.
// Go: format/util.go:176 isListElement
pub fn is_list_element(parent: Node, node: Node) -> bool {
    match parent.kind() {
        SyntaxKind::ClassDeclaration | SyntaxKind::InterfaceDeclaration => {
            return node.loc().contained_by(parent.member_list().loc());
        }
        SyntaxKind::ModuleDeclaration => {
            let body = parent.body();
            return body.is_some()
                && body.kind() == SyntaxKind::ModuleBlock
                && node.loc().contained_by(body.statement_list().loc());
        }
        SyntaxKind::SourceFile | SyntaxKind::Block | SyntaxKind::ModuleBlock => {
            return node.loc().contained_by(parent.statement_list().loc());
        }
        SyntaxKind::CatchClause => {
            return node
                .loc()
                .contained_by(parent.block().statement_list().loc());
        }
        _ => {}
    }

    false
}
