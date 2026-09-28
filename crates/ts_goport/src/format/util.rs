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
    let line_starts = get_ecma_line_starts(source_file);
    let line = get_ecma_line_of_position(source_file, position);
    line_starts[line as usize]
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

// Go: format/util.go:137 isMemberListElement
pub fn is_member_list_element(parent: Node, node: Node) -> bool {
    match parent.kind() {
        SyntaxKind::ClassDeclaration
        | SyntaxKind::ClassExpression
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::TypeLiteral
        | SyntaxKind::MappedType => {
            return node.loc().contained_by(parent.member_list().loc());
        }
        _ => {}
    }
    false
}
