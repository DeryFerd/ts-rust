//! Port of Go `ls/lsutil/completednode.go`.

use crate::astnav;
use crate::frontend::scanner::scanner_ls;
use crate::ls::lsutil::prelude::*;

// Go: ls/lsutil/completednode.go:12 PositionBelongsToNode
/// PositionBelongsToNode returns true if the position belongs to the node.
/// Assumes `candidate.Pos() <= position` holds.
pub fn position_belongs_to_node(candidate: Node, position: i32, file: Node) -> bool {
    if candidate.pos() > position {
        crate::core::go_panic("Expected candidate.pos <= position".to_string());
    }
    position < candidate.end() || !is_completed_node(candidate, file)
}

// Go: ls/lsutil/completednode.go:19 IsCompletedNode
pub fn is_completed_node(n: Node, source_file: Node) -> bool {
    if n.is_nil() || node_is_missing(n) {
        return false;
    }

    match n.kind() {
        SyntaxKind::ClassDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::ObjectBindingPattern
        | SyntaxKind::TypeLiteral
        | SyntaxKind::Block
        | SyntaxKind::ModuleBlock
        | SyntaxKind::CaseBlock
        | SyntaxKind::NamedImports
        | SyntaxKind::NamedExports => node_ends_with(n, SyntaxKind::CloseBraceToken, source_file),

        SyntaxKind::CatchClause => is_completed_node(n.block(), source_file),

        SyntaxKind::NewExpression => {
            if n.argument_list().is_nil() {
                return true;
            }
            // Go: fallthrough to the CallExpression case.
            node_ends_with(n, SyntaxKind::CloseParenToken, source_file)
        }

        SyntaxKind::CallExpression
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::ParenthesizedType => {
            node_ends_with(n, SyntaxKind::CloseParenToken, source_file)
        }

        SyntaxKind::FunctionType | SyntaxKind::ConstructorType => {
            is_completed_node(n.type_(), source_file)
        }

        SyntaxKind::Constructor
        | SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::MethodSignature
        | SyntaxKind::ConstructSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::ArrowFunction => {
            if n.body().is_some() {
                return is_completed_node(n.body(), source_file);
            }
            if n.type_().is_some() {
                return is_completed_node(n.type_(), source_file);
            }
            // Even though type parameters can be unclosed, we can get away with
            // having at least a closing paren.
            has_child_of_kind(n, SyntaxKind::CloseParenToken, source_file)
        }

        SyntaxKind::ModuleDeclaration => {
            n.body().is_some() && is_completed_node(n.body(), source_file)
        }

        SyntaxKind::IfStatement => {
            if n.else_statement().is_some() {
                return is_completed_node(n.else_statement(), source_file);
            }
            is_completed_node(n.then_statement(), source_file)
        }

        SyntaxKind::ExpressionStatement => {
            is_completed_node(n.expression(), source_file)
                || has_child_of_kind(n, SyntaxKind::SemicolonToken, source_file)
        }

        SyntaxKind::ArrayLiteralExpression
        | SyntaxKind::ArrayBindingPattern
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::ComputedPropertyName
        | SyntaxKind::TupleType => node_ends_with(n, SyntaxKind::CloseBracketToken, source_file),

        SyntaxKind::IndexSignature => {
            // Go: n.AsIndexSignatureDeclaration().Type
            if n.type_().is_some() {
                return is_completed_node(n.type_(), source_file);
            }
            has_child_of_kind(n, SyntaxKind::CloseBracketToken, source_file)
        }

        SyntaxKind::CaseClause | SyntaxKind::DefaultClause => {
            // there is no such thing as terminator token for CaseClause/DefaultClause so for simplicity always consider them non-completed
            false
        }

        SyntaxKind::ForStatement
        | SyntaxKind::ForInStatement
        | SyntaxKind::ForOfStatement
        | SyntaxKind::WhileStatement => is_completed_node(n.statement(), source_file),
        SyntaxKind::DoStatement => {
            // rough approximation: if DoStatement has While keyword - then if node is completed is checking the presence of ')';
            if has_child_of_kind(n, SyntaxKind::WhileKeyword, source_file) {
                return node_ends_with(n, SyntaxKind::CloseParenToken, source_file);
            }
            is_completed_node(n.statement(), source_file)
        }

        SyntaxKind::TypeQuery => is_completed_node(n.expr_name(), source_file),

        SyntaxKind::TypeOfExpression
        | SyntaxKind::DeleteExpression
        | SyntaxKind::VoidExpression
        | SyntaxKind::YieldExpression
        | SyntaxKind::SpreadElement => is_completed_node(n.expression(), source_file),

        SyntaxKind::TaggedTemplateExpression => is_completed_node(n.template(), source_file),

        SyntaxKind::TemplateExpression => {
            if n.template_spans().is_nil() {
                return false;
            }
            let last_span = n.template_spans().nodes().last().unwrap_or(Node::NIL);
            is_completed_node(last_span, source_file)
        }

        SyntaxKind::TemplateSpan => node_is_present(n.literal()),

        SyntaxKind::ExportDeclaration | SyntaxKind::ImportDeclaration => {
            node_is_present(n.module_specifier())
        }

        SyntaxKind::PrefixUnaryExpression => is_completed_node(n.operand(), source_file),

        SyntaxKind::BinaryExpression => is_completed_node(n.right(), source_file),

        SyntaxKind::ConditionalExpression => is_completed_node(n.when_false(), source_file),

        _ => true,
    }
}

// Go: ls/lsutil/completednode.go:162 nodeEndsWith
/// Checks if node ends with 'expectedLastToken'.
/// If child at position 'length - 1' is 'SemicolonToken' it is skipped and 'expectedLastToken' is compared with child at position 'length - 2'.
fn node_ends_with(n: Node, expected_last_token: SyntaxKind, source_file: Node) -> bool {
    let last_child_node = get_last_visited_child(n, source_file);
    let mut last_node_and_tokens: Vec<Node> = Vec::new();
    let token_start_pos;
    if last_child_node.is_some() {
        last_node_and_tokens = vec![last_child_node];
        token_start_pos = last_child_node.end();
    } else {
        token_start_pos = n.pos();
    }
    let sf_text = source_file_text(source_file);
    let mut scanner =
        scanner_ls::get_scanner_for_source_file(source_file, &sf_text, token_start_pos);
    let mut start_pos = token_start_pos;
    while start_pos < n.end() {
        let token_kind = scanner.token();
        let token_full_start = scanner.token_full_start();
        let token_end = scanner.token_end();
        let token = source_file_get_or_create_token(
            source_file,
            token_kind,
            token_full_start,
            token_end,
            n,
            scanner.token_flags(),
        );
        last_node_and_tokens.push(token);
        start_pos = token_end;
        scanner.scan();
    }
    if last_node_and_tokens.is_empty() {
        return false;
    }
    let last_child = last_node_and_tokens[last_node_and_tokens.len() - 1];
    if last_child.kind() == expected_last_token {
        return true;
    } else if last_child.kind() == SyntaxKind::SemicolonToken && last_node_and_tokens.len() > 1 {
        return last_node_and_tokens[last_node_and_tokens.len() - 2].kind() == expected_last_token;
    }
    false
}

// Go: ls/lsutil/completednode.go:194 hasChildOfKind
fn has_child_of_kind(containing_node: Node, kind: SyntaxKind, source_file: Node) -> bool {
    astnav::find_child_of_kind(containing_node, kind, source_file).is_some()
}
