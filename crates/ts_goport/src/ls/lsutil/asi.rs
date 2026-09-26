//! Port of Go `ls/lsutil/asi.go`.

use crate::astnav;
use crate::ls::lsutil::prelude::*;

// Go: ls/lsutil/asi.go:9 PositionIsASICandidate
pub fn position_is_asi_candidate(pos: i32, context: Node, file: Node) -> bool {
    let context_ancestor = find_ancestor_or_quit(context, |ancestor: Node| -> FindAncestorResult {
        if ancestor.end() != pos {
            return FindAncestorResult::FIND_ANCESTOR_QUIT;
        }

        to_find_ancestor_result(syntax_may_be_asi_candidate(ancestor.kind()))
    });

    context_ancestor.is_some() && node_is_asi_candidate(context_ancestor, file)
}

// Go: ls/lsutil/asi.go:21 SyntaxMayBeASICandidate
pub fn syntax_may_be_asi_candidate(kind: SyntaxKind) -> bool {
    syntax_requires_trailing_comma_or_semicolon_or_asi(kind)
        || syntax_requires_trailing_function_block_or_semicolon_or_asi(kind)
        || syntax_requires_trailing_module_block_or_semicolon_or_asi(kind)
        || syntax_requires_trailing_semicolon_or_asi(kind)
}

// Go: ls/lsutil/asi.go:28 SyntaxRequiresTrailingCommaOrSemicolonOrASI
pub fn syntax_requires_trailing_comma_or_semicolon_or_asi(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::CallSignature
        || kind == SyntaxKind::ConstructSignature
        || kind == SyntaxKind::IndexSignature
        || kind == SyntaxKind::PropertySignature
        || kind == SyntaxKind::MethodSignature
}

// Go: ls/lsutil/asi.go:36 SyntaxRequiresTrailingFunctionBlockOrSemicolonOrASI
pub fn syntax_requires_trailing_function_block_or_semicolon_or_asi(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::FunctionDeclaration
        || kind == SyntaxKind::Constructor
        || kind == SyntaxKind::MethodDeclaration
        || kind == SyntaxKind::GetAccessor
        || kind == SyntaxKind::SetAccessor
}

// Go: ls/lsutil/asi.go:44 SyntaxRequiresTrailingModuleBlockOrSemicolonOrASI
pub fn syntax_requires_trailing_module_block_or_semicolon_or_asi(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::ModuleDeclaration
}

// Go: ls/lsutil/asi.go:48 SyntaxRequiresTrailingSemicolonOrASI
pub fn syntax_requires_trailing_semicolon_or_asi(kind: SyntaxKind) -> bool {
    kind == SyntaxKind::VariableStatement
        || kind == SyntaxKind::ExpressionStatement
        || kind == SyntaxKind::DoStatement
        || kind == SyntaxKind::ContinueStatement
        || kind == SyntaxKind::BreakStatement
        || kind == SyntaxKind::ReturnStatement
        || kind == SyntaxKind::ThrowStatement
        || kind == SyntaxKind::DebuggerStatement
        || kind == SyntaxKind::PropertyDeclaration
        || kind == SyntaxKind::TypeAliasDeclaration
        || kind == SyntaxKind::ImportDeclaration
        || kind == SyntaxKind::ImportEqualsDeclaration
        || kind == SyntaxKind::ExportDeclaration
        || kind == SyntaxKind::NamespaceExportDeclaration
        || kind == SyntaxKind::ExportAssignment
}

// Go: ls/lsutil/asi.go:66 NodeIsASICandidate
pub fn node_is_asi_candidate(node: Node, file: Node) -> bool {
    let last_token = get_last_token(node, file);
    if last_token.is_some() && last_token.kind() == SyntaxKind::SemicolonToken {
        return false;
    }

    if syntax_requires_trailing_comma_or_semicolon_or_asi(node.kind()) {
        if last_token.is_some() && last_token.kind() == SyntaxKind::CommaToken {
            return false;
        }
    } else if syntax_requires_trailing_module_block_or_semicolon_or_asi(node.kind()) {
        let last_child = get_last_child(node, file);
        if last_child.is_some() && is_module_block(last_child) {
            return false;
        }
    } else if syntax_requires_trailing_function_block_or_semicolon_or_asi(node.kind()) {
        let last_child = get_last_child(node, file);
        if last_child.is_some() && is_function_block(last_child) {
            return false;
        }
    } else if !syntax_requires_trailing_semicolon_or_asi(node.kind()) {
        return false;
    }

    // See comment in parser's `parseDoStatement`
    if node.kind() == SyntaxKind::DoStatement {
        return true;
    }

    let top_node = find_ancestor(node, |ancestor: Node| -> bool {
        ancestor.parent().is_nil()
    });
    let next_token = astnav::find_next_token(node, top_node, file);
    if next_token.is_nil() || next_token.kind() == SyntaxKind::CloseBraceToken {
        return true;
    }

    let start_line = get_ecma_line_of_position(file, node.end());
    let end_line = get_ecma_line_of_position(
        file,
        astnav::get_start_of_node(next_token, file, false /*includeJSDoc*/),
    );
    start_line != end_line
}
