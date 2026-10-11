//! Port of Effect-TS/tsgo `internal/refactors/toggle_return_type_annotation.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::TypeParser;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/toggle_return_type_annotation.go:14 ToggleReturnTypeAnnotation
pub static TOGGLE_RETURN_TYPE_ANNOTATION: Refactor = Refactor {
    name: "toggleReturnTypeAnnotation",
    description: "Toggle return type annotation",
    kind: "rewrite.effect.toggleReturnTypeAnnotation",
    run: run_toggle_return_type_annotation,
};

// Go: refactors/toggle_return_type_annotation.go:21 runToggleReturnTypeAnnotation
fn run_toggle_return_type_annotation(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain looking for a function-like declaration
    let mut matched_node = Node::NIL;
    let mut node = token;
    while node.is_some() {
        if matches!(
            node.kind(),
            SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
                | SyntaxKind::MethodDeclaration
        ) {
            matched_node = node;
            break;
        }
        node = node.parent();
    }

    if matched_node.is_nil() {
        return Vec::new();
    }

    // Get the type node and close paren position
    let type_node = get_function_like_type(matched_node);
    let close_paren =
        astnav::find_child_of_kind(matched_node, SyntaxKind::CloseParenToken, ctx.source_file);

    // For arrow functions without parens (e.g., x => ...), use the last parameter end
    let mut end_node = Node::NIL;
    if close_paren.is_some() {
        end_node = close_paren;
    } else if matched_node.kind() == SyntaxKind::ArrowFunction {
        if let Some(last) = matched_node.parameters().last() {
            end_node = last;
        }
    }

    if end_node.is_nil() {
        return Vec::new();
    }

    let sf = ctx.source_file;
    if type_node.is_some() {
        // Remove existing return type annotation: delete from endNode.End() to type.End()
        let action = ctx.new_refactor_action("Toggle return type annotation", |tracker| {
            tracker.delete_range(sf, TextRange::new(end_node.end(), type_node.end()));
        });
        return with_kind(action, "refactor.rewrite.effect.toggleReturnTypeAnnotation");
    }

    // Add return type annotation: infer return type and insert after close paren
    // Must have a body to infer from
    // PORT: Go `BodyData() == nil` cannot happen for the 4 kinds above.
    if matched_node.body().is_nil() {
        return Vec::new();
    }

    let return_type = get_inferred_return_type_from_checker(ctx.tp, matched_node);
    if return_type.is_nil() {
        return Vec::new();
    }

    let type_str = ctx.tp.checker.type_to_string_ex(
        return_type,
        matched_node,
        TypeFormatFlags::NO_TRUNCATION,
        None,
    );
    if type_str.is_empty() {
        return Vec::new();
    }

    let pos = ctx.byte_pos_to_lsp_position(end_node.end());
    let action = ctx.new_refactor_action("Toggle return type annotation", |tracker| {
        tracker.insert_text(sf, pos, &(": ".to_string() + &type_str));
    });
    with_kind(action, "refactor.rewrite.effect.toggleReturnTypeAnnotation")
}

// Go: refactors/toggle_return_type_annotation.go:110 getFunctionLikeType
// getFunctionLikeType returns the return type node from a function-like declaration.
fn get_function_like_type(node: Node) -> Node {
    match node.kind() {
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::MethodDeclaration => node.type_(),
        _ => Node::NIL,
    }
}

// Go: refactors/toggle_return_type_annotation.go:126 getInferredReturnTypeFromChecker
// getInferredReturnTypeFromChecker extracts the return type from a function-like declaration
// using the type checker. It handles overloaded functions and regular signatures.
fn get_inferred_return_type_from_checker(tp: &mut TypeParser<'_>, declaration: Node) -> TypeId {
    let mut return_type = TypeId::NIL;

    // Try overloaded function handling
    let decl_type = tp.get_type_at_location(declaration);
    if decl_type.is_some() {
        let c = &mut *tp.checker;
        let signatures = c.get_signatures_of_type(decl_type, SignatureKind::CALL);
        if signatures.len() > 1 {
            let mut return_types = Vec::new();
            for &sig in signatures.iter() {
                let rt = c.get_return_type_of_signature(sig);
                if rt.is_some() {
                    return_types.push(rt);
                }
            }
            if !return_types.is_empty() {
                return_type = c.get_union_type(&return_types);
            }
        }
    }

    if return_type.is_nil() {
        let c = &mut *tp.checker;
        let sig = c.get_signature_from_declaration(declaration);
        if sig.is_some() {
            return_type = c.get_return_type_of_signature(sig);
        }
    }

    return_type
}
