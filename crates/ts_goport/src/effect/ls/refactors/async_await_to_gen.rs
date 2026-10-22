//! Port of Effect-TS/tsgo `internal/refactors/async_await_to_gen.go`.
//!
//! The helpers that the other async/await refactors and effectGenToFn use
//! are here, as in Go (`clone_node_list` is in `refactors/mod.rs`).

use crate::ast::visitor::{NodeVisitorHooks, new_node_visitor};
use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::{clone_node_list, with_kind};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{find_effect_module_identifier, get_function_like_body};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/async_await_to_gen.go:12 AsyncAwaitToGen
pub static ASYNC_AWAIT_TO_GEN: Refactor = Refactor {
    name: "asyncAwaitToGen",
    description: "Convert async/await to Effect.gen",
    kind: "rewrite.effect.asyncAwaitToGen",
    run: run_async_await_to_gen,
};

// Go: refactors/async_await_to_gen.go:19 runAsyncAwaitToGen
fn run_async_await_to_gen(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain to find the nearest async function
    let async_fn = find_async_function(token);
    if async_fn.is_nil() {
        return Vec::new();
    }

    let effect_module_name = find_effect_module_identifier(ctx.source_file);

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Rewrite to Effect.gen", |tracker| {
        let new_decl = transform_async_to_effect_gen(tracker, async_fn, &effect_module_name);
        if new_decl.is_some() {
            set_parent_in_children(new_decl);
            // For FunctionDeclaration (a statement), replace directly.
            // For FunctionExpression/ArrowFunction (not statements), find the
            // containing statement and replace at that level to avoid a printer
            // assertion failure with complex synthetic trees in expression context.
            if async_fn.kind() == SyntaxKind::FunctionDeclaration {
                tracker.replace_node(sf, async_fn, new_decl, None);
            } else {
                replace_expression_via_statement(tracker, sf, async_fn, new_decl);
            }
        }
    });
    with_kind(action, "refactor.rewrite.effect.asyncAwaitToGen")
}

// Go: refactors/async_await_to_gen.go:64 replaceExpressionViaStatement
/// replaceExpressionViaStatement replaces an expression node by finding its
/// containing VariableStatement, rebuilding it with the new expression as
/// initializer, and replacing the entire statement. This avoids a printer
/// assertion failure that occurs when replacing non-statement nodes with
/// complex synthetic trees.
// A catch clause variable with an initializer (`catch (e = async () =>
// ...)`, a grammar error that parses) under a variable statement has a
// CatchClause parent: Go `AsVariableDeclarationList` panics there
// (`go_node_as_panic`), and the LSP request answers an internal error.
pub(crate) fn replace_expression_via_statement(
    tracker: &mut Tracker,
    sf: Node,
    old_expr: Node,
    new_expr: Node,
) {
    // Walk up to find containing VariableDeclaration
    let var_decl = find_parent_of_kind(old_expr, SyntaxKind::VariableDeclaration);
    if var_decl.is_nil() {
        // Fallback: replace directly
        tracker.replace_node(sf, old_expr, new_expr, None);
        return;
    }

    // Walk up to find containing VariableStatement
    let var_stmt = find_parent_of_kind(var_decl, SyntaxKind::VariableStatement);
    if var_stmt.is_nil() {
        tracker.replace_node(sf, old_expr, new_expr, None);
        return;
    }

    let new_var_stmt = {
        let f = tracker.node_factory();

        // Rebuild the VariableDeclaration with new initializer
        let mut name = Node::NIL;
        if var_decl.name().is_some() {
            name = f.deep_clone_node(var_decl.name());
        }
        let mut type_node = Node::NIL;
        if var_decl.type_().is_some() {
            type_node = f.deep_clone_node(var_decl.type_());
        }
        let new_var_decl = f.new_variable_declaration(name, Node::NIL, type_node, new_expr);

        // Rebuild the VariableDeclarationList
        // Go: refactors/async_await_to_gen.go:93 `varDecl.Parent.AsVariableDeclarationList()`
        let vdl = var_decl.parent();
        if vdl.kind() != SyntaxKind::VariableDeclarationList {
            go_node_as_panic(vdl, "VariableDeclarationList");
        }
        let new_var_decl_list = f.new_variable_declaration_list(
            f.new_node_list(&[new_var_decl]),
            vdl.flags() & NodeFlags::BLOCK_SCOPED,
        );

        // Rebuild the VariableStatement with cloned modifiers
        let mods = clone_modifier_tokens(tracker, var_stmt.modifiers());
        f.new_variable_statement(mods, new_var_decl_list)
    };

    set_parent_in_children(new_var_stmt);
    tracker.replace_node(sf, var_stmt, new_var_stmt, None);
}

/// The modifiers of `mods` as new modifier tokens, or nil when there are
/// none.
// PORT: Go repeats this loop in replaceExpressionViaStatement and in
// effect_gen_to_fn.go buildEffectGenToFnDeclaration (twice).
pub(super) fn clone_modifier_tokens(tracker: &Tracker, mods: ModifierList) -> ModifierList {
    if mods.is_nil() {
        return ModifierList::NIL;
    }
    let f = tracker.node_factory();
    let mod_nodes: Vec<Node> = mods
        .nodes()
        .iter()
        .map(|m| f.new_modifier(m.kind()))
        .collect();
    if mod_nodes.is_empty() {
        return ModifierList::NIL;
    }
    f.new_modifier_list(&mod_nodes)
}

// Go: refactors/async_await_to_gen.go:115 findParentOfKind
/// findParentOfKind walks up the parent chain to find a node of the given kind.
pub(super) fn find_parent_of_kind(node: Node, kind: SyntaxKind) -> Node {
    let mut n = node.parent();
    while n.is_some() {
        if n.kind() == kind {
            return n;
        }
        n = n.parent();
    }
    Node::NIL
}

// Go: refactors/async_await_to_gen.go:126 findAsyncFunction
/// findAsyncFunction walks the ancestor chain from token to find the nearest
/// async function declaration, function expression, or arrow function.
pub(super) fn find_async_function(token: Node) -> Node {
    let mut node = token;
    while node.is_some() {
        if matches!(
            node.kind(),
            SyntaxKind::FunctionDeclaration
                | SyntaxKind::FunctionExpression
                | SyntaxKind::ArrowFunction
        ) {
            if get_combined_modifier_flags(node).intersects(ModifierFlags::ASYNC)
                && get_function_like_body(node).is_some()
            {
                return node;
            }
            // If we hit a non-async function boundary, stop looking
            return Node::NIL;
        }
        node = node.parent();
    }
    Node::NIL
}

// Go: refactors/async_await_to_gen.go:143 transformAsyncToEffectGen
/// transformAsyncToEffectGen transforms an async function to use Effect.gen.
fn transform_async_to_effect_gen(tracker: &Tracker, node: Node, effect_module_name: &str) -> Node {
    let body = get_function_like_body(node);
    if body.is_nil() {
        return Node::NIL;
    }

    // Transform await expressions to yield* Effect.promise(...)
    let transformed_body = transform_body_await_to_yield(tracker, body, &mut |t, expr| {
        build_yield_star_promise(t, expr, effect_module_name)
    });

    // Build Effect.gen(function*() { transformedBody })
    let effect_gen_call = build_effect_gen_call(tracker, transformed_body, effect_module_name);

    // Build non-async declaration wrapping the gen call
    build_non_async_declaration(tracker, node, effect_gen_call)
}

// Go: refactors/async_await_to_gen.go:162 TransformAwaitExpr
/// TransformAwaitExpr is the callback type for transforming await expressions.
pub(super) type TransformAwaitExpr<'f> = dyn FnMut(&Tracker, Node) -> Node + 'f;

// Go: refactors/async_await_to_gen.go:166 transformBodyAwaitToYield
/// transformBodyAwaitToYield replaces all AwaitExpression nodes in the body
/// with the result of onAwait. Returns a deep-cloned, fully synthetic tree.
// PORT: the visitor callback is `Fn`, so `on_await` (an `FnMut` that the
// TryPromise refactors use to count the errors) sits in a `RefCell`. It does
// not call back into the visitor.
pub(super) fn transform_body_await_to_yield(
    tracker: &Tracker,
    body: Node,
    on_await: &mut TransformAwaitExpr<'_>,
) -> Node {
    let f = tracker.node_factory();

    // If no await expressions, just deep-clone the body
    if !contains_await_expression(body) {
        return f.deep_clone_node(body);
    }

    // Visit the original body to transform await → yield*
    let on_await = RefCell::new(on_await);
    let mut v = new_node_visitor(
        |n: Node, v| {
            if n.kind() == SyntaxKind::AwaitExpression {
                let visited_inner = v.visit_node(n.expression());
                return (*on_await.borrow_mut())(tracker, visited_inner);
            }
            v.visit_each_child(n)
        },
        Some(f),
        NodeVisitorHooks::default(),
        (),
    );

    let visited = v.visit_node(body);

    // Deep-clone the result to make all nodes synthetic
    let result = f.deep_clone_node(visited);
    set_parent_in_children(result);
    result
}

// Go: refactors/async_await_to_gen.go:193 containsAwaitExpression
/// containsAwaitExpression checks if a node tree contains any AwaitExpression.
fn contains_await_expression(node: Node) -> bool {
    if node.kind() == SyntaxKind::AwaitExpression {
        return true;
    }
    let mut found = false;
    node.for_each_child(|child| {
        if contains_await_expression(child) {
            found = true;
            return true; // stop
        }
        false
    });
    found
}

// Go: refactors/async_await_to_gen.go:209 buildYieldStarPromise
/// buildYieldStarPromise builds: yield* Effect.promise(() => expr)
pub(super) fn build_yield_star_promise(
    tracker: &Tracker,
    expr: Node,
    effect_module_name: &str,
) -> Node {
    let f = tracker.node_factory();

    // () => expr
    let arrow_fn = f.new_arrow_function(
        ModifierList::NIL,    // modifiers
        NodeList::NIL,        // typeParameters
        f.new_node_list(&[]), // parameters (empty)
        Node::NIL,            // returnType
        Node::NIL,            // fullSignature
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        expr,
    );

    // Effect.promise(() => expr)
    let effect_id = f.new_identifier(effect_module_name);
    let promise_access = f.new_property_access_expression(
        effect_id,
        Node::NIL,
        f.new_identifier("promise"),
        NodeFlags::NONE,
    );
    let promise_call = f.new_call_expression(
        promise_access,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&[arrow_fn]),
        NodeFlags::NONE,
    );

    // yield* Effect.promise(() => expr)
    f.new_yield_expression(f.new_token(SyntaxKind::AsteriskToken), promise_call)
}

// Go: refactors/async_await_to_gen.go:240 buildEffectGenCall
/// buildEffectGenCall builds: Effect.gen(function*() { body })
pub(super) fn build_effect_gen_call(
    tracker: &Tracker,
    body: Node,
    effect_module_name: &str,
) -> Node {
    let f = tracker.node_factory();
    let block_body = if body.kind() == SyntaxKind::Block {
        body
    } else {
        // Expression body: wrap in { return <expr> }
        let return_stmt = f.new_return_statement(body);
        f.new_block(f.new_node_list(&[return_stmt]), true)
    };

    // function*() { ... }
    let gen_fn = f.new_function_expression(
        ModifierList::NIL,                      // modifiers
        f.new_token(SyntaxKind::AsteriskToken), // asterisk (generator)
        Node::NIL,                              // name
        NodeList::NIL,                          // typeParameters
        f.new_node_list(&[]),                   // parameters (empty)
        Node::NIL,                              // returnType
        Node::NIL,                              // fullSignature
        block_body,
    );

    // Effect.gen(function*() { ... })
    let effect_id = f.new_identifier(effect_module_name);
    let gen_access = f.new_property_access_expression(
        effect_id,
        Node::NIL,
        f.new_identifier("gen"),
        NodeFlags::NONE,
    );
    f.new_call_expression(
        gen_access,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&[gen_fn]),
        NodeFlags::NONE,
    )
}

// Go: refactors/async_await_to_gen.go:276 buildNonAsyncDeclaration
/// buildNonAsyncDeclaration builds a new function declaration/expression/arrow
/// without the async modifier, with the given effectGenCall as the new body.
pub(super) fn build_non_async_declaration(
    tracker: &Tracker,
    node: Node,
    effect_gen_call: Node,
) -> Node {
    let modifiers = get_modifiers_without_async(tracker, node);
    let f = tracker.node_factory();

    match node.kind() {
        SyntaxKind::ArrowFunction => f.new_arrow_function(
            modifiers,
            clone_node_list(tracker, node.type_parameter_list()),
            clone_node_list(tracker, node.parameter_list()),
            Node::NIL, // returnType
            Node::NIL, // fullSignature
            f.new_token(SyntaxKind::EqualsGreaterThanToken),
            effect_gen_call,
        ),

        SyntaxKind::FunctionDeclaration | SyntaxKind::FunctionExpression => {
            let return_stmt = f.new_return_statement(effect_gen_call);
            let new_body = f.new_block(f.new_node_list(&[return_stmt]), true);
            let mut name = Node::NIL;
            if node.name().is_some() {
                name = f.deep_clone_node(node.name());
            }
            let type_parameters = clone_node_list(tracker, node.type_parameter_list());
            let parameters = clone_node_list(tracker, node.parameter_list());
            // PORT: Go has one case per kind with the same arguments.
            if node.kind() == SyntaxKind::FunctionDeclaration {
                f.new_function_declaration(
                    modifiers,
                    Node::NIL, // asteriskToken
                    name,
                    type_parameters,
                    parameters,
                    Node::NIL, // returnType
                    Node::NIL, // fullSignature
                    new_body,
                )
            } else {
                f.new_function_expression(
                    modifiers,
                    Node::NIL, // asteriskToken
                    name,
                    type_parameters,
                    parameters,
                    Node::NIL, // returnType
                    Node::NIL, // fullSignature
                    new_body,
                )
            }
        }

        _ => Node::NIL,
    }
}

// Go: refactors/async_await_to_gen.go:335 getModifiersWithoutAsync
/// getModifiersWithoutAsync returns a new modifier list with the async keyword removed.
pub(super) fn get_modifiers_without_async(tracker: &Tracker, node: Node) -> ModifierList {
    let src_modifiers = match node.kind() {
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction => node.modifiers(),
        _ => ModifierList::NIL,
    };

    if src_modifiers.is_nil() {
        return ModifierList::NIL;
    }

    let f = tracker.node_factory();
    let mod_nodes: Vec<Node> = src_modifiers
        .nodes()
        .iter()
        .filter(|m| m.kind() != SyntaxKind::AsyncKeyword)
        .map(|m| f.new_modifier(m.kind()))
        .collect();

    if mod_nodes.is_empty() {
        return ModifierList::NIL;
    }
    f.new_modifier_list(&mod_nodes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
    use crate::ls::{change, lsconv, lsutil};
    use crate::lsp::lsproto;

    // A catch clause variable with an initializer parses (TS1197 is a
    // checker error), and its VariableDeclaration has a CatchClause parent.
    // Go `varDecl.Parent.AsVariableDeclarationList()` (async_await_to_gen.go:93)
    // panics there, so the codeAction request answers an internal error
    // with this text instead of any action.
    #[test]
    fn replace_expression_via_statement_panics_as_go_on_a_catch_variable() {
        let text = "export const handler = () => {\n  try {\n    return 1\n  } catch (e = async () => 1) {\n    return 2\n  }\n}\n";
        let opts = SourceFileParseOptions {
            file_name: "/catch.ts".to_string(),
            ..Default::default()
        };
        let sf = parse_source_file(&opts, text, ScriptKind::TS).root;
        let pos = text.find("async").expect("the async arrow") as i32;
        let async_fn = find_async_function(astnav::get_token_at_position(sf, pos));
        assert_eq!(async_fn.kind(), SyntaxKind::ArrowFunction);
        let mut tracker = Tracker::new(change::new_tracker(
            &crate::gostd::context::background(),
            &crate::options::CompilerOptions::default(),
            lsutil::FormatCodeSettings::default(),
            lsconv::new_converters(lsproto::PositionEncodingKind::UTF16, |_| None),
        ));
        let new_expr = tracker.node_factory().new_identifier("replacement");
        let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            replace_expression_via_statement(&mut tracker, sf, async_fn, new_expr);
        }))
        .expect_err("Go panics");
        assert_eq!(
            payload
                .downcast_ref::<crate::core::GoPanic>()
                .map(|p| p.message.as_str()),
            Some(
                "interface conversion: ast.nodeData is *ast.CatchClause, not *ast.VariableDeclarationList"
            )
        );
    }
}
