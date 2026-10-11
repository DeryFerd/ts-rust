//! Port of Effect-TS/tsgo `internal/refactors/async_await_to_gen_try_promise.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::async_await_to_gen::{
    build_effect_gen_call, build_non_async_declaration, find_async_function, find_parent_of_kind,
    replace_expression_via_statement, transform_body_await_to_yield,
};
use crate::effect::ls::refactors::with_kind;
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{
    find_effect_module_identifier, find_module_identifier, get_function_like_body,
};
use crate::ls::CodeAction;
use crate::ls::change::LeadingTriviaOption;
use crate::prelude::*;

// Go: refactors/async_await_to_gen_try_promise.go:14 AsyncAwaitToGenTryPromise
pub static ASYNC_AWAIT_TO_GEN_TRY_PROMISE: Refactor = Refactor {
    name: "asyncAwaitToGenTryPromise",
    description: "Convert async/await to Effect.gen (with error handling)",
    kind: "rewrite.effect.asyncAwaitToGenTryPromise",
    run: run_async_await_to_gen_try_promise,
};

// Go: refactors/async_await_to_gen_try_promise.go:21 runAsyncAwaitToGenTryPromise
fn run_async_await_to_gen_try_promise(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
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
    let data_module_name = find_module_identifier(ctx.source_file, "Data");

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Rewrite to Effect.gen with failures", |tracker| {
        transform_async_to_effect_gen_try_promise(
            tracker,
            sf,
            async_fn,
            &effect_module_name,
            &data_module_name,
        );
    });
    with_kind(action, "refactor.rewrite.effect.asyncAwaitToGenTryPromise")
}

// Go: refactors/async_await_to_gen_try_promise.go:50 transformAsyncToEffectGenTryPromise
fn transform_async_to_effect_gen_try_promise(
    tracker: &mut Tracker,
    sf: Node,
    node: Node,
    effect_module_name: &str,
    data_module_name: &str,
) {
    let body = get_function_like_body(node);
    if body.is_nil() {
        return;
    }

    // Track error classes to generate
    let mut error_count = 0;
    let mut error_classes: Vec<Node> = Vec::new();

    // Determine if function is exported (error classes should match)
    let is_exported = is_exported_for_error_classes(node);

    // Transform await expressions to yield* Effect.tryPromise(...)
    let transformed_body = transform_body_await_to_yield(tracker, body, &mut |t, expr| {
        error_count += 1;
        let error_name = format!("Error{error_count}");

        // Build the error class declaration
        let error_class = build_tagged_error_class(t, data_module_name, &error_name, is_exported);
        error_classes.push(error_class);

        build_yield_star_try_promise(t, expr, effect_module_name, &error_name)
    });

    // Build Effect.gen(function*() { transformedBody })
    let effect_gen_call = build_effect_gen_call(tracker, transformed_body, effect_module_name);

    // Build non-async declaration wrapping the gen call
    let new_decl = build_non_async_declaration(tracker, node, effect_gen_call);
    if new_decl.is_nil() {
        return;
    }

    set_parent_in_children(new_decl);

    insert_error_classes_and_replace(tracker, sf, node, new_decl, error_classes);
}

/// Go: `isExported` in transformAsyncToEffectGenTryPromise: the function's
/// own export flag, else the export flag of the nearest variable statement
/// above it.
// PORT: Go repeats these lines in async_await_to_fn_try_promise.go:240.
pub(super) fn is_exported_for_error_classes(node: Node) -> bool {
    let mut is_exported = get_combined_modifier_flags(node).intersects(ModifierFlags::EXPORT);
    // Also check parent variable statement for export
    if !is_exported {
        let var_stmt = find_parent_of_kind(node, SyntaxKind::VariableStatement);
        if var_stmt.is_some() {
            is_exported = get_combined_modifier_flags(var_stmt).intersects(ModifierFlags::EXPORT);
        }
    }
    is_exported
}

/// Go: the tail of transformAsyncToEffectGenTryPromise: insert the error
/// classes before the top-level statement, then replace the function.
// PORT: Go repeats these lines in async_await_to_fn_try_promise.go:275.
pub(super) fn insert_error_classes_and_replace(
    tracker: &mut Tracker,
    sf: Node,
    node: Node,
    new_decl: Node,
    error_classes: Vec<Node>,
) {
    // Find the top-level statement containing the function (for inserting error classes before it)
    let top_level_stmt = find_top_level_statement(node);

    // Insert error classes before the top-level statement
    for error_class in error_classes {
        set_parent_in_children(error_class);
        tracker.insert_node_before(
            sf,
            top_level_stmt,
            error_class,
            true,
            LeadingTriviaOption::NONE,
        );
    }

    // Replace the function
    if node.kind() == SyntaxKind::FunctionDeclaration {
        tracker.replace_node(sf, node, new_decl, None);
    } else {
        replace_expression_via_statement(tracker, sf, node, new_decl);
    }
}

// Go: refactors/async_await_to_gen_try_promise.go:112 findTopLevelStatement
/// findTopLevelStatement walks up the parent chain from node until it finds
/// a node whose parent is the SourceFile.
fn find_top_level_statement(node: Node) -> Node {
    let mut current = node;
    while current.parent().is_some() && current.parent().kind() != SyntaxKind::SourceFile {
        current = current.parent();
    }
    current
}

// Go: refactors/async_await_to_gen_try_promise.go:121 buildYieldStarTryPromise
/// buildYieldStarTryPromise builds: yield* Effect.tryPromise({ try: () => expr, catch: cause => new ErrorN({ cause }) })
pub(super) fn build_yield_star_try_promise(
    tracker: &Tracker,
    expr: Node,
    effect_module_name: &str,
    error_name: &str,
) -> Node {
    let f = tracker.node_factory();

    // try: () => expr
    let try_arrow = f.new_arrow_function(
        ModifierList::NIL,    // modifiers
        NodeList::NIL,        // typeParameters
        f.new_node_list(&[]), // parameters (empty)
        Node::NIL,            // returnType
        Node::NIL,            // fullSignature
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        expr,
    );
    let try_prop = f.new_property_assignment(
        ModifierList::NIL, // modifiers
        f.new_identifier("try"),
        Node::NIL, // postfixToken
        Node::NIL, // typeNode
        try_arrow,
    );

    // catch: cause => new ErrorN({ cause })
    let cause_param = f.new_parameter_declaration(
        ModifierList::NIL, // modifiers
        Node::NIL,         // dotDotDotToken
        f.new_identifier("cause"),
        Node::NIL, // questionToken
        Node::NIL, // typeNode
        Node::NIL, // initializer
    );

    // new ErrorN({ cause })
    let cause_shorthand = f.new_shorthand_property_assignment(
        ModifierList::NIL, // modifiers
        f.new_identifier("cause"),
        Node::NIL, // postfixToken
        Node::NIL, // typeNode
        Node::NIL, // equalsToken
        Node::NIL, // objectAssignmentInitializer
    );
    let obj_literal = f.new_object_literal_expression(
        f.new_node_list(&[cause_shorthand]),
        false, // not multiline
    );
    let new_error_expr = f.new_new_expression(
        f.new_identifier(error_name),
        NodeList::NIL, // typeArguments
        f.new_node_list(&[obj_literal]),
    );

    let catch_arrow = f.new_arrow_function(
        ModifierList::NIL, // modifiers
        NodeList::NIL,     // typeParameters
        f.new_node_list(&[cause_param]),
        Node::NIL, // returnType
        Node::NIL, // fullSignature
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        new_error_expr,
    );
    let catch_prop = f.new_property_assignment(
        ModifierList::NIL, // modifiers
        f.new_identifier("catch"),
        Node::NIL, // postfixToken
        Node::NIL, // typeNode
        catch_arrow,
    );

    // { try: () => expr, catch: cause => new ErrorN({ cause }) }
    let options_obj = f.new_object_literal_expression(
        f.new_node_list(&[try_prop, catch_prop]),
        false, // not multiline
    );

    // Effect.tryPromise({ ... })
    let effect_id = f.new_identifier(effect_module_name);
    let try_promise_access = f.new_property_access_expression(
        effect_id,
        Node::NIL,
        f.new_identifier("tryPromise"),
        NodeFlags::NONE,
    );
    let try_promise_call = f.new_call_expression(
        try_promise_access,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&[options_obj]),
        NodeFlags::NONE,
    );

    // yield* Effect.tryPromise({ ... })
    f.new_yield_expression(f.new_token(SyntaxKind::AsteriskToken), try_promise_call)
}

// Go: refactors/async_await_to_gen_try_promise.go:211 buildTaggedErrorClass
/// buildTaggedErrorClass builds: class ErrorN extends Data.TaggedError("ErrorN")<{ cause: unknown }> {}
pub(super) fn build_tagged_error_class(
    tracker: &Tracker,
    data_module_name: &str,
    error_name: &str,
    is_exported: bool,
) -> Node {
    let f = tracker.node_factory();

    // Data.TaggedError("ErrorN")
    let data_id = f.new_identifier(data_module_name);
    let tagged_error_access = f.new_property_access_expression(
        data_id,
        Node::NIL,
        f.new_identifier("TaggedError"),
        NodeFlags::NONE,
    );
    let tagged_error_call = f.new_call_expression(
        tagged_error_access,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&[f.new_string_literal(error_name, TokenFlags::NONE)]),
        NodeFlags::NONE,
    );

    // <{ cause: unknown }>
    let cause_prop_sig = f.new_property_signature_declaration(
        ModifierList::NIL, // modifiers
        f.new_identifier("cause"),
        Node::NIL, // postfixToken
        f.new_keyword_type_node(SyntaxKind::UnknownKeyword),
        Node::NIL, // initializer
    );
    let type_literal = f.new_type_literal_node(f.new_node_list(&[cause_prop_sig]));

    // Data.TaggedError("ErrorN")<{ cause: unknown }>
    let expr_with_type_args =
        f.new_expression_with_type_arguments(tagged_error_call, f.new_node_list(&[type_literal]));

    // extends clause
    let heritage_clause = f.new_heritage_clause(
        SyntaxKind::ExtendsKeyword,
        f.new_node_list(&[expr_with_type_args]),
    );

    // Modifiers (export if needed)
    let mut modifiers = ModifierList::NIL;
    if is_exported {
        modifiers = f.new_modifier_list(&[f.new_modifier(SyntaxKind::ExportKeyword)]);
    }

    // class ErrorN extends Data.TaggedError("ErrorN")<{ cause: unknown }> {}
    f.new_class_declaration(
        modifiers,
        f.new_identifier(error_name),
        NodeList::NIL, // typeParameters
        f.new_node_list(&[heritage_clause]),
        f.new_node_list(&[]), // empty members
    )
}
