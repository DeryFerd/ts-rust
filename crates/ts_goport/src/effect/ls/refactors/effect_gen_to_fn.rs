//! Port of Effect-TS/tsgo `internal/refactors/effect_gen_to_fn.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::async_await_to_gen::{
    clone_modifier_tokens, replace_expression_via_statement,
};
use crate::effect::ls::refactors::{clone_node_list, with_kind};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{
    EffectGenCallResult, TypeParser, get_function_like_body, get_function_like_name,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/effect_gen_to_fn.go:13 EffectGenToFn
pub static EFFECT_GEN_TO_FN: Refactor = Refactor {
    name: "effectGenToFn",
    description: "Convert to Effect.fn",
    kind: "rewrite.effect.effectGenToFn",
    run: run_effect_gen_to_fn,
};

// Go: refactors/effect_gen_to_fn.go:21 effectGenParsed
/// effectGenParsed holds the parsed components of a function returning Effect.gen.
struct EffectGenParsed {
    /// The function-like node (arrow, declaration, expression, method)
    func_node: Node,
    /// The parsed Effect.gen call
    gen_call: Rc<EffectGenCallResult>,
    /// Collected pipe arguments (from .pipe() or pipe() wrappers)
    pipe_args: Vec<Node>,
}

// Go: refactors/effect_gen_to_fn.go:27 runEffectGenToFn
fn run_effect_gen_to_fn(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain to find a function-like node returning Effect.gen
    let Some(parsed) = find_function_returning_effect_gen(ctx.tp, token) else {
        return Vec::new();
    };

    let fn_name = get_function_like_name(parsed.func_node);

    let description = if fn_name.is_empty() {
        "Convert to Effect.fn".to_string()
    } else {
        format!("Convert to Effect.fn(\"{fn_name}\")")
    };

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action(&description, |tracker| {
        let new_node = build_effect_gen_to_fn_replacement(tracker, &parsed, &fn_name);
        if new_node.is_nil() {
            return;
        }
        set_parent_in_children(new_node);

        match parsed.func_node.kind() {
            SyntaxKind::FunctionDeclaration | SyntaxKind::MethodDeclaration => {
                tracker.replace_node(sf, parsed.func_node, new_node, None);
            }
            _ => {
                replace_expression_via_statement(tracker, sf, parsed.func_node, new_node);
            }
        }
    });
    with_kind(action, "refactor.rewrite.effect.effectGenToFn")
}

// Go: refactors/effect_gen_to_fn.go:76 findFunctionReturningEffectGen
/// findFunctionReturningEffectGen walks from the token up the ancestor chain to find
/// a function-like node whose body directly returns an Effect.gen call, optionally
/// wrapped in pipe/pipeable chains.
// PORT: Go also passes the checker, which no callee reads; the checker is
// `tp.checker`.
fn find_function_returning_effect_gen(
    tp: &mut TypeParser<'_>,
    token: Node,
) -> Option<EffectGenParsed> {
    let mut node = token;
    while node.is_some() {
        match node.kind() {
            SyntaxKind::ArrowFunction
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration => {
                // Hit a function boundary without finding Effect.gen — stop
                return parse_function_returning_effect_gen(tp, node);
            }
            SyntaxKind::FunctionExpression => {
                // Don't match on generator functions (those are inside Effect.gen already)
                if node.asterisk_token().is_nil() {
                    return parse_function_returning_effect_gen(tp, node);
                }
            }
            _ => {}
        }
        node = node.parent();
    }
    None
}

// Go: refactors/effect_gen_to_fn.go:104 parseFunctionReturningEffectGen
/// parseFunctionReturningEffectGen extracts the Effect.gen call and any pipe args
/// from a function-like node. Returns nil if the function doesn't match.
fn parse_function_returning_effect_gen(
    tp: &mut TypeParser<'_>,
    node: Node,
) -> Option<EffectGenParsed> {
    let body = get_function_like_body(node);
    if body.is_nil() {
        return None;
    }

    // Skip through { return <expr> } blocks to get the actual expression
    let mut subject = skip_return_block(body);

    // Peel off pipe wrappers, collecting args
    let mut pipe_args: Vec<Node> = Vec::new();
    while let Some(pipe_result) = tp.parse_pipe_call(subject) {
        // Prepend args (inner pipes go first)
        let mut args = pipe_result.args.clone();
        args.append(&mut pipe_args);
        pipe_args = args;
        subject = pipe_result.subject;
    }

    // Check if the core expression is Effect.gen(function*() { ... })
    let gen_call = tp.effect_gen_call(subject)?;

    Some(EffectGenParsed {
        func_node: node,
        gen_call,
        pipe_args,
    })
}

// Go: refactors/effect_gen_to_fn.go:139 skipReturnBlock
/// skipReturnBlock unwraps a block containing a single return statement to get the expression.
fn skip_return_block(node: Node) -> Node {
    if node.kind() != SyntaxKind::Block {
        return node;
    }
    let statements = node.statements();
    if statements.len() != 1 {
        return node;
    }
    let stmt = statements.get(0);
    if stmt.kind() != SyntaxKind::ReturnStatement {
        return node;
    }
    if stmt.expression().is_nil() {
        return node;
    }
    stmt.expression()
}

// Go: refactors/effect_gen_to_fn.go:159 buildEffectGenToFnReplacement
/// buildEffectGenToFnReplacement builds the replacement node for the effectGenToFn refactor.
fn build_effect_gen_to_fn_replacement(
    tracker: &Tracker,
    parsed: &EffectGenParsed,
    fn_name: &str,
) -> Node {
    let node = parsed.func_node;
    let gen_call = &parsed.gen_call;
    let f = tracker.node_factory();

    // Get the generator body
    let mut block_body = Node::NIL;
    if gen_call.body.is_some() {
        let body = gen_call.body;
        if body.kind() == SyntaxKind::Block {
            block_body = f.deep_clone_node(body);
        } else {
            // Expression body: wrap in { return <expr> }
            let cloned_expr = f.deep_clone_node(body);
            let return_stmt = f.new_return_statement(cloned_expr);
            block_body = f.new_block(f.new_node_list(&[return_stmt]), true);
        }
    }
    if block_body.is_nil() {
        return Node::NIL;
    }

    // Get type parameters and parameters from the outer function
    // PORT: Go has one case per kind with the same fields.
    let (type_params, params) = match node.kind() {
        SyntaxKind::ArrowFunction
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::MethodDeclaration => (
            clone_node_list(tracker, node.type_parameter_list()),
            clone_node_list(tracker, node.parameter_list()),
        ),
        _ => (NodeList::NIL, NodeList::NIL),
    };

    // Build function*(params) { body }
    let gen_fn = f.new_function_expression(
        ModifierList::NIL,                      // modifiers
        f.new_token(SyntaxKind::AsteriskToken), // asterisk (generator)
        Node::NIL,                              // name
        type_params,                            // typeParameters
        params,                                 // parameters
        Node::NIL,                              // returnType
        Node::NIL,                              // fullSignature
        block_body,
    );

    // Build Effect.fn or Effect.fn("name")
    // PORT: `EffectModule` is nil for a named import (`gen(function* ...)`).
    // Go then builds a property access with a nil expression, and the
    // printer dereferences it when `NewRefactorAction` gets the changes. The
    // codeAction request answers Go's internal error for that nil
    // dereference; the port panics here with the same value. Go prints no
    // signal line in an answer, so no fault address is needed.
    if gen_call.effect_module.is_nil() {
        crate::core::go_nil_dereference();
    }
    let effect_id = f.deep_clone_node(gen_call.effect_module);
    let fn_access = f.new_property_access_expression(
        effect_id,
        Node::NIL,
        f.new_identifier("fn"),
        NodeFlags::NONE,
    );

    let fn_call_expr = if !fn_name.is_empty() {
        // Effect.fn("name")
        f.new_call_expression(
            fn_access,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&[f.new_string_literal(fn_name, TokenFlags::NONE)]),
            NodeFlags::NONE,
        )
    } else {
        fn_access
    };

    // Build the arguments: [generatorFn, ...pipeArgs]
    let mut args = vec![gen_fn];
    for &pipe_arg in &parsed.pipe_args {
        args.push(f.deep_clone_node(pipe_arg));
    }

    // Effect.fn("name")(function*(params) { body }, ...pipeArgs)
    let effect_fn_call = f.new_call_expression(
        fn_call_expr,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&args),
        NodeFlags::NONE,
    );

    // Wrap in appropriate declaration
    build_effect_gen_to_fn_declaration(tracker, node, effect_fn_call)
}

// Go: refactors/effect_gen_to_fn.go:251 buildEffectGenToFnDeclaration
/// buildEffectGenToFnDeclaration wraps the Effect.fn call in the appropriate declaration.
fn build_effect_gen_to_fn_declaration(tracker: &Tracker, node: Node, effect_fn_call: Node) -> Node {
    let f = tracker.node_factory();
    match node.kind() {
        SyntaxKind::FunctionDeclaration => {
            if node.name().is_nil() {
                return effect_fn_call;
            }

            // Collect modifiers
            let mods = clone_modifier_tokens(tracker, node.modifiers());

            // const name = Effect.fn("name")(...)
            let var_decl = f.new_variable_declaration(
                f.deep_clone_node(node.name()),
                Node::NIL, // exclamationToken
                Node::NIL, // type
                effect_fn_call,
            );
            let var_decl_list =
                f.new_variable_declaration_list(f.new_node_list(&[var_decl]), NodeFlags::CONST);
            f.new_variable_statement(mods, var_decl_list)
        }

        SyntaxKind::MethodDeclaration => {
            // Convert method to property declaration: name = Effect.fn("name")(...)
            let mods = clone_modifier_tokens(tracker, node.modifiers());
            f.new_property_declaration(
                mods,
                f.deep_clone_node(node.name()),
                Node::NIL, // postfixToken
                Node::NIL, // type
                effect_fn_call,
            )
        }

        // For arrow functions and function expressions, return the expression directly
        _ => effect_fn_call,
    }
}
