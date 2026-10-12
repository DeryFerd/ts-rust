//! Port of Effect-TS/tsgo `internal/fixables/effect_fn_opportunity.go`.

use rustc_hash::FxHashSet;

use crate::astnav::get_token_at_position;
use crate::effect::etscore::{
    EFFECT_FN_INFERRED_SPAN, EFFECT_FN_NO_SPAN, EFFECT_FN_SPAN, EFFECT_FN_SUGGESTED_SPAN,
    EFFECT_FN_UNTRACED,
};
use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::rules::effect_fn_opportunity::analyze_effect_fn_opportunity;
use crate::effect::typeparser::{
    EffectFnOpportunityResult, find_effect_module_identifier, get_function_like_body,
    get_function_like_parameters, get_function_like_type_parameters,
};
use crate::frontend::scanner::new_scanner;
use crate::gostd::strconv;
use crate::ls::CodeAction;
use crate::ls::utilities::{go_check_slice_bounds, go_text_slice};
use crate::lsp::lsproto;
use crate::prelude::*;
use crate::scanner_util::{get_text_of_node, get_token_pos_of_node, skip_trivia};

// Go: fixables/effect_fn_opportunity.go:21 EffectFnOpportunityFix
pub static EFFECT_FN_OPPORTUNITY_FIX: Fixable = Fixable {
    name: "effectFnOpportunity",
    description: "Convert to Effect.fn",
    // Go: tsdiag.This_expression_can_be_rewritten_in_the_reusable_function_form_0_effect_effectFnOpportunity
    error_codes: &[377047],
    fix_ids: &[
        "effectFnOpportunity_toEffectFnWithSpan",
        "effectFnOpportunity_toEffectFnUntraced",
        "effectFnOpportunity_toEffectFnNoSpan",
        "effectFnOpportunity_toEffectFnSpanInferred",
        "effectFnOpportunity_toEffectFnSpanSuggested",
    ],
    run: run_effect_fn_opportunity_fix,
};

// Go: fixables/effect_fn_opportunity.go:35 runEffectFnOpportunityFix
fn run_effect_fn_opportunity_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_effect_fn_opportunity(ctx.tp, sf);

    let Some(result) = matches
        .into_iter()
        .find(|m| m.location.intersects(ctx.span) || ctx.span.contained_by(m.location))
        .map(|m| m.result)
    else {
        return Vec::new();
    };
    let ctx: &FixableContext<'_, '_> = ctx;
    let effect_config = ctx.options;
    let is_func_decl = result.target_node.kind() == SyntaxKind::FunctionDeclaration;

    let mut actions = Vec::new();

    // Fix 1: toEffectFnWithSpan - available when explicit withSpan expression exists
    if effect_config.effect_fn_includes(EFFECT_FN_SPAN)
        && result.explicit_trace_expression.is_some()
    {
        // Remove withSpan from pipe args (it's the last one)
        let mut pipe_args: &[Node] = &result.pipe_arguments;
        if let Some((_, init)) = pipe_args.split_last() {
            pipe_args = init;
        }
        if let Some(action) = ctx.new_fix_action(
            "Convert to Effect.fn (with span from withSpan)".to_string(),
            |tracker| {
                let trace = get_text_of_node(result.explicit_trace_expression);
                effect_fn_build_replacement(
                    ctx,
                    tracker,
                    sf,
                    &result,
                    "fn",
                    &trace,
                    pipe_args,
                    is_func_decl,
                );
            },
        ) {
            actions.push(action);
        }
    }

    // Fix 2: toEffectFnUntraced - available when gen opportunity (generator function exists)
    if effect_config.effect_fn_includes(EFFECT_FN_UNTRACED) && result.generator_function.is_some() {
        if let Some(action) =
            ctx.new_fix_action("Convert to Effect.fnUntraced".to_string(), |tracker| {
                effect_fn_build_replacement(
                    ctx,
                    tracker,
                    sf,
                    &result,
                    "fnUntraced",
                    "",
                    &result.pipe_arguments,
                    is_func_decl,
                );
            })
        {
            actions.push(action);
        }
    }

    // Fix 3: toEffectFnNoSpan - available when no-span variant is enabled
    if effect_config.effect_fn_includes(EFFECT_FN_NO_SPAN) {
        if let Some(action) =
            ctx.new_fix_action("Convert to Effect.fn (no span)".to_string(), |tracker| {
                effect_fn_build_replacement(
                    ctx,
                    tracker,
                    sf,
                    &result,
                    "fn",
                    "",
                    &result.pipe_arguments,
                    is_func_decl,
                );
            })
        {
            actions.push(action);
        }
    }

    // Fix 4: toEffectFnSpanInferred - available when no explicit withSpan and inferred trace name exists
    if effect_config.effect_fn_includes(EFFECT_FN_INFERRED_SPAN)
        && result.explicit_trace_expression.is_nil()
        && !result.inferred_trace_name.is_empty()
    {
        if let Some(action) = ctx.new_fix_action(
            format!("Convert to Effect.fn(\"{}\")", result.inferred_trace_name),
            |tracker| {
                let trace = strconv::quote(&result.inferred_trace_name);
                effect_fn_build_replacement(
                    ctx,
                    tracker,
                    sf,
                    &result,
                    "fn",
                    &trace,
                    &result.pipe_arguments,
                    is_func_decl,
                );
            },
        ) {
            actions.push(action);
        }
    }

    // Fix 5: toEffectFnSpanSuggested - available when no explicit withSpan, has suggested trace name,
    // and (inferred-span is not enabled OR suggested name differs from inferred name)
    if effect_config.effect_fn_includes(EFFECT_FN_SUGGESTED_SPAN)
        && result.explicit_trace_expression.is_nil()
        && !result.suggested_trace_name.is_empty()
        && (!effect_config.effect_fn_includes(EFFECT_FN_INFERRED_SPAN)
            || result.suggested_trace_name != result.inferred_trace_name)
    {
        if let Some(action) = ctx.new_fix_action(
            format!("Convert to Effect.fn(\"{}\")", result.suggested_trace_name),
            |tracker| {
                let trace = strconv::quote(&result.suggested_trace_name);
                effect_fn_build_replacement(
                    ctx,
                    tracker,
                    sf,
                    &result,
                    "fn",
                    &trace,
                    &result.pipe_arguments,
                    is_func_decl,
                );
            },
        ) {
            actions.push(action);
        }
    }

    actions
}

// Go: fixables/effect_fn_opportunity.go:136 effectFnBuildReplacement
/// effectFnBuildReplacement edits around the original body rather than printing a
/// cloned AST. The body and all surrounding declarations/properties retain their
/// comments, literal spelling, whitespace, and semicolon style.
#[allow(clippy::too_many_arguments)]
fn effect_fn_build_replacement(
    ctx: &FixableContext<'_, '_>,
    tracker: &mut Tracker,
    sf: Node,
    result: &EffectFnOpportunityResult,
    variant: &str,
    trace: &str,
    pipe_args: &[Node],
    is_func_decl: bool,
) {
    let target = result.target_node;
    let mut body = get_function_like_body(target);
    if result.has_gen_body && result.generator_function.is_some() {
        body = result.generator_function.body();
    }
    if body.is_nil() {
        return;
    }

    let file_text = source_file_text(sf);
    let text: &str = &file_text;
    // Go `text[a:b]` slices bytes: a bound inside a char keeps the cut bytes
    // (`go_text_slice`), and a bound out of range panics with Go's text.
    let slice = |a: i32, b: i32| go_text_slice(text, a, b);
    let start = get_token_pos_of_node(target, sf, false);
    let body_start = get_token_pos_of_node(body, sf, false);
    let mut module = find_effect_module_identifier(sf);
    if result.effect_module.is_some() {
        module = get_text_of_node(result.effect_module);
    }
    let mut prefix = format!("{module}.{variant}");
    if !trace.is_empty() {
        prefix += &format!("({trace})");
    }
    prefix.push('(');
    let mut suffix = String::new();

    if !result.has_gen_body && target.kind() == SyntaxKind::FunctionExpression {
        // Keep the original function expression's signature verbatim.
        prefix += &slice(start, body_start);
    } else {
        prefix += "function";
        if result.has_gen_body {
            prefix.push('*');
        }
        let signature = effect_fn_signature_range(sf, target);
        // `signature.end()` is one byte past the closing parenthesis (or the
        // `=` of a bare parameter's `=>`), an ASCII byte in a parsed tree, so
        // the cut bytes of `slice` stay a Go-only case here.
        let mut signature_text = slice(signature.pos(), signature.end()).into_owned();
        // Go `signatureText[0]` on an empty text panics.
        let Some(&first) = signature_text.as_bytes().first() else {
            crate::core::go_panic(
                "runtime error: index out of range [0] with length 0".to_string(),
            );
        };
        if first != b'(' && first != b'<' {
            signature_text = format!("({signature_text})");
        }
        let mut comment_start = start;
        if is_func_decl && target.modifiers().is_some() {
            comment_start = target.modifiers().end();
        }
        prefix += &effect_fn_comments(sf, comment_start, signature.pos(), Node::NIL);
        prefix += &signature_text;
        let comments = effect_fn_comments(sf, signature.end(), body_start, Node::NIL);
        if !comments.is_empty() {
            prefix += &comments;
        } else {
            prefix.push(' ');
        }
        if body.kind() != SyntaxKind::Block {
            prefix += "{ return ";
            suffix += " }";
        }
    }

    if is_func_decl {
        let decl = target;
        let mut declaration_prefix = String::new();
        let modifiers = decl.modifiers();
        if modifiers.is_some() {
            declaration_prefix = slice(start, modifiers.end()).into_owned() + " ";
        }
        prefix = declaration_prefix + "const " + &get_text_of_node(decl.name()) + " = " + &prefix;
    }

    let mut cursor = body.end();
    for &arg in pipe_args {
        // Include both leading and trailing trivia, including line comments before
        // the next comma/closing parenthesis. Never reprint the argument itself.
        let end = skip_trivia(text, arg.end());
        let start = get_token_pos_of_node(arg, sf, false);
        suffix.push(',');
        suffix += &effect_fn_comments(sf, cursor, arg.pos(), Node::NIL);
        suffix += &slice(arg.pos(), start);
        suffix += &effect_fn_pipe_argument_text(arg, &slice(start, arg.end()));
        suffix += &slice(arg.end(), end);
        cursor = end;
    }
    let moved_trace = if trace.is_empty() {
        Node::NIL
    } else {
        result.explicit_trace_expression
    };
    suffix += &effect_fn_comments(sf, cursor, target.end(), moved_trace);
    suffix.push(')');
    if is_func_decl {
        suffix.push(';');
    }

    tracker.replace_range_with_text(
        sf,
        lsproto::Range {
            start: ctx.byte_pos_to_lsp_position(start),
            end: ctx.byte_pos_to_lsp_position(body_start),
        },
        &prefix,
    );
    tracker.replace_range_with_text(
        sf,
        lsproto::Range {
            start: ctx.byte_pos_to_lsp_position(body.end()),
            end: ctx.byte_pos_to_lsp_position(target.end()),
        },
        &suffix,
    );
}

// Go: fixables/effect_fn_opportunity.go:243 effectFnPipeArgumentText
/// effectFnPipeArgumentText prevents Effect.fn's additional function arguments
/// from reaching a bare pipeable's optional parameters. Factory calls already
/// produce data-last pipeables and can be retained as written.
fn effect_fn_pipe_argument_text(arg: Node, text: &str) -> String {
    if skip_parentheses(arg).kind() == SyntaxKind::CallExpression {
        return text.to_string();
    }

    // Avoid capturing references such as _.ignore in the new arrow's scope.
    fn visit(node: Node, identifiers: &mut FxHashSet<&'static str>) -> bool {
        if node.kind() == SyntaxKind::Identifier {
            identifiers.insert(node.text());
        }
        node.for_each_child(|child| visit(child, identifiers));
        false
    }
    let mut identifiers = FxHashSet::default();
    visit(arg, &mut identifiers);
    let mut parameter = "_".to_string();
    let mut suffix = 1;
    while identifiers.contains(parameter.as_str()) {
        parameter = format!("_{suffix}");
        suffix += 1;
    }

    let text = match arg.kind() {
        // These expressions can be used directly as a callee.
        SyntaxKind::Identifier
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::ParenthesizedExpression => text.to_string(),
        _ => format!("({text})"),
    };
    format!("{parameter} => {text}({parameter})")
}

// Go: fixables/effect_fn_opportunity.go:276 effectFnSignatureRange
/// effectFnSignatureRange locates the complete parameter/type-parameter spelling,
/// including comments and defaults. Bare arrow parameters need parentheses when
/// moved to a function expression.
fn effect_fn_signature_range(sf: Node, target: Node) -> TextRange {
    let file_text = source_file_text(sf);
    let text: &str = &file_text;
    let params = get_function_like_parameters(target);
    let (mut start, mut end) = (params.pos(), params.end());
    if start > 0 && text.as_bytes()[(start - 1) as usize] == b'(' {
        start -= 1;
        end = skip_trivia(text, end) + 1; // closing parenthesis
    } else {
        return TextRange::new(skip_trivia(text, start), end);
    }
    let type_params = get_function_like_type_parameters(target);
    if type_params.is_some() {
        start = type_params.pos() - 1; // opening angle bracket
    }
    TextRange::new(start, end)
}

// Go: fixables/effect_fn_opportunity.go:294 effectFnComments
/// effectFnComments retains comments from discarded wrapper syntax, such as the
/// outer return statement. Arguments and the function body are copied separately.
fn effect_fn_comments(sf: Node, start: i32, end: i32, moved: Node) -> String {
    let file_text = source_file_text(sf);
    go_check_slice_bounds(&file_text, start, end);
    if start == end {
        return String::new();
    }
    // Go slices bytes, so `start` can cut a char (the `+ 1` of
    // `effect_fn_signature_range`; the callers' ends are node bounds). The
    // text then starts with a byte that is not UTF-8, and Go's scanner reads
    // all of it as one NonTextFileMarkerTrivia token ("File appears to be
    // binary"), so the loop below adds nothing, unless `start` is in `moved`:
    // then it goes on from the end of `moved`, a char boundary.
    if !file_text.is_char_boundary(start as usize) {
        if moved.is_some()
            && start >= get_token_pos_of_node(moved, sf, false)
            && start < moved.end()
        {
            return effect_fn_comments(sf, moved.end().min(end), end, moved);
        }
        // Go's `default` case on that token: the token call, which can
        // panic as Go's does. Its token does not change the result, because
        // the next scan is EndOfFile.
        get_token_at_position(sf, start);
        return String::new();
    }
    // PORT: Go `sf.Text()[start:end]`. `start` is a char boundary here, and
    // each caller's `end` is a node or token bound (`signature.pos()`,
    // `body_start`, `arg.pos()`, `target.end()`), so this byte slice is Go's
    // slice. A cut `end` would need the port form of `go_text_slice`, whose
    // escape units are longer than Go's bytes and would move the scanner
    // offsets below away from the file positions.
    let text = &file_text[start as usize..end as usize];
    let slice = |a: i32, b: i32| &text[a as usize..b as usize];
    let mut s = new_scanner();
    s.set_skip_trivia(false);
    s.set_text(text);
    let mut comments = String::new();
    let mut trivia_start: i32 = 0;
    let mut has_comment = false;
    let mut token = s.scan();
    while token != SyntaxKind::EndOfFile {
        if moved.is_some()
            && start + s.token_start() >= get_token_pos_of_node(moved, sf, false)
            && start + s.token_start() < moved.end()
        {
            if has_comment {
                comments += slice(trivia_start, s.token_start());
            }
            trivia_start = moved.end().min(end) - start;
            s.reset_pos(trivia_start);
            has_comment = false;
            token = s.scan();
            continue;
        }
        match token {
            SyntaxKind::SingleLineCommentTrivia | SyntaxKind::MultiLineCommentTrivia => {
                comments += slice(trivia_start, s.token_end());
                trivia_start = s.token_end();
                has_comment = true;
            }
            SyntaxKind::WhitespaceTrivia | SyntaxKind::NewLineTrivia => {
                // Whitespace is retained with the adjacent comment.
            }
            _ => {
                if has_comment {
                    comments += slice(trivia_start, s.token_start());
                }
                // Use the parsed token's extent for contextual tokens (regexes and
                // template tails), so comment-like text inside literals is not moved.
                let original = get_token_at_position(sf, start + s.token_start());
                trivia_start = s.token_end();
                if original.end() > start + trivia_start {
                    trivia_start = original.end().min(end) - start;
                    s.reset_pos(trivia_start);
                }
                has_comment = false;
            }
        }
        token = s.scan();
    }
    if has_comment {
        comments += &text[trivia_start as usize..];
    }
    comments
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
    use crate::scanner_util::{go_string_bytes, go_string_from_bytes};

    // Go slices the file text by bytes (effect_fn_opportunity.go:296
    // `sf.Text()[start:end]`), so a start inside a char is no panic: the
    // text starts with a byte that is not UTF-8, which Go's scanner reads
    // as one NonTextFileMarkerTrivia token to the end, and no comment is
    // kept. The answers are those of the Go function on the same texts
    // (effect-tsgo 0.51.1, followups43 go-test.log).
    #[test]
    fn comments_from_a_start_inside_a_char_are_empty_as_go() {
        let cases = [
            (
                "const f = (a: string) => /* \u{e9} */ 1 // \u{fc}\n",
                "\u{e9}",
                1,
            ),
            (
                "const f = (a: string) => /* \u{e9} */ 1 // \u{fc}\n",
                "\u{fc}",
                1,
            ),
            ("const f\u{e9} = 1 /* c */ + 2\n", "\u{e9}", 1),
            ("const s = \"\u{4e2d}\" /* c */ + 2\n", "\u{4e2d}", 1),
            ("const s = \"\u{4e2d}\" /* c */ + 2\n", "\u{4e2d}", 2),
            ("const g = 1 /* \u{4e2d} */ + 2\n", "\u{4e2d}", 2),
        ];
        for (text, at, offset) in cases {
            let opts = SourceFileParseOptions {
                file_name: "/t.ts".to_string(),
                ..Default::default()
            };
            let sf = parse_source_file(&opts, text, ScriptKind::TS).root;
            let start = (text.find(at).expect("the char") + offset) as i32;
            assert_eq!(
                effect_fn_comments(sf, start, text.len() as i32, Node::NIL),
                "",
                "{text:?} from {start}"
            );
        }
        // The signature slice keeps the cut byte, as Go's `text[a:b]`.
        let text = "const f = (a) => 1 // \u{e9}\n";
        let cut = go_text_slice(text, 0, text.find('\u{e9}').expect("the char") as i32 + 1);
        let mut want = b"const f = (a) => 1 // ".to_vec();
        want.push(0xc3);
        assert_eq!(go_string_bytes(&cut).into_owned(), want);
        assert_eq!(cut, go_string_from_bytes(want));
    }
}
