//! Port of Effect-TS/tsgo `internal/rules/effect_fn_iife.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// EffectFnIife detects Effect.fn or Effect.fnUntraced calls that are immediately invoked (IIFE pattern).
pub static EFFECT_FN_IIFE: Rule = Rule {
    name: "effectFnIife",
    group: "antipattern",
    description: "Effect.fn or Effect.fnUntraced is called as an IIFE; use Effect.gen instead",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377011],
    run: run_effect_fn_iife,
};

fn run_effect_fn_iife(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_effect_fn_iife(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        let result = &m.result;
        let mut effect_module_name = "Effect".to_string();
        if result.effect_module.is_some() && result.effect_module.kind() == SyntaxKind::Identifier {
            effect_module_name = get_text_of_node(result.effect_module);
        }
        let mut with_span_hint = String::new();
        if result.trace_expression.is_some() {
            let text = source_file_text(ctx.source_file);
            let trace_text = &text
                [result.trace_expression.pos() as usize..result.trace_expression.end() as usize];
            with_span_hint = format!(
                " with Effect.withSpan({trace_text}) piped in the end to maintain tracing spans"
            );
        }
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::X_0_1_returns_a_reusable_function_that_can_take_arguments_but_it_is_invoked_immediately_here_Effect_gen_represents_the_immediate_use_form_for_this_pattern_2_effect_effectFnIife,
            Vec::new(),
            vec![effect_module_name, result.variant.clone(), with_span_hint],
        ));
    }
    diags
}

// EffectFnIifeMatch holds the parsed result needed by both the diagnostic rule
// and the quick-fix for the effectFnIife pattern.
#[derive(Clone, Debug)]
pub struct EffectFnIifeMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub result: Rc<EffectFnIifeResult>,
}

#[derive(Clone, Debug)]
pub struct EffectFnIifeResult {
    pub outer_call: Node,
    pub inner_call: Node,
    pub effect_module: Node,
    pub variant: String,
    pub generator_function: Node,
    pub pipe_arguments: Vec<Node>,
    pub trace_expression: Node,
}

// AnalyzeEffectFnIife finds all Effect.fn or Effect.fnUntraced calls that are
// immediately invoked (IIFE pattern) in the given source file.
pub fn analyze_effect_fn_iife(tp: &mut TypeParser<'_>, sf: Node) -> Vec<EffectFnIifeMatch> {
    let mut matches = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<EffectFnIifeMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if let Some(result) = parse_effect_fn_iife(tp, n) {
            matches.push(EffectFnIifeMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, result.outer_call),
                result,
            });
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);

    matches
}

fn parse_effect_fn_iife(tp: &mut TypeParser<'_>, node: Node) -> Option<Rc<EffectFnIifeResult>> {
    if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
        return None;
    }

    let outer_call = node;
    if outer_call.expression().is_nil() {
        return None;
    }

    let inner_node = outer_call.expression();
    if inner_node.kind() != SyntaxKind::CallExpression {
        return None;
    }

    let inner_call = inner_node;

    if let Some(result) = tp.effect_fn_call(inner_node) {
        return Some(Rc::new(EffectFnIifeResult {
            outer_call,
            inner_call,
            effect_module: result.effect_module,
            variant: result.variant.as_str().to_string(),
            generator_function: result.generator_function(),
            pipe_arguments: result.pipe_arguments.clone(),
            trace_expression: result.trace_expression,
        }));
    }

    None
}
