// Go: internal/rules/run_effect_inside_effect.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// runEffectApis lists the Effect module run APIs that should not be called inside Effect generators.
static RUN_EFFECT_APIS: &[&str] = &["runSync", "runPromise", "runFork", "runCallback"];

/// RunEffectInsideEffect detects Effect.runSync, Effect.runPromise, Effect.runFork, and
/// Effect.runCallback call expressions inside Effect generator contexts and suggests alternatives.
pub static RUN_EFFECT_INSIDE_EFFECT: Rule = Rule {
    name: "runEffectInsideEffect",
    group: "antipattern",
    description: "Suggests using Runtime or Effect.run*With methods instead of Effect.run* inside Effect contexts",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377024, 377025, 377074],
    run: run_run_effect_inside_effect,
};

fn run_run_effect_inside_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let supported_effect = ctx.tp.supported_effect_version();

    let matches = analyze_run_effect_inside_effect(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        let callee_text =
            get_source_text_of_node_from_source_file(m.source_file, m.callee_node, false);
        if m.is_nested_scope {
            if supported_effect == EffectMajorVersion::V4 {
                diags.push(ctx.new_diagnostic(
                    m.source_file,
                    m.location,
                    diag::X_0_is_called_inside_an_Effect_with_a_separate_services_invocation_In_this_context_child_Effects_run_with_the_surrounding_services_which_can_be_accessed_through_Effect_context_and_Effect_1_With_effect_runEffectInsideEffect,
                    Vec::new(),
                    vec![callee_text, m.method_name.clone()],
                ));
            } else {
                diags.push(ctx.new_diagnostic(
                    m.source_file,
                    m.location,
                    diag::X_0_is_called_inside_an_Effect_with_a_separate_runtime_invocation_In_this_context_run_child_Effects_with_the_surrounding_runtime_which_can_be_accessed_through_Effect_runtime_and_Runtime_1_effect_runEffectInsideEffect,
                    Vec::new(),
                    vec![callee_text, m.method_name.clone()],
                ));
            }
        } else {
            diags.push(ctx.new_diagnostic(
                m.source_file,
                m.location,
                diag::X_0_is_called_inside_an_existing_Effect_context_Here_the_inner_Effect_can_be_used_directly_effect_runEffectInsideEffect,
                Vec::new(),
                vec![callee_text],
            ));
        }
    }
    diags
}

/// RunEffectInsideEffectMatch holds the diagnostic and AST nodes needed by both the
/// diagnostic rule and the quick-fix for the runEffectInsideEffect pattern.
#[derive(Clone, Debug, Default)]
pub struct RunEffectInsideEffectMatch {
    /// The source file where this match was found
    pub source_file: Node,
    /// Pre-computed error range (on the callee expression)
    pub location: TextRange,
    /// The full call expression node (e.g., Effect.runPromise(check))
    pub call_node: Node,
    /// The callee expression (e.g., Effect.runPromise)
    pub callee_node: Node,
    /// The matched run API name (e.g., "runPromise")
    pub method_name: String,
    /// True when call is in a nested scope rather than direct generator scope
    pub is_nested_scope: bool,
    /// The enclosing Effect generator function
    pub generator_function: Node,
}

// Go: rules/run_effect_inside_effect.go AnalyzeRunEffectInsideEffect
/// AnalyzeRunEffectInsideEffect finds all Effect.run* calls inside Effect generators,
/// returning matches with structured data for both diagnostics and quick-fixes.
pub fn analyze_run_effect_inside_effect(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<RunEffectInsideEffectMatch> {
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<RunEffectInsideEffectMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression {
            if let (m, true) = analyze_run_effect_inside_effect_node(tp, sf, n) {
                matches.push(m);
            }
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    let mut matches = Vec::new();
    walk(tp, sf, &mut matches, sf);
    matches
}

// Go: rules/run_effect_inside_effect.go analyzeRunEffectInsideEffectNode
/// analyzeRunEffectInsideEffectNode checks a single call expression for Effect.run* inside an Effect generator.
fn analyze_run_effect_inside_effect_node(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> (RunEffectInsideEffectMatch, bool) {
    if node.kind() != SyntaxKind::CallExpression {
        return (RunEffectInsideEffectMatch::default(), false);
    }
    let call = node;

    // Must have at least one argument (matching the TS reference: node.arguments.length === 0 => continue)
    if call.argument_list().is_nil() || call.arguments().is_empty() {
        return (RunEffectInsideEffectMatch::default(), false);
    }

    let callee = call.expression();

    // Check if the callee is one of the Effect.run* APIs
    let method_name = match_run_effect_api(tp, callee);
    if method_name.is_empty() {
        return (RunEffectInsideEffectMatch::default(), false);
    }

    let mut gen_fn = tp.get_effect_yield_generator_function(node);
    if gen_fn.is_nil() {
        let mut current = node.parent();
        while current.is_some() {
            if tp
                .get_effect_context_flags(current)
                .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
            {
                gen_fn = tp.get_effect_yield_generator_function(current);
                if gen_fn.is_some() {
                    break;
                }
            }
            current = current.parent();
        }
    }
    if gen_fn.is_nil() {
        return (RunEffectInsideEffectMatch::default(), false);
    }

    // Check that the generator body has at least one statement
    if gen_fn.body().is_nil() || gen_fn.body().kind() != SyntaxKind::Block {
        return (RunEffectInsideEffectMatch::default(), false);
    }
    let block = gen_fn.body();
    if block.statements().is_empty() {
        return (RunEffectInsideEffectMatch::default(), false);
    }

    let is_nested_scope = get_containing_function(node) != gen_fn;

    (
        RunEffectInsideEffectMatch {
            source_file: sf,
            location: get_error_range_for_node(sf, callee),
            call_node: node,
            callee_node: callee,
            method_name,
            is_nested_scope,
            generator_function: gen_fn,
        },
        true,
    )
}

// Go: rules/run_effect_inside_effect.go matchRunEffectApi
/// matchRunEffectApi checks if the node references one of the Effect.run* APIs and returns the method name.
/// Returns empty string if no match.
fn match_run_effect_api(tp: &mut TypeParser<'_>, node: Node) -> String {
    for name in RUN_EFFECT_APIS {
        if tp.is_node_reference_to_effect_module_api(node, name) {
            return (*name).to_string();
        }
    }
    String::new()
}
