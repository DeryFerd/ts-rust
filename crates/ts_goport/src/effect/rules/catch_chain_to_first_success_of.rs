//! Port of Effect-TS/tsgo `internal/rules/catch_chain_to_first_success_of.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// CatchChainToFirstSuccessOf suggests firstSuccessOf for equivalent catch fallback chains.
// Go: rules/catch_chain_to_first_success_of.go CatchChainToFirstSuccessOf
pub static CATCH_CHAIN_TO_FIRST_SUCCESS_OF: Rule = Rule {
    name: "catchChainToFirstSuccessOf",
    group: "style",
    description: "Suggests Effect.firstSuccessOf for consecutive error-independent Effect.catch fallbacks when the error type is preserved",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377107],
    run: run_catch_chain_to_first_success_of,
};

fn run_catch_chain_to_first_success_of(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_chain_to_first_success_of(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Chained_Effect_catch_fallbacks_that_ignore_the_error_can_be_written_with_Effect_firstSuccessOf_Wrap_each_lazy_fallback_with_Effect_suspend_to_preserve_when_it_is_constructed_effect_catchChainToFirstSuccessOf,
            Vec::new(),
            Vec::new(),
        ));
    }
    diagnostics
}

// Go: rules/catch_chain_to_first_success_of.go CatchChainToFirstSuccessOfMatch
#[derive(Clone, Copy)]
pub struct CatchChainToFirstSuccessOfMatch {
    pub source_file: Node,
    pub location: TextRange,
}

// Go: rules/catch_chain_to_first_success_of.go catchChainToFirstSuccessOfCandidate
// PORT: Go keeps a pointer into the flow's transformations; the port keeps a copy.
#[derive(Clone)]
pub struct CatchChainToFirstSuccessOfCandidate {
    pub transformation: PipingFlowTransformation,
    pub error_type: TypeId,
}

/// AnalyzeCatchChainToFirstSuccessOf finds consecutive zero-argument catch fallbacks.
// Go: rules/catch_chain_to_first_success_of.go AnalyzeCatchChainToFirstSuccessOf
pub fn analyze_catch_chain_to_first_success_of(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<CatchChainToFirstSuccessOfMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    // PORT: Go's `flush` closure.
    fn flush(
        c: &mut Checker,
        sf: Node,
        matches: &mut Vec<CatchChainToFirstSuccessOfMatch>,
        chain: &mut Vec<CatchChainToFirstSuccessOfCandidate>,
        initial_error: &mut TypeId,
        output_error: &mut TypeId,
    ) {
        if catch_chain_preserves_first_success_of_error(c, *initial_error, *output_error, chain) {
            let outermost = &chain[chain.len() - 1].transformation;
            matches.push(CatchChainToFirstSuccessOfMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, outermost.callee),
            });
        }
        chain.clear();
        *initial_error = TypeId::NIL;
        *output_error = TypeId::NIL;
    }

    let mut matches = Vec::new();
    for flow in tp.piping_flows(sf, true).iter() {
        let mut chain: Vec<CatchChainToFirstSuccessOfCandidate> = Vec::new();
        let mut initial_error = TypeId::NIL;
        let mut output_error = TypeId::NIL;

        for i in 0..flow.transformations.len() {
            let transformation = &flow.transformations[i];
            let (candidate, ok) =
                analyze_catch_chain_to_first_success_of_candidate(tp, transformation);
            if !ok {
                flush(
                    tp.checker,
                    sf,
                    &mut matches,
                    &mut chain,
                    &mut initial_error,
                    &mut output_error,
                );
                continue;
            }

            if chain.is_empty() {
                let mut input_type = flow.subject.out_type;
                if i > 0 {
                    input_type = flow.transformations[i - 1].out_type;
                }
                let input_effect = tp.strict_effect_type(input_type);
                let Some(input_effect) = input_effect.filter(|e| e.e.is_some()) else {
                    flush(
                        tp.checker,
                        sf,
                        &mut matches,
                        &mut chain,
                        &mut initial_error,
                        &mut output_error,
                    );
                    continue;
                };
                initial_error = input_effect.e;
            }

            let output_effect = tp.strict_effect_type(transformation.out_type);
            let Some(output_effect) = output_effect.filter(|e| e.e.is_some()) else {
                flush(
                    tp.checker,
                    sf,
                    &mut matches,
                    &mut chain,
                    &mut initial_error,
                    &mut output_error,
                );
                continue;
            };
            chain.push(candidate.expect("ok candidate"));
            output_error = output_effect.e;
        }

        flush(
            tp.checker,
            sf,
            &mut matches,
            &mut chain,
            &mut initial_error,
            &mut output_error,
        );
    }

    matches
}

// Go: rules/catch_chain_to_first_success_of.go analyzeCatchChainToFirstSuccessOfCandidate
// PORT: Go returns a zero candidate with `false`; the port returns `None` there.
fn analyze_catch_chain_to_first_success_of_candidate(
    tp: &mut TypeParser<'_>,
    transformation: &PipingFlowTransformation,
) -> (Option<CatchChainToFirstSuccessOfCandidate>, bool) {
    if transformation.callee.is_nil()
        || !tp.is_node_reference_to_effect_module_api(transformation.callee, "catch")
        || transformation.args.len() != 1
    {
        return (None, false);
    }

    let lazy = parse_lazy_expression(transformation.args[0], LazyExpressionFlags::THUNK);
    if lazy.as_ref().is_none_or(|lazy| lazy.expression.is_nil()) {
        return (None, false);
    }

    let handler_type = tp.get_type_at_location(transformation.args[0]);
    if handler_type.is_nil() {
        return (None, false);
    }
    let signatures = tp
        .checker
        .get_signatures_of_type_exported(handler_type, SignatureKind::CALL);
    if signatures.len() != 1 {
        return (None, false);
    }

    let return_type = tp
        .checker
        .get_return_type_of_signature_exported(signatures[0]);
    let fallback_type = tp.strict_effect_type(return_type);
    let Some(fallback_type) = fallback_type.filter(|e| e.e.is_some()) else {
        return (None, false);
    };

    (
        Some(CatchChainToFirstSuccessOfCandidate {
            transformation: transformation.clone(),
            error_type: fallback_type.e,
        }),
        true,
    )
}

// Go: rules/catch_chain_to_first_success_of.go catchChainPreservesFirstSuccessOfError
fn catch_chain_preserves_first_success_of_error(
    c: &mut Checker,
    initial_error: TypeId,
    output_error: TypeId,
    chain: &[CatchChainToFirstSuccessOfCandidate],
) -> bool {
    if initial_error.is_nil()
        || output_error.is_nil()
        || chain.len() < 2
        || c.ty(initial_error).flags.intersects(TypeFlags::ANY)
        || c.ty(output_error).flags.intersects(TypeFlags::ANY)
    {
        return false;
    }

    let final_error = chain[chain.len() - 1].error_type;
    // catch retains only the final fallback error, while firstSuccessOf unions all
    // candidate errors. The union is unchanged only when each earlier error fits.
    if final_error.is_nil()
        || c.ty(final_error).flags.intersects(TypeFlags::ANY)
        || !c.is_type_assignable_to_exported(final_error, output_error)
        || !c.is_type_assignable_to_exported(output_error, final_error)
        || !c.is_type_assignable_to_exported(initial_error, output_error)
    {
        return false;
    }

    for candidate in &chain[..chain.len() - 1] {
        if candidate.error_type.is_nil()
            || c.ty(candidate.error_type).flags.intersects(TypeFlags::ANY)
            || !c.is_type_assignable_to_exported(candidate.error_type, output_error)
        {
            return false;
        }
    }
    true
}
