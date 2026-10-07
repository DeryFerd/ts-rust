//! Port of Effect-TS/tsgo `internal/rules/catch_die_to_or_die.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// CatchDieToOrDie suggests using Effect.orDie instead of a catch-all
/// handler that forwards the typed failure unchanged to Effect.die.
pub static CATCH_DIE_TO_OR_DIE: Rule = Rule {
    name: "catchDieToOrDie",
    group: "style",
    description: "Suggests using Effect.orDie instead of Effect.catch or Effect.catchAll with an identity-forwarding Effect.die handler",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377115],
    run: run_catch_die_to_or_die,
};

fn run_catch_die_to_or_die(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_die_to_or_die(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_orDie_expresses_escalating_every_typed_failure_into_a_defect_more_directly_than_Effect_0_with_an_identity_forwarding_Effect_die_handler_effect_catchDieToOrDie,
            Vec::new(),
            args![m.catch_method_name],
        ));
    }
    diagnostics
}

/// CatchDieToOrDieMatch holds the nodes needed by the diagnostic and fix.
pub struct CatchDieToOrDieMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub effect_module: Node,
    pub catch_method_name: String,
    pub has_type_arguments: bool,
}

/// AnalyzeCatchDieToOrDie finds Effect.catch/catchAll transformations whose
/// handler is Effect.die or forwards its sole argument unchanged to Effect.die.
// Go: rules/catch_die_to_or_die.go AnalyzeCatchDieToOrDie
pub fn analyze_catch_die_to_or_die(tp: &mut TypeParser<'_>, sf: Node) -> Vec<CatchDieToOrDieMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        let mut input_type = flow.subject.out_type;
        for transformation in &flow.transformations {
            let callee = transformation.callee;
            let args = &transformation.args;
            let (method_name, effect_module, ok) = catch_die_method(tp, callee);
            if ok && args.len() == 1 {
                let (handler, _, _) = tp.unwrap_identity_forwarder(args[0]);
                if tp.is_node_reference_to_effect_module_api(handler, "die") {
                    let input_effect = tp.strict_effect_type(input_type);
                    if let Some(input_effect) = input_effect
                        && input_effect.e.is_some()
                        && !tp
                            .checker
                            .ty(input_effect.e)
                            .flags
                            .intersects(TypeFlags::NEVER)
                    {
                        matches.push(CatchDieToOrDieMatch {
                            source_file: sf,
                            location: get_error_range_for_node(sf, callee),
                            transformation: transformation.clone(),
                            effect_module,
                            catch_method_name: method_name,
                            has_type_arguments: catch_die_has_type_arguments(Some(transformation)),
                        });
                    }
                }
            }

            input_type = transformation.out_type;
        }
    }

    matches
}

// Go: rules/catch_die_to_or_die.go catchDieMethod
fn catch_die_method(tp: &mut TypeParser<'_>, callee: Node) -> (String, Node, bool) {
    if callee.is_nil() {
        return (String::new(), Node::NIL, false);
    }

    let mut name = "catchAll";
    if tp.supported_effect_version() == EffectMajorVersion::V4 {
        name = "catch";
    }
    if !tp.is_node_reference_to_effect_module_api(callee, name) {
        return (String::new(), Node::NIL, false);
    }

    let mut effect_module = Node::NIL;
    if callee.kind() == SyntaxKind::PropertyAccessExpression {
        effect_module = callee.expression();
    }
    (name.to_string(), effect_module, true)
}

// Go: rules/catch_die_to_or_die.go catchDieHasTypeArguments
pub fn catch_die_has_type_arguments(transformation: Option<&PipingFlowTransformation>) -> bool {
    transformation.is_some_and(|transformation| {
        transformation.type_arguments.is_some() && !transformation.type_arguments.nodes().is_empty()
    })
}
