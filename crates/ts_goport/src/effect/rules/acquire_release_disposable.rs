//! Port of Effect-TS/tsgo `internal/rules/acquire_release_disposable.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

use super::all_of_map_to_for_each::{contains_spread_element, has_call_type_arguments};

// Go: rules.AcquireReleaseDisposable
/// AcquireReleaseDisposable suggests Effect.acquireDisposable when an
/// acquireRelease finalizer only invokes the acquired resource's JavaScript
/// disposal protocol.
pub static ACQUIRE_RELEASE_DISPOSABLE: Rule = Rule {
    name: "acquireReleaseDisposable",
    group: "style",
    description: "Suggests Effect.acquireDisposable when Effect.acquireRelease only invokes the acquired resource's disposal protocol",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377119],
    run: run_acquire_release_disposable,
};

fn run_acquire_release_disposable(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_acquire_release_disposable(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_acquireDisposable_expresses_this_disposable_resource_acquisition_more_directly_than_Effect_acquireRelease_with_a_manual_disposal_finalizer_effect_acquireReleaseDisposable,
            Vec::new(),
            Vec::new(),
        ));
    }
    diagnostics
}

// Go: rules.AcquireReleaseDisposableMatch
/// AcquireReleaseDisposableMatch holds the nodes needed by the diagnostic and
/// its quick fix.
#[derive(Clone)]
pub struct AcquireReleaseDisposableMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub call_node: Node,
    pub effect_module: Node,
    pub acquire: Node,
    pub has_type_arguments: bool,
}

// Go: rules.AnalyzeAcquireReleaseDisposable
/// AnalyzeAcquireReleaseDisposable finds Effect.acquireRelease calls whose
/// resulting success type is disposable and whose release callback consists
/// solely of invoking that resource's disposal protocol.
// PORT: Go also returns nil for a nil type parser or checker; neither is nil here.
pub fn analyze_acquire_release_disposable(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<AcquireReleaseDisposableMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let disposable = global_disposable_union(tp.checker);
    let global_symbol = tp
        .checker
        .get_global_symbol_exported("Symbol", SymbolFlags::VALUE, None);
    if disposable.is_nil() || global_symbol.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    walk(tp, sf, disposable, global_symbol, &mut matches, sf);
    matches
}

fn walk(
    tp: &mut TypeParser<'_>,
    sf: Node,
    disposable: TypeId,
    global_symbol: SymbolId,
    matches: &mut Vec<AcquireReleaseDisposableMatch>,
    node: Node,
) -> bool {
    if node.is_nil() {
        return false;
    }

    if let Some(m) =
        analyze_acquire_release_disposable_call(tp, sf, node, disposable, global_symbol)
    {
        matches.push(m);
    }

    node.for_each_child(|child| walk(tp, sf, disposable, global_symbol, matches, child));
    false
}

// Go: rules.globalDisposableUnion
fn global_disposable_union(c: &mut Checker) -> TypeId {
    let mut types = Vec::new();
    for name in ["Disposable", "AsyncDisposable"] {
        let symbol = c.get_global_symbol_exported(name, SymbolFlags::TYPE, None);
        if symbol.is_nil() {
            continue;
        }
        let t = c.get_declared_type_of_symbol_exported(symbol);
        if t.is_some() {
            types.push(t);
        }
    }
    if types.is_empty() {
        return TypeId::NIL;
    }
    if types.len() == 1 {
        return types[0];
    }
    c.get_union_type_ex_exported(&types, UnionReduction::NONE)
}

// Go: rules.analyzeAcquireReleaseDisposableCall
fn analyze_acquire_release_disposable_call(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
    disposable: TypeId,
    global_symbol: SymbolId,
) -> Option<AcquireReleaseDisposableMatch> {
    if node.kind() != SyntaxKind::CallExpression {
        return None;
    }
    let call = node;
    let args = call.arguments().to_vec();
    if call.expression().is_nil()
        || call.question_dot_token().is_some()
        || args.len() != 2
        || contains_spread_element(&args)
        || !tp.is_node_reference_to_effect_module_api(call.expression(), "acquireRelease")
    {
        return None;
    }

    let node_type = tp.get_type_at_location(node);
    let result = tp.strict_effect_type(node_type)?;
    if !is_definitely_disposable(tp, result.a, disposable) {
        return None;
    }

    if !is_disposal_release(tp, args[1], global_symbol) {
        return None;
    }

    let mut effect_module = Node::NIL;
    if call.expression().kind() == SyntaxKind::PropertyAccessExpression {
        let access = call.expression();
        if access.question_dot_token().is_nil() {
            effect_module = access.expression();
        }
    }

    Some(AcquireReleaseDisposableMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, call.expression()),
        call_node: node,
        effect_module,
        acquire: args[0],
        has_type_arguments: has_call_type_arguments(call),
    })
}

// Go: rules.isDefinitelyDisposable
fn is_definitely_disposable(tp: &mut TypeParser<'_>, success: TypeId, disposable: TypeId) -> bool {
    if success.is_nil() || disposable.is_nil() {
        return false;
    }
    for member in tp.unroll_union_members(success) {
        if member.is_nil()
            || tp
                .checker
                .ty(member)
                .flags()
                .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::NEVER)
        {
            return false;
        }
    }
    tp.checker
        .is_type_assignable_to_exported(success, disposable)
}

// Go: rules.isDisposalRelease
fn is_disposal_release(tp: &mut TypeParser<'_>, node: Node, global_symbol: SymbolId) -> bool {
    let Some(release) = parse_lazy_expression(node, LazyExpressionFlags::NONE) else {
        return false;
    };
    if release.params.is_empty() || release.params.len() > 2 {
        return false;
    }

    let resource = release.params[0];
    if !is_plain_identifier_parameter(resource) {
        return false;
    }
    if release.params.len() == 2 && !is_plain_identifier_parameter(release.params[1]) {
        return false;
    }
    let resource_symbol = tp.get_symbol_at_location(resource.name());
    if resource_symbol.is_nil() {
        return false;
    }

    let expression = skip_parentheses(release.expression);
    if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
        return false;
    }
    let wrapper = expression;
    let wrapper_args = wrapper.arguments().to_vec();
    if wrapper.expression().is_nil()
        || wrapper.question_dot_token().is_some()
        || wrapper_args.len() != 1
        || contains_spread_element(&wrapper_args)
    {
        return false;
    }

    let wrapper_name = if tp.is_node_reference_to_effect_module_api(wrapper.expression(), "sync") {
        "sync"
    } else if tp.is_node_reference_to_effect_module_api(wrapper.expression(), "promise") {
        "promise"
    } else {
        return false;
    };

    let mut flags = LazyExpressionFlags::THUNK;
    if wrapper_name == "promise" {
        flags |= LazyExpressionFlags::ALLOW_ASYNC;
    }
    let Some(thunk) = parse_lazy_expression(wrapper_args[0], flags) else {
        return false;
    };
    if thunk.expression.is_nil() {
        return false;
    }

    let (protocol, ok) =
        disposal_protocol_call(tp, thunk.expression, resource_symbol, global_symbol);
    ok && (protocol == "dispose" && wrapper_name == "sync"
        || protocol == "asyncDispose" && wrapper_name == "promise")
}

// Go: rules.isPlainIdentifierParameter
fn is_plain_identifier_parameter(node: Node) -> bool {
    if node.is_nil()
        || node.kind() != SyntaxKind::Parameter
        || node.name().is_nil()
        || node.name().kind() != SyntaxKind::Identifier
    {
        return false;
    }
    let parameter = node;
    parameter.dot_dot_dot_token().is_nil()
        && parameter.question_token().is_nil()
        && parameter.initializer().is_nil()
}

// Go: rules.disposalProtocolCall
fn disposal_protocol_call(
    tp: &mut TypeParser<'_>,
    node: Node,
    resource_symbol: SymbolId,
    global_symbol: SymbolId,
) -> (String, bool) {
    let node = skip_parentheses(node);
    if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
        return (String::new(), false);
    }
    let call = node;
    if call.question_dot_token().is_some()
        || !call.type_arguments().is_empty()
        || !call.arguments().is_empty()
        || call.expression().is_nil()
        || call.expression().kind() != SyntaxKind::ElementAccessExpression
    {
        return (String::new(), false);
    }

    let element = call.expression();
    if element.question_dot_token().is_some()
        || element.expression().is_nil()
        || element.argument_expression().is_nil()
    {
        return (String::new(), false);
    }
    let actual_resource = tp.get_symbol_at_location(skip_parentheses(element.expression()));
    if actual_resource.is_nil()
        || tp
            .checker
            .get_symbol_if_same_reference(actual_resource, resource_symbol)
            .is_nil()
    {
        return (String::new(), false);
    }

    let key = skip_parentheses(element.argument_expression());
    if key.is_nil() || key.kind() != SyntaxKind::PropertyAccessExpression {
        return (String::new(), false);
    }
    let access = key;
    if access.question_dot_token().is_some()
        || access.expression().is_nil()
        || access.name().is_nil()
    {
        return (String::new(), false);
    }
    let access_symbol = tp.get_symbol_at_location(access.expression());
    let actual_symbol = tp.resolve_to_global_symbol(access_symbol);
    if actual_symbol.is_nil() || actual_symbol != global_symbol {
        return (String::new(), false);
    }

    let protocol = access.name().text().to_string();
    let ok = protocol == "dispose" || protocol == "asyncDispose";
    (protocol, ok)
}
