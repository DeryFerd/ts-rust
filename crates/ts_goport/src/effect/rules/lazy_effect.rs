//! Port of Effect-TS/tsgo `internal/rules/lazy_effect.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/lazy_effect.go LazyEffect
pub static LAZY_EFFECT: Rule = Rule {
    name: "lazyEffect",
    group: "antipattern",
    description: "Suggests avoiding exported zero-argument functions and service members that lazily return Effect or Stream values",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377091],
    run: run_lazy_effect,
};

fn run_lazy_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    if !ctx.tp.detect_effect_version_string().starts_with("4.") {
        return Vec::new();
    }

    let mut diags = Vec::new();

    for stmt in ctx.source_file.statements().iter() {
        if stmt.is_nil() {
            continue;
        }

        diags.extend(check_lazy_effect_export(ctx, stmt));
        diags.extend(check_lazy_effect_interface(ctx, stmt));
        diags.extend(check_lazy_effect_service(ctx, stmt));
    }

    diags
}

// Go: rules/lazy_effect.go checkLazyEffectInterface
fn check_lazy_effect_interface(ctx: &mut RuleContext<'_, '_>, stmt: Node) -> Vec<Diagnostic> {
    if stmt.kind() != SyntaxKind::InterfaceDeclaration
        || !has_syntactic_modifier(stmt, ModifierFlags::EXPORT)
        || stmt.name().is_nil()
    {
        return Vec::new();
    }

    let interface_name = get_text_of_node(stmt.name());
    let mut diags = Vec::new();
    for member in stmt.members().iter() {
        if member.is_nil() || member.name().is_nil() {
            continue;
        }
        if member.kind() != SyntaxKind::PropertySignature
            && member.kind() != SyntaxKind::MethodSignature
        {
            continue;
        }

        let member_type = ctx.tp.get_type_at_location(member.name());
        let Some(lazy_type_name) = lazy_effect_like_type_name(ctx.tp, member_type) else {
            continue;
        };

        let message_subject = format!(
            "Interface '{}' member '{}'",
            interface_name,
            get_text_of_node(member.name())
        );
        let sf = ctx.source_file;
        diags.push(ctx.new_diagnostic(
            sf,
            ctx.get_error_range(member.name()),
            diag::X_0_returns_a_lazy_1_1_is_already_lazy_so_wrapping_it_in_a_zero_argument_function_adds_unnecessary_indirection_effect_lazyEffect,
            Vec::new(),
            vec![message_subject, lazy_type_name.to_string()],
        ));
    }

    diags
}

// Go: rules/lazy_effect.go checkLazyEffectExport
fn check_lazy_effect_export(ctx: &mut RuleContext<'_, '_>, stmt: Node) -> Vec<Diagnostic> {
    if !has_syntactic_modifier(stmt, ModifierFlags::EXPORT) {
        return Vec::new();
    }

    match stmt.kind() {
        SyntaxKind::FunctionDeclaration => {
            if stmt.body().is_nil()
                || stmt.name().is_nil()
                || stmt.name().kind() != SyntaxKind::Identifier
            {
                return Vec::new();
            }
            return lazy_effect_diagnostic_for_exported_declaration(ctx, stmt.name());
        }

        SyntaxKind::VariableStatement => {
            let decl_list = stmt.declaration_list();
            if decl_list.is_nil() {
                return Vec::new();
            }

            let mut diags = Vec::new();
            for decl in decl_list.declarations().nodes().iter() {
                if decl.is_nil()
                    || decl.name().is_nil()
                    || decl.name().kind() != SyntaxKind::Identifier
                {
                    continue;
                }
                diags.extend(lazy_effect_diagnostic_for_exported_declaration(
                    ctx,
                    decl.name(),
                ));
            }
            return diags;
        }
        _ => {}
    }

    Vec::new()
}

// Go: rules/lazy_effect.go lazyEffectDiagnosticForExportedDeclaration
fn lazy_effect_diagnostic_for_exported_declaration(
    ctx: &mut RuleContext<'_, '_>,
    name: Node,
) -> Vec<Diagnostic> {
    let decl_type = ctx.tp.get_type_at_location(name);
    let Some(lazy_type_name) = lazy_effect_like_type_name(ctx.tp, decl_type) else {
        return Vec::new();
    };

    let message_subject = format!("Exported declaration '{}'", get_text_of_node(name));
    let sf = ctx.source_file;
    vec![ctx.new_diagnostic(
        sf,
        ctx.get_error_range(name),
        diag::X_0_returns_a_lazy_1_1_is_already_lazy_so_wrapping_it_in_a_zero_argument_function_adds_unnecessary_indirection_effect_lazyEffect,
        Vec::new(),
        vec![message_subject, lazy_type_name.to_string()],
    )]
}

// Go: rules/lazy_effect.go checkLazyEffectService
fn check_lazy_effect_service(ctx: &mut RuleContext<'_, '_>, stmt: Node) -> Vec<Diagnostic> {
    if stmt.kind() != SyntaxKind::ClassDeclaration
        || stmt.name().is_nil()
        || stmt.name().kind() != SyntaxKind::Identifier
    {
        return Vec::new();
    }
    if ctx.tp.extends_context_service(stmt).is_none() {
        return Vec::new();
    }

    let class_sym = ctx.tp.get_symbol_at_location(stmt.name());
    if class_sym.is_nil() {
        return Vec::new();
    }
    let class_type = ctx
        .tp
        .checker
        .get_type_of_symbol_at_location(class_sym, stmt.name());
    if class_type.is_nil() {
        return Vec::new();
    }

    let Some(service) = ctx.tp.service_type(class_type) else {
        return Vec::new();
    };
    if service.shape.is_nil() {
        return Vec::new();
    }

    let service_name = get_text_of_node(stmt.name());
    let mut diags = Vec::new();
    for member in ctx
        .tp
        .checker
        .get_properties_of_type_exported(service.shape)
    {
        if member.is_nil() {
            continue;
        }

        let member_type = ctx
            .tp
            .checker
            .get_type_of_symbol_at_location(member, stmt.name());
        let Some(lazy_type_name) = lazy_effect_like_type_name(ctx.tp, member_type) else {
            continue;
        };

        let message_subject = format!(
            "Service '{}' member '{}'",
            service_name,
            ctx.tp.checker.sym(member).name
        );
        let sf = ctx.source_file;
        diags.push(ctx.new_diagnostic(
            sf,
            ctx.get_error_range(stmt.name()),
            diag::X_0_returns_a_lazy_1_1_is_already_lazy_so_wrapping_it_in_a_zero_argument_function_adds_unnecessary_indirection_effect_lazyEffect,
            Vec::new(),
            vec![message_subject, lazy_type_name.to_string()],
        ));
    }

    diags
}

/// Go returns `(string, bool)`; `None` is Go's `"", false`.
// Go: rules/lazy_effect.go lazyEffectLikeTypeName
fn lazy_effect_like_type_name(tp: &mut TypeParser<'_>, t: TypeId) -> Option<&'static str> {
    if t.is_nil() {
        return None;
    }

    let call_signatures = tp
        .checker
        .get_signatures_of_type_exported(t, SignatureKind::CALL);
    if call_signatures.len() != 1 {
        return None;
    }

    let sig = call_signatures[0];
    if !tp.checker.sig(sig).type_parameters().is_empty() {
        return None;
    }
    if !tp.checker.sig(sig).parameters().is_empty() {
        return None;
    }

    let return_type = tp.checker.get_return_type_of_signature_exported(sig);
    if return_type.is_nil() {
        return None;
    }

    if tp.strict_is_effect_type(return_type) {
        return Some("Effect");
    }
    if tp.layer_type(return_type).is_some() {
        return Some("Layer");
    }
    if tp.stream_type(return_type).is_some() {
        return Some("Stream");
    }

    None
}
