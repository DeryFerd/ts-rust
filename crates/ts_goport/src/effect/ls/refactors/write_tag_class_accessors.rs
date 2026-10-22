//! Port of Effect-TS/tsgo `internal/refactors/write_tag_class_accessors.go`.
//!
//! Effect v3 only: for a class that extends `Effect.Service` (with
//! `accessors: true`) or `Effect.Tag`, it writes `static override`
//! accessors for the service methods that are generic or overloaded.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::{EffectMajorVersion, TypeParser, find_effect_module_identifier};
use crate::ls::CodeAction;
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: refactors/write_tag_class_accessors.go:17 WriteTagClassAccessors
pub static WRITE_TAG_CLASS_ACCESSORS: Refactor = Refactor {
    name: "writeTagClassAccessors",
    description: "Implement Service accessors",
    kind: "rewrite.effect.writeTagClassAccessors",
    run: run_write_tag_class_accessors,
};

// Go: refactors/write_tag_class_accessors.go:25 involvedMember
// involvedMember holds a property symbol and its type for accessor generation.
struct InvolvedMember {
    property: SymbolId,
    property_type: TypeId,
}

// Go: refactors/write_tag_class_accessors.go:30 runWriteTagClassAccessors
fn run_write_tag_class_accessors(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // V3-only refactor
    if ctx.tp.supported_effect_version() == EffectMajorVersion::V4 {
        return Vec::new();
    }

    // Walk ancestors to find a ClassDeclaration
    let mut class_node = Node::NIL;
    let mut node = token;
    while node.is_some() && node.kind() != SyntaxKind::SourceFile {
        if node.kind() == SyntaxKind::ClassDeclaration {
            class_node = node;
            break;
        }
        node = node.parent();
    }
    if class_node.is_nil() {
        return Vec::new();
    }

    // Check ExtendsEffectService (with accessors: true) or ExtendsEffectTag
    let class_name;
    if let Some(service_result) = ctx.tp.extends_effect_v3_service(class_node) {
        if !has_accessors_true(service_result.options) {
            return Vec::new();
        }
        class_name = service_result.class_name;
    } else if let Some(tag_result) = ctx.tp.extends_effect_tag(class_node) {
        // Effect.Tag always has accessors
        class_name = tag_result.class_name;
    } else {
        return Vec::new();
    }

    if class_name.is_nil() {
        return Vec::new();
    }

    // Resolve the service shape type via the _Service variance struct
    let class_symbol = ctx.tp.get_symbol_at_location(class_name);
    if class_symbol.is_nil() {
        return Vec::new();
    }
    let class_type = ctx
        .tp
        .checker
        .get_type_of_symbol_at_location(class_symbol, class_node);
    if class_type.is_nil() {
        return Vec::new();
    }

    let Some(context_tag) = ctx.tp.context_tag(class_type) else {
        return Vec::new();
    };
    if context_tag.shape.is_nil() {
        return Vec::new();
    }

    // Unroll union and filter out primitives
    let services = ctx.tp.unroll_union_members(context_tag.shape);
    let non_primitive_services = filter_non_primitive_types(ctx.tp.checker, services);
    if non_primitive_services.is_empty() {
        return Vec::new();
    }

    // Find involved members (those with generics or multiple overloads)
    let mut members: Vec<InvolvedMember> = Vec::new();
    let mut seen: FxHashSet<&'static str> = FxHashSet::default();
    let c = &mut *ctx.tp.checker;
    for &service in &non_primitive_services {
        for property in c.get_properties_of_type_exported(service) {
            let prop_name = c.sym(property).name.as_str();
            if seen.contains(prop_name) {
                continue;
            }
            let property_type = c.get_type_of_symbol_at_location(property, class_node);
            let call_signatures = c.get_signatures_of_type(property_type, SignatureKind::CALL);
            if call_signatures.is_empty() {
                continue;
            }
            let has_generics = call_signatures
                .iter()
                .any(|&sig| !c.sig(sig).type_parameters().is_empty());
            if call_signatures.len() > 1 || has_generics {
                members.push(InvolvedMember {
                    property,
                    property_type,
                });
                seen.insert(prop_name);
            }
        }
    }

    if members.is_empty() {
        return Vec::new();
    }

    let effect_identifier = find_effect_module_identifier(ctx.source_file);
    let class_name_text = get_text_of_node(class_name);

    // PORT: Go builds the text in the tracker closure (`generateAccessors`),
    // which cannot borrow the checker here; the text is built first and the
    // closure inserts it. Nothing else uses the checker in between.
    let Some((insert_pos, text)) = generate_accessors(
        ctx,
        class_node,
        &class_name_text,
        &effect_identifier,
        &members,
    ) else {
        return Vec::new();
    };
    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Implement Service accessors", |tracker| {
        tracker.insert_text(sf, insert_pos, &text);
    });
    with_kind(action, "refactor.rewrite.effect.writeTagClassAccessors")
}

// Go: refactors/write_tag_class_accessors.go:147 hasAccessorsTrue
// hasAccessorsTrue checks if an options object literal has `accessors: true`.
fn has_accessors_true(options: Node) -> bool {
    if options.is_nil() || options.kind() != SyntaxKind::ObjectLiteralExpression {
        return false;
    }
    // PORT: Go also checks a nil `Properties` list and nil elements; the
    // port's property list is never nil.
    for prop in options.properties().iter() {
        if prop.is_nil() || prop.kind() != SyntaxKind::PropertyAssignment {
            continue;
        }
        if prop.name().is_nil() {
            continue;
        }
        let name = get_text_of_node(prop.name());
        if name == "accessors"
            && prop.initializer().is_some()
            && prop.initializer().kind() == SyntaxKind::TrueKeyword
        {
            return true;
        }
    }
    false
}

// Go: refactors/write_tag_class_accessors.go:172 filterNonPrimitiveTypes
// filterNonPrimitiveTypes filters out primitive types (number, string, boolean, literals).
fn filter_non_primitive_types(c: &Checker, types: Vec<TypeId>) -> Vec<TypeId> {
    types
        .into_iter()
        .filter(|&t| {
            let flags = c.ty(t).flags;
            !(flags.intersects(TypeFlags::NUMBER)
                || flags.intersects(TypeFlags::STRING)
                || flags.intersects(TypeFlags::BOOLEAN)
                || flags.intersects(TypeFlags::LITERAL))
        })
        .collect()
}

// Go: refactors/write_tag_class_accessors.go:188 generateAccessors
// generateAccessors generates accessor text directly via InsertText.
// PORT: Go calls `tracker.InsertText` at the end; the port returns the
// position and the text (with its final new line) for the caller's tracker
// closure, or `None` when Go inserts nothing. Go's `classDecl == nil` check
// cannot fail for a ClassDeclaration node.
fn generate_accessors(
    ctx: &mut RefactorContext<'_, '_>,
    class_node: Node,
    class_name_text: &str,
    effect_identifier: &str,
    members: &[InvolvedMember],
) -> Option<(lsproto::Position, String)> {
    // Find insert location: first member's pos, or end of class - 1
    let mut insert_pos = class_node.end() - 1;
    if let Some(first) = class_node.members().first() {
        insert_pos = first.pos();
    }
    let ls_pos = ctx.byte_pos_to_lsp_position(insert_pos);

    let mut sb = String::new();
    for member in members {
        let property_name = ctx.tp.checker.sym(member.property).name.as_str();
        let call_signatures = ctx
            .tp
            .checker
            .get_signatures_of_type(member.property_type, SignatureKind::CALL);
        if call_signatures.is_empty() {
            continue;
        }

        let force_any = call_signatures.len() > 1;

        // Build signature type strings
        let mut sig_type_strs: Vec<String> = Vec::new();
        for &sig in call_signatures.iter() {
            let sig_str = build_proxy_signature_text(
                ctx.tp,
                sig,
                class_node,
                class_name_text,
                effect_identifier,
            );
            if !sig_str.is_empty() {
                sig_type_strs.push(sig_str);
            }
        }
        if sig_type_strs.is_empty() {
            continue;
        }

        // Build type annotation
        let type_annotation = if sig_type_strs.len() == 1 {
            sig_type_strs[0].clone()
        } else {
            "(".to_string() + &sig_type_strs.join(") & (") + ")"
        };

        // Build the property text
        sb.push_str("\n  static override ");
        sb.push_str(property_name);
        sb.push_str(": ");
        sb.push_str(&type_annotation);
        sb.push_str(" = (");
        if force_any {
            sb.push_str("...args: any[]");
        } else {
            sb.push_str("...args");
        }
        sb.push_str(") => ");
        sb.push_str(effect_identifier);
        sb.push_str(".andThen(");
        sb.push_str(class_name_text);
        sb.push_str(", (");
        if force_any {
            sb.push_str("_: any");
        } else {
            sb.push('_');
        }
        sb.push_str(") => _.");
        sb.push_str(property_name);
        sb.push_str("(...args))");
        if force_any {
            sb.push_str(" as any");
        }
    }

    if sb.is_empty() {
        return None;
    }
    Some((ls_pos, sb + "\n"))
}

// Go: refactors/write_tag_class_accessors.go:274 buildProxySignatureText
// buildProxySignatureText builds the text representation of a proxy function type for a call signature.
fn build_proxy_signature_text(
    tp: &mut TypeParser<'_>,
    sig: SignatureId,
    class_node: Node,
    class_name_text: &str,
    effect_identifier: &str,
) -> String {
    let mut sb = String::new();

    // Type parameters
    let type_params = tp.checker.sig(sig).type_parameters().to_vec();
    if !type_params.is_empty() {
        sb.push('<');
        for (i, &type_param) in type_params.iter().enumerate() {
            if i > 0 {
                sb.push_str(", ");
            }
            let c = &mut *tp.checker;
            let type_param_symbol = c.ty(type_param).symbol;
            sb.push_str(c.sym(type_param_symbol).name.as_str());
            let constraint_type = c.get_constraint_of_type_parameter_exported(type_param);
            if constraint_type.is_some() {
                sb.push_str(" extends ");
                sb.push_str(&c.type_to_string_ex(
                    constraint_type,
                    class_node,
                    TypeFormatFlags::NO_TRUNCATION,
                    None,
                ));
            }
        }
        sb.push('>');
    }

    // Parameters
    sb.push('(');
    let params = tp.checker.sig(sig).parameters().to_vec();
    let has_rest_parameter = tp.checker.sig(sig).has_rest_parameter();
    for (i, &param) in params.iter().enumerate() {
        if i > 0 {
            sb.push_str(", ");
        }
        if has_rest_parameter && i == params.len() - 1 {
            sb.push_str("...");
        }
        let c = &mut *tp.checker;
        sb.push_str(c.sym(param).name.as_str());
        sb.push_str(": ");
        let param_type = c.get_type_of_symbol_at_location(param, class_node);
        sb.push_str(&c.type_to_string_ex(
            param_type,
            class_node,
            TypeFormatFlags::NO_TRUNCATION,
            None,
        ));
    }
    sb.push(')');

    // Return type
    sb.push_str(" => ");
    let return_type = tp.checker.get_return_type_of_signature_exported(sig);
    let wrapped_return = build_wrapped_return_type_text(
        tp,
        return_type,
        class_node,
        class_name_text,
        effect_identifier,
    );
    sb.push_str(&wrapped_return);

    sb
}

// Go: refactors/write_tag_class_accessors.go:328 buildWrappedReturnTypeText
// buildWrappedReturnTypeText builds the text representation of the wrapped return type.
fn build_wrapped_return_type_text(
    tp: &mut TypeParser<'_>,
    return_type: TypeId,
    class_node: Node,
    class_name_text: &str,
    effect_identifier: &str,
) -> String {
    // Try to parse as Effect type
    if let Some(effect) = tp.effect_type(return_type) {
        let c = &mut *tp.checker;
        let a_str = c.type_to_string_ex(effect.a, class_node, TypeFormatFlags::NO_TRUNCATION, None);
        let e_str = c.type_to_string_ex(effect.e, class_node, TypeFormatFlags::NO_TRUNCATION, None);

        let r_str = if effect.r.is_some() && c.ty(effect.r).flags.intersects(TypeFlags::NEVER) {
            class_name_text.to_string()
        } else {
            class_name_text.to_string()
                + " | "
                + &c.type_to_string_ex(effect.r, class_node, TypeFormatFlags::NO_TRUNCATION, None)
        };

        return effect_identifier.to_string()
            + ".Effect<"
            + &a_str
            + ", "
            + &e_str
            + ", "
            + &r_str
            + ">";
    }

    // Try to detect Promise<T>
    let c = &mut *tp.checker;
    let return_type_str = c.type_to_string_ex(
        return_type,
        class_node,
        TypeFormatFlags::NO_TRUNCATION,
        None,
    );
    if let Some(inner_type_str) = is_promise_type_string(&return_type_str) {
        return effect_identifier.to_string()
            + ".Effect<"
            + inner_type_str
            + ", Cause.UnknownException, "
            + class_name_text
            + ">";
    }

    // Fallback: Effect<A, never, ClassName>
    let a_str = c.type_to_string_ex(
        return_type,
        class_node,
        TypeFormatFlags::NO_TRUNCATION,
        None,
    );
    effect_identifier.to_string() + ".Effect<" + &a_str + ", never, " + class_name_text + ">"
}

// Go: refactors/write_tag_class_accessors.go:364 isPromiseTypeString
// isPromiseTypeString checks if the type string represents a Promise<T> and extracts the inner type string.
// PORT: Go returns `(string, bool)`; `None` is Go's `("", false)`.
fn is_promise_type_string(type_str: &str) -> Option<&str> {
    if !type_str.starts_with("Promise<") {
        return None;
    }
    let bytes = type_str.as_bytes();
    let mut depth = 0;
    for (i, &b) in bytes.iter().enumerate().skip(8) {
        match b {
            b'<' => depth += 1,
            b'>' => {
                if depth == 0 {
                    return Some(&type_str[8..i]);
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_promise_type_string_cases() {
        assert_eq!(is_promise_type_string("Promise<number>"), Some("number"));
        assert_eq!(
            is_promise_type_string("Promise<Map<string, Promise<void>>>"),
            Some("Map<string, Promise<void>>")
        );
        assert_eq!(is_promise_type_string("Promise<number"), None);
        assert_eq!(is_promise_type_string("Effect<number>"), None);
        assert_eq!(is_promise_type_string("Promise<>"), Some(""));
    }
}
