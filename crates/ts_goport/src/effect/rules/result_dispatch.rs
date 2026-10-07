//! Port of Effect-TS/tsgo `internal/rules/result_dispatch.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

use super::catch_tag_to_catch_reason::same_catch_reason_symbol;
use super::redundant_map_error::unwrap_transparent_expression;

pub fn result_dispatch_tag_value(condition: DispatchCondition) -> (String, bool) {
    let value = unwrap_transparent_expression(condition.tag_value);
    if condition.tag_subject.is_some() && value.is_some() && is_string_literal(value) {
        return (value.text().to_string(), true);
    }
    (String::new(), false)
}

pub fn is_result_dispatch_tag_reference(
    tp: &mut TypeParser<'_>,
    tag_subject: Node,
    root_symbol: SymbolId,
) -> bool {
    let tag_subject = unwrap_transparent_expression(tag_subject);
    if tag_subject.is_nil() || root_symbol.is_nil() {
        return false;
    }

    let mut root = tag_subject;
    loop {
        root = unwrap_transparent_expression(root);
        if root.is_nil() || root.kind() != SyntaxKind::PropertyAccessExpression {
            break;
        }
        let property = root;
        if property.expression().is_nil() {
            return false;
        }
        root = property.expression();
    }
    if root.is_nil() || !same_catch_reason_symbol(tp, root, root_symbol) {
        return false;
    }

    let owner_type = tp.get_type_at_location(tag_subject);
    if owner_type.is_nil() {
        return false;
    }
    if tp
        .checker
        .get_property_of_type_exported(owner_type, "_tag")
        .is_some()
    {
        return true;
    }
    for member in tp.unroll_union_members(owner_type) {
        if member.is_some()
            && tp
                .checker
                .get_property_of_type_exported(member, "_tag")
                .is_some()
        {
            return true;
        }
    }
    false
}
