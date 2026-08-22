//! Canonical declared and value identities for top-level literal enums.
//!
//! This is the dependency-closed prefix of pinned typescript-go's
//! `getDeclaredTypeOfEnum`, `getDeclaredTypeOfEnumMember`,
//! `getTypeOfFuncClassEnumModule`, and `computeEnumMemberValues`. It supports
//! one non-merged top-level enum declaration whose members have identifier or
//! string-literal names and constant numeric or string expressions. Earlier
//! members can be referenced by name, property access, or string element
//! access. Numeric
//! auto-increment, explicit ambient behavior, const-enum provenance,
//! regular/fresh member identities, the enum declared union, and the separate
//! enum value object are published together.
//! Numeric and string identities use the pinned `(enum owner, literal value)`
//! cache key, so later duplicate-valued members route to the first member's
//! regular/fresh pair.
//!
//! Source statement dispatch is deliberately not part of this module. Its
//! integration seam is [`get_enum_semantics`]: a source prepass can call it for
//! every hoisted enum owner, then use [`CanonicalEnumSemantics::value_type`]
//! for value reads and each member's fresh identity for property reads.
//! Merged declarations, computed names, forward references, and expressions
//! outside the upstream constant evaluator remain typed unsupported
//! boundaries.

use ts_ast::{
    BinaryExpressionData, NodeData, NodeList, NodeRef, SyntaxKind, TemplateExpressionData,
};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};
use ts_evaluator::{
    Evaluation, EvaluationMetadata, EvaluationOutcome, UnknownReason, Value, evaluate_with,
};
use ts_jsnum::Number;

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, TypeId,
    links::{
        DeclaredTypeLinks, EnumMemberLinks, EvaluatorResult, EvaluatorValue, NodeCheckFlags,
        NodeLinks, ValueSymbolLinks,
    },
    type_records::{
        LiteralValue, RegularLiteralLink, StructuredTypeData, TypeCacheState, TypeData,
        UnionOrIntersectionTypeData, UnionTypeData,
    },
    types::{ObjectFlags, TypeFlags},
};

/// Compile-time value retained for one enum member.
#[derive(Clone, Debug, PartialEq)]
pub enum CanonicalEnumMemberValue {
    Number(Number),
    String(String),
    /// Pinned `nil` evaluator result and `TypeFlagsEnum` identity.
    Computed,
}

/// A nonfatal enum initializer diagnostic retained for source execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct EnumMemberDiagnostic {
    pub(super) node: NodeRef,
    pub(super) code: u32,
}

/// Published semantic identities for one enum member.
#[derive(Clone, Debug, PartialEq)]
pub struct CanonicalEnumMemberSemantics {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub regular_type: TypeId,
    pub fresh_type: TypeId,
    pub value: CanonicalEnumMemberValue,
}

/// Complete dependency-closed result for one top-level enum declaration.
#[derive(Clone, Debug, PartialEq)]
pub struct CanonicalEnumSemantics {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    /// Type-side identity (`E`).
    pub declared_type: TypeId,
    /// Value-side anonymous object identity (`typeof E`).
    pub value_type: TypeId,
    pub members: Vec<CanonicalEnumMemberSemantics>,
    pub is_const: bool,
    pub is_ambient: bool,
}

/// Syntax families intentionally deferred beyond the literal enum cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EnumTypeUnsupported {
    MergedDeclarations(SemanticSymbolId),
    NestedDeclaration(NodeRef),
    Modifiers(NodeRef),
    MemberName(NodeRef),
    MemberModifiers(NodeRef),
    Initializer(NodeRef),
    MissingInitializer(NodeRef),
}

/// Malformed retained syntax, binder provenance, or semantic cache state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EnumTypeInvariant {
    SymbolNotOwned(SemanticSymbolId),
    MissingOrForeignFacts(NodeRef),
    InvalidDeclaration(NodeRef),
    InvalidOwnerSymbol(SemanticSymbolId),
    InvalidExportRoute(NodeRef),
    InvalidMember(NodeRef),
    InvalidMemberSymbol(NodeRef),
    InvalidCache(SemanticSymbolId),
    Capacity(SemanticSymbolId),
}

/// Exact failure domain for canonical enum publication.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EnumTypeError {
    Unsupported(EnumTypeUnsupported),
    Invariant(EnumTypeInvariant),
}

impl std::fmt::Display for EnumTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(reason) => {
                write!(formatter, "enum syntax is unsupported: {reason:?}")
            }
            Self::Invariant(reason) => {
                write!(formatter, "enum semantic invariant failed: {reason:?}")
            }
        }
    }
}

impl std::error::Error for EnumTypeError {}

#[derive(Clone, Debug, PartialEq)]
struct EnumMemberPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    value: CanonicalEnumMemberValue,
    name_diagnostic: Option<EnumMemberDiagnostic>,
    diagnostic: Option<EnumMemberDiagnostic>,
}

#[derive(Clone, Debug, PartialEq)]
struct EnumPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    members: Vec<EnumMemberPlan>,
    is_const: bool,
    is_ambient: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EnumState {
    Cold,
    Resolved,
}

fn unsupported(reason: EnumTypeUnsupported) -> EnumTypeError {
    EnumTypeError::Unsupported(reason)
}

fn invariant(reason: EnumTypeInvariant) -> EnumTypeError {
    EnumTypeError::Invariant(reason)
}

fn preflight_node<'a>(
    store: &CanonicalTypeMapperStore,
    host: &'a DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<&'a ts_ast::Node, EnumTypeError> {
    if !store.contains_node_ref(node) {
        return Err(invariant(EnumTypeInvariant::MissingOrForeignFacts(node)));
    }
    host.node(node)
        .ok_or_else(|| invariant(EnumTypeInvariant::MissingOrForeignFacts(node)))
}

fn plan_enum(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<EnumPlan, EnumTypeError> {
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or_else(|| invariant(EnumTypeInvariant::SymbolNotOwned(symbol)))?;
    let owner = store
        .symbol(symbol)
        .ok_or_else(|| invariant(EnumTypeInvariant::SymbolNotOwned(symbol)))?;
    if !matches!(owner.declarations(), Some([_])) {
        return Err(unsupported(EnumTypeUnsupported::MergedDeclarations(symbol)));
    }
    let declaration = owner.declarations().expect("one declaration was checked")[0];
    let record = preflight_node(store, host, declaration)?;
    let NodeData::EnumDeclaration(enumeration) = &record.data else {
        return Err(invariant(EnumTypeInvariant::InvalidDeclaration(
            declaration,
        )));
    };
    if record.kind != SyntaxKind::EnumDeclaration
        || store.source_node_kind(declaration) != Some(SyntaxKind::EnumDeclaration)
        || store.source_node_parent(declaration)
            != Some(super::store::SourceNodeParent::Parent(
                host.bound_file(declaration)
                    .ok_or_else(|| {
                        invariant(EnumTypeInvariant::MissingOrForeignFacts(declaration))
                    })?
                    .source_file(),
            ))
    {
        return Err(unsupported(EnumTypeUnsupported::NestedDeclaration(
            declaration,
        )));
    }
    let name = NodeRef::new(declaration.arena, declaration.file, enumeration.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invariant(EnumTypeInvariant::InvalidDeclaration(
            declaration,
        )));
    };
    let (is_const, has_declare_modifier, is_exported) = validate_modifiers(
        store,
        host,
        declaration,
        enumeration
            .modifiers
            .as_ref()
            .map(|modifiers| &modifiers.list),
    )?;
    let expected_flags = if is_const {
        SymbolFlags::CONST_ENUM
    } else {
        SymbolFlags::REGULAR_ENUM
    };
    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(EnumTypeInvariant::MissingOrForeignFacts(declaration)))?;
    let is_ambient = has_declare_modifier
        || bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file);
    let bound_owner = bound
        .symbol(declaration)
        .and_then(|candidate| store.get_merged_symbol(candidate));
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || owner.flags() != expected_flags
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_bytes() != identifier.text.as_bytes()
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.exports().is_some() == enumeration.members.nodes.is_empty()
        || owner.export_symbol().is_some()
        || bound_owner != Some(symbol)
    {
        return Err(invariant(EnumTypeInvariant::InvalidOwnerSymbol(symbol)));
    }
    validate_export_route(
        store,
        declaration,
        symbol,
        is_exported,
        is_ambient,
        bound.local_symbol(declaration),
        bound.symbol(bound.source_file()),
    )?;

    let member_table = owner
        .exports()
        .and_then(|members| store.symbol_table(members));
    if member_table.map_or(0, ts_binder::semantic::SymbolTable::len)
        != enumeration.members.nodes.len()
    {
        return Err(invariant(EnumTypeInvariant::InvalidOwnerSymbol(symbol)));
    }
    let mut members = Vec::with_capacity(enumeration.members.nodes.len());
    let mut next_numeric = Some(Number::new(0.0));
    for member_id in &enumeration.members.nodes {
        let member = NodeRef::new(declaration.arena, declaration.file, *member_id);
        let member_record = preflight_node(store, host, member)?;
        let NodeData::EnumMember(member_data) = &member_record.data else {
            return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
        };
        if member_record.kind != SyntaxKind::EnumMember
            || member_record.parent != Some(declaration.node)
            || member_data.postfix_token.is_some()
        {
            return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
        }
        if member_data.modifiers.is_some() {
            return Err(unsupported(EnumTypeUnsupported::MemberModifiers(member)));
        }
        let member_name = NodeRef::new(member.arena, member.file, member_data.name);
        let member_name_record = preflight_node(store, host, member_name)?;
        let member_name_text = match &member_name_record.data {
            NodeData::Identifier(identifier)
                if member_name_record.kind == SyntaxKind::Identifier =>
            {
                identifier.text.as_str()
            }
            NodeData::StringLiteral(literal)
                if member_name_record.kind == SyntaxKind::StringLiteral =>
            {
                literal.text.as_str()
            }
            _ => return Err(unsupported(EnumTypeUnsupported::MemberName(member_name))),
        };
        if member_name_record.parent != Some(member.node) {
            return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
        }
        let name_diagnostic = (!matches!(member_name_text, "NaN" | "Infinity" | "-Infinity")
            && Number::from_string(member_name_text).to_string() == member_name_text)
            .then_some(EnumMemberDiagnostic {
                node: member_name,
                code: 2452,
            });
        let member_symbol = bound
            .symbol(member)
            .and_then(|candidate| store.get_merged_symbol(candidate))
            .ok_or_else(|| invariant(EnumTypeInvariant::InvalidMemberSymbol(member)))?;
        let member_symbol_record = store
            .symbol(member_symbol)
            .ok_or_else(|| invariant(EnumTypeInvariant::InvalidMemberSymbol(member)))?;
        if member_table.and_then(|members| members.get_source(member_name_text))
            != Some(member_symbol)
            || member_symbol_record.flags() != SymbolFlags::ENUM_MEMBER
            || member_symbol_record.check_flags() != CheckFlags::NONE
            || member_symbol_record.name().as_bytes() != member_name_text.as_bytes()
            || member_symbol_record.declarations() != Some(&[member])
            || member_symbol_record.value_declaration() != Some(member)
            || member_symbol_record.members().is_some()
            || member_symbol_record.exports().is_some()
            || member_symbol_record.parent() != Some(symbol)
            || member_symbol_record.export_symbol().is_some()
        {
            return Err(invariant(EnumTypeInvariant::InvalidMemberSymbol(member)));
        }
        let (value, diagnostic) = match member_data.initializer {
            Some(initializer) => {
                let initializer = NodeRef::new(member.arena, member.file, initializer);
                let evaluated = constant_initializer(
                    store,
                    host,
                    member,
                    initializer,
                    &identifier.text,
                    &members,
                );
                let (value, diagnostic) = match evaluated {
                    Ok(CanonicalEnumMemberValue::Number(value)) if is_const && value.is_nan() => (
                        CanonicalEnumMemberValue::Number(value),
                        Some(EnumMemberDiagnostic {
                            node: initializer,
                            code: 2478,
                        }),
                    ),
                    Ok(CanonicalEnumMemberValue::Number(value))
                        if is_const && value.is_infinite() =>
                    {
                        (
                            CanonicalEnumMemberValue::Number(value),
                            Some(EnumMemberDiagnostic {
                                node: initializer,
                                code: 2477,
                            }),
                        )
                    }
                    Ok(value) => (value, None),
                    Err(EnumTypeError::Unsupported(EnumTypeUnsupported::Initializer(_)))
                        if is_const || is_ambient =>
                    {
                        (
                            CanonicalEnumMemberValue::Computed,
                            Some(EnumMemberDiagnostic {
                                node: initializer,
                                code: if is_const { 2474 } else { 1066 },
                            }),
                        )
                    }
                    Err(error) => return Err(error),
                };
                next_numeric = match &value {
                    CanonicalEnumMemberValue::Number(value) => Some(*value + Number::new(1.0)),
                    CanonicalEnumMemberValue::String(_) | CanonicalEnumMemberValue::Computed => {
                        None
                    }
                };
                (value, diagnostic)
            }
            None if is_ambient && !is_const => {
                next_numeric = None;
                (CanonicalEnumMemberValue::Computed, None)
            }
            None => match next_numeric {
                Some(value) => {
                    next_numeric = Some(value + Number::new(1.0));
                    (CanonicalEnumMemberValue::Number(value), None)
                }
                None => (
                    CanonicalEnumMemberValue::Computed,
                    Some(EnumMemberDiagnostic {
                        node: member_name,
                        code: 1061,
                    }),
                ),
            },
        };
        members.push(EnumMemberPlan {
            declaration: member,
            symbol: member_symbol,
            value,
            name_diagnostic,
            diagnostic,
        });
    }
    let plan = EnumPlan {
        declaration,
        symbol,
        members,
        is_const,
        is_ambient,
    };
    enum_state(store, &plan)?;
    Ok(plan)
}

/// Allocation-free syntax, binder, and cold/warm cache preflight for a type
/// reference that targets an enum owner.
pub(super) fn preflight_enum(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<(), EnumTypeError> {
    plan_enum(store, host, symbol).map(drop)
}

/// Returns nonfatal member diagnostics without publishing enum state.
pub(super) fn preflight_enum_diagnostics(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Vec<EnumMemberDiagnostic>, EnumTypeError> {
    let plan = plan_enum(store, host, symbol)?;
    Ok(plan
        .members
        .into_iter()
        .flat_map(|member| [member.name_diagnostic, member.diagnostic])
        .flatten()
        .collect())
}

fn validate_modifiers(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    modifiers: Option<&NodeList>,
) -> Result<(bool, bool, bool), EnumTypeError> {
    let mut is_const = false;
    let mut is_ambient = false;
    let mut is_exported = false;
    let Some(modifiers) = modifiers else {
        return Ok((false, false, false));
    };
    if modifiers.has_trailing_comma || modifiers.nodes.is_empty() {
        return Err(unsupported(EnumTypeUnsupported::Modifiers(declaration)));
    }
    for modifier_id in &modifiers.nodes {
        let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier_id);
        let record = preflight_node(store, host, modifier)?;
        if record.parent != Some(declaration.node) || !matches!(record.data, NodeData::Token(_)) {
            return Err(invariant(EnumTypeInvariant::InvalidDeclaration(
                declaration,
            )));
        }
        let slot = match record.kind {
            SyntaxKind::ConstKeyword => &mut is_const,
            SyntaxKind::DeclareKeyword => &mut is_ambient,
            SyntaxKind::ExportKeyword => &mut is_exported,
            _ => return Err(unsupported(EnumTypeUnsupported::Modifiers(modifier))),
        };
        if *slot {
            return Err(unsupported(EnumTypeUnsupported::Modifiers(modifier)));
        }
        *slot = true;
    }
    Ok((is_const, is_ambient, is_exported))
}

fn validate_export_route(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    is_exported: bool,
    is_ambient: bool,
    local: Option<SemanticSymbolId>,
    raw_source_owner: Option<SemanticSymbolId>,
) -> Result<(), EnumTypeError> {
    match (is_exported, local) {
        (false, None)
            if store
                .symbol(owner)
                .is_some_and(|symbol| symbol.parent().is_none()) =>
        {
            Ok(())
        }
        (_, Some(local)) if is_exported || is_ambient => {
            let source_owner = raw_source_owner
                .and_then(|source| store.get_merged_symbol(source))
                .ok_or_else(|| invariant(EnumTypeInvariant::InvalidExportRoute(declaration)))?;
            let owner_record = store
                .symbol(owner)
                .ok_or_else(|| invariant(EnumTypeInvariant::InvalidExportRoute(declaration)))?;
            let local_record = store
                .symbol(local)
                .ok_or_else(|| invariant(EnumTypeInvariant::InvalidExportRoute(declaration)))?;
            if owner_record.parent() == Some(source_owner)
                && local_record.flags() == SymbolFlags::EXPORT_VALUE
                && local_record.check_flags() == CheckFlags::NONE
                && local_record.name() == owner_record.name()
                && local_record.declarations() == Some(&[declaration])
                && local_record.value_declaration().is_none()
                && local_record.members().is_none()
                && local_record.exports().is_none()
                && local_record.parent().is_none()
                && local_record.export_symbol() == Some(owner)
            {
                Ok(())
            } else {
                Err(invariant(EnumTypeInvariant::InvalidExportRoute(
                    declaration,
                )))
            }
        }
        _ => Err(invariant(EnumTypeInvariant::InvalidExportRoute(
            declaration,
        ))),
    }
}

fn constant_initializer(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    initializer: NodeRef,
    enum_name: &str,
    previous_members: &[EnumMemberPlan],
) -> Result<CanonicalEnumMemberValue, EnumTypeError> {
    preflight_constant_expression(store, host, member, initializer, member)?;
    let (arena, _) = host
        .source(initializer)
        .ok_or_else(|| invariant(EnumTypeInvariant::MissingOrForeignFacts(initializer)))?;
    let evaluation = evaluate_with(arena, initializer.node, &mut |entity| {
        let entity = NodeRef::new(initializer.arena, initializer.file, entity);
        resolve_enum_entity(store, host, entity, enum_name, previous_members)
            .unwrap_or_else(|| Evaluation::unknown(UnknownReason::UnresolvedEntity(entity.node)))
    });
    match evaluation.outcome {
        EvaluationOutcome::Value(Value::Number(value)) => {
            Ok(CanonicalEnumMemberValue::Number(value))
        }
        EvaluationOutcome::Value(Value::String(value)) => {
            Ok(CanonicalEnumMemberValue::String(value))
        }
        EvaluationOutcome::Value(_)
        | EvaluationOutcome::Unknown(_)
        | EvaluationOutcome::Error(_) => {
            Err(unsupported(EnumTypeUnsupported::Initializer(initializer)))
        }
    }
}

fn preflight_constant_expression(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    expression: NodeRef,
    parent: NodeRef,
) -> Result<(), EnumTypeError> {
    let record = preflight_node(store, host, expression)?;
    if record.parent != Some(parent.node) {
        return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
    }
    let child = |node| NodeRef::new(expression.arena, expression.file, node);
    match &record.data {
        NodeData::NumericLiteral(_) if record.kind == SyntaxKind::NumericLiteral => Ok(()),
        NodeData::StringLiteral(_) if record.kind == SyntaxKind::StringLiteral => Ok(()),
        NodeData::NoSubstitutionTemplateLiteral(_)
            if record.kind == SyntaxKind::NoSubstitutionTemplateLiteral =>
        {
            Ok(())
        }
        NodeData::Identifier(_) if record.kind == SyntaxKind::Identifier => Ok(()),
        NodeData::ParenthesizedExpression(parenthesized)
            if record.kind == SyntaxKind::ParenthesizedExpression =>
        {
            preflight_constant_expression(
                store,
                host,
                member,
                child(parenthesized.expression),
                expression,
            )
        }
        NodeData::PrefixUnaryExpression(prefix)
            if record.kind == SyntaxKind::PrefixUnaryExpression
                && matches!(
                    prefix.operator,
                    SyntaxKind::PlusToken | SyntaxKind::MinusToken | SyntaxKind::TildeToken
                ) =>
        {
            preflight_constant_expression(store, host, member, child(prefix.operand), expression)
        }
        NodeData::BinaryExpression(binary) if record.kind == SyntaxKind::BinaryExpression => {
            preflight_binary_constant_expression(store, host, member, expression, binary)
        }
        NodeData::TemplateExpression(template) if record.kind == SyntaxKind::TemplateExpression => {
            preflight_template_constant_expression(store, host, member, expression, template)
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.question_dot_token.is_none() =>
        {
            let base = child(access.expression);
            let base_record = preflight_node(store, host, base)?;
            let name = child(access.name);
            let name_record = preflight_node(store, host, name)?;
            if base_record.parent != Some(expression.node)
                || name_record.parent != Some(expression.node)
                || !matches!(base_record.data, NodeData::Identifier(_))
                || !matches!(name_record.data, NodeData::Identifier(_))
            {
                return Err(unsupported(EnumTypeUnsupported::Initializer(expression)));
            }
            Ok(())
        }
        NodeData::ElementAccessExpression(access)
            if record.kind == SyntaxKind::ElementAccessExpression
                && access.question_dot_token.is_none() =>
        {
            let base = child(access.expression);
            let base_record = preflight_node(store, host, base)?;
            let argument = child(access.argument_expression);
            let argument_record = preflight_node(store, host, argument)?;
            if base_record.parent != Some(expression.node)
                || argument_record.parent != Some(expression.node)
                || !matches!(base_record.data, NodeData::Identifier(_))
                || !matches!(
                    argument_record.data,
                    NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_)
                )
            {
                return Err(unsupported(EnumTypeUnsupported::Initializer(expression)));
            }
            Ok(())
        }
        _ => Err(unsupported(EnumTypeUnsupported::Initializer(expression))),
    }
}

fn preflight_binary_constant_expression(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    expression: NodeRef,
    binary: &BinaryExpressionData,
) -> Result<(), EnumTypeError> {
    let child = |node| NodeRef::new(expression.arena, expression.file, node);
    let operator = child(binary.operator_token);
    let operator_record = preflight_node(store, host, operator)?;
    if operator_record.parent != Some(expression.node)
        || !matches!(operator_record.data, NodeData::Token(_))
    {
        return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
    }
    if !matches!(
        operator_record.kind,
        SyntaxKind::BarToken
            | SyntaxKind::AmpersandToken
            | SyntaxKind::GreaterThanGreaterThanToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanToken
            | SyntaxKind::LessThanLessThanToken
            | SyntaxKind::CaretToken
            | SyntaxKind::AsteriskToken
            | SyntaxKind::SlashToken
            | SyntaxKind::PlusToken
            | SyntaxKind::MinusToken
            | SyntaxKind::PercentToken
            | SyntaxKind::AsteriskAsteriskToken
    ) {
        return Err(unsupported(EnumTypeUnsupported::Initializer(expression)));
    }
    preflight_constant_expression(store, host, member, child(binary.left), expression)?;
    preflight_constant_expression(store, host, member, child(binary.right), expression)
}

fn preflight_template_constant_expression(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    member: NodeRef,
    expression: NodeRef,
    template: &TemplateExpressionData,
) -> Result<(), EnumTypeError> {
    let child = |node| NodeRef::new(expression.arena, expression.file, node);
    let head = child(template.head);
    let head_record = preflight_node(store, host, head)?;
    if head_record.parent != Some(expression.node)
        || !matches!(head_record.data, NodeData::TemplateHead(_))
    {
        return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
    }
    for span in &template.template_spans.nodes {
        let span = child(*span);
        let span_record = preflight_node(store, host, span)?;
        let NodeData::TemplateSpan(span_data) = &span_record.data else {
            return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
        };
        if span_record.parent != Some(expression.node) {
            return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
        }
        preflight_constant_expression(store, host, member, child(span_data.expression), span)?;
        let literal = child(span_data.literal);
        let literal_record = preflight_node(store, host, literal)?;
        if literal_record.parent != Some(span.node)
            || !matches!(
                literal_record.data,
                NodeData::TemplateMiddle(_) | NodeData::TemplateTail(_)
            )
        {
            return Err(invariant(EnumTypeInvariant::InvalidMember(member)));
        }
    }
    Ok(())
}

fn resolve_enum_entity(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    entity: NodeRef,
    enum_name: &str,
    previous_members: &[EnumMemberPlan],
) -> Option<Evaluation> {
    let record = preflight_node(store, host, entity).ok()?;
    let member_name = match &record.data {
        NodeData::Identifier(identifier) => identifier.text.as_str(),
        NodeData::PropertyAccessExpression(access) => {
            let base = host.node(NodeRef::new(entity.arena, entity.file, access.expression))?;
            let NodeData::Identifier(base) = &base.data else {
                return None;
            };
            if base.text != enum_name {
                return None;
            }
            let member = host.node(NodeRef::new(entity.arena, entity.file, access.name))?;
            let NodeData::Identifier(member) = &member.data else {
                return None;
            };
            member.text.as_str()
        }
        NodeData::ElementAccessExpression(access) => {
            let base = host.node(NodeRef::new(entity.arena, entity.file, access.expression))?;
            let NodeData::Identifier(base) = &base.data else {
                return None;
            };
            if base.text != enum_name {
                return None;
            }
            let argument = host.node(NodeRef::new(
                entity.arena,
                entity.file,
                access.argument_expression,
            ))?;
            match &argument.data {
                NodeData::StringLiteral(literal) => literal.text.as_str(),
                NodeData::NoSubstitutionTemplateLiteral(literal) => literal.text.as_str(),
                _ => return None,
            }
        }
        _ => return None,
    };
    let member = previous_members.iter().find(|member| {
        store
            .symbol(member.symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            == Some(member_name)
    });
    let Some(member) = member else {
        if matches!(record.data, NodeData::Identifier(_))
            && matches!(member_name, "NaN" | "Infinity")
        {
            let bound = host.bound_file(entity)?;
            let local_symbol = bound
                .locals(bound.source_file())
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source(member_name));
            let global_symbol = store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                .and_then(|globals| globals.get_source(member_name));
            if local_symbol.is_none() || local_symbol == global_symbol {
                return Some(Evaluation::known(Value::Number(Number::from_string(
                    member_name,
                ))));
            }
        }
        return None;
    };
    let value = match &member.value {
        CanonicalEnumMemberValue::Number(value) => Value::Number(*value),
        CanonicalEnumMemberValue::String(value) => Value::String(value.clone()),
        CanonicalEnumMemberValue::Computed => return None,
    };
    Some(Evaluation {
        metadata: EvaluationMetadata {
            is_syntactically_string: matches!(value, Value::String(_)),
            ..EvaluationMetadata::default()
        },
        outcome: EvaluationOutcome::Value(value),
    })
}

fn enum_state(
    store: &CanonicalTypeMapperStore,
    plan: &EnumPlan,
) -> Result<EnumState, EnumTypeError> {
    let owner_declared = store.declared_type_links(plan.symbol);
    let owner_value = store.value_symbol_links(plan.symbol);
    let node_links = store.node_links(plan.declaration);
    let members_are_cold = plan.members.iter().all(|member| {
        store
            .declared_type_links(member.symbol)
            .is_none_or(|links| links == &DeclaredTypeLinks::default())
            && store
                .value_symbol_links(member.symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
            && store
                .enum_member_links(member.declaration)
                .is_none_or(|links| links == &EnumMemberLinks::default())
    });
    let is_cold = owner_declared.is_none_or(|links| {
        links.declared_type.is_none()
            && !links.interface_checked
            && !links.index_signatures_checked
            && !links.type_parameters_checked
    }) && owner_value.is_none_or(|links| links == &ValueSymbolLinks::default())
        && node_links.is_none_or(|links| {
            !links.flags.contains(NodeCheckFlags::ENUM_VALUES_COMPUTED)
                && links.declaration_requires_scope_change
                    == NodeLinks::default().declaration_requires_scope_change
                && !links.has_reported_statement_in_ambient_context
        })
        && members_are_cold;
    if is_cold {
        return Ok(EnumState::Cold);
    }
    validate_resolved_enum(store, plan).map(|_| EnumState::Resolved)
}

fn validate_resolved_enum(
    store: &CanonicalTypeMapperStore,
    plan: &EnumPlan,
) -> Result<CanonicalEnumSemantics, EnumTypeError> {
    let cache_error = || invariant(EnumTypeInvariant::InvalidCache(plan.symbol));
    let declared_type = store
        .declared_type_links(plan.symbol)
        .filter(|links| {
            !links.interface_checked
                && !links.index_signatures_checked
                && !links.type_parameters_checked
        })
        .and_then(|links| links.declared_type)
        .ok_or_else(cache_error)?;
    let value_type = store
        .value_symbol_links(plan.symbol)
        .filter(|links| {
            **links
                == ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    ..ValueSymbolLinks::default()
                }
        })
        .and_then(|links| links.resolved_type)
        .ok_or_else(cache_error)?;
    validate_value_type(store, plan.symbol, value_type).ok_or_else(cache_error)?;
    if !store.node_links(plan.declaration).is_some_and(|links| {
        links.flags.contains(NodeCheckFlags::ENUM_VALUES_COMPUTED)
            && links.declaration_requires_scope_change
                == NodeLinks::default().declaration_requires_scope_change
            && !links.has_reported_statement_in_ambient_context
    }) {
        return Err(cache_error());
    }
    let mut members = Vec::<CanonicalEnumMemberSemantics>::with_capacity(plan.members.len());
    for (index, member) in plan.members.iter().enumerate() {
        let fresh_type = store
            .declared_type_links(member.symbol)
            .filter(|links| {
                **links
                    == DeclaredTypeLinks {
                        declared_type: links.declared_type,
                        ..DeclaredTypeLinks::default()
                    }
            })
            .and_then(|links| links.declared_type)
            .ok_or_else(cache_error)?;
        if store.value_symbol_links(member.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(fresh_type),
                ..ValueSymbolLinks::default()
            })
        {
            return Err(cache_error());
        }
        if !store
            .enum_member_links(member.declaration)
            .is_some_and(|links| evaluator_result_matches(&links.value, &member.value))
        {
            return Err(cache_error());
        }
        let identity_index = first_member_identity_index(&plan.members, index);
        let identity_symbol = plan.members[identity_index].symbol;
        let regular_type = validate_literal_pair(store, fresh_type, identity_symbol, &member.value)
            .ok_or_else(cache_error)?;
        if identity_index != index {
            let identity = &members[identity_index];
            if regular_type != identity.regular_type || fresh_type != identity.fresh_type {
                return Err(cache_error());
            }
        }
        members.push(CanonicalEnumMemberSemantics {
            declaration: member.declaration,
            symbol: member.symbol,
            regular_type,
            fresh_type,
            value: member.value.clone(),
        });
    }
    validate_declared_type(store, plan, declared_type, &members).ok_or_else(cache_error)?;
    Ok(CanonicalEnumSemantics {
        declaration: plan.declaration,
        symbol: plan.symbol,
        declared_type,
        value_type,
        members,
        is_const: plan.is_const,
        is_ambient: plan.is_ambient,
    })
}

fn validate_value_type(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    value_type: TypeId,
) -> Option<()> {
    let record = store.type_payload(value_type)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    (record.flags() == TypeFlags::OBJECT
        && record.object_flags() == ObjectFlags::ANONYMOUS
        && record.symbol() == Some(symbol)
        && record.alias().is_none()
        && object.structured == StructuredTypeData::default()
        && object.target.is_none()
        && object.mapper.is_none()
        && object.instantiations == TypeCacheState::Unallocated)
        .then_some(())
}

fn validate_literal_pair(
    store: &CanonicalTypeMapperStore,
    fresh: TypeId,
    symbol: SemanticSymbolId,
    value: &CanonicalEnumMemberValue,
) -> Option<TypeId> {
    let fresh_record = store.type_payload(fresh)?;
    let TypeData::Literal(fresh_data) = fresh_record.data() else {
        return None;
    };
    let regular = fresh_data.regular_type;
    let regular_record = store.type_payload(regular)?;
    let TypeData::Literal(regular_data) = regular_record.data() else {
        return None;
    };
    let (flags, literal) = literal_payload(value);
    (fresh != regular
        && fresh_record.flags() == flags
        && regular_record.flags() == flags
        && fresh_record.object_flags() == ObjectFlags::NONE
        && regular_record.object_flags() == ObjectFlags::NONE
        && fresh_record.symbol() == Some(symbol)
        && regular_record.symbol() == Some(symbol)
        && fresh_record.alias().is_none()
        && regular_record.alias().is_none()
        && enum_literal_values_match(&fresh_data.value, &literal)
        && enum_literal_values_match(&regular_data.value, &literal)
        && fresh_data.fresh_type == Some(fresh)
        && regular_data.fresh_type == Some(fresh)
        && regular_data.regular_type == regular)
        .then_some(regular)
}

fn enum_value_from_literal(value: &LiteralValue) -> Option<CanonicalEnumMemberValue> {
    match value {
        LiteralValue::Number(value) => Some(CanonicalEnumMemberValue::Number(*value)),
        LiteralValue::String(value) => Some(CanonicalEnumMemberValue::String(value.clone())),
        LiteralValue::ComputedEnum => Some(CanonicalEnumMemberValue::Computed),
        LiteralValue::Boolean(_) | LiteralValue::BigInt(_) => None,
    }
}

fn enum_literal_values_match(left: &LiteralValue, right: &LiteralValue) -> bool {
    match (left, right) {
        (LiteralValue::Number(left), LiteralValue::Number(right)) => {
            left == right || left.is_nan() && right.is_nan()
        }
        _ => left == right,
    }
}

fn enum_literal_values_share_cache_key(
    left: &CanonicalEnumMemberValue,
    right: &CanonicalEnumMemberValue,
) -> bool {
    match (left, right) {
        (CanonicalEnumMemberValue::Number(left), CanonicalEnumMemberValue::Number(right)) => {
            left == right || left.is_nan() && right.is_nan()
        }
        (CanonicalEnumMemberValue::String(left), CanonicalEnumMemberValue::String(right)) => {
            left == right
        }
        _ => false,
    }
}

fn first_member_identity_index(members: &[EnumMemberPlan], index: usize) -> usize {
    members[..index]
        .iter()
        .position(|member| {
            enum_literal_values_share_cache_key(&member.value, &members[index].value)
        })
        .unwrap_or(index)
}

fn validated_enum_literal_symbol(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<SemanticSymbolId> {
    let record = store.type_payload(type_)?;
    let TypeData::Literal(data) = record.data() else {
        return None;
    };
    let regular = data.regular_type;
    let TypeData::Literal(regular_data) = store.type_payload(regular)?.data() else {
        return None;
    };
    let fresh = regular_data.fresh_type?;
    let symbol = record.symbol()?;
    let value = enum_value_from_literal(&data.value)?;
    ((type_ == regular || type_ == fresh)
        && validate_literal_pair(store, fresh, symbol, &value) == Some(regular))
    .then_some(symbol)
}

/// Returns the pinned unqualified enum or enum-member display when `type_` is
/// a complete canonical enum identity.
pub(super) fn enum_type_display_name(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<String> {
    let record = store.type_payload(type_)?;
    if !record.flags().intersects(TypeFlags::ENUM_LIKE) {
        return None;
    }
    let symbol = record.symbol()?;
    let symbol_record = store.symbol(symbol)?;
    if symbol_record.flags() == SymbolFlags::ENUM_MEMBER {
        (validated_enum_literal_symbol(store, type_) == Some(symbol)).then_some(())?;
        let parent = symbol_record.parent()?;
        let parent_record = store.symbol(parent)?;
        parent_record
            .flags()
            .intersects(SymbolFlags::ENUM)
            .then_some(())?;
        return Some(format!(
            "{}.{}",
            parent_record.name().as_utf8()?,
            symbol_record.name().as_utf8()?
        ));
    }
    if !symbol_record.flags().intersects(SymbolFlags::ENUM) {
        return None;
    }
    if record.flags() == TypeFlags::ENUM {
        (validated_enum_literal_symbol(store, type_) == Some(symbol)).then_some(())?;
    } else {
        let TypeData::Union(union) = record.data() else {
            return None;
        };
        let alias = record.alias().and_then(|alias| store.type_alias(alias))?;
        if record.flags() != TypeFlags::UNION | TypeFlags::ENUM_LITERAL
            || record.object_flags() != ObjectFlags::PRIMITIVE_UNION
            || alias.symbol() != Some(symbol)
            || alias.type_arguments().is_some()
            || union.union.types.len() < 2
            || union.union.types.windows(2).any(|pair| pair[0] >= pair[1])
            || union
                != &(UnionTypeData {
                    union: UnionOrIntersectionTypeData {
                        types: union.union.types.clone(),
                        ..UnionOrIntersectionTypeData::default()
                    },
                    ..UnionTypeData::default()
                })
            || union.union.types.iter().any(|member| {
                validated_enum_literal_symbol(store, *member).is_none_or(|member_symbol| {
                    store
                        .symbol(member_symbol)
                        .is_none_or(|member| member.parent() != Some(symbol))
                })
            })
        {
            return None;
        }
    }
    Some(symbol_record.name().as_utf8()?.to_owned())
}

/// Returns the enum owner for one exact canonical enum or enum-member type.
pub(super) fn canonical_enum_type_owner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<SemanticSymbolId> {
    enum_type_display_name(store, type_)?;
    let symbol = store.type_payload(type_)?.symbol()?;
    let record = store.symbol(symbol)?;
    if record.flags() == SymbolFlags::ENUM_MEMBER {
        record.parent()
    } else {
        Some(symbol)
    }
}

/// Whether `type_` is an exact canonical enum union accepted by relation
/// traversal instead of the disjoint primitive-union cache validator.
pub(super) fn is_canonical_enum_union(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    store.type_payload(type_).is_some_and(|record| {
        record.flags() == TypeFlags::UNION | TypeFlags::ENUM_LITERAL
            && enum_type_display_name(store, type_).is_some()
    })
}

fn validate_declared_type(
    store: &CanonicalTypeMapperStore,
    plan: &EnumPlan,
    declared_type: TypeId,
    members: &[CanonicalEnumMemberSemantics],
) -> Option<()> {
    let expected_types = members
        .iter()
        .enumerate()
        .filter_map(|(index, member)| {
            (first_member_identity_index(&plan.members, index) == index)
                .then_some(member.regular_type)
        })
        .collect::<Vec<_>>();
    match expected_types.as_slice() {
        [] => {
            let record = store.type_payload(declared_type)?;
            let TypeData::Literal(data) = record.data() else {
                return None;
            };
            let fresh = data.fresh_type?;
            (validate_literal_pair(
                store,
                fresh,
                plan.symbol,
                &CanonicalEnumMemberValue::Computed,
            )? == declared_type)
                .then_some(())
        }
        [member] => (declared_type == *member).then_some(()),
        _ => {
            let record = store.type_payload(declared_type)?;
            let TypeData::Union(union) = record.data() else {
                return None;
            };
            let alias = record.alias().and_then(|alias| store.type_alias(alias))?;
            (record.flags() == TypeFlags::UNION | TypeFlags::ENUM_LITERAL
                && record.object_flags() == ObjectFlags::PRIMITIVE_UNION
                && record.symbol() == Some(plan.symbol)
                && alias.symbol() == Some(plan.symbol)
                && alias.type_arguments().is_none()
                && union
                    == &UnionTypeData {
                        union: UnionOrIntersectionTypeData {
                            types: expected_types,
                            ..UnionOrIntersectionTypeData::default()
                        },
                        ..UnionTypeData::default()
                    })
                .then_some(())
        }
    }
}

fn literal_payload(value: &CanonicalEnumMemberValue) -> (TypeFlags, LiteralValue) {
    match value {
        CanonicalEnumMemberValue::Number(value) => (
            TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::Number(*value),
        ),
        CanonicalEnumMemberValue::String(value) => (
            TypeFlags::STRING_LITERAL | TypeFlags::ENUM_LITERAL,
            LiteralValue::String(value.clone()),
        ),
        CanonicalEnumMemberValue::Computed => (TypeFlags::ENUM, LiteralValue::ComputedEnum),
    }
}

fn evaluator_result(value: &CanonicalEnumMemberValue) -> EvaluatorResult {
    EvaluatorResult {
        value: match value {
            CanonicalEnumMemberValue::Number(value) => Some(EvaluatorValue::Number(*value)),
            CanonicalEnumMemberValue::String(value) => Some(EvaluatorValue::String(value.clone())),
            CanonicalEnumMemberValue::Computed => None,
        },
        is_syntactically_string: matches!(value, CanonicalEnumMemberValue::String(_)),
        resolved_other_files: false,
        has_external_references: false,
    }
}

fn evaluator_result_matches(actual: &EvaluatorResult, expected: &CanonicalEnumMemberValue) -> bool {
    let value_matches = match (&actual.value, expected) {
        (Some(EvaluatorValue::Number(actual)), CanonicalEnumMemberValue::Number(expected)) => {
            actual == expected || actual.is_nan() && expected.is_nan()
        }
        (Some(EvaluatorValue::String(actual)), CanonicalEnumMemberValue::String(expected)) => {
            actual == expected
        }
        (None, CanonicalEnumMemberValue::Computed) => true,
        _ => false,
    };
    value_matches
        && actual.is_syntactically_string == matches!(expected, CanonicalEnumMemberValue::String(_))
        && !actual.resolved_other_files
        && !actual.has_external_references
}

fn alloc_literal_pair(
    store: &mut CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    value: &CanonicalEnumMemberValue,
) -> (TypeId, TypeId) {
    let (flags, literal) = literal_payload(value);
    let regular = store
        .alloc_literal_type(flags, literal.clone(), RegularLiteralLink::SelfType)
        .expect("reserved enum regular literal capacity and validated its flags");
    let fresh = store
        .alloc_literal_type(flags, literal, RegularLiteralLink::Type(regular))
        .expect("reserved enum fresh literal capacity and validated its regular type");
    assert!(store.set_literal_links(regular, Some(fresh), regular));
    assert!(store.set_literal_links(fresh, Some(fresh), regular));
    assert!(store.set_type_symbol(regular, Some(symbol)));
    assert!(store.set_type_symbol(fresh, Some(symbol)));
    (regular, fresh)
}

fn publish_enum(
    store: &mut CanonicalTypeMapperStore,
    plan: &EnumPlan,
) -> Result<CanonicalEnumSemantics, EnumTypeError> {
    let member_identity_count = plan
        .members
        .iter()
        .enumerate()
        .filter(|(index, _)| first_member_identity_index(&plan.members, *index) == *index)
        .count();
    let member_type_count = member_identity_count
        .checked_mul(2)
        .ok_or_else(|| invariant(EnumTypeInvariant::Capacity(plan.symbol)))?;
    let declared_type_count =
        usize::from(plan.members.is_empty()) * 2 + usize::from(member_identity_count >= 2);
    let type_count = member_type_count
        .checked_add(declared_type_count)
        .and_then(|count| count.checked_add(1))
        .ok_or_else(|| invariant(EnumTypeInvariant::Capacity(plan.symbol)))?;
    let alias_count = usize::from(member_identity_count >= 2);
    if !store.try_reserve_types(type_count) || !store.try_reserve_type_aliases(alias_count) {
        return Err(invariant(EnumTypeInvariant::Capacity(plan.symbol)));
    }

    let mut members = Vec::<CanonicalEnumMemberSemantics>::with_capacity(plan.members.len());
    for (index, member) in plan.members.iter().enumerate() {
        let identity_index = first_member_identity_index(&plan.members, index);
        let (regular_type, fresh_type) = if identity_index == index {
            alloc_literal_pair(store, member.symbol, &member.value)
        } else {
            let identity = &members[identity_index];
            (identity.regular_type, identity.fresh_type)
        };
        members.push(CanonicalEnumMemberSemantics {
            declaration: member.declaration,
            symbol: member.symbol,
            regular_type,
            fresh_type,
            value: member.value.clone(),
        });
    }
    let member_types = members
        .iter()
        .enumerate()
        .filter_map(|(index, member)| {
            (first_member_identity_index(&plan.members, index) == index)
                .then_some(member.regular_type)
        })
        .collect::<Vec<_>>();
    let declared_type = match member_types.as_slice() {
        [] => alloc_literal_pair(store, plan.symbol, &CanonicalEnumMemberValue::Computed).0,
        [member] => *member,
        _ => {
            let union = store
                .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, member_types)
                .expect("reserved enum union capacity and validated member identities");
            assert!(store.add_type_flags(union, TypeFlags::ENUM_LITERAL));
            assert!(store.set_type_symbol(union, Some(plan.symbol)));
            let alias = store
                .alloc_type_alias(Some(plan.symbol))
                .expect("reserved enum alias capacity and validated its symbol");
            assert!(store.set_type_alias(union, Some(alias)));
            union
        }
    };
    let value_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .expect("reserved enum value-object capacity and validated its symbol");

    let mut owner_declared_links = store
        .declared_type_links(plan.symbol)
        .cloned()
        .unwrap_or_default();
    owner_declared_links.declared_type = Some(declared_type);
    assert!(store.set_declared_type_links(plan.symbol, owner_declared_links));
    assert!(store.set_value_symbol_links(
        plan.symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        }
    ));
    let mut node_links = store
        .node_links(plan.declaration)
        .cloned()
        .unwrap_or_default();
    node_links.flags |= NodeCheckFlags::ENUM_VALUES_COMPUTED;
    assert!(store.set_node_links(plan.declaration, node_links));
    for member in &members {
        assert!(store.set_declared_type_links(
            member.symbol,
            DeclaredTypeLinks {
                declared_type: Some(member.fresh_type),
                ..DeclaredTypeLinks::default()
            }
        ));
        assert!(store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(member.fresh_type),
                ..ValueSymbolLinks::default()
            }
        ));
        assert!(store.set_enum_member_links(
            member.declaration,
            EnumMemberLinks {
                value: evaluator_result(&member.value),
            }
        ));
    }
    validate_resolved_enum(store, plan)
}

/// Plans, publishes, or validates one exact top-level literal enum.
///
/// The complete syntax/binder plan and cold/warm cache state are validated
/// before the first write. Unsupported and poisoned-cache errors are therefore
/// mutation-free. All fallible arena reservations precede publication.
pub(super) fn get_enum_semantics(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<CanonicalEnumSemantics, EnumTypeError> {
    let plan = plan_enum(store, host, symbol)?;
    match enum_state(store, &plan)? {
        EnumState::Cold => publish_enum(store, &plan),
        EnumState::Resolved => validate_resolved_enum(store, &plan),
    }
}

/// Declared-type dispatch seam for both enum owners and enum members.
pub(super) fn get_declared_enum_or_member(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, EnumTypeError> {
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or_else(|| invariant(EnumTypeInvariant::SymbolNotOwned(symbol)))?;
    let record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(EnumTypeInvariant::SymbolNotOwned(symbol)))?;
    if record.flags().intersects(SymbolFlags::ENUM) {
        return get_enum_semantics(store, host, symbol).map(|result| Some(result.declared_type));
    }
    if record.flags().contains(SymbolFlags::ENUM_MEMBER) {
        let parent = record
            .parent()
            .ok_or_else(|| invariant(EnumTypeInvariant::InvalidOwnerSymbol(symbol)))?;
        let result = get_enum_semantics(store, host, parent)?;
        return result
            .members
            .iter()
            .find(|member| member.symbol == symbol)
            .map(|member| Some(member.fresh_type))
            .ok_or_else(|| invariant(EnumTypeInvariant::InvalidMemberSymbol(result.declaration)));
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena, NodeData};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, mapper::TypeMapper, type_records::TypeRecord,
        type_to_string,
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn fixture(source: &str) -> Fixture {
        fixture_with_module_state(source, CanonicalModuleState::Script)
    }

    fn fixture_with_module_state(source: &str, module_state: CanonicalModuleState) -> Fixture {
        fixture_with_facts(source, module_state, false)
    }

    fn fixture_with_facts(
        source: &str,
        module_state: CanonicalModuleState,
        is_declaration_file: bool,
    ) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(43);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/enums.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    is_declaration_file,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new([(arena, bound)]).unwrap()
    }

    fn declaration_name<'a>(arena: &'a NodeArena, node: &ts_ast::Node) -> Option<&'a str> {
        let name = match &node.data {
            NodeData::EnumDeclaration(data) => data.name,
            NodeData::EnumMember(data) => data.name,
            _ => return None,
        };
        match &arena.get(name)?.data {
            NodeData::Identifier(identifier) => Some(&identifier.text),
            NodeData::StringLiteral(literal) => Some(&literal.text),
            _ => None,
        }
    }

    fn named_node(fixture: &Fixture, kind: SyntaxKind, name: &str) -> NodeRef {
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind && declaration_name(&fixture.parsed.arena, node) == Some(name))
                    .then_some(id)
            })
            .unwrap();
        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node)
    }

    fn symbol(fixture: &Fixture, kind: SyntaxKind, name: &str) -> SemanticSymbolId {
        fixture.files[&fixture.file]
            .symbol(named_node(fixture, kind, name))
            .unwrap()
    }

    fn member<'a>(
        result: &'a CanonicalEnumSemantics,
        fixture: &Fixture,
        name: &str,
    ) -> &'a CanonicalEnumMemberSemantics {
        let symbol = symbol(fixture, SyntaxKind::EnumMember, name);
        result
            .members
            .iter()
            .find(|member| member.symbol == symbol)
            .unwrap()
    }

    #[test]
    fn literal_enum_publishes_exact_type_value_member_graph_and_is_warm() {
        let mut fixture =
            fixture(r#"enum Mixed { Zero, Two = 2, Three, Negative = -1, Word = "word" }"#);
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Mixed");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();
        let alias_count = fixture.store.type_alias_len();

        let first = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(fixture.store.type_len(), type_count + 12);
        assert_eq!(fixture.store.type_alias_len(), alias_count + 1);
        assert!(!first.is_const);
        assert!(!first.is_ambient);
        assert_eq!(
            member(&first, &fixture, "Zero").value,
            CanonicalEnumMemberValue::Number(Number::new(0.0))
        );
        assert_eq!(
            member(&first, &fixture, "Two").value,
            CanonicalEnumMemberValue::Number(Number::new(2.0))
        );
        assert_eq!(
            member(&first, &fixture, "Three").value,
            CanonicalEnumMemberValue::Number(Number::new(3.0))
        );
        assert_eq!(
            member(&first, &fixture, "Negative").value,
            CanonicalEnumMemberValue::Number(Number::new(-1.0))
        );
        assert_eq!(
            member(&first, &fixture, "Word").value,
            CanonicalEnumMemberValue::String("word".to_owned())
        );
        let declared = fixture.store.type_payload(first.declared_type).unwrap();
        assert_eq!(declared.flags(), TypeFlags::UNION | TypeFlags::ENUM_LITERAL);
        assert_eq!(declared.symbol(), Some(owner));
        assert_eq!(
            type_to_string(&fixture.store, first.declared_type),
            Ok("Mixed".to_owned())
        );
        let value = fixture.store.type_payload(first.value_type).unwrap();
        assert_eq!(value.flags(), TypeFlags::OBJECT);
        assert_eq!(value.object_flags(), ObjectFlags::ANONYMOUS);
        assert_eq!(value.symbol(), Some(owner));
        for member in &first.members {
            assert_ne!(member.regular_type, member.fresh_type);
            assert_eq!(
                fixture
                    .store
                    .type_payload(member.regular_type)
                    .unwrap()
                    .symbol(),
                Some(member.symbol)
            );
            let member_name = fixture.store.symbol(member.symbol).unwrap().name();
            assert_eq!(
                type_to_string(&fixture.store, member.fresh_type),
                Ok(format!("Mixed.{}", member_name.as_utf8().unwrap()))
            );
            assert_eq!(
                fixture
                    .store
                    .type_payload(member.fresh_type)
                    .unwrap()
                    .symbol(),
                Some(member.symbol)
            );
            assert_eq!(
                fixture
                    .store
                    .is_type_assignable_to(member.fresh_type, first.declared_type),
                Ok(true)
            );
        }
        let state = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let mut checked_links = fixture.store.declared_type_links(owner).cloned().unwrap();
        checked_links.enum_checked = true;
        assert!(fixture.store.set_declared_type_links(owner, checked_links));
        let second = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(second, first);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
        let three = member(&first, &fixture, "Three");
        assert_eq!(
            get_declared_enum_or_member(&mut fixture.store, &host, three.symbol),
            Ok(Some(three.fresh_type))
        );
    }

    #[test]
    fn quoted_enum_member_names_publish_and_resolve_through_element_access() {
        let mut fixture = fixture(concat!(
            "enum Named { ",
            "'non identifier' = 1, ",
            "'//' = 2, ",
            "'-Infinity' = 3, ",
            "NaN = 4, ",
            "Infinity = 5, ",
            "Copied = Named['non identifier'], ",
            "}",
        ));
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Named");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        for (name, expected) in [
            ("non identifier", 1.0),
            ("//", 2.0),
            ("-Infinity", 3.0),
            ("NaN", 4.0),
            ("Infinity", 5.0),
            ("Copied", 1.0),
        ] {
            assert_eq!(
                member(&result, &fixture, name).value,
                CanonicalEnumMemberValue::Number(Number::new(expected)),
                "member {name}",
            );
        }
        assert_eq!(
            member(&result, &fixture, "Copied").fresh_type,
            member(&result, &fixture, "non identifier").fresh_type
        );
    }

    #[test]
    fn canonical_numeric_quoted_names_report_ts2452_without_rejecting_members() {
        let mut fixture = fixture(concat!(
            "enum Names { ",
            "'1' = 0, ",
            "'-1' = 1, ",
            "'01' = 2, ",
            "'1.0' = 3, ",
            "'Infinity' = 4, ",
            "'-Infinity' = 5, ",
            "'NaN' = 6, ",
            "}",
        ));
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Names");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let diagnostics = preflight_enum_diagnostics(&fixture.store, &host, owner).unwrap();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2452, 2452]
        );
        for diagnostic in diagnostics {
            assert_eq!(
                fixture.parsed.arena.get(diagnostic.node.node).unwrap().kind,
                SyntaxKind::StringLiteral
            );
        }

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(result.members.len(), 7);
    }

    #[test]
    fn constant_expressions_resolve_prior_members_and_preserve_cached_identities() {
        let mut fixture = fixture(concat!(
            "enum Flags { ",
            "One = 1, ",
            "Two = One << 1, ",
            "Four = Flags.Two * 2, ",
            "Mask = Four | One, ",
            "Inverted = ~Mask, ",
            "Power = (1 + 2) ** 2, ",
            "Copied = Flags['One'], ",
            "Separated = 1_000 + One, ",
            "Word = 'flag' + Flags.One, ",
            "Label = `value-${Flags['Two']}`, ",
            "}",
        ));
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Flags");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let first = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();

        for (name, value) in [
            ("One", 1.0),
            ("Two", 2.0),
            ("Four", 4.0),
            ("Mask", 5.0),
            ("Inverted", -6.0),
            ("Power", 9.0),
            ("Copied", 1.0),
            ("Separated", 1_001.0),
        ] {
            let member = member(&first, &fixture, name);
            assert_eq!(
                member.value,
                CanonicalEnumMemberValue::Number(Number::new(value))
            );
            assert!(
                !fixture
                    .store
                    .enum_member_links(member.declaration)
                    .unwrap()
                    .value
                    .is_syntactically_string
            );
        }
        for (name, value) in [("Word", "flag1"), ("Label", "value-2")] {
            let member = member(&first, &fixture, name);
            assert_eq!(
                member.value,
                CanonicalEnumMemberValue::String(value.to_owned())
            );
            assert!(
                fixture
                    .store
                    .enum_member_links(member.declaration)
                    .unwrap()
                    .value
                    .is_syntactically_string
            );
        }
        let one = member(&first, &fixture, "One");
        let copied = member(&first, &fixture, "Copied");
        assert_eq!(copied.regular_type, one.regular_type);
        assert_eq!(copied.fresh_type, one.fresh_type);

        let warm = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, owner),
            Ok(first)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn forward_references_and_non_constant_expression_forms_are_atomic() {
        for (source, name) in [
            ("enum Forward { First = Later, Later = 1 }", "Forward"),
            ("enum Outside { First = external + 1 }", "Outside"),
            ("enum Condition { First = true ? 1 : 2 }", "Condition"),
            ("enum Assertion { First = 1 as number }", "Assertion"),
            ("enum Optional { First = Optional?.First }", "Optional"),
        ] {
            let mut fixture = fixture(source);
            let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, name);
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    get_enum_semantics(&mut fixture.store, &host, owner),
                    Err(EnumTypeError::Unsupported(
                        EnumTypeUnsupported::Initializer(_)
                    ))
                ),
                "unexpected result for {source}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.type_alias_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before
            );
        }
    }

    #[test]
    fn computed_nan_values_share_one_enum_identity_and_validate_warm_caches() {
        let mut fixture = fixture(concat!(
            "enum Exceptional { ",
            "First = 0 / 0, ",
            "Again = 0 / 0, ",
            "Positive = 1 / 0, ",
            "Negative = -1 / 0, ",
            "}",
        ));
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Exceptional");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let first = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        let first_nan = member(&first, &fixture, "First");
        let second_nan = member(&first, &fixture, "Again");
        assert!(matches!(
            first_nan.value,
            CanonicalEnumMemberValue::Number(value) if value.is_nan()
        ));
        assert_eq!(second_nan.regular_type, first_nan.regular_type);
        assert_eq!(second_nan.fresh_type, first_nan.fresh_type);
        for name in ["Positive", "Negative"] {
            assert!(matches!(
                member(&first, &fixture, name).value,
                CanonicalEnumMemberValue::Number(value) if value.is_infinite()
            ));
        }

        let warm = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let replay = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(replay.declared_type, first.declared_type);
        assert_eq!(replay.value_type, first.value_type);
        assert_eq!(replay.members[0].fresh_type, first_nan.fresh_type);
        assert_eq!(replay.members[1].fresh_type, first_nan.fresh_type);
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn global_nan_and_infinity_identifiers_keep_pinned_enum_identities() {
        let mut fixture = fixture(concat!(
            "enum Exceptional { ",
            "First = -NaN, ",
            "Again = NaN, ",
            "Positive = Infinity, ",
            "Negative = -Infinity, ",
            "}",
        ));
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Exceptional");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        let first = member(&result, &fixture, "First");
        let again = member(&result, &fixture, "Again");
        assert!(matches!(
            first.value,
            CanonicalEnumMemberValue::Number(value) if value.is_nan()
        ));
        assert_eq!(first.regular_type, again.regular_type);
        assert_eq!(first.fresh_type, again.fresh_type);
        assert_eq!(
            member(&result, &fixture, "Positive").value,
            CanonicalEnumMemberValue::Number(Number::infinity(1))
        );
        assert_eq!(
            member(&result, &fixture, "Negative").value,
            CanonicalEnumMemberValue::Number(Number::infinity(-1))
        );
        assert!(
            preflight_enum_diagnostics(&fixture.store, &host, owner)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn ambient_computed_initializers_publish_values_and_retain_ts1066() {
        let mut fixture =
            fixture("declare enum Ambient { Numeric = 4.23, Computed = 'foo'.length }");
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Ambient");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let diagnostics = preflight_enum_diagnostics(&fixture.store, &host, owner).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, 1066);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(diagnostics[0].node.node)
                .unwrap()
                .kind,
            SyntaxKind::PropertyAccessExpression
        );

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(
            member(&result, &fixture, "Numeric").value,
            CanonicalEnumMemberValue::Number(Number::new(4.23))
        );
        assert_eq!(
            member(&result, &fixture, "Computed").value,
            CanonicalEnumMemberValue::Computed
        );
        assert_eq!(
            preflight_enum_diagnostics(&fixture.store, &host, owner),
            Ok(diagnostics)
        );
    }

    #[test]
    fn invalid_const_initializers_retain_pinned_values_and_diagnostics() {
        let mut fixture = fixture(concat!(
            "const enum Invalid { ",
            "Positive = 1 / 0, ",
            "Negative = -1 / 0, ",
            "NotANumber = 0 / 0, ",
            "Unknown = external, ",
            "}",
        ));
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Invalid");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let diagnostics = preflight_enum_diagnostics(&fixture.store, &host, owner).unwrap();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2477, 2477, 2478, 2474]
        );

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(
            member(&result, &fixture, "Positive").value,
            CanonicalEnumMemberValue::Number(Number::infinity(1))
        );
        assert_eq!(
            member(&result, &fixture, "Negative").value,
            CanonicalEnumMemberValue::Number(Number::infinity(-1))
        );
        assert!(matches!(
            member(&result, &fixture, "NotANumber").value,
            CanonicalEnumMemberValue::Number(value) if value.is_nan()
        ));
        assert_eq!(
            member(&result, &fixture, "Unknown").value,
            CanonicalEnumMemberValue::Computed
        );
    }

    #[test]
    fn missing_initializer_after_string_publishes_computed_member_and_ts1061() {
        let mut fixture = fixture("enum Broken { First = 'value', Second }");
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Broken");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let diagnostics = preflight_enum_diagnostics(&fixture.store, &host, owner).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, 1061);

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(
            member(&result, &fixture, "Second").value,
            CanonicalEnumMemberValue::Computed
        );
    }

    #[test]
    fn duplicate_literal_values_share_first_identity_in_source_order_and_are_warm() {
        let mut fixture = fixture(
            r#"
                enum Aliased {
                    First = 7,
                    Second = 7,
                    Word = "word",
                    WordAgain = "word",
                    AutoTarget = 9,
                    AutoBase = 8,
                    AutoDuplicate,
                }
            "#,
        );
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Aliased");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();
        let alias_count = fixture.store.type_alias_len();

        let cold = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert_eq!(fixture.store.type_len(), type_count + 10);
        assert_eq!(fixture.store.type_alias_len(), alias_count + 1);
        let first = member(&cold, &fixture, "First");
        let second = member(&cold, &fixture, "Second");
        let word = member(&cold, &fixture, "Word");
        let word_again = member(&cold, &fixture, "WordAgain");
        let auto_target = member(&cold, &fixture, "AutoTarget");
        let auto_base = member(&cold, &fixture, "AutoBase");
        let auto_duplicate = member(&cold, &fixture, "AutoDuplicate");

        for (identity, duplicate) in [
            (first, second),
            (word, word_again),
            (auto_target, auto_duplicate),
        ] {
            assert_eq!(duplicate.regular_type, identity.regular_type);
            assert_eq!(duplicate.fresh_type, identity.fresh_type);
            assert_ne!(duplicate.symbol, identity.symbol);
            assert_eq!(
                fixture
                    .store
                    .type_payload(duplicate.regular_type)
                    .unwrap()
                    .symbol(),
                Some(identity.symbol)
            );
            assert_eq!(
                fixture
                    .store
                    .declared_type_links(duplicate.symbol)
                    .and_then(|links| links.declared_type),
                Some(identity.fresh_type)
            );
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(duplicate.symbol)
                    .and_then(|links| links.resolved_type),
                Some(identity.fresh_type)
            );
            assert_eq!(
                fixture
                    .store
                    .enum_member_links(duplicate.declaration)
                    .unwrap()
                    .value,
                evaluator_result(&duplicate.value)
            );
            assert_eq!(
                get_declared_enum_or_member(&mut fixture.store, &host, duplicate.symbol),
                Ok(Some(identity.fresh_type))
            );
        }
        assert_eq!(
            type_to_string(&fixture.store, second.fresh_type),
            Ok("Aliased.First".to_owned())
        );
        assert_eq!(
            type_to_string(&fixture.store, word_again.fresh_type),
            Ok("Aliased.Word".to_owned())
        );
        assert_eq!(
            type_to_string(&fixture.store, auto_duplicate.fresh_type),
            Ok("Aliased.AutoTarget".to_owned())
        );

        let TypeData::Union(union) = fixture
            .store
            .type_payload(cold.declared_type)
            .unwrap()
            .data()
        else {
            panic!("four first-occurrence identities must form an enum union")
        };
        assert_eq!(
            union.union.types,
            vec![
                first.regular_type,
                word.regular_type,
                auto_target.regular_type,
                auto_base.regular_type,
            ]
        );

        let warm_state = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, owner),
            Ok(cold)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm_state
        );
    }

    #[test]
    fn duplicate_only_enum_collapses_to_the_first_member_without_an_alias() {
        let mut fixture = fixture(r#"enum Same { First = "same", Second = "same" }"#);
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Same");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let type_count = fixture.store.type_len();
        let alias_count = fixture.store.type_alias_len();

        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        let first = member(&result, &fixture, "First");
        let second = member(&result, &fixture, "Second");
        assert_eq!(fixture.store.type_len(), type_count + 3);
        assert_eq!(fixture.store.type_alias_len(), alias_count);
        assert_eq!(result.declared_type, first.regular_type);
        assert_eq!(second.regular_type, first.regular_type);
        assert_eq!(second.fresh_type, first.fresh_type);
        assert_eq!(
            type_to_string(&fixture.store, result.declared_type),
            Ok("Same.First".to_owned())
        );
    }

    #[test]
    fn warm_duplicate_cache_rejects_a_separate_valid_pair_atomically() {
        let mut fixture = fixture("enum Reused { First = 1, Second = 1, Other = 2 }");
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Reused");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let published = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        let first = member(&published, &fixture, "First").clone();
        let second = member(&published, &fixture, "Second").clone();
        assert!(fixture.store.try_reserve_types(2));
        let (_, separate_fresh) =
            alloc_literal_pair(&mut fixture.store, second.symbol, &second.value);
        assert!(fixture.store.set_declared_type_links(
            second.symbol,
            DeclaredTypeLinks {
                declared_type: Some(separate_fresh),
                ..DeclaredTypeLinks::default()
            }
        ));
        assert!(fixture.store.set_value_symbol_links(
            second.symbol,
            ValueSymbolLinks {
                resolved_type: Some(separate_fresh),
                ..ValueSymbolLinks::default()
            }
        ));
        let poisoned_state = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, owner),
            Err(EnumTypeError::Invariant(EnumTypeInvariant::InvalidCache(
                owner
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned_state
        );

        assert!(fixture.store.set_declared_type_links(
            second.symbol,
            DeclaredTypeLinks {
                declared_type: Some(first.fresh_type),
                ..DeclaredTypeLinks::default()
            }
        ));
        assert!(fixture.store.set_value_symbol_links(
            second.symbol,
            ValueSymbolLinks {
                resolved_type: Some(first.fresh_type),
                ..ValueSymbolLinks::default()
            }
        ));
        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, owner),
            Ok(published)
        );
    }

    #[test]
    fn const_and_ambient_flags_control_uninitialized_member_values_exactly() {
        let mut fixture = fixture_with_module_state(
            r#"
                export declare const enum Flags { A, B = "b" }
                export declare enum Ambient { X, Y = 4, Z }
                export declare enum Empty {}
            "#,
            CanonicalModuleState::External,
        );
        for (name, is_const) in [("Flags", true), ("Ambient", false)] {
            let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, name);
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
            assert_eq!(result.is_const, is_const);
            assert!(result.is_ambient);
        }
        let flags_owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Flags");
        let ambient_owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Ambient");
        let empty_owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Empty");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let flags = get_enum_semantics(&mut fixture.store, &host, flags_owner).unwrap();
        let ambient = get_enum_semantics(&mut fixture.store, &host, ambient_owner).unwrap();
        let empty = get_enum_semantics(&mut fixture.store, &host, empty_owner).unwrap();
        assert_eq!(
            member(&flags, &fixture, "A").value,
            CanonicalEnumMemberValue::Number(Number::new(0.0))
        );
        assert_eq!(
            member(&flags, &fixture, "B").value,
            CanonicalEnumMemberValue::String("b".to_owned())
        );
        for name in ["X", "Z"] {
            let member = member(&ambient, &fixture, name);
            assert_eq!(member.value, CanonicalEnumMemberValue::Computed);
            assert_eq!(
                fixture
                    .store
                    .type_payload(member.regular_type)
                    .unwrap()
                    .flags(),
                TypeFlags::ENUM
            );
            assert_eq!(
                fixture
                    .store
                    .enum_member_links(member.declaration)
                    .unwrap()
                    .value
                    .value,
                None
            );
        }
        assert_eq!(
            member(&ambient, &fixture, "Y").value,
            CanonicalEnumMemberValue::Number(Number::new(4.0))
        );
        assert!(empty.members.is_empty());
        let empty_record = fixture.store.type_payload(empty.declared_type).unwrap();
        assert_eq!(empty_record.flags(), TypeFlags::ENUM);
        assert_eq!(empty_record.symbol(), Some(empty_owner));
        assert_eq!(
            type_to_string(&fixture.store, empty.declared_type),
            Ok("Empty".to_owned())
        );
    }

    #[test]
    fn declaration_file_enum_is_implicitly_ambient() {
        let mut fixture = fixture_with_facts(
            "enum Ambient { First, Second = 2 }",
            CanonicalModuleState::External,
            true,
        );
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Ambient");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let result = get_enum_semantics(&mut fixture.store, &host, owner).unwrap();
        assert!(result.is_ambient);
        assert_eq!(
            member(&result, &fixture, "First").value,
            CanonicalEnumMemberValue::Computed
        );
        assert_eq!(
            member(&result, &fixture, "Second").value,
            CanonicalEnumMemberValue::Number(Number::new(2.0))
        );
    }

    #[test]
    fn unsupported_and_poisoned_enum_queries_are_atomic() {
        let mut fixture = fixture(
            r"
                enum Computed { A = runtime }
                enum Good { A }
            ",
        );
        let computed = symbol(&fixture, SyntaxKind::EnumDeclaration, "Computed");
        let good = symbol(&fixture, SyntaxKind::EnumDeclaration, "Good");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let initial = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(matches!(
            get_enum_semantics(&mut fixture.store, &host, computed),
            Err(EnumTypeError::Unsupported(
                EnumTypeUnsupported::Initializer(_)
            ))
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            initial
        );

        let published = get_enum_semantics(&mut fixture.store, &host, good).unwrap();
        let owner_links = fixture.store.value_symbol_links(good).cloned().unwrap();
        let member = &published.members[0];
        assert!(fixture.store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(published.value_type),
                ..ValueSymbolLinks::default()
            }
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, good),
            Err(EnumTypeError::Invariant(EnumTypeInvariant::InvalidCache(
                good
            )))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
        assert!(fixture.store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(member.fresh_type),
                ..ValueSymbolLinks::default()
            }
        ));
        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, good),
            Ok(published)
        );
        assert_eq!(fixture.store.value_symbol_links(good), Some(&owner_links));
    }

    #[test]
    fn enum_merges_stay_an_explicit_atomic_boundary() {
        let mut fixture = fixture("enum Merged { A } enum Merged { B }");
        let owner = symbol(&fixture, SyntaxKind::EnumDeclaration, "Merged");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let state = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_enum_semantics(&mut fixture.store, &host, owner),
            Err(EnumTypeError::Unsupported(
                EnumTypeUnsupported::MergedDeclarations(owner)
            ))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
    }
}
