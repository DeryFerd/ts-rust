//! Exact read-only source integration for direct `receiver[index]` access.
//!
//! This is the dependency-closed expression prefix of pinned
//! `checkElementAccessExpression` plus `getPropertyTypeForIndexType`. It
//! supports canonical `any`, direct `Array<T>`/`ReadonlyArray<T>` references,
//! required own properties selected by string or number literals, primitive
//! string indexing, and resolved anonymous string/number index signatures.
//! Optional chains, writes, tuples, unions, generic indexed access types, and
//! apparent/global property lookup stay typed boundaries.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{InternalSymbolName, SemanticSymbolId};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    ArrayTypeError, CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    SymbolNodeLinks, TypeDisplayUnavailable, TypeId, TypeNodeLinks,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    formatter::{
        type_to_string_with_host_and_flags, type_to_string_with_host_global_types_and_flags,
    },
    source::{PlannedExpression, PlannedExpressionKind},
    type_records::{LiteralValue, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

/// Source element syntax or semantic families outside this exact read slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceElementUnsupported {
    Access(NodeRef),
    Receiver(NodeRef),
    Index(NodeRef),
    MemberCall(NodeRef),
    Write(NodeRef),
    IndexType(TypeId),
    OptionalProperty {
        node: NodeRef,
        property: SemanticSymbolId,
    },
    IndexSignatureSurface(TypeId),
}

/// Exact indexed-access planning or checking failure without a guessed type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceElementError {
    Unsupported(SourceElementUnsupported),
    InvalidCache(NodeRef),
    InvalidType(TypeId),
    Relation(RelationUnavailable),
    Array(ArrayTypeError),
    Literal(LiteralTypeCacheError),
    Display(TypeDisplayUnavailable),
    MissingDiagnostic(u32),
}

impl From<RelationUnavailable> for SourceElementError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<ArrayTypeError> for SourceElementError {
    fn from(error: ArrayTypeError) -> Self {
        Self::Array(error)
    }
}

impl From<LiteralTypeCacheError> for SourceElementError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Literal(error)
    }
}

impl From<TypeDisplayUnavailable> for SourceElementError {
    fn from(error: TypeDisplayUnavailable) -> Self {
        Self::Display(error)
    }
}

impl std::fmt::Display for SourceElementError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(error) => {
                write!(formatter, "source element access is unsupported: {error:?}")
            }
            Self::InvalidCache(node) => {
                write!(formatter, "source element cache is invalid at {node:?}")
            }
            Self::InvalidType(type_) => {
                write!(formatter, "source element type is invalid: {type_:?}")
            }
            Self::Relation(error) => error.fmt(formatter),
            Self::Array(error) => error.fmt(formatter),
            Self::Literal(error) => write!(formatter, "source element literal failed: {error:?}"),
            Self::Display(error) => error.fmt(formatter),
            Self::MissingDiagnostic(code) => {
                write!(formatter, "source element diagnostic TS{code} is missing")
            }
        }
    }
}

impl std::error::Error for SourceElementError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::Array(error) => Some(error),
            Self::Display(error) => Some(error),
            Self::Unsupported(_)
            | Self::InvalidCache(_)
            | Self::InvalidType(_)
            | Self::Literal(_)
            | Self::MissingDiagnostic(_) => None,
        }
    }
}

/// Element-access syntax proven before either child is recursively planned.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectSourceElementSyntax {
    node: NodeRef,
    receiver: NodeRef,
    index: NodeRef,
}

impl DirectSourceElementSyntax {
    pub(super) const fn receiver(self) -> NodeRef {
        self.receiver
    }

    pub(super) const fn index(self) -> NodeRef {
        self.index
    }
}

/// Fully planned direct read with both recursive expression children retained.
#[derive(Clone, Debug)]
pub(super) struct SourceElementPlan {
    pub(super) node: NodeRef,
    pub(super) receiver: PlannedExpression,
    pub(super) index: PlannedExpression,
}

/// Exact result and retryable diagnostic publication for one element read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceElement {
    pub(super) type_: TypeId,
    pub(super) diagnostic: Option<CanonicalCheckerDiagnostic>,
}

/// Proves a non-optional, read-only element-access AST and its existing cache
/// shape before recursive source planning begins.
pub(super) fn plan_direct_source_element_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourceElementSyntax, SourceElementError> {
    let Some(record) = arena.get(node.node) else {
        return Err(unsupported_access(node));
    };
    let NodeData::ElementAccessExpression(access) = &record.data else {
        return Err(unsupported_access(node));
    };
    if record.kind != SyntaxKind::ElementAccessExpression
        || record.flags.0 != 0
        || access.flow_node.is_some()
        || access.question_dot_token.is_some()
        || access.facts != 0
    {
        return Err(unsupported_access(node));
    }

    if let Some(parent) = record.parent
        && let Some(parent_record) = arena.get(parent)
        && let NodeData::CallExpression(call) = &parent_record.data
        && call.expression == node.node
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::MemberCall(NodeRef::new(node.arena, node.file, parent)),
        ));
    }
    if let Some(parent) = record.parent
        && let Some(parent_record) = arena.get(parent)
        && let NodeData::BinaryExpression(binary) = &parent_record.data
        && binary.left == node.node
        && arena
            .get(binary.operator_token)
            .is_some_and(|operator| operator.kind.is_assignment_operator())
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Write(node),
        ));
    }

    let receiver = NodeRef::new(node.arena, node.file, access.expression);
    let index = NodeRef::new(node.arena, node.file, access.argument_expression);
    if arena
        .get(receiver.node)
        .is_none_or(|child| child.parent != Some(node.node))
        || arena
            .get(index.node)
            .is_none_or(|child| child.parent != Some(node.node))
    {
        return Err(unsupported_access(node));
    }

    preflight_element_links(store, node)?;
    Ok(DirectSourceElementSyntax {
        node,
        receiver,
        index,
    })
}

/// Joins proven syntax to the source planner's recursively validated children.
pub(super) fn finish_direct_source_element_plan(
    syntax: DirectSourceElementSyntax,
    receiver: PlannedExpression,
    index: PlannedExpression,
) -> Result<SourceElementPlan, SourceElementError> {
    if receiver.node != syntax.receiver
        || !matches!(receiver.kind, PlannedExpressionKind::Identifier(_))
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Receiver(syntax.receiver),
        ));
    }
    if index.node != syntax.index
        || !matches!(
            index.kind,
            PlannedExpressionKind::Null
                | PlannedExpressionKind::String(_)
                | PlannedExpressionKind::Number { .. }
                | PlannedExpressionKind::BigInt { .. }
                | PlannedExpressionKind::Boolean(_)
                | PlannedExpressionKind::GlobalUndefined
                | PlannedExpressionKind::Identifier(_)
        )
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Index(syntax.index),
        ));
    }
    Ok(SourceElementPlan {
        node: syntax.node,
        receiver,
        index,
    })
}

/// Checks one direct source read with the production global identities.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_element(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    check_direct_source_element_worker(
        store,
        host,
        Some(global_types),
        CanonicalArrayTargets::from_global_types(global_types),
        options,
        plan,
        receiver_type,
        index_type,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn check_direct_source_element_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    array_targets: CanonicalArrayTargets,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    check_direct_source_element_worker(
        store,
        host,
        None,
        array_targets,
        options,
        plan,
        receiver_type,
        index_type,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_direct_source_element_worker(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    array_targets: CanonicalArrayTargets,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    if store.type_payload(receiver_type).is_none() {
        return Err(SourceElementError::InvalidType(receiver_type));
    }
    let index = classify_index(store, index_type)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let any = bootstrap.any_type;
    let error = bootstrap.error_type;
    let string = bootstrap.string_type;

    let resolution = if matches!(index.shape, IndexShape::Invalid) {
        ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
    } else if receiver_type == any {
        ElementResolution::success(any, None)
    } else if let Some(array) =
        store.canonical_array_reference_with_targets(array_targets, receiver_type)?
    {
        if index.is_number_applicable() {
            ElementResolution::success(array.element_type, None)
        } else if index.is_string_or_number() {
            ElementResolution::diagnostic(error, ElementDiagnostic::NumberIndexRequired)
        } else {
            ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
        }
    } else if is_string_receiver(store, receiver_type)? {
        if index.is_number_applicable() {
            ElementResolution::success(string, None)
        } else if index.is_string_or_number() {
            ElementResolution::diagnostic(error, ElementDiagnostic::NumberIndexRequired)
        } else {
            ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
        }
    } else {
        resolve_object_element(store, plan, receiver_type, &index, any, error)?
    };

    let diagnostic = prepare_element_diagnostic(
        store,
        host,
        global_types,
        options,
        plan,
        receiver_type,
        index_type,
        resolution.diagnostic,
    )?;
    publish_element_links(store, plan.node, resolution.property, resolution.type_)?;
    Ok(CheckedSourceElement {
        type_: resolution.type_,
        diagnostic,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IndexShape {
    Any,
    String,
    Number,
    Literal { numeric_name: bool },
    Invalid,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassifiedIndex {
    shape: IndexShape,
    property_name: Option<String>,
}

impl ClassifiedIndex {
    fn is_number_applicable(&self) -> bool {
        matches!(
            self.shape,
            IndexShape::Any | IndexShape::Number | IndexShape::Literal { numeric_name: true }
        )
    }

    fn is_string_or_number(&self) -> bool {
        !matches!(self.shape, IndexShape::Invalid)
    }
}

fn classify_index(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
) -> Result<ClassifiedIndex, SourceElementError> {
    let record = store
        .type_payload(index_type)
        .ok_or(SourceElementError::InvalidType(index_type))?;
    let flags = record.flags();
    if flags.intersects(TypeFlags::FRESHABLE) {
        store.validate_union_constituent(index_type)?;
    }
    if flags == TypeFlags::STRING {
        return Ok(ClassifiedIndex {
            shape: IndexShape::String,
            property_name: None,
        });
    }
    if flags == TypeFlags::NUMBER {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Number,
            property_name: None,
        });
    }
    if flags == TypeFlags::ANY {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Any,
            property_name: None,
        });
    }
    if flags.intersects(
        TypeFlags::ES_SYMBOL
            | TypeFlags::UNIQUE_ES_SYMBOL
            | TypeFlags::UNION
            | TypeFlags::INTERSECTION
            | TypeFlags::TYPE_PARAMETER
            | TypeFlags::INDEX
            | TypeFlags::INDEXED_ACCESS
            | TypeFlags::CONDITIONAL
            | TypeFlags::SUBSTITUTION,
    ) {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexType(index_type),
        ));
    }
    let TypeData::Literal(literal) = record.data() else {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Invalid,
            property_name: None,
        });
    };
    let name = match &literal.value {
        LiteralValue::String(value) if flags == TypeFlags::STRING_LITERAL => value.clone(),
        LiteralValue::Number(value) if flags == TypeFlags::NUMBER_LITERAL => value.to_string(),
        _ => {
            return Ok(ClassifiedIndex {
                shape: IndexShape::Invalid,
                property_name: None,
            });
        }
    };
    Ok(ClassifiedIndex {
        shape: IndexShape::Literal {
            numeric_name: is_numeric_literal_name(&name),
        },
        property_name: Some(name),
    })
}

fn is_numeric_literal_name(name: &str) -> bool {
    ts_jsnum::from_string(name).to_string() == name
}

fn is_string_receiver(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
) -> Result<bool, SourceElementError> {
    let record = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    if record.flags().intersects(TypeFlags::STRING_LITERAL) {
        store.validate_union_constituent(receiver_type)?;
    }
    Ok(matches!(
        record.flags(),
        TypeFlags::STRING | TypeFlags::STRING_LITERAL
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ElementDiagnostic {
    NumberIndexRequired,
    InvalidIndexType,
    MissingLiteralProperty,
    MissingBroadIndex,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ElementResolution {
    type_: TypeId,
    property: Option<SemanticSymbolId>,
    diagnostic: Option<ElementDiagnostic>,
}

impl ElementResolution {
    const fn success(type_: TypeId, property: Option<SemanticSymbolId>) -> Self {
        Self {
            type_,
            property,
            diagnostic: None,
        }
    }

    const fn diagnostic(type_: TypeId, diagnostic: ElementDiagnostic) -> Self {
        Self {
            type_,
            property: None,
            diagnostic: Some(diagnostic),
        }
    }
}

fn resolve_object_element(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    any_type: TypeId,
    error_type: TypeId,
) -> Result<ElementResolution, SourceElementError> {
    if matches!(index.shape, IndexShape::Invalid) {
        return Ok(ElementResolution::diagnostic(
            error_type,
            ElementDiagnostic::InvalidIndexType,
        ));
    }

    if let Some(name) = index.property_name.as_deref() {
        match store.resolved_own_property(receiver_type, name) {
            Ok(Some(property)) => {
                if property.optional {
                    return Err(SourceElementError::Unsupported(
                        SourceElementUnsupported::OptionalProperty {
                            node: plan.node,
                            property: property.symbol,
                        },
                    ));
                }
                return Ok(ElementResolution::success(
                    property.type_,
                    Some(property.symbol),
                ));
            }
            Ok(None) => {}
            Err(RelationUnavailable::StructuredIndexInfos(_)) => {}
            Err(error) => return Err(error.into()),
        }
    }

    if let Some(signatures) = resolved_index_signature_surface(store, receiver_type)? {
        let selected = if matches!(index.shape, IndexShape::Any) {
            signatures.string.or(signatures.number)
        } else if index.is_number_applicable() {
            signatures.number.or(signatures.string)
        } else {
            signatures.string
        };
        if let Some(value) = selected {
            return Ok(ElementResolution::success(value, None));
        }
        return Ok(ElementResolution::diagnostic(
            error_type,
            if signatures.number.is_some() {
                ElementDiagnostic::NumberIndexRequired
            } else {
                ElementDiagnostic::MissingBroadIndex
            },
        ));
    }

    if matches!(index.shape, IndexShape::Any) {
        return Ok(ElementResolution::success(any_type, None));
    }

    // A broad key has no concrete property to query, but this missing-name
    // lookup still runs the exact own-property surface validator before a
    // diagnostic claims that the receiver has no index signature.
    if index.property_name.is_none() {
        store.resolved_own_property(receiver_type, "")?;
    }
    Ok(ElementResolution::diagnostic(
        error_type,
        if index.property_name.is_some() {
            ElementDiagnostic::MissingLiteralProperty
        } else {
            ElementDiagnostic::MissingBroadIndex
        },
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedIndexSignatures {
    string: Option<TypeId>,
    number: Option<TypeId>,
}

fn resolved_index_signature_surface(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
) -> Result<Option<ResolvedIndexSignatures>, SourceElementError> {
    let record = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    let TypeData::Object(object) = record.data() else {
        return Ok(None);
    };
    let Some(index_infos) = object.structured.index_infos.as_deref() else {
        return Ok(None);
    };
    let object_flags = record.object_flags();
    if index_infos.is_empty()
        || record.flags() != TypeFlags::OBJECT
        || object_flags & ObjectFlags::OBJECT_TYPE_KIND_MASK != ObjectFlags::ANONYMOUS
        || !object_flags.contains(ObjectFlags::MEMBERS_RESOLVED)
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object
            .structured
            .properties
            .as_ref()
            .is_some_and(|items| !items.is_empty())
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexSignatureSurface(receiver_type),
        ));
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let mut resolved = ResolvedIndexSignatures {
        string: None,
        number: None,
    };
    let mut seen = HashSet::new();
    let mut index_symbol = None;
    for id in index_infos {
        if !seen.insert(*id) {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(receiver_type),
            ));
        }
        let info = store
            .index_info(*id)
            .ok_or(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(receiver_type),
            ))?;
        if store.type_payload(info.value_type()).is_none() {
            return Err(SourceElementError::InvalidType(info.value_type()));
        }
        match info.key_type() {
            key if key == bootstrap.string_type && resolved.string.is_none() => {
                resolved.string = Some(info.value_type());
            }
            key if key == bootstrap.number_type && resolved.number.is_none() => {
                resolved.number = Some(info.value_type());
            }
            _ => {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ));
            }
        }
        match (index_symbol, info.index_symbol()) {
            (None, symbol) => index_symbol = Some(symbol),
            (Some(expected), actual) if expected == actual => {}
            _ => {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ));
            }
        }
    }

    match (object.structured.members, index_symbol.flatten()) {
        (None, None) => {}
        (Some(members), Some(symbol)) => {
            let table = store
                .symbol_table(members)
                .ok_or(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ))?;
            if table.len() != 1
                || table.get(InternalSymbolName::Index.as_ref()) != Some(symbol)
                || store.symbol(symbol).is_none()
            {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ));
            }
        }
        _ => {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(receiver_type),
            ));
        }
    }
    Ok(Some(resolved))
}

#[allow(clippy::too_many_arguments)]
fn prepare_element_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
    kind: Option<ElementDiagnostic>,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceElementError> {
    let Some(kind) = kind else {
        return Ok(None);
    };
    if !options.no_implicit_any && !matches!(kind, ElementDiagnostic::InvalidIndexType) {
        return Ok(None);
    }
    let diagnostic = match kind {
        ElementDiagnostic::NumberIndexRequired => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(7015).ok_or(SourceElementError::MissingDiagnostic(7015))?,
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::InvalidIndexType => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2538).ok_or(SourceElementError::MissingDiagnostic(2538))?,
                [display_type(
                    store,
                    host,
                    global_types,
                    options,
                    index_type,
                )?],
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::MissingLiteralProperty | ElementDiagnostic::MissingBroadIndex => {
            let index = display_type(store, host, global_types, options, index_type)?;
            let receiver = display_type(store, host, global_types, options, receiver_type)?;
            let detail = if kind == ElementDiagnostic::MissingLiteralProperty {
                let property = classify_index(store, index_type)?
                    .property_name
                    .ok_or(SourceElementError::InvalidType(index_type))?;
                Diagnostic::with_arguments(
                    message_by_code(2339).ok_or(SourceElementError::MissingDiagnostic(2339))?,
                    [property, receiver.clone()],
                )
            } else {
                Diagnostic::with_arguments(
                    message_by_code(7054).ok_or(SourceElementError::MissingDiagnostic(7054))?,
                    [index.clone(), receiver.clone()],
                )
            }
            .render()
            .expect("the pinned element diagnostic detail has complete arguments");
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(7053).ok_or(SourceElementError::MissingDiagnostic(7053))?,
                    [index, receiver],
                )
                .with_details([format!("  {detail}")]),
                related_information: Vec::new(),
            }
        }
    };
    Ok(Some(diagnostic))
}

fn display_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    type_: TypeId,
) -> Result<String, SourceElementError> {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    Ok(match global_types {
        Some(global_types) => type_to_string_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            type_,
            flags,
        )?,
        None => type_to_string_with_host_and_flags(store, host, type_, flags)?,
    })
}

fn unsupported_access(node: NodeRef) -> SourceElementError {
    SourceElementError::Unsupported(SourceElementUnsupported::Access(node))
}

fn preflight_element_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourceElementError> {
    if let Some(links) = store.type_node_links(node) {
        let expected = TypeNodeLinks {
            resolved_type: links.resolved_type,
            ..TypeNodeLinks::default()
        };
        if links != &expected
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(SourceElementError::InvalidCache(node));
        }
    }
    if let Some(links) = store.symbol_node_links(node)
        && links
            .resolved_symbol
            .is_some_and(|symbol| store.symbol(symbol).is_none())
    {
        return Err(SourceElementError::InvalidCache(node));
    }
    Ok(())
}

fn publish_element_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    property: Option<SemanticSymbolId>,
    type_: TypeId,
) -> Result<(), SourceElementError> {
    let expected_type = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: property,
    };
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_type)
        || store
            .symbol_node_links(node)
            .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected_symbol)
    {
        return Err(SourceElementError::InvalidCache(node));
    }
    if property.is_some() && !store.set_symbol_node_links(node, expected_symbol) {
        return Err(SourceElementError::InvalidCache(node));
    }
    if !store.set_type_node_links(node, expected_type) {
        return Err(SourceElementError::InvalidCache(node));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeArena};
    use ts_binder::{BoundFile, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        DeclaredTypeLinks, IntrinsicBootstrapOptions, ValueSymbolLinks,
        declared::type_list_key,
        global_types::create_type_from_generic_global_type,
        source::{PlannedIdentifierRead, PlannedIdentifierReadKind},
    };

    fn parse_fixture(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn registered_store(parsed: &ParseResult, file: FileId) -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn empty_host() -> DeclaredTypeHost<'static> {
        DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap()
    }

    fn element_access(parsed: &ParseResult, file: FileId) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ElementAccessExpression)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    fn alloc_symbol(
        store: &mut CanonicalTypeMapperStore,
        flags: SymbolFlags,
        name: &str,
    ) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap()
    }

    fn identifier(node: NodeRef, symbol: SemanticSymbolId) -> PlannedExpression {
        PlannedExpression::new(
            node,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
        )
    }

    fn source_plan(
        parsed: &ParseResult,
        file: FileId,
        store: &CanonicalTypeMapperStore,
        index: PlannedExpressionKind,
        receiver_symbol: SemanticSymbolId,
    ) -> SourceElementPlan {
        let access = element_access(parsed, file);
        let syntax = plan_direct_source_element_syntax(&parsed.arena, store, access).unwrap();
        finish_direct_source_element_plan(
            syntax,
            identifier(syntax.receiver(), receiver_symbol),
            PlannedExpression::new(syntax.index(), index),
        )
        .unwrap()
    }

    fn property_object(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        type_: TypeId,
        optional: bool,
    ) -> (TypeId, SemanticSymbolId) {
        let property = alloc_symbol(
            store,
            SymbolFlags::PROPERTY
                | if optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                },
            name,
        );
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(name), property),
            Some(None)
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(members),
            Some(vec![property]),
            None,
            None,
            None,
        ));
        (object, property)
    }

    fn index_object(store: &mut CanonicalTypeMapperStore, key: TypeId, value: TypeId) -> TypeId {
        let index = store
            .alloc_index_info(key, value, false, None, Vec::new())
            .unwrap();
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            None,
            None,
            None,
            None,
            Some(vec![index]),
        ));
        object
    }

    fn canonical_array_target(store: &mut CanonicalTypeMapperStore) -> TypeId {
        let symbol = alloc_symbol(store, SymbolFlags::INTERFACE, "Array");
        let parameter_symbol = alloc_symbol(store, SymbolFlags::TYPE_PARAMETER, "T");
        let parameter = store.alloc_type_parameter(Some(parameter_symbol)).unwrap();
        assert!(store.set_declared_type_links(
            parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        let this_type = store.alloc_type_parameter(Some(symbol)).unwrap();
        assert!(store.initialize_interface_type_parameters(
            target,
            vec![parameter, this_type],
            0,
            this_type,
            type_list_key(&[parameter]),
        ));
        target
    }

    fn strict_options() -> CanonicalCheckerOptions {
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        }
    }

    #[test]
    fn literal_property_read_publishes_exact_symbol_and_type_cold_and_warm() {
        let parsed = parse_fixture("const result = object[\"known\"];");
        let file = FileId::new(601);
        let mut store = registered_store(&parsed, file);
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let index = store.regular_string_literal_type("known".into()).unwrap();
        let (object, property) = property_object(&mut store, "known", number, false);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::String("known".into()),
            receiver_symbol,
        );
        let targets = CanonicalArrayTargets::for_single_target_validation(object);
        let host = empty_host();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_element_with_array_targets(
                    &mut store,
                    &host,
                    targets,
                    strict_options(),
                    &plan,
                    object,
                    index,
                ),
                Ok(CheckedSourceElement {
                    type_: number,
                    diagnostic: None,
                })
            );
        }
        assert_eq!(
            store
                .type_node_links(plan.node)
                .and_then(|links| links.resolved_type),
            Some(number)
        );
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
    }

    #[test]
    fn array_number_reads_return_the_element_and_wrong_strings_emit_ts7015() {
        let parsed = parse_fixture("const first = array[0];");
        let file = FileId::new(602);
        let mut store = registered_store(&parsed, file);
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let zero = store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let target = canonical_array_target(&mut store);
        let array =
            create_type_from_generic_global_type(&mut store, target, number, ObjectFlags::NONE)
                .unwrap();
        let receiver_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "array");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Number {
                value: ts_jsnum::Number::new(0.0),
                unary_operand: None,
            },
            receiver_symbol,
        );
        let host = empty_host();
        let targets = CanonicalArrayTargets::for_test(target, target);
        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                targets,
                strict_options(),
                &plan,
                array,
                zero,
            ),
            Ok(CheckedSourceElement {
                type_: number,
                diagnostic: None,
            })
        );

        let wrong_parsed = parse_fixture("const wrong = array[\"wrong\"];");
        let wrong_file = FileId::new(603);
        assert!(
            store
                .register_source_file(&wrong_parsed.arena, wrong_parsed.source_file, wrong_file,)
                .is_some()
        );
        let wrong = store.regular_string_literal_type("wrong".into()).unwrap();
        let wrong_plan = source_plan(
            &wrong_parsed,
            wrong_file,
            &store,
            PlannedExpressionKind::String("wrong".into()),
            receiver_symbol,
        );
        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &host,
            targets,
            strict_options(),
            &wrong_plan,
            array,
            wrong,
        )
        .unwrap();
        assert_eq!(
            checked.type_,
            store.intrinsic_bootstrap().unwrap().error_type
        );
        let diagnostic = checked.diagnostic.unwrap();
        assert_eq!(diagnostic.node, Some(wrong_plan.index.node));
        assert_eq!(diagnostic.diagnostic.code(), 7015);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Element implicitly has an 'any' type because index expression is not of type 'number'."
        );
        assert_eq!(string, store.intrinsic_bootstrap().unwrap().string_type);
    }

    #[test]
    fn missing_literal_and_broad_object_keys_emit_exact_ts7053_chains() {
        for (offset, source, literal_name, expected_index, expected_detail) in [
            (
                0,
                "const result = object[\"missing\"];",
                Some("missing"),
                "\"missing\"",
                "  Property 'missing' does not exist on type '{ known: number; }'.",
            ),
            (
                1,
                "const result = object[key];",
                None,
                "string",
                "  No index signature with a parameter of type 'string' was found on type '{ known: number; }'.",
            ),
        ] {
            let parsed = parse_fixture(source);
            let file = FileId::new(604 + offset);
            let mut store = registered_store(&parsed, file);
            let (number, string) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.number_type, bootstrap.string_type)
            };
            let (object, _) = property_object(&mut store, "known", number, false);
            let receiver_symbol =
                alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
            let index_type = if offset == 0 {
                store.regular_string_literal_type("missing".into()).unwrap()
            } else {
                string
            };
            let index_kind = if let Some(literal_name) = literal_name {
                PlannedExpressionKind::String(literal_name.into())
            } else {
                let key_symbol =
                    alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "key");
                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                    resolved_symbol: key_symbol,
                    value_symbol: key_symbol,
                    kind: PlannedIdentifierReadKind::Variable,
                })
            };
            let plan = source_plan(&parsed, file, &store, index_kind, receiver_symbol);
            let host = empty_host();
            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(object),
                strict_options(),
                &plan,
                object,
                index_type,
            )
            .unwrap();
            let diagnostic = checked.diagnostic.unwrap();
            assert_eq!(diagnostic.node, Some(plan.node));
            assert_eq!(diagnostic.diagnostic.code(), 7053);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Element implicitly has an 'any' type because expression of type '{expected_index}' can't be used to index type '{{ known: number; }}'.\n{expected_detail}"
                )
            );
        }
    }

    #[test]
    fn string_and_number_index_signatures_follow_pinned_applicability() {
        let parsed = parse_fixture("const result = dictionary[key];");
        let file = FileId::new(606);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let string_dictionary = index_object(&mut store, string, number);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "dictionary");
        let key_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "key");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: key_symbol,
                value_symbol: key_symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
            receiver_symbol,
        );
        let host = empty_host();
        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(string_dictionary),
                strict_options(),
                &plan,
                string_dictionary,
                string,
            ),
            Ok(CheckedSourceElement {
                type_: number,
                diagnostic: None,
            })
        );

        let number_parsed = parse_fixture("const result = dictionary[\"0\"];");
        let number_file = FileId::new(607);
        assert!(
            store
                .register_source_file(&number_parsed.arena, number_parsed.source_file, number_file,)
                .is_some()
        );
        let number_dictionary = index_object(&mut store, number, string);
        let zero = store.regular_string_literal_type("0".into()).unwrap();
        let number_plan = source_plan(
            &number_parsed,
            number_file,
            &store,
            PlannedExpressionKind::String("0".into()),
            receiver_symbol,
        );
        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(number_dictionary),
                strict_options(),
                &number_plan,
                number_dictionary,
                zero,
            ),
            Ok(CheckedSourceElement {
                type_: string,
                diagnostic: None,
            })
        );
    }

    #[test]
    fn invalid_boolean_index_emits_ts2538_even_without_no_implicit_any() {
        let parsed = parse_fixture("const result = object[true];");
        let file = FileId::new(608);
        let mut store = registered_store(&parsed, file);
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let true_type = store.intrinsic_bootstrap().unwrap().true_type;
        let (object, _) = property_object(&mut store, "known", number, false);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Boolean(true),
            receiver_symbol,
        );
        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            CanonicalCheckerOptions::default(),
            &plan,
            object,
            true_type,
        )
        .unwrap();
        let diagnostic = checked.diagnostic.unwrap();
        assert_eq!(diagnostic.node, Some(plan.index.node));
        assert_eq!(diagnostic.diagnostic.code(), 2538);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'true' cannot be used as an index type."
        );
    }

    #[test]
    fn optional_chains_member_calls_and_poisoned_links_fail_closed() {
        let optional = parse_fixture("const result = object?.[\"known\"];");
        let optional_file = FileId::new(609);
        let optional_access = element_access(&optional, optional_file);
        let optional_store = registered_store(&optional, optional_file);
        assert_eq!(
            plan_direct_source_element_syntax(&optional.arena, &optional_store, optional_access,),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::Access(optional_access),
            ))
        );

        let call = parse_fixture("const result = object[\"known\"]();");
        let call_file = FileId::new(610);
        let call_access = element_access(&call, call_file);
        let call_store = registered_store(&call, call_file);
        assert!(matches!(
            plan_direct_source_element_syntax(&call.arena, &call_store, call_access),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::MemberCall(_)
            ))
        ));

        let poisoned = parse_fixture("const result = object[\"known\"];");
        let poisoned_file = FileId::new(611);
        let poisoned_access = element_access(&poisoned, poisoned_file);
        let mut poisoned_store = registered_store(&poisoned, poisoned_file);
        assert!(poisoned_store.set_type_node_links(
            poisoned_access,
            TypeNodeLinks {
                outer_type_parameters: Some(Vec::new()),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            plan_direct_source_element_syntax(&poisoned.arena, &poisoned_store, poisoned_access,),
            Err(SourceElementError::InvalidCache(poisoned_access))
        );
    }
}
