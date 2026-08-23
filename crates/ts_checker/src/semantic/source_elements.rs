//! Exact read-only source integration for direct `receiver[index]` access.
//!
//! This is the dependency-closed expression prefix of pinned
//! `checkElementAccessExpression` plus `getPropertyTypeForIndexType`. It
//! supports canonical `any`, direct `Array<T>`/`ReadonlyArray<T>` references,
//! validated fixed tuple elements,
//! required own and shared union properties selected by string or number
//! literals, primitive string indexing, resolved anonymous string/number index
//! signatures, finite unions of valid literal keys, optional properties, and
//! optional chains. Writes, generic indexed access types, and apparent/global
//! property lookup stay typed boundaries.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    ArrayTypeError, CanonicalCheckerDiagnostic, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    SymbolNodeLinks, TypeDisplayUnavailable, TypeId, TypeNodeLinks, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    enums,
    formatter::{
        type_to_string_with_host_and_flags, type_to_string_with_host_global_types_and_flags,
    },
    member_resolution::UnionPropertyError,
    source::PlannedExpression,
    store::SourceNodeParent,
    type_records::{LiteralValue, StructuredTypeData, TypeCacheState, TypeData, TypeRecord},
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
    optional: bool,
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
    optional: bool,
}

/// Exact result and retryable diagnostic publication for one element read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceElement {
    pub(super) type_: TypeId,
    pub(super) diagnostic: Option<CanonicalCheckerDiagnostic>,
}

/// Proves a read-only element-access AST and its existing cache shape before
/// recursive source planning begins.
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
    let Some(receiver_record) = arena.get(receiver.node) else {
        return Err(unsupported_access(node));
    };
    let Some(index_record) = arena.get(index.node) else {
        return Err(unsupported_access(node));
    };
    if receiver_record.parent != Some(node.node) || index_record.parent != Some(node.node) {
        return Err(unsupported_access(node));
    }
    let optional = if let Some(token_id) = access.question_dot_token {
        let Some(token) = arena.get(token_id) else {
            return Err(unsupported_access(node));
        };
        if token.kind != SyntaxKind::QuestionDotToken
            || token.parent != Some(node.node)
            || token.flags.0 != 0
            || token.range.start < receiver_record.range.end
            || token.range.end > index_record.range.start
        {
            return Err(unsupported_access(node));
        }
        true
    } else {
        receiver_continues_optional_chain(arena, receiver_record)
    };

    preflight_element_links(store, node)?;
    Ok(DirectSourceElementSyntax {
        node,
        receiver,
        index,
        optional,
    })
}

/// Joins proven syntax to the source planner's recursively validated children.
pub(super) fn finish_direct_source_element_plan(
    syntax: DirectSourceElementSyntax,
    receiver: PlannedExpression,
    index: PlannedExpression,
) -> Result<SourceElementPlan, SourceElementError> {
    if receiver.node != syntax.receiver {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Receiver(syntax.receiver),
        ));
    }
    if index.node != syntax.index {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Index(syntax.index),
        ));
    }
    Ok(SourceElementPlan {
        node: syntax.node,
        receiver,
        index,
        optional: syntax.optional,
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
    let indices = classify_indices(store, index_type)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let any = bootstrap.any_type;
    let error = bootstrap.error_type;
    let string = bootstrap.string_type;
    let undefined = bootstrap.undefined_type;
    let (receiver_type, propagate_undefined) = if plan.optional && receiver_type != any {
        optional_element_receiver(store, global_types, plan, receiver_type)?
    } else {
        (receiver_type, false)
    };

    let mut resolutions = Vec::with_capacity(indices.len());
    for index in &indices {
        let resolution = resolve_element_index(
            store,
            global_types,
            array_targets,
            plan,
            receiver_type,
            index,
            any,
            error,
            string,
            undefined,
        )?;
        if indices.len() != 1 && resolution.diagnostic.is_some() {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexType(index_type),
            ));
        }
        resolutions.push(resolution);
    }
    let resolution = if let [resolution] = resolutions.as_slice() {
        *resolution
    } else {
        let values = resolutions
            .iter()
            .map(|resolution| resolution.type_)
            .collect::<Vec<_>>();
        let type_ = if values.iter().all(|value| *value == values[0]) {
            values[0]
        } else if let Some(global_types) = global_types {
            store.expression_union_type_with_global_types(
                global_types,
                &values,
                UnionReduction::Literal,
            )?
        } else {
            #[cfg(test)]
            {
                store.expression_union_type(&values, UnionReduction::Literal)?
            }
            #[cfg(not(test))]
            {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexType(index_type),
                ));
            }
        };
        ElementResolution::success(type_, None)
    };

    let type_ = if propagate_undefined
        && resolution.type_ != any
        && resolution.type_ != error
        && resolution.type_ != undefined
    {
        element_union_type(
            store,
            global_types,
            plan.node,
            &[resolution.type_, undefined],
            resolution.property,
        )?
    } else {
        resolution.type_
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
    publish_element_links(store, plan.node, resolution.property, type_)?;
    Ok(CheckedSourceElement { type_, diagnostic })
}

fn receiver_continues_optional_chain(arena: &NodeArena, receiver: &ts_ast::Node) -> bool {
    match &receiver.data {
        NodeData::PropertyAccessExpression(access) => {
            access.question_dot_token.is_some()
                || arena
                    .get(access.expression)
                    .is_some_and(|parent| receiver_continues_optional_chain(arena, parent))
        }
        NodeData::ElementAccessExpression(access) => {
            access.question_dot_token.is_some()
                || arena
                    .get(access.expression)
                    .is_some_and(|parent| receiver_continues_optional_chain(arena, parent))
        }
        _ => false,
    }
}

fn optional_element_receiver(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
) -> Result<(TypeId, bool), SourceElementError> {
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .options
        .strict_null_checks;
    if !strict {
        return Ok((receiver_type, false));
    }
    let Some(record) = store.type_payload(receiver_type) else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    if !record.flags().intersects(TypeFlags::UNION) {
        if record.flags().intersects(TypeFlags::NULLABLE) {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::Receiver(plan.receiver.node),
            ));
        }
        return Ok((receiver_type, false));
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    let constituents = union.union.types.clone();
    let mut retained = Vec::with_capacity(constituents.len());
    for constituent in constituents.iter().copied() {
        let flags = store
            .type_payload(constituent)
            .map(TypeRecord::flags)
            .ok_or(SourceElementError::InvalidType(constituent))?;
        if !flags.intersects(TypeFlags::NULLABLE) {
            retained.push(constituent);
        }
    }
    if retained.len() == constituents.len() {
        return Ok((receiver_type, false));
    }
    let Some(first) = retained.first().copied() else {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Receiver(plan.receiver.node),
        ));
    };
    let receiver = if retained.len() == 1 {
        first
    } else {
        element_union_type(store, global_types, plan.node, &retained, None)?
    };
    Ok((receiver, true))
}

#[allow(clippy::too_many_arguments)]
fn resolve_element_index(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    array_targets: CanonicalArrayTargets,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    any: TypeId,
    error: TypeId,
    string: TypeId,
    undefined: TypeId,
) -> Result<ElementResolution, SourceElementError> {
    Ok(if receiver_type == error {
        ElementResolution::success(error, None)
    } else if matches!(index.shape, IndexShape::Invalid) {
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
    } else if let Some(tuple) = resolve_tuple_element(store, receiver_type, index, undefined)? {
        tuple
    } else if is_string_receiver(store, receiver_type)? {
        if index.is_number_applicable() {
            ElementResolution::success(string, None)
        } else if index.is_string_or_number() {
            ElementResolution::diagnostic(error, ElementDiagnostic::NumberIndexRequired)
        } else {
            ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
        }
    } else {
        resolve_object_element(store, global_types, plan, receiver_type, index, any, error)?
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

fn classify_indices(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
) -> Result<Vec<ClassifiedIndex>, SourceElementError> {
    let mut types = Vec::new();
    collect_index_types(store, index_type, &mut types, &mut HashSet::new())?;
    types
        .into_iter()
        .map(|type_| classify_index(store, type_))
        .collect()
}

fn collect_index_types(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
    result: &mut Vec<TypeId>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), SourceElementError> {
    let record = store
        .type_payload(index_type)
        .ok_or(SourceElementError::InvalidType(index_type))?;
    if !record.flags().intersects(TypeFlags::UNION) {
        if matches!(record.data(), TypeData::Union(_)) {
            return Err(SourceElementError::InvalidType(index_type));
        }
        result.push(index_type);
        return Ok(());
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourceElementError::InvalidType(index_type));
    };
    if record.flags().intersects(TypeFlags::BOOLEAN) {
        result.push(index_type);
        return Ok(());
    }
    if union.union.types.is_empty() || !visiting.insert(index_type) {
        return Err(SourceElementError::InvalidType(index_type));
    }
    for constituent in &union.union.types {
        collect_index_types(store, *constituent, result, visiting)?;
    }
    visiting.remove(&index_type);
    Ok(())
}

fn classify_index(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
) -> Result<ClassifiedIndex, SourceElementError> {
    let record = store
        .type_payload(index_type)
        .ok_or(SourceElementError::InvalidType(index_type))?;
    let flags = record.flags();
    if flags.intersects(TypeFlags::ENUM_LIKE) {
        if enums::canonical_enum_type_owner(store, index_type).is_none() {
            return Err(SourceElementError::Literal(
                LiteralTypeCacheError::InvalidCachedLiteral(index_type),
            ));
        }
    } else if flags.intersects(TypeFlags::FRESHABLE) {
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
    if flags.intersects(TypeFlags::BOOLEAN) {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Invalid,
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
        LiteralValue::String(value) if flags.intersects(TypeFlags::STRING_LITERAL) => value.clone(),
        LiteralValue::Number(value) if flags.intersects(TypeFlags::NUMBER_LITERAL) => {
            value.to_string()
        }
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
    MissingConstEnumProperty,
    MissingBroadIndex,
    NegativeTupleIndex,
    TupleIndexOutOfBounds { length: usize, index: usize },
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

fn resolve_tuple_element(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    undefined: TypeId,
) -> Result<Option<ElementResolution>, SourceElementError> {
    let Some(shape) = store
        .canonical_tuple_shape(receiver_type)
        .map_err(|_| SourceElementError::InvalidType(receiver_type))?
    else {
        return Ok(None);
    };
    let Some(name) = index.property_name.as_deref() else {
        return Ok(None);
    };
    if !matches!(index.shape, IndexShape::Literal { numeric_name: true }) {
        return Ok(None);
    }
    if name.starts_with('-') {
        return Ok(Some(ElementResolution::diagnostic(
            undefined,
            ElementDiagnostic::NegativeTupleIndex,
        )));
    }
    let Ok(position) = name.parse::<usize>() else {
        return Ok(None);
    };
    if let Some(element) = shape.element_types().get(position).copied() {
        return Ok(Some(ElementResolution::success(element, None)));
    }
    if shape
        .element_infos()
        .last()
        .is_some_and(|info| info.flags().contains(super::signatures::ElementFlags::REST))
        && let Some(element) = shape.element_types().last().copied()
    {
        return Ok(Some(ElementResolution::success(element, None)));
    }
    Ok(Some(ElementResolution::diagnostic(
        undefined,
        ElementDiagnostic::TupleIndexOutOfBounds {
            length: shape.element_types().len(),
            index: position,
        },
    )))
}

fn resolve_object_element(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
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
        if let Some(resolution) =
            resolve_enum_element(store, plan, receiver_type, name, error_type)?
        {
            return Ok(resolution);
        }
        if store
            .type_payload(receiver_type)
            .is_some_and(|record| record.flags().intersects(TypeFlags::UNION))
        {
            let property = store
                .resolved_union_property(receiver_type, name)
                .map_err(|error| union_property_error(plan.node, receiver_type, error))?;
            return Ok(match property {
                Some(property) => {
                    ElementResolution::success(property.type_id(), Some(property.symbol()))
                }
                None => ElementResolution::diagnostic(
                    error_type,
                    ElementDiagnostic::MissingLiteralProperty,
                ),
            });
        }
        match store.resolved_own_property(receiver_type, name) {
            Ok(Some(property)) => {
                let type_ = optional_element_read_type(
                    store,
                    global_types,
                    plan.node,
                    property.symbol,
                    property.type_,
                    property.optional,
                )?;
                return Ok(ElementResolution::success(type_, Some(property.symbol)));
            }
            Ok(None) | Err(RelationUnavailable::StructuredIndexInfos(_)) => {}
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
        let union_members = match store.type_payload(receiver_type).map(TypeRecord::data) {
            Some(TypeData::Union(union)) => Some(union.union.types.clone()),
            _ => None,
        };
        if let Some(union_members) = union_members {
            if union_members.is_empty() {
                return Err(SourceElementError::InvalidType(receiver_type));
            }
            for member in union_members {
                if resolved_index_signature_surface(store, member)?.is_some() {
                    return Err(SourceElementError::Unsupported(
                        SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                    ));
                }
                store.resolved_own_property(member, "")?;
            }
        } else {
            store.resolved_own_property(receiver_type, "")?;
        }
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

fn resolve_enum_element(
    store: &CanonicalTypeMapperStore,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    name: &str,
    error_type: TypeId,
) -> Result<Option<ElementResolution>, SourceElementError> {
    if !matches!(
        store.source_node_kind(plan.index.node),
        Some(SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral)
    ) {
        return Ok(None);
    }
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    let Some(owner) = receiver.symbol() else {
        return Ok(None);
    };
    let owner_record = store
        .symbol(owner)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    if !owner_record.flags().intersects(SymbolFlags::ENUM) {
        return Ok(None);
    }
    let TypeData::Object(value) = receiver.data() else {
        return Err(SourceElementError::InvalidCache(plan.node));
    };
    let [declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(SourceElementError::InvalidCache(plan.node));
    };
    let declared = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    let empty_enum = store.type_payload(declared).is_some_and(|declared| {
        declared.flags() == TypeFlags::ENUM && declared.symbol() == Some(owner)
    });
    if !matches!(
        owner_record.flags(),
        SymbolFlags::REGULAR_ENUM | SymbolFlags::CONST_ENUM
    ) || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration() != Some(*declaration)
        || owner_record.members().is_some()
        || owner_record.exports().is_some() == empty_enum
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::EnumDeclaration)
        || receiver.flags() != TypeFlags::OBJECT
        || receiver.object_flags() != ObjectFlags::ANONYMOUS
        || receiver.alias().is_some()
        || value.structured != StructuredTypeData::default()
        || value.target.is_some()
        || value.mapper.is_some()
        || value.instantiations != TypeCacheState::Unallocated
        || store.value_symbol_links(owner)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(receiver_type),
                ..ValueSymbolLinks::default()
            })
        || enums::canonical_enum_type_owner(store, declared) != Some(owner)
    {
        return Err(SourceElementError::InvalidCache(plan.node));
    }

    let member = match owner_record.exports() {
        Some(exports) => {
            let exports = store
                .symbol_table(exports)
                .ok_or(SourceElementError::InvalidCache(plan.node))?;
            if exports.is_empty() {
                return Err(SourceElementError::InvalidCache(plan.node));
            }
            exports.get_source(name)
        }
        None => None,
    };
    let Some(member) = member else {
        return Ok(Some(ElementResolution::diagnostic(
            error_type,
            if owner_record.flags() == SymbolFlags::CONST_ENUM {
                ElementDiagnostic::MissingConstEnumProperty
            } else {
                ElementDiagnostic::MissingLiteralProperty
            },
        )));
    };
    let (resolved, type_) = enums::enum_value_member_type(store, receiver_type, name)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    if resolved != member
        || store.value_symbol_links(member)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(SourceElementError::InvalidCache(plan.node));
    }
    Ok(Some(ElementResolution::success(type_, Some(member))))
}

fn optional_element_read_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    node: NodeRef,
    property: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
) -> Result<TypeId, SourceElementError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    if !optional || !bootstrap.options.strict_null_checks {
        return Ok(type_);
    }
    if global_types.is_none() && bootstrap.options.exact_optional_property_types {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::OptionalProperty { node, property },
        ));
    }
    let undefined = bootstrap.undefined_or_missing_type;
    element_union_type(
        store,
        global_types,
        node,
        &[type_, undefined],
        Some(property),
    )
}

fn element_union_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    node: NodeRef,
    types: &[TypeId],
    property: Option<SemanticSymbolId>,
) -> Result<TypeId, SourceElementError> {
    if let Some(global_types) = global_types {
        return store
            .expression_union_type_with_global_types(global_types, types, UnionReduction::Literal)
            .map_err(Into::into);
    }
    #[cfg(test)]
    {
        let _ = (node, property);
        store
            .expression_union_type(types, UnionReduction::Literal)
            .map_err(Into::into)
    }
    #[cfg(not(test))]
    {
        Err(SourceElementError::Unsupported(match property {
            Some(property) => SourceElementUnsupported::OptionalProperty { node, property },
            None => SourceElementUnsupported::Access(node),
        }))
    }
}

fn union_property_error(
    node: NodeRef,
    receiver_type: TypeId,
    error: UnionPropertyError,
) -> SourceElementError {
    match error {
        UnionPropertyError::UnsupportedUnion(_)
        | UnionPropertyError::UnsupportedConstituent(_)
        | UnionPropertyError::UnsupportedPropertyType(_)
        | UnionPropertyError::UnsupportedExactOptionalProperty(_) => {
            SourceElementError::Unsupported(SourceElementUnsupported::IndexSignatureSurface(
                receiver_type,
            ))
        }
        UnionPropertyError::InvalidUnion(_)
        | UnionPropertyError::InvalidProperty(_)
        | UnionPropertyError::InvalidCache(_)
        | UnionPropertyError::Capacity(_) => SourceElementError::InvalidCache(node),
        UnionPropertyError::Relation(error) => SourceElementError::Relation(error),
        UnionPropertyError::TypeCache(error) => SourceElementError::Literal(error),
    }
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
        (Some(members), None)
            if valid_bound_declared_index_member(store, record.symbol(), members, index_infos) => {}
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

fn valid_bound_declared_index_member(
    store: &CanonicalTypeMapperStore,
    owner: Option<SemanticSymbolId>,
    members: SymbolTableId,
    index_infos: &[super::IndexInfoId],
) -> bool {
    let Some(owner) = owner else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([owner_declaration]) = owner_record.declarations() else {
        return false;
    };
    let Some(table) = store.symbol_table(members) else {
        return false;
    };
    let Some(symbol) = table.get(InternalSymbolName::Index.as_ref()) else {
        return false;
    };
    let Some(record) = store.symbol(symbol) else {
        return false;
    };
    let declarations = index_infos
        .iter()
        .map(|index| {
            let info = store.index_info(*index)?;
            let declaration = info.declaration()?;
            (info.index_symbol().is_none()
                && info.components().is_empty()
                && store.source_node_kind(declaration) == Some(SyntaxKind::IndexSignature))
            .then_some(declaration)
        })
        .collect::<Option<Vec<_>>>();
    table.len() == 1
        && store.get_merged_symbol(owner) == Some(owner)
        && owner_record.flags() == SymbolFlags::TYPE_LITERAL
        && owner_record.check_flags() == CheckFlags::NONE
        && owner_record.name() == InternalSymbolName::Type.as_ref()
        && owner_record.value_declaration().is_none()
        && owner_record.members() == Some(members)
        && owner_record.exports().is_none()
        && owner_record.parent().is_none()
        && owner_record.export_symbol().is_none()
        && store.source_node_kind(*owner_declaration) == Some(SyntaxKind::TypeLiteral)
        && store.get_merged_symbol(symbol) == Some(symbol)
        && record.flags() == SymbolFlags::SIGNATURE
        && record.check_flags() == CheckFlags::NONE
        && record.name() == InternalSymbolName::Index.as_ref()
        && declarations.as_deref().is_some_and(|declarations| {
            record.declarations() == Some(declarations)
                && declarations.iter().all(|declaration| {
                    store.source_node_parent(*declaration)
                        == Some(SourceNodeParent::Parent(*owner_declaration))
                })
        })
        && record.value_declaration().is_none()
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent() == Some(owner)
        && record.export_symbol().is_none()
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
    if !options.no_implicit_any
        && !matches!(
            kind,
            ElementDiagnostic::InvalidIndexType
                | ElementDiagnostic::MissingConstEnumProperty
                | ElementDiagnostic::NegativeTupleIndex
                | ElementDiagnostic::TupleIndexOutOfBounds { .. }
        )
    {
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
        ElementDiagnostic::NegativeTupleIndex => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(2514).ok_or(SourceElementError::MissingDiagnostic(2514))?,
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::TupleIndexOutOfBounds { length, index } => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2493).ok_or(SourceElementError::MissingDiagnostic(2493))?,
                [
                    display_type(store, host, global_types, options, receiver_type)?,
                    length.to_string(),
                    index.to_string(),
                ],
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::MissingConstEnumProperty => {
            let property = classify_index(store, index_type)?
                .property_name
                .ok_or(SourceElementError::InvalidType(index_type))?;
            let receiver = display_type(store, host, global_types, options, receiver_type)?;
            CanonicalCheckerDiagnostic {
                node: Some(plan.index.node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2339).ok_or(SourceElementError::MissingDiagnostic(2339))?,
                    [property, receiver],
                ),
                related_information: Vec::new(),
            }
        }
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
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, DeclaredTypeLinks, IntrinsicBootstrapOptions, ValueSymbolLinks,
        declared::type_list_key,
        global_types::create_type_from_generic_global_type,
        signatures::ElementFlags,
        source::{PlannedExpressionKind, PlannedIdentifierRead, PlannedIdentifierReadKind},
        tuple_types::CanonicalTupleTypeRequest,
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

    fn published_enum(
        parsed: &ParseResult,
        file: FileId,
    ) -> (
        CanonicalTypeMapperStore,
        BoundFile,
        enums::CanonicalEnumSemantics,
    ) {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/enum-element-access.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::EnumDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let enumeration = {
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            enums::get_enum_semantics(&mut store, &host, owner).unwrap()
        };
        (store, bound, enumeration)
    }

    fn enum_element_plan(
        parsed: &ParseResult,
        file: FileId,
        store: &CanonicalTypeMapperStore,
        owner: SemanticSymbolId,
        name: &str,
    ) -> SourceElementPlan {
        let access = element_access(parsed, file);
        let syntax = plan_direct_source_element_syntax(&parsed.arena, store, access).unwrap();
        finish_direct_source_element_plan(
            syntax,
            PlannedExpression::new(
                syntax.receiver(),
                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                    resolved_symbol: owner,
                    value_symbol: owner,
                    kind: PlannedIdentifierReadKind::DeclaredValue,
                }),
            ),
            PlannedExpression::new(
                syntax.index(),
                PlannedExpressionKind::String(name.to_owned()),
            ),
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
    fn bound_declared_index_member_rejects_cloned_nonowner_table() {
        let parsed = parse_fixture("type Table = { [key: string]: number };");
        let file = FileId::new(600);
        let mut store = registered_store(&parsed, file);
        let literal = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::IndexSignature).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let members = store.alloc_symbol_table();
        let owner = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_LITERAL,
                EscapedName::internal(InternalSymbolName::Type),
            ))
            .unwrap();
        assert!(store.set_symbol_declarations(owner, Some(vec![literal]), None));
        assert!(store.set_symbol_relationships(owner, Some(members), None, None, None));
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::SIGNATURE,
                EscapedName::internal(InternalSymbolName::Index),
            ))
            .unwrap();
        assert!(store.set_symbol_declarations(symbol, Some(vec![declaration]), None));
        assert!(store.set_symbol_relationships(symbol, None, None, Some(owner), None));
        assert_eq!(
            store.insert_symbol(
                members,
                EscapedName::internal(InternalSymbolName::Index),
                symbol,
            ),
            Some(None)
        );
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let index = store
            .alloc_index_info(string, number, false, Some(declaration), Vec::new())
            .unwrap();
        assert!(valid_bound_declared_index_member(
            &store,
            Some(owner),
            members,
            &[index],
        ));

        let replacement = store.clone_symbol_table(members).unwrap();
        assert_eq!(
            store
                .symbol_table(replacement)
                .and_then(|table| table.get(InternalSymbolName::Index.as_ref())),
            Some(symbol)
        );
        assert!(!valid_bound_declared_index_member(
            &store,
            Some(owner),
            replacement,
            &[index],
        ));
    }

    #[test]
    fn enum_member_literals_classify_as_their_numeric_and_string_values() {
        let parsed = parse_fixture("enum Keys { Zero = 0, Label = 'name' }");
        let file = FileId::new(620);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/enum-element-keys.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let bound = &files[&file];
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::EnumDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        let enumeration = enums::get_enum_semantics(&mut store, &host, owner).unwrap();

        for (member, name, numeric_name) in [
            (&enumeration.members[0], "0", true),
            (&enumeration.members[1], "name", false),
        ] {
            let expected = ClassifiedIndex {
                shape: IndexShape::Literal { numeric_name },
                property_name: Some(name.to_owned()),
            };
            assert_eq!(
                classify_index(&store, member.regular_type),
                Ok(expected.clone())
            );
            assert_eq!(classify_index(&store, member.fresh_type), Ok(expected));
        }
    }

    #[test]
    fn enum_string_element_reads_publish_exact_member_links_cold_and_warm() {
        for (offset, declaration) in [(0, "enum"), (1, "const enum")] {
            let parsed = parse_fixture(&format!(
                "{declaration} Status {{ Ready = 1 }} const result = Status[\"Ready\"];"
            ));
            let file = FileId::new(621 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let member = &enumeration.members[0];
            let index = store.regular_string_literal_type("Ready".into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, "Ready");
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let targets =
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type);

            for _ in 0..2 {
                assert_eq!(
                    check_direct_source_element_with_array_targets(
                        &mut store,
                        &host,
                        targets,
                        CanonicalCheckerOptions::default(),
                        &plan,
                        enumeration.value_type,
                        index,
                    ),
                    Ok(CheckedSourceElement {
                        type_: member.fresh_type,
                        diagnostic: None,
                    }),
                );
            }
            assert_eq!(
                store
                    .type_node_links(plan.node)
                    .and_then(|links| links.resolved_type),
                Some(member.fresh_type),
            );
            assert_eq!(
                store
                    .symbol_node_links(plan.node)
                    .and_then(|links| links.resolved_symbol),
                Some(member.symbol),
            );
        }
    }

    #[test]
    fn missing_const_enum_elements_issue_direct_ts2339_on_the_string_index() {
        for (offset, declaration, no_implicit_any, expected_code) in [
            (0, "const enum", false, Some(2339)),
            (1, "const enum", true, Some(2339)),
            (2, "enum", false, None),
            (3, "enum", true, Some(7053)),
        ] {
            let parsed = parse_fixture(&format!(
                "{declaration} Status {{ Ready }} const result = Status[\"Missing\"];"
            ));
            let file = FileId::new(623 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let index = store.regular_string_literal_type("Missing".into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, "Missing");
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let options = CanonicalCheckerOptions {
                no_implicit_any,
                ..CanonicalCheckerOptions::default()
            };
            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                options,
                &plan,
                enumeration.value_type,
                index,
            )
            .unwrap();

            assert_eq!(
                checked
                    .diagnostic
                    .as_ref()
                    .map(|diagnostic| diagnostic.diagnostic.code()),
                expected_code,
            );
            if let Some(diagnostic) = checked.diagnostic {
                if expected_code == Some(2339) {
                    assert_eq!(diagnostic.node, Some(plan.index.node));
                    assert_eq!(
                        diagnostic.diagnostic.render().unwrap(),
                        "Property 'Missing' does not exist on type 'typeof Status'.",
                    );
                } else {
                    assert_eq!(diagnostic.node, Some(plan.node));
                }
            }
            assert_eq!(
                checked.type_,
                store.intrinsic_bootstrap().unwrap().error_type,
            );
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn poisoned_enum_element_owner_exports_and_member_links_fail_closed() {
        #[derive(Clone, Copy)]
        enum Poison {
            OwnerValue,
            Exports,
            MemberValue,
        }

        for (offset, poison) in [Poison::OwnerValue, Poison::Exports, Poison::MemberValue]
            .into_iter()
            .enumerate()
        {
            let parsed =
                parse_fixture("const enum Status { Ready = 1 } const result = Status[\"Ready\"];");
            let file = FileId::new(627 + u32::try_from(offset).unwrap());
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let member = &enumeration.members[0];
            let index = store.regular_string_literal_type("Ready".into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, "Ready");
            let error = store.intrinsic_bootstrap().unwrap().error_type;
            match poison {
                Poison::OwnerValue => assert!(store.set_value_symbol_links(
                    enumeration.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(error),
                        ..ValueSymbolLinks::default()
                    },
                )),
                Poison::Exports => {
                    let exports = store.alloc_symbol_table();
                    assert!(store.set_symbol_relationships(
                        enumeration.symbol,
                        None,
                        Some(exports),
                        None,
                        None,
                    ));
                }
                Poison::MemberValue => assert!(store.set_value_symbol_links(
                    member.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(error),
                        ..ValueSymbolLinks::default()
                    },
                )),
            }
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();

            assert_eq!(
                check_direct_source_element_with_array_targets(
                    &mut store,
                    &host,
                    CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                    CanonicalCheckerOptions::default(),
                    &plan,
                    enumeration.value_type,
                    index,
                ),
                Err(SourceElementError::InvalidCache(plan.node)),
            );
            assert!(store.type_node_links(plan.node).is_none());
            assert!(store.symbol_node_links(plan.node).is_none());
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
    fn optional_literal_property_reads_include_undefined_under_strict_null_checks() {
        let parsed = parse_fixture("const result = object[\"value\"];");
        let file = FileId::new(614);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_or_missing_type)
        };
        let index = store.regular_string_literal_type("value".into()).unwrap();
        let (object, property) = property_object(&mut store, "value", string, true);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::String("value".into()),
            receiver_symbol,
        );

        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            strict_options(),
            &plan,
            object,
            index,
        )
        .unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("strict optional property access must produce a union")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property),
        );
    }

    #[test]
    fn optional_element_chains_remove_nullish_receivers_and_restore_undefined() {
        let parsed = parse_fixture("const result = object?.[\"value\"];");
        let file = FileId::new(615);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let index = store.regular_string_literal_type("value".into()).unwrap();
        let (object, property) = property_object(&mut store, "value", string, false);
        let nullable = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, object])
            .unwrap();
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::String("value".into()),
            receiver_symbol,
        );

        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            strict_options(),
            &plan,
            nullable,
            index,
        )
        .unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("optional element access must preserve undefined")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property),
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
    fn fixed_tuple_indices_return_the_exact_positional_element() {
        let parsed = parse_fixture("const result = tuple[1];");
        let file = FileId::new(612);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let elements = [string, number];
        let infos = [
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap(),
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap(),
        ];
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&elements, &infos, false))
            .unwrap();
        let array_target = canonical_array_target(&mut store);
        let receiver_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "tuple");
        let one = store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Number {
                value: ts_jsnum::Number::new(1.0),
                unary_operand: None,
            },
            receiver_symbol,
        );

        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_test(array_target, array_target),
                strict_options(),
                &plan,
                tuple,
                one,
            ),
            Ok(CheckedSourceElement {
                type_: number,
                diagnostic: None,
            }),
        );
    }

    #[test]
    fn fixed_tuple_out_of_bounds_indices_emit_ts2493_without_no_implicit_any() {
        for (file_id, source, nonempty, index, expected) in [
            (
                613,
                "const result = tuple[0];",
                false,
                0_u32,
                "Tuple type '[]' of length '0' has no element at index '0'.",
            ),
            (
                616,
                "const result = tuple[2];",
                true,
                2_u32,
                "Tuple type '[string]' of length '1' has no element at index '2'.",
            ),
        ] {
            let parsed = parse_fixture(source);
            let file = FileId::new(file_id);
            let mut store = registered_store(&parsed, file);
            let (string, undefined) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.undefined_type)
            };
            let tuple = if nonempty {
                let info = store
                    .create_tuple_element_info(ElementFlags::REQUIRED, None)
                    .unwrap();
                store
                    .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                        &[string],
                        &[info],
                        false,
                    ))
                    .unwrap()
            } else {
                store.create_canonical_empty_tuple_type().unwrap()
            };
            let array_target = canonical_array_target(&mut store);
            let receiver_symbol =
                alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "tuple");
            let value = ts_jsnum::Number::new(f64::from(index));
            let index_type = store.regular_number_literal_type(value).unwrap();
            let plan = source_plan(
                &parsed,
                file,
                &store,
                PlannedExpressionKind::Number {
                    value,
                    unary_operand: None,
                },
                receiver_symbol,
            );

            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_test(array_target, array_target),
                CanonicalCheckerOptions::default(),
                &plan,
                tuple,
                index_type,
            )
            .unwrap();
            assert_eq!(checked.type_, undefined);
            let diagnostic = checked.diagnostic.unwrap();
            assert_eq!(diagnostic.node, Some(plan.index.node));
            assert_eq!(diagnostic.diagnostic.code(), 2493);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
        }
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
    fn broad_keys_on_object_unions_emit_ts7053_for_the_complete_union() {
        let parsed = parse_fixture(concat!(
            "declare const key: string; ",
            "declare const object: ",
            "{ id: '00' } | { id: '01' } | { id: '02' }; ",
            "const result = object[key];",
        ));
        let file = FileId::new(617);
        let access = element_access(&parsed, file);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/union-element-access.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            strict_options(),
        )
        .unwrap();
        let expected_receiver = "{ id: \"00\"; } | { id: \"01\"; } | { id: \"02\"; }";

        for index in 0..2 {
            if index == 0 {
                context.check_source_file(file).unwrap();
            } else {
                context.recheck_source_file(file).unwrap();
            }
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("expected one broad-key object-union diagnostic");
            };
            assert_eq!(diagnostic.node, Some(access));
            assert_eq!(diagnostic.diagnostic.code(), 7053);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Element implicitly has an 'any' type because expression of type 'string' can't be used to index type '{expected_receiver}'.\n  No index signature with a parameter of type 'string' was found on type '{expected_receiver}'."
                )
            );
        }
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().error_type),
        );
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn broad_keys_keep_union_index_signatures_as_an_explicit_boundary() {
        let parsed = parse_fixture("const result = object[key];");
        let file = FileId::new(618);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (object, _) = property_object(&mut store, "id", number, false);
        let dictionary = index_object(&mut store, string, number);
        let mut members = vec![object, dictionary];
        members.sort();
        let union = store.alloc_union_type(ObjectFlags::NONE, members).unwrap();
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
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

        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_single_target_validation(union),
                strict_options(),
                &plan,
                union,
                string,
            ),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(union),
            )),
        );
        assert!(store.type_node_links(plan.node).is_none());
        assert!(store.symbol_node_links(plan.node).is_none());
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
    fn existing_error_receivers_skip_index_diagnostics_and_preserve_error_type() {
        let parsed = parse_fixture("const result = missing[true];");
        let file = FileId::new(619);
        let mut store = registered_store(&parsed, file);
        let (error, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.true_type)
        };
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "missing");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Boolean(true),
            receiver_symbol,
        );

        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_single_target_validation(error),
                strict_options(),
                &plan,
                error,
                boolean,
            ),
            Ok(CheckedSourceElement {
                type_: error,
                diagnostic: None,
            }),
        );
        assert_eq!(
            store
                .type_node_links(plan.node)
                .and_then(|links| links.resolved_type),
            Some(error),
        );
        assert!(store.symbol_node_links(plan.node).is_none());
    }

    #[test]
    fn member_calls_and_poisoned_links_fail_closed() {
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
