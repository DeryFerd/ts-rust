//! Exact concrete indexed-access type-node selection.
//!
//! This leaf owns the allocation-free success prefix of pinned
//! `getTypeFromIndexedAccessTypeNode`, `getIndexedAccessTypeOrUndefined`, and
//! `getPropertyTypeForIndexType`. The object operand is one direct, possibly
//! parenthesized type literal admitted by [`super::object_members`]. Required
//! own properties and string/number/template-pattern index signatures are
//! supported, including mixed surfaces: an exact literal property wins, then
//! one applicable number or template index wins over a string index. Generic
//! type-parameter pairs have a separate deferred constructor. Other named
//! operands, optional properties, overlapping non-string indexes, union keys,
//! tuples, apparent types, and diagnostic recovery remain explicit
//! concrete-planner boundaries.
//!
//! Planning chooses the exact property symbol or index-info slot before any
//! semantic child executes. Finishing only validates the already-resolved
//! object and returns an existing value type, so this concrete path never
//! allocates an `IndexedAccessType` or mutates a checker cache.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::SemanticSymbolId;
use ts_jsnum::Number;

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId,
    bootstrap::LiteralTypeCacheError,
    callable_sets::{StoredCallableSetValidation, validate_stored_declared_method_callable_set},
    declared::{cached_ordinary_type_parameter_owner, preflight_node},
    links::ValueSymbolLinks,
    object_members::{self, PropertyObjectError, PropertyObjectPlan, PropertyObjectState},
    type_nodes::normalize_numeric_separators,
    type_records::{LiteralValue, TypeData, TypeRecord},
    types::{AccessFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// Concrete key forms for which applicable index selection is allocation-free.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum ConcreteIndexKey {
    String,
    Number,
    StringLiteral { value: String, numeric_name: bool },
    NumberLiteral(Number),
}

impl ConcreteIndexKey {
    fn literal_property_name(&self) -> Option<ConcretePropertyName<'_>> {
        match self {
            Self::String | Self::Number => None,
            Self::StringLiteral { value, .. } => Some(ConcretePropertyName::Borrowed(value)),
            Self::NumberLiteral(value) => Some(ConcretePropertyName::Number(*value)),
        }
    }

    fn number_applicable(&self) -> bool {
        matches!(
            self,
            Self::Number
                | Self::NumberLiteral(_)
                | Self::StringLiteral {
                    numeric_name: true,
                    ..
                }
        )
    }
}

enum ConcretePropertyName<'value> {
    Borrowed(&'value str),
    Number(Number),
}

impl ConcretePropertyName<'_> {
    fn matches(&self, candidate: &str) -> bool {
        match self {
            Self::Borrowed(value) => *value == candidate,
            Self::Number(value) => value.to_string() == candidate,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PlannedIndexKind {
    String,
    Number,
    Template,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConcreteIndexedSelection {
    Property(SemanticSymbolId),
    Index { slot: usize, kind: PlannedIndexKind },
}

/// Complete dependency-free proof for one concrete indexed-access type node.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct ConcreteIndexedAccessPlan {
    node: NodeRef,
    object: NodeRef,
    object_literal: NodeRef,
    object_wrappers: Vec<NodeRef>,
    index: NodeRef,
    object_plan: PropertyObjectPlan,
    key: ConcreteIndexKey,
    selection: ConcreteIndexedSelection,
    cached_type: Option<TypeId>,
}

impl ConcreteIndexedAccessPlan {
    pub(super) const fn object(&self) -> NodeRef {
        self.object
    }

    pub(super) const fn object_literal(&self) -> NodeRef {
        self.object_literal
    }

    pub(super) const fn object_plan(&self) -> &PropertyObjectPlan {
        &self.object_plan
    }

    pub(super) const fn index(&self) -> NodeRef {
        self.index
    }
}

/// Syntax, capability, or warm-cache failure for the concrete A11a leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConcreteIndexedAccessError {
    DeclaredType(DeclaredTypeError),
    PropertyObject(PropertyObjectError),
    InvalidSyntax(NodeRef),
    UnsupportedObject(NodeRef),
    UnsupportedIndex(NodeRef),
    UnsupportedObjectSurface(NodeRef),
    OptionalProperty {
        node: NodeRef,
        property: SemanticSymbolId,
    },
    MissingProperty(NodeRef),
    MissingIndexSignature(NodeRef),
    InvalidCache(NodeRef),
    InvalidType(TypeId),
    LiteralCache(LiteralTypeCacheError),
}

impl From<DeclaredTypeError> for ConcreteIndexedAccessError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<PropertyObjectError> for ConcreteIndexedAccessError {
    fn from(error: PropertyObjectError) -> Self {
        Self::PropertyObject(error)
    }
}

impl From<LiteralTypeCacheError> for ConcreteIndexedAccessError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

impl std::fmt::Display for ConcreteIndexedAccessError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "concrete indexed-access type failed: {self:?}")
    }
}

impl std::error::Error for ConcreteIndexedAccessError {}

/// Returns the canonical deferred indexed access for two owned type parameters.
///
/// Transient access flags do not affect the stored type identity. A malformed
/// existing record or duplicate identity fails without allocating another type.
pub(super) fn get_deferred_indexed_access_type(
    store: &mut CanonicalTypeMapperStore,
    object_type: TypeId,
    index_type: TypeId,
    access_flags: AccessFlags,
) -> Option<TypeId> {
    cached_ordinary_type_parameter_owner(store, object_type)?;
    cached_ordinary_type_parameter_owner(store, index_type)?;
    let persistent_flags = access_flags & AccessFlags::PERSISTENT;
    let mut cached = None;

    for (type_, record) in store.types() {
        let TypeData::IndexedAccess(indexed) = record.data() else {
            continue;
        };
        if indexed.object_type != object_type
            || indexed.index_type != index_type
            || indexed.access_flags != persistent_flags
        {
            continue;
        }
        if record.flags() != TypeFlags::INDEXED_ACCESS
            || record.symbol().is_some()
            || record.alias().is_some()
            || cached.replace(type_).is_some()
        {
            return None;
        }
    }

    cached.or_else(|| store.alloc_indexed_access_type(object_type, index_type, persistent_flags))
}

/// Preflights one complete concrete indexed-access dependency closure.
///
/// The returned plan has already selected one required property or one exact
/// source-declared index-signature slot. A warm parent is accepted only when
/// its fully resolved object and canonical literal key reproduce the cached
/// result exactly.
pub(super) fn plan_concrete_indexed_access(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<ConcreteIndexedAccessPlan, ConcreteIndexedAccessError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::IndexedAccessTypeNode(indexed) = &record.data else {
        return Err(ConcreteIndexedAccessError::InvalidSyntax(node));
    };
    if record.kind != SyntaxKind::IndexedAccessType || record.flags.0 & NODE_FLAG_JSDOC != 0 {
        return Err(ConcreteIndexedAccessError::InvalidSyntax(node));
    }

    let object = NodeRef::new(node.arena, node.file, indexed.object_type);
    let index = NodeRef::new(node.arena, node.file, indexed.index_type);
    let object_record = preflight_node(store, host, object)?;
    let index_record = preflight_node(store, host, index)?;
    if object == index
        || object_record.parent != Some(node.node)
        || index_record.parent != Some(node.node)
        || object_record.range.start != record.range.start
        || object_record.range.end > index_record.range.start
        || index_record.range.end >= record.range.end
    {
        return Err(ConcreteIndexedAccessError::InvalidSyntax(node));
    }

    let (object_literal, object_wrappers) =
        direct_type_literal(store, host, object).map_err(|error| match error {
            DirectTypeLiteralError::Declared(error) => {
                ConcreteIndexedAccessError::DeclaredType(error)
            }
            DirectTypeLiteralError::Invalid(node) => {
                ConcreteIndexedAccessError::InvalidSyntax(node)
            }
            DirectTypeLiteralError::Unsupported(node) => {
                ConcreteIndexedAccessError::UnsupportedObject(node)
            }
        })?;
    let object_plan =
        object_members::plan_concrete_indexed_access_type_literal(store, host, object_literal)?;
    validate_member_domains(store, host, &object_plan)?;
    validate_member_annotation_cache(store, host, &object_plan)?;
    let key = classify_index(store, host, index)?;
    let selection = select_concrete_member(store, host, &object_plan, &key, index)?;

    validate_transparent_object_links(store, &object_wrappers)?;
    validate_existing_index_links(store, index, &key)?;
    let cached_type = validate_parent_links(store, node)?;
    let plan = ConcreteIndexedAccessPlan {
        node,
        object,
        object_literal,
        object_wrappers,
        index,
        object_plan,
        key,
        selection,
        cached_type,
    };
    if let Some(cached) = cached_type {
        let object_type = store
            .type_node_links(object_literal)
            .and_then(|links| links.resolved_type)
            .ok_or(ConcreteIndexedAccessError::InvalidCache(node))?;
        let index_type = cached_index_type(store, &plan)?;
        let resolved = resolved_selection_type(store, &plan, object_type)?;
        if resolved != cached {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        validate_index_type(store, &plan.key, index_type)?;
    }
    Ok(plan)
}

#[derive(Clone, Copy)]
struct PrimitiveDomain(u8);

impl PrimitiveDomain {
    const STRING: Self = Self(1 << 0);
    const NUMBER: Self = Self(1 << 1);
    const BOOLEAN: Self = Self(1 << 2);
    const BIGINT: Self = Self(1 << 3);
    const SYMBOL: Self = Self(1 << 4);
    const NEVER: Self = Self(0);

    const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    const fn is_subset_of(self, other: Self) -> bool {
        self.0 & !other.0 == 0
    }
}

/// Proves the TS2411/TS2413 obligations for the narrow mixed/paired surface.
///
/// General source checking does not yet run `checkIndexConstraints`, so this
/// leaf may only publish a mixed type literal when primitive syntax proves
/// every applicable property is assignable to its indexes and every narrower
/// index is assignable to the string index. Single-index, property-free
/// literals have no cross-member obligation and retain the broader annotation
/// capability.
fn validate_member_domains(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    object: &PropertyObjectPlan,
) -> Result<(), ConcreteIndexedAccessError> {
    if object.indexes.is_empty() || object.indexes.len() == 1 && object.properties.is_empty() {
        return Ok(());
    }

    let string_index = object.indexes.iter().find(|index| {
        store.source_node_kind(index.key_type_node) == Some(SyntaxKind::StringKeyword)
    });
    let number_index = object.indexes.iter().find(|index| {
        store.source_node_kind(index.key_type_node) == Some(SyntaxKind::NumberKeyword)
    });
    let string_domain = string_index
        .map(|index| {
            primitive_domain(store, host, index.value_type_node).ok_or(
                ConcreteIndexedAccessError::UnsupportedObjectSurface(object.node),
            )
        })
        .transpose()?;

    if string_domain.is_none()
        && (number_index.is_some()
            || object.indexes.iter().any(|index| {
                store.source_node_kind(index.key_type_node) != Some(SyntaxKind::TemplateLiteralType)
            }))
    {
        return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
            object.node,
        ));
    }

    let number_domain =
        number_index.and_then(|index| primitive_domain(store, host, index.value_type_node));
    if number_index.is_some()
        && !number_domain
            .is_some_and(|domain| string_domain.is_some_and(|string| domain.is_subset_of(string)))
    {
        return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
            object.node,
        ));
    }
    for property in &object.properties {
        let mut applicable_domain = string_domain;
        if is_numeric_literal_name(&property.name)
            && let Some(number) = number_domain
        {
            applicable_domain =
                Some(applicable_domain.map_or(number, |existing| existing.intersection(number)));
        }
        for index in &object.indexes {
            if store.source_node_kind(index.key_type_node) != Some(SyntaxKind::TemplateLiteralType)
                || !template_pattern_syntax_matches_name(
                    store,
                    host,
                    index.key_type_node,
                    &property.name,
                )?
            {
                continue;
            }
            let domain = primitive_domain(store, host, index.value_type_node).ok_or(
                ConcreteIndexedAccessError::UnsupportedObjectSurface(object.node),
            )?;
            applicable_domain =
                Some(applicable_domain.map_or(domain, |existing| existing.intersection(domain)));
        }
        let Some(applicable_domain) = applicable_domain else {
            continue;
        };
        let Some(domain) = (!property.optional)
            .then(|| primitive_domain(store, host, property.type_node))
            .flatten()
        else {
            return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                object.node,
            ));
        };
        if !domain.is_subset_of(applicable_domain) {
            return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                object.node,
            ));
        }
    }
    if let Some(string) = string_domain {
        for index in &object.indexes {
            if store.source_node_kind(index.key_type_node) != Some(SyntaxKind::TemplateLiteralType)
            {
                continue;
            }
            let domain = primitive_domain(store, host, index.value_type_node).ok_or(
                ConcreteIndexedAccessError::UnsupportedObjectSurface(object.node),
            )?;
            if !domain.is_subset_of(string) {
                return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                    object.node,
                ));
            }
        }
    }
    Ok(())
}

/// Keeps the leaf's object publication dependency-closed in the presence of
/// pre-existing checker links.
///
/// A cold inline object accepts only a cold/default annotation subtree. This
/// intentionally leaves independently pre-resolved child annotations as a
/// fail-closed boundary for this first leaf. A resolved object instead
/// requires every property and index annotation to reproduce its published
/// member identity without executing a child first.
fn validate_member_annotation_cache(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    object: &PropertyObjectPlan,
) -> Result<(), ConcreteIndexedAccessError> {
    let state = object_members::type_literal_state(store, object)?;
    let Some(PropertyObjectState::Resolved(object_type)) = state else {
        if state.is_none()
            && object.properties.iter().any(|property| {
                store
                    .value_symbol_links(property.symbol)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
            })
        {
            return Err(ConcreteIndexedAccessError::InvalidCache(object.node));
        }
        for property in &object.properties {
            validate_cold_annotation_subtree(store, host, property.type_node)?;
        }
        for method in &object.methods {
            if store
                .signature_links(method.declaration)
                .is_some_and(|links| links != &super::SignatureLinks::default())
            {
                return Err(ConcreteIndexedAccessError::InvalidCache(method.declaration));
            }
            validate_cold_annotation_subtree(store, host, method.return_type)?;
            for parameter in &method.parameters {
                if store
                    .value_symbol_links(parameter.symbol)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
                {
                    return Err(ConcreteIndexedAccessError::InvalidCache(
                        parameter.type_node,
                    ));
                }
                validate_cold_annotation_subtree(store, host, parameter.type_node)?;
            }
        }
        for index in &object.indexes {
            validate_cold_annotation_subtree(store, host, index.key_type_node)?;
            validate_cold_annotation_subtree(store, host, index.value_type_node)?;
        }
        return Ok(());
    };

    for property in &object.properties {
        let published = store
            .value_symbol_links(property.symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(ConcreteIndexedAccessError::InvalidCache(property.type_node))?;
        let method_count = object
            .methods
            .iter()
            .filter(|method| method.symbol == property.symbol)
            .count();
        if method_count == 0
            && cached_annotation_identity(store, host, property.type_node)? != published
        {
            return Err(ConcreteIndexedAccessError::InvalidCache(property.type_node));
        }
        if method_count != 0 {
            let Some(StoredCallableSetValidation::Valid { projection, .. }) =
                validate_stored_declared_method_callable_set(store, published)
            else {
                return Err(ConcreteIndexedAccessError::InvalidCache(property.type_node));
            };
            if projection.call_signatures.len() != method_count {
                return Err(ConcreteIndexedAccessError::InvalidCache(property.type_node));
            }
            let methods = object
                .methods
                .iter()
                .filter(|method| method.symbol == property.symbol);
            for (method, callable) in methods.zip(projection.call_signatures.iter()) {
                if cached_annotation_identity(store, host, method.return_type)?
                    != callable
                        .return_type
                        .ok_or(ConcreteIndexedAccessError::InvalidCache(method.return_type))?
                {
                    return Err(ConcreteIndexedAccessError::InvalidCache(method.return_type));
                }
                let parameters = callable
                    .parameters
                    .iter()
                    .copied()
                    .chain(callable.rest_parameter);
                for (parameter, expected) in method.parameters.iter().zip(parameters) {
                    if cached_annotation_identity(store, host, parameter.type_node)? != expected {
                        return Err(ConcreteIndexedAccessError::InvalidCache(
                            parameter.type_node,
                        ));
                    }
                }
            }
        }
    }

    let infos = match store.type_payload(object_type).map(TypeRecord::data) {
        Some(TypeData::Object(object)) => object.structured.index_infos.as_deref(),
        _ => None,
    }
    .unwrap_or_default();
    if infos.len() != object.indexes.len() {
        return Err(ConcreteIndexedAccessError::InvalidCache(object.node));
    }
    for (planned, info) in object.indexes.iter().zip(infos) {
        let info = store
            .index_info(*info)
            .ok_or(ConcreteIndexedAccessError::InvalidCache(
                planned.declaration,
            ))?;
        if cached_annotation_identity(store, host, planned.key_type_node)? != info.key_type()
            || cached_annotation_identity(store, host, planned.value_type_node)?
                != info.value_type()
        {
            return Err(ConcreteIndexedAccessError::InvalidCache(
                planned.value_type_node,
            ));
        }
    }
    Ok(())
}

fn validate_cold_annotation_subtree(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    root: NodeRef,
) -> Result<(), ConcreteIndexedAccessError> {
    let mut pending = vec![(root, None)];
    let mut seen = Vec::new();
    while let Some((node, expected_parent)) = pending.pop() {
        if seen.contains(&node) {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        let record = preflight_node(store, host, node)?;
        if expected_parent.is_some() && record.parent != expected_parent {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        if store.type_node_links(node).is_some_and(|links| {
            links.resolved_type.is_some() || links.outer_type_parameters.is_some()
        }) {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        seen.push(node);
        record.for_each_child(|child| {
            pending.push((NodeRef::new(node.arena, node.file, child), Some(node.node)));
        });
    }
    Ok(())
}

fn cached_annotation_identity(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<TypeId, ConcreteIndexedAccessError> {
    let record = preflight_node(store, host, node)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConcreteIndexedAccessError::InvalidCache(node))?;
    let keyword = match record.kind {
        SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
        SyntaxKind::StringKeyword => Some(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
        SyntaxKind::BigIntKeyword => Some(bootstrap.bigint_type),
        SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
        SyntaxKind::SymbolKeyword => Some(bootstrap.es_symbol_type),
        SyntaxKind::VoidKeyword => Some(bootstrap.void_type),
        SyntaxKind::UndefinedKeyword => Some(bootstrap.undefined_type),
        SyntaxKind::NullKeyword => Some(bootstrap.null_type),
        SyntaxKind::NeverKeyword => Some(bootstrap.never_type),
        SyntaxKind::ObjectKeyword => Some(bootstrap.non_primitive_type),
        SyntaxKind::IntrinsicKeyword => Some(bootstrap.intrinsic_marker_type),
        _ => None,
    };
    if let Some(keyword) = keyword {
        validate_empty_annotation_links(store, node)?;
        return Ok(keyword);
    }

    if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
        if record.kind != SyntaxKind::ParenthesizedType {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        validate_empty_annotation_links(store, node)?;
        let child = NodeRef::new(node.arena, node.file, parenthesized.type_);
        let child_record = preflight_node(store, host, child)?;
        if child_record.parent != Some(node.node)
            || child_record.range.start < record.range.start
            || child_record.range.end > record.range.end
        {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        return cached_annotation_identity(store, host, child);
    }

    if let NodeData::LiteralTypeNode(literal) = &record.data {
        let literal = NodeRef::new(node.arena, node.file, literal.literal);
        let literal_record = preflight_node(store, host, literal)?;
        if literal_record.parent != Some(node.node) || literal_record.range != record.range {
            return Err(ConcreteIndexedAccessError::InvalidCache(node));
        }
        if literal_record.kind == SyntaxKind::NullKeyword
            && matches!(literal_record.data, NodeData::KeywordExpression(_))
        {
            validate_empty_annotation_links(store, node)?;
            return Ok(bootstrap.null_type);
        }
    }

    let links = store
        .type_node_links(node)
        .ok_or(ConcreteIndexedAccessError::InvalidCache(node))?;
    if links.outer_type_parameters.is_some() {
        return Err(ConcreteIndexedAccessError::InvalidCache(node));
    }
    let type_ = links
        .resolved_type
        .ok_or(ConcreteIndexedAccessError::InvalidCache(node))?;
    store
        .type_payload(type_)
        .map(|_| type_)
        .ok_or(ConcreteIndexedAccessError::InvalidCache(node))
}

fn validate_empty_annotation_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), ConcreteIndexedAccessError> {
    if store
        .type_node_links(node)
        .is_some_and(|links| links.resolved_type.is_some() || links.outer_type_parameters.is_some())
    {
        Err(ConcreteIndexedAccessError::InvalidCache(node))
    } else {
        Ok(())
    }
}

fn primitive_domain(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Option<PrimitiveDomain> {
    let record = preflight_node(store, host, node).ok()?;
    match (&record.data, record.kind) {
        (_, SyntaxKind::StringKeyword) => Some(PrimitiveDomain::STRING),
        (_, SyntaxKind::NumberKeyword) => Some(PrimitiveDomain::NUMBER),
        (_, SyntaxKind::BooleanKeyword) => Some(PrimitiveDomain::BOOLEAN),
        (_, SyntaxKind::BigIntKeyword) => Some(PrimitiveDomain::BIGINT),
        (_, SyntaxKind::SymbolKeyword) => Some(PrimitiveDomain::SYMBOL),
        (_, SyntaxKind::NeverKeyword) => Some(PrimitiveDomain::NEVER),
        (NodeData::ParenthesizedTypeNode(parenthesized), SyntaxKind::ParenthesizedType) => {
            let child = NodeRef::new(node.arena, node.file, parenthesized.type_);
            let child_record = preflight_node(store, host, child).ok()?;
            (child != node
                && child_record.parent == Some(node.node)
                && child_record.range.start >= record.range.start
                && child_record.range.end <= record.range.end)
                .then(|| primitive_domain(store, host, child))
                .flatten()
        }
        (NodeData::UnionTypeNode(union), SyntaxKind::UnionType)
            if union.types.nodes.len() >= 2
                && !union.types.has_trailing_comma
                && union.types.range == record.range =>
        {
            let mut domain = PrimitiveDomain::NEVER;
            let mut previous_end = record.range.start;
            let mut seen = Vec::with_capacity(union.types.nodes.len());
            for child in &union.types.nodes {
                let child = NodeRef::new(node.arena, node.file, *child);
                let child_record = preflight_node(store, host, child).ok()?;
                if child == node
                    || child_record.parent != Some(node.node)
                    || child_record.range.start < previous_end
                    || child_record.range.start < record.range.start
                    || child_record.range.end > record.range.end
                    || seen.contains(&child)
                {
                    return None;
                }
                previous_end = child_record.range.end;
                seen.push(child);
                domain = domain.union(primitive_domain(store, host, child)?);
            }
            Some(domain)
        }
        _ => None,
    }
}

/// Validates the recursively resolved children and returns the existing value
/// type selected during planning. This function performs no semantic writes.
pub(super) fn finish_concrete_indexed_access(
    store: &CanonicalTypeMapperStore,
    plan: &ConcreteIndexedAccessPlan,
    object_type: TypeId,
    index_type: TypeId,
) -> Result<TypeId, ConcreteIndexedAccessError> {
    validate_transparent_object_links(store, &plan.object_wrappers)?;
    validate_index_type(store, &plan.key, index_type)?;
    let resolved = resolved_selection_type(store, plan, object_type)?;
    if plan.cached_type.is_some_and(|cached| cached != resolved) {
        return Err(ConcreteIndexedAccessError::InvalidCache(plan.node));
    }
    Ok(resolved)
}

enum DirectTypeLiteralError {
    Declared(DeclaredTypeError),
    Invalid(NodeRef),
    Unsupported(NodeRef),
}

fn direct_type_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    root: NodeRef,
) -> Result<(NodeRef, Vec<NodeRef>), DirectTypeLiteralError> {
    let mut node = root;
    let mut wrappers = Vec::new();
    loop {
        if wrappers.contains(&node) {
            return Err(DirectTypeLiteralError::Invalid(root));
        }
        let record = preflight_node(store, host, node).map_err(DirectTypeLiteralError::Declared)?;
        match (&record.data, record.kind) {
            (NodeData::TypeLiteralNode(_), SyntaxKind::TypeLiteral) => {
                return Ok((node, wrappers));
            }
            (NodeData::ParenthesizedTypeNode(parenthesized), SyntaxKind::ParenthesizedType) => {
                wrappers.push(node);
                let child = NodeRef::new(node.arena, node.file, parenthesized.type_);
                let child_record =
                    preflight_node(store, host, child).map_err(DirectTypeLiteralError::Declared)?;
                if child_record.parent != Some(node.node)
                    || child_record.range.start < record.range.start
                    || child_record.range.end > record.range.end
                {
                    return Err(DirectTypeLiteralError::Invalid(node));
                }
                node = child;
            }
            _ => return Err(DirectTypeLiteralError::Unsupported(root)),
        }
    }
}

fn classify_index(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<ConcreteIndexKey, ConcreteIndexedAccessError> {
    let record = preflight_node(store, host, node)?;
    match record.kind {
        SyntaxKind::StringKeyword => Ok(ConcreteIndexKey::String),
        SyntaxKind::NumberKeyword => Ok(ConcreteIndexKey::Number),
        SyntaxKind::LiteralType => {
            let NodeData::LiteralTypeNode(literal) = &record.data else {
                return Err(ConcreteIndexedAccessError::InvalidSyntax(node));
            };
            let literal = NodeRef::new(node.arena, node.file, literal.literal);
            let literal_record = preflight_node(store, host, literal)?;
            if literal_record.parent != Some(node.node)
                || literal_record.range != record.range
                || literal_record.flags.0 & NODE_FLAG_JSDOC != 0
            {
                return Err(ConcreteIndexedAccessError::InvalidSyntax(node));
            }
            match &literal_record.data {
                NodeData::StringLiteral(data)
                    if literal_record.kind == SyntaxKind::StringLiteral
                        && data.token_flags.0 == 0 =>
                {
                    Ok(ConcreteIndexKey::StringLiteral {
                        numeric_name: is_numeric_literal_name(&data.text),
                        value: data.text.clone(),
                    })
                }
                NodeData::NoSubstitutionTemplateLiteral(data)
                    if literal_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral
                        && data.token_flags.0 == 0
                        && data.template_flags.0 == 0 =>
                {
                    Ok(ConcreteIndexKey::StringLiteral {
                        numeric_name: is_numeric_literal_name(&data.text),
                        value: data.text.clone(),
                    })
                }
                NodeData::NumericLiteral(data)
                    if literal_record.kind == SyntaxKind::NumericLiteral
                        && data.token_flags.0 == 0 =>
                {
                    numeric_literal_value(&data.text)
                        .map(ConcreteIndexKey::NumberLiteral)
                        .ok_or(ConcreteIndexedAccessError::InvalidSyntax(node))
                }
                NodeData::PrefixUnaryExpression(prefix)
                    if literal_record.kind == SyntaxKind::PrefixUnaryExpression
                        && prefix.operator == SyntaxKind::MinusToken =>
                {
                    let operand = NodeRef::new(node.arena, node.file, prefix.operand);
                    let operand_record = preflight_node(store, host, operand)?;
                    let NodeData::NumericLiteral(data) = &operand_record.data else {
                        return Err(ConcreteIndexedAccessError::UnsupportedIndex(node));
                    };
                    if operand_record.kind != SyntaxKind::NumericLiteral
                        || operand_record.parent != Some(literal.node)
                        || operand_record.flags.0 & NODE_FLAG_JSDOC != 0
                        || data.token_flags.0 != 0
                    {
                        return Err(ConcreteIndexedAccessError::InvalidSyntax(node));
                    }
                    numeric_literal_value(&data.text)
                        .map(|value| ConcreteIndexKey::NumberLiteral(-value))
                        .ok_or(ConcreteIndexedAccessError::InvalidSyntax(node))
                }
                _ => Err(ConcreteIndexedAccessError::UnsupportedIndex(node)),
            }
        }
        _ => Err(ConcreteIndexedAccessError::UnsupportedIndex(node)),
    }
}

fn numeric_literal_value(text: &str) -> Option<Number> {
    let normalized = normalize_numeric_separators(text)?;
    let value = ts_jsnum::from_string(&normalized);
    (!value.is_nan()).then_some(value)
}

fn is_numeric_literal_name(name: &str) -> bool {
    ts_jsnum::from_string(name).to_string() == name
}

/// Returns whether an already-resolved key is a valid template index pattern.
pub(super) fn is_template_pattern_index_key(
    store: &CanonicalTypeMapperStore,
    key_type: TypeId,
) -> bool {
    store.is_template_pattern_index_key(key_type)
}

/// Checks a literal property name against one canonical template index key.
pub(super) fn template_pattern_index_matches_name(
    store: &CanonicalTypeMapperStore,
    key_type: TypeId,
    name: &str,
) -> bool {
    store.template_pattern_index_matches_name(key_type, name)
}

/// Checks one exact `prefix-${string}-suffix` index before its type is cached.
fn template_pattern_syntax_matches_name(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    pattern: NodeRef,
    name: &str,
) -> Result<bool, ConcreteIndexedAccessError> {
    let unsupported = || ConcreteIndexedAccessError::UnsupportedObjectSurface(pattern);
    let record = preflight_node(store, host, pattern)?;
    let NodeData::TemplateLiteralTypeNode(template) = &record.data else {
        return Err(unsupported());
    };
    let [span] = template.template_spans.nodes.as_slice() else {
        return Err(unsupported());
    };
    let head = NodeRef::new(pattern.arena, pattern.file, template.head);
    let span = NodeRef::new(pattern.arena, pattern.file, *span);
    let head_record = preflight_node(store, host, head)?;
    let span_record = preflight_node(store, host, span)?;
    let NodeData::TemplateHead(head_data) = &head_record.data else {
        return Err(unsupported());
    };
    let NodeData::TemplateLiteralTypeSpan(span_data) = &span_record.data else {
        return Err(unsupported());
    };
    let placeholder = NodeRef::new(pattern.arena, pattern.file, span_data.type_);
    let tail = NodeRef::new(pattern.arena, pattern.file, span_data.literal);
    let placeholder_record = preflight_node(store, host, placeholder)?;
    let tail_record = preflight_node(store, host, tail)?;
    let NodeData::TemplateTail(tail_data) = &tail_record.data else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::TemplateLiteralType
        || record.flags.0 != 0
        || template.template_spans.has_trailing_comma
        || head_record.kind != SyntaxKind::TemplateHead
        || head_record.flags.0 != 0
        || head_record.parent != Some(pattern.node)
        || head_data.token_flags.0 != 0
        || head_data.template_flags.0 != 0
        || span_record.kind != SyntaxKind::TemplateLiteralTypeSpan
        || span_record.flags.0 != 0
        || span_record.parent != Some(pattern.node)
        || placeholder_record.kind != SyntaxKind::StringKeyword
        || placeholder_record.flags.0 != 0
        || placeholder_record.parent != Some(span.node)
        || !matches!(placeholder_record.data, NodeData::KeywordTypeNode(_))
        || tail_record.kind != SyntaxKind::TemplateTail
        || tail_record.flags.0 != 0
        || tail_record.parent != Some(span.node)
        || tail_data.token_flags.0 != 0
        || tail_data.template_flags.0 != 0
        || head_data.text.is_empty() && tail_data.text.is_empty()
        || head_record.range.start < record.range.start
        || head_record.range.end > placeholder_record.range.start
        || placeholder_record.range.end > tail_record.range.start
        || tail_record.range.end > record.range.end
    {
        return Err(unsupported());
    }

    let matches = name
        .strip_prefix(&head_data.text)
        .is_some_and(|remaining| remaining.ends_with(&tail_data.text));
    if let Some(links) = store.type_node_links(pattern) {
        if links.outer_type_parameters.is_some() {
            return Err(ConcreteIndexedAccessError::InvalidCache(pattern));
        }
        if let Some(key_type) = links.resolved_type
            && (!is_template_pattern_index_key(store, key_type)
                || template_pattern_index_matches_name(store, key_type, name) != matches)
        {
            return Err(ConcreteIndexedAccessError::InvalidCache(pattern));
        }
    }
    Ok(matches)
}

fn select_concrete_member(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    object: &PropertyObjectPlan,
    key: &ConcreteIndexKey,
    index: NodeRef,
) -> Result<ConcreteIndexedSelection, ConcreteIndexedAccessError> {
    if !object.call_signatures.is_empty() {
        return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
            object.node,
        ));
    }

    let literal_property_name = key.literal_property_name();
    if let Some(property) = literal_property_name.as_ref().and_then(|name| {
        object
            .properties
            .iter()
            .find(|property| name.matches(&property.name))
    }) {
        if property.optional {
            return Err(ConcreteIndexedAccessError::OptionalProperty {
                node: index,
                property: property.symbol,
            });
        }
        return Ok(ConcreteIndexedSelection::Property(property.symbol));
    }

    if object.indexes.is_empty() {
        return if object.properties.is_empty() {
            Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                object.node,
            ))
        } else if literal_property_name.is_some() {
            Err(ConcreteIndexedAccessError::MissingProperty(index))
        } else {
            Err(ConcreteIndexedAccessError::MissingIndexSignature(index))
        };
    }

    let mut string = None;
    let mut number = None;
    let mut template = None;
    for (slot, planned) in object.indexes.iter().enumerate() {
        let target = match store.source_node_kind(planned.key_type_node) {
            Some(SyntaxKind::StringKeyword) => Some(&mut string),
            Some(SyntaxKind::NumberKeyword) => Some(&mut number),
            Some(SyntaxKind::TemplateLiteralType) => {
                let ConcreteIndexKey::StringLiteral { value, .. } = key else {
                    continue;
                };
                if template_pattern_syntax_matches_name(store, host, planned.key_type_node, value)?
                {
                    Some(&mut template)
                } else {
                    None
                }
            }
            _ => {
                return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                    object.node,
                ));
            }
        };
        if target.is_some_and(|target| target.replace(slot).is_some()) {
            return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                object.node,
            ));
        }
    }
    let number = number.filter(|_| key.number_applicable());
    if number.is_some() && template.is_some() {
        return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
            object.node,
        ));
    }
    let (slot, kind) = template
        .map(|slot| (slot, PlannedIndexKind::Template))
        .or_else(|| number.map(|slot| (slot, PlannedIndexKind::Number)))
        .or_else(|| string.map(|slot| (slot, PlannedIndexKind::String)))
        .ok_or(ConcreteIndexedAccessError::MissingIndexSignature(index))?;
    Ok(ConcreteIndexedSelection::Index { slot, kind })
}

fn validate_parent_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<TypeId>, ConcreteIndexedAccessError> {
    let Some(links) = store.type_node_links(node) else {
        return Ok(None);
    };
    if links.outer_type_parameters.is_some()
        || links
            .resolved_type
            .is_some_and(|type_| store.type_payload(type_).is_none())
    {
        return Err(ConcreteIndexedAccessError::InvalidCache(node));
    }
    Ok(links.resolved_type)
}

fn validate_transparent_object_links(
    store: &CanonicalTypeMapperStore,
    wrappers: &[NodeRef],
) -> Result<(), ConcreteIndexedAccessError> {
    if wrappers.iter().any(|wrapper| {
        store.type_node_links(*wrapper).is_some_and(|links| {
            links.resolved_type.is_some() || links.outer_type_parameters.is_some()
        })
    }) {
        return Err(ConcreteIndexedAccessError::InvalidCache(wrappers[0]));
    }
    Ok(())
}

fn cached_index_type(
    store: &CanonicalTypeMapperStore,
    plan: &ConcreteIndexedAccessPlan,
) -> Result<TypeId, ConcreteIndexedAccessError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConcreteIndexedAccessError::InvalidCache(plan.index))?;
    match &plan.key {
        ConcreteIndexKey::String => {
            validate_keyword_index_links(store, plan.index)?;
            Ok(bootstrap.string_type)
        }
        ConcreteIndexKey::Number => {
            validate_keyword_index_links(store, plan.index)?;
            Ok(bootstrap.number_type)
        }
        ConcreteIndexKey::StringLiteral { .. } | ConcreteIndexKey::NumberLiteral(_) => {
            let links = store
                .type_node_links(plan.index)
                .ok_or(ConcreteIndexedAccessError::InvalidCache(plan.index))?;
            if links.outer_type_parameters.is_some() {
                return Err(ConcreteIndexedAccessError::InvalidCache(plan.index));
            }
            links
                .resolved_type
                .ok_or(ConcreteIndexedAccessError::InvalidCache(plan.index))
        }
    }
}

fn validate_keyword_index_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), ConcreteIndexedAccessError> {
    if store
        .type_node_links(node)
        .is_some_and(|links| links.resolved_type.is_some() || links.outer_type_parameters.is_some())
    {
        return Err(ConcreteIndexedAccessError::InvalidCache(node));
    }
    Ok(())
}

fn validate_existing_index_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    key: &ConcreteIndexKey,
) -> Result<(), ConcreteIndexedAccessError> {
    match key {
        ConcreteIndexKey::String | ConcreteIndexKey::Number => {
            validate_keyword_index_links(store, node)
        }
        ConcreteIndexKey::StringLiteral { .. } | ConcreteIndexKey::NumberLiteral(_) => {
            let Some(links) = store.type_node_links(node) else {
                return Ok(());
            };
            if links.outer_type_parameters.is_some() {
                return Err(ConcreteIndexedAccessError::InvalidCache(node));
            }
            if let Some(type_) = links.resolved_type {
                validate_index_type(store, key, type_)
                    .map_err(|_| ConcreteIndexedAccessError::InvalidCache(node))?;
            }
            Ok(())
        }
    }
}

fn validate_index_type(
    store: &CanonicalTypeMapperStore,
    key: &ConcreteIndexKey,
    type_: TypeId,
) -> Result<(), ConcreteIndexedAccessError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConcreteIndexedAccessError::InvalidType(type_))?;
    match key {
        ConcreteIndexKey::String if type_ == bootstrap.string_type => Ok(()),
        ConcreteIndexKey::Number if type_ == bootstrap.number_type => Ok(()),
        ConcreteIndexKey::StringLiteral { value, .. }
            if bootstrap.cached_string_literal_type(value) == Some(type_) =>
        {
            store.validate_union_constituent(type_)?;
            let record = store
                .type_payload(type_)
                .ok_or(ConcreteIndexedAccessError::InvalidType(type_))?;
            if record.flags() == TypeFlags::STRING_LITERAL
                && matches!(record.data(), TypeData::Literal(literal)
                    if literal.regular_type == type_
                        && literal.value == LiteralValue::String(value.clone()))
            {
                Ok(())
            } else {
                Err(ConcreteIndexedAccessError::InvalidType(type_))
            }
        }
        ConcreteIndexKey::NumberLiteral(value)
            if bootstrap.cached_number_literal_type(*value) == Some(type_) =>
        {
            store.validate_union_constituent(type_)?;
            let record = store
                .type_payload(type_)
                .ok_or(ConcreteIndexedAccessError::InvalidType(type_))?;
            if record.flags() == TypeFlags::NUMBER_LITERAL
                && matches!(record.data(), TypeData::Literal(literal)
                    if literal.regular_type == type_
                        && literal.value == LiteralValue::Number(*value))
            {
                Ok(())
            } else {
                Err(ConcreteIndexedAccessError::InvalidType(type_))
            }
        }
        _ => Err(ConcreteIndexedAccessError::InvalidType(type_)),
    }
}

fn resolved_selection_type(
    store: &CanonicalTypeMapperStore,
    plan: &ConcreteIndexedAccessPlan,
    object_type: TypeId,
) -> Result<TypeId, ConcreteIndexedAccessError> {
    let state = object_members::type_literal_state(store, &plan.object_plan)?.ok_or(
        ConcreteIndexedAccessError::InvalidCache(plan.object_literal),
    )?;
    if !matches!(state, PropertyObjectState::Resolved(type_) if type_ == object_type) {
        return Err(ConcreteIndexedAccessError::InvalidCache(
            plan.object_literal,
        ));
    }
    let result =
        match plan.selection {
            ConcreteIndexedSelection::Property(property) => store
                .value_symbol_links(property)
                .and_then(|links| links.resolved_type)
                .ok_or(ConcreteIndexedAccessError::InvalidCache(
                    plan.object_literal,
                ))?,
            ConcreteIndexedSelection::Index { slot, kind } => {
                let record = store
                    .type_payload(object_type)
                    .ok_or(ConcreteIndexedAccessError::InvalidType(object_type))?;
                let TypeData::Object(object) = record.data() else {
                    return Err(ConcreteIndexedAccessError::InvalidType(object_type));
                };
                let infos = object.structured.index_infos.as_deref().ok_or(
                    ConcreteIndexedAccessError::InvalidCache(plan.object_literal),
                )?;
                if infos.len() != plan.object_plan.indexes.len() {
                    return Err(ConcreteIndexedAccessError::InvalidCache(
                        plan.object_literal,
                    ));
                }
                let info = store.index_info(infos[slot]).ok_or(
                    ConcreteIndexedAccessError::InvalidCache(plan.object_literal),
                )?;
                let bootstrap = store
                    .intrinsic_bootstrap()
                    .ok_or(ConcreteIndexedAccessError::InvalidType(object_type))?;
                let expected_key = match kind {
                    PlannedIndexKind::String => bootstrap.string_type,
                    PlannedIndexKind::Number => bootstrap.number_type,
                    PlannedIndexKind::Template => {
                        let key_type = store
                            .type_node_links(plan.object_plan.indexes[slot].key_type_node)
                            .and_then(|links| links.resolved_type)
                            .ok_or(ConcreteIndexedAccessError::InvalidCache(
                                plan.object_literal,
                            ))?;
                        let ConcreteIndexKey::StringLiteral { value, .. } = &plan.key else {
                            return Err(ConcreteIndexedAccessError::InvalidCache(
                                plan.object_literal,
                            ));
                        };
                        if !is_template_pattern_index_key(store, key_type)
                            || !template_pattern_index_matches_name(store, key_type, value)
                        {
                            return Err(ConcreteIndexedAccessError::InvalidCache(
                                plan.object_literal,
                            ));
                        }
                        key_type
                    }
                };
                if info.key_type() != expected_key
                    || info.declaration() != Some(plan.object_plan.indexes[slot].declaration)
                {
                    return Err(ConcreteIndexedAccessError::InvalidCache(
                        plan.object_literal,
                    ));
                }
                info.value_type()
            }
        };
    store
        .type_payload(result)
        .map(|_| result)
        .ok_or(ConcreteIndexedAccessError::InvalidType(result))
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        CheckFlags, EscapedName, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::{
        AccessFlags, get_deferred_indexed_access_type, is_template_pattern_index_key,
        template_pattern_index_matches_name,
    };
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
        DeclaredTypeLinks, IntrinsicBootstrapOptions, TypeData, TypeId,
    };

    fn checker_context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/indexed-access-unit.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn indexed_access_node(parsed: &ParseResult) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::IndexedAccessType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FileId::new(0),
                    node,
                ))
            })
            .expect("the source must contain one indexed-access type")
    }

    fn owned_type_parameter(store: &mut CanonicalTypeMapperStore, name: &str) -> TypeId {
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_PARAMETER,
            EscapedName::source(name),
            CheckFlags::NONE,
        );
        let type_ = store.alloc_type_parameter(Some(symbol)).unwrap();
        assert!(store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(type_),
                ..DeclaredTypeLinks::default()
            },
        ));
        type_
    }

    #[test]
    fn deferred_indexed_access_normalizes_flags_and_reuses_owned_identity() {
        let mut store = CanonicalTypeMapperStore::new();
        let object = owned_type_parameter(&mut store, "U");
        let index = owned_type_parameter(&mut store, "P");
        let before = store.type_len();

        let plain = get_deferred_indexed_access_type(
            &mut store,
            object,
            index,
            AccessFlags::WRITING | AccessFlags::CACHE_SYMBOL,
        )
        .unwrap();
        let TypeData::IndexedAccess(data) = store.type_payload(plain).unwrap().data() else {
            panic!("the generic access must retain its deferred type")
        };
        assert_eq!(data.object_type, object);
        assert_eq!(data.index_type, index);
        assert_eq!(data.access_flags, AccessFlags::NONE);
        assert_eq!(
            get_deferred_indexed_access_type(&mut store, object, index, AccessFlags::NONE),
            Some(plain),
        );

        let optional = get_deferred_indexed_access_type(
            &mut store,
            object,
            index,
            AccessFlags::INCLUDE_UNDEFINED | AccessFlags::CONTEXTUAL,
        )
        .unwrap();
        assert_ne!(optional, plain);
        assert_eq!(
            get_deferred_indexed_access_type(
                &mut store,
                object,
                index,
                AccessFlags::INCLUDE_UNDEFINED | AccessFlags::WRITING,
            ),
            Some(optional),
        );
        assert_eq!(store.type_len(), before + 2);
    }

    #[test]
    fn deferred_indexed_access_rejects_unowned_and_poisoned_type_identities() {
        let mut store = CanonicalTypeMapperStore::new();
        let object = owned_type_parameter(&mut store, "U");
        let index = owned_type_parameter(&mut store, "P");
        let mut foreign_store = CanonicalTypeMapperStore::new();
        let foreign = owned_type_parameter(&mut foreign_store, "Foreign");
        let orphan = store.alloc_type_parameter(None).unwrap();
        let before = store.type_len();

        for (object, index) in [(foreign, index), (object, foreign), (orphan, index)] {
            assert_eq!(
                get_deferred_indexed_access_type(&mut store, object, index, AccessFlags::NONE),
                None,
            );
            assert_eq!(store.type_len(), before);
        }

        let cached =
            get_deferred_indexed_access_type(&mut store, object, index, AccessFlags::NONE).unwrap();
        let owner = store.type_payload(object).unwrap().symbol().unwrap();
        assert!(store.set_type_symbol(cached, Some(owner)));
        let poisoned = store.type_len();
        assert_eq!(
            get_deferred_indexed_access_type(&mut store, object, index, AccessFlags::NONE),
            None,
        );
        assert_eq!(store.type_len(), poisoned);
    }

    #[test]
    fn concrete_template_pattern_index_resolves_and_replays_without_allocations() {
        let parsed =
            parse_source_file("type Value = { [name: `do-${string}`]: number }['do-click'];");
        let indexed = indexed_access_node(&parsed);
        let mut context = checker_context(&parsed);
        let expected = context.store().intrinsic_bootstrap().unwrap().number_type;

        assert_eq!(context.get_type_from_type_node(indexed), Ok(expected));
        let NodeData::IndexedAccessTypeNode(access) = &parsed.arena.get(indexed.node).unwrap().data
        else {
            unreachable!("the fixture retained its indexed-access node")
        };
        let object = NodeRef::new(indexed.arena, indexed.file, access.object_type);
        let object_type = context
            .store()
            .type_node_links(object)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let TypeData::Object(object_record) =
            context.store().type_payload(object_type).unwrap().data()
        else {
            panic!("the template index belongs to an anonymous type literal")
        };
        let [index] = object_record.structured.index_infos.as_deref().unwrap() else {
            panic!("the literal publishes exactly one template index")
        };
        let index = context.store().index_info(*index).unwrap();
        assert!(is_template_pattern_index_key(
            context.store(),
            index.key_type(),
        ));
        assert_eq!(index.value_type(), expected);
        let warm = (
            context.store().type_len(),
            context.store().index_info_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().type_node_links(indexed).cloned(),
        );

        assert_eq!(context.get_type_from_type_node(indexed), Ok(expected));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().index_info_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().type_node_links(indexed).cloned(),
            ),
            warm,
        );
    }

    #[test]
    fn concrete_template_indexes_preserve_exact_property_and_string_fallback_order() {
        for (source, expected_string) in [
            (
                concat!(
                    "type Value = { ",
                    "[name: `do-${string}`]: number; ",
                    "'ns:thing': string; ",
                    "}['ns:thing'];",
                ),
                true,
            ),
            (
                concat!(
                    "type Value = { ",
                    "[name: string]: string | number; ",
                    "[name: `do-${string}`]: number; ",
                    "}['do-click'];",
                ),
                false,
            ),
            (
                concat!(
                    "type Value = { ",
                    "[name: string]: string | number; ",
                    "[name: `do-${string}`]: number; ",
                    "}['other'];",
                ),
                true,
            ),
            (
                "type Value = { [name: `${string}-ready`]: string }['widget-ready'];",
                true,
            ),
        ] {
            let parsed = parse_source_file(source);
            let indexed = indexed_access_node(&parsed);
            let mut context = checker_context(&parsed);
            let (string, number) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let expected = if expected_string { string } else { number };
            let resolved = context.get_type_from_type_node(indexed).unwrap();
            if source.contains("}['other']") {
                let TypeData::Union(union) = context.store().type_payload(resolved).unwrap().data()
                else {
                    panic!("a nonmatching pattern falls back to the string index")
                };
                assert!(union.union.types.contains(&string));
                assert!(union.union.types.contains(&number));
            } else {
                assert_eq!(resolved, expected, "source: {source}");
            }
        }
    }

    #[test]
    fn unsupported_template_indexes_fail_before_cache_publication() {
        for source in [
            "type Value = { [name: `do-${string}`]: number }['ns:thing'];",
            concat!(
                "type Value = { ",
                "[name: `do-${string}`]: number; ",
                "'do-click': string; ",
                "}['do-click'];",
            ),
            concat!(
                "type Value = { ",
                "[name: string]: number; ",
                "[name: `do-${string}`]: string; ",
                "}['do-click'];",
            ),
            concat!(
                "type Value = { ",
                "[name: `do-${string}`]: number; ",
                "[name: `${string}-ready`]: string; ",
                "}['do-ready'];",
            ),
            "type Value = { [name: `id-${number}`]: string }['id-1'];",
        ] {
            let parsed = parse_source_file(source);
            let indexed = indexed_access_node(&parsed);
            let mut context = checker_context(&parsed);
            let before = (
                context.store().type_len(),
                context.store().index_info_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert!(
                context.get_type_from_type_node(indexed).is_err(),
                "source: {source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().index_info_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "source: {source}",
            );
            assert!(context.store().type_node_links(indexed).is_none());
        }
    }

    #[test]
    fn template_pattern_index_matches_only_compatible_property_names() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let pattern = store
            .get_template_literal_type(&["do-".to_owned(), String::new()], &[string])
            .unwrap();

        assert!(is_template_pattern_index_key(&store, pattern));
        assert!(template_pattern_index_matches_name(
            &store, pattern, "do-click"
        ));
        assert!(template_pattern_index_matches_name(&store, pattern, "do-"));
        assert!(!template_pattern_index_matches_name(
            &store, pattern, "ns:thing"
        ));
        assert!(!template_pattern_index_matches_name(
            &store,
            pattern,
            "redo-click"
        ));
    }

    #[test]
    fn numeric_template_pattern_indexes_reject_non_numeric_substitutions() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let pattern = store
            .get_template_literal_type(&["id-".to_owned(), String::new()], &[number])
            .unwrap();

        assert!(template_pattern_index_matches_name(
            &store, pattern, "id-12"
        ));
        assert!(!template_pattern_index_matches_name(
            &store, pattern, "id-value"
        ));
    }

    #[test]
    fn template_pattern_indexes_reuse_canonical_placeholder_matching() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number, bigint) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.bigint_type,
        );
        let uppercase_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Uppercase"),
            CheckFlags::NONE,
        );
        let uppercase = store
            .get_string_mapping_type(uppercase_symbol, string)
            .unwrap();
        let uppercase_pattern = store
            .get_template_literal_type(&["key-".to_owned(), String::new()], &[uppercase])
            .unwrap();
        let adjacent = store
            .get_template_literal_type(
                &[String::new(), String::new(), String::new()],
                &[string, number],
            )
            .unwrap();
        let numeric = store
            .get_template_literal_type(&["id-".to_owned(), String::new()], &[number])
            .unwrap();
        let integral = store
            .get_template_literal_type(&["big-".to_owned(), String::new()], &[bigint])
            .unwrap();

        assert!(is_template_pattern_index_key(&store, uppercase_pattern));
        for (pattern, name, expected) in [
            (uppercase_pattern, "key-ABC", true),
            (uppercase_pattern, "key-Abc", false),
            (adjacent, "a42", true),
            (adjacent, "1", false),
            (numeric, "id-1.0", true),
            (numeric, "id-NaN", false),
            (numeric, "id-Infinity", false),
            (integral, "big-0xff", true),
            (
                integral,
                "big-340282366920938463463374607431768211456",
                true,
            ),
            (integral, "big-+1", false),
        ] {
            assert_eq!(
                template_pattern_index_matches_name(&store, pattern, name),
                expected,
                "pattern value {name}",
            );
        }
    }
}
