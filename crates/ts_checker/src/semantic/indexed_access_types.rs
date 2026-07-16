//! Exact concrete indexed-access type-node selection.
//!
//! This leaf owns the allocation-free success prefix of pinned
//! `getTypeFromIndexedAccessTypeNode`, `getIndexedAccessTypeOrUndefined`, and
//! `getPropertyTypeForIndexType`. The object operand is one direct, possibly
//! parenthesized type literal admitted by [`super::object_members`]. Required
//! own properties and string/number index signatures are supported, including
//! mixed surfaces: an exact literal property wins, then an applicable number
//! index wins over a string index. Generic or named operands, optional
//! properties, union keys, tuples, apparent types, and diagnostic recovery
//! remain explicit boundaries.
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
    declared::preflight_node,
    object_members::{self, PropertyObjectError, PropertyObjectPlan, PropertyObjectState},
    type_nodes::normalize_numeric_separators,
    type_records::{LiteralValue, TypeData},
    types::TypeFlags,
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
    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn object(&self) -> NodeRef {
        self.object
    }

    pub(super) const fn index(&self) -> NodeRef {
        self.index
    }

    pub(super) const fn cached_type(&self) -> Option<TypeId> {
        self.cached_type
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
    let object_plan = object_members::plan_type_literal(store, host, object_literal, None)?;
    let key = classify_index(store, host, index)?;
    let selection = select_concrete_member(store, &object_plan, &key, index)?;

    validate_transparent_object_links(store, &object_wrappers)?;
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

fn select_concrete_member(
    store: &CanonicalTypeMapperStore,
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
    for (slot, planned) in object.indexes.iter().enumerate() {
        let target = match store.source_node_kind(planned.key_type_node) {
            Some(SyntaxKind::StringKeyword) => &mut string,
            Some(SyntaxKind::NumberKeyword) => &mut number,
            _ => {
                return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                    object.node,
                ));
            }
        };
        if target.replace(slot).is_some() {
            return Err(ConcreteIndexedAccessError::UnsupportedObjectSurface(
                object.node,
            ));
        }
    }
    let (slot, kind) = if key.number_applicable() {
        number
            .map(|slot| (slot, PlannedIndexKind::Number))
            .or_else(|| string.map(|slot| (slot, PlannedIndexKind::String)))
    } else {
        string.map(|slot| (slot, PlannedIndexKind::String))
    }
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
