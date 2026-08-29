//! Canonical mapped object types and lazy mapped properties.
//!
//! The implementation follows `getTypeFromMappedTypeNode`,
//! `resolveMappedTypeMembers`, and `getTypeOfMappedSymbol` from the pinned
//! TypeScript Go checker. Source routing supplies the already-resolved type
//! operands. This module owns mapped records, transient property symbols,
//! modifier preservation, and delayed property type computation.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind, append_js_string};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolTableId, semantic::PreparedSymbolTable,
};
use xxhash_rust::xxh3::Xxh3;

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, IndexInfoId, TypeId,
    TypeMapperId, TypeResolutionTarget, TypeSystemPropertyName,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    declared::{
        cached_ordinary_type_parameter_owner, preflight_node, preflight_type_parameter_symbol,
        type_list_key,
    },
    indexed_access_types::{
        cached_deferred_indexed_access_type, is_template_pattern_index_key,
        template_pattern_index_matches_name,
    },
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession, MappedTemplateFrame,
        cached_instantiation_with_vector, canonical_anonymous_union,
        instantiate_type_with_vector_and_session, instantiated_member_type_matches,
        with_mapped_template_frame,
    },
    instantiated_members::{RecoveredPropertyTypeIdentity, property_recovery_type_identity},
    keyof_types::{
        NongenericKeyofError, cached_nongeneric_keyof_type, plan_nongeneric_keyof_type,
        resolve_nongeneric_keyof_type,
    },
    links::{MappedSymbolLinks, TypeNodeLinks, ValueSymbolLinks},
    mapper::TypeMapperApplication,
    signatures::{IndexFlags, IndexInfo},
    store::SourceNodeParent,
    template_types::{MAX_TEMPLATE_UNION_SIZE, StringMappingKind},
    type_nodes::type_alias_instantiation_cache_key,
    type_records::{
        CacheHashKey, LiteralValue, StructuredTypeData, TypeCacheState, TypeData, TypeRecord,
    },
    types::{AccessFlags, ObjectFlags, TypeFlags},
};

/// The exact modifier bits used by the upstream mapped type checker.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct MappedTypeModifiers(u8);

impl MappedTypeModifiers {
    pub const NONE: Self = Self(0);
    pub const INCLUDE_READONLY: Self = Self(1 << 0);
    pub const EXCLUDE_READONLY: Self = Self(1 << 1);
    pub const INCLUDE_OPTIONAL: Self = Self(1 << 2);
    pub const EXCLUDE_OPTIONAL: Self = Self(1 << 3);

    #[must_use]
    pub const fn bits(self) -> u8 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// Decodes the token nodes retained by the mapped type parser.
    #[must_use]
    pub fn from_token_kinds(
        readonly: Option<SyntaxKind>,
        optional: Option<SyntaxKind>,
    ) -> Option<Self> {
        let readonly = match readonly {
            None => Self::NONE,
            Some(SyntaxKind::ReadonlyKeyword | SyntaxKind::PlusToken) => Self::INCLUDE_READONLY,
            Some(SyntaxKind::MinusToken) => Self::EXCLUDE_READONLY,
            Some(_) => return None,
        };
        let optional = match optional {
            None => Self::NONE,
            Some(SyntaxKind::QuestionToken | SyntaxKind::PlusToken) => Self::INCLUDE_OPTIONAL,
            Some(SyntaxKind::MinusToken) => Self::EXCLUDE_OPTIONAL,
            Some(_) => return None,
        };
        Some(readonly | optional)
    }

    #[must_use]
    pub const fn valid(self) -> bool {
        self.0 & !0b1111 == 0
            && !(self.contains(Self::INCLUDE_READONLY) && self.contains(Self::EXCLUDE_READONLY))
            && !(self.contains(Self::INCLUDE_OPTIONAL) && self.contains(Self::EXCLUDE_OPTIONAL))
    }
}

impl std::ops::BitOr for MappedTypeModifiers {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

/// Resolved inputs needed to create one source-owned mapped type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MappedTypeRequest {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    type_parameter: TypeId,
    constraint_type: TypeId,
    template_type: TypeId,
    modifiers_type: TypeId,
    name_type: Option<TypeId>,
}

impl MappedTypeRequest {
    #[must_use]
    pub const fn new(
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        type_parameter: TypeId,
        constraint_type: TypeId,
        template_type: TypeId,
        modifiers_type: TypeId,
    ) -> Self {
        Self {
            declaration,
            symbol,
            type_parameter,
            constraint_type,
            template_type,
            modifiers_type,
            name_type: None,
        }
    }

    #[must_use]
    pub const fn with_name_type(mut self, name_type: TypeId) -> Self {
        self.name_type = Some(name_type);
        self
    }

    #[must_use]
    pub const fn declaration(self) -> NodeRef {
        self.declaration
    }

    #[must_use]
    pub const fn type_parameter(self) -> TypeId {
        self.type_parameter
    }

    #[must_use]
    pub const fn constraint_type(self) -> TypeId {
        self.constraint_type
    }

    #[must_use]
    pub const fn template_type(self) -> TypeId {
        self.template_type
    }

    #[must_use]
    pub const fn modifiers_type(self) -> TypeId {
        self.modifiers_type
    }
}

/// Cached structured members published for one mapped type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedMappedTypeMembers {
    type_: TypeId,
    members: SymbolTableId,
    properties: Vec<SemanticSymbolId>,
}

impl ResolvedMappedTypeMembers {
    #[must_use]
    pub const fn type_id(&self) -> TypeId {
        self.type_
    }

    #[must_use]
    pub const fn members(&self) -> SymbolTableId {
        self.members
    }

    #[must_use]
    pub fn properties(&self) -> &[SemanticSymbolId] {
        &self.properties
    }
}

/// One lazily evaluated mapped property.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolvedMappedProperty {
    symbol: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
    readonly: bool,
}

impl ResolvedMappedProperty {
    #[must_use]
    pub const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    #[must_use]
    pub const fn type_id(self) -> TypeId {
        self.type_
    }

    #[must_use]
    pub const fn is_optional(self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn is_readonly(self) -> bool {
        self.readonly
    }
}

/// Ordered properties of an authenticated finite `Record<K, T>` instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FiniteRecordMappedProjection {
    pub(super) type_: TypeId,
    pub(super) declaration: NodeRef,
    pub(super) members: SymbolTableId,
    pub(super) properties: Vec<FiniteRecordMappedProperty>,
}

/// One validated transient property owned by a finite mapped `Record`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FiniteRecordMappedProperty {
    pub(super) symbol: SemanticSymbolId,
    pub(super) name: EscapedName,
    pub(super) type_: TypeId,
    pub(super) optional: bool,
    pub(super) readonly: bool,
}

/// An invalid mapped record, unsupported input, or poisoned lazy cache.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MappedTypeError {
    Declared(DeclaredTypeError),
    BootstrapUninitialized,
    InvalidDeclaration(NodeRef),
    InvalidSymbol(SemanticSymbolId),
    InvalidTypeParameter(TypeId),
    InvalidMappedType(TypeId),
    InvalidModifiers,
    InvalidSource(TypeId),
    UnsupportedSource(TypeId),
    UnsupportedConstraint(TypeId),
    UnsupportedNameType(TypeId),
    UnsupportedTemplate(TypeId),
    InvalidCachedMembers(TypeId),
    InvalidCachedProperty(SemanticSymbolId),
    RecursiveMembers(TypeId),
    CircularProperty(SemanticSymbolId),
    CrossProductTooLarge { size: usize, limit: usize },
    InstantiationDepthLimit { depth: usize, limit: usize },
    InstantiationCountLimit { count: usize, limit: usize },
    Capacity,
}

impl std::fmt::Display for MappedTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Declared(error) => error.fmt(formatter),
            Self::BootstrapUninitialized => {
                formatter.write_str("mapped types require checker bootstrap")
            }
            Self::InvalidDeclaration(node) => {
                write!(formatter, "invalid mapped type declaration {node:?}")
            }
            Self::InvalidSymbol(symbol) => {
                write!(formatter, "invalid mapped type symbol {symbol:?}")
            }
            Self::InvalidTypeParameter(type_) => {
                write!(formatter, "invalid mapped type parameter {type_:?}")
            }
            Self::InvalidMappedType(type_) => write!(formatter, "invalid mapped type {type_:?}"),
            Self::InvalidModifiers => {
                formatter.write_str("mapped type modifiers are contradictory")
            }
            Self::InvalidSource(type_) => {
                write!(formatter, "mapped type source {type_:?} is malformed")
            }
            Self::UnsupportedSource(type_) => write!(
                formatter,
                "mapped type source {type_:?} is not a resolved property object"
            ),
            Self::UnsupportedConstraint(type_) => write!(
                formatter,
                "mapped type constraint {type_:?} is not a finite property-key set"
            ),
            Self::UnsupportedNameType(type_) => write!(
                formatter,
                "mapped property name {type_:?} cannot be resolved"
            ),
            Self::UnsupportedTemplate(type_) => write!(
                formatter,
                "mapped property template {type_:?} cannot be instantiated"
            ),
            Self::InvalidCachedMembers(type_) => write!(
                formatter,
                "mapped type {type_:?} has invalid cached members"
            ),
            Self::InvalidCachedProperty(symbol) => write!(
                formatter,
                "mapped property {symbol:?} has invalid cached links"
            ),
            Self::RecursiveMembers(type_) => {
                write!(
                    formatter,
                    "mapped type {type_:?} recursively resolves its members"
                )
            }
            Self::CircularProperty(symbol) => {
                write!(formatter, "mapped property {symbol:?} references itself")
            }
            Self::CrossProductTooLarge { size, limit } => {
                write!(
                    formatter,
                    "mapped key union size {size} reached the limit {limit}"
                )
            }
            Self::InstantiationDepthLimit { depth, limit } => write!(
                formatter,
                "mapped type instantiation depth {depth} reached the limit {limit}"
            ),
            Self::InstantiationCountLimit { count, limit } => write!(
                formatter,
                "mapped type instantiation count {count} reached the limit {limit}"
            ),
            Self::Capacity => formatter.write_str("mapped type allocation capacity was exhausted"),
        }
    }
}

impl std::error::Error for MappedTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Declared(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DeclaredTypeError> for MappedTypeError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::Declared(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)] // Shared type-node dispatch is integrated by its owning agent.
pub(super) struct MappedTypeDeclarationPlan {
    node: NodeRef,
    symbol: SemanticSymbolId,
    type_parameter_symbol: SemanticSymbolId,
    constraint: NodeRef,
    template: Option<NodeRef>,
    name_type: Option<NodeRef>,
    modifiers_source: Option<NodeRef>,
    modifiers: MappedTypeModifiers,
}

#[allow(dead_code)] // Shared type-node dispatch consumes these planned source operands.
impl MappedTypeDeclarationPlan {
    pub(super) const fn node(self) -> NodeRef {
        self.node
    }

    pub(super) const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn type_parameter_symbol(self) -> SemanticSymbolId {
        self.type_parameter_symbol
    }

    pub(super) const fn constraint(self) -> NodeRef {
        self.constraint
    }

    pub(super) const fn template(self) -> Option<NodeRef> {
        self.template
    }

    pub(super) const fn name_type(self) -> Option<NodeRef> {
        self.name_type
    }

    pub(super) const fn modifiers_source(self) -> Option<NodeRef> {
        self.modifiers_source
    }

    pub(super) const fn modifiers(self) -> MappedTypeModifiers {
        self.modifiers
    }
}

/// Validates one mapped declaration without allocating semantic records.
#[allow(dead_code)] // Shared type-node dispatch is integrated by its owning agent.
pub(super) fn plan_mapped_type_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<MappedTypeDeclarationPlan, MappedTypeError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::MappedTypeNode(mapped) = &record.data else {
        return Err(MappedTypeError::InvalidDeclaration(node));
    };
    if record.kind != SyntaxKind::MappedType || mapped.members.is_some() {
        return Err(MappedTypeError::InvalidDeclaration(node));
    }
    let bound = host
        .bound_file(node)
        .ok_or(MappedTypeError::InvalidDeclaration(node))?;
    let symbol = bound
        .symbol(node)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(MappedTypeError::InvalidDeclaration(node))?;
    let owner = store
        .symbol(symbol)
        .ok_or(MappedTypeError::InvalidSymbol(symbol))?;
    if owner.flags() != SymbolFlags::TYPE_LITERAL
        || !owner
            .declarations()
            .is_some_and(|declarations| declarations.contains(&node))
    {
        return Err(MappedTypeError::InvalidSymbol(symbol));
    }

    let parameter = NodeRef::new(node.arena, node.file, mapped.type_parameter);
    let parameter_record = preflight_node(store, host, parameter)?;
    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(MappedTypeError::InvalidDeclaration(node));
    };
    if parameter_record.kind != SyntaxKind::TypeParameter
        || parameter_record.parent != Some(node.node)
    {
        return Err(MappedTypeError::InvalidDeclaration(node));
    }
    let type_parameter_symbol = bound
        .symbol(parameter)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(MappedTypeError::InvalidDeclaration(node))?;
    preflight_type_parameter_symbol(store, host, type_parameter_symbol, &mut HashSet::new())?;

    let constraint = parameter_data
        .constraint
        .map(|constraint| NodeRef::new(node.arena, node.file, constraint))
        .ok_or(MappedTypeError::InvalidDeclaration(node))?;
    let constraint_record = preflight_node(store, host, constraint)?;
    if constraint_record.parent != Some(parameter.node) {
        return Err(MappedTypeError::InvalidDeclaration(node));
    }
    let modifiers_source = match &constraint_record.data {
        NodeData::TypeOperatorNode(operator)
            if constraint_record.kind == SyntaxKind::TypeOperator
                && operator.operator == SyntaxKind::KeyOfKeyword =>
        {
            let target = NodeRef::new(node.arena, node.file, operator.type_);
            if preflight_node(store, host, target)?.parent != Some(constraint.node) {
                return Err(MappedTypeError::InvalidDeclaration(node));
            }
            Some(target)
        }
        _ => None,
    };
    let validate_child =
        |child: Option<ts_ast::NodeId>| -> Result<Option<NodeRef>, MappedTypeError> {
            let Some(child) = child else {
                return Ok(None);
            };
            let child = NodeRef::new(node.arena, node.file, child);
            if preflight_node(store, host, child)?.parent != Some(node.node) {
                return Err(MappedTypeError::InvalidDeclaration(node));
            }
            Ok(Some(child))
        };
    let readonly = validate_child(mapped.readonly_token)?;
    let optional = validate_child(mapped.question_token)?;
    let modifiers = MappedTypeModifiers::from_token_kinds(
        readonly.and_then(|token| store.source_node_kind(token)),
        optional.and_then(|token| store.source_node_kind(token)),
    )
    .ok_or(MappedTypeError::InvalidDeclaration(node))?;

    Ok(MappedTypeDeclarationPlan {
        node,
        symbol,
        type_parameter_symbol,
        constraint,
        template: validate_child(mapped.type_)?,
        name_type: validate_child(mapped.name_type)?,
        modifiers_source,
        modifiers,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceProperty {
    symbol: SemanticSymbolId,
    name: EscapedName,
    optional: bool,
    readonly: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceIndex {
    key_type: TypeId,
    value_type: TypeId,
    readonly: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MappedShape {
    type_: TypeId,
    type_parameter: TypeId,
    constraint_type: TypeId,
    template_type: TypeId,
    modifiers_type: TypeId,
    name_type: Option<TypeId>,
    source_properties: Vec<SourceProperty>,
    source_indexes: Vec<SourceIndex>,
    keyof_any_constraint: bool,
    template_parameters: Option<[TypeId; 2]>,
}

/// Created only when mapped property evaluation observes a caller limit event.
#[derive(Debug)]
pub(super) struct MappedPropertyRecovery {
    valid: bool,
    symbol: SemanticSymbolId,
    shape: MappedShape,
    key_type: TypeId,
    result: TypeId,
    links: ValueSymbolLinks,
    identity: Vec<RecoveredPropertyTypeIdentity>,
}

impl MappedPropertyRecovery {
    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) fn invalidate_for_raw_write(&mut self, symbol: SemanticSymbolId) -> bool {
        let invalidated = self.valid
            && (symbol == self.symbol
                || self
                    .shape
                    .source_properties
                    .iter()
                    .any(|source| source.symbol == symbol));
        if invalidated {
            self.valid = false;
        }
        invalidated
    }

    pub(super) fn matches_published_links(&self, links: Option<&ValueSymbolLinks>) -> bool {
        self.valid && links == Some(&self.links)
    }

    fn matches(
        &self,
        store: &CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
        shape: &MappedShape,
        key_type: TypeId,
        result: TypeId,
    ) -> bool {
        self.symbol == symbol
            && self.shape == *shape
            && self.key_type == key_type
            && self.result == result
            && self.matches_published_links(store.value_symbol_links(symbol))
            && mapped_property_recovery_identity(store, shape, key_type, result)
                .is_some_and(|identity| identity == self.identity)
    }
}

fn mapped_property_recovery_identity(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    result: TypeId,
) -> Option<Vec<RecoveredPropertyTypeIdentity>> {
    let mut roots = vec![
        shape.template_type,
        shape.type_parameter,
        shape.constraint_type,
        shape.modifiers_type,
        key_type,
        result,
    ];
    if direct_mapped_request_template(store, shape).ok()? {
        roots.extend(mapped_optional_template_sentinel(store, shape).ok()?);
    } else {
        roots.push(cached_mapped_template_input(store, shape).ok().flatten()?);
    }
    roots.extend(shape.name_type);
    roots.extend(shape.template_parameters.into_iter().flatten());
    property_recovery_type_identity(store, &roots, None)
}

/// Created only when mapped index evaluation observes a caller limit event.
#[derive(Debug)]
pub(super) struct MappedIndexRecovery {
    valid: bool,
    index: IndexInfoId,
    shape: MappedShape,
    plan: PlannedMappedIndex,
    result: TypeId,
    identity: Vec<RecoveredPropertyTypeIdentity>,
}

impl MappedIndexRecovery {
    pub(super) const fn index(&self) -> IndexInfoId {
        self.index
    }

    pub(super) fn invalidate_for_raw_write(&mut self, symbol: SemanticSymbolId) -> bool {
        let invalidated = self.valid
            && self
                .shape
                .source_properties
                .iter()
                .any(|source| source.symbol == symbol);
        if invalidated {
            self.valid = false;
        }
        invalidated
    }

    pub(super) fn invalidate_for_index_write(&mut self) -> bool {
        let invalidated = self.valid;
        self.valid = false;
        invalidated
    }

    pub(super) fn matches_published_info(&self, index: Option<&IndexInfo>) -> bool {
        self.valid
            && index.is_some_and(|index| {
                index.id() == self.index
                    && index.key_type() == self.plan.key_type
                    && index.value_type() == self.result
                    && index.is_readonly() == self.plan.readonly
                    && index.declaration().is_none()
                    && index.index_symbol().is_none()
                    && index.components().is_empty()
            })
    }

    fn matches(
        &self,
        store: &CanonicalTypeMapperStore,
        index: IndexInfoId,
        shape: &MappedShape,
        plan: &PlannedMappedIndex,
    ) -> bool {
        self.index == index
            && self.shape == *shape
            && self.plan == *plan
            && self.matches_published_info(store.index_info(index))
            && mapped_property_recovery_identity(store, shape, plan.key_type, self.result)
                .is_some_and(|identity| identity == self.identity)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RecordMappedAliasShape {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    parameter: TypeId,
    parameter_symbol: SemanticSymbolId,
    key_argument: TypeId,
    value_argument: TypeId,
    modifiers_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct HomomorphicMappedAliasShape {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    parameter: TypeId,
    parameter_symbol: SemanticSymbolId,
    source_argument: TypeId,
    template: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PickMappedAliasShape {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    parameter: TypeId,
    parameter_symbol: SemanticSymbolId,
    source_argument: TypeId,
    key_argument: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PropTypesRequiredKeysShape {
    mapped: TypeId,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    parameter: TypeId,
    parameter_symbol: SemanticSymbolId,
    source_parameter: TypeId,
    source_argument: TypeId,
    conditional: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RecursiveMappedAliasShape {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    alias: SemanticSymbolId,
    parameters: [TypeId; 2],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedMappedIndex {
    key_type: TypeId,
    value_type: PlannedMappedIndexValue,
    readonly: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PlannedMappedIndexValue {
    Resolved(TypeId),
    Template,
}

#[derive(Clone, Debug)]
struct PlannedMappedProperty {
    name: EscapedName,
    name_types: Vec<MappedTypeKey>,
    keys: Vec<MappedTypeKey>,
    origin: Option<SemanticSymbolId>,
    optional: bool,
    readonly: bool,
    strip_optional: bool,
}

/// A mapped key preserves an existing numeric or string literal identity.
/// Generated string literals remain unallocated until cold publication.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum MappedTypeKey {
    Existing(TypeId),
    String(String),
}

impl MappedTypeKey {
    fn source_string(store: &CanonicalTypeMapperStore, value: String) -> Self {
        store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| bootstrap.cached_string_literal_type(&value))
            .map_or(Self::String(value), Self::Existing)
    }

    pub(super) fn cached_type(&self, store: &CanonicalTypeMapperStore) -> Option<TypeId> {
        match self {
            Self::Existing(type_) => store.type_payload(*type_).map(|_| *type_),
            Self::String(value) => store
                .intrinsic_bootstrap()
                .and_then(|bootstrap| bootstrap.cached_string_literal_type(value)),
        }
    }

    pub(super) fn name(&self, store: &CanonicalTypeMapperStore) -> Option<String> {
        match self {
            Self::Existing(type_) => property_name_from_type(store, *type_),
            Self::String(value) => Some(value.clone()),
        }
    }

    fn escaped_name(&self, store: &CanonicalTypeMapperStore) -> Option<EscapedName> {
        match self {
            Self::Existing(type_) => escaped_property_name_from_type(store, *type_),
            Self::String(value) => Some(EscapedName::source(value.clone())),
        }
    }
}

/// The pinned fast path returns an unchanged mapped constraint. Remapping
/// instead computes property names without materializing property symbols.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MappedTypeKeys {
    Constraint(TypeId),
    Remapped(Vec<MappedTypeKey>),
}

pub(super) fn plan_mapped_type_keys(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<MappedTypeKeys, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(type_));
    };
    let constraint = mapped
        .constraint_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let parameter = mapped
        .type_parameter
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    if store.type_payload(constraint).is_none()
        || mapped_type_parameter_owner(store, type_, parameter).is_none()
    {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    let Some(name_type) = mapped.name_type else {
        return Ok(MappedTypeKeys::Constraint(constraint));
    };
    if name_type == parameter {
        return Ok(MappedTypeKeys::Constraint(constraint));
    }

    let shape = validate_mapped_shape(store, type_)?;
    let planned = plan_mapped_properties(store, &shape, MappedTypeModifiers::NONE)?;
    let mut keys = Vec::new();
    let mut seen = HashSet::new();
    for property in planned {
        for key in property.name_types {
            if seen.insert(key.clone()) {
                keys.push(key);
            }
        }
    }
    Ok(MappedTypeKeys::Remapped(keys))
}

impl CanonicalTypeMapperStore {
    /// Authenticates the concrete source object of an indexed mapped template.
    pub(super) fn source_mapped_indexed_template_is_exact(&self, type_: TypeId) -> bool {
        let Some(TypeData::IndexedAccess(indexed)) = self.type_payload(type_).map(TypeRecord::data)
        else {
            return false;
        };
        if indexed.access_flags != AccessFlags::NONE {
            return false;
        }
        let Some(owner) = cached_ordinary_type_parameter_owner(self, indexed.index_type) else {
            return false;
        };
        let Some([parameter]) = self.symbol(owner).and_then(|owner| owner.declarations()) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(declaration)) = self.source_node_parent(*parameter)
        else {
            return false;
        };
        let Some(mapped_type) = self
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        let Some(TypeData::Mapped(mapped)) = self.type_payload(mapped_type).map(TypeRecord::data)
        else {
            return false;
        };
        if mapped.type_parameter != Some(indexed.index_type)
            || mapped.template_type != Some(type_)
            || mapped.modifiers_type != Some(indexed.object_type)
            || validate_source_mapped_relation_identity(self, mapped_type, false).is_err()
        {
            return false;
        }
        let Ok(plan) = plan_nongeneric_keyof_type(self, indexed.object_type) else {
            return false;
        };
        if cached_nongeneric_keyof_type(self, &plan).ok().flatten() != mapped.constraint_type {
            return false;
        }
        !matches!(
            self.type_payload(indexed.object_type).map(TypeRecord::data),
            Some(TypeData::Mapped(_))
        ) || matches!(
            self.validate_mapped_type_relation_endpoint(indexed.object_type),
            Ok(Some(_))
        )
    }

    pub(super) fn validate_deferred_mapped_type(
        &self,
        type_: TypeId,
    ) -> Result<(), MappedTypeError> {
        let invalid = || MappedTypeError::InvalidMappedType(type_);
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Err(invalid());
        };
        let declaration = mapped.declaration.ok_or_else(invalid)?;
        let parameter = mapped.type_parameter.ok_or_else(invalid)?;
        let target = mapped.object.target.unwrap_or(type_);
        let target_record = self.type_payload(target).ok_or_else(invalid)?;
        let TypeData::Mapped(original) = target_record.data() else {
            return Err(invalid());
        };
        let original_parameter = original.type_parameter.ok_or_else(invalid)?;
        let request = MappedTypeRequest::new(
            declaration,
            target_record.symbol().ok_or_else(invalid)?,
            original_parameter,
            original.constraint_type.ok_or_else(invalid)?,
            original.template_type.ok_or_else(invalid)?,
            original.modifiers_type.ok_or_else(invalid)?,
        );
        let request = original
            .name_type
            .map_or(request, |name| request.with_name_type(name));
        validate_mapped_request(self, request)?;
        validate_request_record(self, request, target)?;
        if record.flags() != TypeFlags::OBJECT
            || !record.object_flags().contains(ObjectFlags::MAPPED)
            || original.object.target.is_some()
            || original.object.mapper.is_some()
            || mapped.declaration != original.declaration
            || record.symbol() != target_record.symbol()
            || mapped_type_parameter_owner(self, type_, parameter).is_none()
            || self.source_mapped_type_modifiers(declaration).is_none()
            || self
                .type_node_links(declaration)
                .and_then(|links| links.resolved_type)
                != Some(target)
            || [
                mapped.constraint_type,
                mapped.template_type,
                mapped.modifiers_type,
            ]
            .into_iter()
            .any(|type_| type_.is_none_or(|type_| self.type_payload(type_).is_none()))
        {
            return Err(invalid());
        }
        Ok(())
    }

    /// Publishes the mapped declaration and alias identity before its body runs.
    ///
    /// Recursive constraints can then refer to the same declaration-owned
    /// mapped type while its constraint and template are still incomplete.
    #[allow(dead_code)] // Called by the separately owned type-node integration.
    pub(super) fn begin_recursive_mapped_alias(
        &mut self,
        declaration: MappedTypeDeclarationPlan,
        alias: SemanticSymbolId,
        type_parameters: &[TypeId],
    ) -> Result<TypeId, MappedTypeError> {
        validate_recursive_mapped_declaration(self, declaration, alias, type_parameters)?;

        if let Some(existing) = self
            .type_node_links(declaration.node())
            .and_then(|links| links.resolved_type)
        {
            let shape = validate_recursive_mapped_alias_shape(self, existing)?;
            if shape.alias != alias
                || shape.declaration != declaration.node()
                || shape.symbol != declaration.symbol()
                || shape.parameters.as_slice() != type_parameters
            {
                return Err(MappedTypeError::InvalidMappedType(existing));
            }
            return Ok(existing);
        }

        if self
            .type_node_links(declaration.node())
            .is_some_and(|links| links.outer_type_parameters.is_some())
            || self.type_alias_links(alias).is_some_and(|links| {
                links.declared_type.is_some()
                    || links.type_parameters.is_some()
                    || links.instantiations.is_some()
            })
        {
            return Err(MappedTypeError::InvalidDeclaration(declaration.node()));
        }

        let mut alias_arguments = Vec::new();
        alias_arguments
            .try_reserve(type_parameters.len())
            .map_err(|_| MappedTypeError::Capacity)?;
        alias_arguments.extend_from_slice(type_parameters);

        if !self.try_reserve_types(1)
            || !self.try_reserve_type_aliases(1)
            || !self.try_reserve_type_node_links(usize::from(
                self.type_node_links(declaration.node()).is_none(),
            ))
        {
            return Err(MappedTypeError::Capacity);
        }

        let identity = self
            .alloc_type_alias(Some(alias))
            .ok_or(MappedTypeError::InvalidSymbol(alias))?;
        if !self.set_type_alias_arguments(identity, Some(alias_arguments)) {
            return Err(MappedTypeError::InvalidSymbol(alias));
        }

        let mapped = self
            .alloc_mapped_type(
                ObjectFlags::MAPPED,
                Some(declaration.symbol()),
                Some(declaration.node()),
            )
            .ok_or(MappedTypeError::Capacity)?;
        if !self.set_type_alias(mapped, Some(identity)) {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }

        let mut links = self
            .type_node_links(declaration.node())
            .cloned()
            .unwrap_or_default();
        links.resolved_type = Some(mapped);
        if !self.set_type_node_links(declaration.node(), links) {
            return Err(MappedTypeError::InvalidDeclaration(declaration.node()));
        }
        Ok(mapped)
    }

    /// Publishes the eager mapped parameter constraint onto an existing shell.
    #[allow(dead_code)] // Called by the separately owned type-node integration.
    pub(super) fn publish_recursive_mapped_constraint(
        &mut self,
        mapped: TypeId,
        type_parameter: TypeId,
        constraint_type: TypeId,
    ) -> Result<(), MappedTypeError> {
        let shape = validate_recursive_mapped_alias_shape(self, mapped)?;
        let constraint_record = self
            .type_payload(constraint_type)
            .ok_or(MappedTypeError::UnsupportedConstraint(constraint_type))?;
        let TypeData::Index(index) = constraint_record.data() else {
            return Err(MappedTypeError::UnsupportedConstraint(constraint_type));
        };
        if constraint_record.flags() != TypeFlags::INDEX
            || constraint_record.object_flags() != ObjectFlags::NONE
            || constraint_record.symbol().is_some()
            || constraint_record.alias().is_some()
            || index.target != shape.parameters[0]
            || index.index_flags != IndexFlags::NONE
        {
            return Err(MappedTypeError::UnsupportedConstraint(constraint_type));
        }

        let parameter_symbol = cached_ordinary_type_parameter_owner(self, type_parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(type_parameter))?;
        let Some([parameter_declaration]) = self
            .symbol(parameter_symbol)
            .and_then(|symbol| symbol.declarations())
        else {
            return Err(MappedTypeError::InvalidTypeParameter(type_parameter));
        };
        if self.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(shape.declaration))
        {
            return Err(MappedTypeError::InvalidTypeParameter(type_parameter));
        }

        let parameter_data = match self.type_payload(type_parameter).map(TypeRecord::data) {
            Some(TypeData::TypeParameter(parameter)) => parameter.clone(),
            _ => return Err(MappedTypeError::InvalidTypeParameter(type_parameter)),
        };
        let mapped_data = match self.type_payload(mapped).map(TypeRecord::data) {
            Some(TypeData::Mapped(mapped)) => mapped.clone(),
            _ => return Err(MappedTypeError::InvalidMappedType(mapped)),
        };
        if parameter_data.target.is_some()
            || parameter_data.mapper.is_some()
            || parameter_data.is_this_type
            || parameter_data
                .constraint
                .is_some_and(|existing| existing != constraint_type)
            || mapped_data
                .type_parameter
                .is_some_and(|existing| existing != type_parameter)
            || mapped_data
                .constraint_type
                .is_some_and(|existing| existing != constraint_type)
            || mapped_data.type_parameter.is_some() != mapped_data.constraint_type.is_some()
            || mapped_data.type_parameter.is_some() != parameter_data.constraint.is_some()
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        if mapped_data.type_parameter.is_some() {
            return Ok(());
        }

        if !self.set_type_parameter_resolution(
            type_parameter,
            Some(constraint_type),
            parameter_data.target,
            parameter_data.mapper,
            parameter_data.resolved_default_type,
        ) || !self.set_mapped_type_resolution(
            mapped,
            mapped_data.declaration,
            Some(type_parameter),
            Some(constraint_type),
            mapped_data.name_type,
            mapped_data.template_type,
            mapped_data.modifiers_type,
            mapped_data.resolved_apparent_type,
            mapped_data.contains_error,
        ) {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        Ok(())
    }

    /// Finishes an authenticated recursive mapped shell without replacing it.
    #[allow(dead_code)] // Called by the separately owned type-node integration.
    pub(super) fn finish_recursive_mapped_alias(
        &mut self,
        mapped: TypeId,
        request: MappedTypeRequest,
    ) -> Result<TypeId, MappedTypeError> {
        validate_mapped_request(self, request)?;
        let shape = validate_recursive_mapped_alias_shape(self, mapped)?;
        let data = match self.type_payload(mapped).map(TypeRecord::data) {
            Some(TypeData::Mapped(data)) => data.clone(),
            _ => return Err(MappedTypeError::InvalidMappedType(mapped)),
        };
        if shape.declaration != request.declaration
            || shape.symbol != request.symbol
            || data.type_parameter != Some(request.type_parameter)
            || data.constraint_type != Some(request.constraint_type)
            || request.modifiers_type != shape.parameters[0]
            || request.name_type.is_some()
            || data.name_type.is_some()
            || data
                .template_type
                .is_some_and(|existing| existing != request.template_type)
            || data
                .modifiers_type
                .is_some_and(|existing| existing != request.modifiers_type)
            || data.template_type.is_some() != data.modifiers_type.is_some()
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        validate_recursive_mapped_template(self, request, shape)?;

        if data.template_type.is_none()
            && !self.set_mapped_type_resolution(
                mapped,
                data.declaration,
                data.type_parameter,
                data.constraint_type,
                None,
                Some(request.template_type),
                Some(request.modifiers_type),
                data.resolved_apparent_type,
                data.contains_error,
            )
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        Ok(mapped)
    }

    /// Replays an identity alias instantiation through the mapped-object cache.
    ///
    /// Pinned alias identity seeds use a type-list key. Ordinary alias
    /// instantiations add a nil-alias discriminator, so their first identity
    /// lookup must still allocate a mapper and initialize the object cache.
    #[allow(dead_code)] // Called by the separately owned type-node integration.
    pub(super) fn instantiate_recursive_mapped_alias_identity(
        &mut self,
        alias: SemanticSymbolId,
        mapped: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        alias_instantiation_key: CacheHashKey,
    ) -> Result<TypeId, MappedTypeError> {
        let shape = validate_recursive_mapped_alias_shape(self, mapped)?;
        let expected_alias_key = recursive_mapped_instantiation_key(type_arguments, None);
        if shape.alias != alias
            || shape.parameters.as_slice() != type_parameters
            || type_arguments != type_parameters
            || alias_instantiation_key != expected_alias_key
            || alias_instantiation_key == type_list_key(type_parameters)
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }

        let mut alias_links = self
            .type_alias_links(alias)
            .cloned()
            .ok_or(MappedTypeError::InvalidSymbol(alias))?;
        let instantiations = alias_links
            .instantiations
            .as_mut()
            .ok_or(MappedTypeError::InvalidSymbol(alias))?;
        if alias_links.declared_type != Some(mapped)
            || alias_links.type_parameters.as_deref() != Some(type_parameters)
            || instantiations.get(&type_list_key(type_parameters)) != Some(&mapped)
            || instantiations
                .values()
                .any(|instantiation| self.type_payload(*instantiation).is_none())
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        if let Some(existing) = instantiations.get(&alias_instantiation_key) {
            if *existing != mapped {
                return Err(MappedTypeError::InvalidMappedType(mapped));
            }
            self.validate_recursive_mapped_alias_identity(
                alias,
                mapped,
                type_parameters,
                alias_instantiation_key,
            )?;
            return Ok(mapped);
        }

        let declaration_links = self
            .type_node_links(shape.declaration)
            .cloned()
            .ok_or(MappedTypeError::InvalidDeclaration(shape.declaration))?;
        let Some(TypeData::Mapped(mapped_data)) = self.type_payload(mapped).map(TypeRecord::data)
        else {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        };
        if declaration_links.outer_type_parameters.is_some()
            || mapped_data.object.instantiations != TypeCacheState::Unallocated
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }

        let mut mapper_sources = Vec::new();
        mapper_sources
            .try_reserve(type_parameters.len())
            .map_err(|_| MappedTypeError::Capacity)?;
        mapper_sources.extend_from_slice(type_parameters);
        let mut mapper_targets = Vec::new();
        mapper_targets
            .try_reserve(type_arguments.len())
            .map_err(|_| MappedTypeError::Capacity)?;
        mapper_targets.extend_from_slice(type_arguments);
        let mut outer_parameters = Vec::new();
        outer_parameters
            .try_reserve(type_parameters.len())
            .map_err(|_| MappedTypeError::Capacity)?;
        outer_parameters.extend_from_slice(type_parameters);
        let mut object_instantiations = HashMap::new();
        object_instantiations
            .try_reserve(1)
            .map_err(|_| MappedTypeError::Capacity)?;
        instantiations
            .try_reserve(1)
            .map_err(|_| MappedTypeError::Capacity)?;
        if !self.try_reserve_mappers(1) {
            return Err(MappedTypeError::Capacity);
        }

        let global_alias = self
            .global_symbol_id(alias)
            .ok_or(MappedTypeError::InvalidSymbol(alias))?;
        let object_key = recursive_mapped_instantiation_key(
            type_parameters,
            Some((global_alias, type_parameters)),
        );
        object_instantiations.insert(object_key, mapped);
        let substitution = self
            .new_type_mapper(mapper_sources, mapper_targets)
            .ok_or(MappedTypeError::InvalidMappedType(mapped))?;
        if self.type_mapper_has_exact_endpoints(substitution, type_parameters, type_arguments)
            != Some(true)
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }

        let mut declaration_links = declaration_links;
        declaration_links.outer_type_parameters = Some(outer_parameters);
        instantiations.insert(alias_instantiation_key, mapped);
        if !self.set_type_node_links(shape.declaration, declaration_links)
            || !self
                .set_object_instantiations(mapped, TypeCacheState::Allocated(object_instantiations))
            || !self.set_type_alias_links(alias, alias_links)
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        self.validate_recursive_mapped_alias_identity(
            alias,
            mapped,
            type_parameters,
            alias_instantiation_key,
        )?;
        Ok(mapped)
    }

    /// Checks both alias keys and the alias-aware mapped-object self cache.
    #[allow(dead_code)] // Called by the separately owned type-node integration.
    pub(super) fn validate_recursive_mapped_alias_identity(
        &self,
        alias: SemanticSymbolId,
        mapped: TypeId,
        type_parameters: &[TypeId],
        alias_instantiation_key: CacheHashKey,
    ) -> Result<(), MappedTypeError> {
        let shape = validate_recursive_mapped_alias_shape(self, mapped)?;
        let Some(global_alias) = self.symbol_store().assigned_global_symbol_id(alias) else {
            return Err(MappedTypeError::InvalidSymbol(alias));
        };
        let object_key = recursive_mapped_instantiation_key(
            type_parameters,
            Some((global_alias, type_parameters)),
        );
        let links = self
            .type_alias_links(alias)
            .ok_or(MappedTypeError::InvalidSymbol(alias))?;
        let declaration_links = self
            .type_node_links(shape.declaration)
            .ok_or(MappedTypeError::InvalidDeclaration(shape.declaration))?;
        let TypeData::Mapped(mapped_data) = self
            .type_payload(mapped)
            .ok_or(MappedTypeError::InvalidMappedType(mapped))?
            .data()
        else {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        };
        let TypeCacheState::Allocated(object_instantiations) = &mapped_data.object.instantiations
        else {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        };
        let Some(alias_instantiations) = &links.instantiations else {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        };
        if shape.alias != alias
            || shape.parameters.as_slice() != type_parameters
            || links.declared_type != Some(mapped)
            || links.type_parameters.as_deref() != Some(type_parameters)
            || alias_instantiation_key != recursive_mapped_instantiation_key(type_parameters, None)
            || alias_instantiations.get(&type_list_key(type_parameters)) != Some(&mapped)
            || alias_instantiations.get(&alias_instantiation_key) != Some(&mapped)
            || object_instantiations.get(&object_key) != Some(&mapped)
            || object_instantiations
                .values()
                .any(|instantiation| self.type_payload(*instantiation).is_none())
            || declaration_links.outer_type_parameters.as_deref() != Some(type_parameters)
        {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        Ok(())
    }

    /// Creates or validates the canonical record for one mapped declaration.
    ///
    /// The constraint is eager, as in `getTypeFromMappedTypeNode`. Property
    /// members and property value types remain unresolved.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid source identities, incompatible warm
    /// records, missing bootstrap state, or allocation failure.
    pub fn create_mapped_type(
        &mut self,
        request: MappedTypeRequest,
    ) -> Result<TypeId, MappedTypeError> {
        validate_mapped_request(self, request)?;
        if let Some(existing) = self
            .type_node_links(request.declaration)
            .and_then(|links| links.resolved_type)
        {
            validate_request_record(self, request, existing)?;
            return Ok(existing);
        }
        if !self.try_reserve_types(1)
            || !self.try_reserve_type_node_links(usize::from(
                self.type_node_links(request.declaration).is_none(),
            ))
        {
            return Err(MappedTypeError::Capacity);
        }
        let type_ = self
            .alloc_mapped_type(
                ObjectFlags::MAPPED,
                Some(request.symbol),
                Some(request.declaration),
            )
            .ok_or(MappedTypeError::Capacity)?;
        if !self.set_mapped_type_resolution(
            type_,
            Some(request.declaration),
            Some(request.type_parameter),
            Some(request.constraint_type),
            request.name_type,
            Some(request.template_type),
            Some(request.modifiers_type),
            None,
            false,
        ) {
            return Err(MappedTypeError::InvalidMappedType(type_));
        }
        let mut links = self
            .type_node_links(request.declaration)
            .cloned()
            .unwrap_or_else(TypeNodeLinks::default);
        links.resolved_type = Some(type_);
        if !self.set_type_node_links(request.declaration, links) {
            return Err(MappedTypeError::InvalidDeclaration(request.declaration));
        }
        Ok(type_)
    }

    /// Instantiates the authenticated `Record<K extends keyof any, T>` alias.
    ///
    /// The mapped record retains its original target and composite mapper.
    /// Its fresh mapped parameter points back to the declaration-owned
    /// parameter while carrying the concrete key constraint.
    ///
    /// # Errors
    ///
    /// Returns an error for an unauthenticated alias, invalid arguments,
    /// malformed mapped records, or exhausted allocation capacity.
    pub fn instantiate_record_mapped_alias(
        &mut self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
    ) -> Result<TypeId, MappedTypeError> {
        let shape = validate_record_mapped_alias_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
        )?;
        if type_arguments == type_parameters {
            return Ok(declared_type);
        }
        if !self.try_reserve_types(2) || !self.try_reserve_mappers(3) {
            return Err(MappedTypeError::Capacity);
        }

        let outer_mapper = self
            .new_type_mapper(type_parameters.to_vec(), type_arguments.to_vec())
            .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
        let parameter = self
            .alloc_type_parameter(Some(shape.parameter_symbol))
            .ok_or(MappedTypeError::Capacity)?;
        let parameter_mapper = self
            .new_simple_type_mapper(shape.parameter, parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(shape.parameter))?;
        let mapper = self
            .combine_type_mappers(Some(parameter_mapper), outer_mapper)
            .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
        if !self.set_type_parameter_resolution(
            parameter,
            Some(shape.key_argument),
            Some(shape.parameter),
            Some(mapper),
            None,
        ) {
            return Err(MappedTypeError::InvalidTypeParameter(parameter));
        }

        let instantiated = self
            .alloc_mapped_type(
                ObjectFlags::INSTANTIATED_MAPPED,
                Some(shape.symbol),
                Some(shape.declaration),
            )
            .ok_or(MappedTypeError::Capacity)?;
        if !self.set_object_target_and_mapper(instantiated, Some(declared_type), Some(mapper))
            || !self.set_mapped_type_resolution(
                instantiated,
                Some(shape.declaration),
                Some(parameter),
                Some(shape.key_argument),
                None,
                Some(shape.value_argument),
                Some(shape.modifiers_type),
                None,
                false,
            )
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        self.validate_record_mapped_alias_instantiation(
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            instantiated,
        )?;
        Ok(instantiated)
    }

    /// Validates the cloned parameter and mapper of a cached `Record`.
    ///
    /// # Errors
    ///
    /// Returns an error when the alias, arguments, mapped target, cloned
    /// parameter, or composite mapper have invalid provenance.
    pub fn validate_record_mapped_alias_instantiation(
        &self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        instantiated: TypeId,
    ) -> Result<(), MappedTypeError> {
        let shape = validate_record_mapped_alias_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
        )?;
        if type_arguments == type_parameters {
            return if instantiated == declared_type {
                Ok(())
            } else {
                Err(MappedTypeError::InvalidMappedType(instantiated))
            };
        }
        let record = self
            .type_payload(instantiated)
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let parameter = mapped
            .type_parameter
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let instantiation_mapper = mapped
            .object
            .mapper
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let Some(TypeMapperApplication::Composite { first, second }) =
            self.mapper_application(instantiation_mapper, shape.parameter)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let allowed_flags = ObjectFlags::INSTANTIATED_MAPPED
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::PROPAGATING_FLAGS;
        if record.flags() != TypeFlags::OBJECT
            || !record
                .object_flags()
                .contains(ObjectFlags::INSTANTIATED_MAPPED)
            || !(record.object_flags() & !allowed_flags).is_empty()
            || record.alias().is_some_and(|identity| {
                self.type_alias(identity).is_none_or(|identity| {
                    let Some(symbol) = identity.symbol() else {
                        return true;
                    };
                    self.get_merged_symbol(symbol) != Some(symbol)
                        || self
                            .symbol(symbol)
                            .is_none_or(|record| record.flags() != SymbolFlags::TYPE_ALIAS)
                        || identity.type_arguments().is_none_or(|arguments| {
                            arguments
                                .iter()
                                .any(|argument| self.type_payload(*argument).is_none())
                                || symbol == alias && arguments != type_arguments
                        })
                })
            })
            || record.symbol() != Some(shape.symbol)
            || mapped.declaration != Some(shape.declaration)
            || mapped.object.target != Some(declared_type)
            || mapped.object.instantiations != TypeCacheState::Unallocated
            || mapped.constraint_type != Some(shape.key_argument)
            || mapped.template_type != Some(shape.value_argument)
            || mapped.modifiers_type != Some(shape.modifiers_type)
            || mapped.name_type.is_some()
            || mapped.contains_error
            || parameter == shape.parameter
            || mapped_type_parameter_owner(self, instantiated, parameter)
                != Some(shape.parameter_symbol)
            || self.type_mapper_has_exact_endpoints(first, &[shape.parameter], &[parameter])
                != Some(true)
            || self.type_mapper_has_exact_endpoints(second, type_parameters, type_arguments)
                != Some(true)
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        if record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            let member_shape = validate_mapped_shape(self, instantiated)
                .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            let (properties, indexes) =
                plan_mapped_members(self, &member_shape, MappedTypeModifiers::NONE)
                    .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            if !matches!(
                validate_warm_mapped_members(self, &member_shape, &properties, &indexes),
                Ok(Some(_))
            ) {
                return Err(MappedTypeError::InvalidMappedType(instantiated));
            }
        } else if mapped.object.structured != StructuredTypeData::default() {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        Ok(())
    }

    /// Instantiates a mapped alias whose template reads its source by key.
    ///
    /// The concrete source supplies both the canonical `keyof` constraint and
    /// the property modifiers. Indexed values remain unresolved until their
    /// mapped property is requested.
    pub(super) fn instantiate_homomorphic_mapped_alias(
        &mut self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        modifiers: MappedTypeModifiers,
    ) -> Result<TypeId, MappedTypeError> {
        let shape = validate_homomorphic_mapped_alias_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            modifiers,
        )?;
        if type_arguments == type_parameters {
            return Ok(declared_type);
        }

        let key_plan = plan_nongeneric_keyof_type(self, shape.source_argument)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;
        cached_nongeneric_keyof_type(self, &key_plan)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;
        if !self.try_reserve_types(3) || !self.try_reserve_mappers(3) {
            return Err(MappedTypeError::Capacity);
        }
        let constraint = resolve_nongeneric_keyof_type(self, &key_plan)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;

        let outer_mapper = self
            .new_type_mapper(type_parameters.to_vec(), type_arguments.to_vec())
            .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
        let parameter = self
            .alloc_type_parameter(Some(shape.parameter_symbol))
            .ok_or(MappedTypeError::Capacity)?;
        let parameter_mapper = self
            .new_simple_type_mapper(shape.parameter, parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(shape.parameter))?;
        let mapper = self
            .combine_type_mappers(Some(parameter_mapper), outer_mapper)
            .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
        if !self.set_type_parameter_resolution(
            parameter,
            Some(constraint),
            Some(shape.parameter),
            Some(mapper),
            None,
        ) {
            return Err(MappedTypeError::InvalidTypeParameter(parameter));
        }

        let instantiated = self
            .alloc_mapped_type(
                ObjectFlags::INSTANTIATED_MAPPED,
                Some(shape.symbol),
                Some(shape.declaration),
            )
            .ok_or(MappedTypeError::Capacity)?;
        if !self.set_object_target_and_mapper(instantiated, Some(declared_type), Some(mapper))
            || !self.set_mapped_type_resolution(
                instantiated,
                Some(shape.declaration),
                Some(parameter),
                Some(constraint),
                None,
                Some(shape.template),
                Some(shape.source_argument),
                None,
                false,
            )
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }

        self.validate_homomorphic_mapped_alias_instantiation(
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            instantiated,
            modifiers,
        )?;
        Ok(instantiated)
    }

    /// Checks a homomorphic alias clone and any published mapped members.
    pub(super) fn validate_homomorphic_mapped_alias_instantiation(
        &self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        instantiated: TypeId,
        modifiers: MappedTypeModifiers,
    ) -> Result<(), MappedTypeError> {
        let shape = validate_homomorphic_mapped_alias_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            modifiers,
        )?;
        if type_arguments == type_parameters {
            return if instantiated == declared_type {
                Ok(())
            } else {
                Err(MappedTypeError::InvalidMappedType(instantiated))
            };
        }

        let key_plan = plan_nongeneric_keyof_type(self, shape.source_argument)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;
        let constraint = cached_nongeneric_keyof_type(self, &key_plan)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let record = self
            .type_payload(instantiated)
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let parameter = mapped
            .type_parameter
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let type_mapper = mapped
            .object
            .mapper
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let Some(TypeMapperApplication::Composite { first, second }) =
            self.mapper_application(type_mapper, shape.parameter)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let template = mapped
            .template_type
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let allowed_flags = ObjectFlags::INSTANTIATED_MAPPED
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::PROPAGATING_FLAGS;
        if record.flags() != TypeFlags::OBJECT
            || !record
                .object_flags()
                .contains(ObjectFlags::INSTANTIATED_MAPPED)
            || !(record.object_flags() & !allowed_flags).is_empty()
            || record.alias().is_some_and(|identity| {
                self.type_alias(identity).is_none_or(|identity| {
                    let Some(symbol) = identity.symbol() else {
                        return true;
                    };
                    self.get_merged_symbol(symbol) != Some(symbol)
                        || self
                            .symbol(symbol)
                            .is_none_or(|record| record.flags() != SymbolFlags::TYPE_ALIAS)
                        || identity.type_arguments().is_none_or(|arguments| {
                            arguments
                                .iter()
                                .any(|argument| self.type_payload(*argument).is_none())
                                || symbol == alias && arguments != type_arguments
                        })
                })
            })
            || record.symbol() != Some(shape.symbol)
            || mapped.declaration != Some(shape.declaration)
            || mapped.object.target != Some(declared_type)
            || mapped.object.instantiations != TypeCacheState::Unallocated
            || mapped.constraint_type != Some(constraint)
            || mapped.modifiers_type != Some(shape.source_argument)
            || mapped.name_type.is_some()
            || mapped.contains_error
            || parameter == shape.parameter
            || mapped_type_parameter_owner(self, instantiated, parameter)
                != Some(shape.parameter_symbol)
            || self.type_mapper_has_exact_endpoints(first, &[shape.parameter], &[parameter])
                != Some(true)
            || self.type_mapper_has_exact_endpoints(second, type_parameters, type_arguments)
                != Some(true)
            || template != shape.template
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }

        if record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            let member_shape = validate_mapped_shape(self, instantiated)
                .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            let (properties, indexes) = plan_mapped_members(self, &member_shape, modifiers)
                .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            if !matches!(
                validate_warm_mapped_members(self, &member_shape, &properties, &indexes),
                Ok(Some(_))
            ) {
                return Err(MappedTypeError::InvalidMappedType(instantiated));
            }
        } else if mapped.object.structured != StructuredTypeData::default() {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        Ok(())
    }

    /// Instantiates the authenticated `Pick<T, K extends keyof T>` alias.
    ///
    /// The explicit key argument selects properties while the original source
    /// retains declaration, readonly, and optional modifier provenance.
    pub(super) fn instantiate_pick_mapped_alias(
        &mut self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
    ) -> Result<TypeId, MappedTypeError> {
        let shape = validate_pick_mapped_alias_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
        )?;
        if type_arguments == type_parameters {
            return Ok(declared_type);
        }
        if !self.try_reserve_types(3) || !self.try_reserve_mappers(3) {
            return Err(MappedTypeError::Capacity);
        }

        let outer_mapper = self
            .new_type_mapper(type_parameters.to_vec(), type_arguments.to_vec())
            .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
        let parameter = self
            .alloc_type_parameter(Some(shape.parameter_symbol))
            .ok_or(MappedTypeError::Capacity)?;
        let parameter_mapper = self
            .new_simple_type_mapper(shape.parameter, parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(shape.parameter))?;
        let mapper = self
            .combine_type_mappers(Some(parameter_mapper), outer_mapper)
            .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
        if !self.set_type_parameter_resolution(
            parameter,
            Some(shape.key_argument),
            Some(shape.parameter),
            Some(mapper),
            None,
        ) {
            return Err(MappedTypeError::InvalidTypeParameter(parameter));
        }

        let template = self
            .alloc_indexed_access_type(shape.source_argument, parameter, AccessFlags::NONE)
            .ok_or(MappedTypeError::Capacity)?;
        let instantiated = self
            .alloc_mapped_type(
                ObjectFlags::INSTANTIATED_MAPPED,
                Some(shape.symbol),
                Some(shape.declaration),
            )
            .ok_or(MappedTypeError::Capacity)?;
        if !self.set_object_target_and_mapper(instantiated, Some(declared_type), Some(mapper))
            || !self.set_mapped_type_resolution(
                instantiated,
                Some(shape.declaration),
                Some(parameter),
                Some(shape.key_argument),
                None,
                Some(template),
                Some(shape.source_argument),
                None,
                false,
            )
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }

        self.validate_pick_mapped_alias_instantiation(
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            instantiated,
        )?;
        Ok(instantiated)
    }

    /// Validates the source, selected keys, cloned parameter, and warm members.
    pub(super) fn validate_pick_mapped_alias_instantiation(
        &self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        instantiated: TypeId,
    ) -> Result<(), MappedTypeError> {
        let shape = validate_pick_mapped_alias_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
        )?;
        if type_arguments == type_parameters {
            return if instantiated == declared_type {
                Ok(())
            } else {
                Err(MappedTypeError::InvalidMappedType(instantiated))
            };
        }
        let record = self
            .type_payload(instantiated)
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let parameter = mapped
            .type_parameter
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let instantiation_mapper = mapped
            .object
            .mapper
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let Some(TypeMapperApplication::Composite { first, second }) =
            self.mapper_application(instantiation_mapper, shape.parameter)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let Some(TypeData::IndexedAccess(template)) = mapped
            .template_type
            .and_then(|template| self.type_payload(template))
            .map(TypeRecord::data)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let allowed_flags = ObjectFlags::INSTANTIATED_MAPPED
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::PROPAGATING_FLAGS;
        if record.flags() != TypeFlags::OBJECT
            || !record
                .object_flags()
                .contains(ObjectFlags::INSTANTIATED_MAPPED)
            || !(record.object_flags() & !allowed_flags).is_empty()
            || record.alias().is_some_and(|identity| {
                self.type_alias(identity).is_none_or(|identity| {
                    let Some(symbol) = identity.symbol() else {
                        return true;
                    };
                    self.get_merged_symbol(symbol) != Some(symbol)
                        || self
                            .symbol(symbol)
                            .is_none_or(|record| record.flags() != SymbolFlags::TYPE_ALIAS)
                        || identity.type_arguments().is_none_or(|arguments| {
                            arguments
                                .iter()
                                .any(|argument| self.type_payload(*argument).is_none())
                                || symbol == alias && arguments != type_arguments
                        })
                })
            })
            || record.symbol() != Some(shape.symbol)
            || mapped.declaration != Some(shape.declaration)
            || mapped.object.target != Some(declared_type)
            || mapped.object.instantiations != TypeCacheState::Unallocated
            || mapped.constraint_type != Some(shape.key_argument)
            || mapped.modifiers_type != Some(shape.source_argument)
            || mapped.name_type.is_some()
            || mapped.contains_error
            || parameter == shape.parameter
            || mapped_type_parameter_owner(self, instantiated, parameter)
                != Some(shape.parameter_symbol)
            || self.type_mapper_has_exact_endpoints(first, &[shape.parameter], &[parameter])
                != Some(true)
            || self.type_mapper_has_exact_endpoints(second, type_parameters, type_arguments)
                != Some(true)
            || template.object_type != shape.source_argument
            || template.index_type != parameter
            || template.access_flags != AccessFlags::NONE
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        if record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            let member_shape = validate_mapped_shape(self, instantiated)
                .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            let (properties, indexes) =
                plan_mapped_members(self, &member_shape, MappedTypeModifiers::NONE)
                    .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            if !matches!(
                validate_warm_mapped_members(self, &member_shape, &properties, &indexes),
                Ok(Some(_))
            ) {
                return Err(MappedTypeError::InvalidMappedType(instantiated));
            }
        } else if mapped.object.structured != StructuredTypeData::default() {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        Ok(())
    }

    /// Rebinds the authenticated `prop-types` `RequiredKeys` mapped lookup.
    ///
    /// Both the mapped parameter and its conditional check retain their
    /// original declaration while the source and `keyof` identities follow
    /// the supplied outer argument.
    pub(super) fn instantiate_prop_types_required_keys_alias(
        &mut self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
    ) -> Result<TypeId, MappedTypeError> {
        let shape = validate_prop_types_required_keys_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
        )?;
        if type_arguments == type_parameters {
            return Ok(declared_type);
        }
        let key_plan = plan_nongeneric_keyof_type(self, shape.source_argument)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;
        cached_nongeneric_keyof_type(self, &key_plan)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;
        if !self.try_reserve_types(5) || !self.try_reserve_mappers(3) {
            return Err(MappedTypeError::Capacity);
        }
        let constraint = resolve_nongeneric_keyof_type(self, &key_plan)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;

        let outer_mapper = self
            .new_type_mapper(type_parameters.to_vec(), type_arguments.to_vec())
            .ok_or(MappedTypeError::InvalidMappedType(shape.mapped))?;
        let parameter = self
            .alloc_type_parameter(Some(shape.parameter_symbol))
            .ok_or(MappedTypeError::Capacity)?;
        let parameter_mapper = self
            .new_simple_type_mapper(shape.parameter, parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(shape.parameter))?;
        let instantiation_mapper = self
            .combine_type_mappers(Some(parameter_mapper), outer_mapper)
            .ok_or(MappedTypeError::InvalidMappedType(shape.mapped))?;
        if !self.set_type_parameter_resolution(
            parameter,
            Some(constraint),
            Some(shape.parameter),
            Some(instantiation_mapper),
            None,
        ) {
            return Err(MappedTypeError::InvalidTypeParameter(parameter));
        }

        let (root, extends_type) = match self.type_payload(shape.conditional).map(TypeRecord::data)
        {
            Some(TypeData::Conditional(conditional)) => {
                (conditional.root, conditional.extends_type)
            }
            _ => return Err(MappedTypeError::UnsupportedTemplate(shape.conditional)),
        };
        let check = self
            .alloc_indexed_access_type(shape.source_argument, parameter, AccessFlags::NONE)
            .ok_or(MappedTypeError::Capacity)?;
        let template = self
            .alloc_conditional_type(root, check, extends_type, Some(instantiation_mapper), None)
            .ok_or(MappedTypeError::InvalidMappedType(shape.mapped))?;
        let mapped = self
            .alloc_mapped_type(
                ObjectFlags::INSTANTIATED_MAPPED,
                Some(shape.symbol),
                Some(shape.declaration),
            )
            .ok_or(MappedTypeError::Capacity)?;
        if !self.set_object_target_and_mapper(
            mapped,
            Some(shape.mapped),
            Some(instantiation_mapper),
        ) || !self.set_mapped_type_resolution(
            mapped,
            Some(shape.declaration),
            Some(parameter),
            Some(constraint),
            None,
            Some(template),
            Some(shape.source_argument),
            None,
            false,
        ) {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
        let indexed = self
            .alloc_indexed_access_type(mapped, constraint, AccessFlags::NONE)
            .ok_or(MappedTypeError::Capacity)?;
        self.validate_prop_types_required_keys_instantiation(
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            indexed,
        )?;
        Ok(indexed)
    }

    /// Validates an instantiated `RequiredKeys` lookup and its conditional mapper.
    pub(super) fn validate_prop_types_required_keys_instantiation(
        &self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        instantiated: TypeId,
    ) -> Result<(), MappedTypeError> {
        let shape = validate_prop_types_required_keys_request(
            self,
            alias,
            declared_type,
            type_parameters,
            type_arguments,
        )?;
        if type_arguments == type_parameters {
            return if instantiated == declared_type {
                Ok(())
            } else {
                Err(MappedTypeError::InvalidMappedType(instantiated))
            };
        }
        let key_plan = plan_nongeneric_keyof_type(self, shape.source_argument)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?;
        let constraint = cached_nongeneric_keyof_type(self, &key_plan)
            .map_err(|error| mapped_keyof_error(shape.source_argument, error))?
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let result = self
            .type_payload(instantiated)
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let TypeData::IndexedAccess(indexed_access) = result.data() else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let mapped_record = self
            .type_payload(indexed_access.object_type)
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let TypeData::Mapped(mapped) = mapped_record.data() else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let parameter = mapped
            .type_parameter
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let instantiation_mapper = mapped
            .object
            .mapper
            .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
        let Some(TypeMapperApplication::Composite { first, second }) =
            self.mapper_application(instantiation_mapper, shape.parameter)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let Some(TypeData::Conditional(template)) = mapped
            .template_type
            .and_then(|template| self.type_payload(template))
            .map(TypeRecord::data)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let Some(TypeData::Conditional(original)) =
            self.type_payload(shape.conditional).map(TypeRecord::data)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        let Some(TypeData::IndexedAccess(check)) =
            self.type_payload(template.check_type).map(TypeRecord::data)
        else {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        };
        if result.flags() != TypeFlags::INDEXED_ACCESS
            || result.object_flags() != ObjectFlags::NONE
            || result.symbol().is_some()
            || result.alias().is_some()
            || indexed_access.index_type != constraint
            || indexed_access.access_flags != AccessFlags::NONE
            || mapped_record.flags() != TypeFlags::OBJECT
            || !mapped_record
                .object_flags()
                .contains(ObjectFlags::INSTANTIATED_MAPPED)
            || mapped_record.symbol() != Some(shape.symbol)
            || mapped_record.alias().is_some()
            || mapped.declaration != Some(shape.declaration)
            || mapped.object.target != Some(shape.mapped)
            || mapped.object.instantiations != TypeCacheState::Unallocated
            || mapped.constraint_type != Some(constraint)
            || mapped.modifiers_type != Some(shape.source_argument)
            || mapped.name_type.is_some()
            || mapped.contains_error
            || parameter == shape.parameter
            || mapped_type_parameter_owner(self, indexed_access.object_type, parameter)
                != Some(shape.parameter_symbol)
            || self.type_mapper_has_exact_endpoints(first, &[shape.parameter], &[parameter])
                != Some(true)
            || self.type_mapper_has_exact_endpoints(
                second,
                &[shape.source_parameter],
                &[shape.source_argument],
            ) != Some(true)
            || template.root != original.root
            || template.extends_type != original.extends_type
            || template.mapper != Some(instantiation_mapper)
            || template.combined_mapper.is_some()
            || check.object_type != shape.source_argument
            || check.index_type != parameter
            || check.access_flags != AccessFlags::NONE
        {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        if mapped_record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            let member_shape = validate_mapped_shape(self, indexed_access.object_type)
                .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            let (properties, indexes) =
                plan_mapped_members(self, &member_shape, MappedTypeModifiers::NONE)
                    .map_err(|_| MappedTypeError::InvalidMappedType(instantiated))?;
            if !matches!(
                validate_warm_mapped_members(self, &member_shape, &properties, &indexes),
                Ok(Some(_))
            ) {
                return Err(MappedTypeError::InvalidMappedType(instantiated));
            }
        } else if mapped.object.structured != StructuredTypeData::default() {
            return Err(MappedTypeError::InvalidMappedType(instantiated));
        }
        Ok(())
    }

    /// Publishes or validates the lazy property symbols of one mapped type.
    ///
    /// # Errors
    ///
    /// Returns an error for unsupported key domains, invalid source objects,
    /// incompatible modifiers, poisoned caches, or allocation failure.
    pub fn resolve_mapped_type_members(
        &mut self,
        type_: TypeId,
        modifiers: MappedTypeModifiers,
    ) -> Result<ResolvedMappedTypeMembers, MappedTypeError> {
        self.resolve_mapped_type_members_with_session(
            type_,
            modifiers,
            &mut InstantiationSession::new(InstantiationLimits::default()),
        )
    }

    /// Keeps lazy index values in the caller's instantiation query.
    pub(super) fn resolve_mapped_type_members_with_session(
        &mut self,
        type_: TypeId,
        modifiers: MappedTypeModifiers,
        session: &mut InstantiationSession,
    ) -> Result<ResolvedMappedTypeMembers, MappedTypeError> {
        if !modifiers.valid() {
            return Err(MappedTypeError::InvalidModifiers);
        }
        let declared = self.declared_mapped_modifiers(type_)?;
        if modifiers != MappedTypeModifiers::NONE && modifiers != declared {
            if self.type_payload(type_).is_some_and(|record| {
                record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
                    && matches!(record.data(), TypeData::Mapped(mapped)
                        if mapped.object.target.is_none() && mapped.object.mapper.is_none())
            }) {
                // Direct public requests keep their member-mismatch error. Utility
                // clones reject declared-modifier conflicts before cache checks.
                validate_mapped_member_dependencies(self, type_, &mut HashSet::new())?;
                let shape = validate_mapped_shape(self, type_)?;
                if direct_mapped_request(self, &shape)? {
                    let (properties, indexes) = plan_mapped_members(self, &shape, modifiers)?;
                    let _ = validate_warm_mapped_members(self, &shape, &properties, &indexes)?;
                }
            }
            return Err(MappedTypeError::InvalidModifiers);
        }
        let modifiers = declared;
        validate_mapped_member_dependencies(self, type_, &mut HashSet::new())?;
        if let Some(source) = mapped_member_dependency(self, type_) {
            if self.type_payload(source).is_some_and(|record| {
                !record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            }) {
                validate_unresolved_mapped_members(self, type_)?;
            }
            self.resolve_mapped_type_members_with_session(
                source,
                MappedTypeModifiers::NONE,
                session,
            )?;
        }
        let shape = validate_mapped_shape(self, type_)?;
        let (properties, indexes) = plan_mapped_members(self, &shape, modifiers)?;
        if let Some(cached) = validate_warm_mapped_members(self, &shape, &properties, &indexes)? {
            return Ok(cached);
        }
        if session.recovery_error_type().is_some_and(|error_type| {
            self.intrinsic_bootstrap()
                .is_none_or(|bootstrap| bootstrap.error_type != error_type)
                || self.validate_union_constituent(error_type).is_err()
        }) {
            return Err(MappedTypeError::InvalidMappedType(type_));
        }
        publish_mapped_members(self, &shape, properties, &indexes, session)
    }

    /// Checks source ownership and cached members before a structural relation.
    /// Cold property values stay unresolved. This query does not publish records.
    pub(super) fn validate_mapped_type_relation_endpoint(
        &self,
        type_: TypeId,
    ) -> Result<Option<ResolvedMappedTypeMembers>, MappedTypeError> {
        validate_mapped_relation_identity(self, type_)?;
        validate_mapped_member_dependencies(self, type_, &mut HashSet::new())?;
        if let Some(source) = mapped_member_dependency(self, type_)
            && self
                .validate_mapped_type_relation_endpoint(source)?
                .is_none()
        {
            validate_unresolved_mapped_members(self, type_)?;
            return Ok(None);
        }
        let shape = validate_mapped_shape(self, type_)?;
        let modifiers = self.declared_mapped_modifiers(type_)?;
        let (properties, indexes) = plan_mapped_members(self, &shape, modifiers)?;
        validate_warm_mapped_members(self, &shape, &properties, &indexes)
    }

    fn declared_mapped_modifiers(
        &self,
        type_: TypeId,
    ) -> Result<MappedTypeModifiers, MappedTypeError> {
        let Some(TypeData::Mapped(mapped)) = self.type_payload(type_).map(TypeRecord::data) else {
            return Err(MappedTypeError::InvalidMappedType(type_));
        };
        let declaration = mapped
            .declaration
            .ok_or(MappedTypeError::InvalidMappedType(type_))?;
        self.source_mapped_type_modifiers(declaration)
            .ok_or(MappedTypeError::InvalidDeclaration(declaration))
    }

    /// Validates an existing finite `Record` projection without changing caches.
    pub(super) fn finite_record_mapped_projection(
        &self,
        type_: TypeId,
    ) -> Result<FiniteRecordMappedProjection, MappedTypeError> {
        let (declaration, mapped_shape, planned) = finite_record_mapped_shape(self, type_)?;
        let members = validate_warm_mapped_members(self, &mapped_shape, &planned, &[])?
            .ok_or(MappedTypeError::InvalidCachedMembers(type_))?;
        let mut properties = Vec::with_capacity(members.properties.len());
        for symbol in members.properties {
            let (containing_type, _, cached_type) = validate_mapped_property_header(self, symbol)?;
            if containing_type != type_ || cached_type != Some(mapped_shape.template_type) {
                return Err(MappedTypeError::InvalidCachedProperty(symbol));
            }
            let property = self
                .symbol(symbol)
                .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
            properties.push(FiniteRecordMappedProperty {
                symbol,
                name: property.name().to_owned(),
                type_: mapped_shape.template_type,
                optional: property.flags().contains(SymbolFlags::OPTIONAL),
                readonly: property.check_flags().contains(CheckFlags::READONLY),
            });
        }
        Ok(FiniteRecordMappedProjection {
            type_,
            declaration,
            members: members.members,
            properties,
        })
    }

    /// Resolves finite `Record` members and their values before projection.
    pub(super) fn resolve_finite_record_mapped_projection(
        &mut self,
        type_: TypeId,
    ) -> Result<FiniteRecordMappedProjection, MappedTypeError> {
        let (_, mapped_shape, planned) = finite_record_mapped_shape(self, type_)?;
        if let Some(members) = validate_warm_mapped_members(self, &mapped_shape, &planned, &[])? {
            for symbol in members.properties() {
                let (containing_type, _, cached_type) =
                    validate_mapped_property_header(self, *symbol)?;
                if containing_type != type_
                    || cached_type.is_some_and(|cached| cached != mapped_shape.template_type)
                {
                    return Err(MappedTypeError::InvalidCachedProperty(*symbol));
                }
            }
        }

        let members = self.resolve_mapped_type_members(type_, MappedTypeModifiers::NONE)?;
        for symbol in members.properties() {
            if self.resolve_mapped_symbol_type(*symbol)? != mapped_shape.template_type {
                return Err(MappedTypeError::InvalidCachedProperty(*symbol));
            }
        }
        self.finite_record_mapped_projection(type_)
    }

    /// Resolves one mapped property and evaluates its value type on demand.
    ///
    /// # Errors
    ///
    /// Returns the member-resolution errors above, or an error for an invalid
    /// property cache, unsupported template, or circular property reference.
    pub fn resolve_mapped_type_property(
        &mut self,
        type_: TypeId,
        name: &str,
        modifiers: MappedTypeModifiers,
    ) -> Result<Option<ResolvedMappedProperty>, MappedTypeError> {
        let members = self.resolve_mapped_type_members(type_, modifiers)?;
        let Some(symbol) = self
            .symbol_table(members.members)
            .and_then(|table| table.get_source(name))
        else {
            return Ok(None);
        };
        let type_ = self.resolve_mapped_symbol_type(symbol)?;
        let record = self
            .symbol(symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
        Ok(Some(ResolvedMappedProperty {
            symbol,
            type_,
            optional: record.flags().contains(SymbolFlags::OPTIONAL),
            readonly: record.check_flags().contains(CheckFlags::READONLY),
        }))
    }

    /// Evaluates the delayed template attached to a mapped property symbol.
    ///
    /// # Errors
    ///
    /// Returns an error when its source, key, containing mapped record, cached
    /// type, or resolution-stack state is invalid.
    pub fn resolve_mapped_symbol_type(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, MappedTypeError> {
        self.resolve_mapped_symbol_type_with_session(
            symbol,
            &mut InstantiationSession::new(InstantiationLimits::default()),
        )
    }

    /// Keeps lazy mapped property demands in the caller's instantiation query.
    pub(super) fn resolve_mapped_symbol_type_with_session(
        &mut self,
        symbol: SemanticSymbolId,
        session: &mut InstantiationSession,
    ) -> Result<TypeId, MappedTypeError> {
        let (containing_type, key_type, cached) = validate_mapped_property_header(self, symbol)?;
        if let Some(cached) = cached {
            let shape = validate_mapped_shape(self, containing_type)?;
            let modifiers = self.declared_mapped_modifiers(containing_type)?;
            let (properties, indexes) = plan_mapped_members(self, &shape, modifiers)?;
            let members = validate_warm_mapped_members(self, &shape, &properties, &indexes)?
                .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
            if !members.properties.contains(&symbol) {
                return Err(MappedTypeError::InvalidCachedProperty(symbol));
            }
            return Ok(cached);
        }
        if session.recovery_error_type().is_some_and(|error_type| {
            self.intrinsic_bootstrap()
                .is_none_or(|bootstrap| bootstrap.error_type != error_type)
                || self.validate_union_constituent(error_type).is_err()
        }) {
            return Err(MappedTypeError::InvalidCachedProperty(symbol));
        }

        let pushed = self
            .push_type_resolution(
                TypeResolutionTarget::Symbol(symbol),
                TypeSystemPropertyName::Type,
            )
            .map_err(|_| MappedTypeError::InvalidCachedProperty(symbol))?;
        if !pushed {
            set_mapped_contains_error(self, containing_type)?;
            return Err(MappedTypeError::CircularProperty(symbol));
        }

        let limit_mark = session.limit_event_mark();
        let computed =
            compute_mapped_property_type(self, containing_type, symbol, key_type, session);
        let cycle_free = self
            .pop_type_resolution()
            .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
        if !cycle_free {
            set_mapped_contains_error(self, containing_type)?;
            return Err(MappedTypeError::CircularProperty(symbol));
        }
        let type_ = computed?;
        let mut links = self
            .value_symbol_links(symbol)
            .cloned()
            .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
        links.resolved_type = Some(type_);
        let recovery = if session.recovery_error_type().is_some()
            && session.limit_event_occurred_since(limit_mark)
        {
            let shape = validate_mapped_shape(self, containing_type)?;
            let identity = mapped_property_recovery_identity(self, &shape, key_type, type_)
                .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
            if !self.try_reserve_mapped_property_recoveries() {
                return Err(MappedTypeError::Capacity);
            }
            Some(MappedPropertyRecovery {
                valid: true,
                symbol,
                shape,
                key_type,
                result: type_,
                links: links.clone(),
                identity,
            })
        } else {
            None
        };
        if !self.set_value_symbol_links(symbol, links) {
            return Err(MappedTypeError::InvalidCachedProperty(symbol));
        }
        if let Some(recovery) = recovery {
            assert!(self.publish_mapped_property_recovery(recovery));
        }
        Ok(type_)
    }
}

fn finite_record_mapped_shape(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(NodeRef, MappedShape, Vec<PlannedMappedProperty>), MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(type_));
    };
    let identity = record
        .alias()
        .and_then(|identity| store.type_alias(identity))
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let owner = identity
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let owner_arguments = identity
        .type_arguments()
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let alias = if owner_record.name().as_utf8() == Some("Record") {
        owner
    } else {
        store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Record"))
            .and_then(|alias| store.get_merged_symbol(alias))
            .ok_or(MappedTypeError::InvalidMappedType(type_))?
    };
    let declared = mapped
        .object
        .target
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let declaration = mapped
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let key = mapped
        .constraint_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let value = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let parameters = store
        .type_alias_links(alias)
        .and_then(|links| links.type_parameters.as_deref())
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    store.validate_record_mapped_alias_instantiation(
        alias,
        declared,
        parameters,
        &[key, value],
        type_,
    )?;
    if owner != alias {
        let owner_links = store
            .type_alias_links(owner)
            .ok_or(MappedTypeError::InvalidMappedType(type_))?;
        if owner_links.declared_type != Some(type_)
            || owner_links.type_parameters.as_deref().unwrap_or_default() != owner_arguments
        {
            return Err(MappedTypeError::InvalidMappedType(type_));
        }
    }

    let key_record = store
        .type_payload(key)
        .ok_or(MappedTypeError::UnsupportedConstraint(key))?;
    let finite_keys = match key_record.data() {
        TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
            escaped_property_name_from_type(store, key).is_some()
        }
        TypeData::Union(union) => {
            !union.union.types.is_empty()
                && union
                    .union
                    .types
                    .iter()
                    .all(|key| escaped_property_name_from_type(store, *key).is_some())
        }
        _ => false,
    };
    if !finite_keys {
        return Err(MappedTypeError::UnsupportedConstraint(key));
    }

    let shape = validate_mapped_shape(store, type_)?;
    let (properties, indexes) = plan_mapped_members(store, &shape, MappedTypeModifiers::NONE)?;
    if properties.is_empty()
        || !indexes.is_empty()
        || properties.iter().any(|property| {
            property.origin.is_some()
                || property.optional
                || property.readonly
                || property.strip_optional
        })
    {
        return Err(MappedTypeError::UnsupportedConstraint(key));
    }
    Ok((declaration, shape, properties))
}

fn validate_homomorphic_mapped_alias_request(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declared_type: TypeId,
    type_parameters: &[TypeId],
    type_arguments: &[TypeId],
    modifiers: MappedTypeModifiers,
) -> Result<HomomorphicMappedAliasShape, MappedTypeError> {
    if !modifiers.valid() {
        return Err(MappedTypeError::InvalidModifiers);
    }
    let [source_parameter] = type_parameters else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let [source_argument] = type_arguments else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let alias_record = store
        .symbol(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    let Some([alias_declaration]) = alias_record.declarations() else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let links = store
        .type_alias_links(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    if alias_record.flags() != SymbolFlags::TYPE_ALIAS
        || store.get_merged_symbol(alias) != Some(alias)
        || store.source_node_kind(*alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || links.declared_type != Some(declared_type)
        || links.type_parameters.as_deref() != Some(type_parameters)
        || links.instantiations.as_ref().is_none_or(|instantiations| {
            instantiations.get(&type_list_key(type_parameters)) != Some(&declared_type)
                || instantiations
                    .values()
                    .any(|instantiation| store.type_payload(*instantiation).is_none())
        })
    {
        return Err(MappedTypeError::InvalidSymbol(alias));
    }

    let source_owner = cached_ordinary_type_parameter_owner(store, *source_parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(*source_parameter))?;
    let Some([source_declaration]) = store
        .symbol(source_owner)
        .and_then(|owner| owner.declarations())
    else {
        return Err(MappedTypeError::InvalidTypeParameter(*source_parameter));
    };
    if store.source_node_parent(*source_declaration)
        != Some(SourceNodeParent::Parent(*alias_declaration))
    {
        return Err(MappedTypeError::InvalidTypeParameter(*source_parameter));
    }

    let record = store
        .type_payload(declared_type)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let declaration = mapped
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let symbol = record
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter = mapped
        .type_parameter
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter_symbol = cached_ordinary_type_parameter_owner(store, parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(parameter))?;
    let constraint = mapped
        .constraint_type
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let constraint_record = store
        .type_payload(constraint)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::Index(index) = constraint_record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let template = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    if !mapped_template_source_is_exact(store, template, *source_parameter, parameter) {
        return Err(MappedTypeError::UnsupportedTemplate(template));
    }
    let Some([parameter_declaration]) = store
        .symbol(parameter_symbol)
        .and_then(|owner| owner.declarations())
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    let Some(TypeData::TypeParameter(mapped_parameter)) =
        store.type_payload(parameter).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };

    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::MAPPED)
        || record.object_flags().contains(ObjectFlags::INSTANTIATED)
        || record.alias().is_some()
        || store.source_node_kind(declaration) != Some(SyntaxKind::MappedType)
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        || store
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
            != Some(declared_type)
        || mapped.object.target.is_some()
        || mapped.object.mapper.is_some()
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.modifiers_type != Some(*source_parameter)
        || mapped.name_type.is_some()
        || mapped.contains_error
        || constraint_record.flags() != TypeFlags::INDEX
        || constraint_record.object_flags() != ObjectFlags::NONE
        || constraint_record.symbol().is_some()
        || constraint_record.alias().is_some()
        || index.target != *source_parameter
        || index.index_flags != IndexFlags::NONE
        || store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(declaration))
        || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::TypeParameter)
        || mapped_parameter.constraint != Some(constraint)
        || store.symbol(symbol).is_none_or(|owner| {
            owner.flags() != SymbolFlags::TYPE_LITERAL
                || !owner
                    .declarations()
                    .is_some_and(|declarations| declarations.contains(&declaration))
        })
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    }

    if source_argument != source_parameter {
        validate_mapped_utility_source(store, *source_argument)?;
    }

    Ok(HomomorphicMappedAliasShape {
        declaration,
        symbol,
        parameter,
        parameter_symbol,
        source_argument: *source_argument,
        template,
    })
}

fn mapped_template_source_is_exact(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    source: TypeId,
    key: TypeId,
) -> bool {
    if store
        .intrinsic_bootstrap()
        .is_some_and(|bootstrap| template == bootstrap.void_type)
    {
        let Some(owner) = cached_ordinary_type_parameter_owner(store, key) else {
            return false;
        };
        let Some([parameter]) = store.symbol(owner).and_then(|owner| owner.declarations()) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(declaration)) = store.source_node_parent(*parameter)
        else {
            return false;
        };
        let Some(operands) = store.source_mapped_type_operands(declaration) else {
            return false;
        };
        let Some(template_node) = operands.template else {
            return false;
        };
        let Some(mapped_type) = store
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        let Some(TypeData::Mapped(mapped)) = store.type_payload(mapped_type).map(TypeRecord::data)
        else {
            return false;
        };
        return store.validate_union_constituent(template).is_ok()
            && operands.type_parameter == *parameter
            && store.source_node_kind(template_node) == Some(SyntaxKind::VoidKeyword)
            && mapped.template_type == Some(template)
            && mapped.type_parameter == Some(key)
            && mapped.modifiers_type == Some(source)
            && validate_source_mapped_relation_identity(store, mapped_type, false).is_ok();
    }
    let mut current = template;
    let mut seen = HashSet::new();
    while seen.insert(current) {
        let Some(record) = store.type_payload(current) else {
            return false;
        };
        match record.data() {
            TypeData::IndexedAccess(indexed) => {
                return record.flags() == TypeFlags::INDEXED_ACCESS
                    && record.object_flags() == ObjectFlags::NONE
                    && record.symbol().is_none()
                    && record.alias().is_none()
                    && indexed.object_type == source
                    && indexed.index_type == key
                    && indexed.access_flags == AccessFlags::NONE;
            }
            TypeData::TypeReference(_) => {
                let Ok(reference) =
                    super::reference_types::validate_direct_generic_reference(store, current)
                else {
                    return false;
                };
                let [argument] = reference.type_arguments.as_slice() else {
                    return false;
                };
                current = *argument;
            }
            _ => return false,
        }
    }
    false
}

fn validate_mapped_utility_source(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
) -> Result<(), MappedTypeError> {
    let record = store
        .type_payload(source)
        .ok_or(MappedTypeError::InvalidSource(source))?;
    match record.data() {
        TypeData::Intrinsic(_)
            if record
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN) =>
        {
            Ok(())
        }
        TypeData::TypeParameter(_)
            if cached_ordinary_type_parameter_owner(store, source).is_some() =>
        {
            Ok(())
        }
        TypeData::Mapped(_) if plan_mapped_type_keys(store, source).is_ok() => Ok(()),
        _ if record.flags() == TypeFlags::OBJECT
            && record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED) =>
        {
            source_properties(store, source)?;
            source_indexes(store, source)?;
            Ok(())
        }
        _ => Err(MappedTypeError::UnsupportedSource(source)),
    }
}

#[allow(clippy::too_many_lines)] // The mapped lookup and nested conditional form one ownership proof.
fn validate_prop_types_required_keys_request(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declared_type: TypeId,
    type_parameters: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<PropTypesRequiredKeysShape, MappedTypeError> {
    let [source_parameter] = type_parameters else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let [source_argument] = type_arguments else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let owner = store
        .symbol(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    let Some([alias_declaration]) = owner.declarations() else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let Some(module) = store.get_parent_of_symbol(alias) else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let links = store
        .type_alias_links(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    if owner.flags() != SymbolFlags::TYPE_ALIAS
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("RequiredKeys")
        || store.get_merged_symbol(alias) != Some(alias)
        || store
            .symbol(module)
            .is_none_or(|module| !module.flags().intersects(SymbolFlags::MODULE))
        || links.declared_type != Some(declared_type)
        || links.type_parameters.as_deref() != Some(type_parameters)
        || links.instantiations.as_ref().is_none_or(|instantiations| {
            instantiations.get(&type_list_key(type_parameters)) != Some(&declared_type)
                || instantiations
                    .values()
                    .any(|instantiation| store.type_payload(*instantiation).is_none())
        })
    {
        return Err(MappedTypeError::InvalidSymbol(alias));
    }
    let parameter_owner = cached_ordinary_type_parameter_owner(store, *source_parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(*source_parameter))?;
    let Some([source_declaration]) = store
        .symbol(parameter_owner)
        .and_then(|parameter| parameter.declarations())
    else {
        return Err(MappedTypeError::InvalidTypeParameter(*source_parameter));
    };
    if store.source_node_parent(*source_declaration)
        != Some(SourceNodeParent::Parent(*alias_declaration))
    {
        return Err(MappedTypeError::InvalidTypeParameter(*source_parameter));
    }

    let record = store
        .type_payload(declared_type)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::IndexedAccess(indexed) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let key_record = store
        .type_payload(indexed.index_type)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::Index(keys) = key_record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let mapped_record = store
        .type_payload(indexed.object_type)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::Mapped(mapped) = mapped_record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let declaration = mapped
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let symbol = mapped_record
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter = mapped
        .type_parameter
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter_symbol = cached_ordinary_type_parameter_owner(store, parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(parameter))?;
    let Some([parameter_declaration]) = store
        .symbol(parameter_symbol)
        .and_then(|parameter| parameter.declarations())
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    let Some(TypeData::TypeParameter(mapped_parameter)) =
        store.type_payload(parameter).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    let conditional = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let Some(TypeData::Conditional(template)) =
        store.type_payload(conditional).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::UnsupportedTemplate(conditional));
    };
    let Some(TypeData::IndexedAccess(check)) = store
        .type_payload(template.check_type)
        .map(TypeRecord::data)
    else {
        return Err(MappedTypeError::UnsupportedTemplate(conditional));
    };
    if record.flags() != TypeFlags::INDEXED_ACCESS
        || record.object_flags() != ObjectFlags::NONE
        || record.symbol().is_some()
        || record.alias().is_some()
        || indexed.access_flags != AccessFlags::NONE
        || key_record.flags() != TypeFlags::INDEX
        || key_record.object_flags() != ObjectFlags::NONE
        || key_record.symbol().is_some()
        || key_record.alias().is_some()
        || keys.target != *source_parameter
        || keys.index_flags != IndexFlags::NONE
        || mapped_record.flags() != TypeFlags::OBJECT
        || !mapped_record.object_flags().contains(ObjectFlags::MAPPED)
        || mapped_record
            .object_flags()
            .contains(ObjectFlags::INSTANTIATED)
        || mapped_record.alias().is_some()
        || mapped.object.target.is_some()
        || mapped.object.mapper.is_some()
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.constraint_type != Some(indexed.index_type)
        || mapped.modifiers_type != Some(*source_parameter)
        || mapped.name_type.is_some()
        || mapped.contains_error
        || store.source_node_kind(declaration) != Some(SyntaxKind::MappedType)
        || store
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
            != Some(indexed.object_type)
        || store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(declaration))
        || mapped_parameter.constraint != Some(indexed.index_type)
        || template.mapper.is_some()
        || template.combined_mapper.is_some()
        || check.object_type != *source_parameter
        || check.index_type != parameter
        || check.access_flags != AccessFlags::NONE
        || store
            .conditional_root(template.root)
            .is_none_or(|root| root.check_type() != template.check_type)
        || store
            .symbol(symbol)
            .is_none_or(|owner| owner.flags() != SymbolFlags::TYPE_LITERAL)
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    }
    if source_argument != source_parameter {
        validate_mapped_utility_source(store, *source_argument)?;
    }

    Ok(PropTypesRequiredKeysShape {
        mapped: indexed.object_type,
        declaration,
        symbol,
        parameter,
        parameter_symbol,
        source_parameter: *source_parameter,
        source_argument: *source_argument,
        conditional,
    })
}

fn validate_pick_mapped_alias_request(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declared_type: TypeId,
    type_parameters: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<PickMappedAliasShape, MappedTypeError> {
    let [source_parameter, key_parameter] = type_parameters else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let [source_argument, key_argument] = type_arguments else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let alias_record = store
        .symbol(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    let Some([alias_declaration]) = alias_record.declarations() else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let links = store
        .type_alias_links(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    if alias_record.flags() != SymbolFlags::TYPE_ALIAS
        || store.get_merged_symbol(alias) != Some(alias)
        || store.source_node_kind(*alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || links.declared_type != Some(declared_type)
        || links.type_parameters.as_deref() != Some(type_parameters)
        || links.instantiations.as_ref().is_none_or(|instantiations| {
            instantiations.get(&type_list_key(type_parameters)) != Some(&declared_type)
                || instantiations
                    .values()
                    .any(|instantiation| store.type_payload(*instantiation).is_none())
        })
        || source_parameter == key_parameter
        || store.type_payload(*key_argument).is_none()
    {
        return Err(MappedTypeError::InvalidSymbol(alias));
    }
    for parameter in type_parameters {
        let owner = cached_ordinary_type_parameter_owner(store, *parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(*parameter))?;
        let Some([declaration]) = store.symbol(owner).and_then(|owner| owner.declarations()) else {
            return Err(MappedTypeError::InvalidTypeParameter(*parameter));
        };
        if store.source_node_parent(*declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        {
            return Err(MappedTypeError::InvalidTypeParameter(*parameter));
        }
    }
    let TypeData::TypeParameter(key_data) = store
        .type_payload(*key_parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(*key_parameter))?
        .data()
    else {
        return Err(MappedTypeError::InvalidTypeParameter(*key_parameter));
    };
    let key_constraint = key_data
        .constraint
        .ok_or(MappedTypeError::InvalidTypeParameter(*key_parameter))?;
    let Some(TypeData::Index(index)) = store.type_payload(key_constraint).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidTypeParameter(*key_parameter));
    };
    if index.target != *source_parameter || index.index_flags != IndexFlags::NONE {
        return Err(MappedTypeError::InvalidTypeParameter(*key_parameter));
    }

    let record = store
        .type_payload(declared_type)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let declaration = mapped
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let symbol = record
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter = mapped
        .type_parameter
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter_symbol = cached_ordinary_type_parameter_owner(store, parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(parameter))?;
    let template = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let template_record = store
        .type_payload(template)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::IndexedAccess(indexed) = template_record.data() else {
        return Err(MappedTypeError::UnsupportedTemplate(template));
    };
    let Some([parameter_declaration]) = store
        .symbol(parameter_symbol)
        .and_then(|owner| owner.declarations())
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    let Some(TypeData::TypeParameter(mapped_parameter)) =
        store.type_payload(parameter).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::MAPPED)
        || record.object_flags().contains(ObjectFlags::INSTANTIATED)
        || record.alias().is_some()
        || store.source_node_kind(declaration) != Some(SyntaxKind::MappedType)
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        || store
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
            != Some(declared_type)
        || mapped.object.target.is_some()
        || mapped.object.mapper.is_some()
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.constraint_type != Some(*key_parameter)
        || mapped.modifiers_type != Some(*source_parameter)
        || mapped.name_type.is_some()
        || mapped.contains_error
        || template_record.flags() != TypeFlags::INDEXED_ACCESS
        || template_record.object_flags() != ObjectFlags::NONE
        || template_record.symbol().is_some()
        || template_record.alias().is_some()
        || indexed.object_type != *source_parameter
        || indexed.index_type != parameter
        || indexed.access_flags != AccessFlags::NONE
        || store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(declaration))
        || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::TypeParameter)
        || mapped_parameter.constraint != Some(*key_parameter)
        || store.symbol(symbol).is_none_or(|owner| {
            owner.flags() != SymbolFlags::TYPE_LITERAL
                || !owner
                    .declarations()
                    .is_some_and(|declarations| declarations.contains(&declaration))
        })
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    }
    if source_argument != source_parameter {
        validate_mapped_utility_source(store, *source_argument)?;
    }

    Ok(PickMappedAliasShape {
        declaration,
        symbol,
        parameter,
        parameter_symbol,
        source_argument: *source_argument,
        key_argument: *key_argument,
    })
}

fn validate_record_mapped_alias_request(
    store: &CanonicalTypeMapperStore,
    alias: SemanticSymbolId,
    declared_type: TypeId,
    type_parameters: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<RecordMappedAliasShape, MappedTypeError> {
    let [key_parameter, value_parameter] = type_parameters else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let [key_argument, value_argument] = type_arguments else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let alias_record = store
        .symbol(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    let Some([alias_declaration]) = alias_record.declarations() else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    let links = store
        .type_alias_links(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    if alias_record.flags() != SymbolFlags::TYPE_ALIAS
        || alias_record.name().as_utf8() != Some("Record")
        || store.get_merged_symbol(alias) != Some(alias)
        || store.source_node_kind(*alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || links.declared_type != Some(declared_type)
        || links.type_parameters.as_deref() != Some(type_parameters)
        || links.instantiations.as_ref().is_none_or(|instantiations| {
            instantiations.get(&type_list_key(type_parameters)) != Some(&declared_type)
                || instantiations
                    .values()
                    .any(|instantiation| store.type_payload(*instantiation).is_none())
        })
        || key_parameter == value_parameter
    {
        return Err(MappedTypeError::InvalidSymbol(alias));
    }
    for parameter in type_parameters {
        let owner = cached_ordinary_type_parameter_owner(store, *parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(*parameter))?;
        let Some([declaration]) = store.symbol(owner).and_then(|owner| owner.declarations()) else {
            return Err(MappedTypeError::InvalidTypeParameter(*parameter));
        };
        if store.source_node_parent(*declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        {
            return Err(MappedTypeError::InvalidTypeParameter(*parameter));
        }
    }

    let property_keys = store
        .canonical_property_key_type()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    let TypeData::TypeParameter(key_record) = store
        .type_payload(*key_parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(*key_parameter))?
        .data()
    else {
        return Err(MappedTypeError::InvalidTypeParameter(*key_parameter));
    };
    if key_record.constraint != Some(property_keys) {
        return Err(MappedTypeError::InvalidTypeParameter(*key_parameter));
    }
    if !store.is_valid_property_key_type(*key_argument) {
        return Err(MappedTypeError::UnsupportedConstraint(*key_argument));
    }
    if store.type_payload(*value_argument).is_none() {
        return Err(MappedTypeError::UnsupportedTemplate(*value_argument));
    }

    let record = store
        .type_payload(declared_type)
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    };
    let declaration = mapped
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let symbol = record
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter = mapped
        .type_parameter
        .ok_or(MappedTypeError::InvalidMappedType(declared_type))?;
    let parameter_symbol = cached_ordinary_type_parameter_owner(store, parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(parameter))?;
    let unknown = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?
        .unknown_type;
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::MAPPED)
        || record.object_flags().contains(ObjectFlags::INSTANTIATED)
        || record.alias().is_some()
        || store.source_node_kind(declaration) != Some(SyntaxKind::MappedType)
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        || store
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
            != Some(declared_type)
        || mapped.object.target.is_some()
        || mapped.object.mapper.is_some()
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.constraint_type != Some(*key_parameter)
        || mapped.template_type != Some(*value_parameter)
        || mapped.modifiers_type != Some(unknown)
        || mapped.name_type.is_some()
        || mapped.contains_error
        || store.symbol(symbol).is_none_or(|owner| {
            owner.flags() != SymbolFlags::TYPE_LITERAL
                || !owner
                    .declarations()
                    .is_some_and(|declarations| declarations.contains(&declaration))
        })
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(MappedTypeError::InvalidMappedType(declared_type));
    }
    let Some([parameter_declaration]) = store
        .symbol(parameter_symbol)
        .and_then(|owner| owner.declarations())
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    let Some(TypeData::TypeParameter(mapped_parameter)) =
        store.type_payload(parameter).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    };
    if store.source_node_parent(*parameter_declaration)
        != Some(SourceNodeParent::Parent(declaration))
        || store.source_node_kind(*parameter_declaration) != Some(SyntaxKind::TypeParameter)
        || mapped_parameter.constraint != Some(*key_parameter)
    {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    }

    Ok(RecordMappedAliasShape {
        declaration,
        symbol,
        parameter,
        parameter_symbol,
        key_argument: *key_argument,
        value_argument: *value_argument,
        modifiers_type: unknown,
    })
}

fn validate_unresolved_mapped_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    if record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
        || record.data().structured() != Some(&StructuredTypeData::default())
    {
        return Err(MappedTypeError::InvalidCachedMembers(type_));
    }
    Ok(())
}

fn mapped_member_dependency(store: &CanonicalTypeMapperStore, type_: TypeId) -> Option<TypeId> {
    let TypeData::Mapped(mapped) = store.type_payload(type_)?.data() else {
        return None;
    };
    mapped.modifiers_type.filter(|source| {
        matches!(
            store.type_payload(*source).map(TypeRecord::data),
            Some(TypeData::Mapped(_))
        )
    })
}

fn validate_mapped_member_dependencies(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    active: &mut HashSet<TypeId>,
) -> Result<(), MappedTypeError> {
    if !active.insert(type_) {
        return Err(MappedTypeError::RecursiveMembers(type_));
    }
    let result = (|| {
        let record = store
            .type_payload(type_)
            .ok_or(MappedTypeError::InvalidMappedType(type_))?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Err(MappedTypeError::InvalidMappedType(type_));
        };
        if let Some(source) = mapped.modifiers_type
            && matches!(
                store.type_payload(source).map(TypeRecord::data),
                Some(TypeData::Mapped(_))
            )
        {
            validate_mapped_member_dependencies(store, source, active)?;
        }
        Ok(())
    })();
    active.remove(&type_);
    result
}

fn validate_recursive_mapped_declaration(
    store: &CanonicalTypeMapperStore,
    declaration: MappedTypeDeclarationPlan,
    alias: SemanticSymbolId,
    type_parameters: &[TypeId],
) -> Result<(), MappedTypeError> {
    if store.intrinsic_bootstrap().is_none() {
        return Err(MappedTypeError::BootstrapUninitialized);
    }
    let [first_parameter, second_parameter] = type_parameters else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    if first_parameter == second_parameter
        || declaration.name_type().is_some()
        || declaration.template().is_none()
        || declaration.modifiers_source().is_none()
        || declaration.modifiers() != MappedTypeModifiers::NONE
        || store.source_node_kind(declaration.node()) != Some(SyntaxKind::MappedType)
    {
        return Err(MappedTypeError::InvalidDeclaration(declaration.node()));
    }

    let alias_record = store
        .symbol(alias)
        .ok_or(MappedTypeError::InvalidSymbol(alias))?;
    let Some([alias_declaration]) = alias_record.declarations() else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    if alias_record.flags() != SymbolFlags::TYPE_ALIAS
        || store.get_merged_symbol(alias) != Some(alias)
        || store.source_node_kind(*alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || store.source_node_parent(declaration.node())
            != Some(SourceNodeParent::Parent(*alias_declaration))
    {
        return Err(MappedTypeError::InvalidSymbol(alias));
    }

    let mapped_record = store
        .symbol(declaration.symbol())
        .ok_or(MappedTypeError::InvalidSymbol(declaration.symbol()))?;
    if mapped_record.flags() != SymbolFlags::TYPE_LITERAL
        || store.get_merged_symbol(declaration.symbol()) != Some(declaration.symbol())
        || !mapped_record
            .declarations()
            .is_some_and(|declarations| declarations.contains(&declaration.node()))
    {
        return Err(MappedTypeError::InvalidSymbol(declaration.symbol()));
    }

    for parameter in type_parameters {
        let parameter_symbol = cached_ordinary_type_parameter_owner(store, *parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(*parameter))?;
        let Some([parameter_declaration]) = store
            .symbol(parameter_symbol)
            .and_then(|symbol| symbol.declarations())
        else {
            return Err(MappedTypeError::InvalidTypeParameter(*parameter));
        };
        if store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        {
            return Err(MappedTypeError::InvalidTypeParameter(*parameter));
        }
    }

    let mapped_parameter = store
        .symbol(declaration.type_parameter_symbol())
        .ok_or(MappedTypeError::InvalidDeclaration(declaration.node()))?;
    let Some([mapped_parameter_declaration]) = mapped_parameter.declarations() else {
        return Err(MappedTypeError::InvalidDeclaration(declaration.node()));
    };
    if mapped_parameter.flags() != SymbolFlags::TYPE_PARAMETER
        || store.source_node_parent(*mapped_parameter_declaration)
            != Some(SourceNodeParent::Parent(declaration.node()))
    {
        return Err(MappedTypeError::InvalidDeclaration(declaration.node()));
    }
    Ok(())
}

fn validate_recursive_mapped_alias_shape(
    store: &CanonicalTypeMapperStore,
    mapped: TypeId,
) -> Result<RecursiveMappedAliasShape, MappedTypeError> {
    let record = store
        .type_payload(mapped)
        .ok_or(MappedTypeError::InvalidMappedType(mapped))?;
    let TypeData::Mapped(data) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    };
    let declaration = data
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(mapped))?;
    let symbol = record
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(mapped))?;
    let identity = record
        .alias()
        .and_then(|identity| store.type_alias(identity))
        .ok_or(MappedTypeError::InvalidMappedType(mapped))?;
    let alias = identity
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(mapped))?;
    let Some([first_parameter, second_parameter]) = identity.type_arguments() else {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    };
    let parameters = [*first_parameter, *second_parameter];
    if parameters[0] == parameters[1]
        || record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::MAPPED)
        || record.object_flags().contains(ObjectFlags::INSTANTIATED)
        || data.object.target.is_some()
        || data.object.mapper.is_some()
        || data.name_type.is_some()
        || data.contains_error
        || data.type_parameter.is_some() != data.constraint_type.is_some()
        || data.template_type.is_some() != data.modifiers_type.is_some()
        || store
            .type_node_links(declaration)
            .and_then(|links| links.resolved_type)
            != Some(mapped)
        || store.source_node_kind(declaration) != Some(SyntaxKind::MappedType)
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    }

    let Some([alias_declaration]) = store
        .symbol(alias)
        .filter(|record| record.flags() == SymbolFlags::TYPE_ALIAS)
        .and_then(|record| record.declarations())
    else {
        return Err(MappedTypeError::InvalidSymbol(alias));
    };
    if store.get_merged_symbol(alias) != Some(alias)
        || store.source_node_parent(declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        || store
            .symbol(symbol)
            .filter(|record| record.flags() == SymbolFlags::TYPE_LITERAL)
            .and_then(|record| record.declarations())
            .is_none_or(|declarations| !declarations.contains(&declaration))
    {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    }

    for parameter in parameters {
        let parameter_symbol = cached_ordinary_type_parameter_owner(store, parameter)
            .ok_or(MappedTypeError::InvalidTypeParameter(parameter))?;
        let Some([parameter_declaration]) = store
            .symbol(parameter_symbol)
            .and_then(|record| record.declarations())
        else {
            return Err(MappedTypeError::InvalidTypeParameter(parameter));
        };
        if store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(*alias_declaration))
        {
            return Err(MappedTypeError::InvalidTypeParameter(parameter));
        }
    }

    if let Some(links) = store.type_alias_links(alias) {
        if let Some(declared) = links.declared_type {
            if declared != mapped
                || links.type_parameters.as_deref() != Some(parameters.as_slice())
                || links
                    .instantiations
                    .as_ref()
                    .and_then(|instantiations| instantiations.get(&type_list_key(&parameters)))
                    != Some(&mapped)
            {
                return Err(MappedTypeError::InvalidMappedType(mapped));
            }
        } else if links.type_parameters.is_some() || links.instantiations.is_some() {
            return Err(MappedTypeError::InvalidMappedType(mapped));
        }
    }

    if store
        .type_node_links(declaration)
        .and_then(|links| links.outer_type_parameters.as_deref())
        .is_some_and(|outer| outer != parameters)
    {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    }

    Ok(RecursiveMappedAliasShape {
        declaration,
        symbol,
        alias,
        parameters,
    })
}

fn validate_recursive_mapped_template(
    store: &CanonicalTypeMapperStore,
    request: MappedTypeRequest,
    shape: RecursiveMappedAliasShape,
) -> Result<(), MappedTypeError> {
    let boolean = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?
        .boolean_type;
    let Some(TypeData::Conditional(conditional)) = store
        .type_payload(request.template_type)
        .map(TypeRecord::data)
    else {
        return Err(MappedTypeError::UnsupportedTemplate(request.template_type));
    };
    let root = store
        .conditional_root(conditional.root)
        .ok_or(MappedTypeError::UnsupportedTemplate(request.template_type))?;
    let Some(TypeData::IndexedAccess(indexed)) = store
        .type_payload(conditional.check_type)
        .map(TypeRecord::data)
    else {
        return Err(MappedTypeError::UnsupportedTemplate(request.template_type));
    };
    if conditional.extends_type != boolean
        || root.check_type() != conditional.check_type
        || root.extends_type() != boolean
        || root
            .outer_type_parameters()
            .is_some_and(|parameters| parameters != [shape.parameters[1], request.type_parameter])
        || indexed.object_type != shape.parameters[1]
        || indexed.index_type != request.type_parameter
        || indexed.access_flags != AccessFlags::NONE
    {
        return Err(MappedTypeError::UnsupportedTemplate(request.template_type));
    }
    Ok(())
}

fn recursive_mapped_instantiation_key(
    type_arguments: &[TypeId],
    alias: Option<(u64, &[TypeId])>,
) -> CacheHashKey {
    fn write_type_list(hasher: &mut Xxh3, types: &[TypeId]) {
        hasher.update(
            &u64::try_from(types.len())
                .expect("type-list length must fit the pinned uint64 encoding")
                .to_le_bytes(),
        );
        for type_ in types {
            hasher.update(&type_.get().to_le_bytes());
        }
    }

    let mut hasher = Xxh3::new();
    write_type_list(&mut hasher, type_arguments);
    if let Some((symbol, arguments)) = alias {
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        write_type_list(&mut hasher, arguments);
    } else {
        hasher.update(&[0]);
    }
    CacheHashKey::new(hasher.digest128())
}

fn validate_mapped_request(
    store: &CanonicalTypeMapperStore,
    request: MappedTypeRequest,
) -> Result<(), MappedTypeError> {
    if store.intrinsic_bootstrap().is_none() {
        return Err(MappedTypeError::BootstrapUninitialized);
    }
    if store.source_node_kind(request.declaration) != Some(SyntaxKind::MappedType) {
        return Err(MappedTypeError::InvalidDeclaration(request.declaration));
    }
    let owner = store
        .symbol(request.symbol)
        .ok_or(MappedTypeError::InvalidSymbol(request.symbol))?;
    if owner.flags() != SymbolFlags::TYPE_LITERAL
        || !owner
            .declarations()
            .is_some_and(|declarations| declarations.contains(&request.declaration))
    {
        return Err(MappedTypeError::InvalidSymbol(request.symbol));
    }
    let parameter_owner = cached_ordinary_type_parameter_owner(store, request.type_parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(
            request.type_parameter,
        ))?;
    let parameter_declaration = store
        .symbol(parameter_owner)
        .and_then(|symbol| symbol.declarations())
        .and_then(|declarations| declarations.first().copied())
        .ok_or(MappedTypeError::InvalidTypeParameter(
            request.type_parameter,
        ))?;
    if store.source_node_parent(parameter_declaration)
        != Some(SourceNodeParent::Parent(request.declaration))
    {
        return Err(MappedTypeError::InvalidTypeParameter(
            request.type_parameter,
        ));
    }
    for type_ in [
        request.constraint_type,
        request.template_type,
        request.modifiers_type,
    ]
    .into_iter()
    .chain(request.name_type)
    {
        if store.type_payload(type_).is_none() {
            return Err(MappedTypeError::InvalidMappedType(type_));
        }
    }
    Ok(())
}

fn validate_request_record(
    store: &CanonicalTypeMapperStore,
    request: MappedTypeRequest,
    type_: TypeId,
) -> Result<(), MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(type_));
    };
    if record.symbol() != Some(request.symbol)
        || mapped.declaration != Some(request.declaration)
        || mapped.type_parameter != Some(request.type_parameter)
        || mapped.constraint_type != Some(request.constraint_type)
        || mapped.name_type != request.name_type
        || mapped.template_type != Some(request.template_type)
        || mapped.modifiers_type != Some(request.modifiers_type)
    {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    Ok(())
}

fn validate_mapped_shape(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<MappedShape, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(type_));
    };
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::MAPPED)
        || mapped.declaration.is_none_or(|declaration| {
            store.source_node_kind(declaration) != Some(SyntaxKind::MappedType)
        })
    {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    let type_parameter = mapped
        .type_parameter
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let parameter_owner = mapped_type_parameter_owner(store, type_, type_parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(type_parameter))?;
    let constraint_type = mapped
        .constraint_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let template_type = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let modifiers_type = mapped
        .modifiers_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let template_parameters = mapped.object.target.and_then(|target| {
        let TypeData::Mapped(original) = store.type_payload(target)?.data() else {
            return None;
        };
        let TypeData::Index(constraint) = store.type_payload(original.constraint_type?)?.data()
        else {
            return None;
        };
        (original.template_type == Some(template_type)
            && original.modifiers_type == Some(constraint.target))
        .then_some([constraint.target, original.type_parameter?])
    });
    let source_properties = source_properties(store, modifiers_type)?;
    let source_indexes = source_indexes(store, modifiers_type)?;
    let keyof_any_constraint = store
        .type_payload(modifiers_type)
        .is_some_and(|source| source.flags().contains(TypeFlags::ANY))
        && mapped
            .declaration
            .and_then(|declaration| store.source_mapped_type_operands(declaration))
            .is_some_and(|operands| {
                store
                    .symbol(parameter_owner)
                    .and_then(|owner| owner.declarations())
                    == Some(&[operands.type_parameter][..])
                    && store.source_type_operator(operands.constraint)
                        == Some(SyntaxKind::KeyOfKeyword)
            });
    Ok(MappedShape {
        type_,
        type_parameter,
        constraint_type,
        template_type,
        modifiers_type,
        name_type: mapped.name_type,
        source_properties,
        source_indexes,
        keyof_any_constraint,
        template_parameters,
    })
}

fn validate_source_mapped_relation_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    utility_modifiers: bool,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(invalid());
    };
    let declaration = mapped.declaration.ok_or_else(invalid)?;
    let symbol = record.symbol().ok_or_else(invalid)?;
    let parameter = mapped.type_parameter.ok_or_else(invalid)?;
    let parameter_owner =
        cached_ordinary_type_parameter_owner(store, parameter).ok_or_else(invalid)?;
    let Some([parameter_declaration]) = store
        .symbol(parameter_owner)
        .and_then(|owner| owner.declarations())
    else {
        return Err(invalid());
    };
    let operands = store
        .source_mapped_type_operands(declaration)
        .ok_or_else(invalid)?;
    let constraint_node = operands.constraint;
    let constraint = mapped.constraint_type.ok_or_else(invalid)?;
    let template = mapped.template_type.ok_or_else(invalid)?;
    let modifiers_type = mapped.modifiers_type.ok_or_else(invalid)?;
    let template_node = operands.template;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    let allowed_flags = ObjectFlags::MAPPED
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::PROPAGATING_FLAGS;
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::MAPPED)
        || !(record.object_flags() & !allowed_flags).is_empty()
        || record.alias().is_some()
        || mapped.object.target.is_some()
        || mapped.object.mapper.is_some()
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.contains_error
        || !store.source_declaration_belongs_to_symbol(declaration, symbol)
        || !store.source_symbol_declarations_match(symbol)
        || store
            .symbol(symbol)
            .is_none_or(|owner| owner.flags() != SymbolFlags::TYPE_LITERAL)
        || store.type_node_links(declaration)
            != Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                outer_type_parameters: None,
            })
        || store.source_node_parent(*parameter_declaration)
            != Some(SourceNodeParent::Parent(declaration))
        || *parameter_declaration != operands.type_parameter
        || !store.source_declaration_belongs_to_symbol(*parameter_declaration, parameter_owner)
        || !matches!(store.type_payload(parameter).map(TypeRecord::data),
            Some(TypeData::TypeParameter(parameter)) if parameter.constraint == Some(constraint))
        || !store.source_direct_type_annotation_is_exact(constraint_node, constraint)
        || !template_node.map_or(template == bootstrap.any_type, |node| {
            store.source_direct_type_annotation_is_exact(node, template)
        })
    {
        return Err(invalid());
    }
    match (operands.name_type, mapped.name_type) {
        (None, None) => {}
        (Some(node), Some(type_)) if store.source_direct_type_annotation_is_exact(node, type_) => {}
        _ => return Err(invalid()),
    }
    if store.source_type_operator(constraint_node) == Some(SyntaxKind::KeyOfKeyword) {
        let source = store
            .source_direct_type_annotation(constraint_node)
            .ok_or_else(invalid)?;
        if !store.source_direct_type_annotation_is_exact(source, modifiers_type) {
            return Err(invalid());
        }
    } else if !utility_modifiers && modifiers_type != bootstrap.unknown_type {
        return Err(invalid());
    }
    Ok(())
}

fn validate_mapped_relation_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(invalid());
    };
    let Some(target) = mapped.object.target else {
        return validate_source_mapped_relation_identity(store, type_, false);
    };
    validate_source_mapped_relation_identity(store, target, true)?;
    let declaration = mapped.declaration.ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(alias_declaration)) = store.source_node_parent(declaration)
    else {
        return Err(invalid());
    };
    if store.source_node_kind(alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration) {
        return Err(invalid());
    }
    let alias = store
        .source_declaration_symbol(alias_declaration)
        .ok_or_else(invalid)?;
    if !store.source_symbol_declarations_match(alias) {
        return Err(invalid());
    }
    let links = store.type_alias_links(alias).ok_or_else(invalid)?;
    let parameters = links.type_parameters.as_deref().ok_or_else(invalid)?;
    let Some(TypeData::Mapped(original)) = store.type_payload(target).map(TypeRecord::data) else {
        return Err(invalid());
    };
    let substitution = mapped.object.mapper.ok_or_else(invalid)?;
    let Some(TypeMapperApplication::Composite { second, .. }) =
        store.mapper_application(substitution, original.type_parameter.ok_or_else(invalid)?)
    else {
        return Err(invalid());
    };
    let arguments = parameters
        .iter()
        .map(|parameter| store.map_type(second, *parameter))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(invalid)?;
    let modifiers = store.declared_mapped_modifiers(type_)?;
    let validated = match parameters {
        [_] => store.validate_homomorphic_mapped_alias_instantiation(
            alias, target, parameters, &arguments, type_, modifiers,
        ),
        [_, _]
            if matches!(
                original
                    .template_type
                    .and_then(|template| store.type_payload(template))
                    .map(TypeRecord::data),
                Some(TypeData::IndexedAccess(_))
            ) =>
        {
            store.validate_pick_mapped_alias_instantiation(
                alias, target, parameters, &arguments, type_,
            )
        }
        [_, _] => store.validate_record_mapped_alias_instantiation(
            alias, target, parameters, &arguments, type_,
        ),
        _ => return Err(MappedTypeError::UnsupportedSource(type_)),
    };
    validated?;
    let identity = record
        .alias()
        .and_then(|identity| store.type_alias(identity))
        .ok_or_else(invalid)?;
    let owner = identity.symbol().ok_or_else(invalid)?;
    let owner_arguments = identity.type_arguments().ok_or_else(invalid)?;
    let key = if owner == alias {
        if owner_arguments != arguments {
            return Err(invalid());
        }
        type_alias_instantiation_cache_key(&arguments, None)
    } else {
        let owner_record = store.symbol(owner).ok_or_else(invalid)?;
        let Some([owner_declaration]) = owner_record.declarations() else {
            return Err(invalid());
        };
        let owner_links = store.type_alias_links(owner).ok_or_else(invalid)?;
        let body = store
            .source_direct_type_annotation(*owner_declaration)
            .ok_or_else(invalid)?;
        if owner_record.flags() != SymbolFlags::TYPE_ALIAS
            || !store.source_symbol_declarations_match(owner)
            || owner_links.declared_type != Some(type_)
            || owner_links.type_parameters.as_deref().unwrap_or_default() != owner_arguments
            || !store.source_direct_type_annotation_is_exact(body, type_)
        {
            return Err(invalid());
        }
        let global = store
            .symbol_store()
            .assigned_global_symbol_id(owner)
            .ok_or_else(invalid)?;
        type_alias_instantiation_cache_key(&arguments, Some((global, owner_arguments)))
    };
    if links
        .instantiations
        .as_ref()
        .and_then(|entries| entries.get(&key))
        != Some(&type_)
    {
        return Err(invalid());
    }
    Ok(())
}

fn mapped_type_parameter_owner(
    store: &CanonicalTypeMapperStore,
    mapped_type: TypeId,
    parameter: TypeId,
) -> Option<SemanticSymbolId> {
    let record = store.type_payload(mapped_type)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return None;
    };
    if mapped.type_parameter != Some(parameter) {
        return None;
    }
    if let Some(owner) = cached_ordinary_type_parameter_owner(store, parameter) {
        return (!record.object_flags().contains(ObjectFlags::INSTANTIATED)).then_some(owner);
    }
    if !record
        .object_flags()
        .contains(ObjectFlags::INSTANTIATED_MAPPED)
    {
        return None;
    }
    let target = mapped.object.target?;
    let instantiation_mapper = mapped.object.mapper?;
    let TypeData::Mapped(original) = store.type_payload(target)?.data() else {
        return None;
    };
    let original_parameter = original.type_parameter?;
    let owner = cached_ordinary_type_parameter_owner(store, original_parameter)?;
    let parameter_record = store.type_payload(parameter)?;
    let TypeData::TypeParameter(cloned) = parameter_record.data() else {
        return None;
    };
    let TypeMapperApplication::Composite { first, second } =
        store.mapper_application(instantiation_mapper, original_parameter)?
    else {
        return None;
    };
    let computed_variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    (parameter_record.flags() == TypeFlags::TYPE_PARAMETER
        && (parameter_record.object_flags() == ObjectFlags::NONE
            || parameter_record.object_flags() == computed_variable_flags)
        && parameter_record.alias().is_none()
        && parameter_record.symbol() == Some(owner)
        && cloned.target == Some(original_parameter)
        && cloned.mapper == Some(instantiation_mapper)
        && cloned.constraint == mapped.constraint_type
        && cloned.resolved_default_type.is_none()
        && !cloned.is_this_type
        && mapped.declaration == original.declaration
        && record.symbol() == store.type_payload(target)?.symbol()
        && store.type_mapper_has_exact_endpoints(first, &[original_parameter], &[parameter])
            == Some(true)
        && mapped_instantiated_operand_matches(
            store,
            second,
            original.constraint_type?,
            mapped.constraint_type?,
            original_parameter,
            parameter,
        )
        && (mapped_instantiated_operand_matches(
            store,
            second,
            original.template_type?,
            mapped.template_type?,
            original_parameter,
            parameter,
        ) || instantiated_member_type_matches(
            store,
            original.template_type?,
            mapped.template_type?,
            instantiation_mapper,
            None,
        )
        .ok()
            == Some(true))
        && store.map_type(second, original.modifiers_type?) == mapped.modifiers_type)
        .then_some(owner)
}

fn mapped_instantiated_operand_matches(
    store: &CanonicalTypeMapperStore,
    mapper: TypeMapperId,
    original: TypeId,
    instantiated: TypeId,
    original_parameter: TypeId,
    instantiated_parameter: TypeId,
) -> bool {
    if store.map_type(mapper, original) == Some(instantiated) {
        return true;
    }

    match (
        store.type_payload(original).map(TypeRecord::data),
        store.type_payload(instantiated).map(TypeRecord::data),
    ) {
        (Some(TypeData::Index(index)), _) if index.index_flags == IndexFlags::NONE => {
            let Some(source) = store.map_type(mapper, index.target) else {
                return false;
            };
            plan_nongeneric_keyof_type(store, source)
                .ok()
                .and_then(|plan| cached_nongeneric_keyof_type(store, &plan).ok())
                == Some(Some(instantiated))
        }
        (Some(TypeData::IndexedAccess(original)), Some(TypeData::IndexedAccess(instantiated))) => {
            original.index_type == original_parameter
                && instantiated.index_type == instantiated_parameter
                && original.access_flags == AccessFlags::NONE
                && instantiated.access_flags == AccessFlags::NONE
                && store.map_type(mapper, original.object_type) == Some(instantiated.object_type)
        }
        (Some(TypeData::Conditional(original)), Some(TypeData::Conditional(instantiated))) => {
            let Some(TypeData::IndexedAccess(original_check)) = store
                .type_payload(original.check_type)
                .map(TypeRecord::data)
            else {
                return false;
            };
            let Some(TypeData::IndexedAccess(instantiated_check)) = store
                .type_payload(instantiated.check_type)
                .map(TypeRecord::data)
            else {
                return false;
            };
            original.root == instantiated.root
                && original.extends_type == instantiated.extends_type
                && original.mapper.is_none()
                && original.combined_mapper.is_none()
                && instantiated.mapper.is_some()
                && instantiated.combined_mapper.is_none()
                && original_check.index_type == original_parameter
                && instantiated_check.index_type == instantiated_parameter
                && original_check.access_flags == AccessFlags::NONE
                && instantiated_check.access_flags == AccessFlags::NONE
                && store.map_type(mapper, original_check.object_type)
                    == Some(instantiated_check.object_type)
        }
        _ => false,
    }
}

fn source_properties(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Vec<SourceProperty>, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidSource(type_))?;
    if record
        .flags()
        .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        return Ok(Vec::new());
    }
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        return Err(MappedTypeError::UnsupportedSource(type_));
    }
    let structured = record
        .data()
        .structured()
        .ok_or(MappedTypeError::UnsupportedSource(type_))?;
    if structured.call_signature_count != 0 || structured.signatures.is_some() {
        return Err(MappedTypeError::UnsupportedSource(type_));
    }
    let properties = structured.properties.as_deref().unwrap_or_default();
    let table = match structured.members {
        Some(table) => Some(
            store
                .symbol_table(table)
                .ok_or(MappedTypeError::InvalidSource(type_))?,
        ),
        None if properties.is_empty() => None,
        None => return Err(MappedTypeError::InvalidSource(type_)),
    };
    let has_indexes = structured
        .index_infos
        .as_ref()
        .is_some_and(|indexes| !indexes.is_empty());
    let has_reserved_index = has_indexes && !matches!(record.data(), TypeData::Mapped(_));
    if table.is_some_and(|table| {
        table.len()
            != properties
                .len()
                .saturating_add(usize::from(has_reserved_index))
            || table.get(InternalSymbolName::Index.as_ref()).is_some() != has_reserved_index
    }) || table.is_none() && has_indexes
    {
        return Err(MappedTypeError::InvalidSource(type_));
    }
    if has_reserved_index {
        let symbol = table
            .and_then(|table| table.get(InternalSymbolName::Index.as_ref()))
            .and_then(|symbol| store.symbol(symbol))
            .ok_or(MappedTypeError::InvalidSource(type_))?;
        if symbol.flags() != SymbolFlags::SIGNATURE
            || symbol.check_flags() != CheckFlags::NONE
            || symbol.parent() != record.symbol()
        {
            return Err(MappedTypeError::InvalidSource(type_));
        }
    }

    let mut result = Vec::with_capacity(properties.len());
    let mut seen = HashSet::with_capacity(properties.len());
    for symbol in properties {
        let property = store
            .symbol(*symbol)
            .ok_or(MappedTypeError::InvalidSource(type_))?;
        if !property.flags().contains(SymbolFlags::PROPERTY)
            || property.name().as_utf8().is_none()
            || property.name().is_reserved_member_name()
            || table.is_none_or(|table| table.get(property.name()) != Some(*symbol))
            || !seen.insert(*symbol)
        {
            return Err(MappedTypeError::InvalidSource(type_));
        }
        let links = store
            .value_symbol_links(*symbol)
            .ok_or(MappedTypeError::InvalidSource(type_))?;
        if links.resolved_type.is_none() && !property.check_flags().contains(CheckFlags::MAPPED) {
            return Err(MappedTypeError::InvalidSource(type_));
        }
        result.push(SourceProperty {
            symbol: *symbol,
            name: property.name().to_owned(),
            optional: property.flags().contains(SymbolFlags::OPTIONAL),
            readonly: property.check_flags().contains(CheckFlags::READONLY),
        });
    }
    Ok(result)
}

fn source_indexes(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Vec<SourceIndex>, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidSource(type_))?;
    if record
        .flags()
        .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        return Ok(Vec::new());
    }
    let structured = record
        .data()
        .structured()
        .ok_or(MappedTypeError::InvalidSource(type_))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    let mut result = Vec::new();
    let mut seen = HashSet::new();
    for index in structured.index_infos.as_deref().unwrap_or_default() {
        let info = store
            .index_info(*index)
            .ok_or(MappedTypeError::InvalidSource(type_))?;
        let valid_key = [
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.es_symbol_type,
        ]
        .contains(&info.key_type())
            || is_template_pattern_index_key(store, info.key_type());
        if !valid_key
            || !seen.insert(info.key_type())
            || store.type_payload(info.value_type()).is_none()
        {
            return Err(MappedTypeError::InvalidSource(type_));
        }
        result.push(SourceIndex {
            key_type: info.key_type(),
            value_type: info.value_type(),
            readonly: info.is_readonly(),
        });
    }
    Ok(result)
}

fn plan_mapped_members(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    modifiers: MappedTypeModifiers,
) -> Result<(Vec<PlannedMappedProperty>, Vec<PlannedMappedIndex>), MappedTypeError> {
    let indexes = plan_mapped_index_signatures(store, shape, modifiers)?.unwrap_or_default();
    let has_finite_keys = matches!(
        store.type_payload(shape.constraint_type).map(TypeRecord::data),
        Some(TypeData::Union(union))
            if union
                .union
                .types
                .iter()
                .any(|key| escaped_property_name_from_type(store, *key).is_some())
    );
    let properties = if indexes.is_empty() || !shape.source_properties.is_empty() || has_finite_keys
    {
        plan_mapped_properties(store, shape, modifiers)?
    } else {
        Vec::new()
    };
    Ok((properties, indexes))
}

fn plan_mapped_index_signatures(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    modifiers: MappedTypeModifiers,
) -> Result<Option<Vec<PlannedMappedIndex>>, MappedTypeError> {
    if shape
        .name_type
        .is_some_and(|name| name != shape.type_parameter)
    {
        return Ok(None);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    let constraint =
        store
            .type_payload(shape.constraint_type)
            .ok_or(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ))?;
    // Written `keyof` constraints enumerate the source's index signatures.
    // Upstream gives `any` one string index in this path.
    let mut keys = match constraint.data() {
        _ if shape.keyof_any_constraint => vec![bootstrap.string_type],
        TypeData::Intrinsic(_) | TypeData::TemplateLiteral(_) => {
            let Some(key) = mapped_index_key_type(store, shape.constraint_type) else {
                return Ok(None);
            };
            vec![key]
        }
        TypeData::Union(union) => {
            let index_keys = union
                .union
                .types
                .iter()
                .copied()
                .filter_map(|key| mapped_index_key_type(store, key))
                .collect::<Vec<_>>();
            if index_keys.is_empty()
                || union.union.types.iter().any(|key| {
                    mapped_index_key_type(store, *key).is_none()
                        && escaped_property_name_from_type(store, *key).is_none()
                })
            {
                return Ok(None);
            }
            if shape.source_indexes.is_empty() {
                index_keys
            } else {
                shape
                    .source_indexes
                    .iter()
                    .map(|index| index.key_type)
                    .collect()
            }
        }
        TypeData::Index(index)
            if index.target == shape.modifiers_type && !shape.source_indexes.is_empty() =>
        {
            shape
                .source_indexes
                .iter()
                .map(|index| index.key_type)
                .collect()
        }
        _ => return Ok(None),
    };
    keys.sort_unstable();
    keys.dedup();

    let mut result = Vec::with_capacity(keys.len());
    for key_type in keys {
        let source = shape
            .source_indexes
            .iter()
            .find(|index| index.key_type == key_type)
            .or_else(|| {
                if key_type == bootstrap.number_type
                    || is_template_pattern_index_key(store, key_type)
                {
                    shape
                        .source_indexes
                        .iter()
                        .find(|index| index.key_type == bootstrap.string_type)
                } else {
                    None
                }
            });
        let optional = bootstrap.options.strict_null_checks
            && modifiers.contains(MappedTypeModifiers::INCLUDE_OPTIONAL);
        let value_type = if optional
            || shape.template_parameters.is_some() && !mapped_template_indexes_source(store, shape)
        {
            PlannedMappedIndexValue::Template
        } else {
            PlannedMappedIndexValue::Resolved(mapped_index_value_type(
                store, shape, key_type, source,
            )?)
        };
        let readonly = modifiers.contains(MappedTypeModifiers::INCLUDE_READONLY)
            || !modifiers.contains(MappedTypeModifiers::EXCLUDE_READONLY)
                && source.is_some_and(|index| index.readonly);
        result.push(PlannedMappedIndex {
            key_type,
            value_type,
            readonly,
        });
    }
    Ok(Some(result))
}

fn mapped_index_value_type(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    source: Option<&SourceIndex>,
) -> Result<TypeId, MappedTypeError> {
    if shape.template_type == shape.type_parameter {
        return Ok(key_type);
    }
    let template = store
        .type_payload(shape.template_type)
        .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))?;
    match template.data() {
        TypeData::IndexedAccess(_) if mapped_template_indexes_source(store, shape) => source
            .map(|index| index.value_type)
            .or_else(|| {
                store
                    .type_payload(shape.modifiers_type)
                    .filter(|record| record.flags().contains(TypeFlags::ANY))
                    .map(|_| shape.modifiers_type)
            })
            .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type)),
        _ if store
            .type_payload(shape.type_)
            .is_some_and(|record| record.object_flags().contains(ObjectFlags::INSTANTIATED))
            && !mapped_template_source_is_exact(
                store,
                shape.template_type,
                shape.modifiers_type,
                shape.type_parameter,
            ) =>
        {
            Ok(shape.template_type)
        }
        TypeData::Intrinsic(_) | TypeData::Literal(_) => Ok(shape.template_type),
        _ => Err(MappedTypeError::UnsupportedTemplate(shape.template_type)),
    }
}

fn mapped_template_indexes_source(store: &CanonicalTypeMapperStore, shape: &MappedShape) -> bool {
    let Some(TypeData::IndexedAccess(indexed)) = store
        .type_payload(shape.template_type)
        .map(TypeRecord::data)
    else {
        return false;
    };
    let [source, key] = shape
        .template_parameters
        .unwrap_or([shape.modifiers_type, shape.type_parameter]);
    indexed.object_type == source
        && indexed.index_type == key
        && indexed.access_flags == AccessFlags::NONE
}

fn mapped_template_mapping(shape: &MappedShape, key_type: TypeId) -> (Vec<TypeId>, Vec<TypeId>) {
    match shape.template_parameters {
        Some(parameters) => (parameters.to_vec(), vec![shape.modifiers_type, key_type]),
        None => (vec![shape.type_parameter], vec![key_type]),
    }
}

fn plan_mapped_properties(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    modifiers: MappedTypeModifiers,
) -> Result<Vec<PlannedMappedProperty>, MappedTypeError> {
    let keys = constraint_keys(store, shape)?;
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?
        .options
        .strict_null_checks;
    let mut properties = Vec::<PlannedMappedProperty>::new();
    let mut indexes = HashMap::<EscapedName, usize>::new();

    for key in keys {
        let origin = key.escaped_name(store).and_then(|name| {
            shape
                .source_properties
                .iter()
                .find(|property| property.name == name)
                .cloned()
        });
        let names = mapped_name_types(store, shape, &key)?;
        for name_type in names {
            let name =
                name_type
                    .escaped_name(store)
                    .ok_or(MappedTypeError::UnsupportedNameType(
                        shape.name_type.unwrap_or(shape.type_parameter),
                    ))?;
            if let Some(index) = indexes.get(&name).copied() {
                properties[index].keys.push(key.clone());
                properties[index].name_types.push(name_type);
                continue;
            }
            let optional = modifiers.contains(MappedTypeModifiers::INCLUDE_OPTIONAL)
                || !modifiers.contains(MappedTypeModifiers::EXCLUDE_OPTIONAL)
                    && origin.as_ref().is_some_and(|property| property.optional);
            let readonly = modifiers.contains(MappedTypeModifiers::INCLUDE_READONLY)
                || !modifiers.contains(MappedTypeModifiers::EXCLUDE_READONLY)
                    && origin.as_ref().is_some_and(|property| property.readonly);
            let strip_optional =
                strict && !optional && origin.as_ref().is_some_and(|property| property.optional);
            indexes.insert(name.clone(), properties.len());
            properties.push(PlannedMappedProperty {
                name,
                name_types: vec![name_type],
                keys: vec![key.clone()],
                origin: origin.as_ref().map(|property| property.symbol),
                optional,
                readonly,
                strip_optional,
            });
        }
    }
    Ok(properties)
}

fn constraint_keys(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    constraint_keys_with_active_constraints(store, shape, &mut HashSet::new())
}

fn constraint_keys_with_active_constraints(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    active_constraints: &mut HashSet<TypeId>,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    if !active_constraints.insert(shape.constraint_type) {
        return Err(MappedTypeError::UnsupportedConstraint(
            shape.constraint_type,
        ));
    }
    let result = constraint_keys_worker(store, shape, active_constraints);
    active_constraints.remove(&shape.constraint_type);
    result
}

fn constraint_keys_worker(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    active_constraints: &mut HashSet<TypeId>,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    let record =
        store
            .type_payload(shape.constraint_type)
            .ok_or(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ))?;
    let keys = match record.data() {
        TypeData::Index(index) if index.target == shape.modifiers_type => {
            mapped_source_property_keys(store, shape)?
        }
        TypeData::Union(union)
            if !shape.source_indexes.is_empty()
                && union.union.types.iter().any(|key| {
                    shape
                        .source_indexes
                        .iter()
                        .any(|index| index.key_type == *key)
                }) =>
        {
            mapped_source_property_keys(store, shape)?
        }
        TypeData::Union(union)
            if shape
                .name_type
                .is_none_or(|name| name == shape.type_parameter)
                && union
                    .union
                    .types
                    .iter()
                    .any(|key| mapped_index_key_type(store, *key).is_some()) =>
        {
            union
                .union
                .types
                .iter()
                .copied()
                .filter(|key| mapped_index_key_type(store, *key).is_none())
                .map(MappedTypeKey::Existing)
                .collect()
        }
        TypeData::Union(union) => union
            .union
            .types
            .iter()
            .copied()
            .map(MappedTypeKey::Existing)
            .collect(),
        TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => {
            vec![MappedTypeKey::Existing(shape.constraint_type)]
        }
        TypeData::Intrinsic(_) if record.flags().contains(TypeFlags::NEVER) => Vec::new(),
        TypeData::TypeParameter(parameter) => {
            let constraint = parameter
                .constraint
                .ok_or(MappedTypeError::UnsupportedConstraint(
                    shape.constraint_type,
                ))?;
            if constraint == shape.constraint_type {
                return Err(MappedTypeError::UnsupportedConstraint(
                    shape.constraint_type,
                ));
            }
            let constraint_contains_index_keys =
                match store.type_payload(constraint).map(TypeRecord::data) {
                    Some(TypeData::Union(union)) => union
                        .union
                        .types
                        .iter()
                        .any(|key| mapped_index_key_type(store, *key).is_some()),
                    Some(_) => mapped_index_key_type(store, constraint).is_some(),
                    None => {
                        return Err(MappedTypeError::UnsupportedConstraint(constraint));
                    }
                };
            if shape.source_indexes.is_empty() && constraint_contains_index_keys {
                return Err(MappedTypeError::UnsupportedConstraint(
                    shape.constraint_type,
                ));
            }
            let mut nested = shape.clone();
            nested.constraint_type = constraint;
            constraint_keys_with_active_constraints(store, &nested, active_constraints)?
        }
        _ => {
            return Err(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ));
        }
    };
    for key in &keys {
        if key.escaped_name(store).is_none() {
            return Err(MappedTypeError::UnsupportedConstraint(
                key.cached_type(store).unwrap_or(shape.constraint_type),
            ));
        }
    }
    Ok(keys)
}

fn mapped_source_property_keys(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    shape
        .source_properties
        .iter()
        .map(|property| {
            property
                .name
                .as_ref()
                .as_utf8()
                .map(str::to_owned)
                .map(|name| MappedTypeKey::source_string(store, name))
                .ok_or(MappedTypeError::InvalidSource(shape.modifiers_type))
        })
        .collect()
}

fn mapped_name_types(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key: &MappedTypeKey,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    let Some(name_type) = shape.name_type else {
        return Ok(vec![key.clone()]);
    };
    substitute_name_type(store, shape.type_parameter, key, name_type)
}

fn substitute_name_type(
    store: &CanonicalTypeMapperStore,
    parameter: TypeId,
    key: &MappedTypeKey,
    name_type: TypeId,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    substitute_name_type_worker(store, parameter, key, name_type, &mut HashSet::new())
}

fn substitute_name_type_worker(
    store: &CanonicalTypeMapperStore,
    parameter: TypeId,
    key: &MappedTypeKey,
    name_type: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<Vec<MappedTypeKey>, MappedTypeError> {
    if name_type == parameter {
        return Ok(vec![key.clone()]);
    }
    if !visiting.insert(name_type) {
        return Err(MappedTypeError::UnsupportedNameType(name_type));
    }
    let result = (|| {
        let record = store
            .type_payload(name_type)
            .ok_or(MappedTypeError::UnsupportedNameType(name_type))?;
        match record.data() {
            TypeData::Literal(_) if property_name_from_type(store, name_type).is_some() => {
                Ok(vec![MappedTypeKey::Existing(name_type)])
            }
            TypeData::Intrinsic(_) if record.flags().contains(TypeFlags::NEVER) => Ok(Vec::new()),
            TypeData::Union(union) => union
                .union
                .types
                .iter()
                .map(|candidate| {
                    substitute_name_type_worker(store, parameter, key, *candidate, visiting)
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|types| types.into_iter().flatten().collect()),
            TypeData::TemplateLiteral(template) => {
                if template.texts.len() != template.types.len().saturating_add(1) {
                    return Err(MappedTypeError::UnsupportedNameType(name_type));
                }
                let mut names = vec![template.texts[0].clone()];
                for (index, placeholder) in template.types.iter().enumerate() {
                    let candidates =
                        substitute_name_type_worker(store, parameter, key, *placeholder, visiting)?;
                    let size = names.len().saturating_mul(candidates.len());
                    if size >= MAX_TEMPLATE_UNION_SIZE {
                        return Err(MappedTypeError::CrossProductTooLarge {
                            size,
                            limit: MAX_TEMPLATE_UNION_SIZE,
                        });
                    }
                    let mut next = Vec::with_capacity(size);
                    for prefix in names {
                        for candidate in &candidates {
                            let candidate = candidate
                                .name(store)
                                .ok_or(MappedTypeError::UnsupportedNameType(*placeholder))?;
                            let mut name = prefix.clone();
                            append_js_string(&mut name, &candidate);
                            append_js_string(&mut name, &template.texts[index + 1]);
                            next.push(name);
                        }
                    }
                    names = next;
                }
                Ok(names
                    .into_iter()
                    .map(|name| MappedTypeKey::source_string(store, name))
                    .collect())
            }
            TypeData::StringMapping(mapping) => {
                let operation = record
                    .symbol()
                    .and_then(|symbol| store.symbol(symbol))
                    .and_then(|symbol| symbol.name().as_utf8())
                    .and_then(StringMappingKind::from_name)
                    .ok_or(MappedTypeError::UnsupportedNameType(name_type))?;
                let targets =
                    substitute_name_type_worker(store, parameter, key, mapping.target, visiting)?;
                targets
                    .into_iter()
                    .map(|target| {
                        let name = target
                            .name(store)
                            .ok_or(MappedTypeError::UnsupportedNameType(mapping.target))?;
                        Ok(MappedTypeKey::source_string(store, operation.apply(&name)))
                    })
                    .collect()
            }
            _ => Err(MappedTypeError::UnsupportedNameType(name_type)),
        }
    })();
    visiting.remove(&name_type);
    result
}

fn property_name_from_type(store: &CanonicalTypeMapperStore, type_: TypeId) -> Option<String> {
    match store.type_payload(type_)?.data() {
        TypeData::Literal(literal) => match &literal.value {
            LiteralValue::String(value) => Some(value.clone()),
            LiteralValue::Number(value) => Some(value.to_string()),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn escaped_property_name_from_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<EscapedName> {
    match store.type_payload(type_)?.data() {
        TypeData::UniqueEsSymbol(symbol) => Some(symbol.name.clone()),
        _ => property_name_from_type(store, type_).map(EscapedName::source),
    }
}

fn mapped_index_key_type(store: &CanonicalTypeMapperStore, type_: TypeId) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    let record = store.type_payload(type_)?;
    if record.flags().contains(TypeFlags::ANY) {
        Some(bootstrap.string_type)
    } else if [
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.es_symbol_type,
    ]
    .contains(&type_)
        || is_template_pattern_index_key(store, type_)
    {
        Some(type_)
    } else {
        None
    }
}

fn validate_warm_mapped_members(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    expected_properties: &[PlannedMappedProperty],
    expected_indexes: &[PlannedMappedIndex],
) -> Result<Option<ResolvedMappedTypeMembers>, MappedTypeError> {
    let record = store
        .type_payload(shape.type_)
        .ok_or(MappedTypeError::InvalidMappedType(shape.type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(shape.type_));
    };
    let structured = &mapped.object.structured;
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        if structured != &StructuredTypeData::default() {
            return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
        }
        return Ok(None);
    }
    let members = structured
        .members
        .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
    let properties = structured.properties.as_deref().unwrap_or_default();
    let table = store
        .symbol_table(members)
        .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
    let indexes = structured.index_infos.as_deref().unwrap_or_default();
    if properties.len() != expected_properties.len()
        || structured.properties.is_some() == expected_properties.is_empty()
        || table.len() != expected_properties.len()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || indexes.len() != expected_indexes.len()
        || structured.index_infos.is_some() == expected_indexes.is_empty()
    {
        return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
    }
    for (id, expected) in indexes.iter().zip(expected_indexes) {
        let index = store
            .index_info(*id)
            .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
        let matches = if let Some(recovery) = store.mapped_index_recovery(*id) {
            recovery.matches(store, *id, shape, expected)
        } else {
            cached_mapped_index_value_type(store, shape, expected)? == Some(index.value_type())
        };
        if !matches
            || index.key_type() != expected.key_type
            || index.is_readonly() != expected.readonly
            || index.declaration().is_some()
            || index.index_symbol().is_some()
            || !index.components().is_empty()
        {
            return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
        }
    }
    for (symbol, expected) in properties.iter().zip(expected_properties) {
        let property = store
            .symbol(*symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(*symbol))?;
        let value = store
            .value_symbol_links(*symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(*symbol))?;
        let mapped = store
            .mapped_symbol_links(*symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(*symbol))?;
        let expected_flags = SymbolFlags::PROPERTY
            | SymbolFlags::TRANSIENT
            | if expected.optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let expected_checks = expected_check_flags(store, expected)?;
        if property.flags() != expected_flags
            || property.check_flags() != expected_checks
            || property.name() != expected.name.as_ref()
            || property.value_declaration().is_some()
            || property.parent().is_some()
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || table.get(property.name()) != Some(*symbol)
            || mapped.synthetic_origin != expected.origin
            || mapped.key_type.is_none()
            || !keys_match(store, mapped.key_type, &expected.keys)
            || value.containing_type != Some(shape.type_)
            || !keys_match(store, value.name_type, &expected.name_types)
            || value.target.is_some()
            || value.mapper.is_some()
            || value.write_type.is_some()
            || value.function_or_constructor_checked
            || value
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
            || property.declarations()
                != expected.origin.and_then(|origin| {
                    should_link_source_declarations(shape)
                        .then(|| store.symbol(origin)?.declarations())
                        .flatten()
                })
        {
            return Err(MappedTypeError::InvalidCachedProperty(*symbol));
        }
        if let Some(cached) = value.resolved_type {
            let key_type = mapped
                .key_type
                .ok_or(MappedTypeError::InvalidCachedProperty(*symbol))?;
            let matches = if let Some(recovery) = store.mapped_property_recovery(*symbol) {
                recovery.matches(store, *symbol, shape, key_type, cached)
            } else {
                cached_mapped_property_type(store, shape, expected, key_type)? == Some(cached)
            };
            if !matches {
                return Err(MappedTypeError::InvalidCachedProperty(*symbol));
            }
        }
    }
    Ok(Some(ResolvedMappedTypeMembers {
        type_: shape.type_,
        members,
        properties: properties.to_vec(),
    }))
}

fn keys_match(
    store: &CanonicalTypeMapperStore,
    cached: Option<TypeId>,
    expected: &[MappedTypeKey],
) -> bool {
    let Some(cached) = cached else {
        return false;
    };
    let Some(mut expected) = expected
        .iter()
        .map(|identity| identity.cached_type(store))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    expected.sort_unstable();
    expected.dedup();
    match expected.as_slice() {
        [single] => cached == *single,
        _ => store
            .type_payload(cached)
            .and_then(|record| match record.data() {
                TypeData::Union(union) => Some(&union.union.types),
                _ => None,
            })
            .is_some_and(|types| {
                types.len() == expected.len()
                    && expected.iter().all(|identity| types.contains(identity))
            }),
    }
}

fn should_link_source_declarations(shape: &MappedShape) -> bool {
    shape.name_type.is_none() || shape.name_type == Some(shape.type_parameter)
}

fn expected_check_flags(
    store: &CanonicalTypeMapperStore,
    property: &PlannedMappedProperty,
) -> Result<CheckFlags, MappedTypeError> {
    let mut checks = CheckFlags::MAPPED;
    if property.readonly {
        checks |= CheckFlags::READONLY;
    }
    if property.strip_optional {
        checks |= CheckFlags::STRIP_OPTIONAL;
    }
    if let Some(origin) = property.origin {
        checks |= store
            .symbol(origin)
            .ok_or(MappedTypeError::InvalidCachedProperty(origin))?
            .check_flags()
            & CheckFlags::LATE;
    }
    Ok(checks)
}

fn publish_mapped_members(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    planned: Vec<PlannedMappedProperty>,
    indexes: &[PlannedMappedIndex],
    session: &mut InstantiationSession,
) -> Result<ResolvedMappedTypeMembers, MappedTypeError> {
    let table = PreparedSymbolTable::new(planned.len()).ok_or(MappedTypeError::Capacity)?;
    let mut pending_strings = Vec::new();
    let mut seen_pending = HashSet::new();
    let mut union_operations = 0usize;
    for property in &planned {
        expected_check_flags(store, property)?;
        for identities in [&property.keys, &property.name_types] {
            let mut unique = HashSet::new();
            for identity in identities {
                unique.insert(identity.clone());
                if let MappedTypeKey::Existing(type_) = identity {
                    store
                        .type_payload(*type_)
                        .ok_or(MappedTypeError::InvalidMappedType(*type_))?;
                }
                if let MappedTypeKey::String(value) = identity
                    && seen_pending.insert(value.clone())
                {
                    pending_strings.push(value.clone());
                }
            }
            if unique.len() > 1 {
                union_operations = union_operations
                    .checked_add(1)
                    .ok_or(MappedTypeError::Capacity)?;
            }
        }
    }
    let mut prepared = store
        .prepare_type_query_types(&pending_strings, &[], &[], union_operations, 0)
        .map_err(mapped_cache_error)?;
    let mut resolved_keys = Vec::with_capacity(planned.len());
    let mut resolved_names = Vec::with_capacity(planned.len());
    for property in &planned {
        resolved_keys.push(materialize_mapped_identities(
            store,
            &property.keys,
            &mut prepared,
        )?);
        resolved_names.push(materialize_mapped_identities(
            store,
            &property.name_types,
            &mut prepared,
        )?);
    }

    let mut property_data = Vec::with_capacity(planned.len());
    for property in &planned {
        let mut flags = SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT;
        if property.optional {
            flags |= SymbolFlags::OPTIONAL;
        }
        let mut data = SymbolData::new(flags, property.name.clone());
        data.check_flags = expected_check_flags(store, property)?;
        if should_link_source_declarations(shape)
            && let Some(origin) = property.origin
        {
            data.declarations = store
                .symbol(origin)
                .and_then(|source| source.declarations())
                .map(<[_]>::to_vec);
        }
        property_data.push(data);
    }

    // Resolve fallible values before publishing members or their resolved flag.
    let mut staged_indexes = Vec::with_capacity(indexes.len());
    for index in indexes {
        let limit_mark = session.limit_event_mark();
        let value_type = match index.value_type {
            PlannedMappedIndexValue::Resolved(value_type) => value_type,
            PlannedMappedIndexValue::Template => {
                instantiate_mapped_template(store, shape, index.key_type, session)?
            }
        };
        let identity = if session.recovery_error_type().is_some()
            && session.limit_event_occurred_since(limit_mark)
        {
            Some(
                mapped_property_recovery_identity(store, shape, index.key_type, value_type)
                    .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?,
            )
        } else {
            None
        };
        staged_indexes.push((index, value_type, identity));
    }
    if !store.try_reserve_checker_symbol_allocations(planned.len(), 1)
        || !store.try_reserve_value_symbol_links(planned.len())
        || !store.try_reserve_index_infos(indexes.len())
        || !store.try_reserve_mapped_index_recoveries(indexes.len())
    {
        return Err(MappedTypeError::Capacity);
    }

    let members = store.alloc_prepared_symbol_table(table);
    let mut properties = Vec::with_capacity(planned.len());
    for (((property, data), key), name_type) in planned
        .into_iter()
        .zip(property_data)
        .zip(resolved_keys)
        .zip(resolved_names)
    {
        let symbol = store
            .alloc_symbol(data)
            .expect("the mapped member transaction reserved its property symbols");
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                containing_type: Some(shape.type_),
                name_type: Some(name_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_mapped_symbol_links(
            symbol,
            MappedSymbolLinks {
                key_type: Some(key),
                synthetic_origin: property.origin,
            },
        ));
        assert_eq!(
            store.insert_symbol(members, property.name, symbol),
            Some(None)
        );
        properties.push(symbol);
    }
    let mut infos = Vec::with_capacity(staged_indexes.len());
    for (index, value_type, identity) in staged_indexes {
        let info = store
            .alloc_index_info(index.key_type, value_type, index.readonly, None, Vec::new())
            .expect("the mapped member transaction reserved its validated index records");
        if let Some(identity) = identity {
            assert!(store.publish_mapped_index_recovery(MappedIndexRecovery {
                valid: true,
                index: info,
                shape: shape.clone(),
                plan: *index,
                result: value_type,
                identity,
            }));
        }
        infos.push(info);
    }
    assert!(store.set_structured_type_members(
        shape.type_,
        Some(members),
        (!properties.is_empty()).then_some(properties.clone()),
        None,
        None,
        (!infos.is_empty()).then_some(infos),
    ));
    Ok(ResolvedMappedTypeMembers {
        type_: shape.type_,
        members,
        properties,
    })
}

fn materialize_mapped_identities(
    store: &mut CanonicalTypeMapperStore,
    identities: &[MappedTypeKey],
    prepared: &mut PreparedTypeQueryTypes,
) -> Result<TypeId, MappedTypeError> {
    let mut resolved = Vec::with_capacity(identities.len());
    for identity in identities {
        let type_ = match identity {
            MappedTypeKey::Existing(type_) => *type_,
            MappedTypeKey::String(value) => store
                .regular_string_literal_type(value.clone())
                .map_err(mapped_cache_error)?,
        };
        if !resolved.contains(&type_) {
            resolved.push(type_);
        }
    }
    match resolved.as_slice() {
        [single] => Ok(*single),
        [] => Err(MappedTypeError::Capacity),
        _ => store
            .literal_union_type_prepared(&resolved, None, prepared)
            .map_err(mapped_cache_error),
    }
}

fn validate_mapped_property_header(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<(TypeId, TypeId, Option<TypeId>), MappedTypeError> {
    let property = store
        .symbol(symbol)
        .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
    if !property
        .flags()
        .contains(SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
        || !property.check_flags().contains(CheckFlags::MAPPED)
    {
        return Err(MappedTypeError::InvalidCachedProperty(symbol));
    }
    let value = store
        .value_symbol_links(symbol)
        .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
    let mapped = store
        .mapped_symbol_links(symbol)
        .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
    let containing_type = value
        .containing_type
        .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
    let key_type = mapped
        .key_type
        .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
    if !matches!(
        store.type_payload(containing_type).map(TypeRecord::data),
        Some(TypeData::Mapped(_))
    ) || store.type_payload(key_type).is_none()
    {
        return Err(MappedTypeError::InvalidCachedProperty(symbol));
    }
    Ok((containing_type, key_type, value.resolved_type))
}

fn cached_mapped_index_value_type(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    index: &PlannedMappedIndex,
) -> Result<Option<TypeId>, MappedTypeError> {
    match index.value_type {
        PlannedMappedIndexValue::Resolved(value_type) => Ok(Some(value_type)),
        PlannedMappedIndexValue::Template => {
            let Some(template) = cached_mapped_template_input(store, shape)? else {
                return Ok(None);
            };
            let (sources, targets) = mapped_template_mapping(shape, index.key_type);
            cached_instantiation_with_vector(store, template, &sources, &targets, None, None)
                .map_err(|error| mapped_instantiation_error(template, &error))
        }
    }
}

fn cached_mapped_property_type(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    property: &PlannedMappedProperty,
    key_type: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    let direct_request = direct_mapped_request_template(store, shape)?;
    let template_type = if direct_request {
        shape.template_type
    } else {
        let Some(template_type) = cached_mapped_template_input(store, shape)? else {
            return Ok(None);
        };
        template_type
    };
    let template = store
        .type_payload(template_type)
        .ok_or(MappedTypeError::UnsupportedTemplate(template_type))?;
    let raw = match template.data() {
        TypeData::IndexedAccess(_) if mapped_template_indexes_source(store, shape) => {
            cached_indexed_mapped_template(store, shape, key_type)?
        }
        TypeData::IndexedAccess(_) => {
            return Err(MappedTypeError::UnsupportedTemplate(template_type));
        }
        _ if template_type == shape.template_type
            && mapped_template_is_value_parameter(store, shape) =>
        {
            Some(template_type)
        }
        _ if template_type == shape.type_parameter => Some(key_type),
        _ if !template
            .flags()
            .intersects(TypeFlags::TYPE_PARAMETER | TypeFlags::UNION | TypeFlags::OBJECT) =>
        {
            Some(template_type)
        }
        _ => {
            let (sources, targets) = mapped_template_mapping(shape, key_type);
            cached_instantiation_with_vector(store, template_type, &sources, &targets, None, None)
                .map_err(|error| mapped_instantiation_error(template_type, &error))?
        }
    };
    let Some(mut type_) = raw else {
        return Ok(None);
    };
    if direct_request
        && let Some(sentinel) = mapped_optional_template_sentinel(store, shape)?
        && !mapped_optional_value_is_unchanged(store, type_, sentinel)?
    {
        let Some(optional) = store
            .cached_literal_union_type_with_alias(&[type_, sentinel], None, None)
            .map_err(mapped_cache_error)?
        else {
            return Ok(None);
        };
        type_ = optional;
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    let strict = bootstrap.options.strict_null_checks;
    let exact = bootstrap.options.exact_optional_property_types;
    let missing = bootstrap.undefined_or_missing_type;
    let add_optional =
        strict && property.optional && !type_contains_undefined_or_void(store, type_)?;
    if add_optional {
        let Some(optional) = store
            .cached_literal_union_type_with_alias(&[type_, missing], None, None)
            .map_err(mapped_cache_error)?
        else {
            return Ok(None);
        };
        type_ = optional;
    } else if property.strip_optional {
        let removed = if exact {
            missing
        } else {
            bootstrap.undefined_type
        };
        let Some(retained) = cached_remove_type(store, type_, removed)? else {
            return Ok(None);
        };
        type_ = retained;
        if !exact {
            return cached_remove_type(store, type_, bootstrap.void_type);
        }
    }
    Ok(Some(type_))
}

fn cached_remove_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    removed: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    if type_ == removed {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| Some(bootstrap.never_type))
            .ok_or(MappedTypeError::BootstrapUninitialized);
    }
    let Some(TypeData::Union(union)) = store.type_payload(type_).map(TypeRecord::data) else {
        return Ok(Some(type_));
    };
    let retained = union
        .union
        .types
        .iter()
        .copied()
        .filter(|candidate| *candidate != removed)
        .collect::<Vec<_>>();
    if retained.len() == union.union.types.len() {
        return Ok(Some(type_));
    }
    store
        .cached_literal_union_type_with_alias(&retained, None, None)
        .map_err(mapped_cache_error)
}

fn compute_mapped_property_type(
    store: &mut CanonicalTypeMapperStore,
    containing_type: TypeId,
    symbol: SemanticSymbolId,
    key_type: TypeId,
    session: &mut InstantiationSession,
) -> Result<TypeId, MappedTypeError> {
    let shape = validate_mapped_shape(store, containing_type)?;
    let mut type_ = instantiate_mapped_template(store, &shape, key_type, session)?;
    let (optional, strip_optional) = {
        let property = store
            .symbol(symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
        (
            property.flags().contains(SymbolFlags::OPTIONAL),
            property.check_flags().contains(CheckFlags::STRIP_OPTIONAL),
        )
    };
    let (strict, exact, undefined, missing, void) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| {
            (
                bootstrap.options.strict_null_checks,
                bootstrap.options.exact_optional_property_types,
                bootstrap.undefined_type,
                bootstrap.undefined_or_missing_type,
                bootstrap.void_type,
            )
        })
        .ok_or(MappedTypeError::BootstrapUninitialized)?;

    if strict && optional && !type_contains_undefined_or_void(store, type_)? {
        type_ = canonical_anonymous_union(store, &[type_, missing]).map_err(mapped_cache_error)?;
    } else if strip_optional {
        let sentinel = if exact { missing } else { undefined };
        type_ = remove_type(store, type_, sentinel)?;
        if !exact {
            type_ = remove_type(store, type_, void)?;
        }
    }
    Ok(type_)
}

fn mapped_template_is_value_parameter(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> bool {
    if let Some(TypeData::Mapped(mapped)) = store.type_payload(shape.type_).map(TypeRecord::data)
        && let Some(TypeData::Mapped(original)) = mapped
            .object
            .target
            .and_then(|target| store.type_payload(target))
            .map(TypeRecord::data)
        && original.template_type != original.type_parameter
        && original.template_type.is_some_and(|template| {
            matches!(
                store.type_payload(template).map(TypeRecord::data),
                Some(TypeData::TypeParameter(_))
            )
        })
    {
        return true;
    }
    false
}

fn mapped_optional_template_sentinel(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<Option<TypeId>, MappedTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    Ok((bootstrap.options.strict_null_checks
        && store
            .declared_mapped_modifiers(shape.type_)?
            .contains(MappedTypeModifiers::INCLUDE_OPTIONAL))
    .then_some(bootstrap.undefined_or_missing_type))
}

/// Keep the source identity when the exact optional sentinel is already first.
fn mapped_optional_value_is_unchanged(
    store: &CanonicalTypeMapperStore,
    value: TypeId,
    sentinel: TypeId,
) -> Result<bool, MappedTypeError> {
    let record = store
        .type_payload(value)
        .ok_or(MappedTypeError::InvalidMappedType(value))?;
    Ok(value == sentinel
        || record.flags().contains(TypeFlags::UNION)
            && matches!(record.data(), TypeData::Union(union)
                if union.union.types.first() == Some(&sentinel)))
}

/// Public mapped requests retain resolved operands without source annotation caches.
/// This finite interface form has an identity source operand during instantiation.
fn direct_mapped_request(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<bool, MappedTypeError> {
    if shape.template_parameters.is_some() || !shape.source_indexes.is_empty() {
        return Ok(false);
    }
    let Some(TypeData::Index(constraint)) = store
        .type_payload(shape.constraint_type)
        .map(TypeRecord::data)
    else {
        return Ok(false);
    };
    if constraint.target != shape.modifiers_type || constraint.index_flags != IndexFlags::NONE {
        return Ok(false);
    }
    let source = store
        .type_payload(shape.modifiers_type)
        .ok_or(MappedTypeError::InvalidSource(shape.modifiers_type))?;
    let TypeData::Interface(interface) = source.data() else {
        return Ok(false);
    };
    if !source.object_flags().contains(ObjectFlags::INTERFACE)
        || source.object_flags().contains(ObjectFlags::CLASS)
        || interface.outer_type_parameter_count != 0
        || interface
            .all_type_parameters
            .as_ref()
            .is_some_and(|types| !types.is_empty())
        || interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_some_and(|types| !types.is_empty())
    {
        return Ok(false);
    }
    let record = store
        .type_payload(shape.type_)
        .ok_or(MappedTypeError::InvalidMappedType(shape.type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(shape.type_));
    };
    if mapped.object.target.is_some() || mapped.object.mapper.is_some() {
        return Ok(false);
    }
    let declaration = mapped
        .declaration
        .ok_or(MappedTypeError::InvalidMappedType(shape.type_))?;
    let symbol = record
        .symbol()
        .ok_or(MappedTypeError::InvalidMappedType(shape.type_))?;
    validate_direct_mapped_request_identity(store, shape, declaration, symbol)?;
    Ok(true)
}

fn validate_direct_mapped_request_identity(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), MappedTypeError> {
    validate_mapped_request(
        store,
        MappedTypeRequest {
            declaration,
            symbol,
            type_parameter: shape.type_parameter,
            constraint_type: shape.constraint_type,
            template_type: shape.template_type,
            modifiers_type: shape.modifiers_type,
            name_type: shape.name_type,
        },
    )?;
    if store.type_node_links(declaration)
        != Some(&TypeNodeLinks {
            resolved_type: Some(shape.type_),
            outer_type_parameters: None,
        })
        || !matches!(store.type_payload(shape.type_parameter).map(TypeRecord::data),
            Some(TypeData::TypeParameter(parameter)) if parameter.constraint == Some(shape.constraint_type))
    {
        return Err(MappedTypeError::InvalidMappedType(shape.type_));
    }
    Ok(())
}

fn direct_mapped_request_template(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<bool, MappedTypeError> {
    if !mapped_template_indexes_source(store, shape) || !direct_mapped_request(store, shape)? {
        return Ok(false);
    }
    if cached_deferred_indexed_access_type(
        store,
        shape.modifiers_type,
        shape.type_parameter,
        AccessFlags::NONE,
    ) != Ok(Some(shape.template_type))
    {
        return Err(MappedTypeError::InvalidMappedType(shape.template_type));
    }
    let template = store
        .type_payload(shape.template_type)
        .ok_or(MappedTypeError::InvalidMappedType(shape.template_type))?;
    let TypeData::IndexedAccess(indexed) = template.data() else {
        return Err(MappedTypeError::InvalidMappedType(shape.template_type));
    };
    let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if template.object_flags() != ObjectFlags::NONE && template.object_flags() != variable_flags
        || indexed.constrained.resolved_base_constraint.is_some()
    {
        return Err(MappedTypeError::InvalidMappedType(shape.template_type));
    }
    Ok(true)
}

fn cached_mapped_template_input(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<Option<TypeId>, MappedTypeError> {
    match mapped_optional_template_sentinel(store, shape)? {
        Some(missing) => store
            .cached_literal_union_type_with_alias(&[shape.template_type, missing], None, None)
            .map_err(mapped_cache_error),
        None => Ok(Some(shape.template_type)),
    }
}

fn instantiate_mapped_template(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    session: &mut InstantiationSession,
) -> Result<TypeId, MappedTypeError> {
    // Go adds explicit optionality before substitution, including its depth frame.
    let template_type = match mapped_optional_template_sentinel(store, shape)? {
        Some(sentinel) if direct_mapped_request_template(store, shape)? => {
            return instantiate_direct_mapped_request_template(
                store, shape, key_type, sentinel, session,
            );
        }
        Some(missing) => canonical_anonymous_union(store, &[shape.template_type, missing])
            .map_err(mapped_cache_error)?,
        None => shape.template_type,
    };
    let template = store
        .type_payload(template_type)
        .ok_or(MappedTypeError::UnsupportedTemplate(template_type))?;
    match template.data() {
        TypeData::IndexedAccess(_) if mapped_template_indexes_source(store, shape) => {
            return indexed_mapped_template(store, shape, key_type, session);
        }
        TypeData::IndexedAccess(_) => {
            return Err(MappedTypeError::UnsupportedTemplate(template_type));
        }
        _ => {}
    }
    if template_type == shape.template_type && mapped_template_is_value_parameter(store, shape) {
        return Ok(template_type);
    }
    if template_type == shape.type_parameter {
        return Ok(key_type);
    }
    if !template
        .flags()
        .intersects(TypeFlags::TYPE_PARAMETER | TypeFlags::UNION | TypeFlags::OBJECT)
    {
        return Ok(template_type);
    }
    let (sources, targets) = mapped_template_mapping(shape, key_type);
    instantiate_type_with_vector_and_session(
        store,
        template_type,
        &sources,
        &targets,
        None,
        session,
    )
    .map_err(|error| mapped_instantiation_error(template_type, &error))
}

fn instantiate_direct_mapped_request_template(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    sentinel: TypeId,
    session: &mut InstantiationSession,
) -> Result<TypeId, MappedTypeError> {
    let sources = [shape.type_parameter];
    let targets = [key_type];
    let map_error = |error| mapped_instantiation_error(shape.template_type, &error);
    with_mapped_template_frame(
        store,
        MappedTemplateFrame::Optional {
            template: shape.template_type,
            sentinel,
        },
        &sources,
        &targets,
        session,
        map_error,
        |store, session| {
            let value = with_mapped_template_frame(
                store,
                MappedTemplateFrame::Indexed(shape.template_type),
                &sources,
                &targets,
                session,
                map_error,
                |store, session| {
                    let key = instantiate_type_with_vector_and_session(
                        store,
                        shape.type_parameter,
                        &sources,
                        &targets,
                        None,
                        session,
                    )
                    .map_err(map_error)?;
                    if session.recovery_error_type() == Some(key) {
                        return Ok(key);
                    }
                    indexed_mapped_template(store, shape, key, session)
                },
            )?;
            if mapped_optional_value_is_unchanged(store, value, sentinel)? {
                return Ok(value);
            }
            canonical_anonymous_union(store, &[value, sentinel]).map_err(mapped_cache_error)
        },
    )
}

fn cached_indexed_mapped_template(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    let mut values = Vec::new();
    for source in indexed_mapped_template_sources(store, shape, key_type)? {
        let value = match source {
            IndexedMappedValue::Property(symbol) => {
                let Some(value) = store
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                else {
                    return Ok(None);
                };
                value
            }
            IndexedMappedValue::Type(type_) => type_,
        };
        values.push(value);
    }
    match values.as_slice() {
        [value] => Ok(Some(*value)),
        _ => store
            .cached_literal_union_type_with_alias(&values, None, None)
            .map_err(mapped_cache_error),
    }
}

fn indexed_mapped_template(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    session: &mut InstantiationSession,
) -> Result<TypeId, MappedTypeError> {
    let mut values = Vec::new();
    for source in indexed_mapped_template_sources(store, shape, key_type)? {
        let value = match source {
            IndexedMappedValue::Property(symbol) => {
                let links = store
                    .value_symbol_links(symbol)
                    .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
                match links.resolved_type {
                    Some(resolved) => resolved,
                    None => store.resolve_mapped_symbol_type_with_session(symbol, session)?,
                }
            }
            IndexedMappedValue::Type(type_) => type_,
        };
        values.push(value);
    }
    match values.as_slice() {
        [value] => Ok(*value),
        [] => store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type)
            .ok_or(MappedTypeError::BootstrapUninitialized),
        _ => canonical_anonymous_union(store, &values).map_err(mapped_cache_error),
    }
}

enum IndexedMappedValue {
    Property(SemanticSymbolId),
    Type(TypeId),
}

fn indexed_mapped_template_sources(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
) -> Result<Vec<IndexedMappedValue>, MappedTypeError> {
    let keys = match store
        .type_payload(key_type)
        .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))?
        .data()
    {
        TypeData::Union(union) => union.union.types.clone(),
        _ => vec![key_type],
    };
    let mut values = Vec::with_capacity(keys.len());
    for key in keys {
        let name = property_name_from_type(store, key)
            .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))?;
        let source = shape
            .source_properties
            .iter()
            .find(|property| property.name.as_ref().as_utf8() == Some(name.as_str()));
        let property_type = if let Some(source) = source {
            IndexedMappedValue::Property(source.symbol)
        } else {
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(MappedTypeError::BootstrapUninitialized)?;
            let selected = shape
                .source_indexes
                .iter()
                .find(|index| {
                    index.key_type == bootstrap.number_type
                        && ts_jsnum::from_string(&name).to_string() == name
                        || template_pattern_index_matches_name(store, index.key_type, &name)
                })
                .or_else(|| {
                    shape
                        .source_indexes
                        .iter()
                        .find(|index| index.key_type == bootstrap.string_type)
                })
                .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))?;
            IndexedMappedValue::Type(selected.value_type)
        };
        values.push(property_type);
    }
    Ok(values)
}

fn type_contains_undefined_or_void(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    if record
        .flags()
        .intersects(TypeFlags::UNDEFINED | TypeFlags::VOID)
    {
        return Ok(true);
    }
    match record.data() {
        TypeData::Union(union) => union
            .union
            .types
            .iter()
            .map(|constituent| type_contains_undefined_or_void(store, *constituent))
            .try_fold(false, |found, candidate| {
                candidate.map(|candidate| found || candidate)
            }),
        _ => Ok(false),
    }
}

fn remove_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    removed: TypeId,
) -> Result<TypeId, MappedTypeError> {
    if type_ == removed {
        return store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type)
            .ok_or(MappedTypeError::BootstrapUninitialized);
    }
    let Some(TypeData::Union(union)) = store.type_payload(type_).map(TypeRecord::data) else {
        return Ok(type_);
    };
    let retained = union
        .union
        .types
        .iter()
        .copied()
        .filter(|candidate| *candidate != removed)
        .collect::<Vec<_>>();
    if retained.len() == union.union.types.len() {
        return Ok(type_);
    }
    match retained.as_slice() {
        [single] => Ok(*single),
        [] => store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type)
            .ok_or(MappedTypeError::BootstrapUninitialized),
        _ => canonical_anonymous_union(store, &retained).map_err(mapped_cache_error),
    }
}

fn set_mapped_contains_error(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), MappedTypeError> {
    let mapped = match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::Mapped(mapped)) => mapped.clone(),
        _ => return Err(MappedTypeError::InvalidMappedType(type_)),
    };
    if !store.set_mapped_type_resolution(
        type_,
        mapped.declaration,
        mapped.type_parameter,
        mapped.constraint_type,
        mapped.name_type,
        mapped.template_type,
        mapped.modifiers_type,
        mapped.resolved_apparent_type,
        true,
    ) {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    Ok(())
}

fn mapped_keyof_error(source: TypeId, error: NongenericKeyofError) -> MappedTypeError {
    match error {
        NongenericKeyofError::LiteralCache(error) => mapped_cache_error(error),
        NongenericKeyofError::InvalidType(_)
        | NongenericKeyofError::MalformedObject(_)
        | NongenericKeyofError::InvalidCachedResult(_)
        | NongenericKeyofError::CachePublication(_) => MappedTypeError::InvalidSource(source),
        NongenericKeyofError::UnsupportedObject(_)
        | NongenericKeyofError::UnsupportedPropertyName { .. }
        | NongenericKeyofError::PropertiesCacheRequired { .. } => {
            MappedTypeError::UnsupportedSource(source)
        }
    }
}

fn mapped_cache_error(error: LiteralTypeCacheError) -> MappedTypeError {
    match error {
        LiteralTypeCacheError::BootstrapUninitialized => MappedTypeError::BootstrapUninitialized,
        LiteralTypeCacheError::Capacity
        | LiteralTypeCacheError::InvalidValue
        | LiteralTypeCacheError::InvalidPreparedQuery
        | LiteralTypeCacheError::InvalidUnionAlias(_) => MappedTypeError::Capacity,
        LiteralTypeCacheError::InvalidCachedLiteral(type_)
        | LiteralTypeCacheError::InvalidCachedUnion(type_)
        | LiteralTypeCacheError::UnsupportedUnionConstituent(type_)
        | LiteralTypeCacheError::ArrayType { type_, .. } => {
            MappedTypeError::InvalidMappedType(type_)
        }
    }
}

fn mapped_instantiation_error(type_: TypeId, error: &InstantiationError) -> MappedTypeError {
    match error {
        InstantiationError::DepthLimit { depth, limit } => {
            MappedTypeError::InstantiationDepthLimit {
                depth: *depth,
                limit: *limit,
            }
        }
        InstantiationError::CountLimit { count, limit } => {
            MappedTypeError::InstantiationCountLimit {
                count: *count,
                limit: *limit,
            }
        }
        InstantiationError::Union(LiteralTypeCacheError::Capacity) => MappedTypeError::Capacity,
        _ => MappedTypeError::UnsupportedTemplate(type_),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId,
    };
    use ts_jsnum::Number;
    use ts_parser::{ParseResult, parse_source_file};

    use super::{
        MAX_TEMPLATE_UNION_SIZE, MappedTypeError, MappedTypeKey, MappedTypeKeys,
        MappedTypeModifiers, plan_mapped_type_declaration, plan_mapped_type_keys,
    };
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
        DeclaredTypeHost, IntrinsicBootstrapOptions, TypeData, TypeId,
        declared::{execute_type_parameter, type_list_key},
        instantiate::{
            InstantiationLimits, InstantiationSession, instantiate_type_with_vector_and_session,
        },
        keyof_types::{
            NongenericKeyofError, cached_nongeneric_keyof_type, plan_nongeneric_keyof_type,
            resolve_nongeneric_keyof_type,
        },
        links::TypeAliasLinks,
        object_members,
        signatures::IndexFlags,
        type_records::{LiteralValue, TypeCacheState},
        types::{AccessFlags, ObjectFlags},
    };

    fn checker_context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
        checker_context_with_intrinsics(parsed, IntrinsicBootstrapOptions::default())
    }

    fn checker_context_with_intrinsics(
        parsed: &ParseResult,
        intrinsic: IntrinsicBootstrapOptions,
    ) -> CanonicalCheckerContext<'_> {
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/mapped-unit.ts\""),
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
            CanonicalCheckerOptions {
                intrinsic,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn alias_type(
        parsed: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> TypeId {
        let file = FileId::new(0);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        context
            .store()
            .type_alias_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap()
    }

    fn source_property(
        parsed: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> SemanticSymbolId {
        let file = FileId::new(0);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let name = match &record.data {
                    NodeData::PropertyDeclaration(property) => property.name,
                    NodeData::PropertySignatureDeclaration(property) => property.name,
                    _ => return None,
                };
                let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        context.file(file).unwrap().1.symbol(declaration).unwrap()
    }

    fn cache_state(
        store: &CanonicalTypeMapperStore,
    ) -> (usize, usize, usize, usize, usize, usize, [usize; 26]) {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            bootstrap.string_literal_cache_len(),
            bootstrap.union_cache_len(),
            store.checker_link_allocated_lengths(),
        )
    }

    fn record_mapped_fixture(
        parsed: &ParseResult,
        context: &mut CanonicalCheckerContext<'_>,
    ) -> (SemanticSymbolId, TypeId, [TypeId; 2]) {
        let file = FileId::new(0);
        let (alias_node, alias_data) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::TypeAliasDeclaration(alias) => {
                    Some((NodeRef::new(parsed.arena.id(), file, node), alias))
                }
                _ => None,
            })
            .unwrap();
        let mapped_node = NodeRef::new(alias_node.arena, alias_node.file, alias_data.type_);
        let NodeData::MappedTypeNode(mapped) = &parsed.arena.get(mapped_node.node).unwrap().data
        else {
            panic!("Record must retain a mapped declaration")
        };
        let [key_node, value_node] = alias_data
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .as_slice()
        else {
            panic!("Record must declare key and value parameters")
        };
        let parameter_node =
            NodeRef::new(mapped_node.arena, mapped_node.file, mapped.type_parameter);
        let (alias, symbol, key_symbol, value_symbol, parameter_symbol) = {
            let bound = context.file(file).unwrap().1;
            (
                bound.symbol(alias_node).unwrap(),
                bound.symbol(mapped_node).unwrap(),
                bound
                    .symbol(NodeRef::new(alias_node.arena, alias_node.file, *key_node))
                    .unwrap(),
                bound
                    .symbol(NodeRef::new(alias_node.arena, alias_node.file, *value_node))
                    .unwrap(),
                bound.symbol(parameter_node).unwrap(),
            )
        };
        let store = context.store_mut_for_test();
        let key = execute_type_parameter(store, key_symbol);
        let value = execute_type_parameter(store, value_symbol);
        let parameter = execute_type_parameter(store, parameter_symbol);
        let property_keys = store.canonical_property_key_type().unwrap();
        let unknown = store.intrinsic_bootstrap().unwrap().unknown_type;
        assert!(store.set_type_parameter_resolution(key, Some(property_keys), None, None, None));
        assert!(store.set_type_parameter_resolution(parameter, Some(key), None, None, None));
        let declared = store
            .create_mapped_type(super::MappedTypeRequest::new(
                mapped_node,
                symbol,
                parameter,
                key,
                value,
                unknown,
            ))
            .unwrap();
        let parameters = [key, value];
        assert!(store.set_type_alias_links(
            alias,
            TypeAliasLinks {
                declared_type: Some(declared),
                type_parameters: Some(parameters.to_vec()),
                instantiations: Some(HashMap::from([(type_list_key(&parameters), declared)])),
                ..TypeAliasLinks::default()
            },
        ));
        (alias, declared, parameters)
    }

    fn homomorphic_mapped_fixture(
        parsed: &ParseResult,
        context: &mut CanonicalCheckerContext<'_>,
    ) -> (
        SemanticSymbolId,
        TypeId,
        [TypeId; 1],
        TypeId,
        MappedTypeModifiers,
    ) {
        let file = FileId::new(0);
        let (interface_node, alias_node, alias_data) =
            {
                let interface =
                    parsed
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::InterfaceDeclaration)
                                .then_some(NodeRef::new(parsed.arena.id(), file, node))
                        })
                        .unwrap();
                let (alias_node, alias_data) = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| match &record.data {
                        NodeData::TypeAliasDeclaration(alias) => {
                            Some((NodeRef::new(parsed.arena.id(), file, node), alias))
                        }
                        _ => None,
                    })
                    .unwrap();
                (interface, alias_node, alias_data)
            };
        let mapped_node = NodeRef::new(alias_node.arena, alias_node.file, alias_data.type_);
        let NodeData::MappedTypeNode(mapped) = &parsed.arena.get(mapped_node.node).unwrap().data
        else {
            panic!("the homomorphic alias must retain a mapped declaration")
        };
        let [outer_node] = alias_data
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .as_slice()
        else {
            panic!("the homomorphic alias must have one type parameter")
        };
        let parameter_node =
            NodeRef::new(mapped_node.arena, mapped_node.file, mapped.type_parameter);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let source_symbol = bound.symbol(interface_node).unwrap();
        let source_plan = object_members::plan_interface(context.store(), &host, source_symbol)
            .expect("the source interface must retain an authenticated member plan");
        let mapped_plan = plan_mapped_type_declaration(context.store(), &host, mapped_node)
            .expect("the mapped declaration must retain its keyof and indexed operands");
        let alias = bound.symbol(alias_node).unwrap();
        let symbol = bound.symbol(mapped_node).unwrap();
        let outer_symbol = bound
            .symbol(NodeRef::new(alias_node.arena, alias_node.file, *outer_node))
            .unwrap();
        let parameter_symbol = bound.symbol(parameter_node).unwrap();
        let store = context.store_mut_for_test();

        let source = store
            .get_declared_type_of_symbol(&host, source_symbol)
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let property_types = source_plan
            .property_type_nodes()
            .map(|node| match store.source_node_kind(node) {
                Some(SyntaxKind::StringKeyword) => string,
                Some(SyntaxKind::NumberKeyword) => number,
                other => panic!("unexpected homomorphic source property type: {other:?}"),
            })
            .collect::<Vec<_>>();
        let index_types = source_plan
            .index_type_nodes()
            .map(|(key, value)| {
                let key = match store.source_node_kind(key) {
                    Some(SyntaxKind::StringKeyword) => string,
                    Some(SyntaxKind::NumberKeyword) => number,
                    other => panic!("unexpected homomorphic source index key: {other:?}"),
                };
                let value = match store.source_node_kind(value) {
                    Some(SyntaxKind::StringKeyword) => string,
                    Some(SyntaxKind::NumberKeyword) => number,
                    other => panic!("unexpected homomorphic source index value: {other:?}"),
                };
                (key, value)
            })
            .collect::<Vec<_>>();
        let state = object_members::interface_state(store, &source_plan, source).unwrap();
        object_members::publish_declared_members(
            store,
            &source_plan,
            state,
            &property_types,
            &index_types,
            &[],
        )
        .unwrap();

        let outer = execute_type_parameter(store, outer_symbol);
        let parameter = execute_type_parameter(store, parameter_symbol);
        let constraint = store.alloc_index_type(outer, IndexFlags::NONE).unwrap();
        assert!(
            store.set_type_parameter_resolution(parameter, Some(constraint), None, None, None,)
        );
        let template = store
            .alloc_indexed_access_type(outer, parameter, AccessFlags::NONE)
            .unwrap();
        let declared = store
            .create_mapped_type(super::MappedTypeRequest::new(
                mapped_node,
                symbol,
                parameter,
                constraint,
                template,
                outer,
            ))
            .unwrap();
        let parameters = [outer];
        assert!(store.set_type_alias_links(
            alias,
            TypeAliasLinks {
                declared_type: Some(declared),
                type_parameters: Some(parameters.to_vec()),
                instantiations: Some(HashMap::from([(type_list_key(&parameters), declared)])),
                ..TypeAliasLinks::default()
            },
        ));
        (alias, declared, parameters, source, mapped_plan.modifiers())
    }

    fn direct_mapped_request_fixture(
        parsed: &ParseResult,
        context: &mut CanonicalCheckerContext<'_>,
        property_type: TypeId,
    ) -> (TypeId, TypeId, SemanticSymbolId) {
        let file = FileId::new(0);
        let source_node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let (mapped_node, parameter_node) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::MappedTypeNode(mapped) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, mapped.type_parameter),
                ))
            })
            .unwrap();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let source_symbol = bound.symbol(source_node).unwrap();
        let property = source_property(parsed, context, "value");
        let source_plan =
            object_members::plan_interface(context.store(), &host, source_symbol).unwrap();
        let store = context.store_mut_for_test();
        let source = store
            .get_declared_type_of_symbol(&host, source_symbol)
            .unwrap();
        let state = object_members::interface_state(store, &source_plan, source).unwrap();
        object_members::publish_declared_members(
            store,
            &source_plan,
            state,
            &[property_type],
            &[],
            &[],
        )
        .unwrap();
        let parameter = execute_type_parameter(store, bound.symbol(parameter_node).unwrap());
        let constraint = store.alloc_index_type(source, IndexFlags::NONE).unwrap();
        assert!(
            store.set_type_parameter_resolution(parameter, Some(constraint), None, None, None,)
        );
        let template_node = store
            .source_mapped_type_operands(mapped_node)
            .unwrap()
            .template
            .unwrap();
        let template = match store.source_node_kind(template_node) {
            Some(SyntaxKind::BooleanKeyword) => store.intrinsic_bootstrap().unwrap().boolean_type,
            Some(SyntaxKind::IndexedAccessType) => store
                .alloc_indexed_access_type(source, parameter, AccessFlags::NONE)
                .unwrap(),
            other => panic!("unexpected direct mapped template: {other:?}"),
        };
        let mapped = store
            .create_mapped_type(super::MappedTypeRequest::new(
                mapped_node,
                bound.symbol(mapped_node).unwrap(),
                parameter,
                constraint,
                template,
                source,
            ))
            .unwrap();
        assert!(!store.source_mapped_indexed_template_is_exact(template));
        (mapped, parameter, property)
    }

    fn replace_mapped_name(store: &mut CanonicalTypeMapperStore, mapped: TypeId, name: TypeId) {
        let TypeData::Mapped(record) = store.type_payload(mapped).unwrap().data() else {
            panic!("expected a mapped type");
        };
        let record = record.clone();
        assert!(store.set_mapped_type_resolution(
            mapped,
            record.declaration,
            record.type_parameter,
            record.constraint_type,
            Some(name),
            record.template_type,
            record.modifiers_type,
            record.resolved_apparent_type,
            record.contains_error,
        ));
    }

    #[test]
    fn mapped_modifier_bits_match_upstream() {
        assert_eq!(MappedTypeModifiers::INCLUDE_READONLY.bits(), 1);
        assert_eq!(MappedTypeModifiers::EXCLUDE_READONLY.bits(), 2);
        assert_eq!(MappedTypeModifiers::INCLUDE_OPTIONAL.bits(), 4);
        assert_eq!(MappedTypeModifiers::EXCLUDE_OPTIONAL.bits(), 8);
        assert_eq!(
            MappedTypeModifiers::from_token_kinds(
                Some(SyntaxKind::ReadonlyKeyword),
                Some(SyntaxKind::QuestionToken),
            ),
            Some(MappedTypeModifiers::INCLUDE_READONLY | MappedTypeModifiers::INCLUDE_OPTIONAL),
        );
        assert_eq!(
            MappedTypeModifiers::from_token_kinds(
                Some(SyntaxKind::MinusToken),
                Some(SyntaxKind::MinusToken),
            ),
            Some(MappedTypeModifiers::EXCLUDE_READONLY | MappedTypeModifiers::EXCLUDE_OPTIONAL),
        );
        assert!(
            !(MappedTypeModifiers::INCLUDE_OPTIONAL | MappedTypeModifiers::EXCLUDE_OPTIONAL)
                .valid()
        );
    }

    #[test]
    fn source_mapped_declaration_planner_retains_every_routing_operand() {
        let parsed = parse_source_file(
            "interface Shape { value: string }\n\
             type Result = { -readonly [P in keyof Shape]-?: Shape[P] };",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/mapped-plan.ts\""),
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
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::MappedType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        let plan = plan_mapped_type_declaration(&store, &host, node).unwrap();
        assert_eq!(plan.node(), node);
        assert_eq!(plan.symbol(), bound.symbol(node).unwrap());
        let NodeData::MappedTypeNode(mapped) = &parsed.arena.get(node.node).unwrap().data else {
            unreachable!()
        };
        let parameter = NodeRef::new(node.arena, node.file, mapped.type_parameter);
        assert_eq!(
            plan.type_parameter_symbol(),
            bound.symbol(parameter).unwrap(),
        );
        assert_eq!(
            parsed.arena.get(plan.constraint().node).unwrap().kind,
            SyntaxKind::TypeOperator,
        );
        assert_eq!(
            parsed
                .arena
                .get(plan.modifiers_source().unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::TypeReference,
        );
        assert_eq!(
            parsed
                .arena
                .get(plan.template().unwrap().node)
                .unwrap()
                .kind,
            SyntaxKind::IndexedAccessType,
        );
        assert_eq!(plan.name_type(), None);
        assert_eq!(
            plan.modifiers(),
            MappedTypeModifiers::EXCLUDE_READONLY | MappedTypeModifiers::EXCLUDE_OPTIONAL,
        );
    }

    #[test]
    fn homomorphic_aliases_preserve_keyof_origins_and_mapped_property_modifiers() {
        for (alias, expected_modifiers, fixed_readonly, fixed_optional, optional_optional) in [
            (
                "type InferPropsInner<T> = { [K in keyof T]: T[K] };",
                MappedTypeModifiers::NONE,
                true,
                false,
                true,
            ),
            (
                "type ValidationMap<T> = { [K in keyof T]-?: T[K] };",
                MappedTypeModifiers::EXCLUDE_OPTIONAL,
                true,
                false,
                false,
            ),
            (
                "type WeakValidationMap<T> = { [K in keyof T]?: T[K] };",
                MappedTypeModifiers::INCLUDE_OPTIONAL,
                true,
                true,
                true,
            ),
            (
                "type MutableValidationMap<T> = { -readonly [K in keyof T]-?: T[K] };",
                MappedTypeModifiers::EXCLUDE_READONLY | MappedTypeModifiers::EXCLUDE_OPTIONAL,
                false,
                false,
                false,
            ),
        ] {
            let source = format!(
                "interface Shape {{ readonly fixed: string; optional?: number }}\n{alias}\n",
            );
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = checker_context(&parsed);
            let fixed_source = source_property(&parsed, &context, "fixed");
            let optional_source = source_property(&parsed, &context, "optional");
            let (symbol, declared, parameters, argument, modifiers) =
                homomorphic_mapped_fixture(&parsed, &mut context);
            assert_eq!(modifiers, expected_modifiers);
            let store = context.store_mut_for_test();
            let identity_state = (cache_state(store), store.properties_type_cache_len());
            assert_eq!(
                store.instantiate_homomorphic_mapped_alias(
                    symbol,
                    declared,
                    &parameters,
                    &parameters,
                    modifiers,
                ),
                Ok(declared),
            );
            assert_eq!(
                (cache_state(store), store.properties_type_cache_len()),
                identity_state,
            );

            let instantiated = store
                .instantiate_homomorphic_mapped_alias(
                    symbol,
                    declared,
                    &parameters,
                    &[argument],
                    modifiers,
                )
                .unwrap();
            let key_plan = plan_nongeneric_keyof_type(store, argument).unwrap();
            let keys = cached_nongeneric_keyof_type(store, &key_plan)
                .unwrap()
                .unwrap();
            let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
                panic!("the homomorphic instantiation must remain a mapped object")
            };
            assert_eq!(mapped.object.target, Some(declared));
            assert_eq!(mapped.constraint_type, Some(keys));
            assert_eq!(mapped.modifiers_type, Some(argument));

            let members = store
                .resolve_mapped_type_members(instantiated, modifiers)
                .unwrap();
            assert_eq!(members.properties().len(), 2);
            let table = store.symbol_table(members.members()).unwrap();
            let fixed = table.get_source("fixed").unwrap();
            let optional = table.get_source("optional").unwrap();
            assert_eq!(
                store.mapped_symbol_links(fixed).unwrap().synthetic_origin,
                Some(fixed_source),
            );
            assert_eq!(
                store
                    .mapped_symbol_links(optional)
                    .unwrap()
                    .synthetic_origin,
                Some(optional_source),
            );
            assert_eq!(
                store.symbol(fixed).unwrap().declarations(),
                store.symbol(fixed_source).unwrap().declarations(),
            );
            assert!(
                store
                    .value_symbol_links(fixed)
                    .unwrap()
                    .resolved_type
                    .is_none()
            );
            assert!(
                store
                    .value_symbol_links(optional)
                    .unwrap()
                    .resolved_type
                    .is_none()
            );

            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let fixed = store
                .resolve_mapped_type_property(instantiated, "fixed", modifiers)
                .unwrap()
                .unwrap();
            assert_eq!(fixed.type_id(), string);
            assert_eq!(fixed.is_readonly(), fixed_readonly);
            assert_eq!(fixed.is_optional(), fixed_optional);
            let optional = store
                .resolve_mapped_type_property(instantiated, "optional", modifiers)
                .unwrap()
                .unwrap();
            assert_eq!(optional.type_id(), number);
            assert_eq!(optional.is_optional(), optional_optional);

            let warm = (cache_state(store), store.properties_type_cache_len());
            assert_eq!(
                store.validate_homomorphic_mapped_alias_instantiation(
                    symbol,
                    declared,
                    &parameters,
                    &[argument],
                    instantiated,
                    modifiers,
                ),
                Ok(()),
            );
            assert_eq!(
                store.resolve_mapped_type_members(instantiated, modifiers),
                Ok(members),
            );
            assert_eq!(
                (cache_state(store), store.properties_type_cache_len()),
                warm,
            );
        }
    }

    #[test]
    fn homomorphic_aliases_preserve_index_values_and_remove_readonly() {
        let parsed = parse_source_file(concat!(
            "interface Shape { readonly fixed: number; readonly [name: string]: number }\n",
            "type ValidationMap<T> = { -readonly [K in keyof T]-?: T[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters, source, modifiers) =
            homomorphic_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let instantiated = store
            .instantiate_homomorphic_mapped_alias(
                alias,
                declared,
                &parameters,
                &[source],
                modifiers,
            )
            .unwrap();
        let members = store
            .resolve_mapped_type_members(instantiated, modifiers)
            .unwrap();
        assert_eq!(members.properties().len(), 1);
        let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
            unreachable!()
        };
        let [index] = mapped.object.structured.index_infos.as_deref().unwrap() else {
            panic!("the source string index must remain on the mapped result")
        };
        let index = store.index_info(*index).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(index.key_type(), bootstrap.string_type);
        assert_eq!(index.value_type(), bootstrap.number_type);
        assert!(!index.is_readonly());

        let property = store
            .resolve_mapped_type_property(instantiated, "fixed", modifiers)
            .unwrap()
            .unwrap();
        assert!(!property.is_readonly());
        assert_eq!(
            property.type_id(),
            store.intrinsic_bootstrap().unwrap().number_type,
        );
        assert_eq!(
            store.validate_homomorphic_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &[source],
                instantiated,
                modifiers,
            ),
            Ok(()),
        );
    }

    #[test]
    fn homomorphic_aliases_reject_invalid_sources_and_poisoned_clones_without_writes() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "type ValidationMap<T> = { [K in keyof T]-?: T[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters, source, modifiers) =
            homomorphic_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let before = (cache_state(store), store.properties_type_cache_len());
        assert_eq!(
            store.instantiate_homomorphic_mapped_alias(
                alias,
                declared,
                &parameters,
                &[number],
                modifiers,
            ),
            Err(MappedTypeError::UnsupportedSource(number)),
        );
        assert_eq!(
            store.instantiate_homomorphic_mapped_alias(
                alias,
                declared,
                &parameters,
                &[source],
                MappedTypeModifiers::INCLUDE_OPTIONAL | MappedTypeModifiers::EXCLUDE_OPTIONAL,
            ),
            Err(MappedTypeError::InvalidModifiers),
        );
        assert_eq!(
            (cache_state(store), store.properties_type_cache_len()),
            before,
        );

        let instantiated = store
            .instantiate_homomorphic_mapped_alias(
                alias,
                declared,
                &parameters,
                &[source],
                modifiers,
            )
            .unwrap();
        let parameter = match store.type_payload(instantiated).unwrap().data() {
            TypeData::Mapped(mapped) => mapped.type_parameter.unwrap(),
            _ => unreachable!(),
        };
        let (target, mapper) = match store.type_payload(parameter).unwrap().data() {
            TypeData::TypeParameter(parameter) => {
                (parameter.target.unwrap(), parameter.mapper.unwrap())
            }
            _ => unreachable!(),
        };
        assert!(store.set_type_parameter_resolution(
            parameter,
            Some(number),
            Some(target),
            Some(mapper),
            None,
        ));
        let poisoned = (cache_state(store), store.properties_type_cache_len());
        assert_eq!(
            store.validate_homomorphic_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &[source],
                instantiated,
                modifiers,
            ),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(
            store.resolve_mapped_type_members(instantiated, modifiers),
            Err(MappedTypeError::InvalidTypeParameter(parameter)),
        );
        assert_eq!(
            (cache_state(store), store.properties_type_cache_len()),
            poisoned,
        );
    }

    #[test]
    fn conflicting_mapped_modifiers_reject_without_writes_before_and_after_members() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: void } ",
            "type Constant = { [P in keyof Shape]: boolean };",
        ));
        let mut context = checker_context(&parsed);
        let void = context.store().intrinsic_bootstrap().unwrap().void_type;
        let (mapped, _, _) = direct_mapped_request_fixture(&parsed, &mut context, void);
        let store = context.store_mut_for_test();
        let cold = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::INCLUDE_OPTIONAL),
            Err(MappedTypeError::InvalidModifiers),
        );
        assert_eq!(cache_state(store), cold);
        let members = store
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
            .unwrap();
        let [property] = members.properties() else {
            panic!("the direct request must have one property")
        };
        let warm = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::INCLUDE_OPTIONAL),
            Err(MappedTypeError::InvalidCachedProperty(*property)),
        );
        assert_eq!(cache_state(store), warm);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE),
            Ok(members),
        );
        assert_eq!(cache_state(store), warm);

        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let key = store
            .regular_string_literal_type("value".to_owned())
            .unwrap();
        let value = store.intrinsic_bootstrap().unwrap().number_type;
        let mapped = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &[key, value])
            .unwrap();
        let cold = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::INCLUDE_OPTIONAL),
            Err(MappedTypeError::InvalidModifiers),
        );
        assert_eq!(cache_state(store), cold);

        let members = store
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
            .unwrap();
        let warm = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::INCLUDE_OPTIONAL),
            Err(MappedTypeError::InvalidModifiers),
        );
        assert_eq!(cache_state(store), warm);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE),
            Ok(members),
        );
        assert_eq!(cache_state(store), warm);
    }

    #[test]
    fn direct_optional_requests_preserve_void_and_warm_identity() {
        for (strict, exact) in [(false, false), (true, false), (true, true)] {
            let parsed = parse_source_file(concat!(
                "interface Shape { value: void } ",
                "type Soft = { [P in keyof Shape]?: Shape[P] };",
            ));
            let mut context = checker_context_with_intrinsics(
                &parsed,
                IntrinsicBootstrapOptions {
                    strict_null_checks: strict,
                    exact_optional_property_types: exact,
                },
            );
            let void = context.store().intrinsic_bootstrap().unwrap().void_type;
            let (mapped, _, source) = direct_mapped_request_fixture(&parsed, &mut context, void);
            let store = context.store_mut_for_test();
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let members = store
                .resolve_mapped_type_members_with_session(
                    mapped,
                    MappedTypeModifiers::INCLUDE_OPTIONAL,
                    &mut session,
                )
                .unwrap();
            let [symbol] = members.properties() else {
                panic!("the direct request must keep one property")
            };
            assert_eq!(session.query_count(), 0);
            let value = store
                .resolve_mapped_symbol_type_with_session(*symbol, &mut session)
                .unwrap();
            assert_eq!(session.query_count(), if strict { 3 } else { 0 });
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            if strict {
                let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
                    panic!("an explicit optional void value must keep its sentinel")
                };
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&bootstrap.void_type));
                assert!(
                    union
                        .union
                        .types
                        .contains(&bootstrap.undefined_or_missing_type)
                );
            } else {
                assert_eq!(value, bootstrap.void_type);
            }
            assert_eq!(
                store.value_symbol_links(source).unwrap().resolved_type,
                Some(bootstrap.void_type),
            );
            let warm = cache_state(store);
            let count = session.query_count();
            assert_eq!(
                store.resolve_mapped_symbol_type_with_session(*symbol, &mut session),
                Ok(value),
            );
            let property = store
                .resolve_mapped_type_property(
                    mapped,
                    "value",
                    MappedTypeModifiers::INCLUDE_OPTIONAL,
                )
                .unwrap()
                .unwrap();
            assert_eq!(property.type_id(), value);
            assert!(property.is_optional());
            assert_eq!(session.query_count(), count);
            assert_eq!(cache_state(store), warm);
        }
    }

    #[test]
    fn direct_optional_requests_reuse_raw_optional_value_identities() {
        for exact in [false, true] {
            for raw_union in [false, true] {
                let annotation = if raw_union { "number" } else { "never" };
                let parsed = parse_source_file(&format!(
                    "interface Shape {{ value?: {annotation} }} \
                     type Soft = {{ [P in keyof Shape]?: Shape[P] }};",
                ));
                let mut context = checker_context_with_intrinsics(
                    &parsed,
                    IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        exact_optional_property_types: exact,
                    },
                );
                let store = context.store_mut_for_test();
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                let (sentinel, number) =
                    (bootstrap.undefined_or_missing_type, bootstrap.number_type);
                let value = if raw_union {
                    store
                        .alloc_union_type(ObjectFlags::NONE, vec![sentinel, number])
                        .unwrap()
                } else {
                    sentinel
                };
                let (mapped, _, source) =
                    direct_mapped_request_fixture(&parsed, &mut context, value);
                let store = context.store_mut_for_test();
                let mut session = InstantiationSession::new(InstantiationLimits::default());
                let members = store
                    .resolve_mapped_type_members_with_session(
                        mapped,
                        MappedTypeModifiers::INCLUDE_OPTIONAL,
                        &mut session,
                    )
                    .unwrap();
                let [symbol] = members.properties() else {
                    panic!("the direct request must keep one property")
                };
                let cold = cache_state(store);
                assert_eq!(session.query_count(), 0);
                assert_eq!(
                    store.resolve_mapped_symbol_type_with_session(*symbol, &mut session),
                    Ok(value),
                );
                assert_eq!(session.query_count(), 3);
                assert_eq!(cache_state(store), cold);
                assert_eq!(
                    store.value_symbol_links(source).unwrap().resolved_type,
                    Some(value)
                );
                if raw_union {
                    assert_eq!(
                        store.type_payload(value).unwrap().object_flags(),
                        ObjectFlags::NONE
                    );
                    assert!(store.validate_union_constituent(value).is_err());
                }
                assert_eq!(
                    store.resolve_mapped_symbol_type_with_session(*symbol, &mut session),
                    Ok(value),
                );
                let property = store
                    .resolve_mapped_type_property(
                        mapped,
                        "value",
                        MappedTypeModifiers::INCLUDE_OPTIONAL,
                    )
                    .unwrap()
                    .unwrap();
                assert_eq!(property.type_id(), value);
                assert!(property.is_optional());
                assert_eq!(session.query_count(), 3);
                assert_eq!(cache_state(store), cold);
            }
        }
    }

    #[test]
    fn direct_optional_requests_preserve_caller_limits_and_recovery() {
        for recovering in [false, true] {
            let parsed = parse_source_file(concat!(
                "interface Shape { value: void } ",
                "type Soft = { [P in keyof Shape]?: Shape[P] };",
            ));
            let mut context = checker_context_with_intrinsics(
                &parsed,
                IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
            );
            let void = context.store().intrinsic_bootstrap().unwrap().void_type;
            let (mapped, parameter, source) =
                direct_mapped_request_fixture(&parsed, &mut context, void);
            let store = context.store_mut_for_test();
            let members = store
                .resolve_mapped_type_members(mapped, MappedTypeModifiers::INCLUDE_OPTIONAL)
                .unwrap();
            let [symbol] = members.properties() else {
                panic!("the direct request must keep one property")
            };
            let key = store
                .mapped_symbol_links(*symbol)
                .unwrap()
                .key_type
                .unwrap();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (error, void) = (bootstrap.error_type, bootstrap.void_type);
            let limits = InstantiationLimits {
                max_depth: 100,
                max_count: 3,
            };
            let mut session = if recovering {
                InstantiationSession::new_recovering(store, limits, error).unwrap()
            } else {
                InstantiationSession::new(limits)
            };
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    parameter,
                    &[parameter],
                    &[key],
                    None,
                    &mut session,
                ),
                Ok(key),
            );
            assert_eq!(session.query_count(), 1);
            let mark = session.limit_event_mark();
            let before = cache_state(store);
            let result = store.resolve_mapped_symbol_type_with_session(*symbol, &mut session);
            assert_eq!(session.query_count(), 3);
            assert!(session.limit_event_occurred_since(mark));
            assert_eq!(
                store.value_symbol_links(source).unwrap().resolved_type,
                Some(void)
            );
            if recovering {
                assert_eq!(result, Ok(error));
                assert!(store.mapped_property_recovery(*symbol).is_some());
                let warm = cache_state(store);
                let mark = session.limit_event_mark();
                assert_eq!(
                    store.resolve_mapped_symbol_type_with_session(*symbol, &mut session),
                    Ok(error),
                );
                assert_eq!(session.query_count(), 3);
                assert!(!session.limit_event_occurred_since(mark));
                assert_eq!(cache_state(store), warm);
            } else {
                assert_eq!(
                    result,
                    Err(MappedTypeError::InstantiationCountLimit { count: 3, limit: 3 }),
                );
                assert_eq!(
                    store.value_symbol_links(*symbol).unwrap().resolved_type,
                    None
                );
                assert!(store.mapped_property_recovery(*symbol).is_none());
                assert_eq!(cache_state(store), before);
            }
        }
    }

    #[test]
    fn record_alias_instantiation_preserves_parameter_mapper_and_string_index() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let before = (store.type_len(), store.mapper_len());

        assert_eq!(
            store.instantiate_record_mapped_alias(alias, declared, &parameters, &parameters),
            Ok(declared),
        );
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &parameters,
                declared,
            ),
            Ok(()),
        );
        assert_eq!((store.type_len(), store.mapper_len()), before);

        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &arguments)
            .unwrap();
        assert_eq!(
            (store.type_len(), store.mapper_len()),
            (before.0 + 2, before.1 + 3),
        );
        store
            .validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &arguments,
                instantiated,
            )
            .unwrap();
        let (original_parameter, parameter, instantiation_mapper) = {
            let TypeData::Mapped(original) = store.type_payload(declared).unwrap().data() else {
                unreachable!()
            };
            let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
                unreachable!()
            };
            assert_eq!(mapped.object.target, Some(declared));
            assert_eq!(mapped.constraint_type, Some(arguments[0]));
            assert_eq!(mapped.template_type, Some(arguments[1]));
            (
                original.type_parameter.unwrap(),
                mapped.type_parameter.unwrap(),
                mapped.object.mapper.unwrap(),
            )
        };
        let TypeData::TypeParameter(cloned) = store.type_payload(parameter).unwrap().data() else {
            unreachable!()
        };
        assert_eq!(cloned.target, Some(original_parameter));
        assert_eq!(cloned.mapper, Some(instantiation_mapper));
        assert_eq!(cloned.constraint, Some(arguments[0]));

        let members = store
            .resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE)
            .unwrap();
        assert!(members.properties().is_empty());
        let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
            unreachable!()
        };
        let [index] = mapped.object.structured.index_infos.as_deref().unwrap() else {
            panic!("Record<string, number> must publish one string index")
        };
        let index = store.index_info(*index).unwrap();
        assert_eq!(index.key_type(), arguments[0]);
        assert_eq!(index.value_type(), arguments[1]);
        assert!(index.declaration().is_none());
        assert!(index.index_symbol().is_none());
        assert!(index.components().is_empty());

        let warm = (cache_state(store), store.index_info_len());
        store
            .validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &arguments,
                instantiated,
            )
            .unwrap();
        assert_eq!(
            store.resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE),
            Ok(members),
        );
        assert_eq!((cache_state(store), store.index_info_len()), warm);
    }

    #[test]
    fn record_alias_broad_property_keys_publish_exact_index_signatures() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let (string, number, symbol, any, never, property_keys) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.es_symbol_type,
                bootstrap.any_type,
                bootstrap.never_type,
                bootstrap.string_number_symbol_type,
            )
        };
        let value = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();

        for (key, mut expected_keys) in [
            (string, vec![string]),
            (number, vec![number]),
            (symbol, vec![symbol]),
            (any, vec![string]),
            (never, Vec::new()),
            (property_keys, vec![string, number, symbol]),
        ] {
            expected_keys.sort_unstable();
            let instantiated = store
                .instantiate_record_mapped_alias(alias, declared, &parameters, &[key, value])
                .unwrap();
            let members = store
                .resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE)
                .unwrap();
            assert!(members.properties().is_empty());

            let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
                unreachable!()
            };
            let indexes = mapped
                .object
                .structured
                .index_infos
                .as_deref()
                .unwrap_or_default();
            assert_eq!(indexes.len(), expected_keys.len());
            for (index, expected_key) in indexes.iter().zip(expected_keys) {
                let info = store.index_info(*index).unwrap();
                assert_eq!(info.key_type(), expected_key);
                assert_eq!(info.value_type(), value);
                assert!(!info.is_readonly());
                assert!(info.declaration().is_none());
                assert!(info.index_symbol().is_none());
                assert!(info.components().is_empty());
            }

            let warm = (cache_state(store), store.index_info_len());
            assert_eq!(
                store.resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE),
                Ok(members),
            );
            assert_eq!((cache_state(store), store.index_info_len()), warm);
        }
    }

    #[test]
    fn record_alias_finite_keys_preserve_literal_and_unique_symbol_identity() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let text = store
            .regular_string_literal_type("ready".to_owned())
            .unwrap();
        let number = store.regular_number_literal_type(Number::new(7.0)).unwrap();
        let unique = store.alloc_unique_es_symbol_type(alias).unwrap();
        let keys = store
            .alloc_union_type(ObjectFlags::NONE, vec![text, number, unique])
            .unwrap();
        let value = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &[keys, value])
            .unwrap();
        let before_mappers = store.mapper_len();

        let members = store
            .resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE)
            .unwrap();
        assert_eq!(members.properties().len(), 3);
        let table = store.symbol_table(members.members()).unwrap();
        assert!(table.get_source("ready").is_some());
        assert!(table.get_source("7").is_some());
        let TypeData::UniqueEsSymbol(unique_record) = store.type_payload(unique).unwrap().data()
        else {
            unreachable!()
        };
        assert!(table.get(unique_record.name.as_ref()).is_some());

        for property in members.properties() {
            let key = store
                .mapped_symbol_links(*property)
                .and_then(|links| links.key_type)
                .unwrap();
            assert!([text, number, unique].contains(&key));
            assert_eq!(
                store
                    .value_symbol_links(*property)
                    .and_then(|links| links.name_type),
                Some(key),
            );
            assert_eq!(store.resolve_mapped_symbol_type(*property), Ok(value));
        }
        assert_eq!(store.mapper_len(), before_mappers);
        let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
            unreachable!()
        };
        assert!(mapped.object.structured.index_infos.is_none());

        let warm = (cache_state(store), store.index_info_len());
        assert_eq!(
            store.resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE),
            Ok(members),
        );
        assert_eq!((cache_state(store), store.index_info_len()), warm);
    }

    #[test]
    fn finite_record_projection_preserves_owner_identity_and_replays_without_writes() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let first = store
            .regular_string_literal_type("i\u{307}spanyol".to_owned())
            .unwrap();
        let second = store
            .regular_string_literal_type("\u{3bf}\u{3c2}".to_owned())
            .unwrap();
        let keys = store
            .alloc_union_type(ObjectFlags::NONE, vec![first, second])
            .unwrap();
        let value = store.intrinsic_bootstrap().unwrap().string_type;
        let arguments = [keys, value];
        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &arguments)
            .unwrap();
        let identity = store.alloc_type_alias(Some(alias)).unwrap();
        assert!(store.set_type_alias_arguments(identity, Some(arguments.to_vec())));
        assert!(store.set_type_alias(instantiated, Some(identity)));

        let cold = cache_state(store);
        assert_eq!(
            store.finite_record_mapped_projection(instantiated),
            Err(MappedTypeError::InvalidCachedMembers(instantiated)),
        );
        assert_eq!(cache_state(store), cold);

        let projection = store
            .resolve_finite_record_mapped_projection(instantiated)
            .unwrap();
        assert_eq!(projection.type_, instantiated);
        assert_eq!(
            store.source_node_kind(projection.declaration),
            Some(SyntaxKind::MappedType),
        );
        assert_eq!(projection.properties.len(), 2);
        for property in &projection.properties {
            assert_eq!(property.type_, value);
            assert!(!property.optional);
            assert!(!property.readonly);
            assert_eq!(
                store
                    .symbol_table(projection.members)
                    .and_then(|members| members.get(property.name.as_ref())),
                Some(property.symbol),
            );
            let links = store.value_symbol_links(property.symbol).unwrap();
            assert_eq!(links.containing_type, Some(instantiated));
            assert_eq!(links.resolved_type, Some(value));
            assert_eq!(
                links.name_type,
                store
                    .mapped_symbol_links(property.symbol)
                    .and_then(|links| links.key_type),
            );
        }

        let warm = cache_state(store);
        assert_eq!(
            store.finite_record_mapped_projection(instantiated),
            Ok(projection.clone()),
        );
        assert_eq!(
            store.resolve_finite_record_mapped_projection(instantiated),
            Ok(projection),
        );
        assert_eq!(cache_state(store), warm);
    }

    #[test]
    fn finite_record_projection_rejects_broad_and_indexed_key_domains_without_writes() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let (string, number, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
            )
        };
        let literal = store
            .regular_string_literal_type("fixed".to_owned())
            .unwrap();
        let mixed = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, literal])
            .unwrap();

        for key in [string, number, never, mixed] {
            let arguments = [key, number];
            let instantiated = store
                .instantiate_record_mapped_alias(alias, declared, &parameters, &arguments)
                .unwrap();
            let identity = store.alloc_type_alias(Some(alias)).unwrap();
            assert!(store.set_type_alias_arguments(identity, Some(arguments.to_vec())));
            assert!(store.set_type_alias(instantiated, Some(identity)));
            let cold = cache_state(store);

            assert_eq!(
                store.finite_record_mapped_projection(instantiated),
                Err(MappedTypeError::UnsupportedConstraint(key)),
            );
            assert_eq!(
                store.resolve_finite_record_mapped_projection(instantiated),
                Err(MappedTypeError::UnsupportedConstraint(key)),
            );
            assert_eq!(cache_state(store), cold);
        }
    }

    #[test]
    fn finite_record_projection_rejects_forged_property_value_and_owner_caches() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let key = store
            .regular_string_literal_type("ready".to_owned())
            .unwrap();
        let (value, wrong_value) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let arguments = [key, value];
        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &arguments)
            .unwrap();
        let identity = store.alloc_type_alias(Some(alias)).unwrap();
        assert!(store.set_type_alias_arguments(identity, Some(arguments.to_vec())));
        assert!(store.set_type_alias(instantiated, Some(identity)));
        let projection = store
            .resolve_finite_record_mapped_projection(instantiated)
            .unwrap();
        let [property] = projection.properties.as_slice() else {
            panic!("expected one finite mapped Record property")
        };
        let original = store.value_symbol_links(property.symbol).unwrap().clone();

        for (containing_type, resolved_type) in [
            (Some(instantiated), Some(wrong_value)),
            (Some(declared), Some(value)),
        ] {
            let mut poisoned = original.clone();
            poisoned.containing_type = containing_type;
            poisoned.resolved_type = resolved_type;
            assert!(store.set_value_symbol_links(property.symbol, poisoned));
            let state = cache_state(store);
            assert!(matches!(
                store.finite_record_mapped_projection(instantiated),
                Err(MappedTypeError::InvalidCachedProperty(_)
                    | MappedTypeError::InvalidMappedType(_))
            ));
            assert!(matches!(
                store.resolve_finite_record_mapped_projection(instantiated),
                Err(MappedTypeError::InvalidCachedProperty(_)
                    | MappedTypeError::InvalidMappedType(_))
            ));
            assert_eq!(cache_state(store), state);
            assert!(store.set_value_symbol_links(property.symbol, original.clone()));
        }

        assert!(store.set_type_alias_arguments(identity, Some(vec![value, key])));
        let state = cache_state(store);
        assert_eq!(
            store.finite_record_mapped_projection(instantiated),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(
            store.resolve_finite_record_mapped_projection(instantiated),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(cache_state(store), state);
    }

    #[test]
    fn record_alias_mixed_keys_preserve_literal_properties_and_indexes() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let (string, value) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let number = store.regular_number_literal_type(Number::new(3.0)).unwrap();
        let unique = store.alloc_unique_es_symbol_type(alias).unwrap();
        let keys = store
            .alloc_union_type(ObjectFlags::NONE, vec![string, number, unique])
            .unwrap();
        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &[keys, value])
            .unwrap();

        let members = store
            .resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE)
            .unwrap();
        assert_eq!(members.properties().len(), 2);
        assert!(
            store
                .symbol_table(members.members())
                .unwrap()
                .get_source("3")
                .is_some()
        );
        let TypeData::Mapped(mapped) = store.type_payload(instantiated).unwrap().data() else {
            unreachable!()
        };
        let [index] = mapped.object.structured.index_infos.as_deref().unwrap() else {
            panic!("mixed Record keys must preserve their string index")
        };
        let info = store.index_info(*index).unwrap();
        assert_eq!(info.key_type(), string);
        assert_eq!(info.value_type(), value);

        let warm = (cache_state(store), store.index_info_len());
        assert_eq!(
            store.resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE),
            Ok(members),
        );
        assert_eq!((cache_state(store), store.index_info_len()), warm);
    }

    #[test]
    fn record_alias_instantiation_rejects_invalid_arguments_and_poisoned_clones() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean, bigint, unknown) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
            bootstrap.bigint_type,
            bootstrap.unknown_type,
        );
        let before = cache_state(store);
        for invalid in [boolean, bigint, unknown] {
            assert_eq!(
                store.instantiate_record_mapped_alias(
                    alias,
                    declared,
                    &parameters,
                    &[invalid, number],
                ),
                Err(MappedTypeError::UnsupportedConstraint(invalid)),
            );
        }
        assert_eq!(
            store.instantiate_record_mapped_alias(
                alias,
                declared,
                &[parameters[1], parameters[0]],
                &[string, number],
            ),
            Err(MappedTypeError::InvalidSymbol(alias)),
        );
        assert_eq!(cache_state(store), before);

        let unresolved = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &[parameters[0], number])
            .unwrap();
        let before_members = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(unresolved, MappedTypeModifiers::NONE),
            Err(MappedTypeError::UnsupportedConstraint(parameters[0])),
        );
        assert_eq!(cache_state(store), before_members);

        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &[string, number])
            .unwrap();
        let parameter = match store.type_payload(instantiated).unwrap().data() {
            TypeData::Mapped(mapped) => mapped.type_parameter.unwrap(),
            _ => unreachable!(),
        };
        let (original, mapper) = match store.type_payload(parameter).unwrap().data() {
            TypeData::TypeParameter(parameter) => {
                (parameter.target.unwrap(), parameter.mapper.unwrap())
            }
            _ => unreachable!(),
        };
        for (constraint, target, clone_mapper, default) in [
            (Some(number), Some(original), Some(mapper), None),
            (Some(string), Some(parameters[0]), Some(mapper), None),
            (Some(string), Some(original), None, None),
            (Some(string), Some(original), Some(mapper), Some(number)),
        ] {
            assert!(store.set_type_parameter_resolution(
                parameter,
                constraint,
                target,
                clone_mapper,
                default,
            ));
            let poisoned = cache_state(store);
            assert_eq!(
                store.validate_record_mapped_alias_instantiation(
                    alias,
                    declared,
                    &parameters,
                    &[string, number],
                    instantiated,
                ),
                Err(MappedTypeError::InvalidMappedType(instantiated)),
            );
            assert_eq!(
                store.resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE),
                Err(MappedTypeError::InvalidTypeParameter(parameter)),
            );
            assert_eq!(cache_state(store), poisoned);
        }

        assert!(store.set_type_parameter_resolution(
            parameter,
            Some(string),
            Some(original),
            Some(mapper),
            None,
        ));
        assert!(store.set_type_object_flags(
            parameter,
            ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES,
        ));
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &[string, number],
                instantiated,
            ),
            Ok(()),
        );

        assert!(store.set_object_instantiations(
            instantiated,
            TypeCacheState::Allocated(HashMap::new()),
        ));
        let poisoned = cache_state(store);
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &[string, number],
                instantiated,
            ),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(cache_state(store), poisoned);
        assert!(store.set_object_instantiations(instantiated, TypeCacheState::Unallocated));

        assert!(store.add_type_object_flags(instantiated, ObjectFlags::FROM_TYPE_NODE));
        let poisoned = cache_state(store);
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &[string, number],
                instantiated,
            ),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(cache_state(store), poisoned);
    }

    #[test]
    fn record_alias_rejects_non_record_names_and_invalid_identity_caches() {
        let non_record =
            parse_source_file("type Lookup<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(
            non_record.diagnostics.is_empty(),
            "{:?}",
            non_record.diagnostics
        );
        let mut context = checker_context(&non_record);
        let (alias, declared, parameters) = record_mapped_fixture(&non_record, &mut context);
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let before = cache_state(store);
        assert_eq!(
            store.instantiate_record_mapped_alias(alias, declared, &parameters, &arguments),
            Err(MappedTypeError::InvalidSymbol(alias)),
        );
        assert_eq!(cache_state(store), before);

        for corruption in 0..3 {
            let parsed =
                parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = checker_context(&parsed);
            let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
            let store = context.store_mut_for_test();
            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let mut links = store.type_alias_links(alias).unwrap().clone();
            match corruption {
                0 => links.instantiations = None,
                1 => links.instantiations = Some(HashMap::new()),
                2 => {
                    links.instantiations =
                        Some(HashMap::from([(type_list_key(&parameters), string)]));
                }
                _ => unreachable!(),
            }
            assert!(store.set_type_alias_links(alias, links));
            let before = cache_state(store);
            assert_eq!(
                store.instantiate_record_mapped_alias(
                    alias,
                    declared,
                    &parameters,
                    &[string, number],
                ),
                Err(MappedTypeError::InvalidSymbol(alias)),
            );
            assert_eq!(cache_state(store), before);
        }
    }

    #[test]
    fn record_alias_rejects_invalid_key_parameter_constraints() {
        let parsed = parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let store = context.store_mut_for_test();
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        assert!(
            store.set_type_parameter_resolution(parameters[0], Some(string), None, None, None,)
        );
        let before = cache_state(store);
        assert_eq!(
            store.instantiate_record_mapped_alias(alias, declared, &parameters, &[string, number],),
            Err(MappedTypeError::InvalidTypeParameter(parameters[0])),
        );
        assert_eq!(cache_state(store), before);
    }

    #[test]
    fn record_alias_metadata_must_retain_its_exact_symbol_and_arguments() {
        let parsed = parse_source_file(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T };\n",
            "type Owner = string;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
        let owner_declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (name.text == "Owner").then_some(NodeRef::new(
                    parsed.arena.id(),
                    FileId::new(0),
                    node,
                ))
            })
            .unwrap();
        let owner = context
            .file(FileId::new(0))
            .unwrap()
            .1
            .symbol(owner_declaration)
            .unwrap();
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let instantiated = store
            .instantiate_record_mapped_alias(alias, declared, &parameters, &arguments)
            .unwrap();
        let identity = store.alloc_type_alias(Some(alias)).unwrap();
        assert!(store.set_type_alias_arguments(identity, Some(arguments.to_vec())));
        assert!(store.set_type_alias(instantiated, Some(identity)));
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &arguments,
                instantiated,
            ),
            Ok(()),
        );

        let owner_identity = store.alloc_type_alias(Some(owner)).unwrap();
        assert!(store.set_type_alias_arguments(owner_identity, Some(Vec::new())));
        assert!(store.set_type_alias(instantiated, Some(owner_identity)));
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &arguments,
                instantiated,
            ),
            Ok(()),
        );
        assert!(store.set_type_alias(instantiated, Some(identity)));

        assert!(store.set_type_alias_arguments(identity, Some(vec![arguments[1], arguments[0]]),));
        let before = cache_state(store);
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &arguments,
                instantiated,
            ),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(cache_state(store), before);

        let wrong_symbol = store.type_payload(declared).unwrap().symbol().unwrap();
        let wrong_identity = store.alloc_type_alias(Some(wrong_symbol)).unwrap();
        assert!(store.set_type_alias_arguments(wrong_identity, Some(arguments.to_vec())));
        assert!(store.set_type_alias(instantiated, Some(wrong_identity)));
        let before = cache_state(store);
        assert_eq!(
            store.validate_record_mapped_alias_instantiation(
                alias,
                declared,
                &parameters,
                &arguments,
                instantiated,
            ),
            Err(MappedTypeError::InvalidMappedType(instantiated)),
        );
        assert_eq!(cache_state(store), before);
    }

    #[test]
    fn record_alias_rejects_poisoned_warm_index_metadata_without_allocating() {
        for corruption in 0..2 {
            let parsed =
                parse_source_file("type Record<K extends keyof any, T> = { [P in K]: T };\n");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = checker_context(&parsed);
            let (alias, declared, parameters) = record_mapped_fixture(&parsed, &mut context);
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let arguments = [bootstrap.string_type, bootstrap.number_type];
            let instantiated = store
                .instantiate_record_mapped_alias(alias, declared, &parameters, &arguments)
                .unwrap();
            let members = store
                .resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE)
                .unwrap();
            let (index, declaration) = match store.type_payload(instantiated).unwrap().data() {
                TypeData::Mapped(mapped) => (
                    mapped.object.structured.index_infos.as_ref().unwrap()[0],
                    mapped.declaration.unwrap(),
                ),
                _ => unreachable!(),
            };

            match corruption {
                0 => assert!(store.set_index_info_symbol(index, Some(alias))),
                1 => {
                    let poisoned = store
                        .alloc_index_info(
                            arguments[0],
                            arguments[1],
                            false,
                            None,
                            vec![declaration],
                        )
                        .unwrap();
                    assert!(store.set_structured_type_members(
                        instantiated,
                        Some(members.members()),
                        None,
                        None,
                        None,
                        Some(vec![poisoned]),
                    ));
                }
                _ => unreachable!(),
            }

            let before = (cache_state(store), store.index_info_len());
            assert_eq!(
                store.validate_record_mapped_alias_instantiation(
                    alias,
                    declared,
                    &parameters,
                    &arguments,
                    instantiated,
                ),
                Err(MappedTypeError::InvalidMappedType(instantiated)),
            );
            assert_eq!(
                store.resolve_mapped_type_members(instantiated, MappedTypeModifiers::NONE),
                Err(MappedTypeError::InvalidCachedMembers(instantiated)),
            );
            assert_eq!((cache_state(store), store.index_info_len()), before);
        }
    }

    #[test]
    fn identity_key_remapping_preserves_source_declaration_provenance() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "type Identity = { [K in keyof Shape as K]: Shape[K] };\n",
            "type Keys = keyof Identity;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Identity");
        let keys = alias_type(&parsed, &context, "Keys");
        let source = source_property(&parsed, &context, "value");
        let parameter_constraint = match context.store().type_payload(mapped).unwrap().data() {
            TypeData::Mapped(mapped) => mapped.constraint_type.unwrap(),
            _ => unreachable!(),
        };
        assert_eq!(keys, parameter_constraint);

        let property = context
            .store_mut_for_test()
            .resolve_mapped_type_property(mapped, "value", MappedTypeModifiers::NONE)
            .unwrap()
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol(property.symbol())
                .unwrap()
                .declarations(),
            context.store().symbol(source).unwrap().declarations(),
        );
    }

    #[test]
    fn empty_mapped_types_keep_the_upstream_nil_property_cache() {
        let parsed = parse_source_file(concat!(
            "interface Empty {}\n",
            "type Result = { [K in keyof Empty]: Empty[K] };\n",
            "type Keys = keyof Result;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Result");
        assert_eq!(
            alias_type(&parsed, &context, "Keys"),
            context.store().intrinsic_bootstrap().unwrap().never_type,
        );
        let members = context
            .store_mut_for_test()
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
            .unwrap();
        assert!(members.properties().is_empty());
        let TypeData::Mapped(record) = context.store().type_payload(mapped).unwrap().data() else {
            unreachable!()
        };
        assert!(record.object.structured.members.is_some());
        assert!(record.object.structured.properties.is_none());
        let before = cache_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
                .unwrap(),
            members,
        );
        assert_eq!(cache_state(context.store()), before);
    }

    #[test]
    fn broad_mapped_constraints_publish_string_and_number_index_signatures() {
        let parsed = parse_source_file(concat!(
            "type Strings = { [K in string]: number };\n",
            "type Numbers = { readonly [K in number]: string };\n",
            "type KeyValues = { [K in string]: K };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;

        for (name, key_type, value_type, modifiers, readonly) in [
            ("Strings", string, number, MappedTypeModifiers::NONE, false),
            (
                "Numbers",
                number,
                string,
                MappedTypeModifiers::INCLUDE_READONLY,
                true,
            ),
            (
                "KeyValues",
                string,
                string,
                MappedTypeModifiers::NONE,
                false,
            ),
        ] {
            let mapped = alias_type(&parsed, &context, name);
            let before = context.store().index_info_len();
            let members = context
                .store_mut_for_test()
                .resolve_mapped_type_members(mapped, modifiers)
                .unwrap();
            assert!(members.properties().is_empty());
            assert_eq!(context.store().index_info_len(), before + 1);
            let TypeData::Mapped(record) = context.store().type_payload(mapped).unwrap().data()
            else {
                unreachable!()
            };
            assert!(record.object.structured.properties.is_none());
            let [index] = record.object.structured.index_infos.as_deref().unwrap() else {
                panic!("{name} must publish one canonical index signature");
            };
            let info = context.store().index_info(*index).unwrap();
            assert_eq!(info.key_type(), key_type);
            assert_eq!(info.value_type(), value_type);
            assert_eq!(info.is_readonly(), readonly);
            assert!(info.declaration().is_none());

            let warm = (
                cache_state(context.store()),
                context.store().index_info_len(),
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolve_mapped_type_members(mapped, modifiers)
                    .unwrap(),
                members,
            );
            assert_eq!(
                (
                    cache_state(context.store()),
                    context.store().index_info_len()
                ),
                warm,
            );
        }
    }

    #[test]
    fn homomorphic_mapped_indexes_preserve_and_remove_readonly_modifiers() {
        let parsed = parse_source_file(concat!(
            "type Table = { readonly [name: string]: number };\n",
            "type Preserved = { [K in keyof Table]: Table[K] };\n",
            "type Identity = { [K in keyof Table as K]: Table[K] };\n",
            "type Mutable = { -readonly [K in keyof Table]: Table[K] };\n",
            "type MutableIdentity = { -readonly [K in keyof Table as K]: Table[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);

        for (name, modifiers, readonly) in [
            ("Preserved", MappedTypeModifiers::NONE, true),
            ("Identity", MappedTypeModifiers::NONE, true),
            ("Mutable", MappedTypeModifiers::EXCLUDE_READONLY, false),
            (
                "MutableIdentity",
                MappedTypeModifiers::EXCLUDE_READONLY,
                false,
            ),
        ] {
            let mapped = alias_type(&parsed, &context, name);
            let members = context
                .store_mut_for_test()
                .resolve_mapped_type_members(mapped, modifiers)
                .unwrap();
            assert!(members.properties().is_empty());
            let TypeData::Mapped(record) = context.store().type_payload(mapped).unwrap().data()
            else {
                unreachable!()
            };
            let [index] = record.object.structured.index_infos.as_deref().unwrap() else {
                panic!("{name} must retain the source string index");
            };
            let info = context.store().index_info(*index).unwrap();
            assert_eq!(info.key_type(), string);
            assert_eq!(info.value_type(), number);
            assert_eq!(info.is_readonly(), readonly);
        }
    }

    #[test]
    fn homomorphic_mapped_types_preserve_properties_and_index_signatures_together() {
        let parsed = parse_source_file(concat!(
            "interface Table { fixed: number; readonly [name: string]: number }\n",
            "type Preserved = { [K in keyof Table]: Table[K] };\n",
            "type Identity = { [K in keyof Table as K]: Table[K] };\n",
            "type Mutable = { -readonly [K in keyof Table as K]: Table[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);

        for (name, modifiers, readonly) in [
            ("Preserved", MappedTypeModifiers::NONE, true),
            ("Identity", MappedTypeModifiers::NONE, true),
            ("Mutable", MappedTypeModifiers::EXCLUDE_READONLY, false),
        ] {
            let mapped = alias_type(&parsed, &context, name);
            let members = context
                .store_mut_for_test()
                .resolve_mapped_type_members(mapped, modifiers)
                .unwrap();
            assert_eq!(members.properties().len(), 1, "mapped alias {name}");
            let TypeData::Mapped(record) = context.store().type_payload(mapped).unwrap().data()
            else {
                unreachable!()
            };
            assert_eq!(
                context
                    .store()
                    .symbol_table(record.object.structured.members.unwrap())
                    .unwrap()
                    .len(),
                1,
            );
            let [index] = record.object.structured.index_infos.as_deref().unwrap() else {
                panic!("{name} must retain its source string index");
            };
            let index = context.store().index_info(*index).unwrap();
            assert_eq!(index.key_type(), string);
            assert_eq!(index.value_type(), number);
            assert_eq!(index.is_readonly(), readonly);

            let property = context
                .store_mut_for_test()
                .resolve_mapped_type_property(mapped, "fixed", modifiers)
                .unwrap()
                .unwrap();
            assert_eq!(property.type_id(), number);

            let warm = (
                cache_state(context.store()),
                context.store().index_info_len(),
            );
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolve_mapped_type_members(mapped, modifiers)
                    .unwrap(),
                members,
            );
            assert_eq!(
                (
                    cache_state(context.store()),
                    context.store().index_info_len(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn mapped_template_pattern_indexes_preserve_their_exact_key_identity() {
        let parsed = parse_source_file("type Actions = { [K in `do-${string}`]: number };\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Actions");
        let expected_key = match context.store().type_payload(mapped).unwrap().data() {
            TypeData::Mapped(record) => record.constraint_type.unwrap(),
            _ => unreachable!(),
        };
        let members = context
            .store_mut_for_test()
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
            .unwrap();
        assert!(members.properties().is_empty());
        let TypeData::Mapped(record) = context.store().type_payload(mapped).unwrap().data() else {
            unreachable!()
        };
        let [index] = record.object.structured.index_infos.as_deref().unwrap() else {
            panic!("mapped pattern keys must publish one canonical index signature");
        };
        let info = context.store().index_info(*index).unwrap();
        assert_eq!(info.key_type(), expected_key);
        assert_eq!(
            info.value_type(),
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );
        assert!(super::template_pattern_index_matches_name(
            context.store(),
            expected_key,
            "do-click",
        ));
        assert!(!super::template_pattern_index_matches_name(
            context.store(),
            expected_key,
            "ns:thing",
        ));
    }

    #[test]
    fn template_and_intrinsic_key_remapping_stays_canonical_and_lazy() {
        let parsed = parse_source_file(concat!(
            "type Capitalize<S extends string> = intrinsic;\n",
            "interface Shape { first: string; second: number }\n",
            "type Getters = { [K in keyof Shape as `get${Capitalize<K>}`]: Shape[K] };\n",
            "type Keys = keyof Getters;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Getters");
        let keys = alias_type(&parsed, &context, "Keys");
        let TypeData::Union(union) = context.store().type_payload(keys).unwrap().data() else {
            panic!("mapped keyof should preserve the remapped literal union");
        };
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert!(
            union
                .union
                .types
                .contains(&bootstrap.cached_string_literal_type("getFirst").unwrap())
        );
        assert!(
            union
                .union
                .types
                .contains(&bootstrap.cached_string_literal_type("getSecond").unwrap())
        );
        let before = context.store().symbol_len();
        let TypeData::Mapped(record) = context.store().type_payload(mapped).unwrap().data() else {
            unreachable!()
        };
        assert!(record.object.structured.members.is_none());

        let members = context
            .store_mut_for_test()
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
            .unwrap();
        assert_eq!(members.properties().len(), 2);
        assert_eq!(context.store().symbol_len(), before + 2);
        let warm = cache_state(context.store());
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
                .unwrap(),
            members,
        );
        assert_eq!(cache_state(context.store()), warm);
    }

    #[test]
    fn remapped_keyof_includes_inherited_properties_and_reuses_its_cached_union() {
        let parsed = parse_source_file(concat!(
            "interface Base { inherited: string }\n",
            "interface Derived { own: number }\n",
            "interface Derived extends Base {}\n",
            "type Getters = { [K in keyof Derived as `get${K}`]: Derived[K] };\n",
            "type Keys = keyof Getters;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Getters");
        let keys = alias_type(&parsed, &context, "Keys");
        let inherited = source_property(&parsed, &context, "inherited");
        let plan = plan_nongeneric_keyof_type(context.store(), mapped).unwrap();
        let TypeData::Union(union) = context.store().type_payload(keys).unwrap().data() else {
            panic!("inherited mapped keys must retain their canonical literal union");
        };
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(union.union.types.len(), 2);
        assert!(
            union.union.types.contains(
                &bootstrap
                    .cached_string_literal_type("getinherited")
                    .unwrap()
            )
        );
        assert!(
            union
                .union
                .types
                .contains(&bootstrap.cached_string_literal_type("getown").unwrap())
        );

        let warm = cache_state(context.store());
        assert_eq!(
            cached_nongeneric_keyof_type(context.store(), &plan),
            Ok(Some(keys)),
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(context.store_mut_for_test(), &plan),
            Ok(keys),
        );
        assert_eq!(cache_state(context.store()), warm);

        let property = context
            .store_mut_for_test()
            .resolve_mapped_type_property(mapped, "getinherited", MappedTypeModifiers::NONE)
            .unwrap()
            .unwrap();
        assert_eq!(
            context
                .store()
                .mapped_symbol_links(property.symbol())
                .and_then(|links| links.synthetic_origin),
            Some(inherited),
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn remapped_keyof_rejects_poisoned_and_duplicate_cached_unions() {
        for (name_type, reuses_constraint) in [("`get${K}`", false), ("`${K}`", true)] {
            let source = format!(
                "interface Shape {{ first: string; second: number }}\n\
                 type Remapped = {{ [K in keyof Shape as {name_type}]: Shape[K] }};\n\
                 type Keys = keyof Remapped;\n",
            );
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = checker_context(&parsed);
            context.check_source_file(FileId::new(0)).unwrap();
            let mapped = alias_type(&parsed, &context, "Remapped");
            let keys = alias_type(&parsed, &context, "Keys");
            let plan = plan_nongeneric_keyof_type(context.store(), mapped).unwrap();
            let (constraint, owner) = {
                let record = context.store().type_payload(mapped).unwrap();
                let TypeData::Mapped(mapped) = record.data() else {
                    unreachable!()
                };
                (mapped.constraint_type.unwrap(), record.symbol())
            };
            assert_eq!(keys == constraint, reuses_constraint);

            let store = context.store_mut_for_test();
            assert!(store.set_type_symbol(keys, owner));
            let poisoned = cache_state(store);
            assert_eq!(
                cached_nongeneric_keyof_type(store, &plan),
                Err(NongenericKeyofError::InvalidCachedResult(keys)),
            );
            assert_eq!(
                resolve_nongeneric_keyof_type(store, &plan),
                Err(NongenericKeyofError::InvalidCachedResult(keys)),
            );
            assert_eq!(cache_state(store), poisoned);
            assert!(store.set_type_symbol(keys, None));
            assert_eq!(cached_nongeneric_keyof_type(store, &plan), Ok(Some(keys)));

            if !reuses_constraint {
                let (object_flags, types) = {
                    let record = store.type_payload(keys).unwrap();
                    let TypeData::Union(union) = record.data() else {
                        unreachable!()
                    };
                    (record.object_flags(), union.union.types.clone())
                };
                let duplicate = store.alloc_union_type(object_flags, types).unwrap();
                let before = cache_state(store);
                assert_eq!(
                    cached_nongeneric_keyof_type(store, &plan),
                    Err(NongenericKeyofError::InvalidCachedResult(duplicate)),
                );
                assert_eq!(cache_state(store), before);
            }
        }
    }

    #[test]
    fn duplicate_numeric_and_string_names_preserve_both_literal_identities() {
        let parsed = parse_source_file(concat!(
            "interface Shape { first: string; second: number }\n",
            "type Combined = { [K in keyof Shape as 1 | \"1\"]: Shape[K] };\n",
            "type Keys = keyof Combined;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Combined");
        let keyof = alias_type(&parsed, &context, "Keys");
        let mapped_keys = plan_mapped_type_keys(context.store(), mapped).unwrap();
        let MappedTypeKeys::Remapped(keys) = mapped_keys else {
            panic!("numeric and string remapping must keep both output identities");
        };
        assert_eq!(keys.len(), 2);
        let mut saw_number = false;
        let mut saw_string = false;
        for key in &keys {
            let MappedTypeKey::Existing(type_) = key else {
                panic!("source literal names retain canonical identities");
            };
            match context.store().type_payload(*type_).unwrap().data() {
                TypeData::Literal(literal) if matches!(&literal.value, LiteralValue::Number(_)) => {
                    saw_number = true;
                }
                TypeData::Literal(literal) if matches!(&literal.value, LiteralValue::String(value) if value == "1") =>
                {
                    saw_string = true;
                }
                other => panic!("unexpected remapped key {other:?}"),
            }
        }
        assert!(saw_number && saw_string);

        let TypeData::Union(keyof_union) = context.store().type_payload(keyof).unwrap().data()
        else {
            panic!("keyof must preserve both numeric and string key identities");
        };
        assert_eq!(keyof_union.union.types.len(), 2);
        let members = context
            .store_mut_for_test()
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE)
            .unwrap();
        assert_eq!(members.properties().len(), 1);
        let property = members.properties()[0];
        let name_type = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .name_type
            .unwrap();
        let TypeData::Union(name_union) = context.store().type_payload(name_type).unwrap().data()
        else {
            panic!("duplicate numeric/string names must retain their name-type union");
        };
        assert_eq!(name_union.union.types.len(), 2);
    }

    #[test]
    fn poisoned_warm_members_do_not_intern_pending_template_names() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "type Getters = { [K in keyof Shape as `get${K}`]: Shape[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Getters");
        let store = context.store_mut_for_test();
        assert!(store.set_structured_type_members(mapped, None, None, None, None, None));
        let before = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE),
            Err(MappedTypeError::InvalidCachedMembers(mapped)),
        );
        assert_eq!(cache_state(store), before);
        assert!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("getvalue")
                .is_none()
        );
    }

    #[test]
    fn recursive_mapped_member_sources_fail_before_any_semantic_mutation() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "type Result = { [K in keyof Shape]: Shape[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Result");
        let store = context.store_mut_for_test();
        let TypeData::Mapped(record) = store.type_payload(mapped).unwrap().data() else {
            unreachable!()
        };
        let record = record.clone();
        assert!(store.set_mapped_type_resolution(
            mapped,
            record.declaration,
            record.type_parameter,
            record.constraint_type,
            record.name_type,
            record.template_type,
            Some(mapped),
            record.resolved_apparent_type,
            record.contains_error,
        ));
        let before = cache_state(store);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE),
            Err(MappedTypeError::RecursiveMembers(mapped)),
        );
        assert_eq!(cache_state(store), before);
        assert!(
            !store
                .type_payload(mapped)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
    }

    #[test]
    fn unsupported_later_remap_branch_leaves_all_checker_caches_unchanged() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "type Getters = { [K in keyof Shape as `get${K}`]: Shape[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Getters");
        let store = context.store_mut_for_test();
        let name = match store.type_payload(mapped).unwrap().data() {
            TypeData::Mapped(record) => record.name_type.unwrap(),
            _ => unreachable!(),
        };
        let boolean = store.intrinsic_bootstrap().unwrap().boolean_type;
        let invalid = store
            .alloc_union_type(ObjectFlags::NONE, vec![name, boolean])
            .unwrap();
        replace_mapped_name(store, mapped, invalid);
        let before = cache_state(store);
        assert!(matches!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE),
            Err(MappedTypeError::UnsupportedNameType(_)),
        ));
        assert_eq!(cache_state(store), before);
        assert!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("getvalue")
                .is_none()
        );
    }

    #[test]
    fn excessive_template_key_cross_products_preserve_the_ts2590_failure() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "type Getters = { [K in keyof Shape as `get${K}`]: Shape[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let mapped = alias_type(&parsed, &context, "Getters");
        let store = context.store_mut_for_test();
        let mut values = Vec::new();
        for index in 0..317 {
            values.push(
                store
                    .regular_string_literal_type(format!("key{index}"))
                    .unwrap(),
            );
        }
        let union = store.literal_union_type(&values, None).unwrap();
        let template = store
            .alloc_template_literal_type(
                vec![String::new(), String::new(), String::new()],
                vec![union, union],
            )
            .unwrap();
        replace_mapped_name(store, mapped, template);
        let before = cache_state(store);
        let keyof = plan_nongeneric_keyof_type(store, mapped).unwrap();
        assert_eq!(
            keyof.mapped_cross_product_too_large(),
            Some((317 * 317, MAX_TEMPLATE_UNION_SIZE)),
        );
        assert_eq!(
            cached_nongeneric_keyof_type(store, &keyof).unwrap(),
            Some(store.intrinsic_bootstrap().unwrap().error_type),
        );
        assert_eq!(cache_state(store), before);
        assert_eq!(
            store.resolve_mapped_type_members(mapped, MappedTypeModifiers::NONE),
            Err(MappedTypeError::CrossProductTooLarge {
                size: 317 * 317,
                limit: MAX_TEMPLATE_UNION_SIZE,
            }),
        );
        assert_eq!(cache_state(store), before);
    }
}
