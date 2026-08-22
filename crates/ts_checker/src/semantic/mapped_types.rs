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

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId, TypeResolutionTarget,
    TypeSystemPropertyName,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    declared::{
        cached_ordinary_type_parameter_owner, preflight_node, preflight_type_parameter_symbol,
    },
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession, canonical_anonymous_union,
        instantiate_type_with_session,
    },
    links::{MappedSymbolLinks, TypeNodeLinks, ValueSymbolLinks},
    store::SourceNodeParent,
    template_types::{MAX_TEMPLATE_UNION_SIZE, StringMappingKind},
    type_records::{LiteralValue, StructuredTypeData, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
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

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
struct MappedShape {
    type_: TypeId,
    type_parameter: TypeId,
    constraint_type: TypeId,
    template_type: TypeId,
    modifiers_type: TypeId,
    name_type: Option<TypeId>,
    source_properties: Vec<SourceProperty>,
    source_indexes: Vec<SourceIndex>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PlannedMappedIndex {
    key_type: TypeId,
    value_type: TypeId,
    readonly: bool,
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
        || cached_ordinary_type_parameter_owner(store, parameter).is_none()
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
        if !modifiers.valid() {
            return Err(MappedTypeError::InvalidModifiers);
        }
        validate_mapped_member_dependencies(self, type_, &mut HashSet::new())?;
        let shape = validate_mapped_shape(self, type_)?;
        if let Some(indexes) = plan_mapped_index_signatures(self, &shape, modifiers)? {
            return resolve_mapped_index_signatures(self, &shape, &indexes);
        }
        let properties = plan_mapped_properties(self, &shape, modifiers)?;
        if let Some(cached) = validate_warm_mapped_members(self, &shape, &properties)? {
            return Ok(cached);
        }
        publish_mapped_members(self, &shape, properties)
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
        let (containing_type, key_type, cached) = validate_mapped_property_header(self, symbol)?;
        if let Some(cached) = cached {
            if self.type_payload(cached).is_none() {
                return Err(MappedTypeError::InvalidCachedProperty(symbol));
            }
            return Ok(cached);
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

        let computed = compute_mapped_property_type(self, containing_type, symbol, key_type);
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
        if !self.set_value_symbol_links(symbol, links) {
            return Err(MappedTypeError::InvalidCachedProperty(symbol));
        }
        Ok(type_)
    }
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
    if cached_ordinary_type_parameter_owner(store, type_parameter).is_none() {
        return Err(MappedTypeError::InvalidTypeParameter(type_parameter));
    }
    let constraint_type = mapped
        .constraint_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let template_type = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let modifiers_type = mapped
        .modifiers_type
        .ok_or(MappedTypeError::InvalidMappedType(type_))?;
    let source_properties = source_properties(store, modifiers_type)?;
    let source_indexes = source_indexes(store, modifiers_type)?;
    Ok(MappedShape {
        type_,
        type_parameter,
        constraint_type,
        template_type,
        modifiers_type,
        name_type: mapped.name_type,
        source_properties,
        source_indexes,
    })
}

fn source_properties(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Vec<SourceProperty>, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidSource(type_))?;
    if record.flags().contains(TypeFlags::UNKNOWN) {
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
    if record.flags().contains(TypeFlags::UNKNOWN) {
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
        if ![bootstrap.string_type, bootstrap.number_type].contains(&info.key_type())
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

fn plan_mapped_index_signatures(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    modifiers: MappedTypeModifiers,
) -> Result<Option<Vec<PlannedMappedIndex>>, MappedTypeError> {
    if shape.name_type.is_some() || !shape.source_properties.is_empty() {
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
    let mut keys = match constraint.data() {
        TypeData::Intrinsic(_)
            if [bootstrap.string_type, bootstrap.number_type].contains(&shape.constraint_type) =>
        {
            vec![shape.constraint_type]
        }
        TypeData::Union(union)
            if union
                .union
                .types
                .iter()
                .all(|key| [bootstrap.string_type, bootstrap.number_type].contains(key)) =>
        {
            if shape.source_indexes.is_empty() {
                union.union.types.clone()
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
                if key_type == bootstrap.number_type {
                    shape
                        .source_indexes
                        .iter()
                        .find(|index| index.key_type == bootstrap.string_type)
                } else {
                    None
                }
            });
        let value_type = mapped_index_value_type(store, shape, key_type, source)?;
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
        TypeData::IndexedAccess(indexed)
            if indexed.object_type == shape.modifiers_type
                && indexed.index_type == shape.type_parameter =>
        {
            source
                .map(|index| index.value_type)
                .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))
        }
        TypeData::Intrinsic(_) | TypeData::Literal(_) => Ok(shape.template_type),
        _ => Err(MappedTypeError::UnsupportedTemplate(shape.template_type)),
    }
}

fn resolve_mapped_index_signatures(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    expected: &[PlannedMappedIndex],
) -> Result<ResolvedMappedTypeMembers, MappedTypeError> {
    let record = store
        .type_payload(shape.type_)
        .ok_or(MappedTypeError::InvalidMappedType(shape.type_))?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(MappedTypeError::InvalidMappedType(shape.type_));
    };
    let structured = &mapped.object.structured;
    if record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        let members = structured
            .members
            .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
        let table = store
            .symbol_table(members)
            .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
        let infos = structured.index_infos.as_deref().unwrap_or_default();
        if !table.is_empty()
            || structured.properties.is_some()
            || structured.signatures.is_some()
            || structured.call_signature_count != 0
            || infos.len() != expected.len()
            || infos.iter().zip(expected).any(|(id, planned)| {
                store.index_info(*id).is_none_or(|info| {
                    info.key_type() != planned.key_type
                        || info.value_type() != planned.value_type
                        || info.is_readonly() != planned.readonly
                        || info.declaration().is_some()
                })
            })
        {
            return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
        }
        return Ok(ResolvedMappedTypeMembers {
            type_: shape.type_,
            members,
            properties: Vec::new(),
        });
    }
    if structured != &StructuredTypeData::default() {
        return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
    }
    let table = PreparedSymbolTable::new(0).ok_or(MappedTypeError::Capacity)?;
    if !store.try_reserve_checker_symbol_allocations(0, 1)
        || !store.try_reserve_index_infos(expected.len())
    {
        return Err(MappedTypeError::Capacity);
    }
    if !store.set_structured_type_members(shape.type_, None, None, None, None, None) {
        return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
    }
    let members = store.alloc_prepared_symbol_table(table);
    let mut infos = Vec::with_capacity(expected.len());
    for index in expected {
        infos.push(
            store
                .alloc_index_info(
                    index.key_type,
                    index.value_type,
                    index.readonly,
                    None,
                    Vec::new(),
                )
                .ok_or(MappedTypeError::Capacity)?,
        );
    }
    if !store.set_structured_type_members(
        shape.type_,
        Some(members),
        None,
        None,
        None,
        (!infos.is_empty()).then_some(infos),
    ) {
        return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
    }
    Ok(ResolvedMappedTypeMembers {
        type_: shape.type_,
        members,
        properties: Vec::new(),
    })
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
        let origin = key.name(store).and_then(|name| {
            shape
                .source_properties
                .iter()
                .find(|property| property.name.as_ref().as_utf8() == Some(name.as_str()))
                .cloned()
        });
        let names = mapped_name_types(store, shape, &key)?;
        for name_type in names {
            let property_name =
                name_type
                    .name(store)
                    .ok_or(MappedTypeError::UnsupportedNameType(
                        shape.name_type.unwrap_or(shape.type_parameter),
                    ))?;
            let name = EscapedName::source(property_name);
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
    let record =
        store
            .type_payload(shape.constraint_type)
            .ok_or(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ))?;
    let keys = match record.data() {
        TypeData::Index(index) if index.target == shape.modifiers_type => shape
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
            .collect::<Result<Vec<_>, _>>()?,
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
            let mut nested = shape.clone();
            nested.constraint_type = constraint;
            constraint_keys(store, &nested)?
        }
        _ => {
            return Err(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ));
        }
    };
    for key in &keys {
        if key.name(store).is_none() {
            return Err(MappedTypeError::UnsupportedConstraint(
                key.cached_type(store).unwrap_or(shape.constraint_type),
            ));
        }
    }
    Ok(keys)
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

fn validate_warm_mapped_members(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    expected: &[PlannedMappedProperty],
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
    if properties.len() != expected.len()
        || structured.properties.is_some() == expected.is_empty()
        || table.len() != expected.len()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
    {
        return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
    }
    for (symbol, expected) in properties.iter().zip(expected) {
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
    if !store.try_reserve_checker_symbol_allocations(planned.len(), 1)
        || !store.try_reserve_value_symbol_links(planned.len())
    {
        return Err(MappedTypeError::Capacity);
    }
    let mut prepared = store
        .prepare_type_query_types(&pending_strings, &[], &[], union_operations, 0)
        .map_err(mapped_cache_error)?;
    if !store.set_structured_type_members(shape.type_, None, None, None, None, None) {
        return Err(MappedTypeError::InvalidCachedMembers(shape.type_));
    }
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

    let members = store.alloc_prepared_symbol_table(table);
    let mut properties = Vec::with_capacity(planned.len());
    for ((property, key), name_type) in planned.into_iter().zip(resolved_keys).zip(resolved_names) {
        let mut flags = SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT;
        if property.optional {
            flags |= SymbolFlags::OPTIONAL;
        }
        let mut data = SymbolData::new(flags, property.name.clone());
        data.check_flags = expected_check_flags(store, &property)?;
        if should_link_source_declarations(shape)
            && let Some(origin) = property.origin
        {
            data.declarations = store
                .symbol(origin)
                .and_then(|source| source.declarations())
                .map(<[_]>::to_vec);
        }
        let symbol = store.alloc_symbol(data).ok_or(MappedTypeError::Capacity)?;
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
    assert!(store.set_structured_type_members(
        shape.type_,
        Some(members),
        (!properties.is_empty()).then_some(properties.clone()),
        None,
        None,
        None,
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

fn compute_mapped_property_type(
    store: &mut CanonicalTypeMapperStore,
    containing_type: TypeId,
    symbol: SemanticSymbolId,
    key_type: TypeId,
) -> Result<TypeId, MappedTypeError> {
    let shape = validate_mapped_shape(store, containing_type)?;
    let mut type_ = instantiate_mapped_template(store, &shape, key_type)?;
    let (optional, strip_optional) = {
        let property = store
            .symbol(symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(symbol))?;
        (
            property.flags().contains(SymbolFlags::OPTIONAL),
            property.check_flags().contains(CheckFlags::STRIP_OPTIONAL),
        )
    };
    let (strict, exact, undefined, missing) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| {
            (
                bootstrap.options.strict_null_checks,
                bootstrap.options.exact_optional_property_types,
                bootstrap.undefined_type,
                bootstrap.undefined_or_missing_type,
            )
        })
        .ok_or(MappedTypeError::BootstrapUninitialized)?;

    if strict && optional && !type_contains_undefined_or_void(store, type_)? {
        type_ = canonical_anonymous_union(store, &[type_, missing]).map_err(mapped_cache_error)?;
    } else if strip_optional {
        let sentinel = if exact { missing } else { undefined };
        type_ = remove_type(store, type_, sentinel)?;
    }
    Ok(type_)
}

fn instantiate_mapped_template(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
) -> Result<TypeId, MappedTypeError> {
    let template = store
        .type_payload(shape.template_type)
        .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))?;
    let indexed = match template.data() {
        TypeData::IndexedAccess(indexed)
            if indexed.object_type == shape.modifiers_type
                && indexed.index_type == shape.type_parameter =>
        {
            Some(indexed.object_type)
        }
        TypeData::IndexedAccess(_) => {
            return Err(MappedTypeError::UnsupportedTemplate(shape.template_type));
        }
        _ => None,
    };
    if indexed.is_some() {
        return indexed_mapped_template(store, shape, key_type);
    }
    if shape.template_type == shape.type_parameter {
        return Ok(key_type);
    }
    if !template
        .flags()
        .intersects(TypeFlags::TYPE_PARAMETER | TypeFlags::UNION | TypeFlags::OBJECT)
    {
        return Ok(shape.template_type);
    }
    if !store.try_reserve_mappers(1) {
        return Err(MappedTypeError::Capacity);
    }
    let mapper = store
        .new_simple_type_mapper(shape.type_parameter, key_type)
        .ok_or(MappedTypeError::InvalidTypeParameter(shape.type_parameter))?;
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    instantiate_type_with_session(store, shape.template_type, mapper, None, &mut session)
        .map_err(|error| mapped_instantiation_error(shape.template_type, &error))
}

fn indexed_mapped_template(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
) -> Result<TypeId, MappedTypeError> {
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
            .find(|property| property.name.as_ref().as_utf8() == Some(name.as_str()))
            .ok_or(MappedTypeError::UnsupportedTemplate(shape.template_type))?;
        let links = store
            .value_symbol_links(source.symbol)
            .ok_or(MappedTypeError::InvalidCachedProperty(source.symbol))?;
        let property_type = match links.resolved_type {
            Some(resolved) => resolved,
            None => store.resolve_mapped_symbol_type(source.symbol)?,
        };
        values.push(property_type);
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
        InstantiationError::DepthLimit { .. }
        | InstantiationError::CountLimit { .. }
        | InstantiationError::Union(LiteralTypeCacheError::Capacity) => MappedTypeError::Capacity,
        _ => MappedTypeError::UnsupportedTemplate(type_),
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::{
        MAX_TEMPLATE_UNION_SIZE, MappedTypeError, MappedTypeKey, MappedTypeKeys,
        MappedTypeModifiers, plan_mapped_type_declaration, plan_mapped_type_keys,
    };
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
        DeclaredTypeHost, IntrinsicBootstrapOptions, TypeData, TypeId,
        keyof_types::{cached_nongeneric_keyof_type, plan_nongeneric_keyof_type},
        type_records::LiteralValue,
        types::ObjectFlags,
    };

    fn checker_context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
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
            CanonicalCheckerOptions::default(),
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
            "type Mutable = { -readonly [K in keyof Table]: Table[K] };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(&parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);

        for (name, modifiers, readonly) in [
            ("Preserved", MappedTypeModifiers::NONE, true),
            ("Mutable", MappedTypeModifiers::EXCLUDE_READONLY, false),
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
