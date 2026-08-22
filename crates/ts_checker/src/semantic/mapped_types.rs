//! Canonical mapped object types and lazy mapped properties.
//!
//! The implementation follows `getTypeFromMappedTypeNode`,
//! `resolveMappedTypeMembers`, and `getTypeOfMappedSymbol` from the pinned
//! TypeScript Go checker. Source routing supplies the already-resolved type
//! operands. This module owns mapped records, transient property symbols,
//! modifier preservation, and delayed property type computation.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId, TypeResolutionTarget,
    TypeSystemPropertyName,
    bootstrap::LiteralTypeCacheError,
    declared::{
        cached_ordinary_type_parameter_owner, preflight_node, preflight_type_parameter_symbol,
    },
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession, canonical_anonymous_union,
        instantiate_type_with_session,
    },
    links::{MappedSymbolLinks, TypeNodeLinks, ValueSymbolLinks},
    store::SourceNodeParent,
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
    CircularProperty(SemanticSymbolId),
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
            Self::CircularProperty(symbol) => {
                write!(formatter, "mapped property {symbol:?} references itself")
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

#[derive(Clone, Debug)]
struct MappedShape {
    type_: TypeId,
    type_parameter: TypeId,
    constraint_type: TypeId,
    template_type: TypeId,
    modifiers_type: TypeId,
    name_type: Option<TypeId>,
    source_properties: Vec<SourceProperty>,
}

#[derive(Clone, Debug)]
struct PlannedMappedProperty {
    name: EscapedName,
    name_type: TypeId,
    keys: Vec<TypeId>,
    origin: Option<SemanticSymbolId>,
    optional: bool,
    readonly: bool,
    strip_optional: bool,
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
        let shape = validate_mapped_shape(self, type_)?;
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
    Ok(MappedShape {
        type_,
        type_parameter,
        constraint_type,
        template_type,
        modifiers_type,
        name_type: mapped.name_type,
        source_properties,
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
    if structured.call_signature_count != 0
        || structured.signatures.is_some()
        || structured.index_infos.is_some()
    {
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
    if table.is_some_and(|table| table.len() != properties.len()) {
        return Err(MappedTypeError::InvalidSource(type_));
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

fn plan_mapped_properties(
    store: &mut CanonicalTypeMapperStore,
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
        let origin = property_name_from_type(store, key).and_then(|name| {
            shape
                .source_properties
                .iter()
                .find(|property| property.name.as_ref().as_utf8() == Some(name.as_str()))
                .cloned()
        });
        let names = mapped_name_types(store, shape, key)?;
        for name_type in names {
            let property_name = property_name_from_type(store, name_type)
                .ok_or(MappedTypeError::UnsupportedNameType(name_type))?;
            let name = EscapedName::source(property_name);
            if let Some(index) = indexes.get(&name).copied() {
                properties[index].keys.push(key);
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
                name_type,
                keys: vec![key],
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
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
) -> Result<Vec<TypeId>, MappedTypeError> {
    let record =
        store
            .type_payload(shape.constraint_type)
            .ok_or(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ))?;
    let keys = match record.data() {
        TypeData::Index(index) if index.target == shape.modifiers_type => {
            let names = shape
                .source_properties
                .iter()
                .map(|property| {
                    property
                        .name
                        .as_ref()
                        .as_utf8()
                        .map(str::to_owned)
                        .ok_or(MappedTypeError::InvalidSource(shape.modifiers_type))
                })
                .collect::<Result<Vec<_>, _>>()?;
            store
                .prepare_regular_literal_types(&names, &[], &[])
                .map_err(mapped_cache_error)?;
            names
                .into_iter()
                .map(|name| {
                    store
                        .regular_string_literal_type(name)
                        .map_err(mapped_cache_error)
                })
                .collect::<Result<Vec<_>, _>>()?
        }
        TypeData::Union(union) => union.union.types.clone(),
        TypeData::Literal(_) | TypeData::UniqueEsSymbol(_) => vec![shape.constraint_type],
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
        if property_name_from_type(store, *key).is_none() {
            return Err(MappedTypeError::UnsupportedConstraint(*key));
        }
    }
    Ok(keys)
}

fn mapped_name_types(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key: TypeId,
) -> Result<Vec<TypeId>, MappedTypeError> {
    let Some(name_type) = shape.name_type else {
        return Ok(vec![key]);
    };
    substitute_name_type(store, shape.type_parameter, key, name_type)
}

fn substitute_name_type(
    store: &CanonicalTypeMapperStore,
    parameter: TypeId,
    key: TypeId,
    name_type: TypeId,
) -> Result<Vec<TypeId>, MappedTypeError> {
    if name_type == parameter {
        return Ok(vec![key]);
    }
    let record = store
        .type_payload(name_type)
        .ok_or(MappedTypeError::UnsupportedNameType(name_type))?;
    match record.data() {
        TypeData::Literal(_) if property_name_from_type(store, name_type).is_some() => {
            Ok(vec![name_type])
        }
        TypeData::Intrinsic(_) if record.flags().contains(TypeFlags::NEVER) => Ok(Vec::new()),
        TypeData::Union(union) => union
            .union
            .types
            .iter()
            .map(|type_| substitute_name_type(store, parameter, key, *type_))
            .collect::<Result<Vec<_>, _>>()
            .map(|types| types.into_iter().flatten().collect()),
        _ => Err(MappedTypeError::UnsupportedNameType(name_type)),
    }
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
    let properties = structured
        .properties
        .as_deref()
        .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
    let table = store
        .symbol_table(members)
        .ok_or(MappedTypeError::InvalidCachedMembers(shape.type_))?;
    if properties.len() != expected.len()
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
            || value.name_type != Some(expected.name_type)
            || value.target.is_some()
            || value.mapper.is_some()
            || value.write_type.is_some()
            || value.function_or_constructor_checked
            || value
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
            || property.declarations()
                != expected.origin.and_then(|origin| {
                    (shape.name_type.is_none())
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
    expected: &[TypeId],
) -> bool {
    match (cached, expected) {
        (Some(key), [single]) => key == *single,
        (Some(key), expected) => store
            .type_payload(key)
            .and_then(|record| match record.data() {
                TypeData::Union(union) => Some(&union.union.types),
                _ => None,
            })
            .is_some_and(|types| {
                let mut expected = expected.to_vec();
                expected.sort_unstable();
                expected.dedup();
                types == &expected
            }),
        _ => false,
    }
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
    if !store.try_reserve_checker_symbol_allocations(planned.len(), 1)
        || !store.try_reserve_value_symbol_links(planned.len())
    {
        return Err(MappedTypeError::Capacity);
    }
    let mut resolved_keys = Vec::with_capacity(planned.len());
    for property in &planned {
        let key = match property.keys.as_slice() {
            [key] => *key,
            keys => canonical_anonymous_union(store, keys).map_err(mapped_cache_error)?,
        };
        resolved_keys.push(key);
    }

    let members = store.alloc_prepared_symbol_table(table);
    let mut properties = Vec::with_capacity(planned.len());
    for (property, key) in planned.into_iter().zip(resolved_keys) {
        let mut flags = SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT;
        if property.optional {
            flags |= SymbolFlags::OPTIONAL;
        }
        let mut data = SymbolData::new(flags, property.name.clone());
        data.check_flags = expected_check_flags(store, &property)?;
        if shape.name_type.is_none()
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
                name_type: Some(property.name_type),
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
        Some(properties.clone()),
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
        EscapedName,
    };
    use ts_parser::parse_source_file;

    use super::{MappedTypeModifiers, plan_mapped_type_declaration};
    use crate::semantic::{CanonicalTypeMapperStore, DeclaredTypeHost, IntrinsicBootstrapOptions};

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
}
