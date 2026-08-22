//! Lazy members for direct local generic-interface references.
//!
//! This is the property-only prefix of pinned `resolveTypeReferenceMembers`,
//! `resolveObjectTypeMembers`, `instantiateSymbolTable`, and
//! `instantiateSymbol`. A direct reference (including the generic target's
//! canonical identity reference) already belongs to its target's
//! instantiation cache before this module runs. Member resolution pads the
//! explicit arguments with that reference for the implicit `this` type
//! parameter, creates one mapper, and publishes a mixed table of invariant
//! source symbols and lazy transient property proxies in one final
//! transaction.

use std::collections::HashSet;

use ts_ast::SyntaxKind;
use ts_binder::{
    CheckFlags, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalTypeMapperStore, IndexInfoId, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession,
        instantiable_member_type_contains_variables, instantiate_type_with_session,
        instantiate_type_with_vector_and_session, instantiated_member_type_matches,
    },
    links::ValueSymbolLinks,
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_declared_property_object,
    },
    reference_types::{DirectGenericReferenceError, validate_direct_generic_reference},
    store::SourceNodeParent,
    type_records::{
        ConstrainedTypeData, LiteralValue, StructuredTypeData, TypeCacheState, TypeData,
    },
    types::{AccessFlags, ObjectFlags, TypeFlags},
};

/// Optional canonical `Array` capability for the context-free store adapter.
///
/// Production checker contexts retain both `Array` and `ReadonlyArray`
/// identities. This narrow adapter accepts one already-validated generic
/// target and treats it as the sole array family, which is sufficient for
/// direct `T[]` member templates without discovering a global by name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GenericInterfaceArrayTarget {
    target: TypeId,
}

impl GenericInterfaceArrayTarget {
    #[must_use]
    pub const fn new(target: TypeId) -> Self {
        Self { target }
    }

    #[must_use]
    pub const fn target(self) -> TypeId {
        self.target
    }
}

/// The exact cached structured-member identity for one direct reference.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstantiatedInterfaceMembers {
    reference: TypeId,
    target: TypeId,
    mapper: Option<TypeMapperId>,
    members: Option<SymbolTableId>,
    properties: Vec<SemanticSymbolId>,
}

impl InstantiatedInterfaceMembers {
    #[must_use]
    pub const fn reference(&self) -> TypeId {
        self.reference
    }

    #[must_use]
    pub const fn target(&self) -> TypeId {
        self.target
    }

    #[must_use]
    pub const fn mapper(&self) -> Option<TypeMapperId> {
        self.mapper
    }

    #[must_use]
    pub const fn members(&self) -> Option<SymbolTableId> {
        self.members
    }

    #[must_use]
    pub fn properties(&self) -> &[SemanticSymbolId] {
        &self.properties
    }
}

/// One property selected from a direct generic-interface reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InstantiatedInterfaceProperty {
    symbol: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
    readonly: bool,
}

impl InstantiatedInterfaceProperty {
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

/// A malformed cache or a deliberately unsupported generic member surface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GenericInterfaceMemberError {
    Reference(DirectGenericReferenceError),
    UnsupportedTarget(TypeId),
    InvalidTarget(TypeId),
    UnsupportedMember(SemanticSymbolId),
    InvalidMember(SemanticSymbolId),
    UnsupportedPropertyType(TypeId),
    InvalidCachedMembers(TypeId),
    InvalidCachedProperty(SemanticSymbolId),
    Capacity(TypeId),
}

impl std::fmt::Display for GenericInterfaceMemberError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Reference(error) => error.fmt(formatter),
            Self::UnsupportedTarget(type_) => write!(
                formatter,
                "type {type_:?} is outside the local property-only generic interface slice"
            ),
            Self::InvalidTarget(type_) => {
                write!(formatter, "generic interface target {type_:?} is malformed")
            }
            Self::UnsupportedMember(symbol) => write!(
                formatter,
                "member {symbol:?} is outside the property-signature-only slice"
            ),
            Self::InvalidMember(symbol) => {
                write!(
                    formatter,
                    "declared generic interface member {symbol:?} is malformed"
                )
            }
            Self::UnsupportedPropertyType(type_) => write!(
                formatter,
                "property type {type_:?} is outside the installed instantiation slice"
            ),
            Self::InvalidCachedMembers(type_) => {
                write!(formatter, "reference {type_:?} has an invalid member cache")
            }
            Self::InvalidCachedProperty(symbol) => {
                write!(
                    formatter,
                    "instantiated property {symbol:?} has invalid lazy links"
                )
            }
            Self::Capacity(type_) => write!(
                formatter,
                "generic interface member resolution for {type_:?} exhausted capacity"
            ),
        }
    }
}

impl std::error::Error for GenericInterfaceMemberError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Reference(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DirectGenericReferenceError> for GenericInterfaceMemberError {
    fn from(error: DirectGenericReferenceError) -> Self {
        Self::Reference(error)
    }
}

#[derive(Clone, Debug)]
struct DeclaredProperty {
    symbol: SemanticSymbolId,
    name: EscapedName,
    type_: TypeId,
    requires_proxy: bool,
}

type DeclaredTargetHeader = (
    SemanticSymbolId,
    Vec<TypeId>,
    Option<SymbolTableId>,
    Vec<DeclaredProperty>,
);

#[derive(Clone, Debug)]
struct GenericInterfaceShape {
    reference: TypeId,
    target: TypeId,
    source_parameters: Vec<TypeId>,
    target_arguments: Vec<TypeId>,
    properties: Vec<DeclaredProperty>,
    base_types: Vec<TypeId>,
    inherited_properties: Vec<SemanticSymbolId>,
    inherited_members_ready: bool,
}

#[derive(Clone, Debug)]
enum ColdPropertyPlan {
    Reused {
        symbol: SemanticSymbolId,
        name: EscapedName,
    },
    Proxy {
        target: SemanticSymbolId,
        data: SymbolData,
        name_type: Option<TypeId>,
    },
}

#[derive(Debug)]
struct ColdMembersPlan {
    mapper_sources: Vec<TypeId>,
    mapper_targets: Vec<TypeId>,
    requires_mapper: bool,
    table: Option<PreparedSymbolTable>,
    properties: Vec<ColdPropertyPlan>,
}

impl CanonicalTypeMapperStore {
    /// Instantiates one index-signature value while retaining its canonical
    /// key type, readonly flag, declaration, and component identities.
    ///
    /// # Errors
    ///
    /// Returns [`GenericInterfaceMemberError`] for invalid index records,
    /// malformed mappers, unsupported value types, or allocation failure.
    pub fn instantiate_generic_interface_index_info(
        &mut self,
        reference: TypeId,
        index: IndexInfoId,
        mapper: TypeMapperId,
        array_target: Option<GenericInterfaceArrayTarget>,
    ) -> Result<IndexInfoId, GenericInterfaceMemberError> {
        let array_targets = array_target
            .map(|target| CanonicalArrayTargets::for_single_target_validation(target.target));
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        instantiate_generic_index_info_with_array_targets(
            self,
            reference,
            index,
            mapper,
            array_targets,
            &mut session,
        )
    }

    /// Resolves the property-only member table of one direct generic interface
    /// reference, including the canonical target identity.
    ///
    /// The target must already own a fully resolved declared property table.
    /// This store-level adapter intentionally does not parse or publish that
    /// declaration table; the production source adapter remains its owner.
    ///
    /// # Errors
    ///
    /// Returns [`GenericInterfaceMemberError`] for a foreign identity,
    /// malformed or poisoned cache, nonlocal/merged/class target, unsupported
    /// member or property type, or capacity failure. A rejected cold query
    /// publishes no mapper, transient symbol, table, or structured-member
    /// cache.
    pub fn resolve_generic_interface_members(
        &mut self,
        reference: TypeId,
        array_target: Option<GenericInterfaceArrayTarget>,
    ) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
        let array_targets = array_target
            .map(|target| CanonicalArrayTargets::for_single_target_validation(target.target));
        resolve_members_with_array_targets(self, reference, array_targets)
    }

    /// Selects one own property from a direct generic interface reference.
    ///
    /// A valid missing name returns `Ok(None)`. Invariant resolved properties
    /// reuse their declared symbol and type. The first successful lookup of a
    /// variable-containing property caches its instantiated value type on the
    /// transient proxy; warm lookups validate and reuse that exact identity.
    ///
    /// # Errors
    ///
    /// Returns [`GenericInterfaceMemberError`] under the same conditions as
    /// [`Self::resolve_generic_interface_members`], or when a lazy property
    /// cache contradicts its retained target and mapper.
    pub fn resolve_generic_interface_property(
        &mut self,
        reference: TypeId,
        name: &str,
        array_target: Option<GenericInterfaceArrayTarget>,
    ) -> Result<Option<InstantiatedInterfaceProperty>, GenericInterfaceMemberError> {
        let array_targets = array_target
            .map(|target| CanonicalArrayTargets::for_single_target_validation(target.target));
        resolve_property_with_array_targets(self, reference, name, array_targets)
    }
}

pub(super) fn instantiate_generic_index_info_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    index: IndexInfoId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<IndexInfoId, GenericInterfaceMemberError> {
    if store.type_payload(reference).is_none() {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(reference));
    }
    let info = store
        .index_info(index)
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(reference))?;
    let key = info.key_type();
    let value = info.value_type();
    let readonly = info.is_readonly();
    let declaration = info.declaration();
    let components = info.components().to_vec();
    if let Some(symbol) = info.index_symbol() {
        return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
    }
    if store.mapper_payload(mapper).is_none() {
        return Err(GenericInterfaceMemberError::UnsupportedPropertyType(value));
    }
    if !store.try_reserve_index_infos(1) {
        return Err(GenericInterfaceMemberError::Capacity(value));
    }
    let instantiated =
        instantiate_generic_member_type(store, value, mapper, array_targets, session)?;
    if instantiated == value {
        return Ok(index);
    }
    store
        .alloc_index_info(key, instantiated, readonly, declaration, components)
        .ok_or(GenericInterfaceMemberError::Capacity(value))
}

pub(super) fn resolve_members_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
    let mut shape = validate_shape(store, reference, array_targets)?;
    if let Some(cached) = validate_warm_members(store, &shape, array_targets)? {
        return Ok(cached);
    }
    if !shape.inherited_members_ready {
        materialize_inherited_members(store, &shape, array_targets)?;
        shape = validate_shape(store, reference, array_targets)?;
        if !shape.inherited_members_ready {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(reference));
        }
    }
    let plan = prepare_cold_members(store, &shape)?;
    Ok(publish_cold_members(store, &shape, plan))
}

/// Validates the declaration graph and any published member cache without
/// allocating or resolving cold members.
pub(super) fn validate_generic_interface_members(
    store: &CanonicalTypeMapperStore,
    reference: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<InstantiatedInterfaceMembers>, GenericInterfaceMemberError> {
    let shape = validate_shape(store, reference, array_targets)?;
    validate_warm_members(store, &shape, array_targets)
}

pub(super) fn resolve_property_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    name: &str,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<InstantiatedInterfaceProperty>, GenericInterfaceMemberError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_property_with_array_targets_and_session(
        store,
        reference,
        name,
        array_targets,
        &mut session,
    )
}

pub(super) fn resolve_property_with_array_targets_and_session(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    name: &str,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<Option<InstantiatedInterfaceProperty>, GenericInterfaceMemberError> {
    let members = resolve_members_with_array_targets(store, reference, array_targets)?;
    let Some(symbol) = members
        .members
        .and_then(|table| store.symbol_table(table))
        .and_then(|table| table.get_source(name))
    else {
        return Ok(None);
    };
    let record = store
        .symbol(symbol)
        .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?;
    let optional = record.flags().contains(SymbolFlags::OPTIONAL);
    let readonly = record.check_flags().contains(CheckFlags::READONLY);
    let type_ =
        demand_instantiated_property_type(store, reference, symbol, array_targets, session)?;
    Ok(Some(InstantiatedInterfaceProperty {
        symbol,
        type_,
        optional,
        readonly,
    }))
}

/// Demands one property from a validated instantiated interface and fills its
/// lazy type through the caller's existing instantiation session.
pub(super) fn demand_instantiated_property_type(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    symbol: SemanticSymbolId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let members = validate_generic_interface_members(store, reference, array_targets)?
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(reference))?;
    if !members.properties.contains(&symbol) {
        return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
    }
    let record = store
        .symbol(symbol)
        .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?;
    let links = store
        .value_symbol_links(symbol)
        .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?;
    let cached = links.resolved_type;
    let proxy = record.flags().contains(SymbolFlags::TRANSIENT)
        && record.check_flags().contains(CheckFlags::INSTANTIATED);
    if !proxy {
        return cached.ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
    }
    let (target, mapper) = {
        let links = store
            .value_symbol_links(symbol)
            .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?;
        (
            links
                .target
                .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?,
            links
                .mapper
                .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?,
        )
    };
    let template = store
        .value_symbol_links(target)
        .and_then(|links| links.resolved_type)
        .ok_or(GenericInterfaceMemberError::InvalidMember(target))?;
    if let Some(cached) = cached {
        if !cached_instantiated_property_type_matches(
            store,
            template,
            cached,
            mapper,
            array_targets,
        ) {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
        }
        return Ok(cached);
    }
    let instantiated =
        instantiate_generic_member_type(store, template, mapper, array_targets, session)?;
    let links = store
        .value_symbol_links(symbol)
        .cloned()
        .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?;
    if links
        != (ValueSymbolLinks {
            resolved_type: None,
            target: Some(target),
            mapper: Some(mapper),
            name_type: store
                .value_symbol_links(target)
                .and_then(|links| links.name_type),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
    }
    assert!(store.set_value_symbol_links(
        symbol,
        ValueSymbolLinks {
            resolved_type: Some(instantiated),
            ..links
        },
    ));
    Ok(instantiated)
}

fn property_instantiation_error(
    type_: TypeId,
    error: &InstantiationError,
) -> GenericInterfaceMemberError {
    match error {
        InstantiationError::DepthLimit { .. }
        | InstantiationError::CountLimit { .. }
        | InstantiationError::Array(super::array_types::ArrayTypeError::Capacity(_))
        | InstantiationError::Reference(DirectGenericReferenceError::Capacity(_))
        | InstantiationError::Union(super::bootstrap::LiteralTypeCacheError::Capacity) => {
            GenericInterfaceMemberError::Capacity(type_)
        }
        _ => GenericInterfaceMemberError::UnsupportedPropertyType(type_),
    }
}

fn instantiate_generic_member_type(
    store: &mut CanonicalTypeMapperStore,
    template: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let indexed = match store
        .type_payload(template)
        .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(
            template,
        ))?
        .data()
    {
        TypeData::IndexedAccess(indexed) if indexed.access_flags == AccessFlags::NONE => {
            Some((indexed.object_type, indexed.index_type))
        }
        TypeData::IndexedAccess(_) => {
            return Err(GenericInterfaceMemberError::UnsupportedPropertyType(
                template,
            ));
        }
        _ => None,
    };
    let Some((object, index)) = indexed else {
        return instantiate_type_with_session(store, template, mapper, array_targets, session)
            .map_err(|error| property_instantiation_error(template, &error));
    };
    let object = instantiate_type_with_session(store, object, mapper, array_targets, session)
        .map_err(|error| property_instantiation_error(template, &error))?;
    let index = instantiate_type_with_session(store, index, mapper, array_targets, session)
        .map_err(|error| property_instantiation_error(template, &error))?;
    let name = indexed_property_name(store, index);
    if validate_direct_generic_reference(store, object).is_ok() {
        resolve_members_with_array_targets(store, object, array_targets)?;
    }
    let symbol = name.as_deref().and_then(|name| {
        store
            .type_payload(object)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source(name))
    });
    let Some(symbol) = symbol else {
        return indexed_signature_value_type(store, object, index).ok_or(
            GenericInterfaceMemberError::UnsupportedPropertyType(template),
        );
    };
    let checks = store
        .symbol(symbol)
        .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?
        .check_flags();
    if checks.contains(CheckFlags::MAPPED) {
        return store
            .resolve_mapped_symbol_type(symbol)
            .map_err(|_| GenericInterfaceMemberError::InvalidCachedProperty(symbol));
    }
    if checks.contains(CheckFlags::INSTANTIATED) {
        return demand_instantiated_property_type(store, object, symbol, array_targets, session);
    }
    store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))
}

fn indexed_property_name(store: &CanonicalTypeMapperStore, index: TypeId) -> Option<String> {
    match store.type_payload(index)?.data() {
        TypeData::Literal(literal) => match &literal.value {
            LiteralValue::String(name) => Some(ts_ast::normalize_js_string(name)),
            LiteralValue::Number(number) => Some(number.to_string()),
            _ => None,
        },
        _ => None,
    }
}

fn indexed_signature_value_type(
    store: &CanonicalTypeMapperStore,
    object: TypeId,
    index: TypeId,
) -> Option<TypeId> {
    let bootstrap = store.intrinsic_bootstrap()?;
    let record = store.type_payload(index)?;
    let numeric = if record.flags().intersects(TypeFlags::NUMBER_LIKE) {
        true
    } else if let TypeData::Literal(literal) = record.data()
        && let LiteralValue::String(name) = &literal.value
    {
        ts_jsnum::from_string(name).to_string() == *name
    } else if record.flags().intersects(TypeFlags::STRING_LIKE) {
        false
    } else {
        return None;
    };
    let structured = store.type_payload(object)?.data().structured()?;
    let indexes = structured.index_infos.as_deref()?;
    if numeric
        && let Some(value) = indexes.iter().find_map(|index| {
            let info = store.index_info(*index)?;
            (info.key_type() == bootstrap.number_type).then_some(info.value_type())
        })
    {
        return Some(value);
    }
    indexes.iter().find_map(|index| {
        let info = store.index_info(*index)?;
        (info.key_type() == bootstrap.string_type).then_some(info.value_type())
    })
}

fn cached_inherited_properties(
    store: &CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<Vec<SemanticSymbolId>>, GenericInterfaceMemberError> {
    let mut inherited = Vec::new();
    let mut names = shape
        .properties
        .iter()
        .map(|property| property.name.clone())
        .collect::<HashSet<_>>();
    for base in &shape.base_types {
        let Some(base) = mapped_inherited_type(store, shape, *base)? else {
            return Ok(None);
        };
        let properties = if validate_direct_generic_reference(store, base).is_ok() {
            let Some(members) = validate_generic_interface_members(store, base, array_targets)?
            else {
                return Ok(None);
            };
            members.properties
        } else if matches!(
            validate_resolved_declared_property_object(store, base),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        ) {
            store
                .type_payload(base)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.properties.clone())
                .unwrap_or_default()
        } else {
            return Err(GenericInterfaceMemberError::UnsupportedTarget(base));
        };
        for property in properties {
            let name = store
                .symbol(property)
                .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(property))?
                .name()
                .to_owned();
            if names.insert(name) {
                inherited.push(property);
            }
        }
    }
    Ok(Some(inherited))
}

fn mapped_inherited_type(
    store: &CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    type_: TypeId,
) -> Result<Option<TypeId>, GenericInterfaceMemberError> {
    if let Some(index) = shape
        .source_parameters
        .iter()
        .position(|parameter| *parameter == type_)
    {
        return shape
            .target_arguments
            .get(index)
            .copied()
            .map(Some)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target));
    }
    let this_type = store
        .type_payload(shape.target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => interface.this_type,
            _ => None,
        })
        .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target))?;
    if type_ == this_type {
        return Ok(Some(shape.reference));
    }
    let record = store
        .type_payload(type_)
        .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(type_))?;
    if matches!(record.data(), TypeData::Intrinsic(_) | TypeData::Literal(_)) {
        return Ok(Some(type_));
    }
    let reference = match validate_direct_generic_reference(store, type_) {
        Ok(reference) => reference,
        Err(_) if matches!(record.data(), TypeData::Interface(_)) => {
            return Ok(Some(type_));
        }
        Err(_) => return Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_)),
    };
    let mut arguments = Vec::with_capacity(reference.type_arguments.len());
    for argument in &reference.type_arguments {
        let Some(argument) = mapped_inherited_type(store, shape, *argument)? else {
            return Ok(None);
        };
        arguments.push(argument);
    }
    if arguments == reference.type_arguments {
        return Ok(Some(type_));
    }
    let TypeData::Interface(target) = store
        .type_payload(reference.target)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(reference.target))?
        .data()
    else {
        return Err(GenericInterfaceMemberError::InvalidTarget(reference.target));
    };
    let TypeCacheState::Allocated(cache) = &target.reference.object.instantiations else {
        return Err(GenericInterfaceMemberError::InvalidTarget(reference.target));
    };
    let Some(cached) = cache.get(&type_list_key(&arguments)).copied() else {
        return Ok(None);
    };
    let actual = validate_direct_generic_reference(store, cached)?;
    if actual.target != reference.target || actual.type_arguments != arguments {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(cached));
    }
    Ok(Some(cached))
}

fn materialize_inherited_members(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), GenericInterfaceMemberError> {
    let sources = mapper_parameters_for_target(store, shape.target, &shape.source_parameters)?;
    let targets = shape
        .target_arguments
        .iter()
        .copied()
        .chain(std::iter::once(shape.reference))
        .collect::<Vec<_>>();
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    for base in &shape.base_types {
        let resolved = instantiate_type_with_vector_and_session(
            store,
            *base,
            &sources,
            &targets,
            array_targets,
            &mut session,
        )
        .map_err(|error| property_instantiation_error(*base, &error))?;
        if validate_direct_generic_reference(store, resolved).is_ok() {
            resolve_members_with_array_targets(store, resolved, array_targets)?;
        } else if !matches!(
            validate_resolved_declared_property_object(store, resolved),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        ) {
            return Err(GenericInterfaceMemberError::UnsupportedTarget(resolved));
        }
    }
    Ok(())
}

fn validate_shape(
    store: &CanonicalTypeMapperStore,
    reference: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<GenericInterfaceShape, GenericInterfaceMemberError> {
    let direct = validate_direct_generic_reference(store, reference)?;
    let mut active = Vec::new();
    let mut validated = HashSet::new();
    let (_, source_parameters, _, properties) = validate_declared_target(
        store,
        direct.target,
        array_targets,
        &mut active,
        &mut validated,
    )?;
    let base_types = store
        .type_payload(direct.target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => Some(
                interface
                    .resolved_base_types
                    .as_deref()
                    .unwrap_or_default()
                    .to_vec(),
            ),
            _ => None,
        })
        .ok_or(GenericInterfaceMemberError::InvalidTarget(direct.target))?;
    let mut shape = GenericInterfaceShape {
        reference,
        target: direct.target,
        source_parameters,
        target_arguments: direct.type_arguments,
        properties,
        base_types,
        inherited_properties: Vec::new(),
        inherited_members_ready: false,
    };
    if let Some(inherited) = cached_inherited_properties(store, &shape, array_targets)? {
        shape.inherited_properties = inherited;
        shape.inherited_members_ready = true;
    }
    if reference != shape.target {
        let mut target_shape = GenericInterfaceShape {
            reference: shape.target,
            target: shape.target,
            source_parameters: shape.source_parameters.clone(),
            target_arguments: shape.source_parameters.clone(),
            properties: shape.properties.clone(),
            base_types: shape.base_types.clone(),
            inherited_properties: Vec::new(),
            inherited_members_ready: false,
        };
        if let Some(inherited) = cached_inherited_properties(store, &target_shape, array_targets)? {
            target_shape.inherited_properties = inherited;
            target_shape.inherited_members_ready = true;
        }
        validate_warm_members(store, &target_shape, array_targets)?;
    }
    Ok(shape)
}

fn validate_declared_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut Vec<TypeId>,
    validated: &mut HashSet<TypeId>,
) -> Result<DeclaredTargetHeader, GenericInterfaceMemberError> {
    if store
        .type_payload(target)
        .is_some_and(|record| record.object_flags().contains(ObjectFlags::CLASS))
    {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    }
    if validated.contains(&target) {
        return declared_target_header(store, target);
    }
    if active.contains(&target) {
        return declared_target_header(store, target);
    }
    let (owner, source_parameters, declared_members, mut properties) =
        declared_target_header(store, target)?;
    let owner_record = store
        .symbol(owner)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let Some(declarations) = owner_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    };
    if declarations
        .iter()
        .any(|declaration| !valid_generic_interface_declaration_owner(store, owner, *declaration))
    {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    }

    let mapper_parameters = mapper_parameters_for_target(store, target, &source_parameters)?;
    active.push(target);
    let base_types = store
        .type_payload(target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => Some(
                interface
                    .resolved_base_types
                    .as_deref()
                    .unwrap_or_default()
                    .to_vec(),
            ),
            _ => None,
        })
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    for base in base_types {
        if let Ok(reference) = validate_direct_generic_reference(store, base) {
            if active.contains(&reference.target) {
                return Err(GenericInterfaceMemberError::InvalidTarget(target));
            }
            member_type_requires_instantiation(store, base, &mapper_parameters, array_targets)?;
            validate_declared_target(store, reference.target, array_targets, active, validated)?;
        } else if !matches!(
            validate_resolved_declared_property_object(store, base),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        ) {
            return Err(GenericInterfaceMemberError::UnsupportedTarget(base));
        }
    }
    for property in &mut properties {
        property.requires_proxy = member_type_requires_instantiation(
            store,
            property.type_,
            &mapper_parameters,
            array_targets,
        )?;
        validate_nested_reference_targets(
            store,
            property.type_,
            array_targets,
            active,
            validated,
            &mut HashSet::new(),
        )?;
    }
    let popped = active
        .pop()
        .expect("one active generic interface target owns its validation frame");
    debug_assert_eq!(popped, target);
    validated.insert(target);
    Ok((owner, source_parameters, declared_members, properties))
}

fn member_type_requires_instantiation(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, GenericInterfaceMemberError> {
    if let Some(TypeData::IndexedAccess(indexed)) = store
        .type_payload(type_)
        .map(super::type_records::TypeRecord::data)
    {
        if indexed.access_flags != AccessFlags::NONE {
            return Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_));
        }
        member_type_requires_instantiation(
            store,
            indexed.object_type,
            mapper_parameters,
            array_targets,
        )?;
        member_type_requires_instantiation(
            store,
            indexed.index_type,
            mapper_parameters,
            array_targets,
        )?;
        return Ok(true);
    }
    match instantiable_member_type_contains_variables(
        store,
        type_,
        mapper_parameters,
        array_targets,
    ) {
        Ok(requires_instantiation) => Ok(requires_instantiation),
        Err(_)
            if matches!(
                validate_resolved_declared_property_object(store, type_),
                DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
            ) =>
        {
            Ok(false)
        }
        Err(_) => Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_)),
    }
}

fn mapper_parameters_for_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    source_parameters: &[TypeId],
) -> Result<Vec<TypeId>, GenericInterfaceMemberError> {
    let this_type = store
        .type_payload(target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => interface.this_type,
            _ => None,
        })
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    Ok(source_parameters
        .iter()
        .copied()
        .chain(std::iter::once(this_type))
        .collect())
}

#[allow(clippy::too_many_lines)] // One fail-closed proof covers the complete admitted source surface.
fn declared_target_header(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<DeclaredTargetHeader, GenericInterfaceMemberError> {
    let record = store
        .type_payload(target)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    };
    let owner = record
        .symbol()
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let source_parameters = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .filter(|parameters| !parameters.is_empty())
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?
        .to_vec();
    let all_parameters = interface
        .all_type_parameters
        .as_deref()
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let this_type = interface
        .this_type
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let declared_members = interface.declared_members;
    let declared_table = declared_members
        .map(|members| {
            store
                .symbol_table(members)
                .ok_or(GenericInterfaceMemberError::InvalidTarget(target))
        })
        .transpose()?;
    let raw_members = owner_record
        .members()
        .filter(|members| Some(*members) != declared_members)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let raw_table = store
        .symbol_table(raw_members)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let structured = &interface.reference.object.structured;
    let allowed_target_flags = ObjectFlags::INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED;
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags().contains(ObjectFlags::CLASS)
        || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK
            != (ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        || !(record.object_flags() & !allowed_target_flags).is_empty()
        || record.alias().is_some()
        || owner_record.flags() != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(target)
        || all_parameters.len() != source_parameters.len() + 1
        || &all_parameters[..source_parameters.len()] != source_parameters.as_slice()
        || all_parameters.last().copied() != Some(this_type)
        || interface.outer_type_parameter_count != 0
        || !interface.base_types_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface
            .resolved_base_types
            .as_ref()
            .is_some_and(Vec::is_empty)
        || !interface.declared_members_resolved
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || (!record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            && structured != &StructuredTypeData::default())
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || structured.constrained != ConstrainedTypeData::default()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || source_parameters
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != source_parameters.len()
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let Some(this_record) = store.type_payload(this_type) else {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    };
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || this_record.symbol() != Some(owner)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(target)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }

    let Some(owner_declarations) = owner_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    };
    if owner_declarations
        .iter()
        .any(|declaration| !valid_generic_interface_declaration_owner(store, owner, *declaration))
    {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    }
    let mut parameter_symbols = HashSet::with_capacity(source_parameters.len());
    for parameter in &source_parameters {
        let parameter_symbol = cached_ordinary_type_parameter_owner(store, *parameter)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
        let parameter_record = store
            .symbol(parameter_symbol)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
        if store.get_parent_of_symbol(parameter_symbol) != Some(owner)
            || raw_table
                .get(parameter_record.name())
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(parameter_symbol)
            || !parameter_symbols.insert(parameter_symbol)
        {
            return Err(GenericInterfaceMemberError::InvalidTarget(target));
        }
    }
    let declared_count = declared_table.map_or(0, ts_binder::semantic::SymbolTable::len);
    if raw_table.len() != declared_count + parameter_symbols.len() {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }

    let mut properties = Vec::with_capacity(declared_count);
    let mut seen = HashSet::with_capacity(declared_count);
    let mut seen_declarations = HashSet::with_capacity(declared_count);
    for (name, symbol) in declared_table
        .into_iter()
        .flat_map(ts_binder::semantic::SymbolTable::iter)
    {
        if !seen.insert(symbol) {
            return Err(GenericInterfaceMemberError::InvalidMember(symbol));
        }
        let property = store
            .symbol(symbol)
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let Some(declarations) = property
            .declarations()
            .filter(|declarations| !declarations.is_empty())
        else {
            return Err(GenericInterfaceMemberError::InvalidMember(symbol));
        };
        let mut earliest = None;
        for declaration in declarations {
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(*declaration)
            else {
                return Err(GenericInterfaceMemberError::InvalidMember(symbol));
            };
            let Some(owner_index) = owner_declarations
                .iter()
                .position(|owner_declaration| *owner_declaration == parent)
            else {
                return Err(GenericInterfaceMemberError::InvalidMember(symbol));
            };
            if !matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            ) || !declaration.is_for(parent.arena, parent.file)
                || !seen_declarations.insert(*declaration)
            {
                return Err(GenericInterfaceMemberError::InvalidMember(symbol));
            }
            let position = (owner_index, *declaration);
            if earliest.is_none_or(|current| position < current) {
                earliest = Some(position);
            }
        }
        let (owner_index, declaration) =
            earliest.ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        let allowed_checks = CheckFlags::READONLY;
        let links = store
            .value_symbol_links(symbol)
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let type_ = links
            .resolved_type
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let optional_type_is_valid = optional_member_type_is_normalized(
            store,
            type_,
            property.flags().contains(SymbolFlags::OPTIONAL),
        );
        if !property.flags().contains(SymbolFlags::PROPERTY)
            || property.flags().without(allowed_flags) != SymbolFlags::NONE
            || property.check_flags().bits() & !allowed_checks.bits() != 0
            || property.name() != name
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || property.name().as_utf8().is_none()
            || property
                .value_declaration()
                .is_none_or(|value| !declarations.contains(&value))
            || store.get_parent_of_symbol(symbol) != Some(owner)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || raw_table
                .get(property.name())
                .and_then(|member| store.get_merged_symbol(member))
                != Some(symbol)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            || store.type_payload(type_).is_none()
            || !optional_type_is_valid
        {
            return Err(GenericInterfaceMemberError::InvalidMember(symbol));
        }
        properties.push((
            owner_index,
            declaration,
            DeclaredProperty {
                symbol,
                name: property.name().to_owned(),
                type_,
                requires_proxy: false,
            },
        ));
    }
    if raw_table.iter().any(|(name, symbol)| {
        let Some(canonical) = store.get_merged_symbol(symbol) else {
            return true;
        };
        (!seen.contains(&canonical) && !parameter_symbols.contains(&canonical))
            || store
                .symbol(symbol)
                .is_none_or(|record| record.name() != name)
    }) {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    properties.sort_unstable_by_key(|(owner_index, declaration, _)| (*owner_index, *declaration));
    if properties
        .windows(2)
        .any(|pair| (pair[0].0, pair[0].1) >= (pair[1].0, pair[1].1))
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let properties = properties
        .into_iter()
        .map(|(_, _, property)| property)
        .collect();
    Ok((owner, source_parameters, declared_members, properties))
}

fn valid_generic_interface_declaration_owner(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: ts_ast::NodeRef,
) -> bool {
    if store.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration) {
        return false;
    }
    let Some(record) = store.symbol(owner) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(exported) = store.source_node_is_exported(declaration) else {
        return false;
    };
    let container = match store.source_node_kind(parent) {
        Some(SyntaxKind::SourceFile) => parent,
        Some(SyntaxKind::ModuleBlock) => {
            let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(parent) else {
                return false;
            };
            if store.source_node_kind(module) != Some(SyntaxKind::ModuleDeclaration) {
                return false;
            }
            module
        }
        _ => return false,
    };
    let Some(raw_parent) = record.parent() else {
        return !exported;
    };
    if store.source_node_kind(parent) == Some(SyntaxKind::SourceFile) && !exported {
        return false;
    }
    let Some(parent_symbol) = store.get_parent_of_symbol(owner) else {
        return false;
    };
    let Some(parent_record) = store.symbol(parent_symbol) else {
        return false;
    };
    let raw_contains_container = store
        .symbol(raw_parent)
        .and_then(|parent| parent.declarations())
        .is_some_and(|declarations| declarations.contains(&container));
    let merged_contains_container = parent_record
        .declarations()
        .is_some_and(|declarations| declarations.contains(&container));
    parent_record.flags().intersects(SymbolFlags::MODULE)
        && (raw_contains_container || merged_contains_container)
        && parent_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(record.name()))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            == Some(owner)
}

fn optional_member_type_is_normalized(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    optional: bool,
) -> bool {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    if !bootstrap.options.strict_null_checks || !optional {
        return true;
    }
    let sentinel = bootstrap.undefined_or_missing_type;
    if type_ == sentinel
        || bootstrap.options.exact_optional_property_types && type_ == bootstrap.undefined_type
    {
        return true;
    }
    store.type_payload(type_).is_some_and(|record| {
        record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN)
            || matches!(
                record.data(),
                TypeData::Union(union)
                    if {
                        let has_sentinel = union.union.types.contains(&sentinel);
                        let has_undefined = union.union.types.contains(&bootstrap.undefined_type);
                        if bootstrap.options.exact_optional_property_types {
                            has_sentinel != has_undefined
                        } else {
                            has_sentinel
                        }
                    }
            )
    })
}

fn cached_instantiated_property_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    cached: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    if let Some(TypeData::IndexedAccess(indexed)) = store
        .type_payload(template)
        .map(super::type_records::TypeRecord::data)
    {
        if indexed.access_flags != AccessFlags::NONE {
            return false;
        }
        let Some(object) = mapped_index_component(store, indexed.object_type, mapper) else {
            return false;
        };
        let Some(index) = mapped_index_component(store, indexed.index_type, mapper) else {
            return false;
        };
        let named = indexed_property_name(store, index).and_then(|name| {
            store
                .type_payload(object)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source(&name))
                .and_then(|symbol| store.value_symbol_links(symbol))
                .and_then(|links| links.resolved_type)
        });
        return named.or_else(|| indexed_signature_value_type(store, object, index))
            == Some(cached);
    }
    if cached != template
        && matches!(
            store
                .type_payload(cached)
                .map(super::type_records::TypeRecord::data),
            Some(TypeData::Union(_))
        )
    {
        let valid_union = match array_targets {
            Some(targets) => store
                .validate_cached_union_result_with_array_targets(targets, cached, None)
                .is_ok(),
            None => store.validate_cached_union_result(cached, None).is_ok(),
        };
        if !valid_union {
            return false;
        }
    }
    instantiated_member_type_matches(store, template, cached, mapper, array_targets)
        .unwrap_or(false)
}

fn mapped_index_component(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: TypeMapperId,
) -> Option<TypeId> {
    let record = store.type_payload(type_)?;
    if matches!(record.data(), TypeData::TypeParameter(_)) {
        store.map_type(mapper, type_)
    } else {
        Some(type_)
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_nested_reference_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active_targets: &mut Vec<TypeId>,
    validated_targets: &mut HashSet<TypeId>,
    visited_types: &mut HashSet<TypeId>,
) -> Result<(), GenericInterfaceMemberError> {
    if !visited_types.insert(type_) {
        return Ok(());
    }
    let record = store
        .type_payload(type_)
        .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(type_))?;
    match record.data() {
        TypeData::Union(data) => {
            for constituent in &data.union.types {
                validate_nested_reference_targets(
                    store,
                    *constituent,
                    array_targets,
                    active_targets,
                    validated_targets,
                    visited_types,
                )?;
            }
        }
        TypeData::IndexedAccess(indexed) => {
            validate_nested_reference_targets(
                store,
                indexed.object_type,
                array_targets,
                active_targets,
                validated_targets,
                visited_types,
            )?;
            validate_nested_reference_targets(
                store,
                indexed.index_type,
                array_targets,
                active_targets,
                validated_targets,
                visited_types,
            )?;
        }
        TypeData::TypeReference(_) | TypeData::Interface(_) => {
            if let Some(targets) = array_targets
                && let Some(array) = store
                    .canonical_array_reference_with_targets(targets, type_)
                    .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(type_))?
            {
                validate_nested_reference_targets(
                    store,
                    array.element_type,
                    array_targets,
                    active_targets,
                    validated_targets,
                    visited_types,
                )?;
            } else if let Ok(reference) = validate_direct_generic_reference(store, type_) {
                validate_declared_target(
                    store,
                    reference.target,
                    array_targets,
                    active_targets,
                    validated_targets,
                )?;
                for argument in reference.type_arguments {
                    validate_nested_reference_targets(
                        store,
                        argument,
                        array_targets,
                        active_targets,
                        validated_targets,
                        visited_types,
                    )?;
                }
            }
        }
        _ => {}
    }
    visited_types.remove(&type_);
    Ok(())
}

#[allow(clippy::too_many_lines)] // Warm replay validates the complete transactional cache shape.
fn validate_warm_members(
    store: &CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<InstantiatedInterfaceMembers>, GenericInterfaceMemberError> {
    let record = store.type_payload(shape.reference).ok_or(
        GenericInterfaceMemberError::InvalidCachedMembers(shape.reference),
    )?;
    let structured =
        record
            .data()
            .structured()
            .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                shape.reference,
            ))?;
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        if structured != &StructuredTypeData::default() {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                shape.reference,
            ));
        }
        return Ok(None);
    }
    if !shape.inherited_members_ready {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            shape.reference,
        ));
    }
    let expected_count = shape
        .properties
        .len()
        .checked_add(shape.inherited_properties.len())
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
            shape.reference,
        ))?;
    let properties = match structured.properties.as_deref() {
        None if expected_count == 0 => &[][..],
        Some(properties) if properties.len() == expected_count && !properties.is_empty() => {
            properties
        }
        _ => {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                shape.reference,
            ));
        }
    };
    let table = match structured.members {
        None if properties.is_empty() => None,
        Some(members) if !properties.is_empty() => Some(
            store
                .symbol_table(members)
                .filter(|table| table.len() == properties.len())
                .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                    shape.reference,
                ))?,
        ),
        _ => {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                shape.reference,
            ));
        }
    };
    if structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || structured.constrained != ConstrainedTypeData::default()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            shape.reference,
        ));
    }
    let (own_properties, inherited_properties) = properties.split_at(shape.properties.len());
    let mapper_targets = shape
        .target_arguments
        .iter()
        .copied()
        .chain(std::iter::once(shape.reference))
        .collect::<Vec<_>>();
    let all_parameters = shape
        .source_parameters
        .iter()
        .copied()
        .chain(std::iter::once(
            store
                .type_payload(shape.target)
                .and_then(|record| match record.data() {
                    TypeData::Interface(interface) => interface.this_type,
                    _ => None,
                })
                .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target))?,
        ))
        .collect::<Vec<_>>();
    let mapper = own_properties
        .iter()
        .zip(&shape.properties)
        .find_map(|(property, source)| {
            if source.requires_proxy {
                store
                    .value_symbol_links(*property)
                    .and_then(|links| links.mapper)
            } else {
                None
            }
        });
    if mapper.is_none()
        && shape
            .properties
            .iter()
            .any(|property| property.requires_proxy)
        || mapper.is_some_and(|mapper| {
            store.type_mapper_has_exact_endpoints(mapper, &all_parameters, &mapper_targets)
                != Some(true)
        })
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            shape.reference,
        ));
    }
    for (property, source) in own_properties.iter().zip(&shape.properties) {
        let symbol =
            store
                .symbol(*property)
                .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(
                    *property,
                ))?;
        let target = store
            .symbol(source.symbol)
            .ok_or(GenericInterfaceMemberError::InvalidMember(source.symbol))?;
        if !source.requires_proxy {
            if *property != source.symbol
                || table.and_then(|table| table.get(symbol.name())) != Some(source.symbol)
            {
                return Err(GenericInterfaceMemberError::InvalidCachedProperty(
                    *property,
                ));
            }
            continue;
        }
        let mapper = mapper.ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
            shape.reference,
        ))?;
        let links = store.value_symbol_links(*property).ok_or(
            GenericInterfaceMemberError::InvalidCachedProperty(*property),
        )?;
        let expected_checks = CheckFlags::INSTANTIATED
            | (target.check_flags()
                & (CheckFlags::READONLY
                    | CheckFlags::LATE
                    | CheckFlags::OPTIONAL_PARAMETER
                    | CheckFlags::REST_PARAMETER));
        if symbol.flags() != (target.flags() | SymbolFlags::TRANSIENT)
            || symbol.check_flags() != expected_checks
            || symbol.name() != target.name()
            || symbol.declarations() != target.declarations()
            || symbol.value_declaration() != target.value_declaration()
            || symbol.parent() != target.parent()
            || symbol.members().is_some()
            || symbol.exports().is_some()
            || symbol.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || table.and_then(|table| table.get(symbol.name())) != Some(*property)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    target: Some(source.symbol),
                    mapper: Some(mapper),
                    name_type: store
                        .value_symbol_links(source.symbol)
                        .and_then(|links| links.name_type),
                    ..ValueSymbolLinks::default()
                })
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
            || links.resolved_type.is_some_and(|type_| {
                !cached_instantiated_property_type_matches(
                    store,
                    source.type_,
                    type_,
                    mapper,
                    array_targets,
                )
            })
        {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(
                *property,
            ));
        }
    }
    for (actual, expected) in inherited_properties.iter().zip(&shape.inherited_properties) {
        let record = store
            .symbol(*actual)
            .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(*actual))?;
        if actual != expected || table.and_then(|table| table.get(record.name())) != Some(*actual) {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(*actual));
        }
    }
    Ok(Some(InstantiatedInterfaceMembers {
        reference: shape.reference,
        target: shape.target,
        mapper,
        members: structured.members,
        properties: properties.to_vec(),
    }))
}

fn prepare_cold_members(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
) -> Result<ColdMembersPlan, GenericInterfaceMemberError> {
    let count = shape
        .properties
        .len()
        .checked_add(shape.inherited_properties.len())
        .ok_or(GenericInterfaceMemberError::Capacity(shape.reference))?;
    let proxy_count = shape
        .properties
        .iter()
        .filter(|property| property.requires_proxy)
        .count();
    let table = if count == 0 {
        None
    } else {
        Some(prepare_member_table(shape.reference, count)?)
    };
    if !store.try_reserve_checker_symbol_allocations(proxy_count, usize::from(count != 0))
        || !store.try_reserve_mappers(usize::from(proxy_count != 0))
        || !store.try_reserve_value_symbol_links(proxy_count)
    {
        return Err(GenericInterfaceMemberError::Capacity(shape.reference));
    }
    let this_type = store
        .type_payload(shape.target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => interface.this_type,
            _ => None,
        })
        .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target))?;
    let mapper_sources = shape
        .source_parameters
        .iter()
        .copied()
        .chain(std::iter::once(this_type))
        .collect::<Vec<_>>();
    let mapper_targets = shape
        .target_arguments
        .iter()
        .copied()
        .chain(std::iter::once(shape.reference))
        .collect::<Vec<_>>();
    let mut properties = Vec::with_capacity(count);
    for source in &shape.properties {
        if !source.requires_proxy {
            properties.push(ColdPropertyPlan::Reused {
                symbol: source.symbol,
                name: source.name.clone(),
            });
            continue;
        }
        let target = store
            .symbol(source.symbol)
            .ok_or(GenericInterfaceMemberError::InvalidMember(source.symbol))?;
        let mut data =
            SymbolData::new(target.flags() | SymbolFlags::TRANSIENT, source.name.clone());
        data.check_flags = CheckFlags::INSTANTIATED
            | (target.check_flags()
                & (CheckFlags::READONLY
                    | CheckFlags::LATE
                    | CheckFlags::OPTIONAL_PARAMETER
                    | CheckFlags::REST_PARAMETER));
        data.declarations = target.declarations().map(<[_]>::to_vec);
        data.value_declaration = target.value_declaration();
        data.parent = target.parent();
        properties.push(ColdPropertyPlan::Proxy {
            target: source.symbol,
            data,
            name_type: store
                .value_symbol_links(source.symbol)
                .and_then(|links| links.name_type),
        });
    }
    for inherited in &shape.inherited_properties {
        let name = store
            .symbol(*inherited)
            .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(
                *inherited,
            ))?
            .name()
            .to_owned();
        properties.push(ColdPropertyPlan::Reused {
            symbol: *inherited,
            name,
        });
    }
    Ok(ColdMembersPlan {
        mapper_sources,
        mapper_targets,
        requires_mapper: proxy_count != 0,
        table,
        properties,
    })
}

fn publish_cold_members(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    plan: ColdMembersPlan,
) -> InstantiatedInterfaceMembers {
    let mapper = plan.requires_mapper.then(|| {
        store
            .new_type_mapper(plan.mapper_sources, plan.mapper_targets)
            .expect("prevalidated mapper endpoints remain store-owned")
    });
    let members = plan
        .table
        .map(|table| store.alloc_prepared_symbol_table(table));
    let mut properties = Vec::with_capacity(plan.properties.len());
    for property in plan.properties {
        let (name, symbol) = match property {
            ColdPropertyPlan::Reused { symbol, name } => (name, symbol),
            ColdPropertyPlan::Proxy {
                target,
                data,
                name_type,
            } => {
                let name = data.name.clone();
                let symbol = store
                    .alloc_symbol(data)
                    .expect("reserved instantiated property allocation must succeed");
                assert!(store.set_value_symbol_links(
                    symbol,
                    ValueSymbolLinks {
                        target: Some(target),
                        mapper,
                        name_type,
                        ..ValueSymbolLinks::default()
                    },
                ));
                (name, symbol)
            }
        };
        assert_eq!(
            store.insert_symbol(
                members.expect("every planned property has a prepared member table"),
                name,
                symbol,
            ),
            Some(None)
        );
        properties.push(symbol);
    }
    assert!(store.set_structured_type_members(
        shape.reference,
        members,
        (!properties.is_empty()).then(|| properties.clone()),
        None,
        None,
        None,
    ));
    InstantiatedInterfaceMembers {
        reference: shape.reference,
        target: shape.target,
        mapper,
        members,
        properties,
    }
}

fn prepare_member_table(
    reference: TypeId,
    count: usize,
) -> Result<PreparedSymbolTable, GenericInterfaceMemberError> {
    PreparedSymbolTable::new(count).ok_or(GenericInterfaceMemberError::Capacity(reference))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    };
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    };
    use ts_parser::{ParseResult, parse_source_file};

    fn checker_context(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'_> {
        checker_context_with_module_state(parsed, file, options, CanonicalModuleState::Script)
    }

    fn checker_context_with_module_state(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
        module_state: CanonicalModuleState,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-member-unit.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            options,
        )
        .unwrap()
    }

    fn source_symbol(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        name: &str,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let name_node = match &record.data {
                    NodeData::InterfaceDeclaration(interface) => interface.name,
                    NodeData::TypeAliasDeclaration(alias) => alias.name,
                    NodeData::VariableDeclaration(variable) => variable.name,
                    _ => return None,
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap_or_else(|| panic!("missing source declaration {name}"));
        context
            .file(file)
            .unwrap()
            .1
            .symbol(declaration)
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap()
    }

    fn publish_generic_target_for_test(
        context: &mut CanonicalCheckerContext<'_>,
        target: TypeId,
        properties: &[(&str, TypeId)],
        bases: Option<Vec<TypeId>>,
    ) {
        let owner = context
            .store()
            .type_payload(target)
            .unwrap()
            .symbol()
            .unwrap();
        let raw = context.store().symbol(owner).unwrap().members().unwrap();
        let source_properties = properties
            .iter()
            .map(|(name, type_)| {
                let symbol = context
                    .store()
                    .symbol_table(raw)
                    .and_then(|table| table.get_source(name))
                    .unwrap();
                ((*name).to_owned(), symbol, *type_)
            })
            .collect::<Vec<_>>();
        let store = context.store_mut_for_test();
        match bases {
            None => assert!(store.publish_interface_no_base_resolution(target)),
            Some(bases) => {
                assert!(store.set_interface_base_resolution(target, true, None, Some(bases),));
            }
        }
        let members = (!source_properties.is_empty()).then(|| store.alloc_symbol_table());
        for (name, symbol, type_) in source_properties {
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                store.insert_symbol(
                    members.expect("a declared property owns a member table"),
                    EscapedName::source(name),
                    symbol,
                ),
                Some(None),
            );
        }
        assert!(store.set_interface_declared_members(target, true, members, None, None, None));
    }

    #[test]
    fn member_table_capacity_failure_is_typed_before_publication() {
        let mut store = CanonicalTypeMapperStore::new();
        let reference = store
            .alloc_intrinsic_type(TypeFlags::ANY, "capacity-reference")
            .unwrap();

        assert!(matches!(
            prepare_member_table(reference, usize::MAX),
            Err(GenericInterfaceMemberError::Capacity(type_)) if type_ == reference
        ));
        assert_eq!(store.mapper_len(), 0);
        assert_eq!(store.symbol_len(), 0);
        assert_eq!(store.symbol_store().symbol_table_len(), 0);
    }

    #[test]
    fn exact_optional_unions_do_not_retain_missing_and_undefined_together() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            })
            .unwrap();
        let (string, undefined, missing) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.undefined_type,
                bootstrap.missing_type,
            )
        };
        let normalized = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, string])
            .unwrap();
        let unnormalized = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, missing, string])
            .unwrap();

        assert!(optional_member_type_is_normalized(&store, undefined, true));
        assert!(optional_member_type_is_normalized(&store, missing, true));
        assert!(optional_member_type_is_normalized(&store, normalized, true));
        assert!(!optional_member_type_is_normalized(
            &store,
            unnormalized,
            true,
        ));
    }

    #[test]
    fn namespace_owned_and_exported_generic_interfaces_keep_canonical_parent_identity() {
        for (source, state, file) in [
            (
                "declare namespace Model { interface Box<T> { value: T } }",
                CanonicalModuleState::Script,
                FileId::new(6_205),
            ),
            (
                "export interface Box<T> { value: T }",
                CanonicalModuleState::External,
                FileId::new(6_206),
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let context = checker_context_with_module_state(
                &parsed,
                file,
                CanonicalCheckerOptions::default(),
                state,
            );
            let owner = source_symbol(&parsed, file, &context, "Box");
            let declaration = context
                .store()
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap()[0];

            assert!(
                valid_generic_interface_declaration_owner(context.store(), owner, declaration),
                "generic declaration owner was rejected for {source}",
            );
            assert!(context.store().symbol(owner).unwrap().parent().is_some());
        }
    }

    #[test]
    fn reopened_namespaces_preserve_the_canonical_parent_of_generic_interfaces() {
        let first = parse_source_file("declare namespace Models { interface First<T> {} }");
        let second =
            parse_source_file("declare namespace Models { interface Box<T> { value: T } }");
        assert!(first.diagnostics.is_empty(), "{:?}", first.diagnostics);
        assert!(second.diagnostics.is_empty(), "{:?}", second.diagnostics);
        let first_file = FileId::new(6_211);
        let second_file = FileId::new(6_212);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path) in [
            (&first, first_file, "\"/project/namespace-first.ts\""),
            (&second, second_file, "\"/project/namespace-second.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (parsed, file) in [(&first, first_file), (&second, second_file)] {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(first_file, &first.arena), (second_file, &second.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let owner = source_symbol(&second, second_file, &context, "Box");
        let declaration = context
            .store()
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let raw_parent = context.store().symbol(owner).unwrap().parent().unwrap();
        let canonical_parent = context.store().get_parent_of_symbol(owner).unwrap();

        assert!(valid_generic_interface_declaration_owner(
            context.store(),
            owner,
            declaration,
        ));
        assert_eq!(
            context.store().get_merged_symbol(raw_parent),
            Some(canonical_parent),
        );
    }

    #[test]
    fn merged_generic_interface_members_keep_declaration_order() {
        let parsed = parse_source_file(concat!(
            "interface Box<T> { first: T }\n",
            "interface Box<T> { second: T }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_209);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let owner = source_symbol(&parsed, file, &context, "Box");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let parameter = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("merged Box declarations must share one generic target"),
        };
        assert_eq!(
            context
                .store()
                .symbol(owner)
                .unwrap()
                .declarations()
                .unwrap()
                .len(),
            2,
        );
        publish_generic_target_for_test(
            &mut context,
            target,
            &[("first", parameter), ("second", parameter)],
            None,
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();

        let members = context
            .store_mut_for_test()
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        let names = members
            .properties()
            .iter()
            .map(|symbol| {
                context
                    .store()
                    .symbol(*symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned()
            })
            .collect::<Vec<_>>();

        assert_eq!(names, ["first", "second"]);
        for name in &names {
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolve_generic_interface_property(reference, name, None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                string,
            );
        }
    }

    #[test]
    fn generic_interface_inherits_instantiated_base_properties_in_source_order() {
        let parsed = parse_source_file(concat!(
            "interface Base<T> { value: T; fixed: string }\n",
            "interface Derived<T> extends Base<T> { own: T }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_207);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let base_symbol = source_symbol(&parsed, file, &context, "Base");
        let derived_symbol = source_symbol(&parsed, file, &context, "Derived");
        let base = context.get_declared_type_of_symbol(base_symbol).unwrap();
        let derived = context.get_declared_type_of_symbol(derived_symbol).unwrap();
        let (base_parameter, derived_parameter) = {
            let TypeData::Interface(base_data) = context.store().type_payload(base).unwrap().data()
            else {
                panic!("Base must retain a generic interface target")
            };
            let TypeData::Interface(derived_data) =
                context.store().type_payload(derived).unwrap().data()
            else {
                panic!("Derived must retain a generic interface target")
            };
            (
                base_data
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                derived_data
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
            )
        };
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        publish_generic_target_for_test(
            &mut context,
            base,
            &[("value", base_parameter), ("fixed", string)],
            None,
        );
        let base_template = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(base, &[derived_parameter])
            .unwrap();
        publish_generic_target_for_test(
            &mut context,
            derived,
            &[("own", derived_parameter)],
            Some(vec![base_template]),
        );
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(derived, &[number])
            .unwrap();
        let members = context
            .store_mut_for_test()
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        let names = members
            .properties()
            .iter()
            .map(|property| {
                context
                    .store()
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
                    .to_owned()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["own", "value", "fixed"]);
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(reference, "value", None)
                .unwrap()
                .unwrap()
                .type_id(),
            number,
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(reference, "fixed", None)
                .unwrap()
                .unwrap()
                .type_id(),
            string,
        );
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_members(reference, None),
            Ok(members),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            warm,
        );
    }

    #[test]
    fn indexed_generic_member_substitution_selects_the_instantiated_property_type() {
        let parsed = parse_source_file(concat!(
            "interface Shape { value: string }\n",
            "interface Pick<T> { selected: T[\"value\"] }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_208);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let shape_symbol = source_symbol(&parsed, file, &context, "Shape");
        let pick_symbol = source_symbol(&parsed, file, &context, "Pick");
        let shape = context.get_declared_type_of_symbol(shape_symbol).unwrap();
        let target = context.get_declared_type_of_symbol(pick_symbol).unwrap();
        let parameter = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("Pick must retain its generic interface target"),
        };
        let key = context
            .store_mut_for_test()
            .regular_string_literal_type("value".to_owned())
            .unwrap();
        let template = context
            .store_mut_for_test()
            .alloc_indexed_access_type(parameter, key, AccessFlags::NONE)
            .unwrap();
        publish_generic_target_for_test(&mut context, target, &[("selected", template)], None);
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target, &[shape])
            .unwrap();
        let expected = context.store().intrinsic_bootstrap().unwrap().string_type;

        let selected = context
            .store_mut_for_test()
            .resolve_generic_interface_property(reference, "selected", None)
            .unwrap()
            .unwrap();

        assert_eq!(selected.type_id(), expected);
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(reference, "selected", None),
            Ok(Some(selected)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
            ),
            warm,
        );
    }

    #[test]
    fn indexed_generic_members_fall_back_to_canonical_string_index_signatures() {
        let parsed = parse_source_file(concat!(
            "interface Shape { [name: string]: number }\n",
            "interface Pick<T> { named: T[\"missing\"]; broad: T[string] }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_210);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let shape_symbol = source_symbol(&parsed, file, &context, "Shape");
        let pick_symbol = source_symbol(&parsed, file, &context, "Pick");
        let shape = context.get_declared_type_of_symbol(shape_symbol).unwrap();
        let target = context.get_declared_type_of_symbol(pick_symbol).unwrap();
        let parameter = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("Pick must retain its generic interface target"),
        };
        let missing = context
            .store_mut_for_test()
            .regular_string_literal_type("missing".to_owned())
            .unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let named = context
            .store_mut_for_test()
            .alloc_indexed_access_type(parameter, missing, AccessFlags::NONE)
            .unwrap();
        let broad = context
            .store_mut_for_test()
            .alloc_indexed_access_type(parameter, string, AccessFlags::NONE)
            .unwrap();
        publish_generic_target_for_test(
            &mut context,
            target,
            &[("named", named), ("broad", broad)],
            None,
        );
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target, &[shape])
            .unwrap();

        for name in ["named", "broad"] {
            let property = context
                .store_mut_for_test()
                .resolve_generic_interface_property(reference, name, None)
                .unwrap()
                .unwrap();
            assert_eq!(property.type_id(), number);
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolve_generic_interface_property(reference, name, None),
                Ok(Some(property)),
            );
        }
    }

    #[test]
    fn indexed_unicode_property_names_preserve_javascript_code_units() {
        use ts_core::JsString;

        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        for name in ["i\u{307}spanyol", "\u{3bf}\u{3c2}", "SSFOO", "FIOO"] {
            let literal = store.regular_string_literal_type(name.to_owned()).unwrap();
            assert_eq!(
                indexed_property_name(&store, literal).as_deref(),
                Some(name)
            );
        }

        let high = ts_ast::encode_js_string(&JsString::from_units(vec![0xd83d]));
        let low = ts_ast::encode_js_string(&JsString::from_units(vec![0xde00]));
        let separate = format!("{high}{low}");
        let literal = store.regular_string_literal_type(separate).unwrap();
        assert_eq!(
            indexed_property_name(&store, literal).as_deref(),
            Some("\u{1f600}"),
        );
    }

    #[test]
    fn numeric_string_keys_prefer_number_indexes_before_string_indexes() {
        let mut store = CanonicalTypeMapperStore::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let (string, number, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        let string_index = store
            .alloc_index_info(string, boolean, false, None, Vec::new())
            .unwrap();
        let number_index = store
            .alloc_index_info(number, number, false, None, Vec::new())
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
            Some(vec![string_index, number_index]),
        ));
        let numeric_name = store.regular_string_literal_type("42".to_owned()).unwrap();
        let ordinary_name = store
            .regular_string_literal_type("forty-two".to_owned())
            .unwrap();

        assert_eq!(
            indexed_signature_value_type(&store, object, numeric_name),
            Some(number),
        );
        assert_eq!(
            indexed_signature_value_type(&store, object, ordinary_name),
            Some(boolean),
        );
        assert_eq!(
            indexed_signature_value_type(&store, object, number),
            Some(number),
        );
        assert_eq!(
            indexed_signature_value_type(&store, object, string),
            Some(boolean),
        );
    }

    #[test]
    fn generic_index_signature_values_instantiate_and_preserve_source_metadata() {
        let parsed = parse_source_file("interface Box<T> { value: T }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_213);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let owner = source_symbol(&parsed, file, &context, "Box");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let parameter = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("Box must retain its generic interface target"),
        };
        publish_generic_target_for_test(&mut context, target, &[("value", parameter)], None);
        let (string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let source = context
            .store_mut_for_test()
            .alloc_index_info(string, parameter, true, None, Vec::new())
            .unwrap();
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        let mapper = context
            .store_mut_for_test()
            .resolve_generic_interface_members(reference, None)
            .unwrap()
            .mapper()
            .unwrap();

        let instantiated = context
            .store_mut_for_test()
            .instantiate_generic_interface_index_info(reference, source, mapper, None)
            .unwrap();
        let info = context.store().index_info(instantiated).unwrap();
        assert_ne!(instantiated, source);
        assert_eq!(info.key_type(), string);
        assert_eq!(info.value_type(), number);
        assert!(info.is_readonly());
        assert!(info.declaration().is_none());
        assert!(info.components().is_empty());

        let unchanged = context
            .store_mut_for_test()
            .alloc_index_info(string, string, false, None, Vec::new())
            .unwrap();
        let before = context.store().index_info_len();
        assert_eq!(
            context
                .store_mut_for_test()
                .instantiate_generic_interface_index_info(reference, unchanged, mapper, None),
            Ok(unchanged),
        );
        assert_eq!(context.store().index_info_len(), before);
    }

    #[test]
    fn invariant_declared_interface_property_reuses_its_source_symbol() {
        let parsed = parse_source_file(concat!(
            "interface Payload { label: string }\n",
            "interface Box<T> { value: T; payload: Payload }\n",
            "declare const model: Box<number>;\n",
            "const payload: Payload = model.payload;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_201);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());

        let model = source_symbol(&parsed, file, &context, "model");
        let reference = context
            .store()
            .value_symbol_links(model)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let target = match context.store().type_payload(reference).unwrap().data() {
            TypeData::TypeReference(reference) => reference.object.target.unwrap(),
            _ => panic!("the source variable must retain a generic reference"),
        };
        let declared = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface.declared_members.unwrap(),
            _ => panic!("the generic reference target must be an interface"),
        };
        let raw = context
            .store()
            .symbol_table(declared)
            .and_then(|table| table.get_source("payload"))
            .unwrap();
        let payload = context
            .store_mut_for_test()
            .resolve_generic_interface_property(reference, "payload", None)
            .unwrap()
            .unwrap();

        assert_eq!(payload.symbol(), raw);
        assert!(
            !context
                .store()
                .symbol(raw)
                .unwrap()
                .flags()
                .contains(SymbolFlags::TRANSIENT)
        );
    }

    #[test]
    fn exact_optional_properties_accept_normalized_undefined_without_missing() {
        for exact_optional_property_types in [false, true] {
            let parsed = parse_source_file(concat!(
                "interface Box<T> { value?: undefined }\n",
                "type TextBox = Box<string>;\n",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_202);
            let mut context = checker_context(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        exact_optional_property_types,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );
            context.check_source_file(file).unwrap();
            let alias = source_symbol(&parsed, file, &context, "TextBox");
            let reference = context.get_declared_type_of_symbol(alias).unwrap();
            let undefined = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type;

            let property = context
                .store_mut_for_test()
                .resolve_generic_interface_property(reference, "value", None)
                .unwrap_or_else(|error| {
                    panic!(
                        "normalized undefined was rejected with exactOptionalPropertyTypes={exact_optional_property_types}: {error:?}"
                    )
                })
                .unwrap();

            assert_eq!(property.type_id(), undefined);
            assert!(property.is_optional());
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolve_generic_interface_members(reference, None)
                    .unwrap()
                    .mapper(),
                None,
            );
        }
    }

    #[test]
    fn inconsistent_proxy_mappers_fail_before_warm_cache_publication() {
        let parsed = parse_source_file(concat!(
            "interface Box<T> { first: T; second: T }\n",
            "declare const text: Box<string>;\n",
            "const first: string = text.first;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_203);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        context.check_source_file(file).unwrap();
        let text = source_symbol(&parsed, file, &context, "text");
        let reference = context
            .store()
            .value_symbol_links(text)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let members = context
            .store_mut_for_test()
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        let [first, second] = members.properties() else {
            panic!("the generic interface must retain two ordered properties")
        };
        let (first, second) = (*first, *second);
        let target = members.target();
        let (parameter, this_type) = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => (
                interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                interface.this_type.unwrap(),
            ),
            _ => panic!("the member cache must retain its generic target"),
        };
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let forged = context
            .store_mut_for_test()
            .new_type_mapper(vec![parameter, this_type], vec![string, reference])
            .unwrap();
        let links = context.store().value_symbol_links(second).cloned().unwrap();
        assert!(context.store_mut_for_test().set_value_symbol_links(
            second,
            ValueSymbolLinks {
                mapper: Some(forged),
                ..links
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );

        assert_eq!(
            validate_generic_interface_members(context.store(), reference, None),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(second)),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(reference, "first", None),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(second)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            before,
        );
        assert_ne!(first, second);
    }

    #[test]
    fn poisoned_exact_optional_union_cache_is_rejected_without_mutation() {
        let parsed = parse_source_file(concat!(
            "interface Box<T> { value?: undefined }\n",
            "type TextBox = Box<string>;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_204);
        let mut context = checker_context(
            &parsed,
            file,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: true,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        context.check_source_file(file).unwrap();
        let owner = source_symbol(&parsed, file, &context, "Box");
        let alias = source_symbol(&parsed, file, &context, "TextBox");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let reference = context.get_declared_type_of_symbol(alias).unwrap();
        let (parameter, source_property) = {
            let TypeData::Interface(interface) =
                context.store().type_payload(target).unwrap().data()
            else {
                panic!("the source owner must retain its generic interface")
            };
            (
                interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                context
                    .store()
                    .symbol_table(interface.declared_members.unwrap())
                    .and_then(|table| table.get_source("value"))
                    .unwrap(),
            )
        };
        let missing = context.store().intrinsic_bootstrap().unwrap().missing_type;
        let template = context
            .store_mut_for_test()
            .alloc_union_type(ObjectFlags::NONE, vec![missing, parameter])
            .unwrap();
        assert!(context.store_mut_for_test().set_value_symbol_links(
            source_property,
            ValueSymbolLinks {
                resolved_type: Some(template),
                ..ValueSymbolLinks::default()
            },
        ));
        let property = context
            .store_mut_for_test()
            .resolve_generic_interface_property(reference, "value", None)
            .unwrap()
            .unwrap();
        let flags = context
            .store()
            .type_payload(property.type_id())
            .unwrap()
            .object_flags();
        assert!(flags.contains(ObjectFlags::PRIMITIVE_UNION));
        assert!(
            context
                .store_mut_for_test()
                .set_type_object_flags(property.type_id(), flags & !ObjectFlags::PRIMITIVE_UNION,)
        );
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );

        assert_eq!(
            validate_generic_interface_members(context.store(), reference, None),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(
                property.symbol(),
            )),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            before,
        );
    }
}
