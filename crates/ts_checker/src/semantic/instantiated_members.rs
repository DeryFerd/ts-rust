//! Lazy members for direct local generic-interface references.
//!
//! This is the declared-member prefix of pinned `resolveTypeReferenceMembers`,
//! `resolveObjectTypeMembers`, `instantiateSymbolTable`, and
//! `instantiateSymbol`. A direct reference (including the generic target's
//! canonical identity reference) already belongs to its target's
//! instantiation cache before this module runs. Member resolution pads the
//! explicit arguments with that reference for the implicit `this` type
//! parameter, creates a mapper when properties require one, and preserves
//! source-owned methods and index signatures.

use std::collections::HashSet;

use ts_ast::SyntaxKind;
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolTableId, semantic::PreparedSymbolTable,
};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, IndexInfoId, SignatureId, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    callable_sets::{
        CallableSetProjection, StoredCallableSetValidation, instantiated_method_type_matches,
        validated_instantiated_method_mapper,
    },
    callables::{
        CallableFamily, ValidatedSingleCallParameterDisplay, ValidatedSingleCallSignatureDisplay,
        ValidatedSingleCallable,
    },
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    functions::{
        FunctionTypeDisplayError, StoredFunctionTypeValidation, function_type_display_projection,
        validate_stored_function_type,
    },
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession,
        instantiable_member_type_contains_variables, instantiate_type_with_session,
        instantiate_type_with_vector_and_session, instantiated_member_type_matches,
    },
    links::{MembersOrExportsResolutionKind, ValueSymbolLinks},
    mapper::TypeMapperApplication,
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_declared_property_object,
    },
    reference_types::{DirectGenericReferenceError, validate_direct_generic_reference},
    signatures::{SignatureFlags, SignatureInstantiationError},
    store::SourceNodeParent,
    structured_members::{valid_index_symbol, valid_interface_method_value},
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
                "type {type_:?} is outside the supported local generic interface surface"
            ),
            Self::InvalidTarget(type_) => {
                write!(formatter, "generic interface target {type_:?} is malformed")
            }
            Self::UnsupportedMember(symbol) => write!(
                formatter,
                "member {symbol:?} is outside the supported generic interface surface"
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
    method: bool,
}

type DeclaredTargetHeader = (
    SemanticSymbolId,
    Vec<TypeId>,
    Option<SymbolTableId>,
    Vec<DeclaredProperty>,
    Vec<IndexInfoId>,
);

type InheritedInterfaceMembers = (Vec<SemanticSymbolId>, Vec<IndexInfoId>);

#[derive(Clone, Debug)]
struct GenericInterfaceShape {
    reference: TypeId,
    target: TypeId,
    source_parameters: Vec<TypeId>,
    target_arguments: Vec<TypeId>,
    properties: Vec<DeclaredProperty>,
    index_infos: Vec<IndexInfoId>,
    base_types: Vec<TypeId>,
    inherited_properties: Vec<SemanticSymbolId>,
    inherited_index_infos: Vec<IndexInfoId>,
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
    index_infos: Vec<IndexInfoId>,
}

#[derive(Clone, Debug)]
struct PublishedInterfaceMethodSignature {
    source: SignatureId,
    parameter_types: Vec<TypeId>,
    return_type: TypeId,
}

#[derive(Clone, Debug)]
struct PublishedInterfaceMethodPlan {
    method: SemanticSymbolId,
    source: TypeId,
    receiver: TypeId,
    mapper_sources: Vec<TypeId>,
    mapper_targets: Vec<TypeId>,
    signatures: Vec<PublishedInterfaceMethodSignature>,
}

#[derive(Clone, Debug)]
struct PublishedArrayPropertyCallablePlan {
    source: TypeId,
    signature: SignatureId,
    parameter_types: Vec<TypeId>,
    return_type: TypeId,
    mapper_sources: Vec<TypeId>,
    mapper_targets: Vec<TypeId>,
}

pub(super) enum InstantiatedArrayPropertyCallableValidation {
    NotCallable,
    Valid(Vec<TypeId>),
    Malformed,
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

    /// Resolves the declared member surface of one direct generic interface
    /// reference, including the canonical target identity.
    ///
    /// The target must already own a fully resolved declared member surface.
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
    publish_cold_members(store, &shape, plan, array_targets)
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
    let instantiated = if store
        .symbol(target)
        .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD))
    {
        instantiate_generic_interface_method_type(store, template, mapper, array_targets, session)?
    } else {
        instantiate_generic_member_type(store, template, mapper, array_targets, session)?
    };
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

/// Finds type variables in every published method parameter and return type.
pub(super) fn published_method_requires_instantiation(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    method: SemanticSymbolId,
) -> Result<bool, GenericInterfaceMemberError> {
    let (_, target) = store
        .authenticated_interface_method_owner(method)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let TypeData::Interface(interface) = store
        .type_payload(target)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?
        .data()
    else {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    };
    let owner_parameters = interface
        .all_type_parameters
        .as_deref()
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let source = store
        .value_symbol_links(method)
        .and_then(|links| links.resolved_type)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let signatures = store
        .type_payload(source)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.signatures.as_deref())
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let mut requires = false;
    for &signature in signatures {
        let signature = store
            .signature(signature)
            .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
        let mut parameters = owner_parameters.to_vec();
        parameters.extend_from_slice(signature.type_parameters());
        requires |= !signature.type_parameters().is_empty();
        let return_type = signature
            .resolved_return_type()
            .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
        let types = signature
            .parameters()
            .iter()
            .map(|parameter| {
                store
                    .value_symbol_links(*parameter)
                    .and_then(|links| links.resolved_type)
                    .ok_or(GenericInterfaceMemberError::InvalidMember(method))
            })
            .chain(std::iter::once(Ok(return_type)));
        for type_ in types {
            requires |= member_type_requires_instantiation(
                store,
                type_?,
                &parameters,
                Some(CanonicalArrayTargets::from_global_types(global_types)),
            )?;
        }
    }
    Ok(requires)
}

/// Instantiates a published global generic interface method for its receiver.
///
/// Shared declaration signatures and annotation caches remain generic. The
/// returned callable owns mapped signatures and concrete parameter values.
pub(super) fn instantiate_published_generic_interface_method(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
    method: SemanticSymbolId,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let targets = CanonicalArrayTargets::from_global_types(global_types);
    let plan = plan_published_interface_method(store, targets, receiver, method)?;
    if let Some(cached) = cached_published_interface_method(store, &plan, targets)? {
        return Ok(cached);
    }
    if !store.try_reserve_mappers(1)
        || !store.try_reserve_types(1)
        || !store.try_reserve_signatures(plan.signatures.len())
    {
        return Err(GenericInterfaceMemberError::Capacity(plan.receiver));
    }
    let mapper = store
        .new_type_mapper(plan.mapper_sources.clone(), plan.mapper_targets.clone())
        .ok_or(GenericInterfaceMemberError::Capacity(plan.receiver))?;
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut signatures = Vec::with_capacity(plan.signatures.len());
    for source in &plan.signatures {
        let signature = instantiate_generic_method_signature(
            store,
            source.source,
            &source.parameter_types,
            source.return_type,
            mapper,
            Some(targets),
            &mut session,
            plan.method,
            plan.receiver,
        )?;
        signatures.push(signature);
    }
    let callable = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.method))
        .ok_or(GenericInterfaceMemberError::Capacity(plan.receiver))?;
    if !store.set_object_target_and_mapper(callable, Some(plan.source), Some(mapper))
        || !store.set_structured_type_members(callable, None, None, Some(signatures), None, None)
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            plan.receiver,
        ));
    }
    Ok(callable)
}

/// Specializes a published function-valued global Array property for one receiver.
pub(super) fn instantiate_published_generic_array_property_callable(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
    property: SemanticSymbolId,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let targets = CanonicalArrayTargets::from_global_types(global_types);
    let plan = plan_published_array_property_callable(store, targets, receiver, property)?;
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let resolved_parameters = plan
        .parameter_types
        .iter()
        .copied()
        .map(|type_| {
            instantiate_type_with_vector_and_session(
                store,
                type_,
                &plan.mapper_sources,
                &plan.mapper_targets,
                Some(targets),
                &mut session,
            )
            .map_err(|error| property_instantiation_error(type_, &error))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let resolved_return = instantiate_type_with_vector_and_session(
        store,
        plan.return_type,
        &plan.mapper_sources,
        &plan.mapper_targets,
        Some(targets),
        &mut session,
    )
    .map_err(|error| property_instantiation_error(plan.return_type, &error))?;
    if resolved_parameters == plan.parameter_types && resolved_return == plan.return_type {
        return Ok(plan.source);
    }
    for (type_, record) in store.types() {
        let TypeData::Object(object) = record.data() else {
            continue;
        };
        let Some(mapper) = object.mapper else {
            continue;
        };
        if record.symbol() == Some(property)
            && object.target == Some(plan.source)
            && store.type_mapper_has_exact_endpoints(
                mapper,
                &plan.mapper_sources,
                &plan.mapper_targets,
            ) == Some(true)
        {
            return match validate_instantiated_array_property_callable(store, type_) {
                InstantiatedArrayPropertyCallableValidation::Valid(_) => Ok(type_),
                InstantiatedArrayPropertyCallableValidation::NotCallable
                | InstantiatedArrayPropertyCallableValidation::Malformed => {
                    Err(GenericInterfaceMemberError::InvalidCachedMembers(receiver))
                }
            };
        }
    }

    if !store.try_reserve_mappers(1)
        || !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
    {
        return Err(GenericInterfaceMemberError::Capacity(receiver));
    }
    let mapper = store
        .new_type_mapper(plan.mapper_sources.clone(), plan.mapper_targets.clone())
        .ok_or(GenericInterfaceMemberError::Capacity(receiver))?;
    let signature = store
        .instantiate_signature(plan.signature, mapper)
        .map_err(|error| match error {
            SignatureInstantiationError::Capacity(_) => {
                GenericInterfaceMemberError::Capacity(receiver)
            }
            _ => GenericInterfaceMemberError::InvalidMember(property),
        })?;
    let parameters = store
        .signature(signature)
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(receiver))?
        .parameters()
        .to_vec();
    for (&parameter, &type_) in parameters.iter().zip(&resolved_parameters) {
        let links = store.value_symbol_links(parameter).cloned().ok_or(
            GenericInterfaceMemberError::InvalidCachedProperty(parameter),
        )?;
        if links.resolved_type.is_some_and(|cached| cached != type_)
            || links.resolved_type.is_none()
                && !store.set_value_symbol_links(
                    parameter,
                    ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..links
                    },
                )
        {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(
                parameter,
            ));
        }
    }
    if !store.set_signature_resolved_return_type(signature, Some(resolved_return)) {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(receiver));
    }
    let callable = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(property))
        .ok_or(GenericInterfaceMemberError::Capacity(receiver))?;
    if !store.set_object_target_and_mapper(callable, Some(plan.source), Some(mapper))
        || !store.set_structured_type_members(
            callable,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        )
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(receiver));
    }
    Ok(callable)
}

fn plan_published_array_property_callable(
    store: &CanonicalTypeMapperStore,
    targets: CanonicalArrayTargets,
    receiver: TypeId,
    property: SemanticSymbolId,
) -> Result<PublishedArrayPropertyCallablePlan, GenericInterfaceMemberError> {
    let array = store
        .canonical_array_reference_with_targets(targets, receiver)
        .map_err(|_| GenericInterfaceMemberError::InvalidTarget(receiver))?
        .ok_or(GenericInterfaceMemberError::InvalidTarget(receiver))?;
    let receiver = array.base_type;
    let reference = validate_direct_generic_reference(store, receiver)?;
    let expected_target = if array.readonly {
        targets.readonly_array_type()
    } else {
        targets.array_type()
    };
    if reference.target != expected_target {
        return Err(GenericInterfaceMemberError::InvalidTarget(receiver));
    }
    let target_record = store
        .type_payload(reference.target)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(reference.target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(GenericInterfaceMemberError::InvalidTarget(reference.target));
    };
    let owner = target_record
        .symbol()
        .ok_or(GenericInterfaceMemberError::InvalidTarget(reference.target))?;
    let member = store
        .symbol(property)
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?;
    let links = store
        .value_symbol_links(property)
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?;
    let source = links
        .resolved_type
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?;
    if !member.flags().contains(SymbolFlags::PROPERTY)
        || member
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(member.name()))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(property)
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(source),
                ..ValueSymbolLinks::default()
            })
        || !matches!(
            validate_stored_function_type(store, source),
            StoredFunctionTypeValidation::Valid(_)
        )
    {
        return Err(GenericInterfaceMemberError::InvalidMember(property));
    }
    let source_record = store
        .type_payload(source)
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?;
    let TypeData::Object(callable) = source_record.data() else {
        return Err(GenericInterfaceMemberError::InvalidMember(property));
    };
    let [signature] = callable
        .structured
        .signatures
        .as_deref()
        .unwrap_or_default()
    else {
        return Err(GenericInterfaceMemberError::InvalidMember(property));
    };
    let signature_record = store
        .signature(*signature)
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?;
    let parameter_types = store
        .callable_signature_parameter_types(*signature)
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?
        .to_vec();
    let return_type = signature_record
        .resolved_return_type()
        .ok_or(GenericInterfaceMemberError::InvalidMember(property))?;
    let parameters = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .ok_or(GenericInterfaceMemberError::InvalidTarget(reference.target))?;
    let this_type = interface
        .this_type
        .ok_or(GenericInterfaceMemberError::InvalidTarget(reference.target))?;
    if parameters.len() != reference.type_arguments.len()
        || !signature_record.type_parameters().is_empty()
        || signature_record.parameters().len() != parameter_types.len()
    {
        return Err(GenericInterfaceMemberError::InvalidMember(property));
    }
    Ok(PublishedArrayPropertyCallablePlan {
        source,
        signature: *signature,
        parameter_types,
        return_type,
        mapper_sources: parameters
            .iter()
            .copied()
            .chain(std::iter::once(this_type))
            .collect(),
        mapper_targets: reference
            .type_arguments
            .iter()
            .copied()
            .chain(std::iter::once(receiver))
            .collect(),
    })
}

/// Validates a receiver-specialized function-valued Array property.
#[allow(clippy::too_many_lines)] // One proof covers the source signature and mapped proxies.
pub(super) fn validate_instantiated_array_property_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> InstantiatedArrayPropertyCallableValidation {
    let not_callable = InstantiatedArrayPropertyCallableValidation::NotCallable;
    let malformed = || InstantiatedArrayPropertyCallableValidation::Malformed;
    let Some(record) = store.type_payload(type_) else {
        return not_callable;
    };
    let TypeData::Object(object) = record.data() else {
        return not_callable;
    };
    let (Some(source), Some(mapper), Some(property)) =
        (object.target, object.mapper, record.symbol())
    else {
        return not_callable;
    };
    let Some(property_record) = store.symbol(property) else {
        return malformed();
    };
    if !property_record.flags().contains(SymbolFlags::PROPERTY)
        || !store.type_has_function_type_provenance(source)
    {
        return not_callable;
    }
    let Some(owner) = property_record
        .parent()
        .and_then(|parent| store.get_merged_symbol(parent))
    else {
        return malformed();
    };
    let Some(owner_record) = store.symbol(owner) else {
        return malformed();
    };
    let Some(target) = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
    else {
        return malformed();
    };
    let Some(TypeData::Interface(interface)) = store
        .type_payload(target)
        .map(super::type_records::TypeRecord::data)
    else {
        return malformed();
    };
    let Some(parameters) = interface.reference.resolved_type_arguments.as_deref() else {
        return malformed();
    };
    let Some(this_type) = interface.this_type else {
        return malformed();
    };
    let Some(receiver) = store.map_type(mapper, this_type) else {
        return malformed();
    };
    let Ok(reference) = validate_direct_generic_reference(store, receiver) else {
        return malformed();
    };
    let mapper_sources = parameters
        .iter()
        .copied()
        .chain(std::iter::once(this_type))
        .collect::<Vec<_>>();
    let mapper_targets = reference
        .type_arguments
        .iter()
        .copied()
        .chain(std::iter::once(receiver))
        .collect::<Vec<_>>();
    let Some([signature]) = object.structured.signatures.as_deref() else {
        return malformed();
    };
    let Some(instantiated) = store.signature(*signature) else {
        return malformed();
    };
    let Some(original_id) = instantiated.target() else {
        return malformed();
    };
    let Some(original) = store.signature(original_id) else {
        return malformed();
    };
    let Some(source_record) = store.type_payload(source) else {
        return malformed();
    };
    let Some(source_structured) = source_record.data().structured() else {
        return malformed();
    };
    let Some(original_types) = store.callable_signature_parameter_types(original_id) else {
        return malformed();
    };
    let Some(return_type) = instantiated.resolved_return_type() else {
        return malformed();
    };
    let Some(original_return) = original.resolved_return_type() else {
        return malformed();
    };
    let targets = CanonicalArrayTargets::for_single_target_validation(target);
    let global_owner = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get(owner_record.name()))
        .and_then(|owner| store.get_merged_symbol(owner));
    if !matches!(
        owner_record.name().as_utf8(),
        Some("Array" | "ReadonlyArray")
    ) || global_owner != Some(owner)
        || reference.target != target
        || parameters.len() != reference.type_arguments.len()
        || store.type_mapper_has_exact_endpoints(mapper, &mapper_sources, &mapper_targets)
            != Some(true)
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || source_structured.signatures.as_deref() != Some(&[original_id])
        || store.value_symbol_links(property)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(source),
                ..ValueSymbolLinks::default()
            })
        || instantiated.mapper() != Some(mapper)
        || instantiated.declaration() != original.declaration()
        || instantiated.parameters().len() != original.parameters().len()
        || original.parameters().len() != original_types.len()
        || !cached_instantiated_property_type_matches(
            store,
            original_return,
            return_type,
            mapper,
            Some(targets),
        )
    {
        return malformed();
    }
    let mut edges = Vec::with_capacity(original_types.len() + 1);
    for ((parameter, original_parameter), template) in instantiated
        .parameters()
        .iter()
        .zip(original.parameters())
        .zip(original_types)
    {
        let Some(links) = store.value_symbol_links(*parameter) else {
            return malformed();
        };
        let Some(type_) = links.resolved_type else {
            return malformed();
        };
        let valid_links = if parameter == original_parameter {
            links
                == &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
                && type_ == *template
        } else {
            links
                == &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    target: Some(*original_parameter),
                    mapper: Some(mapper),
                    name_type: store
                        .value_symbol_links(*original_parameter)
                        .and_then(|links| links.name_type),
                    ..ValueSymbolLinks::default()
                })
        };
        if !valid_links
            || !cached_instantiated_property_type_matches(
                store,
                *template,
                type_,
                mapper,
                Some(targets),
            )
        {
            return malformed();
        }
        edges.push(type_);
    }
    edges.push(return_type);
    InstantiatedArrayPropertyCallableValidation::Valid(edges)
}

fn plan_published_interface_method(
    store: &CanonicalTypeMapperStore,
    targets: CanonicalArrayTargets,
    receiver: TypeId,
    method: SemanticSymbolId,
) -> Result<PublishedInterfaceMethodPlan, GenericInterfaceMemberError> {
    let array = store
        .canonical_array_reference_with_targets(targets, receiver)
        .map_err(|_| GenericInterfaceMemberError::InvalidTarget(receiver))?
        .ok_or(GenericInterfaceMemberError::InvalidTarget(receiver))?;
    let receiver = array.base_type;
    let (owner, target) = store
        .authenticated_interface_method_owner(method)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let expected_target = if array.readonly {
        targets.readonly_array_type()
    } else {
        targets.array_type()
    };
    if target != expected_target {
        return Err(GenericInterfaceMemberError::InvalidTarget(receiver));
    }
    let reference = validate_direct_generic_reference(store, receiver)?;
    if reference.target != target {
        return Err(GenericInterfaceMemberError::InvalidTarget(receiver));
    }
    let TypeData::Interface(interface) = store
        .type_payload(target)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?
        .data()
    else {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    };
    let parameters = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .filter(|parameters| !parameters.is_empty())
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    let this_type = interface
        .this_type
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    if parameters.len() != reference.type_arguments.len()
        || interface.all_type_parameters.as_deref().is_none_or(|all| {
            all.len() != parameters.len() + 1
                || &all[..parameters.len()] != parameters
                || all.last().copied() != Some(this_type)
        })
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| {
                store
                    .symbol(method)
                    .and_then(|method| members.get(method.name()))
            })
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(method)
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let links = store
        .value_symbol_links(method)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let source = links
        .resolved_type
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    if links
        != &(ValueSymbolLinks {
            resolved_type: Some(source),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(GenericInterfaceMemberError::InvalidMember(method));
    }
    let record = store
        .type_payload(source)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let TypeData::Object(callable) = record.data() else {
        return Err(GenericInterfaceMemberError::InvalidMember(method));
    };
    let signatures = callable
        .structured
        .signatures
        .as_deref()
        .filter(|signatures| !signatures.is_empty())
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || record.symbol() != Some(method)
        || record.alias().is_some()
        || callable.target.is_some()
        || callable.mapper.is_some()
        || callable.instantiations != TypeCacheState::Unallocated
        || callable.structured.members.is_some()
        || callable.structured.properties.is_some()
        || callable.structured.call_signature_count != signatures.len()
        || callable.structured.index_infos.is_some()
        || callable.structured.constrained != ConstrainedTypeData::default()
        || callable
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(GenericInterfaceMemberError::InvalidMember(method));
    }
    let mapper_sources = parameters
        .iter()
        .copied()
        .chain(std::iter::once(this_type))
        .collect::<Vec<_>>();
    let mapper_targets = reference
        .type_arguments
        .iter()
        .copied()
        .chain(std::iter::once(receiver))
        .collect::<Vec<_>>();
    let mut planned = Vec::with_capacity(signatures.len());
    for &signature in signatures {
        if store.interface_method_linked_type(signature) != Some(source) {
            return Err(GenericInterfaceMemberError::InvalidMember(method));
        }
        let record = store
            .signature(signature)
            .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
        let return_type = record
            .resolved_return_type()
            .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
        let parameter_types = store
            .callable_signature_parameter_types(signature)
            .filter(|types| types.len() == record.parameters().len())
            .ok_or(GenericInterfaceMemberError::InvalidMember(method))?
            .to_vec();
        let mut signature_parameters = mapper_sources.clone();
        signature_parameters.extend_from_slice(record.type_parameters());
        for type_ in parameter_types.iter().copied().chain([return_type]) {
            member_type_requires_instantiation(store, type_, &signature_parameters, Some(targets))?;
        }
        planned.push(PublishedInterfaceMethodSignature {
            source: signature,
            parameter_types,
            return_type,
        });
    }
    Ok(PublishedInterfaceMethodPlan {
        method,
        source,
        receiver,
        mapper_sources,
        mapper_targets,
        signatures: planned,
    })
}

fn cached_published_interface_method(
    store: &CanonicalTypeMapperStore,
    plan: &PublishedInterfaceMethodPlan,
    targets: CanonicalArrayTargets,
) -> Result<Option<TypeId>, GenericInterfaceMemberError> {
    let mut cached = None;
    for (type_, record) in store.types() {
        let TypeData::Object(object) = record.data() else {
            continue;
        };
        if record.symbol() != Some(plan.method) || object.target != Some(plan.source) {
            continue;
        }
        let Some(mapper) = object.mapper else {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                plan.receiver,
            ));
        };
        if store.type_mapper_has_exact_endpoints(mapper, &plan.mapper_sources, &plan.mapper_targets)
            != Some(true)
        {
            continue;
        }
        if cached.replace(type_).is_some()
            || record.flags() != TypeFlags::OBJECT
            || record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
            || record.alias().is_some()
            || object.instantiations != TypeCacheState::Unallocated
            || object.structured.members.is_some()
            || object.structured.properties.is_some()
            || object.structured.index_infos.is_some()
            || object.structured.constrained != ConstrainedTypeData::default()
            || object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_some()
            || object.structured.call_signature_count != plan.signatures.len()
        {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                plan.receiver,
            ));
        }
        let signatures = object
            .structured
            .signatures
            .as_deref()
            .filter(|signatures| signatures.len() == plan.signatures.len())
            .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                plan.receiver,
            ))?;
        for (&signature, source) in signatures.iter().zip(&plan.signatures) {
            validate_published_interface_method_signature(
                store, plan, source, signature, mapper, targets,
            )?;
        }
    }
    Ok(cached)
}

fn validate_published_interface_method_signature(
    store: &CanonicalTypeMapperStore,
    plan: &PublishedInterfaceMethodPlan,
    source: &PublishedInterfaceMethodSignature,
    signature: SignatureId,
    mapper: TypeMapperId,
    targets: CanonicalArrayTargets,
) -> Result<(), GenericInterfaceMemberError> {
    let original = store
        .signature(source.source)
        .ok_or(GenericInterfaceMemberError::InvalidMember(plan.method))?;
    let instantiated =
        store
            .signature(signature)
            .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                plan.receiver,
            ))?;
    let return_type = instantiated.resolved_return_type().ok_or(
        GenericInterfaceMemberError::InvalidCachedMembers(plan.receiver),
    )?;
    let signature_mapper =
        validated_instantiated_method_mapper(store, original, instantiated, mapper, Some(targets))
            .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                plan.receiver,
            ))?;
    if instantiated.flags() != (original.flags() & SignatureFlags::PROPAGATING_FLAGS)
        || instantiated.declaration() != original.declaration()
        || instantiated.this_parameter().is_some()
        || instantiated.parameters().len() != original.parameters().len()
        || instantiated.min_argument_count() != original.min_argument_count()
        || instantiated.target() != Some(source.source)
        || instantiated.mapper() != Some(signature_mapper)
        || !instantiated_method_type_matches(
            store,
            source.return_type,
            return_type,
            signature_mapper,
            Some(targets),
        )
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            plan.receiver,
        ));
    }
    for ((&parameter, &original_parameter), &template) in instantiated
        .parameters()
        .iter()
        .zip(original.parameters())
        .zip(&source.parameter_types)
    {
        let links = store.value_symbol_links(parameter).ok_or(
            GenericInterfaceMemberError::InvalidCachedProperty(parameter),
        )?;
        let actual =
            links
                .resolved_type
                .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(
                    parameter,
                ))?;
        let valid_links = if parameter == original_parameter {
            links
                == &(ValueSymbolLinks {
                    resolved_type: Some(actual),
                    ..ValueSymbolLinks::default()
                })
                && actual == template
        } else {
            links
                == &(ValueSymbolLinks {
                    resolved_type: Some(actual),
                    target: Some(original_parameter),
                    mapper: Some(signature_mapper),
                    name_type: store
                        .value_symbol_links(original_parameter)
                        .and_then(|links| links.name_type),
                    ..ValueSymbolLinks::default()
                })
        };
        if !valid_links
            || !instantiated_method_type_matches(
                store,
                template,
                actual,
                signature_mapper,
                Some(targets),
            )
        {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(
                parameter,
            ));
        }
    }
    Ok(())
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
    if store.type_has_function_type_provenance(template) {
        return instantiate_function_member_type(store, template, mapper, array_targets, session);
    }
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
    let name = indexed_property_escaped_name(store, index);
    if validate_direct_generic_reference(store, object).is_ok() {
        resolve_members_with_array_targets(store, object, array_targets)?;
    }
    let symbol = name.as_ref().and_then(|name| {
        store
            .type_payload(object)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(name.as_ref()))
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

fn function_member_signature(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
) -> Option<(SemanticSymbolId, PublishedInterfaceMethodSignature)> {
    if !matches!(
        validate_stored_function_type(store, source),
        StoredFunctionTypeValidation::Valid(_)
    ) {
        return None;
    }
    function_member_declaring_method(store, source)?;
    let record = store.type_payload(source)?;
    let [signature] = record.data().structured()?.signatures.as_deref()? else {
        return None;
    };
    let signature_record = store.signature(*signature)?;
    let parameter_types = store.callable_signature_parameter_types(*signature)?;
    if !signature_record.type_parameters().is_empty()
        || signature_record.this_parameter().is_some()
        || signature_record.has_rest_parameter()
        || signature_record.parameters().len() != parameter_types.len()
    {
        return None;
    }
    Some((
        record.symbol()?,
        PublishedInterfaceMethodSignature {
            source: *signature,
            parameter_types: parameter_types.to_vec(),
            return_type: signature_record.resolved_return_type()?,
        },
    ))
}

/// The installed function-type mapping covers direct global Array method parameters.
fn function_member_declaring_method(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
) -> Option<SemanticSymbolId> {
    let callback = store.type_payload(source)?.symbol()?;
    let [declaration] = store.symbol(callback)?.declarations()? else {
        return None;
    };
    let SourceNodeParent::Parent(parameter) = store.source_node_parent(*declaration)? else {
        return None;
    };
    let SourceNodeParent::Parent(method_declaration) = store.source_node_parent(parameter)? else {
        return None;
    };
    let SourceNodeParent::Parent(interface_declaration) =
        store.source_node_parent(method_declaration)?
    else {
        return None;
    };
    if store.source_node_kind(*declaration) != Some(SyntaxKind::FunctionType)
        || store.source_node_kind(parameter) != Some(SyntaxKind::Parameter)
        || store.source_node_kind(method_declaration) != Some(SyntaxKind::MethodSignature)
        || store.source_node_kind(interface_declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || store.source_direct_type_annotation(parameter) != Some(*declaration)
    {
        return None;
    }
    let globals = store.symbol_table(store.intrinsic_bootstrap()?.globals)?;
    ["Array", "ReadonlyArray"].into_iter().find_map(|name| {
        let owner = store.get_merged_symbol(globals.get_source(name)?)?;
        let owner_record = store.symbol(owner)?;
        if !owner_record
            .declarations()?
            .contains(&interface_declaration)
        {
            return None;
        }
        store
            .symbol_table(owner_record.members()?)?
            .iter()
            .find_map(|(_, method)| {
                let method = store.get_merged_symbol(method)?;
                let method_record = store.symbol(method)?;
                if !method_record.declarations()?.contains(&method_declaration)
                    || store.authenticated_interface_method_owner(method)?.0 != owner
                {
                    return None;
                }
                let callable = store.value_symbol_links(method)?.resolved_type?;
                store
                    .type_payload(callable)?
                    .data()
                    .structured()?
                    .signatures
                    .as_deref()?
                    .iter()
                    .find_map(|&signature| {
                        let record = store.signature(signature)?;
                        if record.declaration() != Some(method_declaration)
                            || store.interface_method_linked_type(signature) != Some(callable)
                        {
                            return None;
                        }
                        let parameter_types =
                            store.callable_signature_parameter_types(signature)?;
                        record
                            .parameters()
                            .iter()
                            .zip(parameter_types)
                            .any(|(&symbol, &type_)| {
                                type_ == source
                                    && store
                                        .symbol(symbol)
                                        .and_then(|symbol| symbol.declarations())
                                        == Some(&[parameter])
                            })
                            .then_some(method)
                    })
            })
    })
}

/// Copies a function-valued member through its enclosing method mapper.
fn instantiate_function_member_type(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let (symbol, template) = function_member_signature(store, source)
        .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(source))?;
    let mut cached = None;
    for (type_, record) in store.types() {
        let TypeData::Object(object) = record.data() else {
            continue;
        };
        if object.target == Some(source)
            && object.mapper == Some(mapper)
            && (cached.replace(type_).is_some()
                || !instantiated_function_member_type_matches(
                    store,
                    source,
                    type_,
                    mapper,
                    array_targets,
                ))
        {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(type_));
        }
    }
    if let Some(cached) = cached {
        return Ok(cached);
    }
    if !store.try_reserve_types(1) || !store.try_reserve_signatures(1) {
        return Err(GenericInterfaceMemberError::Capacity(source));
    }
    let signature = instantiate_generic_method_signature(
        store,
        template.source,
        &template.parameter_types,
        template.return_type,
        mapper,
        array_targets,
        session,
        symbol,
        source,
    )?;
    let predicate = store
        .signature(template.source)
        .and_then(super::signatures::Signature::resolved_type_predicate);
    if let Some(predicate) = predicate {
        let predicate = store
            .type_predicate(predicate)
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let kind = predicate.kind();
        let index = predicate.parameter_index();
        let name = predicate.parameter_name().to_owned();
        let narrowed = predicate.type_id();
        let mapped = narrowed
            .map(|type_| {
                instantiate_generic_member_type(store, type_, mapper, array_targets, session)
            })
            .transpose()?;
        let predicate = store
            .alloc_type_predicate(kind, index, name, mapped)
            .ok_or(GenericInterfaceMemberError::Capacity(source))?;
        if !store.set_signature_resolved_type_predicate(signature, Some(predicate)) {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(source));
        }
    }
    let callable = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
        .ok_or(GenericInterfaceMemberError::Capacity(source))?;
    if !store.set_object_target_and_mapper(callable, Some(source), Some(mapper))
        || !store.set_structured_type_members(
            callable,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        )
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(source));
    }
    Ok(callable)
}

/// Validates copied callback signatures without changing declaration caches.
pub(super) fn instantiated_function_member_type_matches(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    instantiated_function_member_projection(store, source, actual, mapper, array_targets).is_some()
}

#[allow(clippy::too_many_lines)] // The callback and each parameter retain independent source proofs.
fn instantiated_function_member_projection(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<ValidatedSingleCallable> {
    let (symbol, template) = function_member_signature(store, source)?;
    let original = store.signature(template.source)?;
    let record = store.type_payload(actual)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let [signature] = object.structured.signatures.as_deref()? else {
        return None;
    };
    let signature_id = *signature;
    let signature = store.signature(signature_id)?;
    let return_type = signature.resolved_return_type()?;
    if store.mapper_payload(mapper).is_none()
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
        || object.target != Some(source)
        || object.mapper != Some(mapper)
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.index_infos.is_some()
        || object.structured.call_signature_count != 1
        || object.structured.constrained != ConstrainedTypeData::default()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || signature.target() != Some(template.source)
        || signature.mapper() != Some(mapper)
        || signature.flags() != original.flags() & SignatureFlags::PROPAGATING_FLAGS
        || signature.declaration() != original.declaration()
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.parameters().len() != original.parameters().len()
        || signature.min_argument_count() != original.min_argument_count()
        || signature.resolved_min_argument_count() != -1
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || store.signature_has_circular_return_type(signature_id)
        || !instantiated_method_type_matches(
            store,
            template.return_type,
            return_type,
            mapper,
            array_targets,
        )
    {
        return None;
    }
    match (
        original.resolved_type_predicate(),
        signature.resolved_type_predicate(),
    ) {
        (None, None) => {}
        (Some(source), Some(actual)) => {
            let source = store.type_predicate(source)?;
            let actual = store.type_predicate(actual)?;
            if source.kind() != actual.kind()
                || source.parameter_index() != actual.parameter_index()
                || source.parameter_name() != actual.parameter_name()
                || match (source.type_id(), actual.type_id()) {
                    (None, None) => false,
                    (Some(source), Some(actual)) => !instantiated_method_type_matches(
                        store,
                        source,
                        actual,
                        mapper,
                        array_targets,
                    ),
                    _ => true,
                }
            {
                return None;
            }
        }
        _ => return None,
    }
    let mut parameters = Vec::with_capacity(signature.parameters().len());
    for ((&parameter, &source_parameter), &source_type) in signature
        .parameters()
        .iter()
        .zip(original.parameters())
        .zip(&template.parameter_types)
    {
        let parameter_record = store.symbol(parameter)?;
        let source_record = store.symbol(source_parameter)?;
        let links = store.value_symbol_links(parameter)?;
        let actual_type = links.resolved_type?;
        let valid_links = if parameter == source_parameter {
            actual_type == source_type
                && links
                    == &ValueSymbolLinks {
                        resolved_type: Some(actual_type),
                        ..ValueSymbolLinks::default()
                    }
        } else {
            parameter_record.flags() == source_record.flags() | SymbolFlags::TRANSIENT
                && parameter_record.check_flags()
                    == CheckFlags::INSTANTIATED
                        | (source_record.check_flags()
                            & (CheckFlags::READONLY
                                | CheckFlags::LATE
                                | CheckFlags::OPTIONAL_PARAMETER
                                | CheckFlags::REST_PARAMETER))
                && parameter_record.name() == source_record.name()
                && parameter_record.declarations() == source_record.declarations()
                && parameter_record.value_declaration() == source_record.value_declaration()
                && parameter_record.parent() == source_record.parent()
                && parameter_record.members().is_none()
                && parameter_record.exports().is_none()
                && parameter_record.export_symbol().is_none()
                && store.get_merged_symbol(parameter) == Some(parameter)
                && links
                    == &ValueSymbolLinks {
                        resolved_type: Some(actual_type),
                        target: Some(source_parameter),
                        mapper: Some(mapper),
                        name_type: store
                            .value_symbol_links(source_parameter)
                            .and_then(|links| links.name_type),
                        ..ValueSymbolLinks::default()
                    }
        };
        if !valid_links
            || !instantiated_method_type_matches(
                store,
                source_type,
                actual_type,
                mapper,
                array_targets,
            )
        {
            return None;
        }
        parameters.push(actual_type);
    }
    Some(ValidatedSingleCallable {
        owner: actual,
        signature: signature_id,
        parameters,
        rest_parameter: None,
        min_argument_count: usize::try_from(signature.min_argument_count()).ok()?,
        return_type: Some(return_type),
        strict_variance_exempt: false,
    })
}

/// Finds the receiver mapper that owns a copied method callback.
fn instantiated_function_member_owner(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    mapper: TypeMapperId,
) -> Option<CanonicalArrayTargets> {
    store.signatures().find_map(|(_, signature)| {
        if signature.mapper() != Some(mapper) {
            return None;
        }
        let original_id = signature.target()?;
        if !store
            .callable_signature_parameter_types(original_id)?
            .contains(&source)
        {
            return None;
        }
        let method_type = store.interface_method_linked_type(original_id)?;
        let method = store.type_payload(method_type)?.symbol()?;
        let (owner, owner_type) = store.authenticated_interface_method_owner(method)?;
        let owner_record = store.symbol(owner)?;
        let globals = store.intrinsic_bootstrap()?.globals;
        if !matches!(
            owner_record.name().as_utf8(),
            Some("Array" | "ReadonlyArray")
        ) || store
            .symbol_table(globals)?
            .get(owner_record.name())
            .and_then(|owner| store.get_merged_symbol(owner))
            != Some(owner)
        {
            return None;
        }
        let original = store.signature(original_id)?;
        let owner_mapper = if let Some(parameter) = original.type_parameters().first() {
            let TypeMapperApplication::Composite { second, .. } =
                store.mapper_application(mapper, *parameter)?
            else {
                return None;
            };
            second
        } else {
            mapper
        };
        let TypeData::Interface(interface) = store.type_payload(owner_type)?.data() else {
            return None;
        };
        let receiver = store.map_type(owner_mapper, interface.this_type?)?;
        let targets = CanonicalArrayTargets::for_single_target_validation(owner_type);
        let plan = plan_published_interface_method(store, targets, receiver, method).ok()?;
        if store.type_mapper_has_exact_endpoints(
            owner_mapper,
            &plan.mapper_sources,
            &plan.mapper_targets,
        ) != Some(true)
            || validated_instantiated_method_mapper(
                store,
                original,
                signature,
                owner_mapper,
                Some(targets),
            ) != Some(mapper)
        {
            return None;
        }
        Some(targets)
    })
}

/// Provides mapped function types before the declaration-only callable provider.
pub(super) fn validate_instantiated_function_member_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<StoredCallableSetValidation> {
    let TypeData::Object(object) = store.type_payload(type_)?.data() else {
        return None;
    };
    let source = object.target?;
    if !store.type_has_function_type_provenance(source)
        || store
            .type_payload(type_)?
            .symbol()
            .and_then(|symbol| store.symbol(symbol))
            .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::PROPERTY))
    {
        return None;
    }
    let family = CallableFamily::FunctionType;
    let validated = (|| {
        let mapper = object.mapper?;
        let targets = instantiated_function_member_owner(store, source, mapper)?;
        let callable =
            instantiated_function_member_projection(store, source, type_, mapper, Some(targets))?;
        let mut edges = callable.parameters.clone();
        edges.extend(callable.return_type);
        if let Some(predicate) = store
            .signature(callable.signature)?
            .resolved_type_predicate()
        {
            edges.extend(store.type_predicate(predicate)?.type_id());
        }
        Some((callable, edges))
    })();
    Some(match validated {
        Some((callable, edges)) => StoredCallableSetValidation::Valid {
            family,
            projection: CallableSetProjection {
                owner: type_,
                call_signatures: Box::new([callable]),
                construct_signatures: Box::new([]),
            },
            edges,
        },
        None => StoredCallableSetValidation::Malformed { family },
    })
}

/// Uses declaration names and optional markers with mapped parameter values.
pub(super) fn instantiated_function_member_display(
    store: &CanonicalTypeMapperStore,
    host: &super::DeclaredTypeHost<'_>,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<Result<ValidatedSingleCallSignatureDisplay, FunctionTypeDisplayError>> {
    let validation = validate_instantiated_function_member_callable(store, type_)?;
    Some((|| {
        let StoredCallableSetValidation::Valid { projection, .. } = validation else {
            return Err(FunctionTypeDisplayError::Malformed);
        };
        let [callable] = projection.call_signatures.as_ref() else {
            return Err(FunctionTypeDisplayError::Malformed);
        };
        let source = match store.type_payload(type_).map(super::TypeRecord::data) {
            Some(TypeData::Object(object)) => object.target,
            _ => None,
        }
        .ok_or(FunctionTypeDisplayError::Malformed)?;
        let source_display = function_type_display_projection(store, host, source, array_targets)?;
        if source_display.parameters.len() != callable.parameters.len() {
            return Err(FunctionTypeDisplayError::Malformed);
        }
        Ok(ValidatedSingleCallSignatureDisplay {
            owner: type_,
            parameters: source_display
                .parameters
                .into_iter()
                .zip(&callable.parameters)
                .map(
                    |(source, &value_type)| ValidatedSingleCallParameterDisplay {
                        name: source.name,
                        value_type,
                        optional: source.optional,
                    },
                )
                .collect(),
            return_type: callable.return_type,
        })
    })())
}

fn instantiate_generic_interface_method_type(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let method = store
        .type_payload(source)
        .and_then(super::type_records::TypeRecord::symbol)
        .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(source))?;
    if valid_interface_method_value(store, method, source).is_none() {
        return Err(GenericInterfaceMemberError::InvalidMember(method));
    }
    let sources = store
        .type_payload(source)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.signatures.as_deref())
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?
        .iter()
        .copied()
        .map(|signature| {
            let record = store
                .signature(signature)
                .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
            let parameters = store
                .callable_signature_parameter_types(signature)
                .filter(|parameters| parameters.len() == record.parameters().len())
                .ok_or(GenericInterfaceMemberError::InvalidMember(method))?
                .to_vec();
            let return_type = record
                .resolved_return_type()
                .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
            Ok((signature, parameters, return_type))
        })
        .collect::<Result<Vec<_>, GenericInterfaceMemberError>>()?;
    if !store.try_reserve_types(1) || !store.try_reserve_signatures(sources.len()) {
        return Err(GenericInterfaceMemberError::Capacity(source));
    }
    let mut signatures = Vec::with_capacity(sources.len());
    for (original, parameter_templates, return_template) in sources {
        let signature = instantiate_generic_method_signature(
            store,
            original,
            &parameter_templates,
            return_template,
            mapper,
            array_targets,
            session,
            method,
            source,
        )?;
        signatures.push(signature);
    }
    let callable = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
        .ok_or(GenericInterfaceMemberError::Capacity(source))?;
    if !store.set_object_target_and_mapper(callable, Some(source), Some(mapper))
        || !store.set_structured_type_members(callable, None, None, Some(signatures), None, None)
    {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(source));
    }
    Ok(callable)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // One transaction preserves source, owner, and mapper identity.
fn instantiate_generic_method_signature(
    store: &mut CanonicalTypeMapperStore,
    original: SignatureId,
    parameter_templates: &[TypeId],
    return_template: TypeId,
    owner_mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
    method: SemanticSymbolId,
    owner_type: TypeId,
) -> Result<SignatureId, GenericInterfaceMemberError> {
    let source_parameters = store
        .signature(original)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?
        .type_parameters()
        .to_vec();
    let precomputed = if source_parameters.is_empty() {
        let parameters = parameter_templates
            .iter()
            .copied()
            .map(|parameter| {
                instantiate_generic_member_type(
                    store,
                    parameter,
                    owner_mapper,
                    array_targets,
                    session,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let return_type = instantiate_generic_member_type(
            store,
            return_template,
            owner_mapper,
            array_targets,
            session,
        )?;
        Some((parameters, return_type))
    } else {
        None
    };
    let signature = store
        .instantiate_signature(original, owner_mapper)
        .map_err(|error| match error {
            SignatureInstantiationError::Capacity(_) => {
                GenericInterfaceMemberError::Capacity(owner_type)
            }
            _ => GenericInterfaceMemberError::InvalidMember(method),
        })?;
    let instantiated =
        store
            .signature(signature)
            .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                owner_type,
            ))?;
    let mapper = instantiated
        .mapper()
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
            owner_type,
        ))?;
    let fresh_parameters = instantiated.type_parameters().to_vec();
    if fresh_parameters.len() != source_parameters.len() {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            owner_type,
        ));
    }
    for (fresh, source) in fresh_parameters.into_iter().zip(source_parameters) {
        let (constraint, default_type) = match store
            .type_payload(source)
            .map(super::type_records::TypeRecord::data)
        {
            Some(TypeData::TypeParameter(parameter)) => {
                (parameter.constraint, parameter.resolved_default_type)
            }
            _ => return Err(GenericInterfaceMemberError::InvalidMember(method)),
        };
        let constraint = constraint
            .map(|constraint| {
                instantiate_generic_member_type(store, constraint, mapper, array_targets, session)
            })
            .transpose()?;
        let default_type = default_type
            .map(|default_type| {
                instantiate_generic_member_type(store, default_type, mapper, array_targets, session)
            })
            .transpose()?;
        if !store.set_type_parameter_resolution(
            fresh,
            constraint,
            Some(source),
            Some(mapper),
            default_type,
        ) {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                owner_type,
            ));
        }
    }

    let (parameter_types, return_type) = if let Some(resolved) = precomputed {
        resolved
    } else {
        let parameters = parameter_templates
            .iter()
            .copied()
            .map(|parameter| {
                instantiate_generic_member_type(store, parameter, mapper, array_targets, session)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let return_type = instantiate_generic_member_type(
            store,
            return_template,
            mapper,
            array_targets,
            session,
        )?;
        (parameters, return_type)
    };
    let parameters = store
        .signature(signature)
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
            owner_type,
        ))?
        .parameters()
        .to_vec();
    for (&parameter, &type_) in parameters.iter().zip(&parameter_types) {
        let links = store.value_symbol_links(parameter).cloned().ok_or(
            GenericInterfaceMemberError::InvalidCachedProperty(parameter),
        )?;
        if links.resolved_type.is_some_and(|cached| cached != type_)
            || links.resolved_type.is_none()
                && !store.set_value_symbol_links(
                    parameter,
                    ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..links
                    },
                )
        {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(
                parameter,
            ));
        }
    }
    if !store.set_signature_resolved_return_type(signature, Some(return_type)) {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(
            owner_type,
        ));
    }
    Ok(signature)
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

fn indexed_property_escaped_name(
    store: &CanonicalTypeMapperStore,
    index: TypeId,
) -> Option<EscapedName> {
    match store.type_payload(index)?.data() {
        TypeData::UniqueEsSymbol(unique) => Some(unique.name.clone()),
        _ => indexed_property_name(store, index).map(EscapedName::source),
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
) -> Result<Option<InheritedInterfaceMembers>, GenericInterfaceMemberError> {
    let mut inherited = Vec::new();
    let mut inherited_indexes = Vec::new();
    let mut names = shape
        .properties
        .iter()
        .map(|property| property.name.clone())
        .collect::<HashSet<_>>();
    let mut index_keys = shape
        .index_infos
        .iter()
        .map(|index| {
            store
                .index_info(*index)
                .map(super::signatures::IndexInfo::key_type)
                .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target))
        })
        .collect::<Result<HashSet<_>, _>>()?;
    for base in &shape.base_types {
        let Some(base) = mapped_inherited_type(store, shape, *base)? else {
            return Ok(None);
        };
        let (properties, indexes) = if validate_direct_generic_reference(store, base).is_ok() {
            let Some(members) = validate_generic_interface_members(store, base, array_targets)?
            else {
                return Ok(None);
            };
            let indexes = store
                .type_payload(base)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.index_infos.clone())
                .unwrap_or_default();
            (members.properties, indexes)
        } else if matches!(
            validate_resolved_declared_property_object(store, base),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        ) {
            let structured = store
                .type_payload(base)
                .and_then(|record| record.data().structured())
                .ok_or(GenericInterfaceMemberError::UnsupportedTarget(base))?;
            (
                structured.properties.clone().unwrap_or_default(),
                structured.index_infos.clone().unwrap_or_default(),
            )
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
        for index in indexes {
            let key = store
                .index_info(index)
                .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(base))?
                .key_type();
            if index_keys.insert(key) {
                inherited_indexes.push(index);
            }
        }
    }
    Ok(Some((inherited, inherited_indexes)))
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
    let (_, source_parameters, _, properties, index_infos) = validate_declared_target(
        store,
        direct.target,
        array_targets,
        &mut active,
        0,
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
        index_infos,
        base_types,
        inherited_properties: Vec::new(),
        inherited_index_infos: Vec::new(),
        inherited_members_ready: false,
    };
    if let Some((properties, indexes)) = cached_inherited_properties(store, &shape, array_targets)?
    {
        shape.inherited_properties = properties;
        shape.inherited_index_infos = indexes;
        shape.inherited_members_ready = true;
    }
    if reference != shape.target {
        let mut target_shape = GenericInterfaceShape {
            reference: shape.target,
            target: shape.target,
            source_parameters: shape.source_parameters.clone(),
            target_arguments: shape.source_parameters.clone(),
            properties: shape.properties.clone(),
            index_infos: shape.index_infos.clone(),
            base_types: shape.base_types.clone(),
            inherited_properties: Vec::new(),
            inherited_index_infos: Vec::new(),
            inherited_members_ready: false,
        };
        if let Some((properties, indexes)) =
            cached_inherited_properties(store, &target_shape, array_targets)?
        {
            target_shape.inherited_properties = properties;
            target_shape.inherited_index_infos = indexes;
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
    heritage_start: usize,
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
    let (owner, source_parameters, declared_members, mut properties, index_infos) =
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
            if active[heritage_start..].contains(&reference.target) {
                return Err(GenericInterfaceMemberError::InvalidTarget(target));
            }
            member_type_requires_instantiation(store, base, &mapper_parameters, array_targets)?;
            validate_declared_target(
                store,
                reference.target,
                array_targets,
                active,
                heritage_start,
                validated,
            )?;
        } else if !matches!(
            validate_resolved_declared_property_object(store, base),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        ) {
            return Err(GenericInterfaceMemberError::UnsupportedTarget(base));
        }
    }
    for property in &mut properties {
        if property.method {
            let signatures = store
                .type_payload(property.type_)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .ok_or(GenericInterfaceMemberError::InvalidMember(property.symbol))?
                .to_vec();
            for signature in signatures {
                let signature_record = store
                    .signature(signature)
                    .ok_or(GenericInterfaceMemberError::InvalidMember(property.symbol))?;
                let return_type = signature_record
                    .resolved_return_type()
                    .ok_or(GenericInterfaceMemberError::InvalidMember(property.symbol))?;
                let parameter_types = store
                    .callable_signature_parameter_types(signature)
                    .filter(|types| types.len() == signature_record.parameters().len())
                    .ok_or(GenericInterfaceMemberError::InvalidMember(property.symbol))?
                    .to_vec();
                let mut signature_parameters = mapper_parameters.clone();
                signature_parameters.extend_from_slice(signature_record.type_parameters());
                property.requires_proxy |= !signature_record.type_parameters().is_empty();
                for type_ in parameter_types
                    .into_iter()
                    .chain(std::iter::once(return_type))
                {
                    property.requires_proxy |= member_type_requires_instantiation(
                        store,
                        type_,
                        &signature_parameters,
                        array_targets,
                    )?;
                    validate_nested_reference_targets(
                        store,
                        type_,
                        array_targets,
                        active,
                        validated,
                        &mut HashSet::new(),
                    )?;
                }
            }
        } else {
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
    }
    for index in &index_infos {
        let value = store
            .index_info(*index)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?
            .value_type();
        member_type_requires_instantiation(store, value, &mapper_parameters, array_targets)?;
        validate_nested_reference_targets(
            store,
            value,
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
    Ok((
        owner,
        source_parameters,
        declared_members,
        properties,
        index_infos,
    ))
}

fn member_type_requires_instantiation(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, GenericInterfaceMemberError> {
    member_type_requires_instantiation_worker(
        store,
        type_,
        mapper_parameters,
        array_targets,
        &mut HashSet::new(),
    )
}

fn member_type_requires_instantiation_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<bool, GenericInterfaceMemberError> {
    if !active.insert(type_) {
        return Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_));
    }
    let result = member_type_requires_instantiation_inner(
        store,
        type_,
        mapper_parameters,
        array_targets,
        active,
    );
    active.remove(&type_);
    result
}

fn member_type_requires_instantiation_inner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<bool, GenericInterfaceMemberError> {
    if store.type_has_function_type_provenance(type_) {
        let (_, function) = function_member_signature(store, type_)
            .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(type_))?;
        let narrowed = store
            .signature(function.source)
            .and_then(super::signatures::Signature::resolved_type_predicate)
            .and_then(|predicate| store.type_predicate(predicate))
            .and_then(super::signatures::TypePredicate::type_id);
        let mut requires = false;
        for type_ in function
            .parameter_types
            .into_iter()
            .chain([function.return_type])
            .chain(narrowed)
        {
            requires |= member_type_requires_instantiation_worker(
                store,
                type_,
                mapper_parameters,
                array_targets,
                active,
            )?;
        }
        return Ok(requires);
    }
    if let Some(TypeData::IndexedAccess(indexed)) = store
        .type_payload(type_)
        .map(super::type_records::TypeRecord::data)
    {
        if indexed.access_flags != AccessFlags::NONE {
            return Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_));
        }
        member_type_requires_instantiation_worker(
            store,
            indexed.object_type,
            mapper_parameters,
            array_targets,
            active,
        )?;
        member_type_requires_instantiation_worker(
            store,
            indexed.index_type,
            mapper_parameters,
            array_targets,
            active,
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
        || !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
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
        || interface.resolved_base_constructor_type.is_some()
        || interface
            .resolved_base_types
            .as_ref()
            .is_some_and(Vec::is_empty)
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || (!record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            && structured != &StructuredTypeData::default())
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
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
    if !interface.base_types_resolved || !interface.declared_members_resolved {
        if !interface.base_types_resolved
            && !interface.declared_members_resolved
            && interface.resolved_base_types.is_none()
            && declared_members.is_none()
            && !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
            && structured == &StructuredTypeData::default()
            && cold_generic_interface_has_authenticated_non_property_members(
                store,
                owner,
                owner_declarations,
                raw_members,
                &parameter_symbols,
            )
        {
            return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
        }
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let index_infos = interface
        .declared_index_infos
        .as_deref()
        .unwrap_or_default()
        .to_vec();
    let index_symbol = raw_table.get(InternalSymbolName::Index.as_ref());
    if index_infos.is_empty() != index_symbol.is_none()
        || interface
            .declared_index_infos
            .as_ref()
            .is_some_and(Vec::is_empty)
        || index_symbol.is_some_and(|symbol| {
            !valid_index_symbol(store, owner, owner_declarations, symbol, &index_infos)
        })
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let declared_count = declared_table.map_or(0, ts_binder::semantic::SymbolTable::len);
    let resolved_table = store
        .members_and_exports_links(owner)
        .and_then(|links| links.table(MembersOrExportsResolutionKind::ResolvedMembers))
        .map(|members| {
            store
                .symbol_table(members)
                .ok_or(GenericInterfaceMemberError::InvalidTarget(target))
        })
        .transpose()?;

    let mut properties = Vec::with_capacity(declared_count);
    let mut seen = HashSet::with_capacity(declared_count);
    let mut seen_declarations = HashSet::with_capacity(declared_count);
    let mut late_count = 0usize;
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
        let method = property.flags().contains(SymbolFlags::METHOD);
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
            if !(if method {
                store.source_node_kind(*declaration) == Some(SyntaxKind::MethodSignature)
            } else {
                matches!(
                    store.source_node_kind(*declaration),
                    Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                )
            }) || !declaration.is_for(parent.arena, parent.file)
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
        let late = property.check_flags().contains(CheckFlags::LATE)
            || property.flags().contains(SymbolFlags::TRANSIENT)
            || property.name().is_late_bound()
            || links.name_type.is_some();
        let valid_identity = if method {
            !late
                && property.flags() == SymbolFlags::METHOD
                && property.check_flags() == CheckFlags::NONE
                && raw_table
                    .get(property.name())
                    .and_then(|member| store.get_merged_symbol(member))
                    == Some(symbol)
                && links
                    == &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    })
                && valid_interface_method_value(store, symbol, type_).is_some()
        } else if late {
            valid_late_bound_unique_symbol_member(
                store,
                owner,
                symbol,
                declarations,
                links,
                resolved_table,
            )
        } else {
            let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
            property.flags().contains(SymbolFlags::PROPERTY)
                && property.flags().without(allowed_flags) == SymbolFlags::NONE
                && property.check_flags().bits() & !CheckFlags::READONLY.bits() == 0
                && property.name().as_utf8().is_some()
                && raw_table
                    .get(property.name())
                    .and_then(|member| store.get_merged_symbol(member))
                    == Some(symbol)
                && links
                    == &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    })
        };
        if !valid_identity
            || property.name() != name
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property
                .value_declaration()
                .is_none_or(|value| !declarations.contains(&value))
            || store.get_parent_of_symbol(symbol) != Some(owner)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || store.type_payload(type_).is_none()
            || !optional_type_is_valid
        {
            return Err(GenericInterfaceMemberError::InvalidMember(symbol));
        }
        if late {
            late_count = late_count
                .checked_add(1)
                .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
        }
        properties.push((
            owner_index,
            declaration,
            DeclaredProperty {
                symbol,
                name: property.name().to_owned(),
                type_,
                requires_proxy: false,
                method,
            },
        ));
    }
    let early_count = declared_count
        .checked_sub(late_count)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
    if raw_table.len()
        != early_count
            .checked_add(parameter_symbols.len())
            .and_then(|count| count.checked_add(usize::from(index_symbol.is_some())))
            .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    if late_count != 0
        && resolved_table.is_none_or(|resolved| {
            resolved.len() != raw_table.len() + late_count
                || raw_table.iter().any(|(name, symbol)| {
                    resolved
                        .get(name)
                        .and_then(|member| store.get_merged_symbol(member))
                        != store.get_merged_symbol(symbol)
                })
        })
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    if raw_table.iter().any(|(name, symbol)| {
        let Some(canonical) = store.get_merged_symbol(symbol) else {
            return true;
        };
        (!seen.contains(&canonical)
            && !parameter_symbols.contains(&canonical)
            && Some(canonical) != index_symbol)
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
    Ok((
        owner,
        source_parameters,
        declared_members,
        properties,
        index_infos,
    ))
}

fn cold_generic_interface_has_authenticated_non_property_members(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declarations: &[ts_ast::NodeRef],
    members: SymbolTableId,
    parameter_symbols: &HashSet<SemanticSymbolId>,
) -> bool {
    let Some(table) = store.symbol_table(members) else {
        return false;
    };
    let mut seen = HashSet::with_capacity(table.len());
    let mut unsupported_member = false;
    for (name, raw) in table.iter() {
        let Some(symbol) = store.get_merged_symbol(raw) else {
            return false;
        };
        let Some(record) = store.symbol(symbol) else {
            return false;
        };
        if !seen.insert(symbol)
            || record.name() != name
            || store.get_parent_of_symbol(symbol) != Some(owner)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
        {
            return false;
        }
        if parameter_symbols.contains(&symbol) {
            continue;
        }

        let Some(declarations) = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
        else {
            return false;
        };
        let (expected_kind, has_value) = if record.flags().contains(SymbolFlags::PROPERTY) {
            let allowed = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
            if record.flags().without(allowed) != SymbolFlags::NONE
                || record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
                || record.name().as_utf8().is_none()
            {
                return false;
            }
            (SyntaxKind::PropertySignature, true)
        } else if record.flags() == SymbolFlags::METHOD {
            if record.check_flags() != CheckFlags::NONE || record.name().as_utf8().is_none() {
                return false;
            }
            unsupported_member = true;
            (SyntaxKind::MethodSignature, true)
        } else if record.flags() == SymbolFlags::SIGNATURE {
            if record.check_flags() != CheckFlags::NONE {
                return false;
            }
            let kind = if record.name() == InternalSymbolName::Index.as_ref() {
                SyntaxKind::IndexSignature
            } else if record.name() == InternalSymbolName::Call.as_ref() {
                SyntaxKind::CallSignature
            } else if record.name() == InternalSymbolName::New.as_ref() {
                SyntaxKind::ConstructSignature
            } else {
                return false;
            };
            unsupported_member = true;
            (kind, false)
        } else {
            return false;
        };
        if record
            .value_declaration()
            .is_some_and(|declaration| !declarations.contains(&declaration))
            || record.value_declaration().is_some() != has_value
            || store
                .value_symbol_links(symbol)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
            || declarations.iter().any(|declaration| {
                let declaration_kind = store.source_node_kind(*declaration);
                (declaration_kind != Some(expected_kind)
                    && (expected_kind != SyntaxKind::PropertySignature
                        || declaration_kind != Some(SyntaxKind::PropertyDeclaration)))
                    || !matches!(
                        store.source_node_parent(*declaration),
                        Some(SourceNodeParent::Parent(parent))
                            if owner_declarations.contains(&parent)
                    )
            })
        {
            return false;
        }
    }
    unsupported_member
}

fn valid_late_bound_unique_symbol_member(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declarations: &[ts_ast::NodeRef],
    links: &ValueSymbolLinks,
    resolved_table: Option<&ts_binder::semantic::SymbolTable>,
) -> bool {
    let Some(property) = store.symbol(symbol) else {
        return false;
    };
    let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT;
    let allowed_checks = CheckFlags::LATE | CheckFlags::READONLY;
    let Some(name_type) = links.name_type else {
        return false;
    };
    let Some(type_record) = store.type_payload(name_type) else {
        return false;
    };
    let TypeData::UniqueEsSymbol(unique) = type_record.data() else {
        return false;
    };
    let Some(key) = type_record.symbol() else {
        return false;
    };
    let Some(key_record) = store.symbol(key) else {
        return false;
    };
    let Some(global_id) = store.symbol_store().assigned_global_symbol_id(key) else {
        return false;
    };
    let Some(suffix) = unique
        .name
        .as_bytes()
        .strip_prefix(b"\xFE@")
        .and_then(|name| name.strip_prefix(key_record.name().as_bytes()))
        .and_then(|name| name.strip_prefix(b"@"))
    else {
        return false;
    };

    property
        .flags()
        .contains(SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
        && property.flags().without(allowed_flags) == SymbolFlags::NONE
        && property.check_flags().contains(CheckFlags::LATE)
        && property.check_flags().bits() & !allowed_checks.bits() == 0
        && property.name().is_late_bound()
        && property.name() == unique.name.as_ref()
        && suffix == global_id.to_string().as_bytes()
        && type_record.flags() == TypeFlags::UNIQUE_ES_SYMBOL
        && type_record.object_flags() == ObjectFlags::NONE
        && type_record.alias().is_none()
        && key_record
            .flags()
            .contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
        && store.get_merged_symbol(key) == Some(key)
        && store.get_parent_of_symbol(key) == store.get_parent_of_symbol(owner)
        && key_record.value_declaration().is_some_and(|declaration| {
            store.source_node_kind(declaration) == Some(SyntaxKind::VariableDeclaration)
        })
        && store
            .value_symbol_links(key)
            .and_then(|links| links.resolved_type)
            == Some(name_type)
        && resolved_table.and_then(|table| table.get(property.name())) == Some(symbol)
        && declarations.iter().all(|declaration| {
            store
                .symbol_node_links(*declaration)
                .and_then(|links| links.resolved_symbol)
                == Some(symbol)
        })
        && links
            == &(ValueSymbolLinks {
                resolved_type: links.resolved_type,
                name_type: Some(name_type),
                ..ValueSymbolLinks::default()
            })
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
    if store
        .type_payload(template)
        .and_then(super::type_records::TypeRecord::symbol)
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD))
    {
        return cached_instantiated_interface_method_type_matches(
            store,
            template,
            cached,
            mapper,
            array_targets,
        );
    }
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
        let named = indexed_property_escaped_name(store, index).and_then(|name| {
            store
                .type_payload(object)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get(name.as_ref()))
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

fn cached_instantiated_interface_method_type_matches(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    let Some(source_record) = store.type_payload(source) else {
        return false;
    };
    let Some(method) = source_record.symbol() else {
        return false;
    };
    if valid_interface_method_value(store, method, source).is_none() {
        return false;
    }
    let Some(source_signatures) = source_record
        .data()
        .structured()
        .and_then(|structured| structured.signatures.as_deref())
    else {
        return false;
    };
    let Some(actual_record) = store.type_payload(actual) else {
        return false;
    };
    let TypeData::Object(object) = actual_record.data() else {
        return false;
    };
    let Some(actual_signatures) = object.structured.signatures.as_deref() else {
        return false;
    };
    if actual_record.flags() != TypeFlags::OBJECT
        || actual_record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || actual_record.symbol() != Some(method)
        || actual_record.alias().is_some()
        || object.target != Some(source)
        || object.mapper != Some(mapper)
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.index_infos.is_some()
        || object.structured.constrained != ConstrainedTypeData::default()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || actual_signatures.len() != source_signatures.len()
        || object.structured.call_signature_count != actual_signatures.len()
    {
        return false;
    }
    let mut seen = HashSet::with_capacity(actual_signatures.len());
    source_signatures
        .iter()
        .copied()
        .zip(actual_signatures.iter().copied())
        .all(|(source_signature, actual_signature)| {
            let Some(original) = store.signature(source_signature) else {
                return false;
            };
            let Some(instantiated) = store.signature(actual_signature) else {
                return false;
            };
            let Some(source_return) = original.resolved_return_type() else {
                return false;
            };
            let Some(actual_return) = instantiated.resolved_return_type() else {
                return false;
            };
            let Some(parameter_types) = store.callable_signature_parameter_types(source_signature)
            else {
                return false;
            };
            let Some(signature_mapper) = validated_instantiated_method_mapper(
                store,
                original,
                instantiated,
                mapper,
                array_targets,
            ) else {
                return false;
            };
            if !seen.insert(actual_signature)
                || instantiated.flags() != (original.flags() & SignatureFlags::PROPAGATING_FLAGS)
                || instantiated.declaration() != original.declaration()
                || instantiated.this_parameter().is_some()
                || instantiated.parameters().len() != original.parameters().len()
                || parameter_types.len() != original.parameters().len()
                || instantiated.min_argument_count() != original.min_argument_count()
                || instantiated.target() != Some(source_signature)
                || instantiated.mapper() != Some(signature_mapper)
                || !instantiated_method_type_matches(
                    store,
                    source_return,
                    actual_return,
                    signature_mapper,
                    array_targets,
                )
            {
                return false;
            }
            instantiated
                .parameters()
                .iter()
                .copied()
                .zip(original.parameters().iter().copied())
                .zip(parameter_types.iter().copied())
                .all(|((parameter, source_parameter), template)| {
                    let Some(links) = store.value_symbol_links(parameter) else {
                        return false;
                    };
                    let Some(type_) = links.resolved_type else {
                        return false;
                    };
                    let valid_links = if parameter == source_parameter {
                        links
                            == &(ValueSymbolLinks {
                                resolved_type: Some(type_),
                                ..ValueSymbolLinks::default()
                            })
                            && type_ == template
                    } else {
                        links
                            == &(ValueSymbolLinks {
                                resolved_type: Some(type_),
                                target: Some(source_parameter),
                                mapper: Some(signature_mapper),
                                name_type: store
                                    .value_symbol_links(source_parameter)
                                    .and_then(|links| links.name_type),
                                ..ValueSymbolLinks::default()
                            })
                    };
                    valid_links
                        && instantiated_method_type_matches(
                            store,
                            template,
                            type_,
                            signature_mapper,
                            array_targets,
                        )
                })
        })
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
                let heritage_start = active_targets.len();
                validate_declared_target(
                    store,
                    reference.target,
                    array_targets,
                    active_targets,
                    heritage_start,
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
    let expected_index_count = shape
        .index_infos
        .len()
        .checked_add(shape.inherited_index_infos.len())
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
            shape.reference,
        ))?;
    let indexes = match structured.index_infos.as_deref() {
        None if expected_index_count == 0 => &[][..],
        Some(indexes) if indexes.len() == expected_index_count && !indexes.is_empty() => indexes,
        _ => {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(
                shape.reference,
            ));
        }
    };
    let (own_indexes, inherited_indexes) = indexes.split_at(shape.index_infos.len());
    if own_indexes
        .iter()
        .zip(&shape.index_infos)
        .any(|(actual, source)| {
            !valid_instantiated_index_info(store, shape, *source, *actual, mapper, array_targets)
        })
        || inherited_indexes != shape.inherited_index_infos.as_slice()
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

fn valid_instantiated_index_info(
    store: &CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    source: IndexInfoId,
    actual: IndexInfoId,
    mapper: Option<TypeMapperId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    let Some(source_info) = store.index_info(source) else {
        return false;
    };
    let Some(actual_info) = store.index_info(actual) else {
        return false;
    };
    if source_info.key_type() != actual_info.key_type()
        || source_info.is_readonly() != actual_info.is_readonly()
        || source_info.declaration() != actual_info.declaration()
        || source_info.components() != actual_info.components()
        || source_info.index_symbol().is_some()
        || actual_info.index_symbol().is_some()
    {
        return false;
    }
    let value_matches = if let Some(mapper) = mapper {
        cached_instantiated_property_type_matches(
            store,
            source_info.value_type(),
            actual_info.value_type(),
            mapper,
            array_targets,
        )
    } else {
        mapped_inherited_type(store, shape, source_info.value_type())
            .ok()
            .flatten()
            == Some(actual_info.value_type())
    };
    value_matches && (source == actual) == (source_info.value_type() == actual_info.value_type())
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
    let index_count = shape
        .index_infos
        .len()
        .checked_add(shape.inherited_index_infos.len())
        .ok_or(GenericInterfaceMemberError::Capacity(shape.reference))?;
    let table = if count == 0 {
        None
    } else {
        Some(prepare_member_table(shape.reference, count)?)
    };
    if !store.try_reserve_checker_symbol_allocations(proxy_count, usize::from(count != 0))
        || !store.try_reserve_mappers(usize::from(proxy_count != 0))
        || !store.try_reserve_value_symbol_links(proxy_count)
        || !store.try_reserve_index_infos(shape.index_infos.len())
    {
        return Err(GenericInterfaceMemberError::Capacity(shape.reference));
    }
    let mut index_infos = Vec::new();
    index_infos
        .try_reserve_exact(index_count)
        .map_err(|_| GenericInterfaceMemberError::Capacity(shape.reference))?;
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
        index_infos,
    })
}

fn publish_cold_members(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    plan: ColdMembersPlan,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
    let ColdMembersPlan {
        mapper_sources,
        mapper_targets,
        requires_mapper,
        table,
        properties: planned_properties,
        mut index_infos,
    } = plan;
    let mapper = requires_mapper.then(|| {
        store
            .new_type_mapper(mapper_sources.clone(), mapper_targets.clone())
            .expect("prevalidated mapper endpoints remain store-owned")
    });
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    for source in &shape.index_infos {
        let index = if let Some(mapper) = mapper {
            instantiate_generic_index_info_with_array_targets(
                store,
                shape.reference,
                *source,
                mapper,
                array_targets,
                &mut session,
            )?
        } else {
            let info = store
                .index_info(*source)
                .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target))?;
            let key = info.key_type();
            let value = info.value_type();
            let readonly = info.is_readonly();
            let declaration = info.declaration();
            let components = info.components().to_vec();
            let instantiated = instantiate_type_with_vector_and_session(
                store,
                value,
                &mapper_sources,
                &mapper_targets,
                array_targets,
                &mut session,
            )
            .map_err(|error| property_instantiation_error(value, &error))?;
            if instantiated == value {
                *source
            } else {
                store
                    .alloc_index_info(key, instantiated, readonly, declaration, components)
                    .ok_or(GenericInterfaceMemberError::Capacity(shape.reference))?
            }
        };
        index_infos.push(index);
    }
    index_infos.extend_from_slice(&shape.inherited_index_infos);
    let members = table.map(|table| store.alloc_prepared_symbol_table(table));
    let mut properties = Vec::with_capacity(planned_properties.len());
    for property in planned_properties {
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
        (!index_infos.is_empty()).then_some(index_infos),
    ));
    Ok(InstantiatedInterfaceMembers {
        reference: shape.reference,
        target: shape.target,
        mapper,
        members,
        properties,
    })
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
        LateBoundLinks, MembersAndExportsLinks, ResolvedSignatureState, SignatureLinks,
        SymbolNodeLinks, TypeNodeLinks, bootstrap::UnionReduction, signatures::ElementFlags,
        tuple_types::CanonicalTupleTypeRequest,
    };
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        InternalSymbolName,
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

    #[derive(Clone, Copy)]
    struct LateBoundUniqueSymbolTarget {
        target: TypeId,
        key_type: TypeId,
        declaration: NodeRef,
        anonymous: SemanticSymbolId,
        late: SemanticSymbolId,
    }

    fn publish_late_bound_unique_symbol_target_for_test(
        parsed: &ParseResult,
        file: FileId,
        context: &mut CanonicalCheckerContext<'_>,
    ) -> LateBoundUniqueSymbolTarget {
        let owner = source_symbol(parsed, file, context, "Box");
        let key = source_symbol(parsed, file, context, "key");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let parameter = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("Box must retain its generic interface target"),
        };
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let name = match &record.data {
                    NodeData::PropertyDeclaration(property) => property.name,
                    NodeData::PropertySignatureDeclaration(property) => property.name,
                    _ => return None,
                };
                (parsed.arena.get(name)?.kind == SyntaxKind::ComputedPropertyName)
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("Box must retain its computed property declaration");
        let anonymous = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let raw_members = context.store().symbol(owner).unwrap().members().unwrap();
        let first = context
            .store()
            .symbol_table(raw_members)
            .and_then(|members| members.get_source("first"))
            .unwrap();
        let last = context
            .store()
            .symbol_table(raw_members)
            .and_then(|members| members.get_source("last"))
            .unwrap();
        let (string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let store = context.store_mut_for_test();
        let key_type = store.alloc_unique_es_symbol_type(key).unwrap();
        let key_name = match store.type_payload(key_type).unwrap().data() {
            TypeData::UniqueEsSymbol(unique) => unique.name.clone(),
            _ => panic!("the key must retain its unique symbol identity"),
        };
        assert!(store.set_value_symbol_links(
            key,
            ValueSymbolLinks {
                resolved_type: Some(key_type),
                ..ValueSymbolLinks::default()
            },
        ));

        let source_flags = store.symbol(anonymous).unwrap().flags();
        let mut late_data =
            SymbolData::new(source_flags | SymbolFlags::TRANSIENT, key_name.clone());
        late_data.check_flags = CheckFlags::LATE;
        late_data.declarations = Some(vec![declaration]);
        late_data.value_declaration = Some(declaration);
        late_data.parent = Some(owner);
        let late = store.alloc_symbol(late_data).unwrap();
        assert!(store.set_value_symbol_links(
            late,
            ValueSymbolLinks {
                resolved_type: Some(parameter),
                name_type: Some(key_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_late_bound_links(
            anonymous,
            LateBoundLinks {
                late_symbol: Some(late),
            },
        ));
        assert!(store.set_symbol_node_links(
            declaration,
            SymbolNodeLinks {
                resolved_symbol: Some(late),
            },
        ));

        let resolved_members = store.clone_symbol_table(raw_members).unwrap();
        assert_eq!(
            store.insert_symbol(resolved_members, key_name.clone(), late),
            Some(None),
        );
        let mut member_links = MembersAndExportsLinks::default();
        member_links.tables[MembersOrExportsResolutionKind::ResolvedMembers as usize] =
            Some(resolved_members);
        assert!(store.set_members_and_exports_links(owner, member_links));

        assert!(store.publish_interface_no_base_resolution(target));
        let declared_members = store.alloc_symbol_table();
        for (name, symbol, type_) in [
            (EscapedName::source("first"), first, string),
            (EscapedName::source("last"), last, number),
        ] {
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                store.insert_symbol(declared_members, name, symbol),
                Some(None)
            );
        }
        assert_eq!(
            store.insert_symbol(declared_members, key_name, late),
            Some(None),
        );
        assert!(store.set_interface_declared_members(
            target,
            true,
            Some(declared_members),
            None,
            None,
            None,
        ));

        LateBoundUniqueSymbolTarget {
            target,
            key_type,
            declaration,
            anonymous,
            late,
        }
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
    fn cold_generic_interfaces_with_non_property_members_are_unsupported() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface ConcatArray<T> { ",
            "readonly length: number; ",
            "readonly [n: number]: T; ",
            "join(separator?: string): string; ",
            "slice(start?: number, end?: number): T[]; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_218);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let global_types = context.global_types().clone();
        let owner = source_symbol(&parsed, file, &context, "ConcatArray");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();
        let element = store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, number],
                &[element, element],
                false,
            ))
            .unwrap();
        let reference = store
            .create_direct_generic_reference_type(target, &[tuple])
            .unwrap();
        let method = store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("join"))
            .unwrap();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            validate_generic_interface_members(
                store,
                reference,
                Some(CanonicalArrayTargets::from_global_types(&global_types)),
            ),
            Err(GenericInterfaceMemberError::UnsupportedTarget(target)),
        );
        assert!(store.set_symbol_flags(method, SymbolFlags::PROPERTY, CheckFlags::NONE));
        assert_eq!(
            validate_generic_interface_members(
                store,
                reference,
                Some(CanonicalArrayTargets::from_global_types(&global_types)),
            ),
            Err(GenericInterfaceMemberError::InvalidTarget(target)),
        );
        assert!(store.set_symbol_flags(method, SymbolFlags::METHOD, CheckFlags::NONE));
        assert!(store.set_interface_base_resolution(target, true, None, None));
        assert_eq!(
            validate_generic_interface_members(
                store,
                reference,
                Some(CanonicalArrayTargets::from_global_types(&global_types)),
            ),
            Err(GenericInterfaceMemberError::InvalidTarget(target)),
        );
        assert!(store.set_interface_base_resolution(target, false, None, None));
        assert_eq!(
            validate_generic_interface_members(
                store,
                reference,
                Some(CanonicalArrayTargets::from_global_types(&global_types)),
            ),
            Err(GenericInterfaceMemberError::UnsupportedTarget(target)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn global_array_method_overloads_instantiate_for_a_tuple_receiver() {
        let parsed = parse_source_file(concat!(
            "interface ConcatArray<T> {} ",
            "interface Array<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} interface ReadonlyArray<T> {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_217);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let global_types = context.global_types().clone();
        let concat_owner = source_symbol(&parsed, file, &context, "ConcatArray");
        let concat_target = context.get_declared_type_of_symbol(concat_owner).unwrap();
        let (method, element, declarations) = {
            let store = context.store();
            let owner = store
                .type_payload(global_types.array_type)
                .and_then(super::super::type_records::TypeRecord::symbol)
                .unwrap();
            let method = store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("concat"))
                .unwrap();
            let TypeData::Interface(array) =
                store.type_payload(global_types.array_type).unwrap().data()
            else {
                panic!("Array must retain its generic interface target")
            };
            let [element] = array.reference.resolved_type_arguments.as_deref().unwrap() else {
                panic!("Array must have one generic element")
            };
            (
                method,
                *element,
                store
                    .symbol(method)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .to_vec(),
            )
        };
        let plans = declarations
            .iter()
            .copied()
            .map(|declaration| {
                let NodeData::MethodSignatureDeclaration(signature) =
                    &parsed.arena.get(declaration.node).unwrap().data
                else {
                    panic!("concat must preserve its method declaration")
                };
                let [parameter] = signature.parameters.nodes.as_slice() else {
                    panic!("concat must preserve one rest parameter")
                };
                let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
                let NodeData::ParameterDeclaration(parameter_data) =
                    &parsed.arena.get(parameter.node).unwrap().data
                else {
                    panic!("concat must preserve its parameter declaration")
                };
                (
                    declaration,
                    context.file(file).unwrap().1.symbol(parameter).unwrap(),
                    NodeRef::new(
                        parameter.arena,
                        parameter.file,
                        parameter_data.type_.unwrap(),
                    ),
                    NodeRef::new(
                        declaration.arena,
                        declaration.file,
                        signature.type_.unwrap(),
                    ),
                )
            })
            .collect::<Vec<_>>();

        let store = context.store_mut_for_test();
        let concat_element = store
            .create_direct_generic_reference_type(concat_target, &[element])
            .unwrap();
        let combined_element = store
            .expression_union_type_with_global_types(
                &global_types,
                &[element, concat_element],
                UnionReduction::Literal,
            )
            .unwrap();
        let source_parameter_types = [concat_element, combined_element].map(|type_| {
            store
                .create_canonical_array_type(&global_types, type_, false)
                .unwrap()
        });
        let source = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let mut source_signatures = Vec::new();
        for ((declaration, parameter, parameter_annotation, return_annotation), parameter_type) in
            plans.iter().copied().zip(source_parameter_types)
        {
            assert!(store.set_type_node_links(
                parameter_annotation,
                TypeNodeLinks {
                    resolved_type: Some(parameter_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_type_node_links(
                return_annotation,
                TypeNodeLinks {
                    resolved_type: Some(global_types.array_type),
                    ..TypeNodeLinks::default()
                },
            ));
            assert!(store.set_value_symbol_links(
                parameter,
                ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                },
            ));
            let signature = store
                .alloc_signature(
                    SignatureFlags::HAS_REST_PARAMETER,
                    Some(declaration),
                    Vec::new(),
                    None,
                    vec![parameter],
                    Some(global_types.array_type),
                    None,
                    0,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            source_signatures.push(signature);
        }
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(source),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            source,
            None,
            None,
            Some(source_signatures.clone()),
            None,
            None,
        ));
        for (&signature, &(_, _, _, annotation)) in source_signatures.iter().zip(&plans) {
            assert!(store.set_function_signature_return_annotation(signature, annotation, false));
        }
        assert!(
            store.set_callable_signature_parameter_types_batch(
                source_signatures
                    .iter()
                    .copied()
                    .zip(source_parameter_types)
                    .map(|(signature, type_)| (signature, vec![type_]))
                    .collect(),
            )
        );

        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let info = store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, number],
                &[info, info],
                false,
            ))
            .unwrap();
        let receiver = store
            .create_canonical_array_type(&global_types, tuple, false)
            .unwrap();
        let specialized =
            instantiate_published_generic_interface_method(store, &global_types, receiver, method)
                .unwrap();
        assert_ne!(specialized, source);
        let TypeData::Object(callable) = store.type_payload(specialized).unwrap().data() else {
            panic!("the receiver must own a specialized callable object")
        };
        let mapper = callable.mapper.unwrap();
        let signatures = callable.structured.signatures.as_ref().unwrap().clone();
        assert_eq!(callable.target, Some(source));
        assert_eq!(signatures.len(), 2);
        assert_eq!(callable.structured.call_signature_count, 2);

        let specialized_concat = store
            .create_direct_generic_reference_type(concat_target, &[tuple])
            .unwrap();
        let specialized_union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[tuple, specialized_concat],
                UnionReduction::Literal,
            )
            .unwrap();
        let expected_parameters = [specialized_concat, specialized_union].map(|element| {
            store
                .create_canonical_array_type(&global_types, element, false)
                .unwrap()
        });
        for ((&signature, &original), expected) in signatures
            .iter()
            .zip(&source_signatures)
            .zip(expected_parameters)
        {
            let record = store.signature(signature).unwrap();
            let [parameter] = record.parameters() else {
                panic!("each specialized overload must retain its rest parameter")
            };
            let parameter = *parameter;
            assert_eq!(record.flags(), SignatureFlags::HAS_REST_PARAMETER);
            assert_eq!(record.target(), Some(original));
            assert_eq!(record.mapper(), Some(mapper));
            assert_eq!(record.resolved_return_type(), Some(receiver));
            assert_eq!(
                store
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type),
                Some(expected),
            );
            assert!(
                store
                    .symbol(parameter)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::TRANSIENT)
            );
        }
        for ((_, parameter, parameter_annotation, return_annotation), expected) in
            plans.iter().copied().zip(source_parameter_types)
        {
            assert_eq!(
                store
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type),
                Some(expected),
            );
            assert_eq!(
                store
                    .type_node_links(parameter_annotation)
                    .and_then(|links| links.resolved_type),
                Some(expected),
            );
            assert_eq!(
                store
                    .type_node_links(return_annotation)
                    .and_then(|links| links.resolved_type),
                Some(global_types.array_type),
            );
        }
        let warm = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(store, &global_types, receiver, method),
            Ok(specialized),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn late_bound_unique_symbol_members_keep_declaration_and_instantiation_identity() {
        let parsed = parse_source_file(concat!(
            "declare module \"prop-types\" {\n",
            "  export const key: unique symbol;\n",
            "  export interface Box<T> { first: string; [key]?: T; last: number }\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_214);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let target = publish_late_bound_unique_symbol_target_for_test(&parsed, file, &mut context);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target.target, &[string])
            .unwrap();

        let members = context
            .store_mut_for_test()
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        let [first, computed, last] = members.properties() else {
            panic!("the interface must preserve all members in declaration order")
        };
        let (first, computed, last) = (*first, *computed, *last);
        let store = context.store();
        let anonymous = store.symbol(target.anonymous).unwrap();
        let late = store.symbol(target.late).unwrap();
        let instantiated = store.symbol(computed).unwrap();
        let key_name = match store.type_payload(target.key_type).unwrap().data() {
            TypeData::UniqueEsSymbol(unique) => unique.name.clone(),
            _ => panic!("the computed property must retain its unique symbol key"),
        };

        assert_eq!(anonymous.name(), InternalSymbolName::Computed.as_ref());
        assert!(!anonymous.flags().contains(SymbolFlags::TRANSIENT));
        assert_eq!(anonymous.flags() | SymbolFlags::TRANSIENT, late.flags());
        assert_eq!(anonymous.declarations(), late.declarations());
        assert_eq!(anonymous.parent(), late.parent());
        assert_eq!(
            store.late_bound_links(target.anonymous),
            Some(&LateBoundLinks {
                late_symbol: Some(target.late),
            }),
        );
        assert_eq!(
            store
                .symbol_node_links(target.declaration)
                .and_then(|links| links.resolved_symbol),
            Some(target.late),
        );
        assert_eq!(store.symbol(first).unwrap().name().as_utf8(), Some("first"));
        assert_eq!(store.symbol(last).unwrap().name().as_utf8(), Some("last"));
        assert_ne!(computed, target.anonymous);
        assert_ne!(computed, target.late);
        assert_eq!(late.name(), key_name.as_ref());
        assert_eq!(instantiated.name(), key_name.as_ref());
        assert_eq!(
            instantiated.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT,
        );
        assert_eq!(
            instantiated.check_flags(),
            CheckFlags::LATE | CheckFlags::INSTANTIATED,
        );
        assert_eq!(instantiated.declarations(), Some(&[target.declaration][..]));
        assert_eq!(instantiated.parent(), late.parent());
        assert_eq!(
            store
                .symbol_table(members.members().unwrap())
                .and_then(|table| table.get(key_name.as_ref())),
            Some(computed),
        );
        assert_eq!(
            store.value_symbol_links(computed),
            Some(&ValueSymbolLinks {
                target: Some(target.late),
                mapper: members.mapper(),
                name_type: Some(target.key_type),
                ..ValueSymbolLinks::default()
            }),
        );

        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            demand_instantiated_property_type(
                context.store_mut_for_test(),
                reference,
                computed,
                None,
                &mut session,
            ),
            Ok(string),
        );
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
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
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn malformed_late_bound_unique_symbol_members_fail_before_instantiation() {
        let parsed = parse_source_file(concat!(
            "declare const key: unique symbol;\n",
            "declare const other: unique symbol;\n",
            "interface Box<T> { first: string; [key]?: T; last: number }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_215);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let target = publish_late_bound_unique_symbol_target_for_test(&parsed, file, &mut context);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target.target, &[string])
            .unwrap();
        let owner = context
            .store()
            .type_payload(target.target)
            .and_then(super::super::type_records::TypeRecord::symbol)
            .unwrap();
        let member_links = context
            .store()
            .members_and_exports_links(owner)
            .cloned()
            .unwrap();
        let other = source_symbol(&parsed, file, &context, "other");
        let other_type = context
            .store_mut_for_test()
            .alloc_unique_es_symbol_type(other)
            .unwrap();
        assert!(context.store_mut_for_test().set_value_symbol_links(
            other,
            ValueSymbolLinks {
                resolved_type: Some(other_type),
                ..ValueSymbolLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );

        for invalid in [0, 1, 2, 3, 4] {
            let original_links = context
                .store()
                .value_symbol_links(target.late)
                .cloned()
                .unwrap();
            match invalid {
                0 => {
                    assert!(context.store_mut_for_test().set_symbol_flags(
                        target.late,
                        SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT,
                        CheckFlags::NONE,
                    ));
                }
                1 => {
                    assert!(context.store_mut_for_test().set_value_symbol_links(
                        target.late,
                        ValueSymbolLinks {
                            name_type: None,
                            ..original_links.clone()
                        },
                    ));
                }
                2 => {
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_symbol_node_links(target.declaration, SymbolNodeLinks::default(),)
                    );
                }
                3 => {
                    assert!(context.store_mut_for_test().set_value_symbol_links(
                        target.late,
                        ValueSymbolLinks {
                            name_type: Some(other_type),
                            ..original_links.clone()
                        },
                    ));
                }
                4 => {
                    assert!(
                        context.store_mut_for_test().set_members_and_exports_links(
                            owner,
                            MembersAndExportsLinks::default(),
                        )
                    );
                }
                _ => unreachable!(),
            }
            assert_eq!(
                validate_generic_interface_members(context.store(), reference, None),
                Err(GenericInterfaceMemberError::InvalidMember(target.late)),
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
            assert!(context.store_mut_for_test().set_symbol_flags(
                target.late,
                SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT,
                CheckFlags::LATE,
            ));
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(target.late, original_links)
            );
            assert!(context.store_mut_for_test().set_symbol_node_links(
                target.declaration,
                SymbolNodeLinks {
                    resolved_symbol: Some(target.late),
                },
            ));
            assert!(
                context
                    .store_mut_for_test()
                    .set_members_and_exports_links(owner, member_links.clone())
            );
        }
    }

    #[test]
    fn indexed_generic_members_use_unique_symbol_property_identity() {
        let parsed = parse_source_file(concat!(
            "declare const key: unique symbol;\n",
            "interface Box<T> { first: string; [key]?: T; last: number }\n",
            "interface Pick<T> { selected: T }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_216);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let boxed = publish_late_bound_unique_symbol_target_for_test(&parsed, file, &mut context);
        let pick_symbol = source_symbol(&parsed, file, &context, "Pick");
        let pick_target = context.get_declared_type_of_symbol(pick_symbol).unwrap();
        let pick_parameter = match context.store().type_payload(pick_target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("Pick must retain its generic interface target"),
        };
        let template = context
            .store_mut_for_test()
            .alloc_indexed_access_type(pick_parameter, boxed.key_type, AccessFlags::NONE)
            .unwrap();
        publish_generic_target_for_test(&mut context, pick_target, &[("selected", template)], None);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let boxed_number = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(boxed.target, &[number])
            .unwrap();
        let selected = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(pick_target, &[boxed_number])
            .unwrap();

        let property = context
            .store_mut_for_test()
            .resolve_generic_interface_property(selected, "selected", None)
            .unwrap()
            .unwrap();

        assert_eq!(property.type_id(), number);
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(selected, "selected", None),
            Ok(Some(property)),
        );
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
    fn merged_generic_heritage_subsets_preserve_concrete_member_substitutions() {
        let parsed = parse_source_file(concat!(
            "interface Base<Item> { inherited: Item }\n",
            "interface Derived<Unused, Value> extends Base<Value> { own: Unused }\n",
            "interface Derived<Unused, Value> extends Base<Value> { extra: boolean }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_221);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());

        context.check_source_file(file).unwrap();

        let base_symbol = source_symbol(&parsed, file, &context, "Base");
        let derived_symbol = source_symbol(&parsed, file, &context, "Derived");
        let base = context
            .store()
            .declared_type_links(base_symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let target = context
            .store()
            .declared_type_links(derived_symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("the merged generic interface must retain its target")
        };
        let [_, value] = interface
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap()
        else {
            panic!("the derived target must retain both type parameters")
        };
        let value = *value;
        let [base_reference] = interface.resolved_base_types.as_deref().unwrap() else {
            panic!("the merged interface must retain one forwarded base")
        };
        let inherited = validate_direct_generic_reference(context.store(), *base_reference)
            .expect("the forwarded base must remain canonical");
        assert_eq!(inherited.target, base);
        assert_eq!(inherited.type_arguments, [value]);

        let (string, number, boolean) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        let concrete = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target, &[string, number])
            .unwrap();
        let members = context
            .store_mut_for_test()
            .resolve_generic_interface_members(concrete, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| context.store().symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("own"), Some("extra"), Some("inherited")],
        );
        for (name, expected) in [("own", string), ("extra", boolean), ("inherited", number)] {
            assert_eq!(
                context
                    .store_mut_for_test()
                    .resolve_generic_interface_property(concrete, name, None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                expected,
                "{name}",
            );
        }
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(context.diagnostics().is_empty());
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
    fn index_only_generic_interfaces_instantiate_without_allocating_a_mapper() {
        let parsed = parse_source_file("interface Lookup<T> { readonly [index: number]: T }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_219);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        context.check_source_file(file).unwrap();
        let owner = source_symbol(&parsed, file, &context, "Lookup");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let source = match context.store().type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => {
                assert!(interface.declared_members.is_none());
                interface.declared_index_infos.as_ref().unwrap()[0]
            }
            _ => panic!("Lookup must retain its generic interface target"),
        };
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();
        let mapper_count = context.store().mapper_len();

        let members = context
            .store_mut_for_test()
            .resolve_generic_interface_members(reference, None)
            .unwrap();

        assert!(members.properties().is_empty());
        assert!(members.members().is_none());
        assert!(members.mapper().is_none());
        assert_eq!(context.store().mapper_len(), mapper_count);
        let [index] = context
            .store()
            .type_payload(reference)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap()
        else {
            panic!("Lookup<string> must retain one instantiated index")
        };
        let index = *index;
        let actual = context.store().index_info(index).unwrap();
        let original = context.store().index_info(source).unwrap();
        assert_ne!(index, source);
        assert_eq!(actual.key_type(), original.key_type());
        assert_eq!(actual.value_type(), string);
        assert_eq!(actual.declaration(), original.declaration());
        assert!(actual.is_readonly());
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().index_info_len(),
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
                context.store().index_info_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            warm,
        );
    }

    #[test]
    fn generic_interfaces_preserve_instantiated_inherited_index_identity() {
        let parsed = parse_source_file(concat!(
            "interface Base<T> { readonly [name: string]: T }\n",
            "interface Derived<T> extends Base<T> { own: T }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_220);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let base_owner = source_symbol(&parsed, file, &context, "Base");
        let derived_owner = source_symbol(&parsed, file, &context, "Derived");
        let base = context.get_declared_type_of_symbol(base_owner).unwrap();
        let derived = context.get_declared_type_of_symbol(derived_owner).unwrap();
        let (base_parameter, derived_parameter) = {
            let TypeData::Interface(base_data) = context.store().type_payload(base).unwrap().data()
            else {
                panic!("Base must retain its generic target")
            };
            let TypeData::Interface(derived_data) =
                context.store().type_payload(derived).unwrap().data()
            else {
                panic!("Derived must retain its generic target")
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
        let declaration = context
            .store()
            .symbol(base_owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
            .and_then(|symbol| context.store().symbol(symbol))
            .and_then(ts_binder::semantic::Symbol::declarations)
            .and_then(|declarations| declarations.first())
            .copied()
            .unwrap();
        let (string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        publish_generic_target_for_test(&mut context, base, &[], None);
        let index = context
            .store_mut_for_test()
            .alloc_index_info(string, base_parameter, true, Some(declaration), Vec::new())
            .unwrap();
        assert!(context.store_mut_for_test().set_interface_declared_members(
            base,
            true,
            None,
            None,
            None,
            Some(vec![index]),
        ));
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

        assert_eq!(members.properties().len(), 1);
        let [inherited] = context
            .store()
            .type_payload(reference)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap()
        else {
            panic!("Derived<number> must retain its base index")
        };
        let inherited = *inherited;
        let inherited_info = context.store().index_info(inherited).unwrap();
        assert_eq!(inherited_info.key_type(), string);
        assert_eq!(inherited_info.value_type(), number);
        assert_eq!(inherited_info.declaration(), Some(declaration));
        assert!(inherited_info.is_readonly());
        let base_reference = context
            .store_mut_for_test()
            .create_direct_generic_reference_type(base, &[number])
            .unwrap();
        let [base_index] = context
            .store()
            .type_payload(base_reference)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap()
        else {
            panic!("the generic base must retain its instantiated index")
        };
        assert_eq!(inherited, *base_index);
        let warm = (
            context.store().mapper_len(),
            context.store().index_info_len(),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_members(reference, None),
            Ok(members),
        );
        assert_eq!(
            (
                context.store().mapper_len(),
                context.store().index_info_len()
            ),
            warm,
        );
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
