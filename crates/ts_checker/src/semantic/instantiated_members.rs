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
    CanonicalTypeMapperStore, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    declared::cached_ordinary_type_parameter_owner,
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession,
        instantiable_member_type_contains_variables, instantiate_type_with_session,
        instantiated_member_type_matches,
    },
    links::ValueSymbolLinks,
    reference_types::{DirectGenericReferenceError, validate_direct_generic_reference},
    store::SourceNodeParent,
    type_records::{ConstrainedTypeData, StructuredTypeData, TypeData},
    types::{ObjectFlags, TypeFlags},
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

#[derive(Clone, Debug)]
struct GenericInterfaceShape {
    reference: TypeId,
    target: TypeId,
    source_parameters: Vec<TypeId>,
    target_arguments: Vec<TypeId>,
    properties: Vec<DeclaredProperty>,
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

pub(super) fn resolve_members_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
    let shape = validate_shape(store, reference, array_targets)?;
    if let Some(cached) = validate_warm_members(store, &shape, array_targets)? {
        return Ok(cached);
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
        if !instantiated_member_type_matches(store, template, cached, mapper, array_targets)
            .unwrap_or(false)
        {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
        }
        return Ok(cached);
    }
    let instantiated =
        instantiate_type_with_session(store, template, mapper, array_targets, session)
            .map_err(|error| property_instantiation_error(template, &error))?;
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
        None,
        &mut active,
        &mut validated,
    )?;
    let shape = GenericInterfaceShape {
        reference,
        target: direct.target,
        source_parameters,
        target_arguments: direct.type_arguments,
        properties,
    };
    if reference != shape.target {
        let target_shape = GenericInterfaceShape {
            reference: shape.target,
            target: shape.target,
            source_parameters: shape.source_parameters.clone(),
            target_arguments: shape.source_parameters.clone(),
            properties: shape.properties.clone(),
        };
        validate_warm_members(store, &target_shape, array_targets)?;
    }
    Ok(shape)
}

fn validate_declared_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    root_declaration: Option<ts_ast::NodeRef>,
    active: &mut Vec<TypeId>,
    validated: &mut HashSet<TypeId>,
) -> Result<
    (
        SemanticSymbolId,
        Vec<TypeId>,
        Option<SymbolTableId>,
        Vec<DeclaredProperty>,
    ),
    GenericInterfaceMemberError,
> {
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
    let [declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    };
    if store.source_node_kind(*declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || store.source_node_is_exported(*declaration) != Some(false)
        || !matches!(
            store.source_node_parent(*declaration),
            Some(SourceNodeParent::Parent(parent))
                if store.source_node_kind(parent) == Some(SyntaxKind::SourceFile)
        )
        || root_declaration.is_some_and(|root| !declaration.is_for(root.arena, root.file))
    {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    }

    let mapper_parameters = mapper_parameters_for_target(store, target, &source_parameters)?;
    active.push(target);
    for property in &mut properties {
        property.requires_proxy = instantiable_member_type_contains_variables(
            store,
            property.type_,
            &mapper_parameters,
            array_targets,
        )
        .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(property.type_))?;
        validate_nested_reference_targets(
            store,
            property.type_,
            array_targets,
            *declaration,
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
) -> Result<
    (
        SemanticSymbolId,
        Vec<TypeId>,
        Option<SymbolTableId>,
        Vec<DeclaredProperty>,
    ),
    GenericInterfaceMemberError,
> {
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
        || owner_record.parent().is_some()
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
        || interface.resolved_base_types.is_some()
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

    let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(target));
    };
    let mut parameter_symbols = HashSet::with_capacity(source_parameters.len());
    for parameter in &source_parameters {
        let parameter_symbol = cached_ordinary_type_parameter_owner(store, *parameter)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
        let parameter_record = store
            .symbol(parameter_symbol)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(target))?;
        if parameter_record.parent() != Some(owner)
            || raw_table.get(parameter_record.name()) != Some(parameter_symbol)
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
    for (name, symbol) in declared_table.into_iter().flat_map(|table| table.iter()) {
        if !seen.insert(symbol) {
            return Err(GenericInterfaceMemberError::InvalidMember(symbol));
        }
        let property = store
            .symbol(symbol)
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let [declaration] = property.declarations().unwrap_or_default() else {
            return Err(GenericInterfaceMemberError::InvalidMember(symbol));
        };
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        let allowed_checks = CheckFlags::READONLY;
        let links = store
            .value_symbol_links(symbol)
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let type_ = links
            .resolved_type
            .ok_or(GenericInterfaceMemberError::InvalidMember(symbol))?;
        let optional_type_is_valid = store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            if !bootstrap.options.strict_null_checks
                || !property.flags().contains(SymbolFlags::OPTIONAL)
            {
                return true;
            }
            let sentinel = bootstrap.undefined_or_missing_type;
            type_ == sentinel
                || store.type_payload(type_).is_some_and(|record| {
                    record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN)
                        || matches!(
                            record.data(),
                            TypeData::Union(union) if union.union.types.contains(&sentinel)
                        )
                })
        });
        if !property.flags().contains(SymbolFlags::PROPERTY)
            || property.flags().without(allowed_flags) != SymbolFlags::NONE
            || property.check_flags().bits() & !allowed_checks.bits() != 0
            || property.name() != name
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || property.name().as_utf8().is_none()
            || property.value_declaration() != Some(*declaration)
            || property.parent() != Some(owner)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || !matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
            || store.source_node_parent(*declaration)
                != Some(SourceNodeParent::Parent(*owner_declaration))
            || !declaration.is_for(owner_declaration.arena, owner_declaration.file)
            || !seen_declarations.insert(*declaration)
            || raw_table.get(property.name()) != Some(symbol)
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
            *declaration,
            DeclaredProperty {
                symbol,
                name: property.name().to_owned(),
                type_,
                requires_proxy: false,
            },
        ));
    }
    if raw_table.iter().any(|(name, symbol)| {
        (!seen.contains(&symbol) && !parameter_symbols.contains(&symbol))
            || store
                .symbol(symbol)
                .is_none_or(|record| record.name() != name)
    }) {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    properties.sort_unstable_by_key(|(declaration, _)| *declaration);
    if properties.windows(2).any(|pair| pair[0].0 >= pair[1].0) {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let properties = properties
        .into_iter()
        .map(|(_, property)| property)
        .collect();
    Ok((owner, source_parameters, declared_members, properties))
}

#[allow(clippy::too_many_arguments)]
fn validate_nested_reference_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    root_declaration: ts_ast::NodeRef,
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
                    root_declaration,
                    active_targets,
                    validated_targets,
                    visited_types,
                )?;
            }
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
                    root_declaration,
                    active_targets,
                    validated_targets,
                    visited_types,
                )?;
            } else if let Ok(reference) = validate_direct_generic_reference(store, type_) {
                validate_declared_target(
                    store,
                    reference.target,
                    array_targets,
                    Some(root_declaration),
                    active_targets,
                    validated_targets,
                )?;
                for argument in reference.type_arguments {
                    validate_nested_reference_targets(
                        store,
                        argument,
                        array_targets,
                        root_declaration,
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
    let properties = match structured.properties.as_deref() {
        None if shape.properties.is_empty() => &[][..],
        Some(properties)
            if properties.len() == shape.properties.len() && !properties.is_empty() =>
        {
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
    let mapper = properties
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
    for (property, source) in properties.iter().zip(&shape.properties) {
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
                !instantiated_member_type_matches(store, source.type_, type_, mapper, array_targets)
                    .unwrap_or(false)
            })
        {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(
                *property,
            ));
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
    let count = shape.properties.len();
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
}
