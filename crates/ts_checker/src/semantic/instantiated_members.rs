//! Lazy members for generic-interface references and property-object aliases.
//!
//! This is the declared-member prefix of pinned `resolveTypeReferenceMembers`,
//! `resolveObjectTypeMembers`, `instantiateSymbolTable`, and
//! `instantiateSymbol`. A direct reference (including the generic target's
//! canonical identity reference) already belongs to its target's
//! instantiation cache before this module runs. Member resolution pads the
//! explicit arguments with that reference for the implicit `this` type
//! parameter, creates a mapper when properties require one, and preserves
//! source-owned methods and index signatures.
//!
//! Property-object aliases keep their type-literal target and exact alias
//! mapper. Their source annotations and instantiated property types stay lazy.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolData,
    SymbolFlags, SymbolTableId, semantic::PreparedSymbolTable,
};

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeHost, IndexInfoId, RelationUnavailable, SignatureId,
    SourceCheckError, TypeId, TypeMapperId,
    array_types::{CanonicalArrayReference, CanonicalArrayTargets},
    callable_sets::{
        CallableSetProjection, StoredCallableSetValidation, instantiated_method_type_matches,
        validated_instantiated_method_mapper,
    },
    callables::{
        CallableFamily, ValidatedSingleCallParameterDisplay, ValidatedSingleCallSignatureDisplay,
        ValidatedSingleCallable,
    },
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    declared_values::{SelectedDeclaredProperty, selected_property_object_alias_property},
    functions::{
        FunctionTypeDisplayError, StoredFunctionTypeValidation, function_type_display_projection,
        validate_stored_function_type,
    },
    instantiate::{
        InstantiationError, InstantiationLimits, InstantiationSession,
        cached_instantiation_with_vector, instantiable_member_type_contains_variables,
        instantiate_type_with_session, instantiate_type_with_vector_and_session,
        instantiated_member_type_matches,
    },
    links::{MembersOrExportsResolutionKind, ValueSymbolLinks},
    object_aliases::{
        PropertyObjectAliasProjection, cached_property_object_alias_physical_arguments,
        property_object_alias_projection,
    },
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_declared_property_object,
    },
    reference_types::{DirectGenericReferenceError, validate_direct_generic_reference},
    signatures::{
        ElementFlags, IndexInfo, SignatureFlags, SignatureInstantiationError, TupleElementInfo,
    },
    store::SourceNodeParent,
    structured_members::{
        valid_index_symbol, valid_interface_method_value, valid_late_bound_unique_symbol_member,
    },
    tuple_types::{CanonicalTupleTypeRequest, TupleTypeError},
    type_nodes::CanonicalTypeQuery,
    type_records::{
        ConstrainedTypeData, LiteralValue, ObjectTypeData, StructuredTypeData, TypeCacheState,
        TypeData, TypeDataKind, TypeParameterData,
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

/// The source binder table or the exact lazy table of one object-alias instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PropertyObjectAliasMembers {
    pub(super) receiver: TypeId,
    pub(super) target: TypeId,
    pub(super) members: Option<SymbolTableId>,
    pub(super) properties: Vec<SemanticSymbolId>,
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

#[derive(Clone, Debug, Eq, PartialEq)]
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

#[derive(Clone, Debug, Eq, PartialEq)]
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

/// Evidence created only after this producer observes a real caller limit event.
#[derive(Debug)]
pub(super) struct InstantiatedPropertyRecovery {
    valid: bool,
    method: bool,
    symbol: SemanticSymbolId,
    target: SemanticSymbolId,
    template: TypeId,
    mapper: TypeMapperId,
    result: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    identity: Vec<RecoveredPropertyTypeIdentity>,
}

/// Records an index result only after its producer observes a caller limit event.
#[derive(Debug)]
pub(super) struct InstantiatedIndexRecovery {
    valid: bool,
    index: IndexInfoId,
    source: IndexInfoId,
    shape: GenericInterfaceShape,
    mapper: Option<TypeMapperId>,
    mapper_sources: Vec<TypeId>,
    mapper_targets: Vec<TypeId>,
    key_type: TypeId,
    template: TypeId,
    result: TypeId,
    readonly: bool,
    declaration: Option<NodeRef>,
    components: Vec<NodeRef>,
    array_targets: Option<CanonicalArrayTargets>,
    error_type: TypeId,
    identity: Vec<RecoveredPropertyTypeIdentity>,
}

impl InstantiatedIndexRecovery {
    pub(super) const fn index(&self) -> IndexInfoId {
        self.index
    }

    pub(super) fn invalidate_for_raw_write(&mut self, symbol: SemanticSymbolId) -> bool {
        let invalidated = self.valid
            && (self
                .shape
                .properties
                .iter()
                .any(|property| property.symbol == symbol)
                || self.identity.iter().any(|identity| match &identity.shape {
                    RecoveredPropertyTypeShape::Object { signatures, .. } => {
                        signatures.iter().any(|signature| {
                            signature
                                .parameters
                                .iter()
                                .any(|(parameter, _)| *parameter == symbol)
                                || signature
                                    .this_parameter
                                    .as_ref()
                                    .is_some_and(|(parameter, _)| *parameter == symbol)
                        })
                    }
                    _ => false,
                }));
        if invalidated {
            self.valid = false;
        }
        invalidated
    }

    pub(super) fn invalidate_for_index_write(&mut self, index: IndexInfoId) -> bool {
        let invalidated = self.valid && (index == self.index || index == self.source);
        if invalidated {
            self.valid = false;
        }
        invalidated
    }

    pub(super) fn matches_published_info(&self, info: Option<&IndexInfo>) -> bool {
        self.valid
            && info.is_some_and(|info| {
                info.id() == self.index
                    && info.key_type() == self.key_type
                    && info.value_type() == self.result
                    && info.is_readonly() == self.readonly
                    && info.declaration() == self.declaration
                    && info.components() == self.components
                    && info.index_symbol().is_none()
            })
    }

    fn matches(
        &self,
        store: &CanonicalTypeMapperStore,
        shape: &GenericInterfaceShape,
        source: IndexInfoId,
        actual: IndexInfoId,
        mapper: Option<TypeMapperId>,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.source == source
            && self.index == actual
            && self.shape == *shape
            && self.mapper == mapper
            && self.matches_cached_identity(store, array_targets)
            && mapper_parameters_for_target(store, shape.target, &shape.source_parameters)
                .ok()
                .as_deref()
                == Some(self.mapper_sources.as_slice())
            && self.mapper_targets
                == shape
                    .target_arguments
                    .iter()
                    .copied()
                    .chain(std::iter::once(shape.reference))
                    .collect::<Vec<_>>()
    }

    fn matches_cached_identity(
        &self,
        store: &CanonicalTypeMapperStore,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.array_targets == array_targets
            && self.matches_published_info(store.index_info(self.index))
            && store.index_info(self.source).is_some_and(|info| {
                info.value_type() == self.template && info.index_symbol().is_none()
            })
            && self.mapper.is_none_or(|mapper| {
                store.type_mapper_has_exact_endpoints(
                    mapper,
                    &self.mapper_sources,
                    &self.mapper_targets,
                ) == Some(true)
            })
            && store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                bootstrap.error_type == self.error_type
                    && store.validate_union_constituent(self.error_type).is_ok()
            })
            && instantiated_index_recovery_identity(
                store,
                &[self.key_type, self.template, self.result, self.error_type],
                &self.mapper_sources,
                &self.mapper_targets,
                array_targets,
            )
            .is_some_and(|identity| identity == self.identity)
    }
}

fn instantiated_index_recovery_identity(
    store: &CanonicalTypeMapperStore,
    roots: &[TypeId],
    mapper_sources: &[TypeId],
    mapper_targets: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<Vec<RecoveredPropertyTypeIdentity>> {
    let roots = roots
        .iter()
        .chain(mapper_sources)
        .chain(mapper_targets)
        .copied()
        .collect::<Vec<_>>();
    property_recovery_type_identity(store, &roots, array_targets)
}

/// A current producer record borrowed without entering callable or graph validation.
#[derive(Clone, Copy, Debug)]
pub(super) struct InstantiatedPropertyRecoveryIdentity<'a> {
    recovery: &'a InstantiatedPropertyRecovery,
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct RecoveredPropertyTypeIdentity {
    type_: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<(
        super::TypeAliasId,
        Option<SemanticSymbolId>,
        Option<Vec<TypeId>>,
    )>,
    shape: RecoveredPropertyTypeShape,
}

#[derive(Debug, Eq, PartialEq)]
enum RecoveredPropertyTypeShape {
    Leaf(TypeDataKind),
    Literal {
        regular_type: TypeId,
    },
    Parameter(TypeParameterData),
    Array(CanonicalArrayReference),
    Reference {
        target: TypeId,
        arguments: Vec<TypeId>,
    },
    Tuple {
        target: TypeId,
        elements: Vec<TypeId>,
        infos: Vec<TupleElementInfo>,
        readonly: bool,
    },
    Union {
        members: Vec<TypeId>,
        origin: Option<TypeId>,
    },
    TemplateLiteral {
        texts: Vec<String>,
        types: Vec<TypeId>,
    },
    StringMapping(TypeId),
    IndexedAccess {
        object: TypeId,
        index: TypeId,
        access: AccessFlags,
    },
    Object {
        data: ObjectTypeData,
        signatures: Vec<RecoveredPropertySignatureIdentity>,
    },
}

#[derive(Debug, Eq, PartialEq)]
struct RecoveredPropertySignatureIdentity {
    signature: SignatureId,
    flags: SignatureFlags,
    declaration: Option<NodeRef>,
    type_parameters: Vec<TypeId>,
    type_parameter_data: Vec<TypeParameterData>,
    parameters: Vec<(SemanticSymbolId, ValueSymbolLinks)>,
    this_parameter: Option<(SemanticSymbolId, ValueSymbolLinks)>,
    min_argument_count: i32,
    return_type: Option<TypeId>,
    predicate: Option<super::TypePredicateId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
    composite: Option<(bool, Vec<SignatureId>)>,
}

impl InstantiatedPropertyRecovery {
    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) fn is_method_result(&self, type_: TypeId) -> bool {
        self.method && self.result == type_
    }

    pub(super) fn invalidate_for_raw_write(&mut self, symbol: SemanticSymbolId) -> bool {
        let invalidated = self.valid
            && (symbol == self.symbol
                || symbol == self.target
                || self.identity.iter().any(|identity| match &identity.shape {
                    RecoveredPropertyTypeShape::Object { signatures, .. } => {
                        signatures.iter().any(|signature| {
                            signature
                                .parameters
                                .iter()
                                .any(|(parameter, _)| *parameter == symbol)
                                || signature
                                    .this_parameter
                                    .as_ref()
                                    .is_some_and(|(parameter, _)| *parameter == symbol)
                        })
                    }
                    _ => false,
                }));
        if invalidated {
            self.valid = false;
        }
        invalidated
    }

    pub(super) fn matches_published_links(&self, links: Option<&ValueSymbolLinks>) -> bool {
        self.valid
            && links.is_some_and(|links| {
                links.target == Some(self.target)
                    && links.mapper == Some(self.mapper)
                    && links.resolved_type == Some(self.result)
            })
    }

    #[allow(clippy::too_many_arguments)] // Every producer identity is part of the recovery key.
    fn matches_identity(
        &self,
        store: &CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
        target: SemanticSymbolId,
        template: TypeId,
        mapper: TypeMapperId,
        result: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.symbol == symbol
            && self.target == target
            && self.template == template
            && self.mapper == mapper
            && self.result == result
            && self.matches_published_links(store.value_symbol_links(symbol))
            && store
                .value_symbol_links(target)
                .and_then(|links| links.resolved_type)
                == Some(template)
            && property_recovery_type_identity(store, &[template, result], array_targets)
                .is_some_and(|identity| identity == self.identity)
    }

    pub(super) fn checked_identity<'a>(
        &'a self,
        store: &'a CanonicalTypeMapperStore,
    ) -> Option<InstantiatedPropertyRecoveryIdentity<'a>> {
        self.matches_identity(
            store,
            self.symbol,
            self.target,
            self.template,
            self.mapper,
            self.result,
            self.array_targets,
        )
        .then_some(InstantiatedPropertyRecoveryIdentity { recovery: self })
    }

    #[allow(clippy::too_many_arguments)] // The graph check follows the same exact producer key.
    fn matches(
        &self,
        store: &CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
        target: SemanticSymbolId,
        template: TypeId,
        mapper: TypeMapperId,
        result: TypeId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        if !self.matches_identity(
            store,
            symbol,
            target,
            template,
            mapper,
            result,
            array_targets,
        ) {
            return false;
        }
        if self.method {
            return matches!(
                super::callable_sets::validate_stored_callable_set(store, result),
                StoredCallableSetValidation::Valid { .. }
            );
        }
        match array_targets {
            Some(targets) => store
                .validate_cached_array_capability_with_array_targets(targets, result)
                .is_ok(),
            None => store.validate_cached_array_capability(result).is_ok(),
        }
    }
}

impl InstantiatedPropertyRecoveryIdentity<'_> {
    pub(super) const fn source_type(self) -> TypeId {
        self.recovery.template
    }

    pub(super) const fn result_type(self) -> TypeId {
        self.recovery.result
    }

    pub(super) const fn method(self) -> SemanticSymbolId {
        self.recovery.target
    }

    pub(super) const fn mapper(self) -> TypeMapperId {
        self.recovery.mapper
    }

    pub(super) fn signature_mapper(
        self,
        source: SignatureId,
        actual: SignatureId,
    ) -> Option<TypeMapperId> {
        let signatures = |type_| {
            self.recovery.identity.iter().find_map(|identity| {
                if identity.type_ != type_ {
                    return None;
                }
                match &identity.shape {
                    RecoveredPropertyTypeShape::Object { signatures, .. } => Some(signatures),
                    _ => None,
                }
            })
        };
        let source_index = signatures(self.source_type())?
            .iter()
            .position(|entry| entry.signature == source)?;
        let actual_record = signatures(self.result_type())?.get(source_index)?;
        (actual_record.signature == actual && actual_record.target == Some(source))
            .then_some(actual_record.mapper)
            .flatten()
    }

    /// Checks the original mapper and proxy without asking the member graph to validate itself.
    pub(super) fn receiver(self, store: &CanonicalTypeMapperStore) -> Option<TypeId> {
        let (_, owner_type) = store.authenticated_interface_method_owner(self.method())?;
        let TypeData::Interface(interface) = store.type_payload(owner_type)?.data() else {
            return None;
        };
        let receiver = store.map_type(self.mapper(), interface.this_type?)?;
        let plan = plan_published_interface_method(
            store,
            self.recovery.array_targets,
            receiver,
            self.method(),
        )
        .ok()?;
        if plan.source != self.source_type()
            || store.type_mapper_has_exact_endpoints(
                self.mapper(),
                &plan.mapper_sources,
                &plan.mapper_targets,
            ) != Some(true)
        {
            return None;
        }
        let source = store.symbol(self.method())?;
        let proxy = store.symbol(self.recovery.symbol)?;
        let links = store.value_symbol_links(self.recovery.symbol)?;
        let members = store.type_payload(plan.receiver)?.data().structured()?;
        let table = store.symbol_table(members.members?)?;
        let expected_checks = CheckFlags::INSTANTIATED
            | (source.check_flags()
                & (CheckFlags::READONLY
                    | CheckFlags::LATE
                    | CheckFlags::OPTIONAL_PARAMETER
                    | CheckFlags::REST_PARAMETER));
        if proxy.flags() != source.flags() | SymbolFlags::TRANSIENT
            || proxy.check_flags() != expected_checks
            || proxy.name() != source.name()
            || proxy.declarations() != source.declarations()
            || proxy.value_declaration() != source.value_declaration()
            || proxy.parent() != source.parent()
            || proxy.members().is_some()
            || proxy.exports().is_some()
            || proxy.export_symbol().is_some()
            || store.get_merged_symbol(self.recovery.symbol) != Some(self.recovery.symbol)
            || table.get(proxy.name()) != Some(self.recovery.symbol)
            || !members
                .properties
                .as_deref()?
                .contains(&self.recovery.symbol)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(self.result_type()),
                    target: Some(self.method()),
                    mapper: Some(self.mapper()),
                    name_type: store
                        .value_symbol_links(self.method())
                        .and_then(|links| links.name_type),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        Some(plan.receiver)
    }
}

/// Retains type arguments but not member caches that can legitimately warm later.
pub(super) fn property_recovery_type_identity(
    store: &CanonicalTypeMapperStore,
    roots: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<Vec<RecoveredPropertyTypeIdentity>> {
    let mut pending = roots.to_vec();
    let mut seen = HashSet::new();
    let mut identity = Vec::new();
    while let Some(type_) = pending.pop() {
        if !seen.insert(type_) {
            continue;
        }
        let record = store.type_payload(type_)?;
        let alias = match record.alias() {
            Some(alias) => {
                let data = store.type_alias(alias)?;
                let arguments = data.type_arguments().map(<[TypeId]>::to_vec);
                pending.extend(arguments.as_deref().unwrap_or_default());
                Some((alias, data.symbol(), arguments))
            }
            None => None,
        };
        let shape = if let Some(tuple) = store.canonical_tuple_shape(type_).ok()? {
            let elements = tuple.element_types().to_vec();
            pending.extend(&elements);
            RecoveredPropertyTypeShape::Tuple {
                target: tuple.target(),
                elements,
                infos: tuple.element_infos().to_vec(),
                readonly: tuple.is_readonly(),
            }
        } else if let Some(array) = array_targets
            .map(|targets| store.canonical_array_reference_with_targets(targets, type_))
            .transpose()
            .ok()?
            .flatten()
        {
            pending.push(array.element_type);
            RecoveredPropertyTypeShape::Array(array)
        } else if let TypeData::Union(union) = record.data() {
            let members = union.union.types.clone();
            pending.extend(&members);
            pending.extend(union.origin);
            RecoveredPropertyTypeShape::Union {
                members,
                origin: union.origin,
            }
        } else if matches!(
            record.data(),
            TypeData::TypeReference(_) | TypeData::Interface(_)
        ) && let Ok(reference) = validate_direct_generic_reference(store, type_)
        {
            pending.extend(&reference.type_arguments);
            RecoveredPropertyTypeShape::Reference {
                target: reference.target,
                arguments: reference.type_arguments,
            }
        } else {
            match record.data() {
                TypeData::Intrinsic(_) => {
                    store.validate_union_constituent(type_).ok()?;
                    RecoveredPropertyTypeShape::Leaf(record.data().kind())
                }
                TypeData::Literal(literal) => {
                    store.validate_union_constituent(type_).ok()?;
                    pending.push(literal.regular_type);
                    RecoveredPropertyTypeShape::Literal {
                        regular_type: literal.regular_type,
                    }
                }
                TypeData::TypeParameter(parameter) if parameter.target.is_some() => {
                    let mut parameter = parameter.clone();
                    parameter.constrained = ConstrainedTypeData::default();
                    pending.extend(parameter.constraint);
                    pending.extend(parameter.target);
                    pending.extend(parameter.resolved_default_type);
                    RecoveredPropertyTypeShape::Parameter(parameter)
                }
                TypeData::TemplateLiteral(template) => {
                    pending.extend(&template.types);
                    RecoveredPropertyTypeShape::TemplateLiteral {
                        texts: template.texts.clone(),
                        types: template.types.clone(),
                    }
                }
                TypeData::StringMapping(mapping) => {
                    pending.push(mapping.target);
                    RecoveredPropertyTypeShape::StringMapping(mapping.target)
                }
                TypeData::IndexedAccess(indexed) => {
                    pending.extend([indexed.object_type, indexed.index_type]);
                    RecoveredPropertyTypeShape::IndexedAccess {
                        object: indexed.object_type,
                        index: indexed.index_type,
                        access: indexed.access_flags,
                    }
                }
                TypeData::Object(object) => {
                    let mut signatures = Vec::new();
                    for &signature in object.structured.signatures.as_deref().unwrap_or_default() {
                        let record = store.signature(signature)?;
                        let type_parameter_data = record
                            .type_parameters()
                            .iter()
                            .map(|type_| {
                                let TypeData::TypeParameter(parameter) =
                                    store.type_payload(*type_)?.data()
                                else {
                                    return None;
                                };
                                let mut parameter = parameter.clone();
                                parameter.constrained = ConstrainedTypeData::default();
                                pending.extend(parameter.constraint);
                                pending.extend(parameter.resolved_default_type);
                                Some(parameter)
                            })
                            .collect::<Option<Vec<_>>>()?;
                        let parameters = record
                            .parameters()
                            .iter()
                            .map(|symbol| {
                                Some((*symbol, store.value_symbol_links(*symbol)?.clone()))
                            })
                            .collect::<Option<Vec<_>>>()?;
                        let this_parameter = match record.this_parameter() {
                            Some(symbol) => {
                                Some((symbol, store.value_symbol_links(symbol)?.clone()))
                            }
                            None => None,
                        };
                        pending.extend(record.type_parameters());
                        pending.extend(record.resolved_return_type());
                        for (_, links) in parameters.iter().chain(this_parameter.iter()) {
                            pending.extend(links.resolved_type);
                            pending.extend(links.write_type);
                            pending.extend(links.name_type);
                        }
                        if let Some(predicate) = record.resolved_type_predicate() {
                            pending.extend(store.type_predicate(predicate)?.type_id());
                        }
                        signatures.push(RecoveredPropertySignatureIdentity {
                            signature,
                            flags: record.flags(),
                            declaration: record.declaration(),
                            type_parameters: record.type_parameters().to_vec(),
                            type_parameter_data,
                            parameters,
                            this_parameter,
                            min_argument_count: record.min_argument_count(),
                            return_type: record.resolved_return_type(),
                            predicate: record.resolved_type_predicate(),
                            target: record.target(),
                            mapper: record.mapper(),
                            composite: record.composite().map(|composite| {
                                (composite.is_union(), composite.signatures().to_vec())
                            }),
                        });
                    }
                    RecoveredPropertyTypeShape::Object {
                        data: object.clone(),
                        signatures,
                    }
                }
                _ => RecoveredPropertyTypeShape::Leaf(record.data().kind()),
            }
        };
        identity.push(RecoveredPropertyTypeIdentity {
            type_,
            flags: record.flags(),
            object_flags: record.object_flags()
                & !(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                    | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
                    | ObjectFlags::MEMBERS_RESOLVED),
            symbol: record.symbol(),
            alias,
            shape,
        });
    }
    Some(identity)
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
    table: Option<PreparedSymbolTable>,
    properties: Vec<ColdPropertyPlan>,
}

#[derive(Debug)]
struct ColdIndexValues {
    mapper: Option<TypeMapperId>,
    mapper_sources: Vec<TypeId>,
    mapper_targets: Vec<TypeId>,
    indexes: Vec<ColdIndexValue>,
}

#[derive(Debug)]
struct ColdIndexValue {
    source: IndexInfoId,
    key_type: TypeId,
    template: TypeId,
    result: TypeId,
    readonly: bool,
    declaration: Option<NodeRef>,
    components: Vec<NodeRef>,
    recovery: Option<(TypeId, Vec<RecoveredPropertyTypeIdentity>)>,
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
    optional_sentinel: Option<TypeId>,
    target: TypeId,
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
    /// publishes no transient property symbol, table, or structured-member
    /// cache. Failed instantiation can retain type and mapper identities.
    pub fn resolve_generic_interface_members(
        &mut self,
        reference: TypeId,
        array_target: Option<GenericInterfaceArrayTarget>,
    ) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
        let array_targets = array_target
            .map(|target| CanonicalArrayTargets::for_single_target_validation(target.target));
        resolve_members_with_array_targets(self, reference, array_targets)
    }

    /// Selects one own or inherited property from a direct generic interface reference.
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
        self.resolve_generic_interface_property_by_key(
            reference,
            EscapedNameRef::source(name),
            array_target,
        )
    }

    /// Selects a source-name or symbol-key property from a direct reference.
    ///
    /// The key is byte-exact. Unique and well-known symbol names are not
    /// converted to source text. This query uses the same member table and
    /// lazy property type as [`Self::resolve_generic_interface_property`].
    ///
    /// # Errors
    ///
    /// Returns [`GenericInterfaceMemberError`] for an unsupported receiver,
    /// an invalid declaration or cache, or allocation failure. A valid missing
    /// key returns `Ok(None)`.
    pub fn resolve_generic_interface_property_by_key(
        &mut self,
        reference: TypeId,
        name: EscapedNameRef<'_>,
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

/// A source template exposes its binder table without completing all annotations.
/// Only an instance with a cold structured table returns `None`.
pub(super) fn validate_property_object_alias_members(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
) -> Result<Option<PropertyObjectAliasMembers>, RelationUnavailable> {
    validate_property_object_alias_members_with_array_targets(store, receiver, None)
}

#[allow(clippy::too_many_lines)] // Source state and exact proxy state are checked together.
pub(super) fn validate_property_object_alias_members_with_array_targets(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<PropertyObjectAliasMembers>, RelationUnavailable> {
    let projection = property_object_alias_projection(store, receiver)?
        .ok_or(RelationUnavailable::UnsupportedStructuredType(receiver))?;
    reject_mismatched_property_object_alias_values(store, &projection)?;
    validate_property_object_alias_cache_cycles(store, &projection, array_targets)?;
    let (source_members, original_types) =
        validate_property_object_alias_source_members(store, &projection)?;
    if projection.type_ == projection.target {
        return Ok(Some(PropertyObjectAliasMembers {
            receiver,
            target: projection.target,
            members: source_members,
            properties: projection
                .properties
                .iter()
                .map(|property| property.symbol)
                .collect(),
        }));
    }
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let record = store.type_payload(receiver).ok_or_else(invalid)?;
    let structured = record.data().structured().ok_or_else(invalid)?;
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        if structured != &StructuredTypeData::default() {
            return Err(invalid());
        }
        return Ok(None);
    }
    let mapper = projection.mapper.ok_or_else(invalid)?;
    let (members, properties) =
        property_object_alias_member_table(store, receiver, projection.properties.len())?;
    if properties.is_empty() && members.is_some() {
        return Err(invalid());
    }
    for ((&property, source), original) in properties
        .iter()
        .zip(&projection.properties)
        .zip(original_types)
    {
        let record = store.symbol(property).ok_or_else(invalid)?;
        let target = store.symbol(source.symbol).ok_or_else(invalid)?;
        if members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(source.name.as_ref()))
            != Some(property)
        {
            return Err(invalid());
        }
        if property == source.symbol {
            let original = original.ok_or_else(invalid)?;
            if !matches!(
                instantiable_member_type_contains_variables(
                    store,
                    original,
                    &projection.parameters,
                    array_targets,
                ),
                Ok(false)
            ) {
                return Err(invalid());
            }
            continue;
        }
        let links = store.value_symbol_links(property).ok_or_else(invalid)?;
        let expected_checks = CheckFlags::INSTANTIATED
            | if source.readonly {
                CheckFlags::READONLY
            } else {
                CheckFlags::NONE
            };
        if record.flags() != target.flags() | SymbolFlags::TRANSIENT
            || record.check_flags() != expected_checks
            || record.name() != target.name()
            || record.declarations() != target.declarations()
            || record.value_declaration() != target.value_declaration()
            || record.parent() != target.parent()
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_merged_symbol(property) != Some(property)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    target: Some(source.symbol),
                    mapper: Some(mapper),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(invalid());
        }
        // A proxy created while its source was cold remains a proxy even if
        // that source later resolves to a constant type.
        match (original, links.resolved_type) {
            (Some(original), Some(cached)) => {
                let validation_targets = array_targets.or_else(|| {
                    store
                        .instantiated_property_recovery(property)
                        .and_then(|recovery| recovery.array_targets)
                });
                if store.type_payload(cached).is_none()
                    || !cached_instantiated_property_value_matches(
                        store,
                        property,
                        original,
                        mapper,
                        Some(cached),
                        validation_targets,
                    )
                {
                    return Err(invalid());
                }
            }
            (_, None) if store.instantiated_property_recovery(property).is_none() => {}
            _ => return Err(invalid()),
        }
    }
    Ok(Some(PropertyObjectAliasMembers {
        receiver,
        target: projection.target,
        members,
        properties: properties.to_vec(),
    }))
}

/// Direct parameters and scalar unions can reject a wrong result before its graph is read.
fn reject_mismatched_property_object_alias_values(
    store: &CanonicalTypeMapperStore,
    projection: &PropertyObjectAliasProjection,
) -> Result<(), RelationUnavailable> {
    if projection.type_ == projection.target {
        return Ok(());
    }
    let invalid = || RelationUnavailable::InvalidStructuredMembers(projection.type_);
    let record = store.type_payload(projection.type_).ok_or_else(invalid)?;
    if !record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        return Ok(());
    }
    let (_, properties) =
        property_object_alias_member_table(store, projection.type_, projection.properties.len())?;
    for (&property, source) in properties.iter().zip(&projection.properties) {
        let Some(original) = store
            .value_symbol_links(source.symbol)
            .and_then(|links| links.resolved_type)
        else {
            continue;
        };
        let Some(links) = store.value_symbol_links(property) else {
            continue;
        };
        let Some(cached) = links.resolved_type else {
            continue;
        };
        let expected = if let Some(index) = projection
            .parameters
            .iter()
            .position(|parameter| *parameter == original)
        {
            *projection.arguments.get(index).ok_or_else(invalid)?
        } else if let Some(expected) =
            cached_scalar_property_object_alias_union(store, projection, original)
        {
            expected
        } else {
            continue;
        };
        if cached != expected
            && !store
                .instantiated_property_recovery(property)
                .is_some_and(|recovery| recovery.matches_published_links(Some(links)))
        {
            return Err(invalid());
        }
    }
    Ok(())
}

/// Only scalar source and mapped leaves can use this recursive cache reader here.
fn cached_scalar_property_object_alias_union(
    store: &CanonicalTypeMapperStore,
    projection: &PropertyObjectAliasProjection,
    original: TypeId,
) -> Option<TypeId> {
    let record = store.type_payload(original)?;
    let TypeData::Union(union) = record.data() else {
        return None;
    };
    if record.alias().is_some() || union.origin.is_some() {
        return None;
    }
    for source in &union.union.types {
        let mapped = match projection
            .parameters
            .iter()
            .position(|parameter| parameter == source)
        {
            Some(index) => *projection.arguments.get(index)?,
            None => *source,
        };
        let record = store.type_payload(mapped)?;
        if record.alias().is_some()
            || !matches!(record.data(), TypeData::Intrinsic(_) | TypeData::Literal(_))
        {
            return None;
        }
    }
    cached_instantiation_with_vector(
        store,
        original,
        &projection.parameters,
        &projection.arguments,
        None,
        None,
    )
    .ok()
    .flatten()
}

/// Stops alias member edges from re-entering a fresh union validation walk.
/// This guard does not replace any source, mapper, or value-cache check.
#[allow(clippy::too_many_lines)] // Read raw edges once, then find complete cyclic components.
fn validate_property_object_alias_cache_cycles(
    store: &CanonicalTypeMapperStore,
    projection: &PropertyObjectAliasProjection,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), RelationUnavailable> {
    let receiver = projection.type_;
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let mut graph = HashMap::<TypeId, Vec<TypeId>>::new();
    let mut reverse = HashMap::<TypeId, Vec<TypeId>>::new();
    let mut aliases = HashSet::new();
    let mut pending = vec![receiver];
    while let Some(type_) = pending.pop() {
        if graph.contains_key(&type_) {
            continue;
        }
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        let mut children = Vec::new();
        let mut properties = Vec::new();
        let mut signatures = Vec::new();
        let mut indexes = Vec::new();
        let mut source_nodes = Vec::new();
        if let Some(alias) = record.alias() {
            let alias = store.type_alias(alias).ok_or_else(invalid)?;
            children.extend(alias.type_arguments().unwrap_or_default());
        }
        let is_array = cached_property_alias_array_identity(store, type_, array_targets);
        let argument_only = matches!(record.data(), TypeData::TypeReference(_))
            || matches!(record.data(), TypeData::Interface(interface)
                if record.object_flags().contains(ObjectFlags::REFERENCE)
                    && interface.all_type_parameters.as_deref().unwrap_or_default().iter()
                        .any(|parameter| Some(*parameter) != interface.this_type));
        // Ordinary references and the admitted Record mapped union follow arguments only.
        let mut member_sources = Vec::new();
        if !is_array && !argument_only && !matches!(record.data(), TypeData::Mapped(_)) {
            member_sources.push((type_, false));
            if let TypeData::Interface(interface) = record.data() {
                for &base in interface.resolved_base_types.as_deref().unwrap_or_default() {
                    member_sources.push((base, true));
                }
            }
        }
        let mut seen_member_sources = HashSet::new();
        while let Some((member_type, inherited)) = member_sources.pop() {
            if !seen_member_sources.insert((member_type, inherited))
                || cached_property_alias_array_identity(store, member_type, array_targets)
            {
                continue;
            }
            let member_record = store.type_payload(member_type).ok_or_else(invalid)?;
            let target = match member_record.data() {
                TypeData::Object(object) => object.target,
                TypeData::TypeReference(reference) => reference.object.target,
                TypeData::Interface(interface) => interface.reference.object.target,
                TypeData::Tuple(tuple) => tuple.interface.reference.object.target,
                _ => None,
            };
            if let Some(target) = target.filter(|target| *target != member_type) {
                children.push(target);
                if inherited {
                    member_sources.push((target, true));
                }
            }
            if inherited && let TypeData::Interface(interface) = member_record.data() {
                for &base in interface.resolved_base_types.as_deref().unwrap_or_default() {
                    children.push(base);
                    member_sources.push((base, true));
                }
                indexes.extend(
                    interface
                        .declared_index_infos
                        .as_deref()
                        .unwrap_or_default(),
                );
            }
            if let Some(structured) = member_record.data().structured() {
                properties.extend(structured.properties.as_deref().unwrap_or_default());
                signatures.extend(structured.signatures.as_deref().unwrap_or_default());
                indexes.extend(structured.index_infos.as_deref().unwrap_or_default());
            }
            if let Some(declarations) = member_record
                .symbol()
                .and_then(|symbol| store.symbol(symbol))
                .and_then(ts_binder::semantic::Symbol::declarations)
            {
                for &declaration in declarations {
                    if !matches!(
                        (member_record.data(), store.source_node_kind(declaration)),
                        (TypeData::Object(_), Some(SyntaxKind::TypeLiteral))
                            | (
                                TypeData::Interface(_) | TypeData::TypeReference(_),
                                Some(SyntaxKind::InterfaceDeclaration)
                            )
                    ) {
                        continue;
                    }
                    if matches!(member_record.data(), TypeData::Object(_))
                        && cached_property_alias_source_declaration(store, declaration)
                    {
                        aliases.insert(member_type);
                    }
                    for source in store
                        .source_direct_children(declaration)
                        .unwrap_or_default()
                    {
                        if !matches!(
                            store.source_node_kind(source),
                            Some(
                                SyntaxKind::PropertySignature
                                    | SyntaxKind::PropertyDeclaration
                                    | SyntaxKind::MethodSignature
                                    | SyntaxKind::CallSignature
                                    | SyntaxKind::ConstructSignature
                                    | SyntaxKind::IndexSignature
                                    | SyntaxKind::GetAccessor
                                    | SyntaxKind::SetAccessor
                            )
                        ) {
                            continue;
                        }
                        source_nodes.push(source);
                    }
                }
            }
        }
        if type_ == receiver {
            aliases.insert(type_);
            children.extend(&projection.arguments);
            properties.extend(projection.properties.iter().map(|property| property.symbol));
        } else if matches!(record.data(), TypeData::Object(_))
            && let Some(arguments) = cached_property_object_alias_physical_arguments(store, type_)
                .map_err(|_| invalid())?
        {
            children.extend(arguments);
        }
        match record.data() {
            TypeData::Union(union) => {
                children.extend(&union.union.types);
                children.extend(union.origin);
            }
            TypeData::TypeReference(reference) => {
                children.extend(
                    reference
                        .resolved_type_arguments
                        .as_deref()
                        .unwrap_or_default(),
                );
            }
            TypeData::Interface(interface) => {
                children.extend(
                    interface
                        .reference
                        .resolved_type_arguments
                        .as_deref()
                        .unwrap_or_default(),
                );
                if !is_array && !argument_only {
                    children.extend(interface.resolved_base_types.as_deref().unwrap_or_default());
                    indexes.extend(
                        interface
                            .declared_index_infos
                            .as_deref()
                            .unwrap_or_default(),
                    );
                }
            }
            TypeData::Tuple(tuple) => {
                children.extend(
                    tuple
                        .interface
                        .reference
                        .resolved_type_arguments
                        .as_deref()
                        .unwrap_or_default(),
                );
            }
            TypeData::TemplateLiteral(template) => children.extend(&template.types),
            TypeData::StringMapping(mapping) => children.push(mapping.target),
            TypeData::Index(index) => children.push(index.target),
            TypeData::IndexedAccess(access) => {
                children.extend([access.object_type, access.index_type]);
            }
            _ => {}
        }
        let mut seen_source_nodes = HashSet::new();
        while let Some(node) = source_nodes.pop() {
            if !seen_source_nodes.insert(node)
                || matches!(
                    store.source_node_kind(node),
                    Some(
                        SyntaxKind::Block
                            | SyntaxKind::FunctionExpression
                            | SyntaxKind::ArrowFunction
                            | SyntaxKind::ClassExpression
                    )
                )
            {
                continue;
            }
            children.extend(
                store
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type),
            );
            if let Some(symbol) = store.source_declaration_symbol(node) {
                properties.push(symbol);
                properties.extend(
                    store
                        .late_bound_links(symbol)
                        .and_then(|links| links.late_symbol),
                );
            }
            signatures.extend(
                store
                    .signature_links(node)
                    .and_then(|links| links.resolved_signature.signature()),
            );
            source_nodes.extend(store.source_direct_children(node).unwrap_or_default());
        }
        let mut seen_signatures = HashSet::new();
        while let Some(signature) = signatures.pop() {
            if !seen_signatures.insert(signature) {
                continue;
            }
            let signature = store.signature(signature).ok_or_else(invalid)?;
            children.extend(signature.resolved_return_type());
            children.extend(store.circular_return_annotation_type(signature.id()));
            children.extend(
                store
                    .inferred_source_return_cycle(signature.id())
                    .map(|cycle| cycle.body_type),
            );
            children.extend(signature.type_parameters());
            for parameter in signature.type_parameters() {
                if let Some(TypeData::TypeParameter(parameter)) = store
                    .type_payload(*parameter)
                    .map(super::type_records::TypeRecord::data)
                {
                    children.extend(parameter.constraint);
                    children.extend(parameter.resolved_default_type);
                }
            }
            if let Some(predicate) = signature.resolved_type_predicate() {
                children.extend(
                    store
                        .type_predicate(predicate)
                        .ok_or_else(invalid)?
                        .type_id(),
                );
            }
            properties.extend(signature.parameters());
            properties.extend(signature.this_parameter());
            signatures.extend(
                signature
                    .target()
                    .filter(|target| *target != signature.id()),
            );
        }
        let mut seen_properties = HashSet::new();
        while let Some(property) = properties.pop() {
            if !seen_properties.insert(property) {
                continue;
            }
            store.symbol(property).ok_or_else(invalid)?;
            if let Some(links) = store.value_symbol_links(property) {
                children.extend(links.resolved_type);
                properties.extend(links.target.filter(|target| *target != property));
            }
        }
        for index in indexes {
            let index = store.index_info(index).ok_or_else(invalid)?;
            children.extend([index.key_type(), index.value_type()]);
        }
        children.sort_unstable();
        children.dedup();
        for &child in &children {
            reverse.entry(child).or_default().push(type_);
        }
        pending.extend(&children);
        graph.insert(type_, children);
    }

    // Two iterative passes find complete components. Ignoring an ordinary
    // back edge during a single DFS can hide an alias in that same component.
    let mut visited = HashSet::new();
    let mut order = Vec::new();
    let mut pending = vec![(receiver, false)];
    while let Some((type_, leaving)) = pending.pop() {
        if leaving {
            order.push(type_);
        } else if visited.insert(type_) {
            pending.push((type_, true));
            pending.extend(graph[&type_].iter().rev().map(|&child| (child, false)));
        }
    }
    let mut assigned = HashSet::new();
    for type_ in order.into_iter().rev() {
        if !assigned.insert(type_) {
            continue;
        }
        let mut component = vec![type_];
        let mut pending = vec![type_];
        while let Some(type_) = pending.pop() {
            for &parent in reverse.get(&type_).into_iter().flatten() {
                if assigned.insert(parent) {
                    component.push(parent);
                    pending.push(parent);
                }
            }
        }
        let cyclic = component.len() > 1 || graph[&type_].contains(&type_);
        if cyclic && component.iter().any(|type_| aliases.contains(type_)) {
            return Err(RelationUnavailable::UnsupportedStructuredType(receiver));
        }
    }
    Ok(())
}

fn cached_property_alias_array_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let target = match record.data() {
        TypeData::TypeReference(reference) => reference.object.target,
        TypeData::Interface(interface)
            if record.object_flags().contains(ObjectFlags::INTERFACE) =>
        {
            interface.reference.object.target
        }
        _ => return false,
    };
    [Some(type_), target].into_iter().flatten().any(|type_| {
        array_targets.is_some_and(|targets| {
            type_ == targets.array_type() || type_ == targets.readonly_array_type()
        }) || store
            .type_payload(type_)
            .and_then(super::type_records::TypeRecord::symbol)
            .is_some_and(|symbol| store.symbol_is_registered_global_array(symbol))
    })
}

/// Recognizes the source family without validating or resolving its caches.
fn cached_property_alias_source_declaration(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> bool {
    if store.source_node_kind(declaration) != Some(SyntaxKind::TypeLiteral)
        || store
            .source_direct_children(declaration)
            .is_none_or(|children| {
                children.is_empty()
                    || children.iter().any(|child| {
                        !matches!(
                            store.source_node_kind(*child),
                            Some(SyntaxKind::PropertySignature | SyntaxKind::PropertyDeclaration)
                        ) || store
                            .source_child_with_kind(*child, SyntaxKind::ComputedPropertyName)
                            .is_some()
                    })
            })
    {
        return false;
    }
    let mut node = declaration;
    while let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) {
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType)
                if store.source_direct_children(parent).as_deref() == Some(&[node]) =>
            {
                node = parent;
            }
            Some(SyntaxKind::TypeAliasDeclaration) => {
                return store.source_direct_type_annotation(parent) == Some(node)
                    && store
                        .source_direct_children(parent)
                        .is_some_and(|children| {
                            children.iter().any(|child| {
                                store.source_node_kind(*child) == Some(SyntaxKind::TypeParameter)
                            })
                        });
            }
            _ => return false,
        }
    }
    false
}

fn validate_property_object_alias_source_members(
    store: &CanonicalTypeMapperStore,
    projection: &PropertyObjectAliasProjection,
) -> Result<(Option<SymbolTableId>, Vec<Option<TypeId>>), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(projection.target);
    let record = store.type_payload(projection.target).ok_or_else(invalid)?;
    let structured = record.data().structured().ok_or_else(invalid)?;
    let source_members = store
        .symbol(projection.source_symbol)
        .ok_or_else(invalid)?
        .members();
    let complete = record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED);
    if complete {
        let (members, properties) = property_object_alias_member_table(
            store,
            projection.target,
            projection.properties.len(),
        )?;
        if members != source_members
            || !properties
                .iter()
                .copied()
                .eq(projection.properties.iter().map(|property| property.symbol))
        {
            return Err(invalid());
        }
    } else if structured != &StructuredTypeData::default() {
        return Err(invalid());
    }
    let mut original_types = Vec::with_capacity(projection.properties.len());
    for (index, property) in projection.properties.iter().enumerate() {
        let type_ = match selected_property_object_alias_property(store, projection, index)? {
            SelectedDeclaredProperty::Resolved(property) => Some(property.type_),
            SelectedDeclaredProperty::Unresolved(symbol)
                if symbol == property.symbol && !complete =>
            {
                None
            }
            _ => return Err(invalid()),
        };
        original_types.push(type_);
    }
    Ok((source_members, original_types))
}

fn property_object_alias_member_table(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    count: usize,
) -> Result<(Option<SymbolTableId>, &[SemanticSymbolId]), RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let structured = store
        .type_payload(receiver)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    let properties = structured.properties.as_deref().unwrap_or_default();
    if properties.len() != count
        || structured.properties.is_some() == properties.is_empty()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured.index_infos.is_some()
        || structured.constrained != ConstrainedTypeData::default()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || match structured.members {
            Some(members) => store
                .symbol_table(members)
                .is_none_or(|table| table.len() != count),
            None => count != 0,
        }
    {
        return Err(invalid());
    }
    Ok((structured.members, properties))
}

/// Creates only member names and proxies. Original annotations remain lazy.
pub(super) fn resolve_property_object_alias_members(
    store: &mut CanonicalTypeMapperStore,
    receiver: TypeId,
) -> Result<PropertyObjectAliasMembers, RelationUnavailable> {
    if let Some(members) = validate_property_object_alias_members(store, receiver)? {
        return Ok(members);
    }
    let projection = property_object_alias_projection(store, receiver)?
        .ok_or(RelationUnavailable::UnsupportedStructuredType(receiver))?;
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let mapper = projection.mapper.ok_or_else(invalid)?;
    let (_, original_types) = validate_property_object_alias_source_members(store, &projection)?;
    let mut properties = Vec::with_capacity(projection.properties.len());
    let mut proxy_count = 0;
    for (source, original) in projection.properties.iter().zip(original_types) {
        if original.is_some_and(|original| {
            matches!(
                instantiable_member_type_contains_variables(
                    store,
                    original,
                    &projection.parameters,
                    None
                ),
                Ok(false)
            )
        }) {
            properties.push(ColdPropertyPlan::Reused {
                symbol: source.symbol,
                name: source.name.clone(),
            });
        } else {
            properties.push(
                prepare_cold_property_proxy(store, source.symbol, source.readonly)
                    .map_err(|error| property_object_alias_member_error(receiver, &error))?,
            );
            proxy_count += 1;
        }
    }
    let count = properties.len();
    let table = if count == 0 {
        None
    } else {
        Some(
            prepare_member_table(receiver, count)
                .map_err(|error| property_object_alias_member_error(receiver, &error))?,
        )
    };
    if !store.try_reserve_checker_symbol_allocations(proxy_count, usize::from(count != 0))
        || !store.try_reserve_value_symbol_links(proxy_count)
    {
        return Err(RelationUnavailable::UnionValidationCapacity(receiver));
    }
    let (members, properties) =
        publish_prepared_property_table(store, ColdMembersPlan { table, properties }, Some(mapper));
    assert!(store.set_structured_type_members(
        receiver,
        members,
        (!properties.is_empty()).then(|| properties.clone()),
        None,
        None,
        None,
    ));
    Ok(PropertyObjectAliasMembers {
        receiver,
        target: projection.target,
        members,
        properties,
    })
}

/// Resolves one original annotation, then maps only that property's value.
#[allow(clippy::too_many_arguments)] // The source owner supplies the query session and diagnostics.
#[allow(clippy::too_many_lines)] // Keep cold resolution, caller-session mapping, and publication together.
pub(super) fn demand_property_object_alias_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    receiver: TypeId,
    property: SemanticSymbolId,
) -> Result<TypeId, SourceCheckError> {
    let array_targets = Some(CanonicalArrayTargets::from_global_types(global_types));
    let members =
        validate_property_object_alias_members_with_array_targets(store, receiver, array_targets)?
            .ok_or(RelationUnavailable::UnresolvedStructuredMembers(receiver))?;
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let index = members
        .properties
        .iter()
        .position(|symbol| *symbol == property)
        .ok_or_else(invalid)?;
    let projection = property_object_alias_projection(store, receiver)?.ok_or_else(invalid)?;
    let source = projection
        .properties
        .get(index)
        .ok_or_else(invalid)?
        .clone();
    if let Some(type_) = store
        .value_symbol_links(property)
        .and_then(|links| links.resolved_type)
    {
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
        )?
        .preflight_type_of_declared_value(source.symbol)?;
        return Ok(type_);
    }
    if session.recovery_error_type().is_some_and(|error_type| {
        store
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| bootstrap.error_type != error_type)
            || store.validate_union_constituent(error_type).is_err()
    }) {
        return Err(invalid().into());
    }
    let template = match selected_property_object_alias_property(store, &projection, index)? {
        SelectedDeclaredProperty::Resolved(property) => {
            CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
            )?
            .preflight_type_of_declared_value(source.symbol)?;
            property.type_
        }
        SelectedDeclaredProperty::Unresolved(symbol) if symbol == source.symbol => {
            CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
            )?
            .get_type_of_declared_value(source.symbol)?
        }
        _ => return Err(invalid().into()),
    };
    reject_mismatched_property_object_alias_values(store, &projection)?;
    validate_property_object_alias_cache_cycles(store, &projection, array_targets)?;
    if !matches!(
        selected_property_object_alias_property(store, &projection, index)?,
        SelectedDeclaredProperty::Resolved(property) if property.type_ == template
    ) {
        return Err(invalid().into());
    }
    if projection.type_ == projection.target {
        return Ok(template);
    }
    let mapper = projection.mapper.ok_or_else(invalid)?;
    let limit_mark = session.limit_event_mark();
    let instantiated =
        instantiate_generic_member_type(store, template, mapper, array_targets, session)
            .map_err(|error| property_object_alias_member_error(receiver, &error))?;
    let links = store
        .value_symbol_links(property)
        .cloned()
        .ok_or_else(invalid)?;
    if links
        != (ValueSymbolLinks {
            target: Some(source.symbol),
            mapper: Some(mapper),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invalid().into());
    }
    let recovery = if session.recovery_error_type().is_some()
        && session.limit_event_occurred_since(limit_mark)
    {
        let identity =
            property_recovery_type_identity(store, &[template, instantiated], array_targets)
                .ok_or_else(invalid)?;
        if !store.try_reserve_instantiated_property_recoveries() {
            return Err(RelationUnavailable::UnionValidationCapacity(receiver).into());
        }
        Some(InstantiatedPropertyRecovery {
            valid: true,
            method: false,
            symbol: property,
            target: source.symbol,
            template,
            mapper,
            result: instantiated,
            array_targets,
            identity,
        })
    } else {
        if !cached_instantiated_property_type_matches(
            store,
            template,
            instantiated,
            mapper,
            array_targets,
        ) {
            return Err(invalid().into());
        }
        None
    };
    assert!(store.set_value_symbol_links(
        property,
        ValueSymbolLinks {
            resolved_type: Some(instantiated),
            ..links
        }
    ));
    if let Some(recovery) = recovery {
        assert!(store.publish_instantiated_property_recovery(recovery));
    }
    Ok(instantiated)
}

fn property_object_alias_member_error(
    receiver: TypeId,
    error: &GenericInterfaceMemberError,
) -> RelationUnavailable {
    match error {
        GenericInterfaceMemberError::UnsupportedTarget(type_)
        | GenericInterfaceMemberError::UnsupportedPropertyType(type_) => {
            RelationUnavailable::UnsupportedStructuredType(*type_)
        }
        GenericInterfaceMemberError::UnsupportedMember(symbol) => {
            RelationUnavailable::UnsupportedProperty(*symbol)
        }
        GenericInterfaceMemberError::Capacity(type_) => {
            RelationUnavailable::UnionValidationCapacity(*type_)
        }
        GenericInterfaceMemberError::Reference(_)
        | GenericInterfaceMemberError::InvalidTarget(_)
        | GenericInterfaceMemberError::InvalidMember(_)
        | GenericInterfaceMemberError::InvalidCachedMembers(_)
        | GenericInterfaceMemberError::InvalidCachedProperty(_) => {
            RelationUnavailable::InvalidStructuredMembers(receiver)
        }
    }
}

pub(super) fn resolve_members_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_members_with_array_targets_and_session(store, reference, array_targets, &mut session)
}

/// Resolves inherited tables and index values within the caller's query budget.
/// Property proxies remain lazy until their values are demanded.
pub(super) fn resolve_members_with_array_targets_and_session(
    store: &mut CanonicalTypeMapperStore,
    reference: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
    let mut shape = validate_shape(store, reference, array_targets)?;
    if let Some(cached) = validate_warm_members(store, &shape, array_targets)? {
        return Ok(cached);
    }
    if session.recovery_error_type().is_some_and(|error_type| {
        store
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| bootstrap.error_type != error_type)
            || store.validate_union_constituent(error_type).is_err()
    }) {
        return Err(GenericInterfaceMemberError::InvalidCachedMembers(reference));
    }
    // Go substitutes own indexes before it resolves inherited members.
    let indexes = prepare_cold_index_values(store, &shape, array_targets, session)?;
    if !shape.inherited_members_ready {
        materialize_inherited_members(store, &shape, array_targets, session)?;
        shape = validate_shape(store, reference, array_targets)?;
        if !shape.inherited_members_ready {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(reference));
        }
    }
    let plan = prepare_cold_members(store, &shape)?;
    publish_cold_members(store, &shape, plan, indexes, array_targets)
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
    name: EscapedNameRef<'_>,
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
    name: EscapedNameRef<'_>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<Option<InstantiatedInterfaceProperty>, GenericInterfaceMemberError> {
    let members =
        resolve_members_with_array_targets_and_session(store, reference, array_targets, session)?;
    let Some(table) = members.members else {
        return Ok(None);
    };
    let table = store
        .symbol_table(table)
        .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(reference))?;
    let Some(symbol) = table.get(name) else {
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
    let method = store
        .symbol(target)
        .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD));
    if method
        && !matches!(
            super::callable_sets::validate_stored_declared_method_callable_set(store, template),
            Some(StoredCallableSetValidation::Valid { .. })
        )
    {
        return Err(GenericInterfaceMemberError::InvalidMember(target));
    }
    if let Some(cached) = cached {
        if !cached_instantiated_property_value_matches(
            store,
            symbol,
            template,
            mapper,
            Some(cached),
            array_targets,
        ) {
            return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
        }
        return Ok(cached);
    }
    if session.recovery_error_type().is_some_and(|error_type| {
        store
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| bootstrap.error_type != error_type)
            || store.validate_union_constituent(error_type).is_err()
    }) {
        return Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol));
    }
    let limit_mark = session.limit_event_mark();
    let instantiated = if method {
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
    let recovery = if session.recovery_error_type().is_some()
        && session.limit_event_occurred_since(limit_mark)
    {
        let identity =
            property_recovery_type_identity(store, &[template, instantiated], array_targets)
                .ok_or(GenericInterfaceMemberError::InvalidCachedProperty(symbol))?;
        if !store.try_reserve_instantiated_property_recoveries() {
            return Err(GenericInterfaceMemberError::Capacity(template));
        }
        Some(InstantiatedPropertyRecovery {
            valid: true,
            method,
            symbol,
            target,
            template,
            mapper,
            result: instantiated,
            array_targets,
            identity,
        })
    } else {
        None
    };
    assert!(store.set_value_symbol_links(
        symbol,
        ValueSymbolLinks {
            resolved_type: Some(instantiated),
            ..links
        },
    ));
    if let Some(recovery) = recovery {
        assert!(store.publish_instantiated_property_recovery(recovery));
    }
    Ok(instantiated)
}

/// Finds type variables in every published method parameter and return type.
pub(super) fn published_method_requires_instantiation(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    method: SemanticSymbolId,
) -> Result<bool, GenericInterfaceMemberError> {
    let (owner, target) = store
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
    let (source, _, _) = published_interface_method_value(store, owner, method)?;
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
            requires |= member_type_requires_instantiation_worker(
                store,
                type_?,
                &parameters,
                Some(CanonicalArrayTargets::from_global_types(global_types)),
                &mut HashSet::new(),
                true,
            )?;
        }
    }
    Ok(requires)
}

/// Instantiates one published generic interface method for its direct receiver.
///
/// Shared declaration signatures and annotation caches remain generic. The
/// returned value retains optional wrappers around the mapped callable.
pub(super) fn instantiate_published_generic_interface_method(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
    method: SemanticSymbolId,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    instantiate_published_generic_interface_method_with_session(
        store,
        global_types,
        receiver,
        method,
        &mut session,
    )
}

/// Keeps selected method instantiation inside the caller's source query limits.
pub(super) fn instantiate_published_generic_interface_method_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
    method: SemanticSymbolId,
    session: &mut InstantiationSession,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let targets = CanonicalArrayTargets::from_global_types(global_types);
    let plan = plan_published_interface_method(store, Some(targets), receiver, method)?;
    if let Some(cached) = cached_published_interface_method(store, &plan, targets)? {
        return mapped_interface_method_value(store, global_types, &plan, cached);
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
    let mut signatures = Vec::with_capacity(plan.signatures.len());
    for source in &plan.signatures {
        let signature = instantiate_generic_method_signature(
            store,
            source.source,
            &source.parameter_types,
            source.return_type,
            mapper,
            Some(targets),
            session,
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
    mapped_interface_method_value(store, global_types, &plan, callable)
}

fn mapped_interface_method_value(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &PublishedInterfaceMethodPlan,
    callable: TypeId,
) -> Result<TypeId, GenericInterfaceMemberError> {
    let Some(sentinel) = plan.optional_sentinel else {
        return Ok(callable);
    };
    store
        .expression_union_type_with_global_types(
            global_types,
            &[callable, sentinel],
            super::bootstrap::UnionReduction::Literal,
        )
        .map_err(|_| GenericInterfaceMemberError::InvalidCachedMembers(plan.receiver))
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
    targets: Option<CanonicalArrayTargets>,
    receiver: TypeId,
    method: SemanticSymbolId,
) -> Result<PublishedInterfaceMethodPlan, GenericInterfaceMemberError> {
    let method_record = store
        .symbol(method)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    if method_record
        .check_flags()
        .intersects(CheckFlags::INSTANTIATED | CheckFlags::MAPPED)
        || method_record
            .parent()
            .and_then(|owner| store.get_merged_symbol(owner))
            .and_then(|owner| store.symbol(owner))
            .is_some_and(|owner| !owner.flags().contains(SymbolFlags::INTERFACE))
    {
        return Err(GenericInterfaceMemberError::UnsupportedMember(method));
    }
    let (owner, target) = store
        .authenticated_interface_method_owner(method)
        .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
    let receiver_record = store
        .type_payload(receiver)
        .ok_or(GenericInterfaceMemberError::InvalidTarget(receiver))?;
    if !matches!(
        receiver_record.data(),
        TypeData::Interface(_) | TypeData::TypeReference(_)
    ) || receiver_record
        .object_flags()
        .intersects(ObjectFlags::CLASS | ObjectFlags::MAPPED | ObjectFlags::TUPLE)
    {
        return Err(GenericInterfaceMemberError::UnsupportedTarget(receiver));
    }
    let receiver = if let Some(targets) = targets
        && (target == targets.array_type() || target == targets.readonly_array_type())
    {
        store
            .canonical_array_reference_with_targets(targets, receiver)
            .map_err(|_| GenericInterfaceMemberError::InvalidTarget(receiver))?
            .ok_or(GenericInterfaceMemberError::InvalidTarget(receiver))?
            .base_type
    } else {
        receiver
    };
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
    {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
    let (source, value, optional_sentinel) =
        published_interface_method_value(store, owner, method)?;
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
    let declarations = method_record
        .declarations()
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
        || signatures.len() != declarations.len()
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
    for (&signature, &declaration) in signatures.iter().zip(declarations) {
        if store.interface_method_linked_type(signature) != Some(value)
            || store.signature_has_circular_return_type(signature)
        {
            return Err(GenericInterfaceMemberError::InvalidMember(method));
        }
        let record = store
            .signature(signature)
            .ok_or(GenericInterfaceMemberError::InvalidMember(method))?;
        if record.declaration() != Some(declaration)
            || !super::callable_sets::valid_declared_method_type_parameters(
                store,
                record,
                declaration,
            )
        {
            return Err(GenericInterfaceMemberError::InvalidMember(method));
        }
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
        for &parameter in record.type_parameters() {
            let Some(TypeData::TypeParameter(parameter)) =
                store.type_payload(parameter).map(super::TypeRecord::data)
            else {
                return Err(GenericInterfaceMemberError::InvalidMember(method));
            };
            for type_ in [parameter.constraint, parameter.resolved_default_type]
                .into_iter()
                .flatten()
            {
                member_type_requires_instantiation(store, type_, &signature_parameters, targets)?;
            }
        }
        for type_ in parameter_types.iter().copied().chain([return_type]) {
            member_type_requires_instantiation(store, type_, &signature_parameters, targets)?;
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
        optional_sentinel,
        target,
        receiver,
        mapper_sources,
        mapper_targets,
        signatures: planned,
    })
}

/// Authenticates the selected source before a mapped callable enters a type graph.
pub(super) fn published_interface_method_source_matches(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    method: SemanticSymbolId,
    source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    plan_published_interface_method(store, array_targets, receiver, method)
        .is_ok_and(|plan| plan.source == source)
}

/// Reads the callable without discarding its declared optional value or key.
fn published_interface_method_value(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    method: SemanticSymbolId,
) -> Result<(TypeId, TypeId, Option<TypeId>), GenericInterfaceMemberError> {
    let invalid = || GenericInterfaceMemberError::InvalidMember(method);
    let record = store.symbol(method).ok_or_else(invalid)?;
    let links = store.value_symbol_links(method).ok_or_else(invalid)?;
    let value = links.resolved_type.ok_or_else(invalid)?;
    if record.check_flags().contains(CheckFlags::LATE) {
        let resolved_table = store
            .members_and_exports_links(owner)
            .and_then(|links| links.table(MembersOrExportsResolutionKind::ResolvedMembers))
            .and_then(|members| store.symbol_table(members));
        if !valid_late_bound_unique_symbol_member(
            store,
            owner,
            method,
            record.declarations().ok_or_else(invalid)?,
            links,
            resolved_table,
        ) {
            return Err(invalid());
        }
    } else if links
        != &(ValueSymbolLinks {
            resolved_type: Some(value),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invalid());
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let optional = store
        .declared_method_optional_flag(method)
        .ok_or_else(invalid)?;
    if !optional || !bootstrap.options.strict_null_checks {
        return Ok((value, value, None));
    }
    let sentinel = bootstrap.undefined_or_missing_type;
    let TypeData::Union(union) = store.type_payload(value).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let [first, second] = union.union.types.as_slice() else {
        return Err(invalid());
    };
    let callable = match (*first == sentinel, *second == sentinel) {
        (true, false) => *second,
        (false, true) => *first,
        _ => return Err(invalid()),
    };
    let mut expected = [callable, sentinel];
    expected.sort_unstable();
    store
        .validate_canonical_union_metadata(value, &expected)
        .map_err(|_| invalid())?;
    store
        .validate_union_constituent(sentinel)
        .map_err(|_| invalid())?;
    Ok((callable, value, Some(sentinel)))
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
        let invalid = || GenericInterfaceMemberError::InvalidCachedMembers(plan.receiver);
        let cached_receiver = store
            .map_type(mapper, *plan.mapper_sources.last().ok_or_else(invalid)?)
            .ok_or_else(invalid)?;
        let reference =
            validate_direct_generic_reference(store, cached_receiver).map_err(|_| invalid())?;
        let cached_targets = reference
            .type_arguments
            .iter()
            .copied()
            .chain(std::iter::once(cached_receiver))
            .collect::<Vec<_>>();
        if reference.target != plan.target
            || store.type_mapper_has_exact_endpoints(mapper, &plan.mapper_sources, &cached_targets)
                != Some(true)
        {
            return Err(invalid());
        }
        if cached_receiver != plan.receiver {
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
        || instantiated.resolved_min_argument_count() != -1
        || instantiated.resolved_type_predicate().is_some()
        || instantiated.target() != Some(source.source)
        || instantiated.mapper() != Some(signature_mapper)
        || instantiated.isolated_signature_type().is_some()
        || instantiated.composite().is_some()
        || store.signature_has_circular_return_type(signature)
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
            let symbol = store.symbol(parameter).ok_or(
                GenericInterfaceMemberError::InvalidCachedProperty(parameter),
            )?;
            let original_symbol = store
                .symbol(original_parameter)
                .ok_or(GenericInterfaceMemberError::InvalidMember(plan.method))?;
            let expected_checks = CheckFlags::INSTANTIATED
                | (original_symbol.check_flags()
                    & (CheckFlags::READONLY
                        | CheckFlags::LATE
                        | CheckFlags::OPTIONAL_PARAMETER
                        | CheckFlags::REST_PARAMETER));
            symbol.flags() == original_symbol.flags() | SymbolFlags::TRANSIENT
                && symbol.check_flags() == expected_checks
                && symbol.name() == original_symbol.name()
                && symbol.declarations() == original_symbol.declarations()
                && symbol.value_declaration() == original_symbol.value_declaration()
                && symbol.parent() == original_symbol.parent()
                && symbol.members().is_none()
                && symbol.exports().is_none()
                && symbol.export_symbol().is_none()
                && store.get_merged_symbol(parameter) == Some(parameter)
                && links
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

pub(super) fn property_instantiation_error(
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
    if store.mapper_payload(mapper).is_none() {
        return Err(GenericInterfaceMemberError::UnsupportedPropertyType(
            template,
        ));
    }
    instantiate_generic_member_type_worker(
        store,
        template,
        mapper,
        array_targets,
        session,
        &mut HashSet::new(),
    )
}

fn instantiate_generic_member_type_worker(
    store: &mut CanonicalTypeMapperStore,
    template: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
    active: &mut HashSet<TypeId>,
) -> Result<TypeId, GenericInterfaceMemberError> {
    if active.len() >= InstantiationLimits::default().max_depth {
        return Err(GenericInterfaceMemberError::Capacity(template));
    }
    if !active.insert(template) {
        return Err(GenericInterfaceMemberError::UnsupportedPropertyType(
            template,
        ));
    }
    let result = instantiate_generic_member_type_inner(
        store,
        template,
        mapper,
        array_targets,
        session,
        active,
    );
    active.remove(&template);
    result
}

fn instantiate_generic_member_type_inner(
    store: &mut CanonicalTypeMapperStore,
    template: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
    active: &mut HashSet<TypeId>,
) -> Result<TypeId, GenericInterfaceMemberError> {
    if let Some(tuple) = store
        .canonical_tuple_shape(template)
        .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(template))?
    {
        if tuple.combined_flags().intersects(ElementFlags::VARIABLE) {
            return Err(GenericInterfaceMemberError::UnsupportedPropertyType(
                template,
            ));
        }
        let elements = tuple.element_types().to_vec();
        let infos = tuple.element_infos().to_vec();
        let readonly = tuple.is_readonly();
        let instantiated_elements = elements
            .iter()
            .map(|element| {
                instantiate_generic_member_type_worker(
                    store,
                    *element,
                    mapper,
                    array_targets,
                    session,
                    active,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if instantiated_elements == elements {
            return Ok(template);
        }
        return store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &instantiated_elements,
                &infos,
                readonly,
            ))
            .map_err(|error| match error {
                TupleTypeError::Capacity => GenericInterfaceMemberError::Capacity(template),
                _ => GenericInterfaceMemberError::UnsupportedPropertyType(template),
            });
    }
    if let Some(constituents) = method_tuple_union_members(store, template)? {
        let constituents = constituents.to_vec();
        let instantiated_constituents = constituents
            .iter()
            .map(|constituent| {
                instantiate_generic_member_type_worker(
                    store,
                    *constituent,
                    mapper,
                    array_targets,
                    session,
                    active,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if instantiated_constituents == constituents {
            return Ok(template);
        }
        return store
            .literal_union_type_with_alias_and_array_targets(
                &instantiated_constituents,
                None,
                array_targets,
            )
            .map_err(|error| match error {
                super::bootstrap::LiteralTypeCacheError::Capacity => {
                    GenericInterfaceMemberError::Capacity(template)
                }
                _ => GenericInterfaceMemberError::UnsupportedPropertyType(template),
            });
    }
    if store.type_has_function_type_provenance(template) {
        return instantiate_function_member_type(store, template, mapper, array_targets, session);
    }
    if let Some((callback, undefined)) = optional_function_member(store, template)? {
        let instantiated_callback = instantiate_generic_member_type_worker(
            store,
            callback,
            mapper,
            array_targets,
            session,
            active,
        )?;
        if instantiated_callback == callback {
            return Ok(template);
        }
        return store
            .literal_union_type_with_alias_and_array_targets(
                &[instantiated_callback, undefined],
                None,
                array_targets,
            )
            .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(template));
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
        resolve_members_with_array_targets_and_session(store, object, array_targets, session)?;
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
            .resolve_mapped_symbol_type_with_session(symbol, session)
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

/// Tuple unions retain their canonical arms. Alias and mixed-union mapping stay separate.
fn method_tuple_union_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<&[TypeId]>, GenericInterfaceMemberError> {
    let invalid = || GenericInterfaceMemberError::UnsupportedPropertyType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Union(union) = record.data() else {
        return Ok(None);
    };
    let mut tuple_count = 0;
    for constituent in &union.union.types {
        tuple_count += usize::from(
            store
                .canonical_tuple_shape(*constituent)
                .map_err(|_| invalid())?
                .is_some(),
        );
    }
    if tuple_count == 0 {
        return Ok(None);
    }
    if tuple_count != union.union.types.len() || record.alias().is_some() || union.origin.is_some()
    {
        return Err(invalid());
    }
    store
        .validate_canonical_union_metadata(type_, &union.union.types)
        .map_err(|_| invalid())?;
    Ok(Some(&union.union.types))
}

fn optional_function_member(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<(TypeId, TypeId)>, GenericInterfaceMemberError> {
    let invalid = || GenericInterfaceMemberError::UnsupportedPropertyType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Union(union) = record.data() else {
        return Ok(None);
    };
    let [first, second] = union.union.types.as_slice() else {
        return Ok(None);
    };
    let undefined = store
        .intrinsic_bootstrap()
        .ok_or_else(invalid)?
        .undefined_type;
    let callback = if *first == undefined {
        *second
    } else if *second == undefined {
        *first
    } else {
        return Ok(None);
    };
    let callback_source = store.type_has_function_type_provenance(callback)
        || matches!(store.type_payload(callback).map(super::TypeRecord::data),
        Some(TypeData::Object(object)) if object.target.is_some_and(|source| {
            store.type_has_function_type_provenance(source)
        }));
    if !callback_source {
        return Ok(None);
    }
    if record.alias().is_some()
        || union.origin.is_some()
        || store
            .validate_canonical_union_metadata(type_, &union.union.types)
            .is_err()
    {
        return Err(invalid());
    }
    Ok(Some((callback, undefined)))
}

fn method_parameter_contains_function(
    store: &CanonicalTypeMapperStore,
    parameter: TypeId,
    callback: TypeId,
) -> bool {
    parameter == callback
        || optional_function_member(store, parameter)
            .is_ok_and(|optional| optional.is_some_and(|(source, _)| source == callback))
}

pub(super) fn instantiated_optional_function_member_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<bool> {
    let (source, undefined) = match optional_function_member(store, template) {
        Ok(Some(optional)) => optional,
        Ok(None) => return None,
        Err(_) => return Some(false),
    };
    Some(
        optional_function_member(store, actual).is_ok_and(|optional| {
            optional.is_some_and(|(mapped, sentinel)| {
                sentinel == undefined
                    && instantiated_function_member_type_matches(
                        store,
                        source,
                        mapped,
                        mapper,
                        array_targets,
                    )
            })
        }),
    )
}

/// Validates fixed tuple templates through the method's original mapper.
pub(super) fn instantiated_tuple_member_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<bool> {
    if store.mapper_payload(mapper).is_none() {
        return Some(false);
    }
    instantiated_tuple_member_type_matches_worker(
        store,
        template,
        actual,
        mapper,
        array_targets,
        &mut HashSet::new(),
    )
}

fn instantiated_tuple_member_type_matches_worker(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    actual: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<(TypeId, TypeId)>,
) -> Option<bool> {
    let Ok(tuple) = store.canonical_tuple_shape(template) else {
        return Some(false);
    };
    let union = if tuple.is_none() {
        match method_tuple_union_members(store, template) {
            Ok(Some(union)) => Some(union),
            Ok(None) => return None,
            Err(_) => return Some(false),
        }
    } else {
        None
    };
    if active.len() >= InstantiationLimits::default().max_depth
        || !active.insert((template, actual))
    {
        return Some(false);
    }
    let mut child_matches = |template, actual| {
        instantiated_tuple_member_type_matches_worker(
            store,
            template,
            actual,
            mapper,
            array_targets,
            active,
        )
        .unwrap_or_else(|| {
            instantiated_method_type_matches(store, template, actual, mapper, array_targets)
        })
    };
    let result = if let Some(tuple) = tuple {
        store
            .canonical_tuple_shape(actual)
            .ok()
            .flatten()
            .is_some_and(|mapped| {
                !tuple.combined_flags().intersects(ElementFlags::VARIABLE)
                    && tuple.target() == mapped.target()
                    && tuple.element_infos() == mapped.element_infos()
                    && tuple.is_readonly() == mapped.is_readonly()
                    && tuple.element_types().len() == mapped.element_types().len()
                    && tuple
                        .element_types()
                        .iter()
                        .zip(mapped.element_types())
                        .all(|(template, actual)| child_matches(*template, *actual))
            })
    } else {
        let actual_members = match method_tuple_union_members(store, actual) {
            Ok(Some(members)) => Some(members),
            Ok(None) if store.canonical_tuple_shape(actual).ok().flatten().is_some() => {
                Some(std::slice::from_ref(&actual))
            }
            _ => None,
        };
        union.zip(actual_members).is_some_and(|(source, mapped)| {
            source.iter().all(|template| {
                mapped
                    .iter()
                    .any(|actual| child_matches(*template, *actual))
            }) && mapped.iter().all(|actual| {
                source
                    .iter()
                    .any(|template| child_matches(*template, *actual))
            })
        })
    };
    active.remove(&(template, actual));
    Some(result)
}

fn function_member_signature(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
) -> Option<(SemanticSymbolId, PublishedInterfaceMethodSignature)> {
    let (symbol, signature, parameter_types) = function_member_parameters(store, source)?;
    Some((
        symbol,
        PublishedInterfaceMethodSignature {
            source: signature,
            parameter_types,
            return_type: store.signature(signature)?.resolved_return_type()?,
        },
    ))
}

fn function_member_parameters(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
) -> Option<(SemanticSymbolId, SignatureId, Vec<TypeId>)> {
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
    Some((record.symbol()?, *signature, parameter_types.to_vec()))
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
                                method_parameter_contains_function(store, type_, source)
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
        let instantiated_type = narrowed
            .map(|type_| {
                instantiate_generic_member_type(store, type_, mapper, array_targets, session)
            })
            .transpose()?;
        let predicate = store
            .alloc_type_predicate(kind, index, name, instantiated_type)
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
    let method = function_member_declaring_method(store, source)?;
    let (_, owner_type) = store.authenticated_interface_method_owner(method)?;
    let method_source = store.value_symbol_links(method)?.resolved_type?;
    let TypeData::Interface(interface) = store.type_payload(owner_type)?.data() else {
        return None;
    };
    let this_type = interface.this_type?;
    let targets = CanonicalArrayTargets::for_single_target_validation(owner_type);
    let published = store.types().find_map(|(method_type, record)| {
        let TypeData::Object(object) = record.data() else {
            return None;
        };
        if record.symbol() != Some(method) || object.target != Some(method_source) {
            return None;
        }
        let receiver = store.map_type(object.mapper?, this_type)?;
        let plan = plan_published_interface_method(store, Some(targets), receiver, method).ok()?;
        if cached_published_interface_method(store, &plan, targets).ok()? != Some(method_type) {
            return None;
        }
        object
            .structured
            .signatures
            .as_deref()?
            .iter()
            .zip(&plan.signatures)
            .any(|(&signature, original)| {
                original
                    .parameter_types
                    .iter()
                    .any(|parameter| method_parameter_contains_function(store, *parameter, source))
                    && store
                        .signature(signature)
                        .is_some_and(|signature| signature.mapper() == Some(mapper))
            })
            .then_some(targets)
    });
    if published.is_some() {
        return published;
    }
    if store.types().any(|(_, record)| {
        matches!(record.data(), TypeData::Object(object)
            if record.symbol() == Some(method)
                && object.target == Some(method_source)
                && object.mapper == Some(mapper))
    }) {
        return None;
    }

    // An optional callback union is built before its enclosing method value.
    // At that point the source callback and exact owner mapper prove its origin.
    let declaration = store
        .type_payload(source)?
        .symbol()
        .and_then(|symbol| store.symbol(symbol))?
        .declarations()?
        .first()
        .copied()?;
    let SourceNodeParent::Parent(parameter) = store.source_node_parent(declaration)? else {
        return None;
    };
    let SourceNodeParent::Parent(method_declaration) = store.source_node_parent(parameter)? else {
        return None;
    };
    store.source_child_with_kind(parameter, SyntaxKind::QuestionToken)?;
    let signature = store
        .signature_links(method_declaration)?
        .resolved_signature
        .signature()?;
    if !store.signature(signature)?.type_parameters().is_empty() {
        return None;
    }
    let receiver = store.map_type(mapper, this_type)?;
    let reference = validate_direct_generic_reference(store, receiver).ok()?;
    let parameters = interface.reference.resolved_type_arguments.as_deref()?;
    if reference.target != owner_type || reference.type_arguments.len() != parameters.len() {
        return None;
    }
    let sources = parameters
        .iter()
        .copied()
        .chain([this_type])
        .collect::<Vec<_>>();
    let destinations = reference
        .type_arguments
        .iter()
        .copied()
        .chain([receiver])
        .collect::<Vec<_>>();
    (store.type_mapper_has_exact_endpoints(mapper, &sources, &destinations) == Some(true))
        .then_some(targets)
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
            signature: callable.signature,
            parameters: source_display
                .parameters
                .into_iter()
                .zip(&callable.parameters)
                .map(
                    |(source, &value_type)| ValidatedSingleCallParameterDisplay {
                        name: source.name,
                        value_type,
                        annotation_type: None,
                        optional: source.optional,
                        rest: source.rest,
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
    session: &mut InstantiationSession,
) -> Result<(), GenericInterfaceMemberError> {
    let sources = mapper_parameters_for_target(store, shape.target, &shape.source_parameters)?;
    let targets = shape
        .target_arguments
        .iter()
        .copied()
        .chain(std::iter::once(shape.reference))
        .collect::<Vec<_>>();
    for base in &shape.base_types {
        let limit_mark = session.limit_event_mark();
        let resolved = instantiate_type_with_vector_and_session(
            store,
            *base,
            &sources,
            &targets,
            array_targets,
            session,
        )
        .map_err(|error| property_instantiation_error(*base, &error))?;
        if session.limit_event_occurred_since(limit_mark) {
            // Recovered base arguments need their own proof before heritage can reuse them.
            return Err(GenericInterfaceMemberError::UnsupportedTarget(
                shape.reference,
            ));
        }
        if validate_direct_generic_reference(store, resolved).is_ok() {
            resolve_members_with_array_targets_and_session(
                store,
                resolved,
                array_targets,
                session,
            )?;
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
    // Check produced recovery graphs before an invalid nested reference can
    // make the declared member domain appear merely unsupported.
    for index in store
        .type_payload(reference)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.index_infos.as_deref())
        .unwrap_or_default()
    {
        if let Some(recovery) = store.instantiated_index_recovery(*index)
            && recovery.shape.reference == reference
            && !recovery.matches_cached_identity(store, recovery.array_targets)
        {
            return Err(GenericInterfaceMemberError::InvalidCachedMembers(reference));
        }
    }
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
                    // Signature mapping reads reference identities, not their member tables.
                    property.requires_proxy |= member_type_requires_instantiation(
                        store,
                        type_,
                        &signature_parameters,
                        array_targets,
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
        false,
    )
}

fn member_type_requires_instantiation_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
    classify_only: bool,
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
        classify_only,
    );
    active.remove(&type_);
    result
}

#[allow(clippy::too_many_lines)] // Keep fixed tuple reuse and callback parameter checks in one walk.
fn member_type_requires_instantiation_inner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    mapper_parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
    classify_only: bool,
) -> Result<bool, GenericInterfaceMemberError> {
    if let Some(tuple) = store
        .canonical_tuple_shape(type_)
        .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(type_))?
    {
        if !classify_only && tuple.combined_flags().intersects(ElementFlags::VARIABLE) {
            return Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_));
        }
        if active.len() >= InstantiationLimits::default().max_depth {
            return Err(GenericInterfaceMemberError::Capacity(type_));
        }
        let mut requires = false;
        for &element in tuple.element_types() {
            requires |= member_type_requires_instantiation_worker(
                store,
                element,
                mapper_parameters,
                array_targets,
                active,
                classify_only,
            )?;
        }
        return Ok(requires);
    }
    if let Some(constituents) = method_tuple_union_members(store, type_)? {
        if active.len() >= InstantiationLimits::default().max_depth {
            return Err(GenericInterfaceMemberError::Capacity(type_));
        }
        let mut requires = false;
        for &constituent in constituents {
            requires |= member_type_requires_instantiation_worker(
                store,
                constituent,
                mapper_parameters,
                array_targets,
                active,
                classify_only,
            )?;
        }
        return Ok(requires);
    }
    if classify_only
        && let Some(targets) = array_targets
        && let Some(array) = store
            .canonical_array_reference_with_targets(targets, type_)
            .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(type_))?
    {
        return member_type_requires_instantiation_worker(
            store,
            array.element_type,
            mapper_parameters,
            array_targets,
            active,
            true,
        );
    }
    if store.type_has_function_type_provenance(type_) {
        let (_, signature, parameters) = function_member_parameters(store, type_)
            .ok_or(GenericInterfaceMemberError::UnsupportedPropertyType(type_))?;
        let return_type = store
            .signature(signature)
            .and_then(super::signatures::Signature::resolved_return_type);
        let fixed_pending_return = classify_only
            && store
                .function_signature_return_annotation(signature)
                .is_some_and(|(annotation, jsdoc)| {
                    !jsdoc
                        && store
                            .source_node_kind(annotation)
                            .is_some_and(SyntaxKind::is_keyword_type)
                });
        if return_type.is_none() && !fixed_pending_return {
            return Err(GenericInterfaceMemberError::UnsupportedPropertyType(type_));
        }
        let narrowed = store
            .signature(signature)
            .and_then(super::signatures::Signature::resolved_type_predicate)
            .and_then(|predicate| store.type_predicate(predicate))
            .and_then(super::signatures::TypePredicate::type_id);
        let mut requires = false;
        for type_ in parameters.into_iter().chain(return_type).chain(narrowed) {
            requires |= member_type_requires_instantiation_worker(
                store,
                type_,
                mapper_parameters,
                array_targets,
                active,
                classify_only,
            )?;
        }
        return Ok(requires);
    }
    if let Some((callback, _)) = optional_function_member(store, type_)? {
        return member_type_requires_instantiation_worker(
            store,
            callback,
            mapper_parameters,
            array_targets,
            active,
            classify_only,
        );
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
            classify_only,
        )?;
        member_type_requires_instantiation_worker(
            store,
            indexed.index_type,
            mapper_parameters,
            array_targets,
            active,
            classify_only,
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
    let mut late_declaration_count = 0usize;
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
        let valid_identity = if late {
            valid_late_bound_unique_symbol_member(
                store,
                owner,
                symbol,
                declarations,
                links,
                resolved_table,
            ) && (!method || valid_interface_method_value(store, symbol, type_).is_some())
        } else if method {
            property.flags().contains(SymbolFlags::METHOD)
                && property
                    .flags()
                    .without(SymbolFlags::METHOD | SymbolFlags::OPTIONAL)
                    == SymbolFlags::NONE
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
            late_declaration_count = late_declaration_count
                .checked_add(declarations.len())
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
    if store.source_computed_member_count(owner) != Some(late_declaration_count) {
        return Err(GenericInterfaceMemberError::InvalidTarget(target));
    }
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

fn cached_instantiated_property_value_matches(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    template: TypeId,
    mapper: TypeMapperId,
    cached: Option<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    if let Some(recovery) = store.instantiated_property_recovery(symbol) {
        let Some(cached) = cached else {
            return false;
        };
        let Some(target) = store
            .value_symbol_links(symbol)
            .and_then(|links| links.target)
        else {
            return false;
        };
        return recovery.matches(
            store,
            symbol,
            target,
            template,
            mapper,
            cached,
            array_targets,
        );
    }
    cached.is_none_or(|cached| {
        cached_instantiated_property_type_matches(store, template, cached, mapper, array_targets)
    })
}

fn cached_instantiated_property_type_matches(
    store: &CanonicalTypeMapperStore,
    template: TypeId,
    cached: TypeId,
    mapper: TypeMapperId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    if let Some(matches) =
        instantiated_tuple_member_type_matches(store, template, cached, mapper, array_targets)
    {
        return matches;
    }
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
    if let Some(tuple) = store
        .canonical_tuple_shape(type_)
        .map_err(|_| GenericInterfaceMemberError::UnsupportedPropertyType(type_))?
    {
        for element in tuple.element_types() {
            validate_nested_reference_targets(
                store,
                *element,
                array_targets,
                active_targets,
                validated_targets,
                visited_types,
            )?;
        }
        visited_types.remove(&type_);
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
            || !cached_instantiated_property_value_matches(
                store,
                *property,
                source.type_,
                mapper,
                links.resolved_type,
                array_targets,
            )
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
    if let Some(recovery) = store.instantiated_index_recovery(actual) {
        return recovery.matches(store, shape, source, actual, mapper, array_targets);
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
        let Ok(sources) =
            mapper_parameters_for_target(store, shape.target, &shape.source_parameters)
        else {
            return false;
        };
        let targets = shape
            .target_arguments
            .iter()
            .copied()
            .chain(std::iter::once(shape.reference))
            .collect::<Vec<_>>();
        cached_instantiation_with_vector(
            store,
            source_info.value_type(),
            &sources,
            &targets,
            array_targets,
            None,
        )
        .ok()
        .flatten()
            == Some(actual_info.value_type())
    };
    value_matches && (source == actual) == (source_info.value_type() == actual_info.value_type())
}

fn prepare_cold_property_proxy(
    store: &CanonicalTypeMapperStore,
    source: SemanticSymbolId,
    readonly: bool,
) -> Result<ColdPropertyPlan, GenericInterfaceMemberError> {
    let target = store
        .symbol(source)
        .ok_or(GenericInterfaceMemberError::InvalidMember(source))?;
    let mut data = SymbolData::new(
        target.flags() | SymbolFlags::TRANSIENT,
        target.name().to_owned(),
    );
    data.check_flags = CheckFlags::INSTANTIATED
        | (target.check_flags()
            & (CheckFlags::LATE | CheckFlags::OPTIONAL_PARAMETER | CheckFlags::REST_PARAMETER))
        | if readonly {
            CheckFlags::READONLY
        } else {
            CheckFlags::NONE
        };
    data.declarations = target.declarations().map(<[_]>::to_vec);
    data.value_declaration = target.value_declaration();
    data.parent = target.parent();
    Ok(ColdPropertyPlan::Proxy {
        target: source,
        data,
        name_type: store
            .value_symbol_links(source)
            .and_then(|links| links.name_type),
    })
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
        || !store.try_reserve_value_symbol_links(proxy_count)
    {
        return Err(GenericInterfaceMemberError::Capacity(shape.reference));
    }
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
        properties.push(prepare_cold_property_proxy(
            store,
            source.symbol,
            target.check_flags().contains(CheckFlags::READONLY),
        )?);
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
    Ok(ColdMembersPlan { table, properties })
}

fn prepare_cold_index_values(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<ColdIndexValues, GenericInterfaceMemberError> {
    let mapper_sources =
        mapper_parameters_for_target(store, shape.target, &shape.source_parameters)?;
    let mapper_targets = shape
        .target_arguments
        .iter()
        .copied()
        .chain(std::iter::once(shape.reference))
        .collect::<Vec<_>>();
    let requires_mapper = !shape.index_infos.is_empty()
        && shape
            .properties
            .iter()
            .any(|property| property.requires_proxy);
    if !store.try_reserve_mappers(usize::from(requires_mapper)) {
        return Err(GenericInterfaceMemberError::Capacity(shape.reference));
    }
    let mapper = requires_mapper.then(|| {
        store
            .new_type_mapper(mapper_sources.clone(), mapper_targets.clone())
            .expect("prevalidated mapper endpoints remain store-owned")
    });
    let mut indexes = Vec::with_capacity(shape.index_infos.len());
    for source in &shape.index_infos {
        let info = store
            .index_info(*source)
            .ok_or(GenericInterfaceMemberError::InvalidTarget(shape.target))?;
        let key_type = info.key_type();
        let template = info.value_type();
        let readonly = info.is_readonly();
        let declaration = info.declaration();
        let components = info.components().to_vec();
        let limit_mark = session.limit_event_mark();
        let result = if let Some(mapper) = mapper {
            instantiate_generic_member_type(store, template, mapper, array_targets, session)?
        } else {
            instantiate_type_with_vector_and_session(
                store,
                template,
                &mapper_sources,
                &mapper_targets,
                array_targets,
                session,
            )
            .map_err(|error| property_instantiation_error(template, &error))?
        };
        let recovery = if session.limit_event_occurred_since(limit_mark) {
            let error_type = session.recovery_error_type().ok_or(
                GenericInterfaceMemberError::UnsupportedPropertyType(template),
            )?;
            let identity = instantiated_index_recovery_identity(
                store,
                &[key_type, template, result, error_type],
                &mapper_sources,
                &mapper_targets,
                array_targets,
            )
            .ok_or(GenericInterfaceMemberError::InvalidCachedMembers(
                shape.reference,
            ))?;
            Some((error_type, identity))
        } else {
            None
        };
        indexes.push(ColdIndexValue {
            source: *source,
            key_type,
            template,
            result,
            readonly,
            declaration,
            components,
            recovery,
        });
    }
    Ok(ColdIndexValues {
        mapper,
        mapper_sources,
        mapper_targets,
        indexes,
    })
}

fn publish_cold_members(
    store: &mut CanonicalTypeMapperStore,
    shape: &GenericInterfaceShape,
    plan: ColdMembersPlan,
    indexes: ColdIndexValues,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<InstantiatedInterfaceMembers, GenericInterfaceMemberError> {
    let ColdIndexValues {
        mapper,
        mapper_sources,
        mapper_targets,
        indexes,
    } = indexes;
    let count = indexes
        .len()
        .checked_add(shape.inherited_index_infos.len())
        .ok_or(GenericInterfaceMemberError::Capacity(shape.reference))?;
    let recovery_count = indexes
        .iter()
        .filter(|index| index.recovery.is_some())
        .count();
    let needs_mapper = mapper.is_none()
        && shape
            .properties
            .iter()
            .any(|property| property.requires_proxy);
    if !store.try_reserve_index_infos(indexes.len())
        || !store.try_reserve_instantiated_index_recoveries(recovery_count)
        || !store.try_reserve_mappers(usize::from(needs_mapper))
    {
        return Err(GenericInterfaceMemberError::Capacity(shape.reference));
    }
    let mut index_infos = Vec::new();
    index_infos
        .try_reserve_exact(count)
        .map_err(|_| GenericInterfaceMemberError::Capacity(shape.reference))?;
    let mut recoveries = Vec::with_capacity(recovery_count);
    let mapper = mapper.or_else(|| {
        needs_mapper.then(|| {
            store
                .new_type_mapper(mapper_sources.clone(), mapper_targets.clone())
                .expect("prevalidated mapper endpoints remain store-owned")
        })
    });
    for value in indexes {
        let index = if value.result == value.template {
            value.source
        } else {
            store
                .alloc_index_info(
                    value.key_type,
                    value.result,
                    value.readonly,
                    value.declaration,
                    value.components.clone(),
                )
                .expect("reserved index allocation has prevalidated source metadata")
        };
        if let Some((error_type, identity)) = value.recovery {
            recoveries.push(InstantiatedIndexRecovery {
                valid: true,
                index,
                source: value.source,
                shape: shape.clone(),
                mapper,
                mapper_sources: mapper_sources.clone(),
                mapper_targets: mapper_targets.clone(),
                key_type: value.key_type,
                template: value.template,
                result: value.result,
                readonly: value.readonly,
                declaration: value.declaration,
                components: value.components,
                array_targets,
                error_type,
                identity,
            });
        }
        index_infos.push(index);
    }
    index_infos.extend_from_slice(&shape.inherited_index_infos);
    let (members, properties) = publish_prepared_property_table(store, plan, mapper);
    assert!(store.set_structured_type_members(
        shape.reference,
        members,
        (!properties.is_empty()).then(|| properties.clone()),
        None,
        None,
        (!index_infos.is_empty()).then_some(index_infos),
    ));
    for recovery in recoveries {
        assert!(store.publish_instantiated_index_recovery(recovery));
    }
    Ok(InstantiatedInterfaceMembers {
        reference: shape.reference,
        target: shape.target,
        mapper,
        members,
        properties,
    })
}

fn publish_prepared_property_table(
    store: &mut CanonicalTypeMapperStore,
    plan: ColdMembersPlan,
    mapper: Option<TypeMapperId>,
) -> (Option<SymbolTableId>, Vec<SemanticSymbolId>) {
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
                    }
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
            Some(None),
        );
        properties.push(symbol);
    }
    (members, properties)
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
    include!("instantiated_members/wave148_heritage_method_invariants.rs");

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

    fn property_object_alias_variable_type(
        parsed: &ParseResult,
        file: FileId,
        context: &mut CanonicalCheckerContext<'_>,
        name: &str,
    ) -> TypeId {
        let symbol = source_symbol(parsed, file, context, name);
        let annotation = context
            .store()
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .and_then(|declaration| context.store().source_direct_type_annotation(declaration))
            .unwrap();
        context.get_type_from_type_node(annotation).unwrap()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check the raw cycle before any reader can start a fresh graph walk.
    fn property_object_alias_cycle_guard_follows_nested_physical_recovery_arguments() {
        use crate::semantic::bootstrap::LiteralTypeCacheError;

        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Box<T> = { value: T }; ",
            "type Root<T> = { value: Box<T> | undefined }; ",
            "declare const left: Root<string>; declare const right: Root<number>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_812);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = checker_context(&parsed, file, options);
        let roots = ["left", "right"]
            .map(|name| property_object_alias_variable_type(&parsed, file, &mut context, name));
        assert_ne!(roots[0], roots[1]);
        let globals = context.global_types().clone();
        let array_targets = CanonicalArrayTargets::from_global_types(&globals);
        let targets = Some(array_targets);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members = roots.map(|receiver| {
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap()
        });
        let properties = members.each_ref().map(|members| members.properties[0]);
        let values = [0, 1].map(|index| {
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                roots[index],
                properties[index],
            )
            .unwrap()
        });
        let root_projection = property_object_alias_projection(context.store(), roots[0])
            .unwrap()
            .unwrap();
        let source_value = context
            .store()
            .value_symbol_links(root_projection.properties[0].symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            cached_scalar_property_object_alias_union(
                context.store(),
                &root_projection,
                source_value,
            ),
            None,
        );
        let box_symbol = source_symbol(&parsed, file, &context, "Box");
        let box_target = context.get_declared_type_of_symbol(box_symbol).unwrap();
        let box_projection = property_object_alias_projection(context.store(), box_target)
            .unwrap()
            .unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let error = bootstrap.error_type;
        let undefined = bootstrap.undefined_type;
        let mut recovering = InstantiationSession::new_recovering(
            context.store(),
            InstantiationLimits {
                max_depth: 1,
                max_count: 100,
            },
            error,
        )
        .unwrap();
        let hidden_arguments = [roots[1], roots[0]];
        let recovered = hidden_arguments.map(|argument| {
            instantiate_type_with_vector_and_session(
                context.store_mut_for_test(),
                box_target,
                &box_projection.parameters,
                &[argument],
                targets,
                &mut recovering,
            )
            .unwrap()
        });
        assert_ne!(recovered[0], recovered[1]);
        assert_eq!(
            (
                recovering.query_count(),
                recovering.total_count(),
                recovering.limit_event_count(),
            ),
            (2, 2, 2),
        );
        let receivers = [roots[0], roots[1], recovered[0], recovered[1]];
        let projections = receivers.map(|receiver| {
            property_object_alias_projection(context.store(), receiver)
                .unwrap()
                .unwrap()
        });
        for (index, projection) in projections[2..].iter().enumerate() {
            assert_eq!(projection.target, box_target);
            assert_eq!(projection.alias_symbol, box_symbol);
            assert_eq!(projection.identity_symbol, box_symbol);
            assert_eq!(projection.arguments, [hidden_arguments[index]]);
            assert_eq!(projection.identity_arguments, [error]);
            let recovery = context
                .store()
                .property_object_alias_recovery(projection.type_)
                .unwrap();
            assert!(recovery.matches_current_result(context.store()));
            assert!(!recovery.physical_slot_recovered(0));
            assert!(recovery.identity_slot_recovered(0));
        }
        let poisoned_values = recovered.map(|receiver| {
            context
                .store_mut_for_test()
                .literal_union_type_with_alias_and_array_targets(
                    &[receiver, undefined],
                    None,
                    targets,
                )
                .unwrap()
        });
        let original_links = properties.map(|property| {
            context
                .store()
                .value_symbol_links(property)
                .cloned()
                .unwrap()
        });
        let objects = [
            root_projection.target,
            box_target,
            roots[0],
            roots[1],
            recovered[0],
            recovered[1],
        ];
        let symbols = [
            root_projection.properties[0].symbol,
            box_projection.properties[0].symbol,
            properties[0],
            properties[1],
        ];
        let nodes = [
            root_projection.declaration,
            box_projection.declaration,
            root_projection.properties[0].type_node,
            box_projection.properties[0].type_node,
        ];
        let unions = [
            source_value,
            values[0],
            values[1],
            poisoned_values[0],
            poisoned_values[1],
        ];
        let snapshot = |store: &CanonicalTypeMapperStore| {
            (
                (
                    property_recovery_store_counts(store),
                    store.type_alias_len(),
                ),
                objects.map(|type_| {
                    let record = store.type_payload(type_).unwrap();
                    let TypeData::Object(object) = record.data() else {
                        panic!("the alias keeps its anonymous object")
                    };
                    let alias = store.type_alias(record.alias().unwrap()).unwrap();
                    (
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        alias.id(),
                        alias.symbol(),
                        alias.type_arguments().map(<[TypeId]>::to_vec),
                        object.clone(),
                    )
                }),
                [root_projection.alias_symbol, box_symbol]
                    .map(|symbol| store.type_alias_links(symbol).cloned()),
                symbols.map(|symbol| store.value_symbol_links(symbol).cloned()),
                nodes.map(|node| store.type_node_links(node).cloned()),
                unions.map(|type_| {
                    let TypeData::Union(union) = store.type_payload(type_).unwrap().data() else {
                        panic!("the property keeps its union")
                    };
                    union.clone()
                }),
                recovered.map(|type_| {
                    let recovery = store.property_object_alias_recovery(type_).unwrap();
                    (
                        recovery.result(),
                        recovery.error_type(),
                        recovery.physical_slot_recovered(0),
                        recovery.identity_slot_recovered(0),
                    )
                }),
            )
        };
        let before = snapshot(context.store());
        let session_before = (
            session.query_count(),
            session.total_count(),
            session.limit_event_mark(),
        );
        for index in 0..2 {
            assert!(context.store_mut_for_test().set_value_symbol_links(
                properties[index],
                ValueSymbolLinks {
                    resolved_type: Some(poisoned_values[index]),
                    ..original_links[index].clone()
                },
            ));
        }
        let poisoned = snapshot(context.store());
        assert_eq!(poisoned.0, before.0);
        // left -> recovered[0] -> right -> recovered[1] -> left.
        // Both recovered objects hide their physical edge behind a visible error.
        for _ in 0..2 {
            for projection in &projections {
                assert_eq!(
                    validate_property_object_alias_cache_cycles(
                        context.store(),
                        projection,
                        targets,
                    ),
                    Err(RelationUnavailable::UnsupportedStructuredType(
                        projection.type_
                    )),
                );
            }
            for receiver in receivers {
                assert_eq!(
                    validate_property_object_alias_members_with_array_targets(
                        context.store(),
                        receiver,
                        targets,
                    ),
                    Err(RelationUnavailable::UnsupportedStructuredType(receiver)),
                );
                assert_eq!(
                    context
                        .store()
                        .validate_cached_array_capability_with_array_targets(
                            array_targets,
                            receiver
                        ),
                    Err(LiteralTypeCacheError::UnsupportedUnionConstituent(receiver)),
                );
            }
            for index in 0..2 {
                assert_eq!(
                    demand_property_object_alias_property(
                        context.store_mut_for_test(),
                        &host,
                        &globals,
                        options,
                        &mut session,
                        &mut diagnostics,
                        roots[index],
                        properties[index],
                    ),
                    Err(SourceCheckError::RelationUnavailable(
                        RelationUnavailable::UnsupportedStructuredType(roots[index]),
                    )),
                );
                assert!(
                    context
                        .store()
                        .property_object_alias_recovery(recovered[index])
                        .unwrap()
                        .matches_current_result(context.store())
                );
            }
            assert_eq!(snapshot(context.store()), poisoned);
        }
        for index in 0..2 {
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(properties[index], original_links[index].clone())
            );
        }
        assert_eq!(snapshot(context.store()), before);
        for index in 0..2 {
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    roots[index],
                    targets,
                ),
                Ok(Some(members[index].clone())),
            );
            assert_eq!(
                demand_property_object_alias_property(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    roots[index],
                    properties[index],
                ),
                Ok(values[index]),
            );
        }
        for receiver in receivers {
            assert_eq!(
                context
                    .store()
                    .validate_cached_array_capability_with_array_targets(array_targets, receiver),
                Ok(()),
            );
        }
        assert_eq!(snapshot(context.store()), before);
        assert_eq!(
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_mark()
            ),
            session_before,
        );
        assert_eq!(
            (
                recovering.query_count(),
                recovering.total_count(),
                recovering.limit_event_count()
            ),
            (2, 2, 2),
        );
        for receiver in [box_target, recovered[0], recovered[1]] {
            assert!(
                !context
                    .store()
                    .type_payload(receiver)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
        }
        assert!(
            context
                .store()
                .value_symbol_links(box_projection.properties[0].symbol)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert!(diagnostics.is_empty());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep rejection and exact restore in the same source fixture.
    fn property_object_alias_rejects_union_cache_reentry_and_reuses_restored_ids() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Box<T> = { value: T }; declare const box: Box<string>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_804);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = checker_context(&parsed, file, options);
        let receiver = property_object_alias_variable_type(&parsed, file, &mut context, "box");
        let globals = context.global_types().clone();
        let array_targets = CanonicalArrayTargets::from_global_types(&globals);
        let targets = Some(array_targets);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members =
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap();
        let property = members.properties[0];
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                receiver,
                property,
            ),
            Ok(string)
        );
        let invalid_union = context
            .store_mut_for_test()
            .literal_union_type_with_alias_and_array_targets(&[receiver, undefined], None, targets)
            .unwrap();
        let original = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let before = (
            property_recovery_store_counts(context.store()),
            context.store().type_alias_len(),
        );
        assert!(context.store_mut_for_test().set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(invalid_union),
                ..original.clone()
            }
        ));
        for _ in 0..2 {
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Err(RelationUnavailable::InvalidStructuredMembers(receiver)),
            );
            assert_eq!(
                demand_property_object_alias_property(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    receiver,
                    property,
                ),
                Err(SourceCheckError::RelationUnavailable(
                    RelationUnavailable::InvalidStructuredMembers(receiver)
                ))
            );
            assert_eq!(
                context
                    .store()
                    .validate_cached_array_capability_with_array_targets(array_targets, receiver),
                Err(
                    crate::semantic::bootstrap::LiteralTypeCacheError::InvalidCachedUnion(receiver)
                ),
            );
            assert_eq!(
                (
                    property_recovery_store_counts(context.store()),
                    context.store().type_alias_len()
                ),
                before
            );
            assert!(diagnostics.is_empty());
        }
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(property, original)
        );
        assert_eq!(
            validate_property_object_alias_members_with_array_targets(
                context.store(),
                receiver,
                targets
            ),
            Ok(Some(members)),
        );
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                receiver,
                property,
            ),
            Ok(string)
        );
        assert_eq!(
            (
                property_recovery_store_counts(context.store()),
                context.store().type_alias_len()
            ),
            before
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The two routes share the same original and poisoned proxy.
    fn property_object_alias_rejects_holder_union_and_cold_original_cycles() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Box<T> = { value: T | undefined }; ",
            "interface Holder { box: Box<string> } ",
            "type Relay<U> = { item: Holder }; ",
            "declare const box: Box<string>; declare const holder: Holder; ",
            "declare const relay: Relay<number>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_806);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = checker_context(&parsed, file, options);
        let receiver = property_object_alias_variable_type(&parsed, file, &mut context, "box");
        let holder = property_object_alias_variable_type(&parsed, file, &mut context, "holder");
        let relay = property_object_alias_variable_type(&parsed, file, &mut context, "relay");
        assert_eq!(
            validate_resolved_declared_property_object(context.store(), holder),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        );
        assert_eq!(
            super::super::object_members::resolved_declared_property_types(context.store(), holder),
            Some(vec![receiver])
        );
        let globals = context.global_types().clone();
        let targets = Some(CanonicalArrayTargets::from_global_types(&globals));
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members =
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap();
        let property = members.properties[0];
        let value = demand_property_object_alias_property(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            receiver,
            property,
        )
        .unwrap();
        let projection = property_object_alias_projection(context.store(), receiver)
            .unwrap()
            .unwrap();
        let original_type = context
            .store()
            .value_symbol_links(projection.properties[0].symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            cached_scalar_property_object_alias_union(context.store(), &projection, original_type),
            Some(value)
        );
        let relay_source = property_object_alias_projection(context.store(), relay)
            .unwrap()
            .unwrap()
            .target;
        let relay_members =
            resolve_property_object_alias_members(context.store_mut_for_test(), relay_source)
                .unwrap();
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                relay_source,
                relay_members.properties[0],
            ),
            Ok(holder)
        );
        for type_ in [relay_source, relay] {
            assert!(
                !context
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
        }
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let direct_union = context
            .store_mut_for_test()
            .literal_union_type_with_alias_and_array_targets(&[holder, undefined], None, targets)
            .unwrap();
        let cold_union = context
            .store_mut_for_test()
            .literal_union_type_with_alias_and_array_targets(&[relay, undefined], None, targets)
            .unwrap();
        let original = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let before = (
            property_recovery_store_counts(context.store()),
            context.store().type_alias_len(),
        );
        for candidate in [direct_union, cold_union] {
            assert!(context.store_mut_for_test().set_value_symbol_links(
                property,
                ValueSymbolLinks {
                    resolved_type: Some(candidate),
                    ..original.clone()
                }
            ));
            for _ in 0..2 {
                assert_eq!(
                    validate_property_object_alias_cache_cycles(
                        context.store(),
                        &projection,
                        targets
                    ),
                    Err(RelationUnavailable::UnsupportedStructuredType(receiver))
                );
                assert_eq!(
                    validate_property_object_alias_members_with_array_targets(
                        context.store(),
                        receiver,
                        targets
                    ),
                    Err(RelationUnavailable::InvalidStructuredMembers(receiver))
                );
                assert_eq!(
                    demand_property_object_alias_property(
                        context.store_mut_for_test(),
                        &host,
                        &globals,
                        options,
                        &mut session,
                        &mut diagnostics,
                        receiver,
                        property,
                    ),
                    Err(SourceCheckError::RelationUnavailable(
                        RelationUnavailable::InvalidStructuredMembers(receiver)
                    ))
                );
                assert_eq!(
                    (
                        property_recovery_store_counts(context.store()),
                        context.store().type_alias_len()
                    ),
                    before
                );
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(property, original.clone())
            );
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Ok(Some(members.clone()))
            );
            assert_eq!(
                demand_property_object_alias_property(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    receiver,
                    property,
                ),
                Ok(value)
            );
            assert_eq!(
                (
                    property_recovery_store_counts(context.store()),
                    context.store().type_alias_len()
                ),
                before
            );
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Use a real inherited proxy before poisoning the alias cache.
    fn property_object_alias_cycle_guard_follows_generic_heritage_proxies() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Box<T> = { value: T | undefined }; ",
            "interface Base<U> { inherited: U | undefined } ",
            "interface Holder extends Base<Box<string>> {} ",
            "declare const box: Box<string>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_808);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = checker_context(&parsed, file, options);
        context.check_source_file(file).unwrap();
        let receiver = property_object_alias_variable_type(&parsed, file, &mut context, "box");
        let holder_symbol = source_symbol(&parsed, file, &context, "Holder");
        let holder = context
            .store()
            .declared_type_links(holder_symbol)
            .unwrap()
            .declared_type
            .unwrap();
        let TypeData::Interface(interface) = context.store().type_payload(holder).unwrap().data()
        else {
            panic!("Holder must keep its source interface identity");
        };
        let base = interface.resolved_base_types.as_ref().unwrap()[0];
        let inherited = context
            .store()
            .symbol_table(interface.reference.object.structured.members.unwrap())
            .unwrap()
            .get_source("inherited")
            .unwrap();
        let inherited_value = context
            .store_mut_for_test()
            .resolve_generic_interface_property(base, "inherited", None)
            .unwrap()
            .unwrap();
        assert_eq!(inherited_value.symbol(), inherited);
        assert!(matches!(
            context
                .store()
                .type_payload(inherited_value.type_id())
                .unwrap()
                .data(),
            TypeData::Union(_)
        ));
        let inherited_links = context
            .store()
            .value_symbol_links(inherited)
            .unwrap()
            .clone();
        let globals = context.global_types().clone();
        let targets = Some(CanonicalArrayTargets::from_global_types(&globals));
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members =
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap();
        let property = members.properties[0];
        let value = demand_property_object_alias_property(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            receiver,
            property,
        )
        .unwrap();
        let projection = property_object_alias_projection(context.store(), receiver)
            .unwrap()
            .unwrap();
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let candidate = context
            .store_mut_for_test()
            .literal_union_type_with_alias_and_array_targets(&[holder, undefined], None, targets)
            .unwrap();
        let original = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let before = property_recovery_store_counts(context.store());
        assert!(context.store_mut_for_test().set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(candidate),
                ..original.clone()
            }
        ));
        for _ in 0..2 {
            assert_eq!(
                validate_property_object_alias_cache_cycles(context.store(), &projection, targets),
                Err(RelationUnavailable::UnsupportedStructuredType(receiver))
            );
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Err(RelationUnavailable::InvalidStructuredMembers(receiver))
            );
            assert_eq!(
                context.store().value_symbol_links(inherited),
                Some(&inherited_links)
            );
            assert_eq!(property_recovery_store_counts(context.store()), before);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(property, original)
        );
        assert_eq!(
            validate_property_object_alias_members_with_array_targets(
                context.store(),
                receiver,
                targets
            ),
            Ok(Some(members))
        );
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                receiver,
                property,
            ),
            Ok(value)
        );
        assert_eq!(property_recovery_store_counts(context.store()), before);
        assert!(diagnostics.is_empty());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep two cold library annotation routes and exact replay together.
    fn property_object_alias_cycle_guard_reads_cold_library_annotations() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface ColdProperty { p: (Holder) } ",
            "interface ColdMethod { method(): Holder }",
        ));
        let parsed = parse_source_file(concat!(
            "type Box<T> = { value: T | undefined }; ",
            "interface Holder { box: Box<string> } declare const box: Box<string>; ",
            "declare const holder: Holder;",
        ));
        let library_file = FileId::new(19_809);
        let file = FileId::new(19_810);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, default_library) in
            [(&library, library_file, true), (&parsed, file, false)]
        {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!(
                            "\"/project/alias-cycle-{}.ts\"",
                            file.index()
                        )),
                        CanonicalSourceLanguage::TypeScript,
                        default_library,
                        default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(library_file, &library.arena), (file, &parsed.arena)],
            options,
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        let receiver = property_object_alias_variable_type(&parsed, file, &mut context, "box");
        let holder = property_object_alias_variable_type(&parsed, file, &mut context, "holder");
        let globals = context.global_types().clone();
        let targets = Some(CanonicalArrayTargets::from_global_types(&globals));
        let library_bound = context.file(library_file).unwrap().1.clone();
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&library.arena, &library_bound), (&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members =
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap();
        let property = members.properties[0];
        let value = demand_property_object_alias_property(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            receiver,
            property,
        )
        .unwrap();
        let projection = property_object_alias_projection(context.store(), receiver)
            .unwrap()
            .unwrap();
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let mut candidates = Vec::new();
        let mut cold_members = Vec::new();
        for (owner_name, member_name) in [("ColdProperty", "p"), ("ColdMethod", "method")] {
            let owner = source_symbol(&library, library_file, &context, owner_name);
            let type_ = context
                .store_mut_for_test()
                .get_declared_type_of_symbol(&host, owner)
                .unwrap();
            let member = context
                .store()
                .symbol(owner)
                .unwrap()
                .members()
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get_source(member_name))
                .unwrap();
            let declaration = context
                .store()
                .symbol(member)
                .unwrap()
                .value_declaration()
                .unwrap();
            let annotation = context
                .store()
                .source_direct_type_annotation(declaration)
                .unwrap();
            let query_node = if context.store().source_node_kind(annotation)
                == Some(SyntaxKind::ParenthesizedType)
            {
                context.store().source_direct_children(annotation).unwrap()[0]
            } else {
                annotation
            };
            assert_eq!(context.get_type_from_type_node(query_node), Ok(holder));
            if query_node != annotation {
                assert!(
                    context
                        .store()
                        .type_node_links(annotation)
                        .is_none_or(|links| links.resolved_type.is_none())
                );
            }
            assert!(
                context
                    .store()
                    .value_symbol_links(member)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            let TypeData::Interface(interface) =
                context.store().type_payload(type_).unwrap().data()
            else {
                panic!("the library identity must remain an interface");
            };
            assert!(!interface.declared_members_resolved);
            assert_eq!(
                interface.reference.object.structured,
                StructuredTypeData::default()
            );
            candidates.push(
                context
                    .store_mut_for_test()
                    .literal_union_type_with_alias_and_array_targets(
                        &[type_, undefined],
                        None,
                        targets,
                    )
                    .unwrap(),
            );
            cold_members.push((type_, member));
        }
        let original = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let before = property_recovery_store_counts(context.store());
        for candidate in candidates {
            assert!(context.store_mut_for_test().set_value_symbol_links(
                property,
                ValueSymbolLinks {
                    resolved_type: Some(candidate),
                    ..original.clone()
                }
            ));
            for _ in 0..2 {
                assert_eq!(
                    validate_property_object_alias_cache_cycles(
                        context.store(),
                        &projection,
                        targets
                    ),
                    Err(RelationUnavailable::UnsupportedStructuredType(receiver))
                );
                assert_eq!(
                    validate_property_object_alias_members_with_array_targets(
                        context.store(),
                        receiver,
                        targets
                    ),
                    Err(RelationUnavailable::InvalidStructuredMembers(receiver))
                );
                assert_eq!(property_recovery_store_counts(context.store()), before);
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(property, original.clone())
            );
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Ok(Some(members.clone()))
            );
            assert_eq!(
                demand_property_object_alias_property(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    receiver,
                    property,
                ),
                Ok(value)
            );
            assert_eq!(property_recovery_store_counts(context.store()), before);
        }
        for (type_, member) in cold_members {
            assert!(
                !context
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(member)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
        }
        assert!(diagnostics.is_empty());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Warm the unrelated generic template before querying its concrete argument.
    fn property_object_alias_cycle_guard_keeps_direct_generic_arguments_lazy() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Box<T> = { value: T }; interface Wrap<U> { next: Box<Wrap<U>> } ",
            "declare const box: Box<Wrap<string>>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_811);
        let options = CanonicalCheckerOptions::default();
        let mut context = checker_context(&parsed, file, options);
        context.check_source_file(file).unwrap();
        let wrap = source_symbol(&parsed, file, &context, "Wrap");
        let next = context
            .store()
            .symbol(wrap)
            .unwrap()
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("next"))
            .unwrap();
        let source_box = context
            .store()
            .value_symbol_links(next)
            .unwrap()
            .resolved_type
            .unwrap();
        let source_projection = property_object_alias_projection(context.store(), source_box)
            .unwrap()
            .unwrap();
        let source_wrap = source_projection.arguments[0];
        let globals = context.global_types().clone();
        let array_targets = CanonicalArrayTargets::from_global_types(&globals);
        let targets = Some(array_targets);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let source_members =
            resolve_property_object_alias_members(context.store_mut_for_test(), source_box)
                .unwrap();
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                source_box,
                source_members.properties[0],
            ),
            Ok(source_wrap)
        );
        let receiver = property_object_alias_variable_type(&parsed, file, &mut context, "box");
        let projection = property_object_alias_projection(context.store(), receiver)
            .unwrap()
            .unwrap();
        let concrete_wrap = projection.arguments[0];
        assert_ne!(concrete_wrap, source_wrap);
        let members =
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap();
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                receiver,
                members.properties[0],
            ),
            Ok(concrete_wrap)
        );
        let before = property_recovery_store_counts(context.store());
        for _ in 0..2 {
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Ok(Some(members.clone()))
            );
            assert_eq!(
                context
                    .store()
                    .validate_cached_array_capability_with_array_targets(array_targets, receiver),
                Ok(())
            );
            assert_eq!(property_recovery_store_counts(context.store()), before);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(next)
                    .unwrap()
                    .resolved_type,
                Some(source_box)
            );
        }
        assert!(diagnostics.is_empty());
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn property_object_alias_cycle_guard_keeps_ordinary_recursive_interfaces() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Node { next: Node } type Box<T> = { value: T }; ",
            "declare const box: Box<Node>; declare const node: Node;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_807);
        let options = CanonicalCheckerOptions::default();
        let mut context = checker_context(&parsed, file, options);
        let receiver = property_object_alias_variable_type(&parsed, file, &mut context, "box");
        let node = property_object_alias_variable_type(&parsed, file, &mut context, "node");
        let members =
            resolve_property_object_alias_members(context.store_mut_for_test(), receiver).unwrap();
        let globals = context.global_types().clone();
        let array_targets = CanonicalArrayTargets::from_global_types(&globals);
        let targets = Some(array_targets);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            demand_property_object_alias_property(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                receiver,
                members.properties[0],
            ),
            Ok(node)
        );
        let before = property_recovery_store_counts(context.store());
        for _ in 0..2 {
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Ok(Some(members.clone()))
            );
            assert_eq!(
                context
                    .store()
                    .validate_cached_array_capability_with_array_targets(array_targets, receiver),
                Ok(())
            );
            assert_eq!(property_recovery_store_counts(context.store()), before);
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Both nested member caches must keep their identities on replay.
    fn property_object_alias_cycle_guard_accepts_acyclic_nested_instances() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type Box<T> = { value: T }; ",
            "declare const nested: Box<Box<string>>; declare const direct: Box<string>;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(19_805);
        let options = CanonicalCheckerOptions::default();
        let mut context = checker_context(&parsed, file, options);
        let outer = property_object_alias_variable_type(&parsed, file, &mut context, "nested");
        let inner = property_object_alias_variable_type(&parsed, file, &mut context, "direct");
        assert_eq!(
            property_object_alias_projection(context.store(), outer)
                .unwrap()
                .unwrap()
                .arguments,
            [inner]
        );
        let outer_members =
            resolve_property_object_alias_members(context.store_mut_for_test(), outer).unwrap();
        let inner_members =
            resolve_property_object_alias_members(context.store_mut_for_test(), inner).unwrap();
        let globals = context.global_types().clone();
        let array_targets = CanonicalArrayTargets::from_global_types(&globals);
        let targets = Some(array_targets);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            crate::semantic::production::GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        for (receiver, property, expected) in [
            (outer, outer_members.properties[0], inner),
            (inner, inner_members.properties[0], string),
        ] {
            assert_eq!(
                demand_property_object_alias_property(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    receiver,
                    property,
                ),
                Ok(expected)
            );
        }
        let before = (
            property_recovery_store_counts(context.store()),
            context.store().type_alias_len(),
        );
        for (receiver, members, expected) in [
            (outer, outer_members, inner),
            (inner, inner_members, string),
        ] {
            assert_eq!(
                validate_property_object_alias_members_with_array_targets(
                    context.store(),
                    receiver,
                    targets
                ),
                Ok(Some(members.clone())),
            );
            assert_eq!(
                demand_property_object_alias_property(
                    context.store_mut_for_test(),
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                    receiver,
                    members.properties[0],
                ),
                Ok(expected)
            );
            assert_eq!(
                context
                    .store()
                    .validate_cached_array_capability_with_array_targets(array_targets, receiver),
                Ok(())
            );
            assert_eq!(
                (
                    property_recovery_store_counts(context.store()),
                    context.store().type_alias_len()
                ),
                before
            );
        }
        assert!(diagnostics.is_empty());
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

    struct PropertyRecoveryFixture<'a> {
        context: CanonicalCheckerContext<'a>,
        receiver: TypeId,
        reference: TypeId,
        members: InstantiatedInterfaceMembers,
        proxy: SemanticSymbolId,
        sibling: SemanticSymbolId,
        target: SemanticSymbolId,
        template: TypeId,
        mapper: TypeMapperId,
        array_targets: CanonicalArrayTargets,
    }

    fn property_recovery_fixture(
        parsed: &ParseResult,
        file: FileId,
    ) -> PropertyRecoveryFixture<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(parsed, file, CanonicalCheckerOptions::default());
        let box_owner = source_symbol(parsed, file, &context, "Box");
        let first = context
            .store()
            .symbol(box_owner)
            .unwrap()
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("first"))
            .unwrap();
        let annotation = context
            .store()
            .symbol(first)
            .filter(|record| record.flags().contains(SymbolFlags::PROPERTY))
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .and_then(|declaration| context.store().source_direct_type_annotation(declaration));
        if let Some(annotation) = annotation
            && !matches!(
                &parsed.arena.get(annotation.node).unwrap().data,
                NodeData::TypeReferenceNode(reference) if reference.type_arguments.is_none()
            )
        {
            let box_type = context.get_declared_type_of_symbol(box_owner).unwrap();
            let child = context.store().intrinsic_bootstrap().and_then(|bootstrap| {
                context
                    .store()
                    .symbol_table(bootstrap.globals)?
                    .get_source("Child")
            });
            if let Some(child) = child {
                let target = context.get_declared_type_of_symbol(child).unwrap();
                let TypeData::Interface(interface) =
                    context.store().type_payload(target).unwrap().data()
                else {
                    panic!("Child must retain its generic target")
                };
                let parameter = interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0];
                publish_generic_target_for_test(
                    &mut context,
                    target,
                    &[("value", parameter)],
                    None,
                );
            }
            let first_type = context.get_type_from_type_node(annotation).unwrap();
            let TypeData::Interface(interface) =
                context.store().type_payload(box_type).unwrap().data()
            else {
                panic!("Box must retain its generic target")
            };
            let parameter = interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0];
            // Publish wrapped annotations directly. Direct properties and methods use source inheritance.
            publish_generic_target_for_test(
                &mut context,
                box_type,
                &[("first", first_type), ("second", parameter)],
                None,
            );
        }
        let owner = source_symbol(parsed, file, &context, "Derived");
        let receiver = context.get_declared_type_of_symbol(owner).unwrap();
        let array_targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let TypeData::Interface(interface) = context.store().type_payload(receiver).unwrap().data()
        else {
            panic!("Derived must retain its interface type")
        };
        let reference = interface.resolved_base_types.as_ref().unwrap()[0];
        let store = context.store_mut_for_test();
        let members =
            resolve_members_with_array_targets(store, reference, Some(array_targets)).unwrap();
        let table = store.symbol_table(members.members().unwrap()).unwrap();
        let proxy = table.get_source("first").unwrap();
        let sibling = table.get_source("second").unwrap();
        let links = store.value_symbol_links(proxy).unwrap();
        assert!(links.resolved_type.is_none());
        let target = links.target.unwrap();
        let mapper = links.mapper.unwrap();
        let template = store
            .value_symbol_links(target)
            .unwrap()
            .resolved_type
            .unwrap();
        PropertyRecoveryFixture {
            context,
            receiver,
            reference,
            members,
            proxy,
            sibling,
            target,
            template,
            mapper,
            array_targets,
        }
    }

    fn property_recovery_source(member: &str) -> ParseResult {
        parse_source_file(&format!(
            "interface Array<T> {{}} interface ReadonlyArray<T> {{}} \
             interface Child<T> {{ value: T; }} \
             interface Box<T> {{ {member} second: T; }} \
             interface Derived extends Box<number> {{}}"
        ))
    }

    fn property_recovery_store_counts(
        store: &CanonicalTypeMapperStore,
    ) -> ([usize; 6], [usize; 26]) {
        (
            [
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.checker_link_allocated_lengths(),
        )
    }

    #[test]
    fn property_recovery_keeps_direct_and_wrapped_results_on_warm_reads() {
        use crate::semantic::structured_members::{
            InterfaceHeritageMembersValidation, inherited_generic_property_reference,
            validate_interface_heritage_members_with_array_targets,
        };

        for (annotation, max_count) in [
            ("T", 0),
            ("[T]", 0),
            ("readonly [head: T, tail?: T]", 0),
            ("[] | [T]", 0),
            ("Array<T>", 1),
            ("ReadonlyArray<T>", 1),
            ("Child<T>", 1),
            ("[Child<T>, T[]]", 1),
        ] {
            eprintln!("recovery template: {annotation}");
            let parsed = property_recovery_source(&format!("first: {annotation};"));
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_280));
            let store = fixture.context.store_mut_for_test();
            let error_type = store.intrinsic_bootstrap().unwrap().error_type;
            let template_links = store.value_symbol_links(fixture.target).cloned().unwrap();
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let mark = session.limit_event_mark();
            let result = demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session,
            )
            .unwrap_or_else(|error| panic!("{annotation}: {error:?}"));
            assert!(session.limit_event_occurred_since(mark), "{annotation}");
            assert_eq!(
                store
                    .value_symbol_links(fixture.proxy)
                    .unwrap()
                    .resolved_type,
                Some(result)
            );
            assert!(
                store
                    .instantiated_property_recovery(fixture.proxy)
                    .is_some()
            );
            assert!(!cached_instantiated_property_type_matches(
                store,
                fixture.template,
                result,
                fixture.mapper,
                Some(fixture.array_targets)
            ));
            if annotation == "T" {
                assert_eq!(result, error_type);
            } else {
                assert_ne!(result, error_type, "{annotation}");
            }
            assert_eq!(
                validate_generic_interface_members(
                    store,
                    fixture.reference,
                    Some(fixture.array_targets)
                ),
                Ok(Some(fixture.members.clone())),
                "{annotation}"
            );
            assert_eq!(
                validate_interface_heritage_members_with_array_targets(
                    store,
                    fixture.receiver,
                    Some(fixture.array_targets)
                ),
                InterfaceHeritageMembersValidation::Valid,
                "{annotation}"
            );
            assert_eq!(
                inherited_generic_property_reference(
                    store,
                    fixture.receiver,
                    fixture.proxy,
                    Some(fixture.array_targets)
                ),
                Some(fixture.reference)
            );

            if annotation == "Child<T>" {
                let child = store
                    .resolve_generic_interface_property(result, "value", None)
                    .unwrap()
                    .unwrap();
                assert_eq!(child.type_id(), error_type);
            }

            let before = property_recovery_store_counts(store);
            let counts = (session.query_count(), session.total_count());
            let mark = session.limit_event_mark();
            for reset_query in [false, true] {
                if reset_query {
                    session.reset_query();
                }
                let property = resolve_property_with_array_targets_and_session(
                    store,
                    fixture.reference,
                    EscapedNameRef::source("first"),
                    Some(fixture.array_targets),
                    &mut session,
                )
                .unwrap()
                .unwrap();
                assert_eq!(property.symbol(), fixture.proxy);
                assert_eq!(property.type_id(), result);
                assert_eq!(
                    session.query_count(),
                    if reset_query { 0 } else { counts.0 }
                );
                assert_eq!(session.total_count(), counts.1);
                assert!(!session.limit_event_occurred_since(mark));
            }
            let mut other = InstantiationSession::new(InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            });
            let mark = other.limit_event_mark();
            assert_eq!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    Some(fixture.array_targets),
                    &mut other
                ),
                Ok(result)
            );
            assert_eq!((other.query_count(), other.total_count()), (0, 0));
            assert!(!other.limit_event_occurred_since(mark));
            assert_eq!(property_recovery_store_counts(store), before);
            assert_eq!(
                store.value_symbol_links(fixture.target),
                Some(&template_links)
            );
            assert!(
                store
                    .value_symbol_links(fixture.sibling)
                    .unwrap()
                    .resolved_type
                    .is_none()
            );
        }
    }

    #[test]
    fn property_recovery_allows_later_source_parameter_default_resolution() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Box<T = string> { first: T; second: T; } ",
            "interface Derived extends Box<number> {} type DefaultBox = Box;",
        ));
        let file = FileId::new(6_290);
        let mut fixture = property_recovery_fixture(&parsed, file);
        let alias = source_symbol(&parsed, file, &fixture.context, "DefaultBox");
        let store = fixture.context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (error_type, string) = (bootstrap.error_type, bootstrap.string_type);
        let parameter_default = |store: &CanonicalTypeMapperStore| {
            let TypeData::TypeParameter(parameter) =
                store.type_payload(fixture.template).unwrap().data()
            else {
                panic!("the property must retain its source parameter")
            };
            parameter.resolved_default_type
        };
        assert_eq!(parameter_default(store), None);
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error_type,
        )
        .unwrap();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(error_type)
        );
        fixture.context.get_declared_type_of_symbol(alias).unwrap();
        let store = fixture.context.store_mut_for_test();
        assert_eq!(parameter_default(store), Some(string));
        let before = property_recovery_store_counts(store);
        let mark = session.limit_event_mark();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(error_type)
        );
        assert_eq!(property_recovery_store_counts(store), before);
        assert!(!session.limit_event_occurred_since(mark));
        assert_eq!((session.query_count(), session.total_count()), (0, 0));
    }

    #[test]
    fn property_recovery_raw_proxy_and_target_writes_revoke_the_proof() {
        for mutation in ["proxy", "clear", "restore", "normal", "target", "template"] {
            let parsed = property_recovery_source("first: T;");
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_281));
            let store = fixture.context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (error_type, number) = (bootstrap.error_type, bootstrap.number_type);
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            assert_eq!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    Some(fixture.array_targets),
                    &mut session
                ),
                Ok(error_type)
            );
            let symbol = if matches!(mutation, "target" | "template") {
                fixture.target
            } else {
                fixture.proxy
            };
            let mut links = store.value_symbol_links(symbol).cloned().unwrap();
            if mutation == "restore" {
                assert!(store.set_value_symbol_links(
                    symbol,
                    ValueSymbolLinks {
                        resolved_type: None,
                        ..links.clone()
                    }
                ));
            }
            if mutation == "clear" {
                links.resolved_type = None;
            } else if matches!(mutation, "normal" | "template") {
                links.resolved_type = Some(number);
            }
            assert!(store.set_value_symbol_links(symbol, links.clone()));
            assert!(
                !store
                    .instantiated_property_recovery(fixture.proxy)
                    .unwrap()
                    .valid
            );
            let before = (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
            );
            let mark = session.limit_event_mark();
            assert_eq!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    Some(fixture.array_targets),
                    &mut session
                ),
                Err(GenericInterfaceMemberError::InvalidCachedProperty(
                    fixture.proxy
                )),
                "{mutation}"
            );
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before,
                "{mutation}"
            );
            assert_eq!(store.value_symbol_links(symbol), Some(&links));
            assert!(!session.limit_event_occurred_since(mark));
            assert_eq!((session.query_count(), session.total_count()), (0, 0));
        }
    }

    #[test]
    fn property_recovery_rejects_unproven_error_any_and_other_proxy_values() {
        for mutation in ["error", "any", "other_proxy"] {
            let parsed = property_recovery_source("first: T;");
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_282));
            let store = fixture.context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (error_type, any) = (bootstrap.error_type, bootstrap.any_type);
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let symbol = if mutation == "other_proxy" {
                assert_eq!(
                    demand_instantiated_property_type(
                        store,
                        fixture.reference,
                        fixture.proxy,
                        Some(fixture.array_targets),
                        &mut session
                    ),
                    Ok(error_type)
                );
                fixture.sibling
            } else {
                fixture.proxy
            };
            let links = ValueSymbolLinks {
                resolved_type: Some(if mutation == "any" { any } else { error_type }),
                ..store.value_symbol_links(symbol).cloned().unwrap()
            };
            assert!(store.set_value_symbol_links(symbol, links.clone()));
            assert!(store.instantiated_property_recovery(symbol).is_none());
            let before = (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
            );
            let mark = session.limit_event_mark();
            assert_eq!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    symbol,
                    Some(fixture.array_targets),
                    &mut session
                ),
                Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol)),
                "{mutation}"
            );
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before
            );
            assert_eq!(store.value_symbol_links(symbol), Some(&links));
            assert!(!session.limit_event_occurred_since(mark));
        }
    }

    #[test]
    fn property_recovery_failed_and_unrelated_writes_keep_the_proof() {
        let parsed = property_recovery_source("first: T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_283));
        let mut foreign = CanonicalTypeMapperStore::new();
        let foreign_type = foreign
            .alloc_intrinsic_type(TypeFlags::ANY, "foreign")
            .unwrap();
        let store = fixture.context.store_mut_for_test();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error_type,
        )
        .unwrap();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(error_type)
        );
        let proxy_links = store.value_symbol_links(fixture.proxy).cloned().unwrap();
        let before = (
            property_recovery_store_counts(store),
            store.relation_state_snapshot(),
        );
        assert!(!store.set_value_symbol_links(
            fixture.proxy,
            ValueSymbolLinks {
                resolved_type: Some(foreign_type),
                ..proxy_links.clone()
            }
        ));
        assert_eq!(
            (
                property_recovery_store_counts(store),
                store.relation_state_snapshot()
            ),
            before
        );
        let sibling_links = store.value_symbol_links(fixture.sibling).cloned().unwrap();
        assert!(store.set_value_symbol_links(fixture.sibling, sibling_links));
        assert!(
            store
                .instantiated_property_recovery(fixture.proxy)
                .unwrap()
                .valid
        );
        let mark = session.limit_event_mark();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(error_type)
        );
        assert_eq!(store.value_symbol_links(fixture.proxy), Some(&proxy_links));
        assert!(!session.limit_event_occurred_since(mark));
    }

    #[test]
    fn property_recovery_rejects_noncanonical_recovery_before_instantiation() {
        let parsed = property_recovery_source("first: T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_284));
        let store = fixture.context.store_mut_for_test();
        let any = store.intrinsic_bootstrap().unwrap().any_type;
        let links = store.value_symbol_links(fixture.proxy).cloned().unwrap();
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            any,
        )
        .unwrap();
        let before = (
            property_recovery_store_counts(store),
            store.relation_state_snapshot(),
        );
        let mark = session.limit_event_mark();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(
                fixture.proxy
            ))
        );
        assert_eq!(
            (
                property_recovery_store_counts(store),
                store.relation_state_snapshot()
            ),
            before
        );
        assert_eq!(store.value_symbol_links(fixture.proxy), Some(&links));
        assert!(
            store
                .instantiated_property_recovery(fixture.proxy)
                .is_none()
        );
        assert_eq!((session.query_count(), session.total_count()), (0, 0));
        assert!(!session.limit_event_occurred_since(mark));
    }

    #[test]
    fn property_recovery_rejects_changed_wrapped_results() {
        for (annotation, max_count) in [("Array<T>", 1), ("[T]", 0), ("Child<T>", 1)] {
            let parsed = property_recovery_source(&format!("first: {annotation};"));
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_285));
            let store = fixture.context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (error_type, number) = (bootstrap.error_type, bootstrap.number_type);
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let result = demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session,
            )
            .unwrap();
            assert_ne!(result, error_type);
            assert!(store.set_type_reference_resolution(result, None, Some(vec![number])));
            let before = (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
            );
            let mark = session.limit_event_mark();
            let rejected = demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session,
            );
            assert!(rejected.is_err(), "{annotation}: {rejected:?}");
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before
            );
            assert!(!session.limit_event_occurred_since(mark));
        }
    }

    #[test]
    fn property_recovery_requires_the_callers_array_targets_before_writes() {
        let parsed = property_recovery_source("first: Array<T>;");
        let foreign = property_recovery_fixture(&parsed, FileId::new(6_287));
        for targets in [None, Some(foreign.array_targets)] {
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_288));
            let store = fixture.context.store_mut_for_test();
            let error_type = store.intrinsic_bootstrap().unwrap().error_type;
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let links = store.value_symbol_links(fixture.proxy).cloned().unwrap();
            let before = (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
            );
            let mark = session.limit_event_mark();
            assert!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    targets,
                    &mut session
                )
                .is_err()
            );
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before
            );
            assert_eq!(store.value_symbol_links(fixture.proxy), Some(&links));
            assert!(
                store
                    .instantiated_property_recovery(fixture.proxy)
                    .is_none()
            );
            assert_eq!((session.query_count(), session.total_count()), (0, 0));
            assert!(!session.limit_event_occurred_since(mark));
        }
    }

    #[test]
    fn property_recovery_keeps_method_signature_results_on_warm_reads() {
        let parsed = property_recovery_source("first(value: T): T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_286));
        let store = fixture.context.store_mut_for_test();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error_type,
        )
        .unwrap();
        let result = demand_instantiated_property_type(
            store,
            fixture.reference,
            fixture.proxy,
            Some(fixture.array_targets),
            &mut session,
        )
        .unwrap();
        let before = property_recovery_store_counts(store);
        let mark = session.limit_event_mark();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(result)
        );
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(store, result),
            StoredCallableSetValidation::Valid { .. }
        ));
        assert_eq!(property_recovery_store_counts(store), before);
        assert!(!session.limit_event_occurred_since(mark));
    }

    fn recover_first_method(
        fixture: &mut PropertyRecoveryFixture<'_>,
    ) -> (TypeId, InstantiationSession) {
        let store = fixture.context.store_mut_for_test();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error_type,
        )
        .unwrap();
        let mark = session.limit_event_mark();
        let result = demand_instantiated_property_type(
            store,
            fixture.reference,
            fixture.proxy,
            Some(fixture.array_targets),
            &mut session,
        )
        .unwrap();
        assert!(session.limit_event_occurred_since(mark));
        assert_eq!(
            store
                .value_symbol_links(fixture.proxy)
                .unwrap()
                .resolved_type,
            Some(result)
        );
        (result, session)
    }

    #[test]
    fn property_recovery_method_callables_keep_wrappers_generics_and_overloads() {
        use crate::semantic::callable_sets::validate_stored_callable_set;
        for member in [
            "first(value: Array<T>): readonly [T];",
            "first(...values: T[]): [T];",
            "first<U extends T = T>(value: U): [T, U];",
            "first(): T; first(value: T): T;",
        ] {
            eprintln!("recovered method: {member}");
            let parsed = property_recovery_source(member);
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_291));
            let (result, mut session) = recover_first_method(&mut fixture);
            let store = fixture.context.store_mut_for_test();
            let first = validate_stored_callable_set(store, result);
            assert!(
                matches!(first, StoredCallableSetValidation::Valid { .. }),
                "{member}: {first:?}"
            );
            let source_links = store.value_symbol_links(fixture.target).cloned().unwrap();
            let before = (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
            );
            session.reset_query();
            let mark = session.limit_event_mark();
            for _ in 0..2 {
                assert_eq!(
                    demand_instantiated_property_type(
                        store,
                        fixture.reference,
                        fixture.proxy,
                        Some(fixture.array_targets),
                        &mut session
                    ),
                    Ok(result),
                    "{member}",
                );
                assert_eq!(validate_stored_callable_set(store, result), first);
            }
            let mut other = InstantiationSession::new(InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            });
            let other_mark = other.limit_event_mark();
            assert_eq!(
                demand_instantiated_property_type(
                    store,
                    fixture.reference,
                    fixture.proxy,
                    Some(fixture.array_targets),
                    &mut other
                ),
                Ok(result),
            );
            assert_eq!((session.query_count(), session.total_count()), (0, 0));
            assert_eq!((other.query_count(), other.total_count()), (0, 0));
            assert!(!session.limit_event_occurred_since(mark));
            assert!(!other.limit_event_occurred_since(other_mark));
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before
            );
            assert_eq!(
                store.value_symbol_links(fixture.target),
                Some(&source_links)
            );
        }
    }

    #[test]
    fn property_recovery_method_graph_keeps_recursive_receiver_visits_local() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Box<T> { first(value: T): T; second: T; } ",
            "interface Derived extends Box<Derived> {}",
        ));
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_295));
        let (result, mut session) = recover_first_method(&mut fixture);
        let store = fixture.context.store_mut_for_test();
        let before = property_recovery_store_counts(store);
        let mark = session.limit_event_mark();
        assert_eq!(
            store
                .validate_cached_array_capability_with_array_targets(fixture.array_targets, result),
            Ok(())
        );
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(result)
        );
        assert_eq!(property_recovery_store_counts(store), before);
        assert!(!session.limit_event_occurred_since(mark));
    }

    #[test]
    fn property_recovery_callable_reader_rejects_changed_proof_and_result() {
        use crate::semantic::callable_sets::validate_stored_callable_set;
        for mutation in [
            "proxy",
            "target",
            "parameter",
            "source_parameter",
            "normal_values",
            "mapper",
            "symbol",
            "signatures",
            "minimum",
            "source_result",
            "type_parameter",
        ] {
            let member = if mutation == "type_parameter" {
                "first<U = T>(value: U): T;"
            } else {
                "first(value: T): T;"
            };
            let parsed = property_recovery_source(member);
            let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_292));
            let (result, session) = recover_first_method(&mut fixture);
            let store = fixture.context.store_mut_for_test();
            assert!(matches!(
                validate_stored_callable_set(store, result),
                StoredCallableSetValidation::Valid { .. }
            ));
            let signature = store
                .type_payload(result)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_ref()
                .unwrap()[0];
            let original = store.signature(signature).unwrap().target().unwrap();
            let parameter = store.signature(signature).unwrap().parameters()[0];
            let source_parameter = store.signature(original).unwrap().parameters()[0];
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            match mutation {
                "proxy" | "target" | "parameter" | "source_parameter" => {
                    let symbol = match mutation {
                        "proxy" => fixture.proxy,
                        "target" => fixture.target,
                        "parameter" => parameter,
                        "source_parameter" => source_parameter,
                        _ => unreachable!(),
                    };
                    let links = store.value_symbol_links(symbol).cloned().unwrap();
                    assert!(store.set_value_symbol_links(symbol, links));
                }
                "normal_values" => {
                    let links = store.value_symbol_links(parameter).cloned().unwrap();
                    assert!(store.set_value_symbol_links(
                        parameter,
                        ValueSymbolLinks {
                            resolved_type: Some(number),
                            ..links
                        }
                    ));
                    assert!(store.set_signature_resolved_return_type(signature, Some(number)));
                }
                "mapper" => {
                    let TypeData::Interface(interface) =
                        store.type_payload(fixture.members.target()).unwrap().data()
                    else {
                        panic!("the method owner must retain its generic interface")
                    };
                    let sources = interface.all_type_parameters.clone().unwrap();
                    let mut targets = validate_direct_generic_reference(store, fixture.reference)
                        .unwrap()
                        .type_arguments;
                    targets.push(fixture.reference);
                    let mapper = store.new_type_mapper(sources, targets).unwrap();
                    assert_ne!(mapper, fixture.mapper);
                    assert!(store.set_object_target_and_mapper(
                        result,
                        Some(fixture.template),
                        Some(mapper)
                    ));
                }
                "symbol" => assert!(store.set_type_symbol(result, Some(fixture.sibling))),
                "signatures" => assert!(store.set_structured_type_members(
                    result,
                    None,
                    None,
                    Some(vec![original]),
                    None,
                    None
                )),
                "minimum" => {
                    assert!(store.set_signature_resolved_min_argument_count(signature, 99));
                }
                "source_result" => {
                    let string = store.intrinsic_bootstrap().unwrap().string_type;
                    let declaration = store.signature(original).unwrap().declaration().unwrap();
                    let annotation = store.source_direct_type_annotation(declaration).unwrap();
                    assert!(store.set_signature_resolved_return_type(original, Some(string)));
                    assert!(store.set_type_node_links(
                        annotation,
                        TypeNodeLinks {
                            resolved_type: Some(string),
                            ..TypeNodeLinks::default()
                        }
                    ));
                }
                "type_parameter" => {
                    let type_ = store.signature(signature).unwrap().type_parameters()[0];
                    let TypeData::TypeParameter(parameter) =
                        store.type_payload(type_).unwrap().data()
                    else {
                        panic!("the copied method must retain its type parameter")
                    };
                    let (constraint, target, mapper) =
                        (parameter.constraint, parameter.target, parameter.mapper);
                    assert!(store.set_type_parameter_resolution(
                        type_,
                        constraint,
                        target,
                        mapper,
                        Some(number)
                    ));
                }
                _ => unreachable!(),
            }
            let before = (
                property_recovery_store_counts(store),
                store.relation_state_snapshot(),
            );
            let mark = session.limit_event_mark();
            assert!(
                matches!(
                    validate_stored_callable_set(store, result),
                    StoredCallableSetValidation::Malformed {
                        family: CallableFamily::DeclaredCallSignatures
                    }
                ),
                "{mutation}"
            );
            assert_eq!(
                (
                    property_recovery_store_counts(store),
                    store.relation_state_snapshot()
                ),
                before,
                "{mutation}"
            );
            assert!(!session.limit_event_occurred_since(mark));
        }
    }

    #[test]
    fn property_recovery_callable_proof_cannot_move_to_another_result_or_proxy() {
        use crate::semantic::callable_sets::validate_stored_callable_set;
        let parsed = property_recovery_source("first(value: T): T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_293));
        let (result, mut session) = recover_first_method(&mut fixture);
        let store = fixture.context.store_mut_for_test();
        let signatures = store
            .type_payload(result)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .clone()
            .unwrap();
        let copy = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(fixture.target))
            .unwrap();
        assert!(store.set_object_target_and_mapper(
            copy,
            Some(fixture.template),
            Some(fixture.mapper)
        ));
        assert!(store.set_structured_type_members(copy, None, None, Some(signatures), None, None));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let other = store
            .create_direct_generic_reference_type(fixture.members.target(), &[string])
            .unwrap();
        let other_members =
            resolve_members_with_array_targets(store, other, Some(fixture.array_targets)).unwrap();
        let proxy = store
            .symbol_table(other_members.members().unwrap())
            .unwrap()
            .get_source("first")
            .unwrap();
        let links = store.value_symbol_links(proxy).cloned().unwrap();
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: Some(result),
                ..links
            }
        ));
        let before = property_recovery_store_counts(store);
        let mark = session.limit_event_mark();
        assert!(matches!(
            validate_stored_callable_set(store, copy),
            StoredCallableSetValidation::Malformed { .. }
        ));
        assert!(
            demand_instantiated_property_type(
                store,
                other,
                proxy,
                Some(fixture.array_targets),
                &mut session
            )
            .is_err()
        );
        assert!(matches!(
            validate_stored_callable_set(store, result),
            StoredCallableSetValidation::Valid { .. }
        ));
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Ok(result)
        );
        assert_eq!(property_recovery_store_counts(store), before);
        assert!(!session.limit_event_occurred_since(mark));
    }

    #[test]
    fn property_recovery_rejects_bad_method_source_before_instantiation() {
        let parsed = property_recovery_source("first(value: T): number;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_294));
        let store = fixture.context.store_mut_for_test();
        let signature = store
            .type_payload(fixture.template)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let declaration = store.signature(signature).unwrap().declaration().unwrap();
        let annotation = store.source_direct_type_annotation(declaration).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, error_type) = (bootstrap.string_type, bootstrap.error_type);
        assert!(store.set_signature_resolved_return_type(signature, Some(string)));
        assert!(store.set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            }
        ));
        let links = store.value_symbol_links(fixture.proxy).cloned().unwrap();
        let before = (
            property_recovery_store_counts(store),
            store.relation_state_snapshot(),
        );
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error_type,
        )
        .unwrap();
        let mark = session.limit_event_mark();
        assert!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            )
            .is_err()
        );
        assert_eq!(store.value_symbol_links(fixture.proxy), Some(&links));
        assert_eq!(
            (
                property_recovery_store_counts(store),
                store.relation_state_snapshot()
            ),
            before
        );
        assert_eq!((session.query_count(), session.total_count()), (0, 0));
        assert!(!session.limit_event_occurred_since(mark));
    }

    #[test]
    fn property_recovery_rejects_changed_method_signature_results() {
        let parsed = property_recovery_source("first(value: T): T;");
        let mut fixture = property_recovery_fixture(&parsed, FileId::new(6_289));
        let store = fixture.context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (error_type, number) = (bootstrap.error_type, bootstrap.number_type);
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            error_type,
        )
        .unwrap();
        let result = demand_instantiated_property_type(
            store,
            fixture.reference,
            fixture.proxy,
            Some(fixture.array_targets),
            &mut session,
        )
        .unwrap();
        let signature = store
            .type_payload(result)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let parameter = store.signature(signature).unwrap().parameters()[0];
        let links = store.value_symbol_links(parameter).cloned().unwrap();
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..links
            }
        ));
        assert!(store.set_signature_resolved_return_type(signature, Some(number)));
        assert!(cached_instantiated_interface_method_type_matches(
            store,
            fixture.template,
            result,
            fixture.mapper,
            Some(fixture.array_targets)
        ));
        let before = property_recovery_store_counts(store);
        let mark = session.limit_event_mark();
        assert_eq!(
            demand_instantiated_property_type(
                store,
                fixture.reference,
                fixture.proxy,
                Some(fixture.array_targets),
                &mut session
            ),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(
                fixture.proxy
            ))
        );
        assert_eq!(property_recovery_store_counts(store), before);
        assert!(!session.limit_event_occurred_since(mark));
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
    #[allow(clippy::too_many_lines)] // Check source order, union origins, and warm callback identity together.
    fn array_callback_mapping_preserves_constructor_union_order_and_origin() {
        let library = parse_source_file(concat!(
            "interface Array<T> { ",
            "map<U>(callbackfn: (value: T, index: number, array: T[]) => U, ",
            "thisArg?: any): U[]; } interface ReadonlyArray<T> {}",
        ));
        let source = parse_source_file(concat!(
            "class Zebra { z: string; } ",
            "abstract class Alpha { a: string; } ",
            "abstract class Middle { m: string; } ",
            "type Pair = typeof Alpha | typeof Middle; ",
            "declare const grouped: (typeof Zebra | Pair)[]; ",
            "const first = [Zebra, Alpha, Middle].map; ",
            "const second = [Middle, Zebra, Alpha].map; ",
            "const named = grouped.map;",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(6_264);
        let file = FileId::new(6_265);
        let files = [(library_file, &library), (file, &source)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            let is_library = file == library_file;
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!(
                            "\"/project/array-union-{}.ts\"",
                            file.index()
                        )),
                        CanonicalSourceLanguage::TypeScript,
                        is_library,
                        is_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let globals = context.global_types().clone();
        let declarations = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        let instances = declarations
            .into_iter()
            .map(|declaration| context.get_type_at_location(declaration).unwrap())
            .collect::<Vec<_>>();
        let instances = context
            .store_mut_for_test()
            .expression_union_type_with_global_types(&globals, &instances, UnionReduction::Literal)
            .unwrap();
        let TypeData::Union(instances) = context.store().type_payload(instances).unwrap().data()
        else {
            panic!("the named instance union must retain its members")
        };
        assert_eq!(
            instances
                .union
                .types
                .iter()
                .map(|type_| {
                    context
                        .store()
                        .type_payload(*type_)
                        .and_then(super::super::type_records::TypeRecord::symbol)
                        .and_then(|symbol| context.store().symbol(symbol))
                        .and_then(|symbol| symbol.name().as_utf8())
                })
                .collect::<Vec<_>>(),
            [Some("Alpha"), Some("Middle"), Some("Zebra")],
        );
        let accesses = source
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(source.arena.id(), file, node),
                    NodeRef::new(source.arena.id(), file, access.expression),
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(accesses.len(), 3);
        let mut mapped = Vec::new();
        for (index, (access, receiver)) in accesses.into_iter().enumerate() {
            let receiver = context.get_type_at_location(receiver).unwrap();
            let callable = context.get_type_at_location(access).unwrap();
            let array = context
                .store()
                .canonical_array_reference(&globals, receiver)
                .unwrap()
                .unwrap();
            let element = array.element_type;
            let TypeData::Union(union) = context.store().type_payload(element).unwrap().data()
            else {
                panic!("the receiver must retain its constructor union")
            };
            assert_eq!(union.origin.is_some(), index == 2);
            let record = context.store().type_payload(callable).unwrap();
            let method = record.symbol().unwrap();
            let [signature] = record
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_deref()
                .unwrap()
            else {
                panic!("map must retain one specialized signature")
            };
            let parameter = context.store().signature(*signature).unwrap().parameters()[0];
            let callback = context
                .store()
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let [signature] = context
                .store()
                .type_payload(callback)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_deref()
                .unwrap()
            else {
                panic!("the callback must retain one signature")
            };
            let parameters = context
                .store()
                .signature(*signature)
                .unwrap()
                .parameters()
                .iter()
                .map(|parameter| {
                    context
                        .store()
                        .value_symbol_links(*parameter)
                        .and_then(|links| links.resolved_type)
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert_eq!(parameters[0], element);
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(&globals, parameters[2])
                    .unwrap(),
                Some(element),
            );
            let expected = if index == 2 {
                "typeof Zebra | Pair"
            } else {
                "typeof Zebra | typeof Alpha | typeof Middle"
            };
            assert_eq!(context.type_to_string(element).unwrap(), expected);
            let warm = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                instantiate_published_generic_interface_method(
                    context.store_mut_for_test(),
                    &globals,
                    receiver,
                    method,
                )
                .unwrap(),
                callable,
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
            mapped.push(callable);
        }
        assert_eq!(mapped[0], mapped[1]);
    }

    struct ArrayMethodPreflightFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        method: SemanticSymbolId,
        receiver: TypeId,
        parameter: TypeId,
        signature: SignatureId,
    }

    fn array_method_preflight_fixture(
        parsed: &ParseResult,
        file: FileId,
    ) -> ArrayMethodPreflightFixture<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(parsed, file, CanonicalCheckerOptions::default());
        let globals = context.global_types().clone();
        let owner = source_symbol(parsed, file, &context, "Array");
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("f"))
            .unwrap();
        let declaration = context
            .store()
            .symbol(method)
            .unwrap()
            .value_declaration()
            .unwrap();
        let NodeData::MethodSignatureDeclaration(method_data) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected the generic Array method")
        };
        let annotation = NodeRef::new(parsed.arena.id(), file, method_data.type_.unwrap());
        let parameter = context.get_type_from_type_node(annotation).unwrap();
        let parameter_declaration =
            NodeRef::new(parsed.arena.id(), file, method_data.parameters.nodes[0]);
        let parameter_symbol = context
            .file(file)
            .unwrap()
            .1
            .symbol(parameter_declaration)
            .unwrap();
        let store = context.store_mut_for_test();
        assert!(store.set_value_symbol_links(
            parameter_symbol,
            ValueSymbolLinks {
                resolved_type: Some(parameter),
                ..ValueSymbolLinks::default()
            },
        ));
        let source = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration),
                vec![parameter],
                None,
                vec![parameter_symbol],
                Some(parameter),
                None,
                1,
            )
            .unwrap();
        assert!(store.set_signature_links(
            declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
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
            Some(vec![signature]),
            None,
            None,
        ));
        assert!(store.set_function_signature_return_annotation(signature, annotation, false));
        assert!(
            store.set_callable_signature_parameter_types_batch(vec![(signature, vec![parameter])])
        );
        assert_eq!(store.interface_method_linked_type(signature), Some(source));
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let receiver = store
            .create_canonical_array_type(&globals, number, false)
            .unwrap();
        ArrayMethodPreflightFixture {
            context,
            method,
            receiver,
            parameter,
            signature,
        }
    }

    #[test]
    fn array_method_preflight_rejects_function_constraints_and_defaults_before_writes() {
        for (index, method) in [
            "f<U extends (value: T) => T>(value: U): U;",
            "f<U extends ((value: T) => T)[]>(value: U): U;",
            "f<U = (value: T) => T>(value: U): U;",
            "f<U = ((value: T) => T)[]>(value: U): U;",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{ {method} }} interface ReadonlyArray<T> {{}}",
            ));
            let file = FileId::new(6_250 + u32::try_from(index).unwrap());
            let mut fixture = array_method_preflight_fixture(&parsed, file);
            let globals = fixture.context.global_types().clone();
            let TypeData::TypeParameter(parameter) = fixture
                .context
                .store()
                .type_payload(fixture.parameter)
                .unwrap()
                .data()
            else {
                panic!("expected the original generic parameter")
            };
            let unsupported = parameter
                .constraint
                .or(parameter.resolved_default_type)
                .unwrap();
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.signature_len(),
                        store.symbol_len(),
                        store.symbol_store().symbol_table_len(),
                        store.checker_link_allocated_lengths(),
                    ),
                    parsed
                        .arena
                        .iter()
                        .map(|(node, _)| {
                            let node = NodeRef::new(parsed.arena.id(), file, node);
                            let symbol = context.file(file).unwrap().1.symbol(node);
                            (
                                store.type_node_links(node).cloned(),
                                store.signature_links(node).cloned(),
                                symbol
                                    .and_then(|symbol| store.value_symbol_links(symbol))
                                    .cloned(),
                                symbol
                                    .and_then(|symbol| store.declared_type_links(symbol))
                                    .cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            };
            let before = snapshot(&fixture.context);
            for _ in 0..2 {
                assert_eq!(
                    instantiate_published_generic_interface_method(
                        fixture.context.store_mut_for_test(),
                        &globals,
                        fixture.receiver,
                        fixture.method,
                    ),
                    Err(GenericInterfaceMemberError::UnsupportedPropertyType(
                        unsupported
                    )),
                    "{method}",
                );
                assert_eq!(snapshot(&fixture.context), before, "{method}");
            }
        }
    }

    #[test]
    fn array_method_preflight_keeps_supported_constraints_and_defaults() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> { f<U extends T = T>(value: U): U; } ",
            "interface ReadonlyArray<T> {}",
        ));
        let mut fixture = array_method_preflight_fixture(&parsed, FileId::new(6_254));
        let globals = fixture.context.global_types().clone();
        let store = fixture.context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let source_links = store.value_symbol_links(fixture.method).cloned();
        let callable = instantiate_published_generic_interface_method(
            store,
            &globals,
            fixture.receiver,
            fixture.method,
        )
        .unwrap();
        let [signature] = store
            .type_payload(callable)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_deref()
            .unwrap()
        else {
            panic!("expected one mapped method signature")
        };
        let signature = store.signature(*signature).unwrap();
        assert_eq!(signature.target(), Some(fixture.signature));
        let [fresh] = signature.type_parameters() else {
            panic!("expected one fresh generic parameter")
        };
        assert_ne!(*fresh, fixture.parameter);
        let TypeData::TypeParameter(parameter) = store.type_payload(*fresh).unwrap().data() else {
            panic!("expected a mapped generic parameter")
        };
        assert_eq!(parameter.constraint, Some(number));
        assert_eq!(parameter.resolved_default_type, Some(number));
        assert_eq!(parameter.target, Some(fixture.parameter));
        assert_eq!(parameter.mapper, signature.mapper());
        assert_eq!(
            store.value_symbol_links(fixture.method),
            source_links.as_ref()
        );
        let warm = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(
                store,
                &globals,
                fixture.receiver,
                fixture.method
            ),
            Ok(callable),
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

    const NESTED_TUPLE_HOLDER_MEMBERS: [(&str, bool); 3] = [
        ("item: [Child<T>];", false),
        ("item: [[Child<T>]];", false),
        ("item: [T]; [name: string]: [T] | [Child<T>];", true),
    ];

    struct NestedTupleTargetFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        reference: TypeId,
        child_reference: TypeId,
        child_value: SemanticSymbolId,
        template: TypeId,
    }

    fn nested_tuple_target_fixture(
        parsed: &ParseResult,
        file: FileId,
        index: bool,
    ) -> NestedTupleTargetFixture<'_> {
        assert!(parsed.diagnostics.is_empty());
        let mut context = checker_context(parsed, file, CanonicalCheckerOptions::default());
        let child = source_symbol(parsed, file, &context, "Child");
        let holder = source_symbol(parsed, file, &context, "Holder");
        let child_target = context.get_declared_type_of_symbol(child).unwrap();
        let target = context.get_declared_type_of_symbol(holder).unwrap();
        let TypeData::Interface(child_interface) =
            context.store().type_payload(child_target).unwrap().data()
        else {
            panic!("Child must retain its generic interface target")
        };
        let child_parameter = child_interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .unwrap()[0];
        publish_generic_target_for_test(
            &mut context,
            child_target,
            &[("value", child_parameter)],
            None,
        );
        let child_value = context
            .store()
            .symbol(child)
            .unwrap()
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let item = context
            .store()
            .symbol(holder)
            .unwrap()
            .members()
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("item"))
            .unwrap();
        let item_annotation = context
            .store()
            .source_direct_type_annotation(
                context
                    .store()
                    .symbol(item)
                    .unwrap()
                    .value_declaration()
                    .unwrap(),
            )
            .unwrap();
        let item_type = context.get_type_from_type_node(item_annotation).unwrap();
        let index_declaration = index.then(|| {
            context
                .store()
                .symbol(holder)
                .unwrap()
                .members()
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                .and_then(|symbol| context.store().symbol(symbol))
                .and_then(|symbol| symbol.declarations())
                .unwrap()[0]
        });
        let index_type = index_declaration.map(|declaration| {
            let annotation = context
                .store()
                .source_direct_type_annotation(declaration)
                .unwrap();
            context.get_type_from_type_node(annotation).unwrap()
        });
        publish_generic_target_for_test(&mut context, target, &[("item", item_type)], None);
        let store = context.store_mut_for_test();
        if let Some((declaration, value)) = index_declaration.zip(index_type) {
            let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
                panic!("Holder must retain its generic interface target")
            };
            let members = interface.declared_members;
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            let info = store
                .alloc_index_info(string, value, false, Some(declaration), Vec::new())
                .unwrap();
            assert!(store.set_interface_declared_members(
                target,
                true,
                members,
                None,
                None,
                Some(vec![info])
            ));
        }
        let template = index_type.unwrap_or(item_type);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let reference = store
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();
        let child_reference = store
            .create_direct_generic_reference_type(child_target, &[string])
            .unwrap();
        NestedTupleTargetFixture {
            context,
            reference,
            child_reference,
            child_value,
            template,
        }
    }

    fn read_nested_tuple_holder_value(
        store: &mut CanonicalTypeMapperStore,
        reference: TypeId,
        index: bool,
    ) -> Result<TypeId, GenericInterfaceMemberError> {
        if index {
            store.resolve_generic_interface_members(reference, None)?;
            let index = store
                .type_payload(reference)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .index_infos
                .as_ref()
                .unwrap()[0];
            Ok(store.index_info(index).unwrap().value_type())
        } else {
            Ok(store
                .resolve_generic_interface_property(reference, "item", None)?
                .unwrap()
                .type_id())
        }
    }

    #[test]
    fn nested_tuple_targets_keep_cold_and_warm_property_and_index_identity() {
        for (members, index) in NESTED_TUPLE_HOLDER_MEMBERS {
            let parsed = parse_source_file(&format!(
                "interface Child<T> {{ value: T; }} interface Holder<T> {{ {members} }}",
            ));
            let mut fixture = nested_tuple_target_fixture(&parsed, FileId::new(6_273), index);
            let store = fixture.context.store_mut_for_test();
            assert_eq!(
                store
                    .type_payload(fixture.reference)
                    .unwrap()
                    .data()
                    .structured(),
                Some(&StructuredTypeData::default())
            );
            let value = read_nested_tuple_holder_value(store, fixture.reference, index).unwrap();
            let resolved = store
                .resolve_generic_interface_members(fixture.reference, None)
                .unwrap();
            assert_eq!(
                instantiated_tuple_member_type_matches(
                    store,
                    fixture.template,
                    value,
                    resolved.mapper().unwrap(),
                    None
                ),
                Some(true),
                "{members}",
            );
            let before = (
                store.type_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                read_nested_tuple_holder_value(store, fixture.reference, index),
                Ok(value)
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
                "{members}"
            );
        }
    }

    #[test]
    fn nested_tuple_targets_reject_poisoned_children_before_cold_or_warm_writes() {
        for (members, index) in NESTED_TUPLE_HOLDER_MEMBERS {
            for warm in [false, true] {
                let parsed = parse_source_file(&format!(
                    "interface Child<T> {{ value: T; }} interface Holder<T> {{ {members} }}",
                ));
                let mut fixture = nested_tuple_target_fixture(&parsed, FileId::new(6_274), index);
                let store = fixture.context.store_mut_for_test();
                let cached = warm.then(|| {
                    read_nested_tuple_holder_value(store, fixture.reference, index).unwrap()
                });
                let original = store
                    .value_symbol_links(fixture.child_value)
                    .cloned()
                    .unwrap();
                assert!(
                    store.set_value_symbol_links(fixture.child_value, ValueSymbolLinks::default())
                );
                let snapshot = |store: &CanonicalTypeMapperStore| {
                    (
                        store.type_len(),
                        store.mapper_len(),
                        store.index_info_len(),
                        store.symbol_len(),
                        store.checker_link_allocated_lengths(),
                        store
                            .type_payload(fixture.reference)
                            .unwrap()
                            .data()
                            .structured()
                            .cloned(),
                        store
                            .type_payload(fixture.child_reference)
                            .unwrap()
                            .data()
                            .structured()
                            .cloned(),
                    )
                };
                let before = snapshot(store);
                let expected = GenericInterfaceMemberError::InvalidMember(fixture.child_value);
                assert_eq!(
                    read_nested_tuple_holder_value(store, fixture.reference, index),
                    Err(expected.clone()),
                    "{members}, warm={warm}",
                );
                assert_eq!(
                    store.resolve_generic_interface_property(
                        fixture.child_reference,
                        "value",
                        None
                    ),
                    Err(expected),
                    "{members}, warm={warm}",
                );
                assert_eq!(snapshot(store), before, "{members}, warm={warm}");
                assert_eq!(
                    store.value_symbol_links(fixture.child_value),
                    Some(&ValueSymbolLinks::default())
                );
                assert!(store.set_value_symbol_links(fixture.child_value, original));
                let restored =
                    read_nested_tuple_holder_value(store, fixture.reference, index).unwrap();
                if let Some(cached) = cached {
                    assert_eq!(restored, cached, "{members}");
                }
                assert_eq!(
                    read_nested_tuple_holder_value(store, fixture.reference, index),
                    Ok(restored)
                );
            }
        }
    }

    #[test]
    fn generic_method_tuple_union_keeps_empty_arm_and_inherited_mapper() {
        let parsed = parse_source_file(concat!(
            "interface Iterator<T, TReturn, TNext> { next(...args: [] | [TNext]): T; } ",
            "interface Derived extends Iterator<number, void, string> {}",
        ));
        let file = FileId::new(6_270);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let derived = source_symbol(&parsed, file, &context, "Derived");
        let iterator = source_symbol(&parsed, file, &context, "Iterator");
        let target = context.get_declared_type_of_symbol(derived).unwrap();
        let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("Derived must retain its interface target")
        };
        let base = interface.resolved_base_types.as_ref().unwrap()[0];
        let store = context.store_mut_for_test();
        let method = store
            .symbol(iterator)
            .unwrap()
            .members()
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("next"))
            .unwrap();
        let source = store
            .value_symbol_links(method)
            .unwrap()
            .resolved_type
            .unwrap();
        let original_signature = store
            .type_payload(source)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let original_parameter = store.signature(original_signature).unwrap().parameters()[0];
        let template = store
            .value_symbol_links(original_parameter)
            .unwrap()
            .resolved_type
            .unwrap();
        let template_arms = method_tuple_union_members(store, template)
            .unwrap()
            .unwrap()
            .to_vec();
        let original_nonempty = template_arms
            .iter()
            .copied()
            .find(|arm| {
                !store
                    .canonical_tuple_shape(*arm)
                    .unwrap()
                    .unwrap()
                    .element_types()
                    .is_empty()
            })
            .unwrap();
        let next_parameter = store
            .canonical_tuple_shape(original_nonempty)
            .unwrap()
            .unwrap()
            .element_types()[0];
        let next = store
            .resolve_generic_interface_property(base, "next", None)
            .unwrap()
            .unwrap();
        let method_links = store.value_symbol_links(next.symbol()).unwrap();
        assert_eq!(method_links.target, Some(method));
        let mapper = method_links.mapper.unwrap();
        let signature = store
            .type_payload(next.type_id())
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let signature = store.signature(signature).unwrap();
        assert_eq!(signature.target(), Some(original_signature));
        assert_eq!(signature.mapper(), Some(mapper));
        assert!(signature.has_rest_parameter());
        let parameter = store.value_symbol_links(signature.parameters()[0]).unwrap();
        assert_eq!(parameter.target, Some(original_parameter));
        assert_eq!(parameter.mapper, Some(mapper));
        let actual = parameter.resolved_type.unwrap();
        let arms = method_tuple_union_members(store, actual).unwrap().unwrap();
        assert_eq!(arms.len(), 2);
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(store.map_type(mapper, next_parameter), Some(string));
        let empty = arms
            .iter()
            .copied()
            .find(|arm| {
                store
                    .canonical_tuple_shape(*arm)
                    .unwrap()
                    .unwrap()
                    .element_types()
                    .is_empty()
            })
            .unwrap();
        assert!(template_arms.contains(&empty));
        let nonempty = arms.iter().copied().find(|arm| *arm != empty).unwrap();
        assert_eq!(
            store
                .canonical_tuple_shape(nonempty)
                .unwrap()
                .unwrap()
                .element_types(),
            &[string]
        );
        assert_eq!(
            store
                .value_symbol_links(original_parameter)
                .unwrap()
                .resolved_type,
            Some(template)
        );
        assert_eq!(
            store
                .canonical_tuple_shape(original_nonempty)
                .unwrap()
                .unwrap()
                .element_types(),
            &[next_parameter]
        );
        assert!(instantiated_method_type_matches(
            store, template, actual, mapper, None
        ));
        assert!(!instantiated_method_type_matches(
            store, template, nonempty, mapper, None
        ));
        assert!(!instantiated_method_type_matches(
            store, template, string, mapper, None
        ));
        assert!(matches!(
            super::super::callable_sets::validate_stored_callable_set(store, next.type_id()),
            StoredCallableSetValidation::Valid { .. }
        ));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            store.resolve_generic_interface_property(base, "next", None),
            Ok(Some(next))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );

        let unregistered = store
            .alloc_union_type(ObjectFlags::NONE, template_arms)
            .unwrap();
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            member_type_requires_instantiation(store, unregistered, &[next_parameter], None),
            Err(GenericInterfaceMemberError::UnsupportedPropertyType(
                unregistered
            )),
        );
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            instantiate_generic_member_type(store, unregistered, mapper, None, &mut session),
            Err(GenericInterfaceMemberError::UnsupportedPropertyType(
                unregistered
            )),
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
    }

    #[test]
    fn generic_method_tuple_reference_result_keeps_unread_members_cold() {
        let parsed = parse_source_file(concat!(
            "interface Result<T> { value: T; } ",
            "interface Base<T> { read(...args: [] | [T]): Result<T>; } ",
            "interface Derived extends Base<string> {}",
        ));
        let file = FileId::new(6_272);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let derived = source_symbol(&parsed, file, &context, "Derived");
        let result = source_symbol(&parsed, file, &context, "Result");
        let target = context.get_declared_type_of_symbol(derived).unwrap();
        let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("Derived must retain its interface target")
        };
        let base = interface.resolved_base_types.as_ref().unwrap()[0];
        let store = context.store_mut_for_test();
        let result_target = store
            .declared_type_links(result)
            .unwrap()
            .declared_type
            .unwrap();
        let method = store
            .resolve_generic_interface_property(base, "read", None)
            .unwrap()
            .unwrap();
        let signature = store
            .type_payload(method.type_id())
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let return_type = store
            .signature(signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let reference = validate_direct_generic_reference(store, return_type).unwrap();
        assert_eq!(reference.target, result_target);
        assert_eq!(
            reference.type_arguments,
            [store.intrinsic_bootstrap().unwrap().string_type]
        );
        let TypeData::Interface(interface) = store.type_payload(result_target).unwrap().data()
        else {
            panic!("Result must retain its generic interface target")
        };
        assert!(!interface.declared_members_resolved);
        assert!(!interface.base_types_resolved);
        assert_eq!(
            interface.reference.object.structured,
            StructuredTypeData::default()
        );
        assert!(matches!(
            super::super::callable_sets::validate_stored_callable_set(store, method.type_id()),
            StoredCallableSetValidation::Valid { .. }
        ));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            store.resolve_generic_interface_property(base, "read", None),
            Ok(Some(method))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
    }

    #[test]
    fn generic_method_tuple_result_keeps_labels_readonly_and_optional_elements() {
        let parsed =
            parse_source_file("interface Box<T> { read(): readonly [head: T, tail?: T]; }");
        let file = FileId::new(6_271);
        let mut context = checker_context(
            &parsed,
            file,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        context.check_source_file(file).unwrap();
        let owner = source_symbol(&parsed, file, &context, "Box");
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let target = store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        let method = store
            .symbol(owner)
            .unwrap()
            .members()
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("read"))
            .unwrap();
        let source = store
            .value_symbol_links(method)
            .unwrap()
            .resolved_type
            .unwrap();
        let original_signature = store
            .type_payload(source)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let template = store
            .signature(original_signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let undefined = store.intrinsic_bootstrap().unwrap().undefined_type;
        let receiver = store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        let callable =
            instantiate_published_generic_interface_method(store, &globals, receiver, method)
                .unwrap();
        let signature = store
            .type_payload(callable)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let signature = store.signature(signature).unwrap();
        let actual = signature.resolved_return_type().unwrap();
        let mapper = signature.mapper().unwrap();
        assert_eq!(signature.target(), Some(original_signature));
        let original = store.canonical_tuple_shape(template).unwrap().unwrap();
        let result_shape = store.canonical_tuple_shape(actual).unwrap().unwrap();
        assert_eq!(result_shape.target(), original.target());
        assert_eq!(result_shape.element_infos(), original.element_infos());
        assert!(result_shape.is_readonly());
        assert_eq!(result_shape.element_types()[0], number);
        let TypeData::Union(optional) = store
            .type_payload(result_shape.element_types()[1])
            .unwrap()
            .data()
        else {
            panic!("the optional tuple element must retain undefined")
        };
        let mut expected = [number, undefined];
        expected.sort_unstable();
        assert_eq!(optional.union.types, expected);
        assert!(instantiated_method_type_matches(
            store, template, actual, mapper, None
        ));
        assert!(matches!(
            super::super::callable_sets::validate_stored_callable_set(store, callable),
            StoredCallableSetValidation::Valid { .. }
        ));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(store, &globals, receiver, method),
            Ok(callable)
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
    }

    struct PublishedComputedMethodFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        target: TypeId,
        receiver: TypeId,
        method: SemanticSymbolId,
        sibling: SemanticSymbolId,
        key_type: TypeId,
        source: TypeId,
        signature: SignatureId,
        parameter: SemanticSymbolId,
        type_parameter: TypeId,
    }

    fn published_computed_method_fixture(
        parsed: &ParseResult,
        file: FileId,
    ) -> PublishedComputedMethodFixture<'_> {
        use crate::semantic::{
            DeclaredTypeHost,
            object_members::{plan_computed_member_key, publish_computed_member_key_links},
            production::GlobalMergeCompletion,
        };

        assert!(parsed.diagnostics.is_empty());
        let mut context = checker_context(parsed, file, CanonicalCheckerOptions::default());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(ts_binder::CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let owner = source_symbol(parsed, file, &context, "Box");
        let target = context
            .store_mut_for_test()
            .get_declared_type_of_symbol(&host, owner)
            .unwrap();
        let (declaration, method_data) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                (parsed.arena.get(method.name)?.kind == SyntaxKind::ComputedPropertyName)
                    .then_some((NodeRef::new(parsed.arena.id(), file, node), method))
            })
            .unwrap();
        let key_plan = plan_computed_member_key(
            context.store(),
            &host,
            NodeRef::new(parsed.arena.id(), file, method_data.name),
        )
        .unwrap();
        context.get_type_from_type_node(key_plan.type_node).unwrap();
        let (key_type, _) =
            publish_computed_member_key_links(context.store_mut_for_test(), &host, &key_plan)
                .unwrap();
        let early = bound.symbol(declaration).unwrap();
        let parameter_node = NodeRef::new(parsed.arena.id(), file, method_data.parameters.nodes[0]);
        let parameter = bound.symbol(parameter_node).unwrap();
        let store = context.store_mut_for_test();
        let raw = store.symbol(owner).unwrap().members().unwrap();
        let sibling = store.symbol_table(raw).unwrap().get_source("cold").unwrap();
        let resolved = store.clone_symbol_table(raw).unwrap();
        let method = store
            .create_late_bound_property_symbol(owner, early, key_type, resolved)
            .unwrap();
        let mut member_links = MembersAndExportsLinks::default();
        member_links.tables[MembersOrExportsResolutionKind::ResolvedMembers as usize] =
            Some(resolved);
        assert!(store.set_members_and_exports_links(owner, member_links));
        let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
            panic!("Box must retain its generic interface target")
        };
        let type_parameter = interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .unwrap()[0];
        let parameter_annotation = store.source_direct_type_annotation(parameter_node).unwrap();
        let return_annotation = store.source_direct_type_annotation(declaration).unwrap();
        for (annotation, type_) in [
            (parameter_annotation, type_parameter),
            (return_annotation, target),
        ] {
            assert!(store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                },
            ));
        }
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(type_parameter),
                ..ValueSymbolLinks::default()
            },
        ));
        let source = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(method))
            .unwrap();
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(declaration),
                Vec::new(),
                None,
                vec![parameter],
                Some(target),
                None,
                1,
            )
            .unwrap();
        assert!(store.set_signature_links(
            declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            source,
            None,
            None,
            Some(vec![signature]),
            None,
            None
        ));
        assert!(store.set_value_symbol_links(
            method,
            ValueSymbolLinks {
                resolved_type: Some(source),
                name_type: Some(key_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_function_signature_return_annotation(
            signature,
            return_annotation,
            false
        ));
        assert!(
            store.set_callable_signature_parameter_types_batch(vec![(
                signature,
                vec![type_parameter]
            )])
        );
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let receiver = store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        PublishedComputedMethodFixture {
            context,
            target,
            receiver,
            method,
            sibling,
            key_type,
            source,
            signature,
            parameter,
            type_parameter,
        }
    }

    #[test]
    fn published_computed_interface_method_maps_its_own_reference_without_siblings() {
        let parsed = parse_source_file(concat!(
            "declare const key: unique symbol; ",
            "interface Box<T> { [key](value: T): Box<T>; cold(): (value: T) => T; }",
        ));
        let mut fixture = published_computed_method_fixture(&parsed, FileId::new(6_260));
        let globals = fixture.context.global_types().clone();
        let store = fixture.context.store_mut_for_test();
        let source_links = store.value_symbol_links(fixture.method).cloned();
        assert_eq!(
            published_method_requires_instantiation(store, &globals, fixture.method),
            Ok(true)
        );
        let callable = instantiate_published_generic_interface_method(
            store,
            &globals,
            fixture.receiver,
            fixture.method,
        )
        .unwrap();
        let record = store.type_payload(callable).unwrap();
        let TypeData::Object(object) = record.data() else {
            panic!("a selected method must retain a callable object")
        };
        assert_eq!(record.symbol(), Some(fixture.method));
        assert_eq!(object.target, Some(fixture.source));
        let signature = object.structured.signatures.as_ref().unwrap()[0];
        let mapped = store.signature(signature).unwrap();
        assert_eq!(mapped.target(), Some(fixture.signature));
        assert_eq!(mapped.resolved_return_type(), Some(fixture.receiver));
        let mapped_parameter = mapped.parameters()[0];
        let parameter_links = store.value_symbol_links(mapped_parameter).unwrap();
        assert_eq!(parameter_links.target, Some(fixture.parameter));
        assert_eq!(
            parameter_links.resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().number_type)
        );
        assert_eq!(
            store.value_symbol_links(fixture.method),
            source_links.as_ref()
        );
        assert_eq!(source_links.unwrap().name_type, Some(fixture.key_type));
        assert_eq!(
            store
                .value_symbol_links(fixture.parameter)
                .unwrap()
                .resolved_type,
            Some(fixture.type_parameter)
        );
        assert_eq!(
            store
                .signature(fixture.signature)
                .unwrap()
                .resolved_return_type(),
            Some(fixture.target)
        );
        assert!(store.value_symbol_links(fixture.sibling).is_none());
        let TypeData::Interface(interface) = store.type_payload(fixture.target).unwrap().data()
        else {
            panic!("the generic interface target must remain intact")
        };
        assert!(!interface.declared_members_resolved);
        assert!(matches!(
            super::super::callable_sets::validate_stored_callable_set(store, callable),
            StoredCallableSetValidation::Valid { .. }
        ));
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let other_receiver = store
            .create_direct_generic_reference_type(fixture.target, &[string])
            .unwrap();
        let other = instantiate_published_generic_interface_method(
            store,
            &globals,
            other_receiver,
            fixture.method,
        )
        .unwrap();
        assert_ne!(other, callable);
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(
                store,
                &globals,
                fixture.receiver,
                fixture.method
            ),
            Ok(callable)
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
    }

    #[test]
    fn published_computed_interface_method_rejects_wrong_keys_and_mapped_cache_identity() {
        let parsed = parse_source_file(concat!(
            "declare const key: unique symbol; declare const other: unique symbol; ",
            "interface Box<T> { [key](value: T): Box<T>; cold(): (value: T) => T; }",
        ));
        let file = FileId::new(6_261);
        let mut fixture = published_computed_method_fixture(&parsed, file);
        let globals = fixture.context.global_types().clone();
        let other = source_symbol(&parsed, file, &fixture.context, "other");
        let store = fixture.context.store_mut_for_test();
        let other_key = store.alloc_unique_es_symbol_type(other).unwrap();
        let links = store.value_symbol_links(fixture.method).cloned().unwrap();
        assert!(store.set_value_symbol_links(
            fixture.method,
            ValueSymbolLinks {
                name_type: Some(other_key),
                ..links.clone()
            }
        ));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(
                store,
                &globals,
                fixture.receiver,
                fixture.method
            ),
            Err(GenericInterfaceMemberError::InvalidMember(fixture.method))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
        assert!(store.set_value_symbol_links(fixture.method, links));
        let callable = instantiate_published_generic_interface_method(
            store,
            &globals,
            fixture.receiver,
            fixture.method,
        )
        .unwrap();
        let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
            panic!("the selected method must retain a callable object")
        };
        let mapper = object.mapper.unwrap();
        let signature = object.structured.signatures.as_ref().unwrap()[0];
        let parameter = store.signature(signature).unwrap().parameters()[0];
        let links = store.value_symbol_links(parameter).cloned().unwrap();
        assert!(store.set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                target: Some(fixture.method),
                ..links.clone()
            }
        ));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(
                store,
                &globals,
                fixture.receiver,
                fixture.method
            ),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(
                parameter
            ))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
        assert!(store.set_value_symbol_links(parameter, links));
        let TypeData::Interface(interface) = store.type_payload(fixture.target).unwrap().data()
        else {
            panic!("Box must retain its generic interface target")
        };
        let this_type = interface.this_type.unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let wrong_mapper = store
            .new_type_mapper(
                vec![fixture.type_parameter, this_type],
                vec![number, fixture.target],
            )
            .unwrap();
        assert!(store.set_object_target_and_mapper(
            callable,
            Some(fixture.source),
            Some(wrong_mapper)
        ));
        let before = (
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
        );
        assert_eq!(
            instantiate_published_generic_interface_method(
                store,
                &globals,
                fixture.receiver,
                fixture.method
            ),
            Err(GenericInterfaceMemberError::InvalidCachedMembers(
                fixture.receiver
            ))
        );
        assert_eq!(
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len()
            ),
            before
        );
        assert!(store.set_object_target_and_mapper(callable, Some(fixture.source), Some(mapper)));
        assert_eq!(
            instantiate_published_generic_interface_method(
                store,
                &globals,
                fixture.receiver,
                fixture.method
            ),
            Ok(callable)
        );
    }

    #[test]
    fn published_interface_method_maps_optional_callable_and_parameter_wrappers() {
        for exact_optional_property_types in [false, true] {
            let parsed = parse_source_file("interface Box<T> { read?(value?: T): T; }");
            let file = FileId::new(6_262);
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
            let owner = source_symbol(&parsed, file, &context, "Box");
            let globals = context.global_types().clone();
            let store = context.store_mut_for_test();
            let target = store
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let method = store
                .symbol(owner)
                .unwrap()
                .members()
                .and_then(|members| store.symbol_table(members))
                .and_then(|members| members.get_source("read"))
                .unwrap();
            let (source, source_value, sentinel) =
                published_interface_method_value(store, owner, method).unwrap();
            let sentinel = sentinel.unwrap();
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let undefined = store.intrinsic_bootstrap().unwrap().undefined_type;
            let receiver = store
                .create_direct_generic_reference_type(target, &[number])
                .unwrap();
            let value =
                instantiate_published_generic_interface_method(store, &globals, receiver, method)
                    .unwrap();
            let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
                panic!("the mapped optional method must retain its value wrapper")
            };
            assert!(union.union.types.contains(&sentinel));
            let callable = *union
                .union
                .types
                .iter()
                .find(|type_| **type_ != sentinel)
                .unwrap();
            let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
                panic!("the method wrapper must contain a callable object")
            };
            assert_eq!(object.target, Some(source));
            let signature = store
                .signature(object.structured.signatures.as_ref().unwrap()[0])
                .unwrap();
            assert_eq!(signature.min_argument_count(), 0);
            assert_eq!(signature.resolved_return_type(), Some(number));
            let parameter = store
                .value_symbol_links(signature.parameters()[0])
                .unwrap()
                .resolved_type
                .unwrap();
            let TypeData::Union(union) = store.type_payload(parameter).unwrap().data() else {
                panic!("the mapped optional parameter must retain undefined")
            };
            let mut expected = [number, undefined];
            expected.sort_unstable();
            assert_eq!(union.union.types, expected);
            assert_eq!(
                store.value_symbol_links(method).unwrap().resolved_type,
                Some(source_value)
            );
            assert!(
                store
                    .validate_union_constituent_with_global_types(&globals, value)
                    .is_ok()
            );
            let before = (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
            );
            assert_eq!(
                instantiate_published_generic_interface_method(store, &globals, receiver, method),
                Ok(value)
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.symbol_len()
                ),
                before
            );
        }
    }

    #[test]
    fn published_array_method_keeps_callback_parameter_and_return_mapping() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> { visit(callback: (value: T) => T): T; } ",
            "interface ReadonlyArray<T> {}",
        ));
        let file = FileId::new(6_263);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        context.check_source_file(file).unwrap();
        let globals = context.global_types().clone();
        let owner = source_symbol(&parsed, file, &context, "Array");
        let store = context.store();
        let method = store
            .symbol(owner)
            .unwrap()
            .members()
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("visit"))
            .unwrap();
        let source = store
            .value_symbol_links(method)
            .unwrap()
            .resolved_type
            .unwrap();
        let original_signature = store
            .type_payload(source)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let callback = store
            .value_symbol_links(store.signature(original_signature).unwrap().parameters()[0])
            .unwrap()
            .resolved_type
            .unwrap();
        let callback_signature = store
            .type_payload(callback)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        context
            .get_return_type_of_signature(callback_signature)
            .unwrap();
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let receiver = store
            .create_canonical_array_type(&globals, number, false)
            .unwrap();
        let callable =
            instantiate_published_generic_interface_method(store, &globals, receiver, method)
                .unwrap();
        let signature = store
            .type_payload(callable)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let signature = store.signature(signature).unwrap();
        assert_eq!(signature.target(), Some(original_signature));
        assert_eq!(signature.resolved_return_type(), Some(number));
        let mapped_callback = store
            .value_symbol_links(signature.parameters()[0])
            .unwrap()
            .resolved_type
            .unwrap();
        assert_ne!(mapped_callback, callback);
        let mapped_signature = store
            .type_payload(mapped_callback)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let mapped_signature = store.signature(mapped_signature).unwrap();
        assert_eq!(mapped_signature.target(), Some(callback_signature));
        assert_eq!(mapped_signature.resolved_return_type(), Some(number));
        assert_eq!(
            store
                .value_symbol_links(mapped_signature.parameters()[0])
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert!(matches!(
            super::super::callable_sets::validate_stored_callable_set(store, callable),
            StoredCallableSetValidation::Valid { .. }
        ));
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

        let selected = context
            .store_mut_for_test()
            .resolve_generic_interface_property_by_key(reference, key_name.as_ref(), None)
            .unwrap()
            .unwrap();
        assert_eq!(selected.symbol(), computed);
        assert_eq!(selected.type_id(), string);
        assert!(selected.is_optional());
        assert!(!selected.is_readonly());
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property(
                    reference,
                    &key_name.escaped_display().to_string(),
                    None,
                ),
            Ok(None),
            "a displayed symbol name is not its byte-exact key",
        );
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            crate::semantic::object_members::resolve_object_property_by_key(
                context.store_mut_for_test(),
                None,
                reference,
                key_name.as_ref(),
                &mut session,
            ),
            Ok(Some(crate::semantic::relater::ResolvedOwnProperty {
                symbol: selected.symbol(),
                type_: selected.type_id(),
                optional: selected.is_optional(),
                readonly: selected.is_readonly(),
            })),
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .resolve_generic_interface_property_by_key(reference, key_name.as_ref(), None),
            Ok(Some(selected)),
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
    fn late_bound_unique_symbol_method_keys_plan_cold_and_publish_exact_source_symbols() {
        for (index, source) in [
            "declare const key: unique symbol; interface Box<T> { [key](): T; }",
            concat!(
                "interface SymbolConstructor { readonly iterator: unique symbol } ",
                "declare var Symbol: SymbolConstructor; ",
                "interface Box<T> { [Symbol.iterator]?(): T; }",
            ),
            concat!(
                "declare class Keys { static readonly iterator: unique symbol; } ",
                "interface Box<T> { [Keys.iterator](): T; }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            use crate::semantic::{
                DeclaredTypeHost,
                object_members::{
                    ComputedMemberKeyError, plan_computed_member_key,
                    publish_computed_member_key_links, resolved_computed_member_key,
                },
                production::GlobalMergeCompletion,
            };
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_230 + u32::try_from(index).unwrap());
            let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(ts_binder::CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let (declaration, name) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, method.name),
                    ))
                })
                .unwrap();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let plan = plan_computed_member_key(context.store(), &host, name).unwrap();
            assert_eq!(
                resolved_computed_member_key(context.store(), &plan),
                Ok(None)
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            if let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(plan.expression.node).unwrap().data
            {
                let receiver = NodeRef::new(
                    plan.expression.arena,
                    plan.expression.file,
                    access.expression,
                );
                let store = context.store_mut_for_test();
                let number = store.intrinsic_bootstrap().unwrap().number_type;
                assert!(store.set_type_node_links(
                    receiver,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    }
                ));
                let before = (
                    store.type_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths(),
                );
                assert_eq!(
                    plan_computed_member_key(store, &host, name),
                    Err(ComputedMemberKeyError::Invalid(plan.expression))
                );
                assert_eq!(
                    (
                        store.type_len(),
                        store.symbol_len(),
                        store.checker_link_allocated_lengths()
                    ),
                    before
                );
                assert!(store.set_type_node_links(receiver, TypeNodeLinks::default()));
            }
            let key_type = context.get_type_from_type_node(plan.type_node).unwrap();
            let (published_key, escaped_name) =
                publish_computed_member_key_links(context.store_mut_for_test(), &host, &plan)
                    .unwrap();
            assert_eq!(published_key, key_type);
            let owner = source_symbol(&parsed, file, &context, "Box");
            let early = bound.symbol(declaration).unwrap();
            let store = context.store_mut_for_test();
            let raw = store.symbol(owner).unwrap().members();
            let members = match raw {
                Some(table) => store.clone_symbol_table(table).unwrap(),
                None => store.alloc_symbol_table(),
            };
            let incomplete = store.alloc_symbol_table();
            let before = (store.symbol_len(), store.checker_link_allocated_lengths());
            assert_eq!(
                store.create_late_bound_property_symbol(owner, early, key_type, incomplete),
                None
            );
            assert_eq!(
                (store.symbol_len(), store.checker_link_allocated_lengths()),
                before
            );
            let late = store
                .create_late_bound_property_symbol(owner, early, key_type, members)
                .unwrap();
            let symbol = store.symbol(late).unwrap();
            assert_eq!(symbol.name(), escaped_name.as_ref());
            assert_eq!(
                symbol.flags(),
                store.symbol(early).unwrap().flags() | SymbolFlags::TRANSIENT
            );
            assert_eq!(symbol.check_flags(), CheckFlags::LATE);
            assert_eq!(symbol.declarations(), Some(&[declaration][..]));
            assert_eq!(symbol.parent(), Some(owner));
            assert_eq!(
                store
                    .symbol_table(members)
                    .unwrap()
                    .get(escaped_name.as_ref()),
                Some(late)
            );
            assert_eq!(
                store.value_symbol_links(late).unwrap().name_type,
                Some(key_type)
            );
            let warm = (store.symbol_len(), store.checker_link_allocated_lengths());
            assert_eq!(plan_computed_member_key(store, &host, name), Ok(plan));
            assert_eq!(
                store.create_late_bound_property_symbol(owner, early, key_type, members),
                Some(late)
            );
            assert_eq!(
                (store.symbol_len(), store.checker_link_allocated_lengths()),
                warm
            );
        }
    }

    #[test]
    fn late_bound_unique_symbol_method_keys_reject_foreign_and_conflicting_caches() {
        use crate::semantic::{
            DeclaredTypeHost,
            object_members::{
                ComputedMemberKeyError, plan_computed_member_key, publish_computed_member_key_links,
            },
            production::GlobalMergeCompletion,
        };
        let parsed = parse_source_file(concat!(
            "declare const key: unique symbol; declare const other: unique symbol; ",
            "interface Box<T> { [key](): T; }",
        ));
        let file = FileId::new(6_233);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(ts_binder::CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let name = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ComputedPropertyName).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let plan = plan_computed_member_key(context.store(), &host, name).unwrap();
        let key_type = context.get_type_from_type_node(plan.type_node).unwrap();
        let other = source_symbol(&parsed, file, &context, "other");
        let store = context.store_mut_for_test();
        let other_type = store.alloc_unique_es_symbol_type(other).unwrap();
        assert!(store.set_type_node_links(
            plan.expression,
            TypeNodeLinks {
                resolved_type: Some(other_type),
                ..TypeNodeLinks::default()
            }
        ));
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_computed_member_key(store, &host, name),
            Err(ComputedMemberKeyError::Invalid(plan.expression))
        );
        assert_eq!(
            publish_computed_member_key_links(store, &host, &plan),
            Err(ComputedMemberKeyError::Invalid(plan.expression))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths()
            ),
            before
        );
        assert!(store.set_type_node_links(plan.expression, TypeNodeLinks::default()));
        assert_eq!(
            publish_computed_member_key_links(store, &host, &plan)
                .unwrap()
                .0,
            key_type
        );

        let foreign = parse_source_file("interface Foreign { [key](): number; }");
        let foreign_name = foreign
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ComputedPropertyName).then_some(NodeRef::new(
                    foreign.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_computed_member_key(store, &host, foreign_name),
            Err(ComputedMemberKeyError::Invalid(foreign_name))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn iterator_symbol_key_uses_the_global_value_annotation_before_fallback() {
        use crate::semantic::object_members::{
            KnownSymbolKeyError, iterator_key, iterator_key_with_global_types,
        };
        for (index, (body, expected)) in [
            ("readonly iterator: unique symbol", None),
            ("(): symbol; readonly iterator: unique symbol", None),
            ("iterator: \"custom\"", Some("custom")),
            ("iterator: 7", Some("7")),
            ("iterator: number", Some("__@iterator")),
            ("other: string", Some("__@iterator")),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&format!(
                "interface Factory {{ {body} }} interface OtherFactory {{ iterator: \"wrong\" }} declare const Symbol: Factory;"
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_240 + u32::try_from(index).unwrap());
            let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
            let symbol = source_symbol(&parsed, file, &context, "Symbol");
            let declaration = context
                .store()
                .symbol(symbol)
                .unwrap()
                .value_declaration()
                .unwrap();
            let annotation = context
                .store()
                .source_direct_type_annotation(declaration)
                .unwrap();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                iterator_key(context.store_mut_for_test()),
                Err(KnownSymbolKeyError::NeedsValueType {
                    symbol,
                    annotation: Some(annotation)
                })
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
            let value_type = context.get_type_from_type_node(annotation).unwrap();
            let actual = iterator_key(context.store_mut_for_test()).unwrap();
            let globals = context.global_types().clone();
            assert_eq!(
                iterator_key_with_global_types(context.store_mut_for_test(), &globals),
                Ok(actual.clone())
            );
            if let Some(expected) = expected {
                assert_eq!(actual.escaped_display().to_string(), expected);
                assert_eq!(actual.as_ref().is_late_bound(), expected == "__@iterator");
            } else {
                let value = context
                    .store()
                    .type_payload(value_type)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap();
                let property = context
                    .store()
                    .symbol_table(value.members.unwrap())
                    .unwrap()
                    .get_source("iterator")
                    .unwrap();
                let property_type = context
                    .store()
                    .value_symbol_links(property)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                let TypeData::UniqueEsSymbol(unique) =
                    context.store().type_payload(property_type).unwrap().data()
                else {
                    panic!("iterator must retain its unique key type");
                };
                assert_eq!(actual, unique.name);
                assert_ne!(
                    actual,
                    ts_binder::semantic::SymbolStore::known_symbol_name("iterator")
                );
            }
            let warm = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(iterator_key(context.store_mut_for_test()), Ok(actual));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                warm
            );
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(context.store_mut_for_test().set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                }
            ));
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                iterator_key(context.store_mut_for_test()),
                Err(KnownSymbolKeyError::InvalidSymbol(symbol))
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
            let other = source_symbol(&parsed, file, &context, "OtherFactory");
            let other_type = context.get_declared_type_of_symbol(other).unwrap();
            assert!(context.store_mut_for_test().set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(other_type),
                    ..ValueSymbolLinks::default()
                }
            ));
            assert!(context.store_mut_for_test().set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(other_type),
                    ..TypeNodeLinks::default()
                }
            ));
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                iterator_key(context.store_mut_for_test()),
                Err(KnownSymbolKeyError::InvalidSymbol(symbol))
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
    }

    #[test]
    fn iterator_symbol_key_preserves_class_value_and_prototype_validation() {
        use crate::semantic::object_members::{KnownSymbolKeyError, iterator_key};
        let parsed = parse_source_file("declare class Symbol { static iterator: number; }");
        let file = FileId::new(6_250);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let symbol = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source("Symbol")
            .unwrap();
        let members = context.get_nongeneric_class_members(symbol).unwrap();
        let store = context.store_mut_for_test();
        assert_eq!(
            iterator_key(store),
            Ok(ts_binder::semantic::SymbolStore::known_symbol_name(
                "iterator"
            ))
        );
        let original = store.value_symbol_links(symbol).unwrap().clone();
        let any = store.intrinsic_bootstrap().unwrap().any_type;
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(any),
                ..ValueSymbolLinks::default()
            }
        ));
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            iterator_key(store),
            Err(KnownSymbolKeyError::InvalidSymbol(symbol))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths()
            ),
            before
        );
        assert!(store.set_value_symbol_links(symbol, original));
        let prototype = members.prototype();
        let links = store
            .value_symbol_links(prototype)
            .cloned()
            .unwrap_or_default();
        assert!(store.set_value_symbol_links(
            prototype,
            ValueSymbolLinks {
                resolved_type: Some(any),
                ..links
            }
        ));
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            iterator_key(store),
            Err(KnownSymbolKeyError::InvalidSymbol(symbol))
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn iterator_symbol_key_falls_back_only_for_absent_or_unusable_globals() {
        use crate::semantic::object_members::iterator_key;
        for source in [
            "interface Other {}",
            "interface Symbol {}",
            "declare const Symbol: any;",
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(6_246);
            let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert_eq!(
                iterator_key(context.store_mut_for_test()),
                Ok(ts_binder::semantic::SymbolStore::known_symbol_name(
                    "iterator"
                ))
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
    }

    #[test]
    fn iterator_symbol_key_uses_callable_function_augmentation() {
        use crate::semantic::object_members::{
            KnownSymbolKeyError, iterator_key, iterator_key_with_global_types,
        };
        let parsed = parse_source_file(concat!(
            "interface Function { iterator: \"inherited\" } ",
            "interface Factory { (): symbol; } declare const Symbol: Factory;",
        ));
        let file = FileId::new(6_247);
        let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
        let symbol = source_symbol(&parsed, file, &context, "Symbol");
        let function = source_symbol(&parsed, file, &context, "Function");
        let annotation = context
            .store()
            .source_direct_type_annotation(
                context
                    .store()
                    .symbol(symbol)
                    .unwrap()
                    .value_declaration()
                    .unwrap(),
            )
            .unwrap();
        context.get_type_from_type_node(annotation).unwrap();
        context.get_declared_type_of_symbol(function).unwrap();
        let globals = context.global_types().clone();
        assert_eq!(
            iterator_key(context.store_mut_for_test()),
            Err(KnownSymbolKeyError::MissingGlobalTypes)
        );
        assert_eq!(
            iterator_key_with_global_types(context.store_mut_for_test(), &globals),
            Ok(EscapedName::source("inherited"))
        );
    }

    #[test]
    fn late_bound_unique_symbol_method_members_keep_callable_identity_and_source_links() {
        use crate::semantic::{
            DeclaredTypeHost, LateBoundLinks,
            object_members::{
                plan_computed_member_key, publish_computed_member_key_links,
                resolve_object_property_by_key,
            },
            production::GlobalMergeCompletion,
        };
        for (index, parameters) in ["", "<T>"].into_iter().enumerate() {
            let return_text = if parameters.is_empty() { "number" } else { "T" };
            let derived_text = if parameters.is_empty() {
                ""
            } else {
                "interface Derived<T> extends Box<T> {}"
            };
            let parsed = parse_source_file(&format!(
                "declare const key: unique symbol; interface Box{parameters} {{ [key](): {return_text}; }} {derived_text}"
            ));
            let file = FileId::new(6_248 + u32::try_from(index).unwrap());
            let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(ts_binder::CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let owner = source_symbol(&parsed, file, &context, "Box");
            let target = context
                .store_mut_for_test()
                .get_declared_type_of_symbol(&host, owner)
                .unwrap();
            let (declaration, name) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, method.name),
                    ))
                })
                .unwrap();
            let key_plan = plan_computed_member_key(context.store(), &host, name).unwrap();
            context.get_type_from_type_node(key_plan.type_node).unwrap();
            let (key_type, key_name) =
                publish_computed_member_key_links(context.store_mut_for_test(), &host, &key_plan)
                    .unwrap();
            let early = bound.symbol(declaration).unwrap();
            let derived =
                (!parameters.is_empty()).then(|| source_symbol(&parsed, file, &context, "Derived"));
            let store = context.store_mut_for_test();
            let raw = store.symbol(owner).unwrap().members();
            let resolved = match raw {
                Some(raw) => store.clone_symbol_table(raw).unwrap(),
                None => store.alloc_symbol_table(),
            };
            let late = store
                .create_late_bound_property_symbol(owner, early, key_type, resolved)
                .unwrap();
            let mut links = crate::semantic::MembersAndExportsLinks::default();
            links.tables[MembersOrExportsResolutionKind::ResolvedMembers as usize] = Some(resolved);
            assert!(store.set_members_and_exports_links(owner, links));
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let annotation = store.source_direct_type_annotation(declaration).unwrap();
            let return_type = if parameters.is_empty() {
                number
            } else {
                let NodeData::TypeReferenceNode(reference) =
                    &parsed.arena.get(annotation.node).unwrap().data
                else {
                    panic!("the generic method must return its parameter");
                };
                let type_name =
                    NodeRef::new(annotation.arena, annotation.file, reference.type_name);
                let parameter = host
                    .name_resolver_host(store)
                    .unwrap()
                    .resolve_entity_name(type_name, SymbolFlags::TYPE)
                    .unwrap()
                    .unwrap();
                let type_ = store.get_declared_type_of_symbol(&host, parameter).unwrap();
                assert!(store.set_symbol_node_links(
                    annotation,
                    SymbolNodeLinks {
                        resolved_symbol: Some(parameter)
                    }
                ));
                assert!(store.set_type_node_links(
                    annotation,
                    TypeNodeLinks {
                        resolved_type: Some(type_),
                        ..TypeNodeLinks::default()
                    }
                ));
                type_
            };
            let callable = store
                .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(late))
                .unwrap();
            let signature = store
                .alloc_signature(
                    SignatureFlags::NONE,
                    Some(declaration),
                    Vec::new(),
                    None,
                    Vec::new(),
                    Some(return_type),
                    None,
                    0,
                )
                .unwrap();
            assert!(store.set_signature_links(
                declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                }
            ));
            assert!(store.set_structured_type_members(
                callable,
                None,
                None,
                Some(vec![signature]),
                None,
                None
            ));
            assert!(store.set_value_symbol_links(
                late,
                ValueSymbolLinks {
                    resolved_type: Some(callable),
                    name_type: Some(key_type),
                    ..ValueSymbolLinks::default()
                }
            ));
            assert!(
                store.set_callable_signature_parameter_types_batch(vec![(signature, Vec::new())])
            );
            let members = store.alloc_symbol_table();
            assert_eq!(
                store.insert_symbol(members, key_name.clone(), late),
                Some(None)
            );
            assert!(store.publish_interface_no_base_resolution(target));
            assert!(store.set_interface_declared_members(
                target,
                true,
                Some(members),
                None,
                None,
                None
            ));
            let receiver = if parameters.is_empty() {
                assert!(store.set_structured_type_members(
                    target,
                    Some(members),
                    Some(vec![late]),
                    None,
                    None,
                    None
                ));
                target
            } else {
                store
                    .create_direct_generic_reference_type(target, &[number])
                    .unwrap()
            };
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            assert!(valid_late_bound_unique_symbol_member(
                store,
                owner,
                late,
                &[declaration],
                store.value_symbol_links(late).unwrap(),
                store.symbol_table(resolved),
            ));
            assert!(
                valid_interface_method_value(store, late, callable).is_some(),
                "method callable: {:?}, signature: {:?}",
                store.type_payload(callable),
                store.signature(signature)
            );
            if parameters.is_empty() {
                assert!(
                    crate::semantic::structured_members::valid_declared_member_table(
                        store,
                        owner,
                        Some(members)
                    )
                );
            }
            let property = resolve_object_property_by_key(
                store,
                None,
                receiver,
                key_name.as_ref(),
                &mut session,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "method {parameters:?}: {error:?}, receiver: {:?}",
                    store.type_payload(receiver)
                )
            })
            .unwrap();
            if parameters.is_empty() {
                assert_eq!(property.symbol, late);
                assert_eq!(property.type_, callable);
            } else {
                assert_ne!(property.symbol, late);
                assert_ne!(property.type_, callable);
                let links = store.value_symbol_links(property.symbol).unwrap();
                assert_eq!(links.target, Some(late));
                assert_eq!(links.name_type, Some(key_type));
                let instantiated = store
                    .type_payload(property.type_)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap()
                    .signatures
                    .as_ref()
                    .unwrap()[0];
                assert_eq!(
                    store
                        .signature(instantiated)
                        .unwrap()
                        .resolved_return_type(),
                    Some(number)
                );
                assert_eq!(
                    store.signature(signature).unwrap().resolved_return_type(),
                    Some(return_type)
                );
                assert_eq!(
                    store.type_node_links(annotation).unwrap().resolved_type,
                    Some(return_type)
                );
            }
            let warm = (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                resolve_object_property_by_key(
                    store,
                    None,
                    receiver,
                    key_name.as_ref(),
                    &mut session
                ),
                Ok(Some(property))
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths()
                ),
                warm
            );
            if let Some(derived) = derived {
                let derived = store.get_declared_type_of_symbol(&host, derived).unwrap();
                let TypeData::Interface(data) = store.type_payload(derived).unwrap().data() else {
                    panic!("Derived must keep its interface target");
                };
                let parameter = data.reference.resolved_type_arguments.as_ref().unwrap()[0];
                let base = store
                    .create_direct_generic_reference_type(target, &[parameter])
                    .unwrap();
                assert!(store.set_interface_base_resolution(derived, true, None, Some(vec![base])));
                assert!(
                    store.set_interface_declared_members(derived, true, None, None, None, None)
                );
                let inherited = store
                    .create_direct_generic_reference_type(derived, &[number])
                    .unwrap();
                assert_eq!(
                    resolve_object_property_by_key(
                        store,
                        None,
                        inherited,
                        key_name.as_ref(),
                        &mut session
                    ),
                    Ok(Some(property))
                );
            }
            assert!(store.set_late_bound_links(early, LateBoundLinks::default()));
            let before = (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            );
            assert!(
                resolve_object_property_by_key(
                    store,
                    None,
                    receiver,
                    key_name.as_ref(),
                    &mut session
                )
                .is_err()
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.checker_link_allocated_lengths()
                ),
                before
            );
            assert!(store.set_late_bound_links(
                early,
                LateBoundLinks {
                    late_symbol: Some(late)
                }
            ));
            assert_eq!(
                resolve_object_property_by_key(
                    store,
                    None,
                    receiver,
                    key_name.as_ref(),
                    &mut session
                ),
                Ok(Some(property))
            );
        }
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
                context
                    .store_mut_for_test()
                    .resolve_generic_interface_property_by_key(
                        reference,
                        EscapedNameRef::source("missing"),
                        None,
                    ),
                Err(GenericInterfaceMemberError::InvalidMember(target.late)),
                "a missing key cannot hide an invalid declaration cache",
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

    struct GenericIndexSessionFixture<'arena> {
        context: CanonicalCheckerContext<'arena>,
        reference: TypeId,
        target: TypeId,
        parameter: TypeId,
        wrapper: TypeId,
        sources: Vec<IndexInfoId>,
    }

    fn generic_index_session_fixture(
        parsed: &ParseResult,
        file: FileId,
    ) -> GenericIndexSessionFixture<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(parsed, file, CanonicalCheckerOptions::default());
        let wrapper_owner = source_symbol(parsed, file, &context, "Wrapper");
        let wrapper = context.get_declared_type_of_symbol(wrapper_owner).unwrap();
        let TypeData::Interface(wrapper_data) =
            context.store().type_payload(wrapper).unwrap().data()
        else {
            panic!("Wrapper must retain its generic target")
        };
        let wrapper_parameter = wrapper_data
            .reference
            .resolved_type_arguments
            .as_ref()
            .unwrap()[0];
        publish_generic_target_for_test(
            &mut context,
            wrapper,
            &[("value", wrapper_parameter)],
            None,
        );

        let owner = source_symbol(parsed, file, &context, "Lookup");
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let TypeData::Interface(target_data) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("Lookup must retain its generic target")
        };
        let parameter = target_data
            .reference
            .resolved_type_arguments
            .as_ref()
            .unwrap()[0];
        let table = context.store().symbol(owner).unwrap().members().unwrap();
        let own = context
            .store()
            .symbol_table(table)
            .unwrap()
            .get_source("own");
        let mut properties = Vec::new();
        if let Some(own) = own {
            let declaration = context
                .store()
                .symbol(own)
                .unwrap()
                .value_declaration()
                .unwrap();
            let annotation = context
                .store()
                .source_direct_type_annotation(declaration)
                .unwrap();
            properties.push(("own", context.get_type_from_type_node(annotation).unwrap()));
        }
        let index_symbol = context
            .store()
            .symbol_table(table)
            .unwrap()
            .get(InternalSymbolName::Index.as_ref())
            .unwrap();
        let declarations = context
            .store()
            .symbol(index_symbol)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        let mut infos = Vec::new();
        for declaration in declarations {
            let children = context
                .store()
                .source_direct_children(declaration)
                .unwrap()
                .clone();
            let key_parameter = children
                .iter()
                .copied()
                .find(|child| {
                    context.store().source_node_kind(*child) == Some(SyntaxKind::Parameter)
                })
                .unwrap();
            let key_annotation = context
                .store()
                .source_direct_type_annotation(key_parameter)
                .unwrap();
            let value_annotation = context
                .store()
                .source_direct_type_annotation(declaration)
                .unwrap();
            let readonly = children.iter().any(|child| {
                context.store().source_node_kind(*child) == Some(SyntaxKind::ReadonlyKeyword)
            });
            let key = context.get_type_from_type_node(key_annotation).unwrap();
            let value = context.get_type_from_type_node(value_annotation).unwrap();
            infos.push((key, value, readonly, declaration));
        }
        publish_generic_target_for_test(&mut context, target, &properties, None);
        let store = context.store_mut_for_test();
        let members = match store.type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface.declared_members,
            _ => unreachable!(),
        };
        let sources = infos
            .into_iter()
            .map(|(key, value, readonly, declaration)| {
                store
                    .alloc_index_info(key, value, readonly, Some(declaration), Vec::new())
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert!(store.set_interface_declared_members(
            target,
            true,
            members,
            None,
            None,
            Some(sources.clone()),
        ));
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let reference = store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        GenericIndexSessionFixture {
            context,
            reference,
            target,
            parameter,
            wrapper,
            sources,
        }
    }

    fn generic_index_value(
        store: &CanonicalTypeMapperStore,
        reference: TypeId,
    ) -> (IndexInfoId, TypeId) {
        let indexes = store
            .type_payload(reference)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .index_infos
            .as_deref()
            .unwrap();
        assert_eq!(indexes.len(), 1);
        (
            indexes[0],
            store.index_info(indexes[0]).unwrap().value_type(),
        )
    }

    #[test]
    fn generic_index_recovery_uses_the_caller_budget_and_replays_warm_identity() {
        for own in [false, true] {
            for (annotation, remaining) in [("T", 0), ("Wrapper<T>", 1)] {
                let member = if own {
                    format!("own: {annotation};")
                } else {
                    String::new()
                };
                let parsed = parse_source_file(&format!(
                    "interface Wrapper<T> {{ value: T }} \
                     interface Lookup<T> {{ readonly [key: string]: {annotation}; {member} }}",
                ));
                let mut fixture = generic_index_session_fixture(&parsed, FileId::new(6_310));
                let store = fixture.context.store_mut_for_test();
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                let (number, error_type) = (bootstrap.number_type, bootstrap.error_type);
                let mut session = InstantiationSession::new_recovering(
                    store,
                    InstantiationLimits {
                        max_count: 1 + remaining,
                        ..InstantiationLimits::default()
                    },
                    error_type,
                )
                .unwrap();
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        store,
                        fixture.parameter,
                        &[fixture.parameter],
                        &[number],
                        None,
                        &mut session,
                    ),
                    Ok(number)
                );
                assert_eq!(session.query_count(), 1);
                let mark = session.limit_event_mark();
                let members = resolve_members_with_array_targets_and_session(
                    store,
                    fixture.reference,
                    None,
                    &mut session,
                )
                .unwrap();
                assert!(session.limit_event_occurred_since(mark));
                assert_eq!(session.query_count(), 1 + remaining);
                assert_eq!(session.total_count(), 1 + remaining);
                let (index, result) = generic_index_value(store, fixture.reference);
                assert!(store.instantiated_index_recovery(index).is_some());
                if annotation == "T" {
                    assert_eq!(result, error_type);
                } else {
                    let result = validate_direct_generic_reference(store, result).unwrap();
                    assert_eq!(result.target, fixture.wrapper);
                    assert_eq!(result.type_arguments, [error_type]);
                }
                for property in members.properties() {
                    assert!(
                        store
                            .value_symbol_links(*property)
                            .unwrap()
                            .resolved_type
                            .is_none()
                    );
                }
                if annotation == "Wrapper<T>" {
                    let wrapped_value = store
                        .resolve_generic_interface_property(result, "value", None)
                        .unwrap()
                        .unwrap();
                    assert_eq!(wrapped_value.type_id(), error_type);
                }
                if own {
                    let property = store
                        .resolve_generic_interface_property(fixture.reference, "own", None)
                        .unwrap()
                        .unwrap();
                    if annotation == "T" {
                        assert_eq!(property.type_id(), number);
                    } else {
                        let value =
                            validate_direct_generic_reference(store, property.type_id()).unwrap();
                        assert_eq!(value.target, fixture.wrapper);
                        assert_eq!(value.type_arguments, [number]);
                    }
                }
                let before = property_recovery_store_counts(store);
                let mark = session.limit_event_mark();
                for _ in 0..2 {
                    assert_eq!(
                        resolve_members_with_array_targets_and_session(
                            store,
                            fixture.reference,
                            None,
                            &mut session,
                        ),
                        Ok(members.clone())
                    );
                    assert_eq!(
                        resolve_property_with_array_targets_and_session(
                            store,
                            fixture.reference,
                            EscapedNameRef::source("absent"),
                            None,
                            &mut session,
                        ),
                        Ok(None)
                    );
                    assert_eq!(
                        generic_index_value(store, fixture.reference),
                        (index, result)
                    );
                    assert_eq!(property_recovery_store_counts(store), before);
                    assert_eq!(session.query_count(), 1 + remaining);
                    assert_eq!(session.total_count(), 1 + remaining);
                    assert!(!session.limit_event_occurred_since(mark));
                }
                let mut warm = InstantiationSession::new(InstantiationLimits {
                    max_count: 0,
                    ..InstantiationLimits::default()
                });
                assert_eq!(
                    resolve_members_with_array_targets_and_session(
                        store,
                        fixture.reference,
                        None,
                        &mut warm,
                    ),
                    Ok(members)
                );
                assert_eq!(warm.total_count(), 0);
                assert_eq!(property_recovery_store_counts(store), before);
            }
        }
    }

    #[test]
    fn generic_index_only_wrappers_and_unions_replay_without_mapper_allocation() {
        for annotation in ["Wrapper<T>", "T | string"] {
            let parsed = parse_source_file(&format!(
                "interface Wrapper<T> {{ value: T }} \
                 interface Lookup<T> {{ readonly [key: string]: {annotation} }}",
            ));
            let mut fixture = generic_index_session_fixture(&parsed, FileId::new(6_311));
            let store = fixture.context.store_mut_for_test();
            let mappers = store.mapper_len();
            let members =
                resolve_members_with_array_targets(store, fixture.reference, None).unwrap();
            assert!(members.mapper().is_none());
            assert_eq!(store.mapper_len(), mappers);
            let (index, result) = generic_index_value(store, fixture.reference);
            if annotation == "T | string" {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                let TypeData::Union(union) = store.type_payload(result).unwrap().data() else {
                    panic!("Lookup<number> must retain the number|string index value")
                };
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&bootstrap.number_type));
                assert!(union.union.types.contains(&bootstrap.string_type));
            }
            assert!(store.instantiated_index_recovery(index).is_none());
            let before = property_recovery_store_counts(store);
            for _ in 0..2 {
                assert_eq!(
                    resolve_members_with_array_targets(store, fixture.reference, None),
                    Ok(members.clone())
                );
                assert_eq!(
                    generic_index_value(store, fixture.reference),
                    (index, result)
                );
                assert_eq!(property_recovery_store_counts(store), before);
            }
        }
    }

    #[test]
    fn generic_index_failures_do_not_publish_earlier_index_records_or_members() {
        let parsed = parse_source_file(concat!(
            "interface Wrapper<T> { value: T } ",
            "interface Lookup<T> { readonly [key: string]: T; readonly [key: number]: Wrapper<T> }",
        ));
        let mut fixture = generic_index_session_fixture(&parsed, FileId::new(6_312));
        let store = fixture.context.store_mut_for_test();
        let before = property_recovery_store_counts(store);
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_count: 1,
            ..InstantiationLimits::default()
        });
        for _ in 0..2 {
            assert!(
                resolve_members_with_array_targets_and_session(
                    store,
                    fixture.reference,
                    None,
                    &mut session,
                )
                .is_err()
            );
            assert_eq!(
                store
                    .type_payload(fixture.reference)
                    .unwrap()
                    .data()
                    .structured(),
                Some(&StructuredTypeData::default())
            );
            assert_eq!(property_recovery_store_counts(store), before);
            assert_eq!(session.query_count(), 1);
            assert_eq!(session.total_count(), 1);
        }
    }

    #[test]
    fn generic_index_recovery_rejects_noncanonical_error_before_writes() {
        let parsed = parse_source_file(concat!(
            "interface Wrapper<T> { value: T } ",
            "interface Lookup<T> { readonly [key: string]: Wrapper<T>; own: Wrapper<T> }",
        ));
        let mut fixture = generic_index_session_fixture(&parsed, FileId::new(6_313));
        let store = fixture.context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let before = property_recovery_store_counts(store);
        let mut session = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            },
            number,
        )
        .unwrap();
        for _ in 0..2 {
            assert_eq!(
                resolve_members_with_array_targets_and_session(
                    store,
                    fixture.reference,
                    None,
                    &mut session,
                ),
                Err(GenericInterfaceMemberError::InvalidCachedMembers(
                    fixture.reference
                ))
            );
            assert_eq!(property_recovery_store_counts(store), before);
            assert_eq!(session.total_count(), 0);
        }
    }

    #[test]
    fn generic_index_recovery_rejects_raw_index_writes_and_unproven_results() {
        for change_source in [false, true] {
            let parsed = parse_source_file(concat!(
                "interface Wrapper<T> { value: T } ",
                "interface Lookup<T> { readonly [key: string]: Wrapper<T> }",
            ));
            let mut fixture = generic_index_session_fixture(&parsed, FileId::new(6_314));
            let store = fixture.context.store_mut_for_test();
            let error_type = store.intrinsic_bootstrap().unwrap().error_type;
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 1,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            resolve_members_with_array_targets_and_session(
                store,
                fixture.reference,
                None,
                &mut session,
            )
            .unwrap();
            let (index, result) = generic_index_value(store, fixture.reference);
            let written = if change_source {
                fixture.sources[0]
            } else {
                index
            };
            assert!(store.set_index_info_symbol(written, None));
            let before = property_recovery_store_counts(store);
            for _ in 0..2 {
                assert_eq!(
                    resolve_members_with_array_targets_and_session(
                        store,
                        fixture.reference,
                        None,
                        &mut session,
                    ),
                    Err(GenericInterfaceMemberError::InvalidCachedMembers(
                        fixture.reference
                    ))
                );
                assert_eq!(property_recovery_store_counts(store), before);
            }
            let boolean = store.intrinsic_bootstrap().unwrap().boolean_type;
            let other = store
                .create_direct_generic_reference_type(fixture.target, &[boolean])
                .unwrap();
            let source = store.index_info(fixture.sources[0]).unwrap();
            let forged = store
                .alloc_index_info(
                    source.key_type(),
                    result,
                    source.is_readonly(),
                    source.declaration(),
                    source.components().to_vec(),
                )
                .unwrap();
            assert!(store.set_structured_type_members(
                other,
                None,
                None,
                None,
                None,
                Some(vec![forged])
            ));
            assert!(store.instantiated_index_recovery(forged).is_none());
            let before = property_recovery_store_counts(store);
            assert_eq!(
                resolve_members_with_array_targets_and_session(store, other, None, &mut session),
                Err(GenericInterfaceMemberError::InvalidCachedMembers(other))
            );
            assert_eq!(property_recovery_store_counts(store), before);
        }
    }

    #[test]
    fn generic_index_recovery_rejects_source_link_and_result_graph_writes() {
        for source_link in [false, true] {
            let parsed = parse_source_file(concat!(
                "interface Wrapper<T> { value: T } ",
                "interface Lookup<T> { readonly [key: string]: Wrapper<T>; own: Wrapper<T> }",
            ));
            let mut fixture = generic_index_session_fixture(&parsed, FileId::new(6_315));
            let store = fixture.context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (error_type, number) = (bootstrap.error_type, bootstrap.number_type);
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count: 1,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let members = resolve_members_with_array_targets_and_session(
                store,
                fixture.reference,
                None,
                &mut session,
            )
            .unwrap();
            let (_, result) = generic_index_value(store, fixture.reference);
            if source_link {
                let source = store
                    .value_symbol_links(members.properties()[0])
                    .unwrap()
                    .target
                    .unwrap();
                let links = store.value_symbol_links(source).unwrap().clone();
                assert!(store.set_value_symbol_links(source, links));
            } else {
                assert!(store.set_type_reference_resolution(result, None, Some(vec![number])));
            }
            let before = property_recovery_store_counts(store);
            let mark = session.limit_event_mark();
            for _ in 0..2 {
                assert_eq!(
                    resolve_members_with_array_targets_and_session(
                        store,
                        fixture.reference,
                        None,
                        &mut session,
                    ),
                    Err(GenericInterfaceMemberError::InvalidCachedMembers(
                        fixture.reference
                    ))
                );
                assert_eq!(property_recovery_store_counts(store), before);
                assert!(!session.limit_event_occurred_since(mark));
            }
        }
    }

    #[test]
    fn generic_inherited_members_share_the_budget_and_keep_unavailable_replay_stable() {
        for (own_index, max_count) in [(false, 1), (false, 2), (true, 3)] {
            let own = if own_index {
                "readonly [key: number]: T"
            } else {
                "own: T"
            };
            let parsed = parse_source_file(&format!(
                "interface Base<T> {{ readonly [key: string]: T }} \
                 interface Derived<T> extends Base<T> {{ {own} }}",
            ));
            let file = FileId::new(6_316);
            let mut context = checker_context(&parsed, file, CanonicalCheckerOptions::default());
            let base_owner = source_symbol(&parsed, file, &context, "Base");
            let owner = source_symbol(&parsed, file, &context, "Derived");
            let base = context.get_declared_type_of_symbol(base_owner).unwrap();
            let target = context.get_declared_type_of_symbol(owner).unwrap();
            let TypeData::Interface(base_data) = context.store().type_payload(base).unwrap().data()
            else {
                panic!("Base must retain its generic target")
            };
            let base_parameter = base_data
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0];
            let TypeData::Interface(target_data) =
                context.store().type_payload(target).unwrap().data()
            else {
                panic!("Derived must retain its generic target")
            };
            let parameter = target_data
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0];
            let declaration = context
                .store()
                .symbol(base_owner)
                .unwrap()
                .members()
                .and_then(|members| context.store().symbol_table(members))
                .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                .and_then(|symbol| context.store().symbol(symbol))
                .and_then(ts_binder::semantic::Symbol::declarations)
                .unwrap()[0];
            publish_generic_target_for_test(&mut context, base, &[], None);
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let source = context
                .store_mut_for_test()
                .alloc_index_info(string, base_parameter, true, Some(declaration), Vec::new())
                .unwrap();
            assert!(context.store_mut_for_test().set_interface_declared_members(
                base,
                true,
                None,
                None,
                None,
                Some(vec![source]),
            ));
            let base_template = context
                .store_mut_for_test()
                .create_direct_generic_reference_type(base, &[parameter])
                .unwrap();
            let properties = if own_index {
                Vec::new()
            } else {
                vec![("own", parameter)]
            };
            publish_generic_target_for_test(
                &mut context,
                target,
                &properties,
                Some(vec![base_template]),
            );
            if own_index {
                let declaration = context
                    .store()
                    .symbol(owner)
                    .unwrap()
                    .members()
                    .and_then(|members| context.store().symbol_table(members))
                    .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
                    .and_then(|symbol| context.store().symbol(symbol))
                    .and_then(ts_binder::semantic::Symbol::declarations)
                    .unwrap()[0];
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                let index = context
                    .store_mut_for_test()
                    .alloc_index_info(number, parameter, true, Some(declaration), Vec::new())
                    .unwrap();
                assert!(context.store_mut_for_test().set_interface_declared_members(
                    target,
                    true,
                    None,
                    None,
                    None,
                    Some(vec![index]),
                ));
            }
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (number, error_type) = (bootstrap.number_type, bootstrap.error_type);
            let reference = store
                .create_direct_generic_reference_type(target, &[number])
                .unwrap();
            let before_mappers = store.mapper_len();
            let before_indexes = store.index_info_len();
            let mut session = InstantiationSession::new_recovering(
                store,
                InstantiationLimits {
                    max_count,
                    ..InstantiationLimits::default()
                },
                error_type,
            )
            .unwrap();
            let mark = session.limit_event_mark();
            let result = resolve_members_with_array_targets_and_session(
                store,
                reference,
                None,
                &mut session,
            );
            assert!(session.limit_event_occurred_since(mark));
            assert_eq!(session.query_count(), max_count);
            assert_eq!(session.total_count(), max_count);
            if max_count == 1 {
                assert_eq!(
                    result,
                    Err(GenericInterfaceMemberError::UnsupportedTarget(reference))
                );
                assert_eq!(store.mapper_len(), before_mappers);
                assert_eq!(store.index_info_len(), before_indexes);
                assert_eq!(
                    store.type_payload(reference).unwrap().data().structured(),
                    Some(&StructuredTypeData::default())
                );
            } else {
                let members = result.as_ref().unwrap();
                if own_index {
                    let indexes = store
                        .type_payload(reference)
                        .unwrap()
                        .data()
                        .structured()
                        .unwrap()
                        .index_infos
                        .as_deref()
                        .unwrap();
                    assert_eq!(indexes.len(), 2);
                    let own = store.index_info(indexes[0]).unwrap();
                    let inherited = store.index_info(indexes[1]).unwrap();
                    assert_eq!((own.key_type(), own.value_type()), (number, number));
                    assert_eq!(
                        (inherited.key_type(), inherited.value_type()),
                        (string, error_type)
                    );
                    assert!(store.instantiated_index_recovery(indexes[0]).is_none());
                    assert!(store.instantiated_index_recovery(indexes[1]).is_some());
                    assert!(members.properties().is_empty());
                } else {
                    let (index, value) = generic_index_value(store, reference);
                    assert_eq!(value, error_type);
                    assert!(store.instantiated_index_recovery(index).is_some());
                    assert!(
                        store
                            .value_symbol_links(members.properties()[0])
                            .unwrap()
                            .resolved_type
                            .is_none()
                    );
                }
            }
            let before = property_recovery_store_counts(store);
            let mark = session.limit_event_mark();
            for _ in 0..2 {
                assert_eq!(
                    resolve_members_with_array_targets_and_session(
                        store,
                        reference,
                        None,
                        &mut session,
                    ),
                    result
                );
                assert_eq!(property_recovery_store_counts(store), before);
                assert_eq!(session.query_count(), max_count);
                assert_eq!(session.total_count(), max_count);
                assert_eq!(session.limit_event_occurred_since(mark), max_count == 1);
            }
        }
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
