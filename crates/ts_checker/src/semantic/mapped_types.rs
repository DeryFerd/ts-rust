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
    CheckFlags, EscapedName, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolData,
    SymbolFlags, SymbolTableId, semantic::PreparedSymbolTable,
};
use xxhash_rust::xxh3::Xxh3;

#[cfg(test)]
use super::conditional_types::cached_source_conditional_instantiation;

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    IndexInfoId, TypeId, TypeMapperId, TypeResolutionTarget, TypeSystemPropertyName,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    conditional_types::{
        ConditionalBranchSource, ConditionalTypeError,
        cached_source_conditional_instantiation_with_array_targets, conditional_alias_projection,
        conditional_query_alias, validate_conditional_reference_result,
    },
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
        cached_instantiation_with_vector, instantiate_type_with_source,
        instantiate_type_with_vector_and_session, instantiated_member_type_matches,
        with_mapped_template_frame,
    },
    instantiated_members::{RecoveredPropertyTypeIdentity, property_recovery_type_identity},
    keyof_types::{
        NongenericKeyofError, cached_nongeneric_keyof_type, plan_nongeneric_keyof_type,
        plan_nongeneric_keyof_type_with_array_targets, resolve_nongeneric_keyof_type,
        resolve_nongeneric_keyof_type_with_session, validate_generic_keyof_index_type,
        validate_source_object_literal_for_keyof,
    },
    links::{MappedSymbolLinks, SymbolNodeLinks, TypeNodeLinks, ValueSymbolLinks},
    mapper::TypeMapperApplication,
    object_aliases::{
        property_object_alias_identity_source_header, validate_property_object_alias_arguments,
    },
    object_members::{
        DeclaredPropertyObjectValidation, validate_resolved_declared_property_object,
    },
    signatures::{IndexFlags, IndexInfo},
    store::{SourceMappedTypeOperands, SourceNodeParent},
    template_types::{MAX_TEMPLATE_UNION_SIZE, StringMappingKind},
    type_nodes::{
        PropTypesKeyAliasKind, PropTypesKeyAliasPlan, SourceMappedLookupReferenceProof,
        type_alias_instantiation_cache_key,
    },
    type_records::{
        CacheHashKey, ConstrainedTypeData, LiteralValue, StructuredTypeData, TypeCacheState,
        TypeData, TypeRecord,
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

/// The validated alias owner and arguments used without resolving mapped values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MappedAliasDisplayIdentity {
    pub(super) symbol: SemanticSymbolId,
    pub(super) arguments: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SupportedMappedAliasKind {
    Selection,
    Homomorphic(MappedTypeModifiers),
}

impl SupportedMappedAliasKind {
    fn validate_request(
        self,
        store: &CanonicalTypeMapperStore,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
    ) -> Result<(), MappedTypeError> {
        match self {
            Self::Selection => validate_pick_mapped_alias_request(
                store,
                alias,
                declared_type,
                parameters,
                arguments,
            )
            .map(|_| ()),
            Self::Homomorphic(modifiers) => validate_homomorphic_mapped_alias_request(
                store,
                alias,
                declared_type,
                parameters,
                arguments,
                modifiers,
            )
            .map(|_| ()),
        }
    }

    fn validate_instantiation(
        self,
        store: &CanonicalTypeMapperStore,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
        instantiated: TypeId,
    ) -> Result<(), MappedTypeError> {
        match self {
            Self::Selection => store.validate_pick_mapped_alias_instantiation(
                alias,
                declared_type,
                parameters,
                arguments,
                instantiated,
            ),
            Self::Homomorphic(modifiers) => store.validate_homomorphic_mapped_alias_instantiation(
                alias,
                declared_type,
                parameters,
                arguments,
                instantiated,
                modifiers,
            ),
        }
    }

    fn instantiate(
        self,
        store: &mut CanonicalTypeMapperStore,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
        session: Option<&mut InstantiationSession>,
    ) -> Result<TypeId, MappedTypeError> {
        match self {
            Self::Selection => {
                store.instantiate_pick_mapped_alias(alias, declared_type, parameters, arguments)
            }
            Self::Homomorphic(modifiers) => store.instantiate_homomorphic_mapped_alias_worker(
                alias,
                declared_type,
                parameters,
                arguments,
                modifiers,
                session,
            ),
        }
    }
}

/// A source-owned mapped alias, without demanding its mapped properties.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SupportedMappedAliasProjection {
    kind: SupportedMappedAliasKind,
    pub(super) type_: TypeId,
    pub(super) alias: SemanticSymbolId,
    pub(super) declared_type: TypeId,
    pub(super) type_parameters: Vec<TypeId>,
    pub(super) arguments: Vec<TypeId>,
    pub(super) identity_symbol: SemanticSymbolId,
    pub(super) identity_arguments: Vec<TypeId>,
}

/// The mapped child of an alias-owned lookup. The alias cache owns the whole
/// lookup, not the unaliased mapped child returned to the instantiator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceMappedLookupProjection {
    pub(super) type_: TypeId,
    pub(super) target: TypeId,
    pub(super) alias: SemanticSymbolId,
    pub(super) declared_lookup: TypeId,
    pub(super) lookup: TypeId,
    pub(super) type_parameters: Vec<TypeId>,
    pub(super) arguments: Vec<TypeId>,
    origin: SourceMappedLookupOrigin,
}

/// The first source producer owns one concrete alias request and its whole lookup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceMappedLookupRequest {
    pub(super) alias: SemanticSymbolId,
    pub(super) declared_lookup: TypeId,
    pub(super) parameter: TypeId,
    pub(super) argument: TypeId,
    pub(super) alias_identity: Option<(SemanticSymbolId, Vec<TypeId>)>,
    pub(super) key: CacheHashKey,
    pub(super) lookup: TypeId,
    pub(super) mapped_type: TypeId,
    pub(super) producer: SourceMappedLookupProducer,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceMappedLookupProducer {
    Direct {
        reference: NodeRef,
        argument: NodeRef,
        binding: SourceMappedLookupReferenceProof,
    },
    OptionalKeys(Box<SourceMappedLookupOptionalProducer>),
}

/// `OptionalKeys` supplies the concrete argument for its real `RequiredKeys<V>` child.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceMappedLookupOptionalProducer {
    pub(super) reference: NodeRef,
    pub(super) argument: NodeRef,
    pub(super) binding: SourceMappedLookupReferenceProof,
    pub(super) alias: SemanticSymbolId,
    pub(super) declared_type: TypeId,
    pub(super) parameter: TypeId,
    pub(super) alias_identity: Option<(SemanticSymbolId, Vec<TypeId>)>,
    pub(super) key: CacheHashKey,
    pub(super) plan: PropTypesKeyAliasPlan,
}

impl SourceMappedLookupRequest {
    #[allow(clippy::too_many_arguments)] // These are the original alias factory inputs and its whole result.
    pub(super) fn for_lookup(
        store: &CanonicalTypeMapperStore,
        alias: SemanticSymbolId,
        declared_lookup: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
        alias_identity: Option<(SemanticSymbolId, Vec<TypeId>)>,
        key: CacheHashKey,
        lookup: TypeId,
        producer: SourceMappedLookupProducer,
    ) -> Result<Option<Self>, MappedTypeError> {
        let invalid = || MappedTypeError::InvalidMappedType(lookup);
        let ([parameter], [argument]) = (parameters, arguments) else {
            return Err(invalid());
        };
        if parameter == argument {
            return if lookup == declared_lookup {
                Ok(None)
            } else {
                Err(invalid())
            };
        }
        let Some(TypeData::IndexedAccess(indexed)) =
            store.type_payload(lookup).map(TypeRecord::data)
        else {
            return Err(invalid());
        };
        let template = |lookup| {
            let TypeData::IndexedAccess(lookup) = store.type_payload(lookup)?.data() else {
                return None;
            };
            let TypeData::Mapped(mapped) = store.type_payload(lookup.object_type)?.data() else {
                return None;
            };
            mapped.template_type
        };
        // The neutral generic producer keeps the original template and its own proof.
        if template(declared_lookup).is_some_and(|original| template(lookup) == Some(original)) {
            if alias_identity.is_some()
                || key != type_alias_instantiation_cache_key(arguments, None)
                || !source_mapped_lookup_identity_projection(store, lookup, None).is_ok_and(
                    |projection| {
                        projection.is_some_and(|projection| {
                            projection.alias == alias
                                && projection.declared_lookup == declared_lookup
                                && projection.type_parameters == parameters
                                && projection.arguments == arguments
                                && projection.lookup == lookup
                        })
                    },
                )
            {
                return Err(invalid());
            }
            return Ok(None);
        }
        Ok(Some(Self {
            alias,
            declared_lookup,
            parameter: *parameter,
            argument: *argument,
            alias_identity,
            key,
            lookup,
            mapped_type: indexed.object_type,
            producer,
        }))
    }

    /// Another source node may reuse the same request without replacing its producer.
    pub(super) fn same_request(&self, other: &Self) -> bool {
        self.alias == other.alias
            && self.declared_lookup == other.declared_lookup
            && self.parameter == other.parameter
            && self.argument == other.argument
            && self.alias_identity == other.alias_identity
            && self.key == other.key
            && self.lookup == other.lookup
            && self.mapped_type == other.mapped_type
    }
}

/// Reads the first producer's exact request. A warm cache cannot recreate it.
pub(super) fn validated_source_mapped_lookup_request(
    store: &CanonicalTypeMapperStore,
    mapped_type: TypeId,
) -> Result<&SourceMappedLookupRequest, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(mapped_type);
    let request = store
        .source_mapped_lookup_request(mapped_type)
        .ok_or_else(invalid)?;
    let origin = source_mapped_lookup_origin(store, mapped_type)?.ok_or_else(invalid)?;
    let identity = request
        .alias_identity
        .as_ref()
        .map(|(owner, arguments)| {
            store
                .symbol_store()
                .assigned_global_symbol_id(*owner)
                .map(|global| (global, arguments.as_slice()))
                .ok_or_else(invalid)
        })
        .transpose()?;
    if request.mapped_type != mapped_type
        || request.alias != origin.alias
        || request.declared_lookup != origin.declared_lookup
        || request.parameter != origin.source
        || request.argument == request.parameter
        || matches!(store.type_payload(mapped_type).map(TypeRecord::data),
            Some(TypeData::Mapped(mapped)) if mapped.template_type == Some(origin.template))
        || request.key != type_alias_instantiation_cache_key(&[request.argument], identity)
        || store
            .type_alias_links(request.alias)
            .and_then(|links| links.instantiations.as_ref())
            .and_then(|entries| entries.get(&request.key))
            != Some(&request.lookup)
        || !matches!(store.type_payload(request.lookup).map(TypeRecord::data),
            Some(TypeData::IndexedAccess(lookup)) if lookup.object_type == mapped_type)
    {
        return Err(invalid());
    }
    store.validate_prop_types_required_keys_instantiation_worker(
        request.alias,
        request.declared_lookup,
        &[request.parameter],
        &[request.argument],
        request.lookup,
        false,
    )?;
    match &request.producer {
        SourceMappedLookupProducer::Direct {
            reference,
            argument,
            binding,
        } => {
            if !binding.matches_source(store, *reference, *argument, request.alias)
                || source_mapped_reference_request_key(
                    store,
                    *reference,
                    *argument,
                    request.alias,
                    request.argument,
                    request.alias_identity.as_ref(),
                    Some(request.lookup),
                )
                .map_err(|_| invalid())?
                .0 != request.key
            {
                return Err(invalid());
            }
        }
        SourceMappedLookupProducer::OptionalKeys(producer) => {
            validate_optional_mapped_lookup_producer(store, request, producer)?;
        }
    }
    Ok(request)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Source nodes, argument identity, and alias identity are one request.
fn source_mapped_reference_request_key(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    argument_node: NodeRef,
    alias: SemanticSymbolId,
    argument: TypeId,
    identity: Option<&(SemanticSymbolId, Vec<TypeId>)>,
    result: Option<TypeId>,
) -> Result<(CacheHashKey, Option<TypeId>), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(result.unwrap_or(argument));
    let children = store
        .source_direct_children(reference)
        .ok_or_else(invalid)?;
    let [name, source_argument] = children.as_slice() else {
        return Err(invalid());
    };
    if store.source_node_kind(reference) != Some(SyntaxKind::TypeReference)
        || !matches!(
            store.source_node_kind(*name),
            Some(SyntaxKind::Identifier | SyntaxKind::QualifiedName)
        )
        || *source_argument != argument_node
        || !source_mapped_argument_is_exact(store, argument_node, argument)
        || store
            .symbol_node_links(reference)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|symbol| symbol != alias))
        || store.type_node_links(reference).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || result.is_some_and(|result| {
                    links.resolved_type.is_some_and(|cached| cached != result)
                })
        })
        || !store.source_symbol_declarations_match(alias)
    {
        return Err(invalid());
    }
    let mut child = reference;
    let mut seen = HashSet::new();
    let source_owner = loop {
        if !seen.insert(child) {
            return Err(invalid());
        }
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(child) else {
            break None;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType)
                if store.source_direct_children(parent).as_deref() == Some(&[child]) =>
            {
                child = parent;
            }
            Some(SyntaxKind::TypeAliasDeclaration)
                if store.source_direct_type_annotation(parent) == Some(child) =>
            {
                let owner = match store.symbol_store().source_binding_symbols(parent) {
                    Some([Some(symbol), _]) => store.get_merged_symbol(symbol),
                    Some([None, _]) => None,
                    None => store.source_declaration_symbol(parent),
                }
                .ok_or_else(invalid)?;
                break Some(owner);
            }
            _ => break None,
        }
    };
    let effective_owner = source_owner.filter(|owner| {
        !source_mapped_alias_is_local(store, *owner) || source_mapped_alias_is_local(store, alias)
    });
    if effective_owner != identity.map(|(owner, _)| *owner) {
        return Err(invalid());
    }
    let identity = identity
        .map(|(owner, arguments)| {
            let header = property_object_alias_identity_source_header(store, *owner)
                .map_err(|_| invalid())?;
            if header.parameters.len() != arguments.len()
                || header
                    .parameters
                    .iter()
                    .zip(arguments)
                    .any(|((_, owner), argument)| {
                        cached_ordinary_type_parameter_owner(store, *argument) != Some(*owner)
                    })
            {
                return Err(invalid());
            }
            store
                .symbol_store()
                .assigned_global_symbol_id(*owner)
                .map(|global| (global, arguments.as_slice()))
                .ok_or_else(invalid)
        })
        .transpose()?;
    let key = type_alias_instantiation_cache_key(&[argument], identity);
    let cached = store
        .type_alias_links(alias)
        .and_then(|links| links.instantiations.as_ref())
        .and_then(|entries| entries.get(&key))
        .copied();
    let source_result = store
        .type_node_links(reference)
        .and_then(|links| links.resolved_type);
    if result.is_some_and(|result| cached != Some(result))
        || source_result.is_some_and(|source| cached != Some(source))
    {
        return Err(invalid());
    }
    Ok((key, cached))
}

fn source_mapped_argument_is_exact(
    store: &CanonicalTypeMapperStore,
    mut node: NodeRef,
    argument: TypeId,
) -> bool {
    let mut seen = HashSet::new();
    while seen.insert(node) {
        if store.source_node_kind(node) != Some(SyntaxKind::ParenthesizedType) {
            return store.source_direct_type_annotation_is_exact(node, argument);
        }
        if store.type_node_links(node).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != argument)
        }) || store
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return false;
        }
        let Some(children) = store.source_direct_children(node) else {
            return false;
        };
        let [child] = children.as_slice() else {
            return false;
        };
        node = *child;
    }
    false
}

/// A cached source reference must still identify the first producer's request.
pub(super) fn source_mapped_lookup_reference_matches(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    lookup: TypeId,
) -> bool {
    let Some(TypeData::IndexedAccess(indexed)) = store.type_payload(lookup).map(TypeRecord::data)
    else {
        return false;
    };
    let Some(children) = store.source_direct_children(reference) else {
        return false;
    };
    let [_, argument] = children.as_slice() else {
        return false;
    };
    if store
        .source_mapped_lookup_request(indexed.object_type)
        .is_none()
    {
        let Ok(Some(projection)) = source_mapped_lookup_identity_projection(store, lookup, None)
        else {
            return false;
        };
        let [source] = projection.arguments.as_slice() else {
            return false;
        };
        return projection.lookup == lookup
            && source_mapped_reference_request_key(
                store,
                reference,
                *argument,
                projection.alias,
                *source,
                None,
                Some(lookup),
            )
            .is_ok_and(|(key, _)| key == type_alias_instantiation_cache_key(&[*source], None));
    }
    let Ok(request) = validated_source_mapped_lookup_request(store, indexed.object_type) else {
        return false;
    };
    request.lookup == lookup
        && source_mapped_reference_request_key(
            store,
            reference,
            *argument,
            request.alias,
            request.argument,
            request.alias_identity.as_ref(),
            Some(lookup),
        )
        .is_ok_and(|(key, _)| key == request.key)
}

fn source_mapped_alias_is_local(store: &CanonicalTypeMapperStore, alias: SemanticSymbolId) -> bool {
    let Some([declaration]) = store.symbol(alias).and_then(|owner| owner.declarations()) else {
        return false;
    };
    let mut node = *declaration;
    let mut seen = HashSet::new();
    while seen.insert(node) {
        if matches!(
            store.source_node_kind(node),
            Some(
                SyntaxKind::FunctionDeclaration
                    | SyntaxKind::FunctionExpression
                    | SyntaxKind::ArrowFunction
                    | SyntaxKind::MethodDeclaration
                    | SyntaxKind::GetAccessor
                    | SyntaxKind::SetAccessor
                    | SyntaxKind::Constructor
            )
        ) {
            return true;
        }
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) else {
            return false;
        };
        node = parent;
    }
    false
}

#[allow(clippy::too_many_lines)] // The inner request and the actual outer source form one prefix proof.
fn validate_optional_mapped_lookup_producer(
    store: &CanonicalTypeMapperStore,
    request: &SourceMappedLookupRequest,
    producer: &SourceMappedLookupOptionalProducer,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(request.mapped_type);
    let header = property_object_alias_identity_source_header(store, producer.alias)
        .map_err(|_| invalid())?;
    let [(parameter_node, parameter_owner)] = header.parameters.as_slice() else {
        return Err(invalid());
    };
    let source = producer.plan;
    let links = store.type_alias_links(producer.alias).ok_or_else(invalid)?;
    if request.alias_identity.is_some()
        || !producer.binding.matches_source(
            store,
            producer.reference,
            producer.argument,
            producer.alias,
        )
        || source.kind != PropTypesKeyAliasKind::Optional
        || source.required_alias != Some(request.alias)
        || source.parameter != *parameter_owner
        || cached_ordinary_type_parameter_owner(store, producer.parameter) != Some(*parameter_owner)
        || store.source_node_parent(*parameter_node)
            != Some(SourceNodeParent::Parent(header.alias_declaration))
        || store.source_direct_type_annotation(header.alias_declaration) != Some(source.body)
        || store.get_parent_of_symbol(producer.alias) != Some(source.module)
        || store.get_parent_of_symbol(request.alias) != Some(source.module)
        || links.declared_type != Some(producer.declared_type)
        || links.type_parameters.as_deref() != Some(&[producer.parameter])
        || !store.source_direct_type_annotation_is_exact(source.body, producer.declared_type)
    {
        return Err(invalid());
    }
    let children = store
        .source_direct_children(source.body)
        .ok_or_else(invalid)?;
    let [_, keys, required] = children.as_slice() else {
        return Err(invalid());
    };
    let required_children = store
        .source_direct_children(*required)
        .ok_or_else(invalid)?;
    let [_, parameter] = required_children.as_slice() else {
        return Err(invalid());
    };
    if store.source_node_kind(source.body) != Some(SyntaxKind::TypeReference)
        || store
            .symbol_node_links(source.body)
            .and_then(|links| links.resolved_symbol)
            != source.exclude_alias
        || store.source_type_operator(*keys) != Some(SyntaxKind::KeyOfKeyword)
        || store
            .source_direct_type_annotation(*keys)
            .is_none_or(|node| {
                !store.source_direct_type_annotation_is_exact(node, producer.parameter)
            })
        || store.source_node_kind(*required) != Some(SyntaxKind::TypeReference)
        || store.symbol_node_links(*required)
            != Some(&SymbolNodeLinks {
                resolved_symbol: Some(request.alias),
            })
        || !store.source_direct_type_annotation_is_exact(*parameter, producer.parameter)
    {
        return Err(invalid());
    }
    let required_lookup = store
        .type_node_links(*required)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    if store
        .type_alias_links(request.alias)
        .and_then(|links| links.instantiations.as_ref())
        .and_then(|entries| {
            entries.get(&type_alias_instantiation_cache_key(
                &[producer.parameter],
                None,
            ))
        })
        != Some(&required_lookup)
    {
        return Err(invalid());
    }
    store.validate_prop_types_required_keys_instantiation_worker(
        request.alias,
        request.declared_lookup,
        &[request.parameter],
        &[producer.parameter],
        required_lookup,
        false,
    )?;
    let (key, result) = source_mapped_reference_request_key(
        store,
        producer.reference,
        producer.argument,
        producer.alias,
        request.argument,
        producer.alias_identity.as_ref(),
        None,
    )
    .map_err(|_| invalid())?;
    if key != producer.key {
        return Err(invalid());
    }
    // The inner request exists before the fallible outer Exclude result.
    if let Some(result) = result {
        let (Some(TypeData::Conditional(original)), Some(TypeData::Conditional(result))) = (
            store
                .type_payload(producer.declared_type)
                .map(TypeRecord::data),
            store.type_payload(result).map(TypeRecord::data),
        ) else {
            return Err(invalid());
        };
        let key_plan =
            plan_nongeneric_keyof_type(store, request.argument).map_err(|_| invalid())?;
        let keys = cached_nongeneric_keyof_type(store, &key_plan).map_err(|_| invalid())?;
        if original.root != result.root
            || keys != Some(result.check_type)
            || result.extends_type != request.lookup
        {
            return Err(invalid());
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceMappedLookupOrigin {
    declaration: NodeRef,
    target: TypeId,
    alias: SemanticSymbolId,
    declared_lookup: TypeId,
    source: TypeId,
    key: TypeId,
    key_symbol: SemanticSymbolId,
    template: TypeId,
}

/// Accepts either the mapped child or its whole source lookup. It reads only
/// the exact plain alias key. Forwarding keys need a separate source proof.
pub(super) fn source_mapped_lookup_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<SourceMappedLookupProjection>, MappedTypeError> {
    let Some((projection, warm)) =
        source_mapped_lookup_projection_worker(store, type_, array_targets)?
    else {
        return Ok(None);
    };
    if warm {
        return Err(MappedTypeError::UnsupportedTemplate(
            projection.origin.template,
        ));
    }
    Ok(Some(projection))
}

/// Retained callable evidence checks identity before query readiness. This
/// reader cannot authorize instantiation or mapped member demand.
pub(super) fn source_mapped_lookup_identity_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<SourceMappedLookupProjection>, MappedTypeError> {
    source_mapped_lookup_projection_worker(store, type_, array_targets)
        .map(|projection| projection.map(|(projection, _)| projection))
}

fn source_mapped_lookup_projection_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<(SourceMappedLookupProjection, bool)>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let (mapped_type, requested_lookup) = match record.data() {
        TypeData::Mapped(_) => (type_, None),
        TypeData::IndexedAccess(indexed)
            if matches!(
                store
                    .type_payload(indexed.object_type)
                    .map(TypeRecord::data),
                Some(TypeData::Mapped(_))
            ) =>
        {
            (indexed.object_type, Some(type_))
        }
        _ => return Ok(None),
    };
    let Some(origin) = source_mapped_lookup_origin(store, mapped_type)? else {
        return Ok(None);
    };
    let TypeData::Mapped(mapped) = store.type_payload(mapped_type).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    let argument = if mapped_type == origin.target {
        origin.source
    } else {
        let substitution = mapped.object.mapper.ok_or_else(invalid)?;
        let Some(TypeMapperApplication::Composite { second, .. }) =
            store.mapper_application(substitution, origin.key)
        else {
            return Err(invalid());
        };
        store.map_type(second, origin.source).ok_or_else(invalid)?
    };
    validate_source_mapped_lookup_argument(store, origin, argument, array_targets)?;
    let key = type_alias_instantiation_cache_key(&[argument], None);
    let cached = store
        .type_alias_links(origin.alias)
        .and_then(|links| links.instantiations.as_ref())
        .and_then(|entries| entries.get(&key))
        .copied();
    let lookup = if argument == origin.source {
        if cached.is_some_and(|cached| cached != origin.declared_lookup) {
            return Err(invalid());
        }
        origin.declared_lookup
    } else {
        cached.ok_or_else(invalid)?
    };
    if requested_lookup.is_some_and(|requested| requested != lookup)
        || validate_source_mapped_lookup_instance(store, origin, argument, lookup, array_targets)?
            != mapped_type
    {
        return Err(invalid());
    }
    let warm = source_mapped_lookup_state_is_warm(store, origin, mapped_type)?;
    Ok(Some((
        SourceMappedLookupProjection {
            type_: mapped_type,
            target: origin.target,
            alias: origin.alias,
            declared_lookup: origin.declared_lookup,
            lookup,
            type_parameters: vec![origin.source],
            arguments: vec![argument],
            origin,
        },
        warm,
    )))
}

fn source_mapped_lookup_origin(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<SourceMappedLookupOrigin>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Ok(None);
    };
    let source_record = store
        .type_payload(mapped.object.target.unwrap_or(type_))
        .ok_or_else(invalid)?;
    let TypeData::Mapped(source_mapped) = source_record.data() else {
        return Err(invalid());
    };
    let declaration = source_mapped.declaration.ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(lookup_node)) = store.source_node_parent(declaration) else {
        return Ok(None);
    };
    if store.source_node_kind(lookup_node) != Some(SyntaxKind::IndexedAccessType) {
        return Ok(None);
    }
    let Some(SourceNodeParent::Parent(alias_declaration)) = store.source_node_parent(lookup_node)
    else {
        return Ok(None);
    };
    if store.source_node_kind(alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration) {
        return Ok(None);
    }
    // The first lookup family has no captured enclosing type parameters.
    let mut parent = alias_declaration;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(parent) {
            return Err(invalid());
        }
        match store.source_node_parent(parent).ok_or_else(invalid)? {
            SourceNodeParent::Root => break,
            SourceNodeParent::Parent(ancestor) => {
                if !matches!(
                    store.source_node_kind(ancestor),
                    Some(
                        SyntaxKind::SourceFile
                            | SyntaxKind::ModuleBlock
                            | SyntaxKind::ModuleDeclaration
                    )
                ) {
                    return Ok(None);
                }
                parent = ancestor;
            }
        }
    }
    let operands = store
        .source_mapped_type_operands(declaration)
        .ok_or_else(invalid)?;
    if operands.name_type.is_some()
        || store.source_mapped_type_modifiers(declaration) != Some(MappedTypeModifiers::NONE)
        || operands
            .template
            .and_then(|node| store.source_node_kind(node))
            != Some(SyntaxKind::ConditionalType)
        || store.source_type_operator(operands.constraint) != Some(SyntaxKind::KeyOfKeyword)
    {
        return Ok(None);
    }
    let lookup_children = store
        .source_direct_children(lookup_node)
        .ok_or_else(invalid)?;
    let [object_node, index_node] = lookup_children.as_slice() else {
        return Err(invalid());
    };
    if *object_node != declaration
        || store.source_type_operator(*index_node) != Some(SyntaxKind::KeyOfKeyword)
    {
        return Ok(None);
    }
    let alias = match store
        .symbol_store()
        .source_binding_symbols(alias_declaration)
    {
        Some([Some(symbol), _]) => store.get_merged_symbol(symbol),
        Some([None, _]) => None,
        None => store.source_declaration_symbol(alias_declaration),
    }
    .ok_or_else(invalid)?;
    let header =
        property_object_alias_identity_source_header(store, alias).map_err(|_| invalid())?;
    let [(source_declaration, source_symbol)] = header.parameters.as_slice() else {
        return Ok(None);
    };
    let source_children = store
        .source_direct_children(*source_declaration)
        .ok_or_else(invalid)?;
    if !matches!(source_children.as_slice(), [name] if store.source_node_kind(*name) == Some(SyntaxKind::Identifier))
    {
        return Ok(None);
    }
    let links = store.type_alias_links(alias).ok_or_else(invalid)?;
    let declared_lookup = links.declared_type.ok_or_else(invalid)?;
    let Some([source]) = links.type_parameters.as_deref() else {
        return Err(invalid());
    };
    let source = *source;
    let declared_record = store.type_payload(declared_lookup).ok_or_else(invalid)?;
    let TypeData::IndexedAccess(declared) = declared_record.data() else {
        return Err(invalid());
    };
    let target = declared.object_type;
    let target_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Mapped(original) = target_record.data() else {
        return Err(invalid());
    };
    let constraint = original.constraint_type.ok_or_else(invalid)?;
    let template = original.template_type.ok_or_else(invalid)?;
    let key = original.type_parameter.ok_or_else(invalid)?;
    let key_symbol = cached_ordinary_type_parameter_owner(store, key).ok_or_else(invalid)?;
    let source_name = source_type_parameter_name(store, *source_declaration).ok_or_else(invalid)?;
    let key_name =
        source_type_parameter_name(store, operands.type_parameter).ok_or_else(invalid)?;
    let constraint_target = store
        .source_direct_type_annotation(operands.constraint)
        .ok_or_else(invalid)?;
    let index_target = store
        .source_direct_type_annotation(*index_node)
        .ok_or_else(invalid)?;
    let template_node = operands.template.ok_or_else(invalid)?;
    let conditional_children = store
        .source_direct_children(template_node)
        .ok_or_else(invalid)?;
    let [check_node, extends_node, _, _] = conditional_children.as_slice() else {
        return Err(invalid());
    };
    if store.source_node_kind(*check_node) != Some(SyntaxKind::IndexedAccessType) {
        return Ok(None);
    }
    let check_children = store
        .source_direct_children(*check_node)
        .ok_or_else(invalid)?;
    let [check_source, check_key] = check_children.as_slice() else {
        return Err(invalid());
    };
    if !source_type_parameter_reference(store, constraint_target, source_name)
        || !source_type_parameter_reference(store, index_target, source_name)
        || !source_type_parameter_reference(store, *check_source, source_name)
        || !source_type_parameter_reference(store, *check_key, key_name)
    {
        return Ok(None);
    }
    validate_source_mapped_relation_identity(store, target, false)?;
    let template_record = store.type_payload(template).ok_or_else(invalid)?;
    let TypeData::Conditional(conditional) = template_record.data() else {
        return Err(invalid());
    };
    let TypeData::IndexedAccess(check) = store
        .type_payload(conditional.check_type)
        .ok_or_else(invalid)?
        .data()
    else {
        return Err(invalid());
    };
    if header.alias_declaration != alias_declaration
        || store.source_direct_type_annotation(alias_declaration) != Some(lookup_node)
        || links.is_constructor_declared_property
        || cached_ordinary_type_parameter_owner(store, source) != Some(*source_symbol)
        || links
            .instantiations
            .as_ref()
            .and_then(|entries| entries.get(&type_list_key(&[source])))
            != Some(&declared_lookup)
        || !store.source_direct_type_annotation_is_exact(lookup_node, declared_lookup)
        || !store.source_direct_type_annotation_is_exact(*index_node, constraint)
        || !store.source_direct_type_annotation_is_exact(constraint_target, source)
        || !store.source_direct_type_annotation_is_exact(index_target, source)
        || !store.source_direct_type_annotation_is_exact(*check_node, conditional.check_type)
        || !store.source_direct_type_annotation_is_exact(*check_source, source)
        || !store.source_direct_type_annotation_is_exact(*check_key, key)
        || !store.source_direct_type_annotation_is_exact(*extends_node, conditional.extends_type)
        || store
            .symbol(key_symbol)
            .and_then(|symbol| symbol.declarations())
            != Some(&[operands.type_parameter][..])
        || original.declaration != Some(declaration)
        || original.modifiers_type != Some(source)
        || validate_generic_keyof_index_type(store, constraint).map_err(|_| invalid())? != source
        || declared.index_type != constraint
        || validate_source_mapped_lookup_index(store, declared_lookup, target, constraint).is_err()
        || check.object_type != source
        || check.index_type != key
        || validate_source_mapped_lookup_index(store, conditional.check_type, source, key).is_err()
        || conditional.mapper.is_some()
        || conditional.combined_mapper.is_some()
        || template_record.object_flags() != ObjectFlags::NONE
        || store
            .conditional_root(conditional.root)
            .is_none_or(|root| root.node() != template_node)
        || conditional_alias_projection(store, template)
            .map_err(|_| invalid())?
            .is_some()
        || conditional_query_alias(store, template_node)
            .map_err(|_| invalid())?
            .is_some()
        || !unresolved_mapped_structure_is_valid(store, target, &original.object.structured)
        || target_record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    {
        return Err(invalid());
    }
    Ok(Some(SourceMappedLookupOrigin {
        declaration,
        target,
        alias,
        declared_lookup,
        source,
        key,
        key_symbol,
        template,
    }))
}

fn source_mapped_lookup_conditional_is_cold(
    conditional: &super::type_records::ConditionalTypeData,
) -> bool {
    conditional.constrained == ConstrainedTypeData::default()
        && conditional.resolved_true_type.is_none()
        && conditional.resolved_false_type.is_none()
        && conditional.resolved_inferred_true_type.is_none()
        && conditional.resolved_default_constraint.is_none()
        && conditional.resolved_constraint_of_distributive.is_none()
}

fn source_mapped_lookup_conditional_is_warm(
    store: &CanonicalTypeMapperStore,
    origin: SourceMappedLookupOrigin,
    template: TypeId,
) -> Result<bool, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(template);
    let TypeData::Conditional(conditional) =
        store.type_payload(template).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    for cached in [
        conditional.constrained.resolved_base_constraint,
        conditional.resolved_true_type,
        conditional.resolved_false_type,
        conditional.resolved_inferred_true_type,
        conditional.resolved_default_constraint,
        conditional.resolved_constraint_of_distributive,
    ]
    .into_iter()
    .flatten()
    {
        if store.type_payload(cached).is_none() {
            return Err(invalid());
        }
    }
    let node = store
        .source_mapped_type_operands(origin.declaration)
        .and_then(|operands| operands.template)
        .ok_or_else(invalid)?;
    let children = store.source_direct_children(node).ok_or_else(invalid)?;
    let [_, _, true_node, false_node] = children.as_slice() else {
        return Err(invalid());
    };
    for (branch, cached) in [
        (*true_node, conditional.resolved_true_type),
        (*false_node, conditional.resolved_false_type),
        (*true_node, conditional.resolved_inferred_true_type),
    ] {
        let Some(cached) = cached else { continue };
        // Keyword branches are invariant under the mapper. An original source
        // branch can also have its own published identity. Missing branch
        // queries remain missing, even when a caller filled a branch cache.
        let known = store
            .source_node_kind(branch)
            .is_some_and(SyntaxKind::is_keyword_type)
            || conditional.mapper.is_none()
                && store
                    .type_node_links(branch)
                    .is_some_and(|links| links.resolved_type.is_some());
        if known && !store.source_direct_type_annotation_is_exact(branch, cached) {
            return Err(invalid());
        }
    }
    if conditional.combined_mapper.is_none()
        && conditional
            .resolved_inferred_true_type
            .is_some_and(|inferred| conditional.resolved_true_type != Some(inferred))
    {
        return Err(invalid());
    }
    Ok(!source_mapped_lookup_conditional_is_cold(conditional))
}

fn source_mapped_lookup_state_is_warm(
    store: &CanonicalTypeMapperStore,
    origin: SourceMappedLookupOrigin,
    mapped_type: TypeId,
) -> Result<bool, MappedTypeError> {
    let Some(TypeData::Mapped(mapped)) = store.type_payload(mapped_type).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidMappedType(mapped_type));
    };
    let template = mapped
        .template_type
        .ok_or(MappedTypeError::InvalidMappedType(mapped_type))?;
    let original_warm = source_mapped_lookup_conditional_is_warm(store, origin, origin.template)?;
    let instance_warm = template != origin.template
        && source_mapped_lookup_conditional_is_warm(store, origin, template)?;
    Ok(original_warm || instance_warm)
}

fn validate_source_mapped_lookup_cold_state(
    store: &CanonicalTypeMapperStore,
    origin: SourceMappedLookupOrigin,
    mapped_type: TypeId,
) -> Result<(), MappedTypeError> {
    if source_mapped_lookup_state_is_warm(store, origin, mapped_type)? {
        return Err(MappedTypeError::UnsupportedTemplate(origin.template));
    }
    Ok(())
}

fn validate_source_mapped_lookup_index(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    object: TypeId,
    index: TypeId,
) -> Result<(), MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::IndexedAccess(indexed) = record.data() else {
        return Err(invalid());
    };
    let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if record.flags() != TypeFlags::INDEXED_ACCESS
        || record.object_flags() != ObjectFlags::NONE && record.object_flags() != variable_flags
        || record.alias().is_some()
        || record.symbol().is_some()
        || indexed.object_type != object
        || indexed.index_type != index
        || indexed.access_flags != AccessFlags::NONE
        || indexed.constrained != ConstrainedTypeData::default()
        || cached_deferred_indexed_access_type(store, object, index, AccessFlags::NONE)
            != Ok(Some(type_))
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_source_mapped_lookup_argument(
    store: &CanonicalTypeMapperStore,
    origin: SourceMappedLookupOrigin,
    argument: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), MappedTypeError> {
    validate_supported_mapped_alias_source(store, argument, array_targets)?;
    if cached_ordinary_type_parameter_owner(store, argument).is_none() {
        return Err(MappedTypeError::UnsupportedTemplate(origin.template));
    }
    validate_property_object_alias_arguments(store, &[argument])
        .map_err(|_| MappedTypeError::InvalidSource(argument))?;
    Ok(())
}

fn validate_source_mapped_lookup_instance(
    store: &CanonicalTypeMapperStore,
    origin: SourceMappedLookupOrigin,
    argument: TypeId,
    lookup: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(lookup);
    validate_source_mapped_lookup_argument(store, origin, argument, array_targets)?;
    if argument == origin.source {
        return if lookup == origin.declared_lookup {
            Ok(origin.target)
        } else {
            Err(invalid())
        };
    }
    let key_plan = plan_nongeneric_keyof_type_with_array_targets(store, argument, array_targets)
        .map_err(|error| mapped_keyof_error(argument, error))?;
    let constraint = cached_nongeneric_keyof_type(store, &key_plan)
        .map_err(|error| mapped_keyof_error(argument, error))?
        .ok_or_else(invalid)?;
    let TypeData::IndexedAccess(indexed) = store.type_payload(lookup).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    let mapped_type = indexed.object_type;
    validate_source_mapped_lookup_index(store, lookup, mapped_type, constraint)?;
    let record = store.type_payload(mapped_type).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Err(invalid());
    };
    let parameter = mapped.type_parameter.ok_or_else(invalid)?;
    let substitution = mapped.object.mapper.ok_or_else(invalid)?;
    let Some(TypeMapperApplication::Composite { first, second }) =
        store.mapper_application(substitution, origin.key)
    else {
        return Err(invalid());
    };
    let allowed = ObjectFlags::INSTANTIATED_MAPPED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::PROPAGATING_FLAGS;
    if record.flags() != TypeFlags::OBJECT
        || !record
            .object_flags()
            .contains(ObjectFlags::INSTANTIATED_MAPPED)
        || !(record.object_flags() & !allowed).is_empty()
        || record.alias().is_some()
        || record.symbol()
            != store
                .type_payload(origin.target)
                .and_then(TypeRecord::symbol)
        || mapped.declaration != Some(origin.declaration)
        || mapped.object.target != Some(origin.target)
        || mapped.object.instantiations != TypeCacheState::Unallocated
        || mapped.constraint_type != Some(constraint)
        || mapped.modifiers_type != Some(argument)
        || mapped.name_type.is_some()
        || mapped.contains_error
        || parameter == origin.key
        || mapped_type_parameter_owner(store, mapped_type, parameter) != Some(origin.key_symbol)
        || store.type_mapper_has_exact_endpoints(first, &[origin.key], &[parameter]) != Some(true)
        || store.type_mapper_has_exact_endpoints(second, &[origin.source], &[argument])
            != Some(true)
        || !unresolved_mapped_structure_is_valid(store, mapped_type, &mapped.object.structured)
    {
        return Err(invalid());
    }
    let template = mapped.template_type.ok_or_else(invalid)?;
    if template != origin.template {
        // Existing source queries produced this exact closed child before the
        // generic instantiator could retain the original template. This proof
        // does not admit the raw child to general conditional instantiation.
        let template_record = store.type_payload(template).ok_or_else(invalid)?;
        let TypeData::Conditional(conditional) = template_record.data() else {
            return Err(invalid());
        };
        let TypeData::Conditional(original) = store
            .type_payload(origin.template)
            .ok_or_else(invalid)?
            .data()
        else {
            return Err(invalid());
        };
        if template_record.flags() != TypeFlags::CONDITIONAL
            || template_record.object_flags() != ObjectFlags::NONE
            || template_record.alias().is_some()
            || template_record.symbol().is_some()
            || conditional.root != original.root
            || conditional.extends_type != original.extends_type
            || conditional.mapper != Some(substitution)
            || conditional.combined_mapper.is_some()
        {
            return Err(invalid());
        }
        validate_source_mapped_lookup_index(store, conditional.check_type, argument, parameter)?;
    }
    Ok(mapped_type)
}

fn validate_source_mapped_lookup_instance_request(
    store: &CanonicalTypeMapperStore,
    projection: &SourceMappedLookupProjection,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, MappedTypeError> {
    if source_mapped_lookup_projection(store, projection.type_, array_targets)?.as_ref()
        != Some(projection)
    {
        return Err(MappedTypeError::InvalidMappedType(projection.type_));
    }
    let [argument] = arguments else {
        return Err(MappedTypeError::InvalidMappedType(projection.type_));
    };
    validate_source_mapped_lookup_argument(store, projection.origin, *argument, array_targets)?;
    Ok(*argument)
}

/// Reads the complete lookup entry without creating its mapped child or keys.
pub(super) fn cached_source_mapped_lookup_instance(
    store: &CanonicalTypeMapperStore,
    projection: &SourceMappedLookupProjection,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, MappedTypeError> {
    let argument = validate_source_mapped_lookup_instance_request(
        store,
        projection,
        arguments,
        array_targets,
    )?;
    let key = type_alias_instantiation_cache_key(arguments, None);
    let cached = store
        .type_alias_links(projection.alias)
        .and_then(|links| links.instantiations.as_ref())
        .and_then(|entries| entries.get(&key))
        .copied();
    if argument == projection.origin.source && cached.is_none() {
        return Ok(Some(projection.target));
    }
    cached
        .map(|lookup| {
            let mapped = validate_source_mapped_lookup_instance(
                store,
                projection.origin,
                argument,
                lookup,
                array_targets,
            )?;
            validate_source_mapped_lookup_cold_state(store, projection.origin, mapped)?;
            Ok(mapped)
        })
        .transpose()
}

/// Argument mapping and limit recovery stay in the caller's normal frame.
/// This producer publishes one whole plain-key lookup with a cold template.
pub(super) fn instantiate_source_mapped_lookup_instance(
    store: &mut CanonicalTypeMapperStore,
    projection: &SourceMappedLookupProjection,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, MappedTypeError> {
    if let Some(cached) =
        cached_source_mapped_lookup_instance(store, projection, arguments, array_targets)?
    {
        return Ok(cached);
    }
    let origin = projection.origin;
    let argument = arguments[0];
    let key_plan = plan_nongeneric_keyof_type_with_array_targets(store, argument, array_targets)
        .map_err(|error| mapped_keyof_error(argument, error))?;
    cached_nongeneric_keyof_type(store, &key_plan)
        .map_err(|error| mapped_keyof_error(argument, error))?;
    let mut links = store
        .type_alias_links(origin.alias)
        .cloned()
        .ok_or(MappedTypeError::InvalidSymbol(origin.alias))?;
    links
        .instantiations
        .as_mut()
        .ok_or(MappedTypeError::InvalidSymbol(origin.alias))?
        .try_reserve(1)
        .map_err(|_| MappedTypeError::Capacity)?;
    if !store.try_reserve_types(3) || !store.try_reserve_mappers(3) {
        return Err(MappedTypeError::Capacity);
    }
    let constraint = resolve_nongeneric_keyof_type(store, &key_plan)
        .map_err(|error| mapped_keyof_error(argument, error))?;
    let outer_mapper = store
        .new_type_mapper(vec![origin.source], vec![argument])
        .ok_or(MappedTypeError::InvalidMappedType(origin.target))?;
    let parameter = store
        .alloc_type_parameter(Some(origin.key_symbol))
        .ok_or(MappedTypeError::Capacity)?;
    let key_mapper = store
        .new_simple_type_mapper(origin.key, parameter)
        .ok_or(MappedTypeError::InvalidTypeParameter(origin.key))?;
    let substitution = store
        .combine_type_mappers(Some(key_mapper), outer_mapper)
        .ok_or(MappedTypeError::InvalidMappedType(origin.target))?;
    if !store.set_type_parameter_resolution(
        parameter,
        Some(constraint),
        Some(origin.key),
        Some(substitution),
        None,
    ) {
        return Err(MappedTypeError::InvalidTypeParameter(parameter));
    }
    let symbol = store
        .type_payload(origin.target)
        .and_then(TypeRecord::symbol)
        .ok_or(MappedTypeError::InvalidMappedType(origin.target))?;
    let mapped = store
        .alloc_mapped_type(
            ObjectFlags::INSTANTIATED_MAPPED,
            Some(symbol),
            Some(origin.declaration),
        )
        .ok_or(MappedTypeError::Capacity)?;
    if !store.set_object_target_and_mapper(mapped, Some(origin.target), Some(substitution))
        || !store.set_mapped_type_resolution(
            mapped,
            Some(origin.declaration),
            Some(parameter),
            Some(constraint),
            None,
            Some(origin.template),
            Some(argument),
            None,
            false,
        )
    {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    }
    let lookup = store
        .alloc_indexed_access_type(mapped, constraint, AccessFlags::NONE)
        .ok_or(MappedTypeError::Capacity)?;
    validate_source_mapped_lookup_instance(store, origin, argument, lookup, array_targets)?;
    validate_source_mapped_lookup_cold_state(store, origin, mapped)?;
    if links
        .instantiations
        .as_mut()
        .ok_or(MappedTypeError::InvalidSymbol(origin.alias))?
        .insert(type_alias_instantiation_cache_key(arguments, None), lookup)
        .is_some()
        || !store.set_type_alias_links(origin.alias, links)
    {
        return Err(MappedTypeError::InvalidMappedType(mapped));
    }
    Ok(mapped)
}

/// Reuses the installed selection and homomorphic alias producers.
/// Other mapped families keep their existing query and instantiation paths.
pub(super) fn supported_mapped_alias_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    supported_mapped_alias_projection_worker(store, type_, array_targets, &mut HashSet::new())
}

fn supported_mapped_alias_projection_worker(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    if !active.insert(type_) {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    let result = supported_mapped_alias_projection_inner(store, type_, array_targets, active);
    active.remove(&type_);
    result
}

fn supported_mapped_alias_projection_inner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<Option<SupportedMappedAliasProjection>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let TypeData::Mapped(mapped) = record.data() else {
        return Ok(None);
    };
    let declaration = mapped.declaration.ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(alias_declaration)) = store.source_node_parent(declaration)
    else {
        return Ok(None);
    };
    if store.source_node_kind(alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration) {
        return Ok(None);
    }
    let operands = store
        .source_mapped_type_operands(declaration)
        .ok_or_else(invalid)?;
    let source_parameters = store
        .source_direct_children(alias_declaration)
        .ok_or_else(invalid)?
        .into_iter()
        .filter(|node| store.source_node_kind(*node) == Some(SyntaxKind::TypeParameter))
        .collect::<Vec<_>>();
    if operands.name_type.is_some() {
        return Ok(None);
    }
    // Select from source syntax. Damaged template caches must not change families.
    let (kind, constraint_node, constraint_target) = match source_parameters.as_slice() {
        [_, _]
            if store.source_mapped_type_modifiers(declaration)
                == Some(MappedTypeModifiers::NONE)
                && store.source_node_kind(operands.constraint)
                    == Some(SyntaxKind::TypeReference)
                && operands
                    .template
                    .and_then(|node| store.source_node_kind(node))
                    == Some(SyntaxKind::IndexedAccessType) =>
        {
            let Some((constraint, target)) =
                selection_alias_source_constraint(store, &source_parameters, operands)
            else {
                return Ok(None);
            };
            (SupportedMappedAliasKind::Selection, constraint, target)
        }
        [source_parameter] => {
            let Some((constraint, target)) =
                homomorphic_alias_source_constraint(store, *source_parameter, operands)
            else {
                return Ok(None);
            };
            let modifiers = store
                .source_mapped_type_modifiers(declaration)
                .ok_or_else(invalid)?;
            if !modifiers.valid() {
                return Err(invalid());
            }
            (
                SupportedMappedAliasKind::Homomorphic(modifiers),
                constraint,
                target,
            )
        }
        _ => return Ok(None),
    };
    let alias = store
        .source_declaration_symbol(alias_declaration)
        .ok_or_else(invalid)?;
    if !store.source_symbol_declarations_match(alias)
        || store.source_direct_type_annotation(alias_declaration) != Some(declaration)
    {
        return Err(invalid());
    }
    let links = store.type_alias_links(alias).ok_or_else(invalid)?;
    let declared_type = links.declared_type.ok_or_else(invalid)?;
    let type_parameters = links.type_parameters.as_deref().ok_or_else(invalid)?;
    if type_parameters.len() != source_parameters.len()
        || type_parameters
            .iter()
            .zip(&source_parameters)
            .any(|(type_, declaration)| {
                cached_ordinary_type_parameter_owner(store, *type_).is_none_or(|owner| {
                    store.symbol(owner).and_then(|owner| owner.declarations())
                        != Some(&[*declaration][..])
                })
            })
        || mapped.object.target.unwrap_or(type_) != declared_type
    {
        return Err(invalid());
    }
    let constraint = match kind {
        SupportedMappedAliasKind::Selection => {
            let Some(TypeData::TypeParameter(key)) =
                store.type_payload(type_parameters[1]).map(TypeRecord::data)
            else {
                return Err(invalid());
            };
            key.constraint.ok_or_else(invalid)?
        }
        SupportedMappedAliasKind::Homomorphic(_) => {
            let Some(TypeData::Mapped(original)) =
                store.type_payload(declared_type).map(TypeRecord::data)
            else {
                return Err(invalid());
            };
            original.constraint_type.ok_or_else(invalid)?
        }
    };
    if validate_generic_keyof_index_type(store, constraint).map_err(|_| invalid())?
        != type_parameters[0]
        || !store.source_direct_type_annotation_is_exact(constraint_node, constraint)
        || !store.source_direct_type_annotation_is_exact(constraint_target, type_parameters[0])
    {
        return Err(invalid());
    }
    let arguments = if mapped.object.target.is_some() {
        let Some(TypeData::Mapped(original)) =
            store.type_payload(declared_type).map(TypeRecord::data)
        else {
            return Err(invalid());
        };
        let substitution = mapped.object.mapper.ok_or_else(invalid)?;
        let Some(TypeMapperApplication::Composite { second, .. }) =
            store.mapper_application(substitution, original.type_parameter.ok_or_else(invalid)?)
        else {
            return Err(invalid());
        };
        type_parameters
            .iter()
            .map(|parameter| store.map_type(second, *parameter).ok_or_else(invalid))
            .collect::<Result<Vec<_>, _>>()?
    } else {
        type_parameters.to_vec()
    };
    validate_supported_mapped_alias_source_worker(store, arguments[0], array_targets, active)?;
    kind.validate_instantiation(
        store,
        alias,
        declared_type,
        type_parameters,
        &arguments,
        type_,
    )
    .map_err(|error| selection_alias_cache_error(type_, error))?;
    let identity = store
        .mapped_alias_display_identity(type_, alias)
        .map_err(|error| selection_alias_cache_error(type_, error))?;
    if identity.symbol == alias && identity.arguments != arguments {
        return Err(invalid());
    }
    Ok(Some(SupportedMappedAliasProjection {
        kind,
        type_,
        alias,
        declared_type,
        type_parameters: type_parameters.to_vec(),
        arguments,
        identity_symbol: identity.symbol,
        identity_arguments: identity.arguments,
    }))
}

fn selection_alias_source_constraint(
    store: &CanonicalTypeMapperStore,
    parameters: &[NodeRef],
    operands: SourceMappedTypeOperands,
) -> Option<(NodeRef, NodeRef)> {
    let [source_parameter, key_parameter] = parameters else {
        return None;
    };
    let source_name = source_type_parameter_name(store, *source_parameter)?;
    let key_name = source_type_parameter_name(store, *key_parameter)?;
    let mapped_name = source_type_parameter_name(store, operands.type_parameter)?;
    if source_name == key_name || source_name == mapped_name {
        return None;
    }
    let constraint = store.source_direct_type_annotation(*key_parameter)?;
    let constraint_target = store.source_direct_type_annotation(constraint)?;
    let template = operands.template?;
    let template_children = store.source_direct_children(template)?;
    let [object, index] = template_children.as_slice() else {
        return None;
    };
    (store.source_type_operator(constraint) == Some(SyntaxKind::KeyOfKeyword)
        && source_type_parameter_reference(store, constraint_target, source_name)
        && source_type_parameter_reference(store, operands.constraint, key_name)
        && source_type_parameter_reference(store, *object, source_name)
        && source_type_parameter_reference(store, *index, mapped_name))
    .then_some((constraint, constraint_target))
}

fn homomorphic_alias_source_constraint(
    store: &CanonicalTypeMapperStore,
    parameter: NodeRef,
    operands: SourceMappedTypeOperands,
) -> Option<(NodeRef, NodeRef)> {
    let source_name = source_type_parameter_name(store, parameter)?;
    let key_name = source_type_parameter_name(store, operands.type_parameter)?;
    let target = store.source_direct_type_annotation(operands.constraint)?;
    let template = operands.template?;
    (source_name != key_name
        && store.source_type_operator(operands.constraint) == Some(SyntaxKind::KeyOfKeyword)
        && source_type_parameter_reference(store, target, source_name)
        && (store.source_node_kind(template) == Some(SyntaxKind::VoidKeyword)
            || homomorphic_template_index_node(store, template, source_name, key_name).is_some()))
    .then_some((operands.constraint, target))
}

/// Finds the written source/key access through single-argument reference nodes.
fn homomorphic_template_index_node(
    store: &CanonicalTypeMapperStore,
    template: NodeRef,
    source_name: &str,
    key_name: &str,
) -> Option<NodeRef> {
    let mut node = template;
    let mut seen = HashSet::new();
    while seen.insert(node) {
        let children = store.source_direct_children(node)?;
        match store.source_node_kind(node)? {
            SyntaxKind::TypeReference => {
                let [name, argument] = children.as_slice() else {
                    return None;
                };
                if !matches!(
                    store.source_node_kind(*name),
                    Some(SyntaxKind::Identifier | SyntaxKind::QualifiedName)
                ) {
                    return None;
                }
                node = *argument;
            }
            SyntaxKind::IndexedAccessType => {
                let [source, key] = children.as_slice() else {
                    return None;
                };
                return (source_type_parameter_reference(store, *source, source_name)
                    && source_type_parameter_reference(store, *key, key_name))
                .then_some(node);
            }
            _ => return None,
        }
    }
    None
}

fn source_type_parameter_name(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Option<&str> {
    let children = store.source_direct_children(declaration)?;
    let mut names = children
        .into_iter()
        .filter(|child| store.source_node_kind(*child) == Some(SyntaxKind::Identifier));
    let name = names.next()?;
    if names.next().is_some() {
        return None;
    }
    store.source_identifier_text(name)
}

fn source_type_parameter_reference(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    expected_name: &str,
) -> bool {
    let Some(children) = store.source_direct_children(reference) else {
        return false;
    };
    let [name] = children.as_slice() else {
        return false;
    };
    store.source_node_kind(reference) == Some(SyntaxKind::TypeReference)
        && store.source_node_kind(*name) == Some(SyntaxKind::Identifier)
        && store.source_identifier_text(*name) == Some(expected_name)
}

fn selection_alias_cache_error(type_: TypeId, error: MappedTypeError) -> MappedTypeError {
    match error {
        MappedTypeError::UnsupportedConstraint(_)
        | MappedTypeError::UnsupportedNameType(_)
        | MappedTypeError::UnsupportedTemplate(_) => MappedTypeError::InvalidMappedType(type_),
        _ => error,
    }
}

fn validate_supported_mapped_alias_source(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), MappedTypeError> {
    validate_supported_mapped_alias_source_worker(store, source, array_targets, &mut HashSet::new())
}

fn validate_supported_mapped_alias_source_worker(
    store: &CanonicalTypeMapperStore,
    source: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    active: &mut HashSet<TypeId>,
) -> Result<(), MappedTypeError> {
    let record = store
        .type_payload(source)
        .ok_or(MappedTypeError::InvalidSource(source))?;
    match record.data() {
        TypeData::TypeParameter(_) => {
            return cached_ordinary_type_parameter_owner(store, source)
                .map(|_| ())
                .ok_or(MappedTypeError::InvalidSource(source));
        }
        TypeData::Intrinsic(_)
            if record
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN) =>
        {
            return store
                .validate_union_constituent(source)
                .map_err(|_| MappedTypeError::InvalidSource(source));
        }
        TypeData::Mapped(_) => {
            supported_mapped_alias_projection_worker(store, source, array_targets, active)?
                .ok_or(MappedTypeError::UnsupportedSource(source))?;
            return validate_mapped_utility_source(store, source);
        }
        _ => {}
    }
    if validate_source_object_literal_for_keyof(store, source, array_targets)
        .map_err(|_| MappedTypeError::InvalidSource(source))?
    {
        return Ok(());
    }
    if record
        .object_flags()
        .intersects(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
        || record
            .symbol()
            .and_then(|owner| store.symbol(owner))
            .is_some_and(|owner| owner.flags().contains(SymbolFlags::OBJECT_LITERAL))
    {
        return Err(if matches!(record.data(), TypeData::Object(_)) {
            MappedTypeError::UnsupportedSource(source)
        } else {
            MappedTypeError::InvalidSource(source)
        });
    }
    match validate_resolved_declared_property_object(store, source) {
        DeclaredPropertyObjectValidation::Valid(_) => return Ok(()),
        DeclaredPropertyObjectValidation::Malformed => {
            return Err(MappedTypeError::InvalidSource(source));
        }
        DeclaredPropertyObjectValidation::NotDeclared => {}
    }
    if record.data().structured().is_some_and(|structured| {
        structured.signatures.is_some() || structured.call_signature_count != 0
    }) {
        return Err(MappedTypeError::UnsupportedSource(source));
    }
    match plan_nongeneric_keyof_type_with_array_targets(store, source, array_targets) {
        Ok(_) => Ok(()),
        Err(NongenericKeyofError::UnsupportedObject(_)) => {
            Err(MappedTypeError::UnsupportedSource(source))
        }
        Err(_) => Err(MappedTypeError::InvalidSource(source)),
    }
}

fn validate_supported_mapped_alias_instance_request(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<CacheHashKey, MappedTypeError> {
    if supported_mapped_alias_projection(store, projection.type_, array_targets)?.as_ref()
        != Some(projection)
        || arguments.len() != projection.type_parameters.len()
    {
        return Err(MappedTypeError::InvalidMappedType(projection.type_));
    }
    if identity.0 == projection.alias && identity.1 != arguments {
        return Err(MappedTypeError::InvalidMappedType(projection.type_));
    }
    let identity_key = if identity.0 == projection.alias {
        None
    } else {
        if identity.0 != projection.identity_symbol
            || forwarded_mapped_alias_arguments(
                store,
                projection.declared_type,
                identity.0,
                identity.1,
                array_targets,
            )? != arguments
        {
            return Err(MappedTypeError::InvalidMappedType(projection.type_));
        }
        Some((
            store
                .symbol_store()
                .assigned_global_symbol_id(identity.0)
                .ok_or(MappedTypeError::InvalidSymbol(identity.0))?,
            identity.1,
        ))
    };
    validate_supported_mapped_alias_source(store, arguments[0], array_targets)?;
    projection
        .kind
        .validate_request(
            store,
            projection.alias,
            projection.declared_type,
            &projection.type_parameters,
            arguments,
        )
        .map_err(|error| selection_alias_cache_error(projection.type_, error))?;
    Ok(type_alias_instantiation_cache_key(arguments, identity_key))
}

/// Reads the same canonical alias cache used by type-node queries.
pub(super) fn cached_supported_mapped_alias_instance(
    store: &CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, MappedTypeError> {
    let key = validate_supported_mapped_alias_instance_request(
        store,
        projection,
        arguments,
        identity,
        array_targets,
    )?;
    if arguments == projection.arguments
        && identity.0 == projection.identity_symbol
        && identity.1 == projection.identity_arguments
    {
        return Ok(Some(projection.type_));
    }
    if identity.0 == projection.alias && arguments == projection.type_parameters {
        return Ok(Some(projection.declared_type));
    }
    let cached = store
        .type_alias_links(projection.alias)
        .and_then(|links| links.instantiations.as_ref())
        .and_then(|entries| entries.get(&key))
        .copied();
    let Some(cached) = cached else {
        return Ok(None);
    };
    projection
        .kind
        .validate_instantiation(
            store,
            projection.alias,
            projection.declared_type,
            &projection.type_parameters,
            arguments,
            cached,
        )
        .map_err(|error| selection_alias_cache_error(cached, error))?;
    let actual = store
        .mapped_alias_display_identity(cached, projection.alias)
        .map_err(|error| selection_alias_cache_error(cached, error))?;
    if actual.symbol != identity.0 || actual.arguments != identity.1 {
        return Err(MappedTypeError::InvalidMappedType(cached));
    }
    Ok(Some(cached))
}

/// Publishes only a complete source-proved alias instance. Argument substitution
/// and limit recovery belong to the caller's existing instantiation frame.
pub(super) fn instantiate_supported_mapped_alias_instance(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, MappedTypeError> {
    instantiate_supported_mapped_alias_instance_worker(
        store,
        projection,
        arguments,
        identity,
        array_targets,
        None,
    )
}

pub(super) fn instantiate_supported_mapped_alias_instance_with_session(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, MappedTypeError> {
    instantiate_supported_mapped_alias_instance_worker(
        store,
        projection,
        arguments,
        identity,
        array_targets,
        Some(session),
    )
}

fn instantiate_supported_mapped_alias_instance_worker(
    store: &mut CanonicalTypeMapperStore,
    projection: &SupportedMappedAliasProjection,
    arguments: &[TypeId],
    identity: (SemanticSymbolId, &[TypeId]),
    array_targets: Option<CanonicalArrayTargets>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, MappedTypeError> {
    if let Some(cached) = cached_supported_mapped_alias_instance(
        store,
        projection,
        arguments,
        identity,
        array_targets,
    )? {
        return Ok(cached);
    }
    let key = validate_supported_mapped_alias_instance_request(
        store,
        projection,
        arguments,
        identity,
        array_targets,
    )?;
    if identity.0 != projection.alias && arguments == projection.type_parameters {
        return Err(MappedTypeError::UnsupportedSource(projection.type_));
    }
    let mut links = store
        .type_alias_links(projection.alias)
        .cloned()
        .ok_or(MappedTypeError::InvalidSymbol(projection.alias))?;
    links
        .instantiations
        .as_mut()
        .ok_or(MappedTypeError::InvalidSymbol(projection.alias))?
        .try_reserve(1)
        .map_err(|_| MappedTypeError::Capacity)?;
    let mut alias_arguments = Vec::new();
    alias_arguments
        .try_reserve_exact(identity.1.len())
        .map_err(|_| MappedTypeError::Capacity)?;
    alias_arguments.extend_from_slice(identity.1);
    if !store.try_reserve_type_aliases(1)
        || !store.try_reserve_types(3)
        || !store.try_reserve_mappers(3)
    {
        return Err(MappedTypeError::Capacity);
    }
    let result = projection
        .kind
        .instantiate(
            store,
            projection.alias,
            projection.declared_type,
            &projection.type_parameters,
            arguments,
            session,
        )
        .map_err(|error| selection_alias_cache_error(projection.type_, error))?;
    let alias = store
        .alloc_type_alias(Some(identity.0))
        .ok_or(MappedTypeError::Capacity)?;
    if !store.set_type_alias_arguments(alias, Some(alias_arguments))
        || !store.set_type_alias(result, Some(alias))
    {
        return Err(MappedTypeError::InvalidMappedType(result));
    }
    projection
        .kind
        .validate_instantiation(
            store,
            projection.alias,
            projection.declared_type,
            &projection.type_parameters,
            arguments,
            result,
        )
        .map_err(|error| selection_alias_cache_error(result, error))?;
    if links
        .instantiations
        .as_mut()
        .ok_or(MappedTypeError::InvalidSymbol(projection.alias))?
        .insert(key, result)
        .is_some()
        || !store.set_type_alias_links(projection.alias, links)
    {
        return Err(MappedTypeError::InvalidMappedType(result));
    }
    Ok(result)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericMappedTypeProjection {
    pub(super) type_: TypeId,
    pub(super) target: TypeId,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    parameter: TypeId,
    alias: Option<SemanticSymbolId>,
    pub(super) parameters: Vec<TypeId>,
    pub(super) arguments: Vec<TypeId>,
}

fn source_mapped_parameter_constraint(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidTypeParameter(type_);
    let TypeData::TypeParameter(parameter) = store.type_payload(type_).ok_or_else(invalid)?.data()
    else {
        return Err(invalid());
    };
    let owner = cached_ordinary_type_parameter_owner(store, type_).ok_or_else(invalid)?;
    let Some([declaration]) = store.symbol(owner).and_then(|owner| owner.declarations()) else {
        return Err(invalid());
    };
    let annotations = store
        .source_type_parameter_annotations(*declaration)
        .ok_or_else(invalid)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    match (annotations.constraint, parameter.constraint) {
        (None, cached) if cached.is_none_or(|cached| cached == bootstrap.no_constraint_type) => {
            Ok(None)
        }
        (Some(node), Some(type_)) if store.source_direct_type_annotation_is_exact(node, type_) => {
            Ok(Some(type_))
        }
        _ => Err(invalid()),
    }
}

pub(super) fn mapped_modifiers_type_from_constraint(
    store: &CanonicalTypeMapperStore,
    constraint: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(constraint);
    let mut extended = constraint;
    if matches!(
        store.type_payload(constraint).ok_or_else(invalid)?.data(),
        TypeData::TypeParameter(_)
    ) {
        match source_mapped_parameter_constraint(store, constraint)? {
            Some(type_) => extended = type_,
            None => return Ok(None),
        }
    }
    let record = store.type_payload(extended).ok_or_else(invalid)?;
    if !matches!(record.data(), TypeData::Index(_)) {
        return Ok(None);
    }
    validate_generic_keyof_index_type(store, extended)
        .map(Some)
        .map_err(|_| invalid())
}

/// Finds the outer formals used by a written mapped type. An inline mapped
/// type does not capture a formal merely because another formal constrains it.
#[allow(clippy::too_many_lines)] // Source operands, cloned formals, and both cache entries form one proof.
pub(super) fn generic_mapped_type_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<GenericMappedTypeProjection>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let Some(TypeData::Mapped(mapped)) = store.type_payload(type_).map(TypeRecord::data) else {
        return Ok(None);
    };
    let target = mapped.object.target.unwrap_or(type_);
    let original_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Mapped(original) = original_record.data() else {
        return Err(invalid());
    };
    // Existing utility instances retain their alias cache, not this object cache.
    if target != type_ && original.object.instantiations == TypeCacheState::Unallocated {
        return Ok(None);
    }
    let declaration = original.declaration.ok_or_else(invalid)?;
    let mut parent = declaration;
    let mut seen = HashSet::new();
    let alias_declaration = loop {
        if seen.len() >= 16 || !seen.insert(parent) {
            return Err(invalid());
        }
        let Some(SourceNodeParent::Parent(next)) = store.source_node_parent(parent) else {
            return Ok(None);
        };
        match store.source_node_kind(next) {
            Some(SyntaxKind::TypeAliasDeclaration) => break next,
            Some(SyntaxKind::IntersectionType | SyntaxKind::ParenthesizedType) => parent = next,
            _ => return Ok(None),
        }
    };
    let alias_symbol = store
        .source_declaration_symbol(alias_declaration)
        .ok_or_else(invalid)?;
    let header =
        property_object_alias_identity_source_header(store, alias_symbol).map_err(|_| invalid())?;
    if header.alias_declaration != alias_declaration || header.parameters.is_empty() {
        return Ok(None);
    }
    let direct_alias = store.source_direct_type_annotation(alias_declaration) == Some(declaration);
    let mut referenced = HashSet::new();
    let mut nodes = vec![declaration];
    let mut visited = HashSet::new();
    while let Some(node) = nodes.pop() {
        if !visited.insert(node) {
            return Err(invalid());
        }
        if store.source_node_kind(node) == Some(SyntaxKind::TypeReference)
            && let Some(symbol) = store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol)
        {
            referenced.insert(symbol);
        }
        for child in store.source_direct_children(node).ok_or_else(invalid)? {
            if store.source_node_parent(child) != Some(SourceNodeParent::Parent(node)) {
                return Err(invalid());
            }
            nodes.push(child);
        }
    }
    let parameters = header
        .parameters
        .iter()
        .filter(|(_, symbol)| direct_alias || referenced.contains(symbol))
        .map(|(_, symbol)| {
            store
                .declared_type_links(*symbol)
                .and_then(|links| links.declared_type)
                .filter(|type_| {
                    cached_ordinary_type_parameter_owner(store, *type_) == Some(*symbol)
                })
                .ok_or_else(invalid)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let symbol = original_record.symbol().ok_or_else(invalid)?;
    let parameter = original.type_parameter.ok_or_else(invalid)?;
    let operands = store
        .source_mapped_type_operands(declaration)
        .ok_or_else(invalid)?;
    let request = MappedTypeRequest::new(
        declaration,
        symbol,
        parameter,
        original.constraint_type.ok_or_else(invalid)?,
        original.template_type.ok_or_else(invalid)?,
        original.modifiers_type.ok_or_else(invalid)?,
    );
    let request = original
        .name_type
        .map_or(request, |name| request.with_name_type(name));
    validate_mapped_request(store, request)?;
    validate_request_record(store, request, target)?;
    let parameter_owner =
        cached_ordinary_type_parameter_owner(store, parameter).ok_or_else(invalid)?;
    let links = store.type_node_links(declaration).ok_or_else(invalid)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    let source_flags = ObjectFlags::MAPPED
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::PROPAGATING_FLAGS;
    if original_record.flags() != TypeFlags::OBJECT
        || !original_record.object_flags().contains(ObjectFlags::MAPPED)
        || !(original_record.object_flags() & !source_flags).is_empty()
        || original.object.target.is_some()
        || original.object.mapper.is_some()
        || original_record.alias().is_some()
        || original.contains_error
        || links.resolved_type != Some(target)
        || links
            .outer_type_parameters
            .as_ref()
            .is_some_and(|saved| *saved != parameters)
        || !store.source_declaration_belongs_to_symbol(declaration, symbol)
        || !store.source_symbol_declarations_match(symbol)
        || store
            .symbol(parameter_owner)
            .and_then(|owner| owner.declarations())
            != Some(&[operands.type_parameter][..])
        || !matches!(store.type_payload(parameter).map(TypeRecord::data),
            Some(TypeData::TypeParameter(parameter)) if parameter.constraint == Some(request.constraint_type))
        || !store
            .source_direct_type_annotation_is_exact(operands.constraint, request.constraint_type)
        || !operands
            .template
            .map_or(request.template_type == bootstrap.any_type, |node| {
                store.source_direct_type_annotation_is_exact(node, request.template_type)
            })
        || match (operands.name_type, original.name_type) {
            (None, None) => false,
            (Some(node), Some(type_)) => !store.source_direct_type_annotation_is_exact(node, type_),
            _ => true,
        }
    {
        return Err(invalid());
    }
    if store.source_type_operator(operands.constraint) == Some(SyntaxKind::KeyOfKeyword) {
        let source = store
            .source_direct_type_annotation(operands.constraint)
            .ok_or_else(invalid)?;
        if !store.source_direct_type_annotation_is_exact(source, request.modifiers_type) {
            return Err(invalid());
        }
    } else if request.modifiers_type
        != mapped_modifiers_type_from_constraint(store, request.constraint_type)?
            .unwrap_or(bootstrap.unknown_type)
    {
        return Err(invalid());
    }
    let arguments = if target == type_ {
        parameters.clone()
    } else {
        let mapper = mapped.object.mapper.ok_or_else(invalid)?;
        let Some(TypeMapperApplication::Composite { second, .. }) =
            store.mapper_application(mapper, parameter)
        else {
            return Err(invalid());
        };
        let arguments = parameters
            .iter()
            .map(|type_| store.map_type(second, *type_).ok_or_else(invalid))
            .collect::<Result<Vec<_>, _>>()?;
        if store.type_mapper_has_exact_endpoints(second, &parameters, &arguments) != Some(true)
            || mapped_type_parameter_owner(store, type_, mapped.type_parameter.ok_or_else(invalid)?)
                != cached_ordinary_type_parameter_owner(store, parameter)
            || mapped.object.instantiations != TypeCacheState::Unallocated
            || mapped.contains_error
            || !store.type_payload(type_).is_some_and(|record| {
                record.flags() == TypeFlags::OBJECT
                    && record
                        .object_flags()
                        .contains(ObjectFlags::INSTANTIATED_MAPPED)
                    && (record.object_flags() & !(source_flags | ObjectFlags::INSTANTIATED_MAPPED))
                        .is_empty()
                    && record.symbol() == Some(symbol)
            })
        {
            return Err(invalid());
        }
        let mut sources = parameters.clone();
        let mut targets = arguments.clone();
        sources.push(parameter);
        targets.push(mapped.type_parameter.ok_or_else(invalid)?);
        match (original.name_type, mapped.name_type) {
            (None, None) => {}
            (Some(source), Some(actual))
                if cached_instantiation_with_vector(
                    store,
                    source,
                    &sources,
                    &targets,
                    array_targets,
                    None,
                )
                .map_err(|_| invalid())?
                    == Some(actual) => {}
            _ => return Err(invalid()),
        }
        arguments
    };
    let identity = store.type_payload(type_).and_then(TypeRecord::alias);
    if target != type_ && direct_alias {
        let identity = identity
            .and_then(|identity| store.type_alias(identity))
            .ok_or_else(invalid)?;
        if identity.symbol() != Some(alias_symbol)
            || identity.type_arguments().unwrap_or_default() != arguments
        {
            return Err(invalid());
        }
    } else if identity.is_some() {
        return Err(invalid());
    }
    if !store.type_payload(type_).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    }) && !unresolved_mapped_structure_is_valid(store, type_, &mapped.object.structured)
    {
        return Err(invalid());
    }
    match &original.object.instantiations {
        TypeCacheState::Unallocated if target == type_ && links.outer_type_parameters.is_none() => {
        }
        TypeCacheState::Allocated(cache)
            if links.outer_type_parameters.as_deref() == Some(parameters.as_slice())
                && cache.get(&type_alias_instantiation_cache_key(&parameters, None))
                    == Some(&target)
                && cache.get(&type_alias_instantiation_cache_key(&arguments, None))
                    == Some(&type_) => {}
        _ => return Err(invalid()),
    }
    Ok(Some(GenericMappedTypeProjection {
        type_,
        target,
        declaration,
        symbol,
        parameter,
        alias: direct_alias.then_some(alias_symbol),
        parameters,
        arguments,
    }))
}

pub(super) fn cached_generic_mapped_type_instance(
    store: &CanonicalTypeMapperStore,
    projection: &GenericMappedTypeProjection,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(projection.type_);
    if generic_mapped_type_projection(store, projection.type_, array_targets)?.as_ref()
        != Some(projection)
        || arguments.len() != projection.parameters.len()
        || arguments
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
    {
        return Err(invalid());
    }
    if arguments == projection.arguments {
        return Ok(Some(projection.type_));
    }
    if arguments == projection.parameters {
        return Ok(Some(projection.target));
    }
    let key = type_alias_instantiation_cache_key(arguments, None);
    let Some(cached) = store.relation_object_instantiation(projection.target, key) else {
        return Ok(None);
    };
    let actual =
        generic_mapped_type_projection(store, cached, array_targets)?.ok_or_else(invalid)?;
    if actual.target != projection.target
        || actual.parameters != projection.parameters
        || actual.arguments != arguments
    {
        return Err(invalid());
    }
    Ok(Some(cached))
}

/// Substitutes mapped operands through the normal type instantiator. The
/// mapped parameter stays local and receives its own declaration-linked clone.
#[allow(clippy::too_many_lines)] // Publish the operands, local mapper, and identity in one caller frame.
pub(super) fn instantiate_generic_mapped_type_instance(
    store: &mut CanonicalTypeMapperStore,
    projection: &GenericMappedTypeProjection,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<TypeId, MappedTypeError> {
    if let Some(cached) =
        cached_generic_mapped_type_instance(store, projection, arguments, array_targets)?
    {
        return Ok(cached);
    }
    let invalid = || MappedTypeError::InvalidMappedType(projection.target);
    let TypeData::Mapped(original) = store
        .type_payload(projection.target)
        .ok_or_else(invalid)?
        .data()
    else {
        return Err(invalid());
    };
    let original = original.clone();
    let mark = session.limit_event_mark();
    let constraint = instantiate_type_with_vector_and_session(
        store,
        original.constraint_type.ok_or_else(invalid)?,
        &projection.parameters,
        arguments,
        array_targets,
        session,
    )
    .map_err(|error| mapped_instantiation_error(projection.target, &error))?;
    if session.limit_event_occurred_since(mark) {
        return session.recovery_error_type().ok_or_else(invalid);
    }
    if !store.try_reserve_types(2)
        || !store.try_reserve_mappers(3)
        || !store.try_reserve_type_node_links(1)
        || !store.try_reserve_type_aliases(usize::from(projection.alias.is_some()))
    {
        return Err(MappedTypeError::Capacity);
    }
    let owner =
        cached_ordinary_type_parameter_owner(store, projection.parameter).ok_or_else(invalid)?;
    let parameter = store
        .alloc_type_parameter(Some(owner))
        .ok_or(MappedTypeError::Capacity)?;
    let outer = store
        .new_type_mapper(projection.parameters.clone(), arguments.to_vec())
        .ok_or_else(invalid)?;
    let local = store
        .new_simple_type_mapper(projection.parameter, parameter)
        .ok_or_else(invalid)?;
    let mapper = store
        .combine_type_mappers(Some(local), outer)
        .ok_or_else(invalid)?;
    if !store.set_type_parameter_resolution(
        parameter,
        Some(constraint),
        Some(projection.parameter),
        Some(mapper),
        None,
    ) {
        return Err(invalid());
    }
    let mut sources = projection.parameters.clone();
    let mut targets = arguments.to_vec();
    sources.push(projection.parameter);
    targets.push(parameter);
    let template = instantiate_type_with_vector_and_session(
        store,
        original.template_type.ok_or_else(invalid)?,
        &sources,
        &targets,
        array_targets,
        session,
    )
    .map_err(|error| mapped_instantiation_error(projection.target, &error))?;
    let modifiers = instantiate_type_with_vector_and_session(
        store,
        original.modifiers_type.ok_or_else(invalid)?,
        &projection.parameters,
        arguments,
        array_targets,
        session,
    )
    .map_err(|error| mapped_instantiation_error(projection.target, &error))?;
    let name = original
        .name_type
        .map(|name| {
            instantiate_type_with_vector_and_session(
                store,
                name,
                &sources,
                &targets,
                array_targets,
                session,
            )
        })
        .transpose()
        .map_err(|error| mapped_instantiation_error(projection.target, &error))?;
    if session.limit_event_occurred_since(mark) {
        return session.recovery_error_type().ok_or_else(invalid);
    }
    let instantiated = store
        .alloc_mapped_type(
            ObjectFlags::INSTANTIATED_MAPPED,
            Some(projection.symbol),
            Some(projection.declaration),
        )
        .ok_or(MappedTypeError::Capacity)?;
    if !store.set_object_target_and_mapper(instantiated, Some(projection.target), Some(mapper))
        || !store.set_mapped_type_resolution(
            instantiated,
            Some(projection.declaration),
            Some(parameter),
            Some(constraint),
            name,
            Some(template),
            Some(modifiers),
            None,
            false,
        )
    {
        return Err(invalid());
    }
    if let Some(symbol) = projection.alias {
        let identity = store
            .alloc_type_alias(Some(symbol))
            .ok_or(MappedTypeError::Capacity)?;
        if !store.set_type_alias_arguments(identity, Some(arguments.to_vec()))
            || !store.set_type_alias(instantiated, Some(identity))
        {
            return Err(invalid());
        }
    }
    let key = type_alias_instantiation_cache_key(arguments, None);
    if original.object.instantiations == TypeCacheState::Unallocated {
        let mut entries = HashMap::new();
        entries
            .try_reserve(2)
            .map_err(|_| MappedTypeError::Capacity)?;
        entries.insert(
            type_alias_instantiation_cache_key(&projection.parameters, None),
            projection.target,
        );
        entries.insert(key, instantiated);
        if !store.set_object_instantiations(projection.target, TypeCacheState::Allocated(entries)) {
            return Err(invalid());
        }
    } else if !store.try_reserve_object_instantiations(projection.target, 1)
        || store.insert_object_instantiation(projection.target, key, instantiated)
            != Some(instantiated)
    {
        return Err(invalid());
    }
    let mut links = store
        .type_node_links(projection.declaration)
        .cloned()
        .ok_or_else(invalid)?;
    links.outer_type_parameters = Some(projection.parameters.clone());
    if !store.set_type_node_links(projection.declaration, links)
        || generic_mapped_type_projection(store, instantiated, array_targets)?.is_none()
    {
        return Err(invalid());
    }
    Ok(instantiated)
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
    identity: MappedRecoveryIdentity,
}

#[derive(Debug, Eq, PartialEq)]
enum MappedRecoveryIdentity {
    Types(Vec<RecoveredPropertyTypeIdentity>),
    SourceConditional {
        demand: SourceConditionalMappedDemand,
        inputs: Vec<RecoveredPropertyTypeIdentity>,
    },
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
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.symbol == symbol
            && self.shape == *shape
            && self.key_type == key_type
            && self.result == result
            && self.matches_published_links(store.value_symbol_links(symbol))
            && mapped_property_recovery_identity_with_array_targets(
                store,
                shape,
                key_type,
                result,
                array_targets,
            )
            .is_some_and(|identity| identity == self.identity)
    }
}

fn mapped_property_recovery_identity(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    result: TypeId,
) -> Option<MappedRecoveryIdentity> {
    mapped_property_recovery_identity_with_array_targets(store, shape, key_type, result, None)
}

fn mapped_property_recovery_identity_with_array_targets(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    result: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Option<MappedRecoveryIdentity> {
    if source_mapped_lookup_origin(store, shape.type_)
        .ok()?
        .is_some()
    {
        let demand =
            source_conditional_mapped_demand_with_array_targets(store, shape.type_, array_targets)
                .ok()?;
        if source_conditional_mapped_key(store, demand).ok()? != key_type
            || store.intrinsic_bootstrap()?.error_type != result
        {
            return None;
        }
        let mut roots = vec![demand.argument, key_type, result];
        for property in &shape.source_properties {
            roots.push(store.value_symbol_links(property.symbol)?.resolved_type?);
        }
        return Some(MappedRecoveryIdentity::SourceConditional {
            demand,
            inputs: property_recovery_type_identity(store, &roots, array_targets)?,
        });
    }
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
    property_recovery_type_identity(store, &roots, array_targets).map(MappedRecoveryIdentity::Types)
}

/// Created only when mapped index evaluation observes a caller limit event.
#[derive(Debug)]
pub(super) struct MappedIndexRecovery {
    valid: bool,
    index: IndexInfoId,
    shape: MappedShape,
    plan: PlannedMappedIndex,
    result: TypeId,
    identity: MappedRecoveryIdentity,
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
    conditional_template: bool,
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

struct MappedConditionalSource<'a> {
    globals: &'a CanonicalGlobalTypes,
    branches: &'a mut dyn ConditionalBranchSource,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceConditionalMappedDemand {
    origin: SourceMappedLookupOrigin,
    lookup: TypeId,
    argument: TypeId,
    parameter: TypeId,
    mapper: TypeMapperId,
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
        } else if !unresolved_mapped_structure_is_valid(
            self,
            instantiated,
            &mapped.object.structured,
        ) {
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
        self.instantiate_homomorphic_mapped_alias_worker(
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            modifiers,
            None,
        )
    }

    fn instantiate_homomorphic_mapped_alias_worker(
        &mut self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        modifiers: MappedTypeModifiers,
        session: Option<&mut InstantiationSession>,
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
        let constraint = match session {
            Some(session) => resolve_nongeneric_keyof_type_with_session(self, &key_plan, session),
            None => resolve_nongeneric_keyof_type(self, &key_plan),
        }
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

        if shape.conditional_template {
            return if !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
                && unresolved_mapped_structure_is_valid(
                    self,
                    instantiated,
                    &mapped.object.structured,
                ) {
                Ok(())
            } else {
                Err(MappedTypeError::InvalidMappedType(instantiated))
            };
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
        } else if !unresolved_mapped_structure_is_valid(
            self,
            instantiated,
            &mapped.object.structured,
        ) {
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
        } else if !unresolved_mapped_structure_is_valid(
            self,
            instantiated,
            &mapped.object.structured,
        ) {
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
        self.validate_prop_types_required_keys_instantiation_worker(
            alias,
            declared_type,
            type_parameters,
            type_arguments,
            instantiated,
            true,
        )
    }

    fn validate_prop_types_required_keys_instantiation_worker(
        &self,
        alias: SemanticSymbolId,
        declared_type: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
        instantiated: TypeId,
        validate_members: bool,
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
        let retained_template = match self.type_payload(instantiated).map(TypeRecord::data) {
            Some(TypeData::IndexedAccess(indexed)) => self
                .type_payload(indexed.object_type)
                .is_some_and(|record| {
                    matches!(record.data(), TypeData::Mapped(mapped)
                    if mapped.template_type == Some(shape.conditional))
                }),
            _ => false,
        };
        if retained_template {
            let origin = source_mapped_lookup_origin(self, shape.mapped)?
                .ok_or(MappedTypeError::InvalidMappedType(instantiated))?;
            let mapped = validate_source_mapped_lookup_instance(
                self,
                origin,
                shape.source_argument,
                instantiated,
                None,
            )?;
            return validate_source_mapped_lookup_cold_state(self, origin, mapped);
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
            if !validate_members {
                return Ok(());
            }
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
        } else if !unresolved_mapped_structure_is_valid(
            self,
            indexed_access.object_type,
            &mapped.object.structured,
        ) {
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
        self.resolve_mapped_type_members_worker(type_, modifiers, session, None)
    }

    fn resolve_mapped_type_members_worker(
        &mut self,
        type_: TypeId,
        modifiers: MappedTypeModifiers,
        session: &mut InstantiationSession,
        source: Option<&MappedConditionalSource<'_>>,
    ) -> Result<ResolvedMappedTypeMembers, MappedTypeError> {
        let array_targets =
            source.map(|source| CanonicalArrayTargets::from_global_types(source.globals));
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
                    let _ = validate_warm_mapped_members_with_array_targets(
                        self,
                        &shape,
                        &properties,
                        &indexes,
                        array_targets,
                    )?;
                }
            }
            return Err(MappedTypeError::InvalidModifiers);
        }
        let modifiers = declared;
        validate_mapped_member_dependencies(self, type_, &mut HashSet::new())?;
        if let Some(source) = source {
            let demand =
                source_conditional_mapped_demand_with_array_targets(self, type_, array_targets)?;
            source_conditional_mapped_key(self, demand)?;
            source.branches.preflight(self, demand.origin.template)?;
        } else {
            reject_deferred_conditional_mapped_demand(self, type_)?;
        }
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
        if source.is_some() && (properties.len() != 1 || !indexes.is_empty()) {
            return Err(MappedTypeError::UnsupportedConstraint(
                shape.constraint_type,
            ));
        }
        if let Some(cached) = validate_warm_mapped_members_with_array_targets(
            self,
            &shape,
            &properties,
            &indexes,
            array_targets,
        )? {
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
        if source_mapped_lookup_origin(self, type_)?.is_some() {
            reject_deferred_conditional_mapped_demand(self, type_)?;
        }
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

    /// Reads Record arguments only after its source, mapper, and alias cache agree.
    pub(super) fn record_mapped_alias_type_edges(
        &self,
        type_: TypeId,
    ) -> Result<Option<Vec<TypeId>>, MappedTypeError> {
        let invalid = || MappedTypeError::InvalidMappedType(type_);
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Ok(None);
        };
        if !record
            .object_flags()
            .contains(ObjectFlags::INSTANTIATED_MAPPED)
        {
            return Ok(None);
        }
        let declaration = mapped.declaration.ok_or_else(invalid)?;
        let Some(SourceNodeParent::Parent(alias_declaration)) =
            self.source_node_parent(declaration)
        else {
            return Ok(None);
        };
        if self.source_node_kind(alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration) {
            return Ok(None);
        }
        let alias = self
            .source_declaration_symbol(alias_declaration)
            .ok_or_else(invalid)?;
        if self.symbol(alias).ok_or_else(invalid)?.name().as_utf8() != Some("Record") {
            return Ok(None);
        }
        let target = mapped.object.target.ok_or_else(invalid)?;
        let arguments = [
            mapped.constraint_type.ok_or_else(invalid)?,
            mapped.template_type.ok_or_else(invalid)?,
        ];
        let parameters = self
            .type_alias_links(alias)
            .and_then(|links| links.type_parameters.as_deref())
            .ok_or_else(invalid)?;
        self.validate_record_mapped_alias_instantiation(
            alias, target, parameters, &arguments, type_,
        )?;
        let identity = self.mapped_alias_display_identity(type_, alias)?;
        Ok(Some(
            arguments.into_iter().chain(identity.arguments).collect(),
        ))
    }

    /// Checks alias and mapper identity without demanding cold mapped members.
    pub(super) fn mapped_alias_display_identity(
        &self,
        type_: TypeId,
        alias: SemanticSymbolId,
    ) -> Result<MappedAliasDisplayIdentity, MappedTypeError> {
        let invalid = || MappedTypeError::InvalidMappedType(type_);
        let record = self.type_payload(type_).ok_or_else(invalid)?;
        let TypeData::Mapped(mapped) = record.data() else {
            return Err(invalid());
        };
        let declaration = mapped.declaration.ok_or_else(invalid)?;
        let Some(SourceNodeParent::Parent(alias_declaration)) =
            self.source_node_parent(declaration)
        else {
            return Err(invalid());
        };
        if self.source_node_kind(alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration)
            || self.source_declaration_symbol(alias_declaration) != Some(alias)
            || !self.source_symbol_declarations_match(alias)
        {
            return Err(invalid());
        }
        if mapped.object.target.is_some() {
            validate_mapped_relation_identity(self, type_)?;
            let template = mapped
                .template_type
                .and_then(|template| self.type_payload(template))
                .ok_or_else(invalid)?;
            let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
            if let TypeData::IndexedAccess(indexed) = template.data()
                && (template.flags() != TypeFlags::INDEXED_ACCESS
                    || template.object_flags() != ObjectFlags::NONE
                        && template.object_flags() != variable_flags
                    || template.symbol().is_some()
                    || template.alias().is_some()
                    || indexed.constrained != ConstrainedTypeData::default()
                    || cached_deferred_indexed_access_type(
                        self,
                        indexed.object_type,
                        indexed.index_type,
                        indexed.access_flags,
                    ) != Ok(Some(template.id())))
            {
                return Err(invalid());
            }
            let identity = record
                .alias()
                .and_then(|identity| self.type_alias(identity))
                .ok_or_else(invalid)?;
            return Ok(MappedAliasDisplayIdentity {
                symbol: identity.symbol().ok_or_else(invalid)?,
                arguments: identity.type_arguments().ok_or_else(invalid)?.to_vec(),
            });
        }

        let links = self.type_alias_links(alias).ok_or_else(invalid)?;
        let parameters = links.type_parameters.as_deref().unwrap_or_default();
        if links.declared_type != Some(type_)
            || !parameters.is_empty()
                && links.instantiations.as_ref().is_none_or(|entries| {
                    entries.get(&type_list_key(parameters)) != Some(&type_)
                        || entries
                            .values()
                            .any(|type_| self.type_payload(*type_).is_none())
                })
        {
            return Err(invalid());
        }
        // Pick declarations retain their source parameter as the modifier type.
        // Authenticate that shape before allowing the utility modifier rule.
        let pick = matches!(parameters, [_, _])
            && matches!(
                mapped
                    .template_type
                    .and_then(|template| self.type_payload(template))
                    .map(TypeRecord::data),
                Some(TypeData::IndexedAccess(_))
            );
        if pick {
            validate_pick_mapped_alias_request(self, alias, type_, parameters, parameters)?;
        }
        validate_source_mapped_relation_identity(self, type_, pick)?;
        if record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
        {
            let shape = validate_mapped_shape(self, type_)?;
            let modifiers = self.declared_mapped_modifiers(type_)?;
            let (properties, indexes) = plan_mapped_members(self, &shape, modifiers)?;
            if validate_warm_mapped_members(self, &shape, &properties, &indexes)?.is_none() {
                return Err(invalid());
            }
        } else {
            validate_unresolved_mapped_members(self, type_)?;
        }
        Ok(MappedAliasDisplayIdentity {
            symbol: alias,
            arguments: parameters.to_vec(),
        })
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

    pub(super) fn resolve_mapped_type_property_with_source(
        &mut self,
        type_: TypeId,
        name: EscapedNameRef<'_>,
        modifiers: MappedTypeModifiers,
        globals: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
        branches: &mut dyn ConditionalBranchSource,
    ) -> Result<Option<ResolvedMappedProperty>, MappedTypeError> {
        let mut source = MappedConditionalSource { globals, branches };
        let source = source_mapped_lookup_origin(self, type_)?
            .is_some()
            .then_some(&mut source);
        let members =
            self.resolve_mapped_type_members_worker(type_, modifiers, session, source.as_deref())?;
        let Some(symbol) = self
            .symbol_table(members.members)
            .and_then(|table| table.get(name))
        else {
            return Ok(None);
        };
        if !members.properties.contains(&symbol) {
            return Err(MappedTypeError::InvalidCachedProperty(symbol));
        }
        let type_ = self.resolve_mapped_symbol_type_worker(symbol, session, source)?;
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

    pub(super) fn resolve_mapped_lookup_with_source(
        &mut self,
        lookup: TypeId,
        globals: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
        source: &mut dyn ConditionalBranchSource,
    ) -> Result<TypeId, MappedTypeError> {
        let Some(TypeData::IndexedAccess(indexed)) =
            self.type_payload(lookup).map(TypeRecord::data)
        else {
            return Err(MappedTypeError::InvalidMappedType(lookup));
        };
        let demand = source_conditional_mapped_demand_with_array_targets(
            self,
            indexed.object_type,
            Some(CanonicalArrayTargets::from_global_types(globals)),
        )?;
        if demand.lookup != lookup {
            return Err(MappedTypeError::InvalidMappedType(lookup));
        }
        source_conditional_mapped_key(self, demand)?;
        source.preflight(self, demand.origin.template)?;
        super::instantiate::resolve_indexed_access_with_source(
            self, lookup, globals, session, source,
        )
        .map_err(|error| mapped_instantiation_error(lookup, &error))
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
        self.resolve_mapped_symbol_type_worker(symbol, session, None)
    }

    fn resolve_mapped_symbol_type_worker(
        &mut self,
        symbol: SemanticSymbolId,
        session: &mut InstantiationSession,
        source: Option<&mut MappedConditionalSource<'_>>,
    ) -> Result<TypeId, MappedTypeError> {
        let array_targets = source
            .as_ref()
            .map(|source| CanonicalArrayTargets::from_global_types(source.globals));
        let (containing_type, key_type, cached) = validate_mapped_property_header(self, symbol)?;
        if let Some(source) = source.as_ref() {
            let demand = source_conditional_mapped_demand_with_array_targets(
                self,
                containing_type,
                array_targets,
            )?;
            if source_conditional_mapped_key(self, demand)? != key_type {
                return Err(MappedTypeError::InvalidCachedProperty(symbol));
            }
            source.branches.preflight(self, demand.origin.template)?;
        } else {
            reject_deferred_conditional_mapped_demand(self, containing_type)?;
        }
        if let Some(cached) = cached {
            let shape = validate_mapped_shape(self, containing_type)?;
            let modifiers = self.declared_mapped_modifiers(containing_type)?;
            let (properties, indexes) = plan_mapped_members(self, &shape, modifiers)?;
            let members = validate_warm_mapped_members_with_array_targets(
                self,
                &shape,
                &properties,
                &indexes,
                array_targets,
            )?
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
        let computed = match source {
            Some(source) => compute_mapped_property_type_worker(
                self,
                containing_type,
                symbol,
                key_type,
                session,
                Some(source),
            ),
            None => compute_mapped_property_type(self, containing_type, symbol, key_type, session),
        };
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
            let identity = mapped_property_recovery_identity_with_array_targets(
                self,
                &shape,
                key_type,
                type_,
                array_targets,
            )
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
    let conditional_template = conditional_mapped_template_source_is_exact(
        store,
        declaration,
        template,
        *source_parameter,
        parameter,
    )?;
    if !conditional_template
        && !mapped_template_source_is_exact(store, template, *source_parameter, parameter)
    {
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

    if conditional_template
        && (record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            || !unresolved_mapped_structure_is_valid(
                store,
                declared_type,
                &mapped.object.structured,
            ))
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
        conditional_template,
    })
}

/// Proves a deferred conditional alias applied to the written source/key access.
fn conditional_mapped_template_source_is_exact(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    template: TypeId,
    source: TypeId,
    key: TypeId,
) -> Result<bool, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(template);
    let Some(template_node) = store
        .source_mapped_type_operands(declaration)
        .and_then(|operands| operands.template)
    else {
        return Ok(false);
    };
    if store.source_node_kind(template_node) != Some(SyntaxKind::TypeReference)
        || !validate_conditional_reference_result(store, template_node, template)
            .map_err(|_| invalid())?
    {
        return Ok(false);
    }
    if !matches!(
        store.type_payload(template).map(TypeRecord::data),
        Some(TypeData::Conditional(_))
    ) {
        return Ok(false);
    }
    let identity = conditional_alias_projection(store, template)
        .map_err(|_| invalid())?
        .ok_or_else(invalid)?;
    let [argument] = identity.type_arguments else {
        return Ok(false);
    };
    let declarations = [source, key].map(|type_| {
        cached_ordinary_type_parameter_owner(store, type_)
            .and_then(|owner| store.symbol(owner))
            .and_then(|owner| owner.declarations())
    });
    let [Some([source_declaration]), Some([key_declaration])] = declarations else {
        return Err(invalid());
    };
    let source_name = source_type_parameter_name(store, *source_declaration).ok_or_else(invalid)?;
    let key_name = source_type_parameter_name(store, *key_declaration).ok_or_else(invalid)?;
    let Some(indexed_node) =
        homomorphic_template_index_node(store, template_node, source_name, key_name)
    else {
        return Ok(false);
    };
    let reference_children = store
        .source_direct_children(template_node)
        .ok_or_else(invalid)?;
    if !matches!(reference_children.as_slice(), [_, argument_node] if *argument_node == indexed_node)
    {
        return Ok(false);
    }
    let indexed_children = store
        .source_direct_children(indexed_node)
        .ok_or_else(invalid)?;
    let [source_node, key_node] = indexed_children.as_slice() else {
        return Err(invalid());
    };
    let record = store.type_payload(*argument).ok_or_else(invalid)?;
    let TypeData::IndexedAccess(indexed) = record.data() else {
        return Err(invalid());
    };
    let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if record.flags() != TypeFlags::INDEXED_ACCESS
        || record.object_flags() != ObjectFlags::NONE && record.object_flags() != variable_flags
        || record.symbol().is_some()
        || record.alias().is_some()
        || indexed.object_type != source
        || indexed.index_type != key
        || indexed.access_flags != AccessFlags::NONE
        || indexed.constrained != ConstrainedTypeData::default()
        || cached_deferred_indexed_access_type(store, source, key, AccessFlags::NONE)
            != Ok(Some(*argument))
        || !store.source_direct_type_annotation_is_exact(template_node, template)
        || !store.source_direct_type_annotation_is_exact(indexed_node, *argument)
        || !store.source_direct_type_annotation_is_exact(*source_node, source)
        || !store.source_direct_type_annotation_is_exact(*key_node, key)
    {
        return Err(invalid());
    }
    Ok(true)
}

fn deferred_conditional_mapped_template(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    if let Some(origin) = source_mapped_lookup_origin(store, type_)? {
        source_mapped_lookup_projection(store, type_, None)?.ok_or_else(invalid)?;
        return Ok(Some(origin.template));
    }
    let Some(TypeData::Mapped(mapped)) = store.type_payload(type_).map(TypeRecord::data) else {
        return Err(invalid());
    };
    let Some(TypeData::Mapped(original)) = store
        .type_payload(mapped.object.target.unwrap_or(type_))
        .map(TypeRecord::data)
    else {
        return Err(invalid());
    };
    let Some(TypeData::Index(index)) = original
        .constraint_type
        .and_then(|constraint| store.type_payload(constraint))
        .map(TypeRecord::data)
    else {
        return Ok(None);
    };
    let template = original.template_type.ok_or_else(invalid)?;
    conditional_mapped_template_source_is_exact(
        store,
        original.declaration.ok_or_else(invalid)?,
        template,
        index.target,
        original.type_parameter.ok_or_else(invalid)?,
    )
    .map(|supported| supported.then_some(template))
}

fn reject_deferred_conditional_mapped_demand(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), MappedTypeError> {
    if let Some(template) = deferred_conditional_mapped_template(store, type_)? {
        return Err(MappedTypeError::UnsupportedTemplate(template));
    }
    Ok(())
}

/// The original alias row owns this lookup. This proof does not inspect mapped
/// property values, so cached value validation cannot recurse through itself.
#[cfg(test)]
fn source_conditional_mapped_demand(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<SourceConditionalMappedDemand, MappedTypeError> {
    source_conditional_mapped_demand_with_array_targets(store, type_, None)
}

fn source_conditional_mapped_demand_with_array_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceConditionalMappedDemand, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(type_);
    let origin = source_mapped_lookup_origin(store, type_)?
        .ok_or(MappedTypeError::UnsupportedTemplate(type_))?;
    let Some(TypeData::Mapped(payload)) = store.type_payload(type_).map(TypeRecord::data) else {
        return Err(invalid());
    };
    let argument = payload.modifiers_type.ok_or_else(invalid)?;
    let parameter = payload.type_parameter.ok_or_else(invalid)?;
    let mapper = payload
        .object
        .mapper
        .ok_or(MappedTypeError::UnsupportedTemplate(origin.template))?;
    let lookup = validated_source_mapped_lookup_request(store, type_)?.lookup;
    let Some(TypeData::IndexedAccess(indexed)) = store.type_payload(lookup).map(TypeRecord::data)
    else {
        return Err(invalid());
    };
    if indexed.object_type != type_ {
        return Err(invalid());
    }
    store.validate_prop_types_required_keys_instantiation_worker(
        origin.alias,
        origin.declared_lookup,
        &[origin.source],
        &[argument],
        lookup,
        false,
    )?;
    // Retained source productions prove the complete ordered capture vector.
    if cached_source_conditional_instantiation_with_array_targets(
        store,
        origin.template,
        &[origin.source, origin.key],
        &[origin.source, origin.key],
        array_targets,
    )
    .map_err(|_| invalid())?
        != Some(origin.template)
    {
        return Err(invalid());
    }
    source_mapped_lookup_state_is_warm(store, origin, type_)?;
    // Recovery can retain a value before the concrete conditional result is cached.
    // Check the actual input graph even when this read returns no cached result.
    let _ = cached_source_conditional_instantiation_with_array_targets(
        store,
        origin.template,
        &[origin.source, origin.key],
        &[argument, indexed.index_type],
        array_targets,
    )
    .map_err(|_| invalid())?;
    Ok(SourceConditionalMappedDemand {
        origin,
        lookup,
        argument,
        parameter,
        mapper,
    })
}

fn source_conditional_mapped_key(
    store: &CanonicalTypeMapperStore,
    demand: SourceConditionalMappedDemand,
) -> Result<TypeId, MappedTypeError> {
    let Some(TypeData::IndexedAccess(indexed)) =
        store.type_payload(demand.lookup).map(TypeRecord::data)
    else {
        return Err(MappedTypeError::InvalidMappedType(demand.lookup));
    };
    let key = indexed.index_type;
    if !matches!(store.type_payload(key).map(TypeRecord::data),
        Some(TypeData::Literal(literal)) if matches!(literal.value, LiteralValue::String(_)))
    {
        return Err(MappedTypeError::UnsupportedConstraint(key));
    }
    Ok(key)
}

#[cfg(test)]
fn cached_source_mapped_template(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    key: TypeId,
) -> Result<Option<TypeId>, MappedTypeError> {
    cached_source_mapped_template_with_array_targets(store, type_, key, None)
}

fn cached_source_mapped_template_with_array_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    key: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, MappedTypeError> {
    let demand = source_conditional_mapped_demand_with_array_targets(store, type_, array_targets)?;
    if source_conditional_mapped_key(store, demand)? != key {
        return Err(MappedTypeError::InvalidMappedType(type_));
    }
    cached_source_conditional_instantiation_with_array_targets(
        store,
        demand.origin.template,
        &[demand.origin.source, demand.origin.key],
        &[demand.argument, key],
        array_targets,
    )
    .map_err(|error| match error {
        ConditionalTypeError::Declared(error) => MappedTypeError::Declared(error),
        _ => MappedTypeError::InvalidMappedType(type_),
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

// Base-constraint traversal can fill its cache before mapped members are requested.
fn unresolved_mapped_structure_is_valid(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    structured: &StructuredTypeData,
) -> bool {
    let base = structured.constrained.resolved_base_constraint;
    if base.is_some_and(|base| {
        base != type_
            && store.intrinsic_bootstrap().is_none_or(|bootstrap| {
                base != bootstrap.no_constraint_type && base != bootstrap.circular_constraint_type
            })
    }) {
        return false;
    }
    structured
        == &StructuredTypeData {
            constrained: ConstrainedTypeData {
                resolved_base_constraint: base,
            },
            ..StructuredTypeData::default()
        }
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
        || record.data().structured().is_none_or(|structured| {
            !unresolved_mapped_structure_is_valid(store, type_, structured)
        })
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
    } else if !utility_modifiers
        && modifiers_type
            != mapped_modifiers_type_from_constraint(store, constraint)?
                .unwrap_or(bootstrap.unknown_type)
    {
        return Err(invalid());
    }
    Ok(())
}

/// Replays the physical arguments of a mapped forwarding alias from its
/// declared result. Its own formals and the mapped declaration keep separate identities.
fn forwarded_mapped_alias_arguments(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    alias: SemanticSymbolId,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Vec<TypeId>, MappedTypeError> {
    let invalid = || MappedTypeError::InvalidMappedType(target);
    let header =
        property_object_alias_identity_source_header(store, alias).map_err(|_| invalid())?;
    let links = store.type_alias_links(alias).ok_or_else(invalid)?;
    let parameters = links.type_parameters.as_deref().ok_or_else(invalid)?;
    let declared = links
        .declared_type
        .filter(|type_| *type_ != target)
        .ok_or_else(invalid)?;
    let body = store
        .source_direct_type_annotation(header.alias_declaration)
        .ok_or_else(invalid)?;
    if parameters.len() != header.parameters.len()
        || parameters.len() != arguments.len()
        || parameters
            .iter()
            .zip(&header.parameters)
            .any(|(type_, (_, symbol))| {
                cached_ordinary_type_parameter_owner(store, *type_) != Some(*symbol)
            })
        || !store.source_direct_type_annotation_is_exact(body, declared)
    {
        return Err(invalid());
    }
    let declared_record = store.type_payload(declared).ok_or_else(invalid)?;
    let TypeData::Mapped(wrapper) = declared_record.data() else {
        return Err(invalid());
    };
    let identity = declared_record
        .alias()
        .and_then(|alias| store.type_alias(alias))
        .ok_or_else(invalid)?;
    if wrapper.object.target != Some(target)
        || identity.symbol() != Some(alias)
        || identity.type_arguments().unwrap_or_default() != parameters
    {
        return Err(invalid());
    }
    // This is the declaration-only wrapper case below. It does not recurse
    // through a concrete wrapper's instantiation cache.
    validate_mapped_relation_identity(store, declared)?;
    let TypeData::Mapped(original) = store.type_payload(target).ok_or_else(invalid)?.data() else {
        return Err(invalid());
    };
    let declaration = original.declaration.ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(owner)) = store.source_node_parent(declaration) else {
        return Err(invalid());
    };
    let owner = store.source_declaration_symbol(owner).ok_or_else(invalid)?;
    let source = store.type_alias_links(owner).ok_or_else(invalid)?;
    if source.declared_type != Some(target) {
        return Err(invalid());
    }
    let formals = source.type_parameters.as_deref().ok_or_else(invalid)?;
    let mapper = wrapper.object.mapper.ok_or_else(invalid)?;
    let Some(TypeMapperApplication::Composite { second, .. }) =
        store.mapper_application(mapper, original.type_parameter.ok_or_else(invalid)?)
    else {
        return Err(invalid());
    };
    formals
        .iter()
        .map(|formal| {
            let symbolic = store.map_type(second, *formal).ok_or_else(invalid)?;
            cached_instantiation_with_vector(
                store,
                symbolic,
                parameters,
                arguments,
                array_targets,
                None,
            )
            .map_err(|_| invalid())?
            .ok_or(MappedTypeError::UnsupportedSource(symbolic))
        })
        .collect()
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
    let target = mapped.object.target.unwrap_or(type_);
    if matches!(store.type_payload(target).map(TypeRecord::data),
        Some(TypeData::Mapped(original)) if matches!(original.object.instantiations, TypeCacheState::Allocated(_)))
    {
        return generic_mapped_type_projection(store, type_, None)?
            .map(|_| ())
            .ok_or_else(invalid);
    }
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
        {
            return Err(invalid());
        }
        if owner_links.declared_type == Some(type_) {
            if owner_links.type_parameters.as_deref().unwrap_or_default() != owner_arguments
                || !store.source_direct_type_annotation_is_exact(body, type_)
            {
                return Err(invalid());
            }
        } else if forwarded_mapped_alias_arguments(store, target, owner, owner_arguments, None)?
            != arguments
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

/// An uncaptured source formal stays unchanged in the mapped record. A
/// formal with no written constraint has no apparent modifier members.
fn unconstrained_modifier_has_no_members(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<bool, MappedTypeError> {
    let Some(TypeData::TypeParameter(parameter)) = store.type_payload(type_).map(TypeRecord::data)
    else {
        return Ok(false);
    };
    if source_mapped_parameter_constraint(store, type_)?.is_some() {
        return Err(MappedTypeError::UnsupportedSource(type_));
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(MappedTypeError::BootstrapUninitialized)?;
    if parameter
        .constrained
        .resolved_base_constraint
        .is_some_and(|cached| cached != bootstrap.no_constraint_type)
    {
        return Err(MappedTypeError::InvalidSource(type_));
    }
    Ok(true)
}

fn source_properties(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Vec<SourceProperty>, MappedTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(MappedTypeError::InvalidSource(type_))?;
    if unconstrained_modifier_has_no_members(store, type_)? {
        return Ok(Vec::new());
    }
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
    if unconstrained_modifier_has_no_members(store, type_)? {
        return Ok(Vec::new());
    }
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
    validate_warm_mapped_members_with_array_targets(
        store,
        shape,
        expected_properties,
        expected_indexes,
        None,
    )
}

fn validate_warm_mapped_members_with_array_targets(
    store: &CanonicalTypeMapperStore,
    shape: &MappedShape,
    expected_properties: &[PlannedMappedProperty],
    expected_indexes: &[PlannedMappedIndex],
    array_targets: Option<CanonicalArrayTargets>,
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
        if !unresolved_mapped_structure_is_valid(store, shape.type_, structured) {
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
                recovery.matches(store, *symbol, shape, key_type, cached, array_targets)
            } else {
                cached_mapped_property_type(store, shape, expected, key_type, array_targets)?
                    == Some(cached)
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
        .prepare_type_query_types_with_session(
            &pending_strings,
            &[],
            &[],
            union_operations,
            0,
            session,
        )
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
    reject_deferred_conditional_mapped_demand(store, shape.type_)?;
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
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, MappedTypeError> {
    let source_conditional = source_mapped_lookup_origin(store, shape.type_)?.is_some();
    if !source_conditional {
        reject_deferred_conditional_mapped_demand(store, shape.type_)?;
    }
    let direct_request = !source_conditional && direct_mapped_request_template(store, shape)?;
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
    let raw = if source_conditional {
        cached_source_mapped_template_with_array_targets(
            store,
            shape.type_,
            key_type,
            array_targets,
        )?
    } else {
        match template.data() {
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
                cached_instantiation_with_vector(
                    store,
                    template_type,
                    &sources,
                    &targets,
                    None,
                    None,
                )
                .map_err(|error| mapped_instantiation_error(template_type, &error))?
            }
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
    compute_mapped_property_type_worker(store, containing_type, symbol, key_type, session, None)
}

fn compute_mapped_property_type_worker(
    store: &mut CanonicalTypeMapperStore,
    containing_type: TypeId,
    symbol: SemanticSymbolId,
    key_type: TypeId,
    session: &mut InstantiationSession,
    source: Option<&mut MappedConditionalSource<'_>>,
) -> Result<TypeId, MappedTypeError> {
    let shape = validate_mapped_shape(store, containing_type)?;
    let mut type_ = match source {
        Some(source) => {
            instantiate_source_mapped_template(store, &shape, key_type, session, source)?
        }
        None => instantiate_mapped_template(store, &shape, key_type, session)?,
    };
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
        type_ = store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &[type_, missing],
                None,
                None,
                session,
            )
            .map_err(mapped_cache_error)?;
    } else if strip_optional {
        let sentinel = if exact { missing } else { undefined };
        type_ = remove_type(store, type_, sentinel, session)?;
        if !exact {
            type_ = remove_type(store, type_, void, session)?;
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
    // Conditional branch substitution is not part of deferred alias identity.
    reject_deferred_conditional_mapped_demand(store, shape.type_)?;
    // Go adds explicit optionality before substitution, including its depth frame.
    let template_type = match mapped_optional_template_sentinel(store, shape)? {
        Some(sentinel) if direct_mapped_request_template(store, shape)? => {
            return instantiate_direct_mapped_request_template(
                store, shape, key_type, sentinel, session,
            );
        }
        Some(missing) => store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &[shape.template_type, missing],
                None,
                None,
                session,
            )
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

fn instantiate_source_mapped_template(
    store: &mut CanonicalTypeMapperStore,
    shape: &MappedShape,
    key_type: TypeId,
    session: &mut InstantiationSession,
    source: &mut MappedConditionalSource<'_>,
) -> Result<TypeId, MappedTypeError> {
    let array_targets = Some(CanonicalArrayTargets::from_global_types(source.globals));
    let demand =
        source_conditional_mapped_demand_with_array_targets(store, shape.type_, array_targets)?;
    if source_conditional_mapped_key(store, demand)? != key_type {
        return Err(MappedTypeError::InvalidMappedType(shape.type_));
    }
    source.branches.preflight(store, demand.origin.template)?;
    if let Some(cached) = cached_source_mapped_template_with_array_targets(
        store,
        shape.type_,
        key_type,
        array_targets,
    )? {
        return Ok(cached);
    }
    if !store.try_reserve_mappers(2) {
        return Err(MappedTypeError::Capacity);
    }
    let mapper = store
        .append_type_mapping(Some(demand.mapper), demand.parameter, key_type)
        .ok_or(MappedTypeError::InvalidMappedType(shape.type_))?;
    instantiate_type_with_source(
        store,
        demand.origin.template,
        mapper,
        source.globals,
        session,
        source.branches,
    )
    .map_err(|error| mapped_instantiation_error(demand.origin.template, &error))
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
            store
                .literal_union_type_with_alias_and_array_targets_and_session(
                    &[value, sentinel],
                    None,
                    None,
                    session,
                )
                .map_err(mapped_cache_error)
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
        _ => store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &values, None, None, session,
            )
            .map_err(mapped_cache_error),
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
    session: &mut InstantiationSession,
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
        _ => store
            .literal_union_type_with_alias_and_array_targets_and_session(
                &retained, None, None, session,
            )
            .map_err(mapped_cache_error),
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
        InstantiationError::Declared(error) => MappedTypeError::Declared(*error),
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
        MappedTypeModifiers, SourceMappedLookupProjection, SupportedMappedAliasKind,
        SupportedMappedAliasProjection, cached_source_mapped_lookup_instance,
        cached_supported_mapped_alias_instance, instantiate_source_mapped_lookup_instance,
        instantiate_supported_mapped_alias_instance, plan_mapped_type_declaration,
        plan_mapped_type_keys, selection_alias_source_constraint,
        source_mapped_lookup_identity_projection, source_mapped_lookup_projection,
        supported_mapped_alias_projection, unresolved_mapped_structure_is_valid,
    };
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
        CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
        IntrinsicBootstrapOptions, TypeData, TypeId, TypeMapperId,
        array_types::CanonicalArrayTargets,
        bootstrap::UnionReduction,
        callable_sets::{
            StoredCallableSetValidation, validate_stored_callable_set_with_array_targets,
        },
        calls::DirectCallForm,
        conditional_types::{ConditionalTypeBranches, get_false_type_from_conditional_type},
        constraints::get_base_constraint_of_type,
        declared::{execute_type_parameter, type_list_key},
        generic_calls::{
            GenericCallVectorError, GenericCallVectorRequest,
            demand_generic_call_vector_selected_return,
        },
        generic_method_calls::{GenericMethodCallSelection, resolve_generic_method_call},
        instantiate::{
            InstantiationError, InstantiationLimits, InstantiationSession,
            cached_instantiation_with_vector, instantiate_type_with_session,
            instantiate_type_with_vector_and_session,
        },
        instantiated_members::validate_generic_interface_members,
        keyof_types::{
            NongenericKeyofError, cached_nongeneric_keyof_type, plan_nongeneric_keyof_type,
            resolve_nongeneric_keyof_type,
        },
        links::{TypeAliasLinks, ValueSymbolLinks},
        object_members,
        production::GlobalMergeCompletion,
        signatures::IndexFlags,
        structured_members::{
            InterfaceHeritageMembersValidation, validate_interface_heritage_members,
        },
        type_nodes::{CanonicalTypeQuery, TypeNodeUnavailable, type_alias_instantiation_cache_key},
        type_records::{ConditionalTypeData, LiteralValue, StructuredTypeData, TypeCacheState},
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

    const MAPPED_SESSION_LIBRARY: &str = concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {} ",
        "interface Base<T> { value: T; [index: number]: number; }",
    );

    fn mapped_session_context<'arena>(
        library: &'arena ParseResult,
        parsed: &'arena ParseResult,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (file, source, declaration, path) in [
            (
                FileId::new(1),
                library,
                true,
                "\"/project/mapped-session-library.d.ts\"",
            ),
            (
                FileId::new(0),
                parsed,
                false,
                "\"/project/mapped-session.ts\"",
            ),
        ] {
            assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (FileId::new(1), &library.arena),
                (FileId::new(0), &parsed.arena),
            ],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn mapped_session_interface(store: &CanonicalTypeMapperStore, name: &str) -> TypeId {
        let owner = store
            .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source(name))
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap()
    }

    fn mapped_session_counts(store: &CanonicalTypeMapperStore) -> ([usize; 12], [usize; 26]) {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            [
                store.type_len(),
                store.mapper_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.signature_len(),
                store.index_info_len(),
                store.type_alias_len(),
                store.conditional_root_len(),
                bootstrap.union_cache_len(),
                bootstrap.union_of_union_cache_len(),
                store.properties_type_cache_len(),
                store.cached_signature_len(),
            ],
            store.checker_link_allocated_lengths(),
        )
    }

    struct MappedSessionProxy {
        symbol: SemanticSymbolId,
        mapper: TypeMapperId,
        template: TypeId,
        value: TypeId,
        rejected_source: TypeId,
        union_result: TypeId,
    }

    fn prepare_dirty_mapped_session_cache(
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
    ) -> MappedSessionProxy {
        let derived = mapped_session_interface(store, "Derived");
        let plain = mapped_session_interface(store, "Plain");
        let TypeData::Interface(data) = store.type_payload(derived).unwrap().data() else {
            panic!("Derived must retain its real inherited interface")
        };
        let base = data.resolved_base_types.as_ref().unwrap()[0];
        let proxy = store
            .symbol_table(data.reference.object.structured.members.unwrap())
            .and_then(|members| members.get_source("value"))
            .unwrap();
        assert!(store.instantiated_property_recovery(proxy).is_none());
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let source_union = store
            .expression_union_type_with_global_types_and_session(
                globals,
                &[number, derived],
                UnionReduction::Literal,
                &mut setup,
            )
            .unwrap();
        let rows = store
            .intrinsic_bootstrap()
            .unwrap()
            .union_of_union_cache_len();
        let union_result = store
            .expression_union_type_with_global_types_and_session(
                globals,
                &[source_union, plain],
                UnionReduction::Subtype,
                &mut setup,
            )
            .unwrap();
        assert_eq!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
            rows + 1
        );
        let original = store.value_symbol_links(proxy).unwrap().clone();
        assert_eq!(original.resolved_type, Some(number));
        assert!(store.instantiated_property_recovery(proxy).is_none());
        let mapper = original.mapper.unwrap();
        let template = store
            .value_symbol_links(original.target.unwrap())
            .unwrap()
            .resolved_type
            .unwrap();
        assert!(matches!(
            store.type_payload(template).unwrap().data(),
            TypeData::TypeParameter(_)
        ));
        // Reopen only the real proxy's lazy value before the query. Its source,
        // target, mapper, and all other links stay unchanged. No recovery exists.
        let cold = ValueSymbolLinks {
            resolved_type: None,
            ..original
        };
        assert!(store.set_value_symbol_links(proxy, cold.clone()));
        store.mark_union_cache_validation_dirty();
        assert_eq!(store.value_symbol_links(proxy), Some(&cold));
        assert_eq!(
            validate_interface_heritage_members(store, derived),
            InterfaceHeritageMembersValidation::Valid
        );
        assert!(
            validate_generic_interface_members(store, base, None)
                .unwrap()
                .is_some()
        );
        MappedSessionProxy {
            symbol: proxy,
            mapper,
            template,
            value: number,
            rejected_source: derived.max(plain),
            union_result,
        }
    }

    fn spent_mapped_session(
        store: &mut CanonicalTypeMapperStore,
        proxy: &MappedSessionProxy,
        max_count: usize,
    ) -> InstantiationSession {
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_count,
            ..InstantiationLimits::default()
        });
        assert_eq!(
            instantiate_type_with_session(store, proxy.template, proxy.mapper, None, &mut session),
            Ok(proxy.value)
        );
        assert_eq!((session.query_count(), session.total_count()), (1, 1));
        assert_eq!(session.limit_event_count(), 0);
        assert_eq!(
            store
                .value_symbol_links(proxy.symbol)
                .unwrap()
                .resolved_type,
            None
        );
        session
    }

    fn assert_mapped_alias_selected_return_preparation(
        recovering_limit: bool,
        recovering_replay: bool,
    ) {
        let library = parse_source_file(MAPPED_SESSION_LIBRARY);
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Payload { firstKey: number; secondKey: string; } ",
            "type Copy<T> = { [K in keyof T]: T[K] }; ",
            "interface Api { map<T>(value: T): Copy<T>; map(a: number, b: number): number; }",
        ));
        let mut context = mapped_session_context(&library, &parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        assert!(context.diagnostics().is_empty());
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), FileId::new(0), node),
                    NodeRef::new(parsed.arena.id(), FileId::new(0), method.name),
                ))
            })
            .unwrap();
        let callee = context.get_type_at_location(name).unwrap();
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let StoredCallableSetValidation::Valid {
            projection: group, ..
        } = validate_stored_callable_set_with_array_targets(context.store(), callee, Some(targets))
        else {
            panic!("the source method must retain its two real signatures")
        };
        assert_eq!(group.call_signatures.len(), 2);
        let original = group.call_signatures[0].signature;
        let original_signature = context.store().signature(original).unwrap();
        assert_eq!(original_signature.declaration(), Some(declaration));
        let template = original_signature.resolved_return_type().unwrap();
        let projection =
            supported_mapped_alias_projection(context.store(), template, Some(targets))
                .unwrap()
                .unwrap();
        assert_eq!(projection.arguments, original_signature.type_parameters());
        assert_eq!(
            projection.kind,
            SupportedMappedAliasKind::Homomorphic(MappedTypeModifiers::NONE)
        );
        let payload = mapped_session_interface(context.store(), "Payload");
        let store = context.store_mut_for_test();
        let key_plan = plan_nongeneric_keyof_type(store, payload).unwrap();
        assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
        let proxy = prepare_dirty_mapped_session_cache(store, &globals);
        let arguments = [payload];
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: Some(&arguments),
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let limits = InstantiationLimits {
            max_count: 3,
            ..InstantiationLimits::default()
        };
        let error = store.intrinsic_bootstrap().unwrap().error_type;
        let mut limited = if recovering_limit {
            InstantiationSession::new_recovering(store, limits, error).unwrap()
        } else {
            InstantiationSession::new(limits)
        };
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut limited)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("the one-argument call must select its generic method")
        };
        let signature = generic.projection().instantiation.signature;
        assert_eq!(generic.projection().generic_signature, original);
        assert_eq!(generic.projection().instantiation.type_arguments, arguments);
        assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        let alias_links = store.type_alias_links(projection.alias).unwrap().clone();
        let before = mapped_session_counts(store);
        let scans = store.union_cache_validation_scan_count();
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut limited),
            Err(GenericCallVectorError::Instantiation(
                InstantiationError::InvalidType(template)
            ))
        );
        assert_eq!(
            (
                limited.query_count(),
                limited.total_count(),
                limited.limit_event_count()
            ),
            (3, 3, 1)
        );
        assert_eq!(store.union_cache_validation_scan_count(), scans + 1);
        assert_eq!(
            store
                .value_symbol_links(proxy.symbol)
                .unwrap()
                .resolved_type,
            recovering_limit.then_some(error)
        );
        if recovering_limit {
            assert!(
                store
                    .instantiated_property_recovery(proxy.symbol)
                    .unwrap()
                    .matches_published_links(store.value_symbol_links(proxy.symbol))
            );
        } else {
            assert!(store.instantiated_property_recovery(proxy.symbol).is_none());
        }
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        assert_eq!(store.type_alias_links(projection.alias), Some(&alias_links));
        assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
        assert_eq!(mapped_session_counts(store), before);
        assert!(store.type_resolution_is_empty());
        let retry = demand_generic_call_vector_selected_return(store, generic, &mut limited)
            .map(|(type_, _)| type_);
        if recovering_limit {
            assert_eq!(retry, Ok(error));
        } else {
            assert_eq!(
                retry,
                Err(GenericCallVectorError::Instantiation(
                    InstantiationError::CountLimit { count: 3, limit: 3 }
                ))
            );
        }
        assert_eq!(
            (
                limited.query_count(),
                limited.total_count(),
                limited.limit_event_count()
            ),
            (3, 3, 2)
        );
        assert_eq!(mapped_session_counts(store), before);
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        assert_eq!(store.type_alias_links(projection.alias), Some(&alias_links));
        assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
        if recovering_limit {
            let mut fresh = InstantiationSession::new(InstantiationLimits::default());
            // Keep the actual recovery receipt. It must not validate the old
            // subtype result or become an ordinary mapped alias instance.
            assert_eq!(
                super::instantiate_supported_mapped_alias_instance_with_session(
                    store,
                    &projection,
                    &arguments,
                    (projection.alias, &arguments),
                    Some(targets),
                    &mut fresh,
                ),
                Err(MappedTypeError::InvalidMappedType(proxy.union_result))
            );
            assert_eq!(
                (
                    fresh.query_count(),
                    fresh.total_count(),
                    fresh.limit_event_count()
                ),
                (0, 0, 0)
            );
            assert_eq!(
                store
                    .value_symbol_links(proxy.symbol)
                    .unwrap()
                    .resolved_type,
                Some(error)
            );
            assert!(
                store
                    .instantiated_property_recovery(proxy.symbol)
                    .unwrap()
                    .matches_published_links(store.value_symbol_links(proxy.symbol))
            );
            assert_eq!(store.type_alias_links(projection.alias), Some(&alias_links));
            assert_eq!(
                store.signature(signature).unwrap().resolved_return_type(),
                None
            );
            assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
            assert_eq!(mapped_session_counts(store), before);
            assert!(store.type_resolution_is_empty());
            assert!(context.diagnostics().is_empty());
            return;
        }
        let mut adequate = if recovering_replay {
            InstantiationSession::new_recovering(store, InstantiationLimits::default(), error)
                .unwrap()
        } else {
            InstantiationSession::new(InstantiationLimits::default())
        };
        let result = demand_generic_call_vector_selected_return(store, generic, &mut adequate)
            .unwrap()
            .0;
        let actual = supported_mapped_alias_projection(store, result, Some(targets))
            .unwrap()
            .unwrap();
        assert_eq!(actual.alias, projection.alias);
        assert_eq!(actual.declared_type, projection.declared_type);
        assert_eq!(actual.arguments, arguments);
        assert_eq!(actual.identity_arguments, arguments);
        assert_eq!(actual.identity_symbol, projection.alias);
        let TypeData::Mapped(mapped) = store.type_payload(result).unwrap().data() else {
            unreachable!()
        };
        assert_eq!(
            mapped.constraint_type,
            cached_nongeneric_keyof_type(store, &key_plan).unwrap()
        );
        assert_eq!(mapped.modifiers_type, Some(payload));
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            Some(result)
        );
        assert_eq!(
            store.signature(original).unwrap().resolved_return_type(),
            Some(template)
        );
        assert_eq!(
            store
                .value_symbol_links(proxy.symbol)
                .unwrap()
                .resolved_type,
            Some(proxy.value)
        );
        assert!(adequate.total_count() >= 3);
        assert_eq!(adequate.limit_event_count(), 0);
        let warm = mapped_session_counts(store);
        let count = adequate.total_count();
        for _ in 0..2 {
            assert_eq!(
                resolve_generic_method_call(
                    store,
                    &globals,
                    false,
                    request,
                    Some(signature),
                    &mut adequate
                ),
                Ok(Some(selected.clone()))
            );
            assert_eq!(
                demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                    .unwrap()
                    .0,
                result
            );
            assert_eq!(
                super::instantiate_supported_mapped_alias_instance_with_session(
                    store,
                    &projection,
                    &arguments,
                    (projection.alias, &arguments),
                    Some(targets),
                    &mut limited,
                ),
                Ok(result)
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(
                (
                    limited.query_count(),
                    limited.total_count(),
                    limited.limit_event_count()
                ),
                (3, 3, 2)
            );
            assert_eq!(mapped_session_counts(store), warm);
            assert!(store.type_resolution_is_empty());
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn mapped_alias_selected_return_preparation_keeps_the_callers_spent_budget() {
        for recovering_replay in [false, true] {
            assert_mapped_alias_selected_return_preparation(false, recovering_replay);
        }
    }

    #[test]
    fn mapped_alias_return_recovery_keeps_the_real_dirty_cache_error_and_receipt() {
        assert_mapped_alias_selected_return_preparation(true, false);
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum MappedValueUnionCase {
        ExplicitOptional,
        WrappedValue,
        StripOptional,
    }

    fn assert_mapped_value_union_preparation(case: MappedValueUnionCase) {
        let library = parse_source_file(MAPPED_SESSION_LIBRARY);
        let declarations = match case {
            MappedValueUnionCase::ExplicitOptional => concat!(
                "interface Shape { item: number; } ",
                "type Soft<T> = { [K in keyof T]?: T[K] }; ",
                "declare const mapped: Soft<Shape>;",
            ),
            MappedValueUnionCase::WrappedValue => concat!(
                "type DeclaredValue = number | undefined; ",
                "interface Wrapper<T> { value: T; } ",
                "interface Shape { item?: DeclaredValue; } ",
                "type Cells<T> = { [K in keyof T]: Wrapper<T[K]> }; ",
                "declare const mapped: Cells<Shape>;",
            ),
            MappedValueUnionCase::StripOptional => concat!(
                "interface Shape { item?: number | string | void; } ",
                "type Force<T> = { [K in keyof T]-?: T[K] }; ",
                "declare const mapped: Force<Shape>;",
            ),
        };
        let parsed = parse_source_file(&format!(
            "interface Derived extends Base<number> {{}} \
             interface Plain {{ value: number; }} {declarations}"
        ));
        for recovering_replay in [false, true] {
            let mut context = mapped_session_context(&library, &parsed);
            context.check_source_file(FileId::new(0)).unwrap();
            assert!(context.diagnostics().is_empty());
            let annotation = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    variable
                        .type_
                        .map(|node| NodeRef::new(parsed.arena.id(), FileId::new(0), node))
                })
                .unwrap();
            let mapped = context.get_type_from_type_node(annotation).unwrap();
            let source_property = source_property(&parsed, &context, "item");
            let globals = context.global_types().clone();
            let store = context.store_mut_for_test();
            let source_links = store.value_symbol_links(source_property).unwrap().clone();
            let source_value = source_links.resolved_type.unwrap();
            if case == MappedValueUnionCase::WrappedValue {
                let record = store.type_payload(source_value).unwrap();
                let TypeData::Union(union) = record.data() else {
                    panic!("the written annotation must retain its named union")
                };
                assert!(record.alias().is_some());
                assert_eq!(
                    union.union.types.first(),
                    Some(&store.intrinsic_bootstrap().unwrap().undefined_type)
                );
            }
            if case == MappedValueUnionCase::StripOptional {
                let TypeData::Union(union) = store.type_payload(source_value).unwrap().data()
                else {
                    panic!("the source annotation must retain both values and void")
                };
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                assert_eq!(union.union.types.len(), 3);
                assert!(union.union.types.contains(&bootstrap.number_type));
                assert!(union.union.types.contains(&bootstrap.string_type));
                assert!(union.union.types.contains(&bootstrap.void_type));
                assert!(!union.union.types.contains(&bootstrap.undefined_type));
            }
            let mut setup = InstantiationSession::new(InstantiationLimits::default());
            let members = store
                .resolve_mapped_type_members_with_session(
                    mapped,
                    MappedTypeModifiers::NONE,
                    &mut setup,
                )
                .unwrap();
            let [property] = members.properties() else {
                panic!("the source mapped alias must retain one property")
            };
            let property = *property;
            assert_eq!(
                store.value_symbol_links(property).unwrap().resolved_type,
                None
            );
            assert_eq!(
                store
                    .mapped_symbol_links(property)
                    .unwrap()
                    .synthetic_origin,
                Some(source_property)
            );
            let shape = super::validate_mapped_shape(store, mapped).unwrap();
            let key = store
                .mapped_symbol_links(property)
                .unwrap()
                .key_type
                .unwrap();
            let (sources, targets) = super::mapped_template_mapping(&shape, key);
            let proxy = prepare_dirty_mapped_session_cache(store, &globals);
            let limit = if case == MappedValueUnionCase::WrappedValue {
                5
            } else {
                1
            };
            let mut limited = spent_mapped_session(store, &proxy, limit);
            let before = mapped_session_counts(store);
            let scans = store.union_cache_validation_scan_count();
            assert_eq!(
                store.resolve_mapped_symbol_type_with_session(property, &mut limited),
                Err(MappedTypeError::InvalidMappedType(proxy.rejected_source))
            );
            assert_eq!(
                (
                    limited.query_count(),
                    limited.total_count(),
                    limited.limit_event_count()
                ),
                (limit, limit, 1)
            );
            assert_eq!(store.union_cache_validation_scan_count(), scans + 1);
            assert_eq!(
                store.value_symbol_links(property).unwrap().resolved_type,
                None
            );
            assert!(store.mapped_property_recovery(property).is_none());
            assert_eq!(
                store
                    .value_symbol_links(proxy.symbol)
                    .unwrap()
                    .resolved_type,
                None
            );
            assert!(store.instantiated_property_recovery(proxy.symbol).is_none());
            assert_eq!(
                store.value_symbol_links(source_property),
                Some(&source_links)
            );
            assert!(store.type_resolution_is_empty());
            if case == MappedValueUnionCase::WrappedValue {
                // Wrapper mapping precedes optionality. Its complete reference
                // may remain cached, but the mapped property must stay cold.
                let wrapper = cached_instantiation_with_vector(
                    store,
                    shape.template_type,
                    &sources,
                    &targets,
                    None,
                    None,
                )
                .unwrap()
                .unwrap();
                let TypeData::TypeReference(reference) =
                    store.type_payload(wrapper).unwrap().data()
                else {
                    panic!("the completed inner mapping must retain its Wrapper reference")
                };
                assert_eq!(
                    reference.resolved_type_arguments.as_deref(),
                    Some(&[source_value][..])
                );
                assert_eq!(store.validate_union_constituent(wrapper), Ok(()));
            } else {
                assert_eq!(mapped_session_counts(store), before);
            }
            let failed = mapped_session_counts(store);
            let retry_error = if case == MappedValueUnionCase::WrappedValue {
                MappedTypeError::InstantiationCountLimit {
                    count: limit,
                    limit,
                }
            } else {
                MappedTypeError::InvalidMappedType(proxy.rejected_source)
            };
            assert_eq!(
                store.resolve_mapped_symbol_type_with_session(property, &mut limited),
                Err(retry_error)
            );
            assert_eq!(
                (
                    limited.query_count(),
                    limited.total_count(),
                    limited.limit_event_count()
                ),
                (limit, limit, 2)
            );
            assert_eq!(mapped_session_counts(store), failed);
            assert_eq!(
                store.value_symbol_links(property).unwrap().resolved_type,
                None
            );
            assert_eq!(
                store
                    .value_symbol_links(proxy.symbol)
                    .unwrap()
                    .resolved_type,
                None
            );
            assert!(store.type_resolution_is_empty());
            let error = store.intrinsic_bootstrap().unwrap().error_type;
            let mut adequate = if recovering_replay {
                InstantiationSession::new_recovering(store, InstantiationLimits::default(), error)
                    .unwrap()
            } else {
                InstantiationSession::new(InstantiationLimits::default())
            };
            let result = store
                .resolve_mapped_symbol_type_with_session(property, &mut adequate)
                .unwrap();
            assert!(adequate.total_count() > 0);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(
                store
                    .value_symbol_links(proxy.symbol)
                    .unwrap()
                    .resolved_type,
                Some(proxy.value)
            );
            assert!(store.instantiated_property_recovery(proxy.symbol).is_none());
            assert!(store.mapped_property_recovery(property).is_none());
            let TypeData::Union(union) = store.type_payload(result).unwrap().data() else {
                panic!("the requested mapped value must retain two constituents")
            };
            assert_eq!(union.union.types.len(), 2);
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            match case {
                MappedValueUnionCase::ExplicitOptional => {
                    assert!(union.union.types.contains(&bootstrap.number_type));
                    assert!(union.union.types.contains(&bootstrap.undefined_type));
                }
                MappedValueUnionCase::WrappedValue => {
                    assert!(union.union.types.contains(&bootstrap.undefined_type));
                    let wrapper = cached_instantiation_with_vector(
                        store,
                        shape.template_type,
                        &sources,
                        &targets,
                        None,
                        None,
                    )
                    .unwrap()
                    .unwrap();
                    assert!(union.union.types.contains(&wrapper));
                }
                MappedValueUnionCase::StripOptional => {
                    assert!(union.union.types.contains(&bootstrap.number_type));
                    assert!(union.union.types.contains(&bootstrap.string_type));
                    assert!(!union.union.types.contains(&bootstrap.void_type));
                }
            }
            assert_eq!(
                store.value_symbol_links(source_property),
                Some(&source_links)
            );
            let warm = mapped_session_counts(store);
            let count = adequate.total_count();
            for _ in 0..2 {
                assert_eq!(
                    store.resolve_mapped_symbol_type_with_session(property, &mut limited),
                    Ok(result)
                );
                assert_eq!(
                    store.resolve_mapped_type_members_with_session(
                        mapped,
                        MappedTypeModifiers::NONE,
                        &mut adequate
                    ),
                    Ok(members.clone())
                );
                assert_eq!(
                    (
                        limited.query_count(),
                        limited.total_count(),
                        limited.limit_event_count()
                    ),
                    (limit, limit, 2)
                );
                assert_eq!(adequate.total_count(), count);
                assert_eq!(adequate.limit_event_count(), 0);
                assert_eq!(mapped_session_counts(store), warm);
                assert!(store.type_resolution_is_empty());
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn mapped_explicit_optional_template_union_keeps_the_callers_spent_budget() {
        assert_mapped_value_union_preparation(MappedValueUnionCase::ExplicitOptional);
    }

    #[test]
    fn mapped_wrapper_optional_union_keeps_the_callers_spent_budget() {
        assert_mapped_value_union_preparation(MappedValueUnionCase::WrappedValue);
    }

    #[test]
    fn mapped_optional_removal_union_keeps_the_callers_spent_budget() {
        assert_mapped_value_union_preparation(MappedValueUnionCase::StripOptional);
    }

    fn assert_mapped_remap_preparation_uses_caller(value_demand: bool) {
        let library = parse_source_file(MAPPED_SESSION_LIBRARY);
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Shape { first: number; second: string; } ",
            "type Merged = { [K in keyof Shape as 'both']: Shape[K] };",
        ));
        let mut context = mapped_session_context(&library, &parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        assert!(context.diagnostics().is_empty());
        let mapped = alias_type(&parsed, &context, "Merged");
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let record = store.type_payload(mapped).unwrap();
        let TypeData::Mapped(data) = record.data() else {
            unreachable!()
        };
        assert_eq!(data.object.structured.members, None);
        assert!(
            !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let property = value_demand.then(|| {
            let members = store
                .resolve_mapped_type_members_with_session(
                    mapped,
                    MappedTypeModifiers::NONE,
                    &mut setup,
                )
                .unwrap();
            let [property] = members.properties() else {
                panic!("the two source keys must merge into one mapped property")
            };
            assert_eq!(
                store.value_symbol_links(*property).unwrap().resolved_type,
                None
            );
            *property
        });
        let proxy = prepare_dirty_mapped_session_cache(store, &globals);
        let mut limited = spent_mapped_session(store, &proxy, 1);
        let before = mapped_session_counts(store);
        let scans = store.union_cache_validation_scan_count();
        for event in 1..=2 {
            let result = if let Some(property) = property {
                store
                    .resolve_mapped_symbol_type_with_session(property, &mut limited)
                    .map(|_| ())
            } else {
                store
                    .resolve_mapped_type_members_with_session(
                        mapped,
                        MappedTypeModifiers::NONE,
                        &mut limited,
                    )
                    .map(|_| ())
            };
            assert_eq!(
                result,
                Err(MappedTypeError::InvalidMappedType(proxy.rejected_source))
            );
            assert_eq!(
                (
                    limited.query_count(),
                    limited.total_count(),
                    limited.limit_event_count()
                ),
                (1, 1, event)
            );
            assert_eq!(
                store.union_cache_validation_scan_count(),
                scans + usize::try_from(event).unwrap()
            );
            assert_eq!(
                store
                    .value_symbol_links(proxy.symbol)
                    .unwrap()
                    .resolved_type,
                None
            );
            assert!(store.instantiated_property_recovery(proxy.symbol).is_none());
            if let Some(property) = property {
                assert_eq!(
                    store.value_symbol_links(property).unwrap().resolved_type,
                    None
                );
                assert!(store.mapped_property_recovery(property).is_none());
            } else {
                let TypeData::Mapped(data) = store.type_payload(mapped).unwrap().data() else {
                    unreachable!()
                };
                assert_eq!(data.object.structured.members, None);
            }
            assert_eq!(mapped_session_counts(store), before);
            assert!(store.type_resolution_is_empty());
        }
        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let members = store
            .resolve_mapped_type_members_with_session(
                mapped,
                MappedTypeModifiers::NONE,
                &mut adequate,
            )
            .unwrap();
        let [actual_property] = members.properties() else {
            panic!("the merged source keys must keep one property")
        };
        let actual_property = *actual_property;
        assert!(property.is_none_or(|property| property == actual_property));
        assert_eq!(
            store.symbol(actual_property).unwrap().name().as_utf8(),
            Some("both")
        );
        let key = store
            .mapped_symbol_links(actual_property)
            .unwrap()
            .key_type
            .unwrap();
        let TypeData::Union(keys) = store.type_payload(key).unwrap().data() else {
            panic!("both original keys must remain in the mapped key union")
        };
        assert_eq!(keys.union.types.len(), 2);
        for expected in ["first", "second"] {
            assert!(
                keys.union.types.contains(
                    &store
                        .intrinsic_bootstrap()
                        .unwrap()
                        .cached_string_literal_type(expected)
                        .unwrap()
                )
            );
        }
        let value = store
            .resolve_mapped_symbol_type_with_session(actual_property, &mut adequate)
            .unwrap();
        let TypeData::Union(values) = store.type_payload(value).unwrap().data() else {
            panic!("the merged property must keep both source value types")
        };
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(values.union.types.len(), 2);
        assert!(values.union.types.contains(&bootstrap.number_type));
        assert!(values.union.types.contains(&bootstrap.string_type));
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        assert_eq!(
            store
                .value_symbol_links(proxy.symbol)
                .unwrap()
                .resolved_type,
            Some(proxy.value)
        );
        let warm = mapped_session_counts(store);
        let count = adequate.total_count();
        for _ in 0..2 {
            assert_eq!(
                store.resolve_mapped_type_members_with_session(
                    mapped,
                    MappedTypeModifiers::NONE,
                    &mut limited
                ),
                Ok(members.clone())
            );
            assert_eq!(
                store.resolve_mapped_symbol_type_with_session(actual_property, &mut limited),
                Ok(value)
            );
            assert_eq!(
                (
                    limited.query_count(),
                    limited.total_count(),
                    limited.limit_event_count()
                ),
                (1, 1, 2)
            );
            assert_eq!(adequate.total_count(), count);
            assert_eq!(mapped_session_counts(store), warm);
            assert!(store.type_resolution_is_empty());
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn mapped_remapped_key_unions_keep_the_callers_spent_budget() {
        assert_mapped_remap_preparation_uses_caller(false);
    }

    #[test]
    fn mapped_merged_value_unions_keep_the_callers_spent_budget() {
        assert_mapped_remap_preparation_uses_caller(true);
    }

    fn selection_call_fixture(
        parsed: &ParseResult,
    ) -> (
        CanonicalCheckerContext<'_>,
        SupportedMappedAliasProjection,
        TypeId,
    ) {
        let mut context = checker_context(parsed);
        context.check_source_file(FileId::new(0)).unwrap();
        assert!(context.diagnostics().is_empty());
        let annotation = parsed
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::FunctionDeclaration(function) => function.type_,
                _ => None,
            })
            .map(|node| NodeRef::new(parsed.arena.id(), FileId::new(0), node))
            .unwrap();
        let object = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FileId::new(0),
                    node,
                ))
            })
            .unwrap();
        let return_type = context.get_type_from_type_node(annotation).unwrap();
        let source = context.get_type_at_location(object).unwrap();
        let projection = supported_mapped_alias_projection(context.store(), return_type, None)
            .unwrap()
            .unwrap();
        (context, projection, source)
    }

    fn homomorphic_conditional_source(alias: &str, optional: &str) -> String {
        format!(
            "interface Cell<T> {{ value: T; }}\n\
             type Unwrap<V> = V extends Cell<infer R> ? R : never;\n\
             type {alias}<V> = {{ [K in keyof V]{optional}: Unwrap<V[K]> }};\n\
             declare function convert<T>(value: T): {alias}<T>;\n\
             const input = {{ a: 'a', b: 1 }};\n",
        )
    }

    fn nested_lookup_source(alias: &str) -> String {
        format!(
            "interface Cell<Value> {{}}\n\
             type {alias}<Source> = {{ [Key in keyof Source]:\n\
               Source[Key] extends Cell<infer Item> ? Key : never\
             }}[keyof Source];\n\
             type Incoming<P> = P;\n\
             type Later<Q> = Q;\n\
             type Concrete = {{ value: string }};\n",
        )
    }

    fn nested_lookup_fixture<'a>(
        parsed: &'a ParseResult,
        alias_name: &str,
    ) -> (
        CanonicalCheckerContext<'a>,
        SourceMappedLookupProjection,
        TypeId,
        TypeId,
    ) {
        assert!(parsed.diagnostics.is_empty());
        let mut context = checker_context(parsed);
        let (alias, _) = mapped_constraint_alias_parts(parsed, &context, alias_name);
        let (incoming, _) = mapped_constraint_alias_parts(parsed, &context, "Incoming");
        let (later, _) = mapped_constraint_alias_parts(parsed, &context, "Later");
        let lookup = context.get_declared_type_of_symbol(alias).unwrap();
        let incoming = context.get_declared_type_of_symbol(incoming).unwrap();
        let later = context.get_declared_type_of_symbol(later).unwrap();
        let projection = source_mapped_lookup_projection(context.store(), lookup, None)
            .unwrap()
            .unwrap();
        assert_eq!(projection.alias, alias);
        assert_eq!(projection.lookup, projection.declared_lookup);
        assert_eq!(projection.type_, projection.target);
        assert_ne!(projection.type_, projection.lookup);
        assert!(context.diagnostics().is_empty());
        (context, projection, incoming, later)
    }

    const SOURCE_CONDITIONAL_DEMAND: &str = concat!(
        "interface Error { name: string; message: string; stack?: string; }\n",
        "declare module 'prop-types' {\n",
        "export const nominalTypeHack: unique symbol;\n",
        "export type IsOptional<T> = undefined | null extends T ? true : ",
        "undefined extends T ? true : null extends T ? true : false;\n",
        "export type RequiredKeys<V> = { [K in keyof V]: V[K] extends Validator<infer T> ? ",
        "IsOptional<T> extends true ? never : K : never }[keyof V];\n",
        "export interface Validator<T> {\n",
        "(props: object, propName: string, componentName: string, location: string, ",
        "propFullName: string): Error | null;\n",
        "[nominalTypeHack]?: T;\n",
        "}\n",
        "export type Required = RequiredKeys<{ value: Validator<string> }>;\n",
        "}\n",
    );

    fn source_conditional_demand_fixture(
        parsed: &ParseResult,
    ) -> (
        CanonicalCheckerContext<'_>,
        NodeRef,
        TypeId,
        super::SourceConditionalMappedDemand,
    ) {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source("\"/project/source-conditional-demand.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
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
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let (alias, node) = mapped_constraint_alias_parts(parsed, &context, "Required");
        let lookup = context.get_declared_type_of_symbol(alias).unwrap();
        let TypeData::IndexedAccess(indexed) = context.store().type_payload(lookup).unwrap().data()
        else {
            panic!("declared alias query must retain the whole lookup");
        };
        let mapped = indexed.object_type;
        let demand = super::source_conditional_mapped_demand(context.store(), mapped).unwrap();
        assert_eq!(demand.lookup, lookup);
        assert_eq!(
            context.store().type_node_links(node).unwrap().resolved_type,
            Some(lookup)
        );
        assert!(
            !context
                .store()
                .type_payload(mapped)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(context.diagnostics().is_empty());
        (context, node, mapped, demand)
    }

    fn query_source_conditional_demand(
        parsed: &ParseResult,
        context: &mut CanonicalCheckerContext<'_>,
        node: NodeRef,
        session: &mut InstantiationSession,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let bound = context.file(FileId::new(0)).unwrap().1.clone();
        let globals = context.global_types().clone();
        let options = context.options();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        CanonicalTypeQuery::new_with_global_types_and_session(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            session,
            diagnostics,
        )
        .unwrap()
        .get_type_from_type_node(node)
    }

    fn source_conditional_value_symbol(
        store: &CanonicalTypeMapperStore,
        mapped: TypeId,
    ) -> SemanticSymbolId {
        store
            .type_payload(mapped)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .members
            .and_then(|members| store.symbol_table(members))
            .unwrap()
            .get_source("value")
            .unwrap()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Warm the mapped value and its nested callable before direct cache replay.
    fn source_mapped_conditional_demand_rejects_nested_copied_signature_damage() {
        use crate::semantic::{
            array_types::CanonicalArrayTargets,
            callable_sets::StoredCallableSetValidation,
            instantiated_members::{
                resolve_members_with_array_targets, validate_generic_interface_callable,
            },
            object_members::{
                DeclaredPropertyTypeGraphValidation, validate_resolved_declared_property_type_graph,
            },
        };

        for source in [
            SOURCE_CONDITIONAL_DEMAND.to_owned(),
            SOURCE_CONDITIONAL_DEMAND.replace(
                "export type Required = RequiredKeys<{ value: Validator<string> }>;",
                "export interface Inputs { value: Validator<string>; }\nexport type Required = RequiredKeys<Inputs>;",
            ),
        ] {
            for recovering in [false, true] {
            let parsed = parse_source_file(&source);
            let (mut context, node, mapped, demand) = source_conditional_demand_fixture(&parsed);
            let key = super::source_conditional_mapped_key(context.store(), demand).unwrap();
            let result = if recovering {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                let (string, error) = (bootstrap.string_type, bootstrap.error_type);
                let mut session = InstantiationSession::new_recovering(
                    context.store(),
                    InstantiationLimits { max_depth: 100, max_count: 1 },
                    error,
                ).unwrap();
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        context.store_mut_for_test(), demand.origin.source,
                        &[demand.origin.source], &[string], None, &mut session,
                    ),
                    Ok(string),
                );
                let mut diagnostics = CanonicalCheckerDiagnostics::default();
                assert_eq!(
                    query_source_conditional_demand(&parsed, &mut context, node, &mut session, &mut diagnostics),
                    Ok(error),
                );
                assert_eq!(session.limit_event_count(), 1);
                let property = source_conditional_value_symbol(context.store(), mapped);
                assert!(context.store().mapped_property_recovery(property).is_some());
                assert_eq!(super::cached_source_mapped_template(context.store(), mapped, key), Ok(None));
                error
            } else {
                assert_eq!(context.get_type_from_type_node(node), Ok(key));
                key
            };
        let DeclaredPropertyTypeGraphValidation::Traversable(properties) =
            validate_resolved_declared_property_type_graph(context.store(), demand.argument)
        else {
            panic!("the written object must retain its checked property graph")
        };
        let [validator] = properties.as_slice() else {
            panic!("the source object must retain one Validator property")
        };
        let validator = *validator;
        let globals = context.global_types().clone();
        let arrays = Some(CanonicalArrayTargets::from_global_types(&globals));
        resolve_members_with_array_targets(context.store_mut_for_test(), validator, arrays)
            .unwrap();
        let Some(StoredCallableSetValidation::Valid { projection, .. }) =
            validate_generic_interface_callable(context.store(), validator, arrays)
        else {
            panic!("the nested Validator must retain its copied call signature")
        };
        let signature = projection.call_signatures[0].signature;
        let bound = context.file(FileId::new(0)).unwrap().1.clone();
        let options = context.options();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 0,
            max_count: 0,
        });
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            CanonicalTypeQuery::new_with_global_types_and_session(
                context.store_mut_for_test(),
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
            )
            .unwrap()
            .get_type_of_mapped_property(mapped, EscapedName::source("value").as_ref())
            .map(|property| property.map(super::ResolvedMappedProperty::type_id)),
            Ok(Some(result)),
        );

        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        assert!(store.set_signature_resolved_return_type(signature, Some(number)));
        let before = (cache_state(store), store.signature_len());
        for _ in 0..2 {
            assert_eq!(
                    super::cached_source_mapped_template_with_array_targets(
                        store, mapped, key, arrays
                ),
                Err(MappedTypeError::InvalidMappedType(mapped)),
            );
            assert_eq!(
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    &host,
                    &globals,
                    options,
                    &mut session,
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_of_mapped_property(mapped, EscapedName::source("value").as_ref())
                .map(|property| property.map(super::ResolvedMappedProperty::type_id)),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedSyntax {
                        node: demand.origin.declaration,
                        kind: SyntaxKind::MappedType,
                    }
                )),
            );
            assert_eq!((cache_state(store), store.signature_len()), before);
            assert_eq!(
                store.type_node_links(node).unwrap().resolved_type,
                Some(demand.lookup)
            );
            assert!(store.type_resolution_is_empty());
        }
        assert_eq!(
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_count()
            ),
            (0, 0, 0)
        );
            assert!(diagnostics.is_empty());
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The same source query covers fail-fast, recovery, and spent warm replay.
    fn source_mapped_conditional_demand_preserves_spent_limits_and_recovery() {
        for recovering in [false, true] {
            let parsed = parse_source_file(SOURCE_CONDITIONAL_DEMAND);
            let (mut context, node, mapped, demand) = source_conditional_demand_fixture(&parsed);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let (string, error) = (bootstrap.string_type, bootstrap.error_type);
            let key = super::source_conditional_mapped_key(context.store(), demand).unwrap();
            let mut session = if recovering {
                InstantiationSession::new_recovering(
                    context.store(),
                    InstantiationLimits {
                        max_depth: 100,
                        max_count: 1,
                    },
                    error,
                )
                .unwrap()
            } else {
                InstantiationSession::new(InstantiationLimits {
                    max_depth: 100,
                    max_count: 1,
                })
            };
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    context.store_mut_for_test(),
                    demand.origin.source,
                    &[demand.origin.source],
                    &[string],
                    None,
                    &mut session,
                ),
                Ok(string)
            );
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (1, 1, 0)
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = query_source_conditional_demand(
                &parsed,
                &mut context,
                node,
                &mut session,
                &mut diagnostics,
            );
            let symbol = source_conditional_value_symbol(context.store(), mapped);
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (1, 1, 1)
            );
            assert!(context.store().type_resolution_is_empty());
            assert_eq!(
                context.store().type_node_links(node).unwrap().resolved_type,
                Some(demand.lookup)
            );
            assert_eq!(
                super::cached_source_mapped_template(context.store(), mapped, key),
                Ok(None)
            );
            if recovering {
                assert_eq!(result, Ok(error));
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(symbol)
                        .unwrap()
                        .resolved_type,
                    Some(error)
                );
                assert!(context.store().mapped_property_recovery(symbol).is_some());
            } else {
                assert_eq!(
                    result,
                    Err(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::UnsupportedSyntax {
                            node: demand.origin.declaration,
                            kind: SyntaxKind::MappedType,
                        }
                    ))
                );
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(symbol)
                        .unwrap()
                        .resolved_type,
                    None
                );
                assert!(context.store().mapped_property_recovery(symbol).is_none());
                let mut retry = InstantiationSession::new(InstantiationLimits::default());
                assert_eq!(
                    query_source_conditional_demand(
                        &parsed,
                        &mut context,
                        node,
                        &mut retry,
                        &mut diagnostics
                    ),
                    Ok(key)
                );
                assert!(retry.total_count() > 0);
                assert_eq!(retry.limit_event_count(), 0);
            }
            let warm = cache_state(context.store());
            let expected = if recovering { error } else { key };
            assert_eq!(
                query_source_conditional_demand(
                    &parsed,
                    &mut context,
                    node,
                    &mut session,
                    &mut diagnostics
                ),
                Ok(expected)
            );
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (1, 1, 1)
            );
            assert_eq!(cache_state(context.store()), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }

    #[test]
    fn source_mapped_conditional_demand_rejects_warm_mapper_and_value_damage() {
        let parsed = parse_source_file(SOURCE_CONDITIONAL_DEMAND);
        let (mut context, node, mapped, demand) = source_conditional_demand_fixture(&parsed);
        let result = context.get_type_from_type_node(node).unwrap();
        let symbol = source_conditional_value_symbol(context.store(), mapped);
        let links = context.store().value_symbol_links(symbol).unwrap().clone();
        assert_eq!(links.resolved_type, Some(result));
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let wrong = store
            .new_simple_type_mapper(demand.origin.source, number)
            .unwrap();
        for damage in 0..2 {
            if damage == 0 {
                assert!(store.set_object_target_and_mapper(
                    mapped,
                    Some(demand.origin.target),
                    Some(wrong)
                ));
            } else {
                let mut damaged = links.clone();
                damaged.resolved_type = Some(number);
                assert!(store.set_value_symbol_links(symbol, damaged));
            }
            let before = cache_state(store);
            for _ in 0..2 {
                assert_eq!(
                    store.validate_prop_types_required_keys_instantiation(
                        demand.origin.alias,
                        demand.origin.declared_lookup,
                        &[demand.origin.source],
                        &[demand.argument],
                        demand.lookup,
                    ),
                    Err(MappedTypeError::InvalidMappedType(demand.lookup))
                );
                assert_eq!(cache_state(store), before);
                assert!(store.type_resolution_is_empty());
            }
            assert!(store.set_object_target_and_mapper(
                mapped,
                Some(demand.origin.target),
                Some(demand.mapper)
            ));
            assert!(store.set_value_symbol_links(symbol, links.clone()));
            assert_eq!(
                store.validate_prop_types_required_keys_instantiation(
                    demand.origin.alias,
                    demand.origin.declared_lookup,
                    &[demand.origin.source],
                    &[demand.argument],
                    demand.lookup,
                ),
                Ok(())
            );
        }
        let before = cache_state(store);
        let mut session = InstantiationSession::new(InstantiationLimits {
            max_depth: 0,
            max_count: 0,
        });
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_source_conditional_demand(
                &parsed,
                &mut context,
                node,
                &mut session,
                &mut diagnostics
            ),
            Ok(result)
        );
        assert_eq!(
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_count()
            ),
            (0, 0, 0)
        );
        assert_eq!(cache_state(context.store()), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The source error, incomplete member state, and retry stay in one caller session.
    fn source_mapped_conditional_demand_keeps_a_failed_branch_value_unpublished() {
        use crate::semantic::conditional_types::{ConditionalBranchKind, ConditionalBranchSource};

        struct RefusingSource {
            demand: super::SourceConditionalMappedDemand,
            error: DeclaredTypeError,
            calls: usize,
        }

        impl ConditionalBranchSource for RefusingSource {
            fn preflight(
                &self,
                store: &CanonicalTypeMapperStore,
                conditional: TypeId,
            ) -> Result<(), DeclaredTypeError> {
                if conditional != self.demand.origin.template {
                    return Err(self.error);
                }
                let parameters = [self.demand.origin.source, self.demand.origin.key];
                match super::cached_source_conditional_instantiation(
                    store,
                    conditional,
                    &parameters,
                    &parameters,
                ) {
                    Ok(Some(result)) if result == conditional => Ok(()),
                    _ => Err(self.error),
                }
            }

            fn resolve_branch(
                &mut self,
                _store: &mut CanonicalTypeMapperStore,
                _conditional: TypeId,
                _branch: ConditionalBranchKind,
                _session: &mut InstantiationSession,
            ) -> Result<TypeId, DeclaredTypeError> {
                self.calls += 1;
                Err(self.error)
            }
        }

        let parsed = parse_source_file(SOURCE_CONDITIONAL_DEMAND);
        let (mut context, node, mapped, demand) = source_conditional_demand_fixture(&parsed);
        let globals = context.global_types().clone();
        let error =
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::UnsupportedSyntax {
                node: demand.origin.declaration,
                kind: SyntaxKind::MappedType,
            });
        let mut source = RefusingSource {
            demand,
            error,
            calls: 0,
        };
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let result = context
            .store_mut_for_test()
            .resolve_mapped_lookup_with_source(demand.lookup, &globals, &mut session, &mut source);
        assert_eq!(result, Err(MappedTypeError::Declared(error)));
        assert_eq!(source.calls, 1);
        assert!(session.query_count() > 0);
        assert_eq!(session.limit_event_count(), 0);
        let symbol = source_conditional_value_symbol(context.store(), mapped);
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            None
        );
        assert!(context.store().mapped_property_recovery(symbol).is_none());
        assert!(context.store().type_resolution_is_empty());
        let key = super::source_conditional_mapped_key(context.store(), demand).unwrap();
        assert_eq!(
            super::cached_source_mapped_template(context.store(), mapped, key),
            Ok(None)
        );
        assert_eq!(
            context.store().type_node_links(node).unwrap().resolved_type,
            Some(demand.lookup)
        );
        let count = session.total_count();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_source_conditional_demand(
                &parsed,
                &mut context,
                node,
                &mut session,
                &mut diagnostics
            ),
            Ok(key)
        );
        assert!(session.total_count() > count);
        assert_eq!(session.limit_event_count(), 0);
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(key)
        );
        assert!(context.store().type_resolution_is_empty());
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn nested_mapped_lookups_keep_the_parent_cache_and_original_template() {
        for name in ["ChosenKeys", "AcceptedNames"] {
            let parsed = parse_source_file(&nested_lookup_source(name));
            let (mut context, projection, incoming, later) = nested_lookup_fixture(&parsed, name);
            let store = context.store_mut_for_test();
            let (template, conditional) = conditional_template_snapshot(store, projection.type_);
            let parameters = projection.type_parameters.clone();
            let arguments = [incoming];
            let cold = cache_state(store);
            assert_eq!(
                source_mapped_lookup_identity_projection(store, projection.lookup, None),
                Ok(Some(projection.clone()))
            );
            assert_eq!(
                cached_source_mapped_lookup_instance(store, &projection, &arguments, None),
                Ok(None)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    projection.lookup,
                    &parameters,
                    &arguments,
                    None,
                    None
                ),
                Ok(None)
            );
            assert_eq!(cache_state(store), cold);

            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let lookup = instantiate_type_with_vector_and_session(
                store,
                projection.lookup,
                &parameters,
                &arguments,
                None,
                &mut session,
            )
            .unwrap();
            let current = source_mapped_lookup_projection(store, lookup, None)
                .unwrap()
                .unwrap();
            assert_eq!(current.arguments, arguments);
            assert_eq!(current.target, projection.target);
            assert_eq!(current.declared_lookup, projection.lookup);
            assert_ne!(current.type_, projection.type_);
            assert_eq!(
                store
                    .type_alias_links(projection.alias)
                    .unwrap()
                    .instantiations
                    .as_ref()
                    .unwrap()
                    .get(&type_alias_instantiation_cache_key(&arguments, None)),
                Some(&lookup)
            );
            assert_cold_conditional_mapped_type(store, current.type_, template);
            let warm = cache_state(store);
            let counts = (session.query_count(), session.total_count());
            assert_eq!(counts, (4, 4));
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    projection.lookup,
                    &parameters,
                    &arguments,
                    None,
                    &mut session,
                ),
                Ok(lookup)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    store,
                    projection.lookup,
                    &parameters,
                    &arguments,
                    None,
                    None
                ),
                Ok(Some(lookup))
            );
            assert_eq!(cache_state(store), warm);
            assert_eq!((session.query_count(), session.total_count()), (8, 8));

            let next = instantiate_type_with_vector_and_session(
                store,
                lookup,
                &arguments,
                &[later],
                None,
                &mut session,
            )
            .unwrap();
            let next = source_mapped_lookup_projection(store, next, None)
                .unwrap()
                .unwrap();
            assert_eq!(next.arguments, [later]);
            assert_eq!(next.target, projection.target);
            assert_eq!(next.declared_lookup, projection.declared_lookup);
            assert_cold_conditional_mapped_type(store, next.type_, template);
            assert_eq!(
                store.type_payload(template).unwrap().data(),
                &TypeData::Conditional(conditional)
            );
        }
    }

    #[test]
    fn nested_mapped_lookups_reject_damaged_owners_mappers_and_templates() {
        let parsed = parse_source_file(&nested_lookup_source("ChosenKeys"));
        let (mut context, projection, incoming, later) =
            nested_lookup_fixture(&parsed, "ChosenKeys");
        let foreign_parsed = parse_source_file("");
        let foreign_context = checker_context(&foreign_parsed);
        let foreign = foreign_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        let store = context.store_mut_for_test();
        let mapped =
            instantiate_source_mapped_lookup_instance(store, &projection, &[incoming], None)
                .unwrap();
        let current = source_mapped_lookup_projection(store, mapped, None)
            .unwrap()
            .unwrap();
        let TypeData::Mapped(mapped_data) = store.type_payload(mapped).unwrap().data() else {
            unreachable!()
        };
        let mapped_data = mapped_data.clone();
        let (template, conditional) = conditional_template_snapshot(store, mapped);
        let wrong_mapper = store
            .new_simple_type_mapper(projection.type_parameters[0], later)
            .unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let flags = store.type_payload(mapped).unwrap().object_flags();
        let links = store.type_alias_links(projection.alias).unwrap().clone();

        for damage in 0..4 {
            match damage {
                0 => assert!(store.set_object_target_and_mapper(
                    mapped,
                    Some(later),
                    mapped_data.object.mapper
                )),
                1 => assert!(store.set_object_target_and_mapper(
                    mapped,
                    mapped_data.object.target,
                    Some(wrong_mapper)
                )),
                2 => assert!(store.add_type_object_flags(mapped, ObjectFlags::MEMBERS_RESOLVED)),
                3 => assert!(store.set_conditional_resolution(
                    template,
                    None,
                    Some(number),
                    None,
                    None,
                    None,
                    conditional.mapper,
                    conditional.combined_mapper
                )),
                _ => unreachable!(),
            }
            let damaged = cache_state(store);
            for _ in 0..2 {
                assert!(matches!(
                    source_mapped_lookup_projection(store, mapped, None),
                    Err(MappedTypeError::InvalidMappedType(_))
                ));
                assert!(matches!(
                    source_mapped_lookup_identity_projection(store, mapped, None),
                    Err(MappedTypeError::InvalidMappedType(_))
                ));
                assert!(matches!(
                    cached_source_mapped_lookup_instance(store, &projection, &[incoming], None),
                    Err(MappedTypeError::InvalidMappedType(_))
                ));
                assert!(matches!(
                    instantiate_source_mapped_lookup_instance(
                        store,
                        &projection,
                        &[incoming],
                        None
                    ),
                    Err(MappedTypeError::InvalidMappedType(_))
                ));
                assert_eq!(cache_state(store), damaged);
                assert_eq!(store.type_alias_links(projection.alias), Some(&links));
            }
            assert!(store.set_object_target_and_mapper(
                mapped,
                mapped_data.object.target,
                mapped_data.object.mapper
            ));
            assert!(store.set_type_object_flags(mapped, flags));
            assert!(store.set_conditional_resolution(
                template,
                None,
                None,
                None,
                None,
                None,
                conditional.mapper,
                conditional.combined_mapper
            ));
            assert_eq!(
                source_mapped_lookup_projection(store, mapped, None),
                Ok(Some(current.clone()))
            );
            assert_eq!(
                cached_source_mapped_lookup_instance(store, &projection, &[incoming], None),
                Ok(Some(mapped))
            );
        }
        let before = cache_state(store);
        assert!(!store.set_conditional_resolution(
            template,
            None,
            Some(foreign),
            None,
            None,
            None,
            conditional.mapper,
            conditional.combined_mapper
        ));
        assert_eq!(
            source_mapped_lookup_projection(store, foreign, None),
            Err(MappedTypeError::InvalidMappedType(foreign))
        );
        assert_eq!(
            source_mapped_lookup_identity_projection(store, foreign, None),
            Err(MappedTypeError::InvalidMappedType(foreign))
        );
        assert_eq!(
            cached_source_mapped_lookup_instance(store, &projection, &[foreign], None),
            Err(MappedTypeError::InvalidSource(foreign))
        );
        assert_eq!(
            instantiate_source_mapped_lookup_instance(store, &projection, &[foreign], None),
            Err(MappedTypeError::InvalidSource(foreign))
        );
        assert_eq!(cache_state(store), before);
        assert_eq!(store.type_alias_links(projection.alias), Some(&links));
        let mut forged = current.clone();
        forged.arguments = vec![later];
        let before = cache_state(store);
        assert_eq!(
            instantiate_source_mapped_lookup_instance(store, &forged, &[incoming], None),
            Err(MappedTypeError::InvalidMappedType(mapped))
        );
        assert_eq!(cache_state(store), before);
        assert_eq!(
            store.type_payload(template).unwrap().data(),
            &TypeData::Conditional(conditional)
        );
    }

    #[test]
    fn nested_mapped_lookups_keep_valid_warm_branches_as_unsupported() {
        let parsed = parse_source_file(&nested_lookup_source("ChosenKeys"));
        let (mut context, projection, incoming, later) =
            nested_lookup_fixture(&parsed, "ChosenKeys");
        let store = context.store_mut_for_test();
        let mapped =
            instantiate_source_mapped_lookup_instance(store, &projection, &[incoming], None)
                .unwrap();
        let current = source_mapped_lookup_projection(store, mapped, None)
            .unwrap()
            .unwrap();
        let (template, _) = conditional_template_snapshot(store, mapped);
        let never = store.intrinsic_bootstrap().unwrap().never_type;
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        assert_eq!(
            get_false_type_from_conditional_type(
                store,
                template,
                ConditionalTypeBranches {
                    true_type: projection.origin.key,
                    false_type: never
                },
                None,
                Some(&mut session),
            ),
            Ok(never)
        );
        assert_eq!(
            (
                session.query_count(),
                session.total_count(),
                session.limit_event_count()
            ),
            (0, 0, 0)
        );
        let TypeData::Conditional(warm) = store.type_payload(template).unwrap().data() else {
            unreachable!()
        };
        let warm = warm.clone();
        assert_eq!(warm.resolved_false_type, Some(never));
        assert_eq!(warm.resolved_true_type, None);
        let before = (
            cache_state(store),
            store.type_alias_len_internal(),
            store.type_resolution_internal_state(),
        );
        let links = store.type_alias_links(projection.alias).unwrap().clone();
        for attempt in 1..=2 {
            let identity = source_mapped_lookup_identity_projection(store, mapped, None)
                .unwrap()
                .unwrap();
            assert_eq!(identity, current);
            assert_eq!(
                source_mapped_lookup_projection(store, mapped, None),
                Err(MappedTypeError::UnsupportedTemplate(template))
            );
            assert_eq!(
                cached_source_mapped_lookup_instance(store, &projection, &[incoming], None),
                Err(MappedTypeError::UnsupportedTemplate(template))
            );
            assert_eq!(
                instantiate_source_mapped_lookup_instance(store, &projection, &[later], None),
                Err(MappedTypeError::UnsupportedTemplate(template))
            );
            assert_eq!(
                instantiate_source_mapped_lookup_instance(store, &identity, &[later], None),
                Err(MappedTypeError::UnsupportedTemplate(template))
            );
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (attempt - 1, attempt - 1, 0)
            );
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    current.lookup,
                    &[incoming],
                    &[later],
                    None,
                    &mut session
                ),
                Err(InstantiationError::UnsupportedType(mapped))
            );
            assert_eq!(
                (
                    cache_state(store),
                    store.type_alias_len_internal(),
                    store.type_resolution_internal_state()
                ),
                before
            );
            assert_eq!(store.type_alias_links(projection.alias), Some(&links));
            assert_eq!(
                store.type_payload(template).unwrap().data(),
                &TypeData::Conditional(warm.clone())
            );
            assert_eq!(
                (
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count()
                ),
                (attempt, attempt, 0)
            );
        }
    }

    #[test]
    fn nested_mapped_lookups_reject_concrete_and_member_demand_without_publication() {
        let parsed = parse_source_file(&nested_lookup_source("ChosenKeys"));
        let (mut context, projection, incoming, _) = nested_lookup_fixture(&parsed, "ChosenKeys");
        let (concrete, _) = mapped_constraint_alias_parts(&parsed, &context, "Concrete");
        let concrete = context.get_declared_type_of_symbol(concrete).unwrap();
        let store = context.store_mut_for_test();
        let mapped =
            instantiate_source_mapped_lookup_instance(store, &projection, &[incoming], None)
                .unwrap();
        let (template, conditional) = conditional_template_snapshot(store, mapped);
        let key = store.regular_string_literal_type("value".into()).unwrap();
        let indexed = crate::semantic::indexed_access_types::get_instantiated_indexed_access_type(
            store,
            mapped,
            key,
            AccessFlags::NONE,
        )
        .unwrap();
        let before = cache_state(store);
        let links = store.type_alias_links(projection.alias).unwrap().clone();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        for _ in 0..2 {
            assert_eq!(
                instantiate_source_mapped_lookup_instance(store, &projection, &[concrete], None),
                Err(MappedTypeError::UnsupportedTemplate(template))
            );
            for type_ in [projection.type_, mapped] {
                assert_eq!(
                    store.resolve_mapped_type_members_with_session(
                        type_,
                        MappedTypeModifiers::NONE,
                        &mut session
                    ),
                    Err(MappedTypeError::UnsupportedTemplate(template))
                );
                assert_eq!(
                    store.resolve_mapped_type_property(type_, "value", MappedTypeModifiers::NONE),
                    Err(MappedTypeError::UnsupportedTemplate(template))
                );
                assert_eq!(
                    store.validate_mapped_type_relation_endpoint(type_),
                    Err(MappedTypeError::UnsupportedTemplate(template))
                );
            }
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    store,
                    indexed,
                    &[incoming],
                    &[incoming],
                    None,
                    &mut session
                ),
                Err(InstantiationError::UnsupportedType(mapped))
            );
            assert_eq!(cache_state(store), before);
            assert_eq!(store.type_alias_links(projection.alias), Some(&links));
            assert_cold_conditional_mapped_type(store, mapped, template);
        }
        assert_eq!(
            store.type_payload(template).unwrap().data(),
            &TypeData::Conditional(conditional)
        );
    }

    fn conditional_template_snapshot(
        store: &CanonicalTypeMapperStore,
        mapped: TypeId,
    ) -> (TypeId, ConditionalTypeData) {
        let TypeData::Mapped(mapped) = store.type_payload(mapped).unwrap().data() else {
            panic!("the real source query must retain its mapped type");
        };
        let template = mapped.template_type.unwrap();
        let TypeData::Conditional(conditional) = store.type_payload(template).unwrap().data()
        else {
            panic!("the source alias must retain its conditional template");
        };
        assert!(conditional.resolved_true_type.is_none());
        assert!(conditional.resolved_false_type.is_none());
        assert!(conditional.resolved_inferred_true_type.is_none());
        assert!(conditional.resolved_default_constraint.is_none());
        assert!(conditional.resolved_constraint_of_distributive.is_none());
        (template, conditional.clone())
    }

    fn assert_cold_conditional_mapped_type(
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        template: TypeId,
    ) {
        let record = store.type_payload(type_).unwrap();
        let TypeData::Mapped(mapped) = record.data() else {
            panic!("the source query must retain a mapped result");
        };
        assert_eq!(mapped.template_type, Some(template));
        assert!(
            !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(unresolved_mapped_structure_is_valid(
            store,
            type_,
            &mapped.object.structured
        ));
    }

    #[test]
    fn homomorphic_conditional_aliases_keep_source_query_and_warm_identity() {
        for name in ["MappedValues", "DecodedFields"] {
            let parsed = parse_source_file(&homomorphic_conditional_source(name, ""));
            assert!(parsed.diagnostics.is_empty());
            let (mut context, projection, source) = selection_call_fixture(&parsed);
            assert_eq!(
                projection.kind,
                SupportedMappedAliasKind::Homomorphic(MappedTypeModifiers::NONE)
            );
            let bound = context.file(FileId::new(0)).unwrap().1.clone();
            let options = context.options();
            let globals = context.global_types().clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let annotation = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::FunctionDeclaration(function) = &record.data else {
                        return None;
                    };
                    function
                        .type_
                        .map(|node| NodeRef::new(parsed.arena.id(), FileId::new(0), node))
                })
                .unwrap();
            let store = context.store_mut_for_test();
            let (template, conditional) = conditional_template_snapshot(store, projection.type_);
            assert_cold_conditional_mapped_type(store, projection.declared_type, template);
            assert_cold_conditional_mapped_type(store, projection.type_, template);
            let before = (cache_state(store), store.type_alias_len_internal());
            let mut zero = InstantiationSession::new(InstantiationLimits {
                max_depth: 0,
                max_count: 0,
            });
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            for _ in 0..2 {
                assert_eq!(
                    CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        &host,
                        &globals,
                        options,
                        &mut zero,
                        &mut diagnostics,
                    )
                    .unwrap()
                    .get_type_from_type_node(annotation),
                    Ok(projection.type_),
                );
                assert_eq!(
                    (cache_state(store), store.type_alias_len_internal()),
                    before
                );
            }
            assert_eq!(
                (
                    zero.query_count(),
                    zero.total_count(),
                    zero.limit_event_count()
                ),
                (0, 0, 0)
            );
            assert!(diagnostics.is_empty());
            let arguments = [source];
            let identity = (projection.alias, arguments.as_slice());
            assert_eq!(
                cached_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Ok(None)
            );
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            let result = instantiate_type_with_vector_and_session(
                store,
                projection.type_,
                &projection.arguments,
                &arguments,
                None,
                &mut session,
            )
            .unwrap();
            assert_eq!((session.query_count(), session.total_count()), (2, 2));
            let actual = supported_mapped_alias_projection(store, result, None)
                .unwrap()
                .unwrap();
            assert_eq!(actual.declared_type, projection.declared_type);
            assert_eq!(actual.alias, projection.alias);
            assert_eq!(actual.arguments, arguments);
            assert_eq!(actual.identity_symbol, projection.alias);
            assert_eq!(actual.identity_arguments, arguments);
            assert_cold_conditional_mapped_type(store, result, template);
            let warm = (cache_state(store), store.type_alias_len_internal());
            for _ in 0..2 {
                assert_eq!(
                    cached_supported_mapped_alias_instance(
                        store,
                        &projection,
                        &arguments,
                        identity,
                        None
                    ),
                    Ok(Some(result))
                );
                assert_eq!(
                    instantiate_supported_mapped_alias_instance(
                        store,
                        &projection,
                        &arguments,
                        identity,
                        None
                    ),
                    Ok(result)
                );
                assert_eq!((cache_state(store), store.type_alias_len_internal()), warm);
                assert_eq!(
                    store.type_payload(template).unwrap().data(),
                    &TypeData::Conditional(conditional.clone())
                );
            }
        }
    }

    #[test]
    fn homomorphic_conditional_aliases_keep_nested_selection_keys_cold() {
        let parsed = parse_source_file(concat!(
            "interface Cell<T> { value: T; }\n",
            "type Unwrap<V> = V extends Cell<infer R> ? R : never;\n",
            "type MappedValues<V> = { [K in keyof V]: Unwrap<V[K]> };\n",
            "type Selection<S, K extends keyof S> = { [P in K]: S[P] };\n",
            "declare function convert<T, K extends keyof T>(value: T): MappedValues<Selection<T, K>>;\n",
            "const input = { a: 'a', b: 1 };\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let inner = supported_mapped_alias_projection(store, projection.arguments[0], None)
            .unwrap()
            .unwrap();
        assert_eq!(inner.kind, SupportedMappedAliasKind::Selection);
        let (template, conditional) = conditional_template_snapshot(store, projection.type_);
        let b = store.regular_string_literal_type("b".into()).unwrap();
        let arguments = [source, b];
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let result = instantiate_type_with_vector_and_session(
            store,
            projection.type_,
            &inner.arguments,
            &arguments,
            None,
            &mut session,
        )
        .unwrap();
        let actual = supported_mapped_alias_projection(store, result, None)
            .unwrap()
            .unwrap();
        let selected = actual.arguments[0];
        let selected_projection = supported_mapped_alias_projection(store, selected, None)
            .unwrap()
            .unwrap();
        assert_eq!(selected_projection.arguments, arguments);
        let TypeData::Mapped(selected_type) = store.type_payload(selected).unwrap().data() else {
            unreachable!()
        };
        let TypeData::Mapped(mapped) = store.type_payload(result).unwrap().data() else {
            unreachable!()
        };
        assert_eq!(selected_type.constraint_type, Some(b));
        assert_eq!(mapped.constraint_type, Some(b));
        assert!(unresolved_mapped_structure_is_valid(
            store,
            selected,
            &selected_type.object.structured
        ));
        assert_cold_conditional_mapped_type(store, result, template);
        let warm = (cache_state(store), store.type_alias_len_internal());
        assert_eq!(
            super::cached_instantiation_with_vector(
                store,
                projection.type_,
                &inner.arguments,
                &arguments,
                None,
                None
            ),
            Ok(Some(result)),
        );
        assert_eq!((cache_state(store), store.type_alias_len_internal()), warm);
        assert_eq!(
            store.type_payload(template).unwrap().data(),
            &TypeData::Conditional(conditional)
        );
    }

    #[test]
    fn homomorphic_conditional_aliases_use_the_callers_limits_and_recovery() {
        let parsed = parse_source_file(&homomorphic_conditional_source("MappedValues", ""));
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let arguments = [source];
        let links = store.type_alias_links(projection.alias).unwrap().clone();
        let mut spent = InstantiationSession::new(InstantiationLimits {
            max_depth: 100,
            max_count: 1,
        });
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                projection.arguments[0],
                &projection.arguments,
                &arguments,
                None,
                &mut spent,
            ),
            Ok(source)
        );
        assert_eq!(spent.query_count(), 1);
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                projection.type_,
                &projection.arguments,
                &arguments,
                None,
                &mut spent,
            ),
            Err(InstantiationError::CountLimit { count: 1, limit: 1 })
        );
        assert_eq!(
            (
                spent.query_count(),
                spent.total_count(),
                spent.limit_event_count()
            ),
            (1, 1, 1)
        );
        assert_eq!(store.type_alias_links(projection.alias), Some(&links));
        let error = store.intrinsic_bootstrap().unwrap().error_type;
        let mut recovery = InstantiationSession::new_recovering(
            store,
            InstantiationLimits {
                max_depth: 100,
                max_count: 1,
            },
            error,
        )
        .unwrap();
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                projection.type_,
                &projection.arguments,
                &arguments,
                None,
                &mut recovery,
            ),
            Ok(error)
        );
        assert_eq!(
            (
                recovery.query_count(),
                recovery.total_count(),
                recovery.limit_event_count()
            ),
            (1, 1, 1)
        );
        assert_eq!(store.type_alias_links(projection.alias), Some(&links));
        assert_eq!(
            cached_supported_mapped_alias_instance(
                store,
                &projection,
                &arguments,
                (projection.alias, &arguments),
                None,
            ),
            Ok(None)
        );
        let mut fresh = InstantiationSession::new(InstantiationLimits {
            max_depth: 100,
            max_count: 2,
        });
        let result = instantiate_type_with_vector_and_session(
            store,
            projection.type_,
            &projection.arguments,
            &arguments,
            None,
            &mut fresh,
        )
        .unwrap();
        assert_ne!(result, error);
        assert_eq!(
            (
                fresh.query_count(),
                fresh.total_count(),
                fresh.limit_event_count()
            ),
            (2, 2, 0)
        );
        let warm = (cache_state(store), store.type_alias_len_internal());
        assert_eq!(
            cached_supported_mapped_alias_instance(
                store,
                &projection,
                &arguments,
                (projection.alias, &arguments),
                None,
            ),
            Ok(Some(result))
        );
        assert_eq!(
            instantiate_type_with_vector_and_session(
                store,
                projection.type_,
                &projection.arguments,
                &arguments,
                None,
                &mut fresh,
            ),
            Err(InstantiationError::CountLimit { count: 2, limit: 2 })
        );
        assert_eq!((cache_state(store), store.type_alias_len_internal()), warm);
    }

    #[test]
    fn homomorphic_conditional_aliases_reject_and_restore_template_and_alias_caches() {
        let parsed = parse_source_file(&homomorphic_conditional_source("MappedValues", ""));
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let (template, conditional) = conditional_template_snapshot(store, projection.type_);
        let arguments = [source];
        let identity = (projection.alias, arguments.as_slice());
        let result = instantiate_supported_mapped_alias_instance(
            store,
            &projection,
            &arguments,
            identity,
            None,
        )
        .unwrap();
        let TypeData::Mapped(original) =
            store.type_payload(projection.declared_type).unwrap().data()
        else {
            unreachable!()
        };
        let template_node = store
            .source_mapped_type_operands(original.declaration.unwrap())
            .unwrap()
            .template
            .unwrap();
        let original_node = store.type_node_links(template_node).unwrap().clone();
        let original_alias = store.type_payload(template).unwrap().alias();
        let result_alias = store.type_payload(result).unwrap().alias();
        let TypeData::Mapped(mapped) = store.type_payload(result).unwrap().data() else {
            unreachable!()
        };
        let result_mapper = mapped.object.mapper;
        for damage in 0..3 {
            match damage {
                0 => {
                    let mut poisoned = original_node.clone();
                    poisoned.resolved_type = Some(source);
                    assert!(store.set_type_node_links(template_node, poisoned));
                }
                1 => assert!(store.set_type_alias(template, result_alias)),
                2 => assert!(store.set_conditional_resolution(
                    template,
                    None,
                    None,
                    None,
                    None,
                    None,
                    result_mapper,
                    None
                )),
                _ => unreachable!(),
            }
            let before = (cache_state(store), store.type_alias_len_internal());
            for _ in 0..2 {
                assert_eq!(
                    supported_mapped_alias_projection(store, projection.type_, None),
                    Err(MappedTypeError::InvalidMappedType(template))
                );
                assert_eq!(
                    cached_supported_mapped_alias_instance(
                        store,
                        &projection,
                        &arguments,
                        identity,
                        None
                    ),
                    Err(MappedTypeError::InvalidMappedType(template))
                );
                assert_eq!(
                    instantiate_supported_mapped_alias_instance(
                        store,
                        &projection,
                        &arguments,
                        identity,
                        None
                    ),
                    Err(MappedTypeError::InvalidMappedType(template))
                );
                assert_eq!(
                    (cache_state(store), store.type_alias_len_internal()),
                    before
                );
            }
            assert!(store.set_type_node_links(template_node, original_node.clone()));
            assert!(store.set_type_alias(template, original_alias));
            assert!(store.set_conditional_resolution(
                template,
                None,
                None,
                None,
                None,
                None,
                conditional.mapper,
                conditional.combined_mapper
            ));
            assert_eq!(
                cached_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Ok(Some(result))
            );
        }
        let original_links = store.type_alias_links(projection.alias).unwrap().clone();
        let mut poisoned = original_links.clone();
        let key = type_alias_instantiation_cache_key(&arguments, None);
        assert_eq!(
            poisoned
                .instantiations
                .as_mut()
                .unwrap()
                .insert(key, projection.type_),
            Some(result)
        );
        assert!(store.set_type_alias_links(projection.alias, poisoned));
        let before = (cache_state(store), store.type_alias_len_internal());
        assert_eq!(
            cached_supported_mapped_alias_instance(store, &projection, &arguments, identity, None),
            Err(MappedTypeError::InvalidMappedType(projection.type_))
        );
        assert_eq!(
            (cache_state(store), store.type_alias_len_internal()),
            before
        );
        assert!(store.set_type_alias_links(projection.alias, original_links));
        assert_eq!(
            instantiate_supported_mapped_alias_instance(
                store,
                &projection,
                &arguments,
                identity,
                None
            ),
            Ok(result)
        );
        assert_eq!(
            store.type_payload(template).unwrap().data(),
            &TypeData::Conditional(conditional)
        );
    }

    #[test]
    fn homomorphic_conditional_aliases_reject_index_cache_and_forged_projection_state() {
        let parsed = parse_source_file(&homomorphic_conditional_source("MappedValues", ""));
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let (template, conditional) = conditional_template_snapshot(store, projection.type_);
        let arguments = [source];
        let identity = (projection.alias, arguments.as_slice());
        let result = instantiate_supported_mapped_alias_instance(
            store,
            &projection,
            &arguments,
            identity,
            None,
        )
        .unwrap();
        let TypeData::Mapped(original) =
            store.type_payload(projection.declared_type).unwrap().data()
        else {
            unreachable!()
        };
        let key = original.type_parameter.unwrap();
        let node = store
            .source_mapped_type_operands(original.declaration.unwrap())
            .unwrap()
            .template
            .unwrap();
        let reference_children = store.source_direct_children(node).unwrap();
        let indexed = reference_children[1];
        let indexed_children = store.source_direct_children(indexed).unwrap();
        let object_node = indexed_children[0];
        let original_links = store.type_node_links(object_node).unwrap().clone();
        let mut poisoned = original_links.clone();
        poisoned.resolved_type = Some(key);
        assert!(store.set_type_node_links(object_node, poisoned));
        let before = (cache_state(store), store.type_alias_len_internal());
        assert_eq!(
            supported_mapped_alias_projection(store, projection.type_, None),
            Err(MappedTypeError::InvalidMappedType(template))
        );
        assert_eq!(
            cached_supported_mapped_alias_instance(store, &projection, &arguments, identity, None),
            Err(MappedTypeError::InvalidMappedType(template))
        );
        assert_eq!(
            (cache_state(store), store.type_alias_len_internal()),
            before
        );
        assert!(store.set_type_node_links(object_node, original_links));
        let mut wrong_kind = projection.clone();
        wrong_kind.kind = SupportedMappedAliasKind::Selection;
        let mut wrong_arguments = projection.clone();
        wrong_arguments.arguments = arguments.to_vec();
        for forged in [wrong_kind, wrong_arguments] {
            for _ in 0..2 {
                assert_eq!(
                    cached_supported_mapped_alias_instance(
                        store, &forged, &arguments, identity, None
                    ),
                    Err(MappedTypeError::InvalidMappedType(projection.type_))
                );
                assert_eq!(
                    instantiate_supported_mapped_alias_instance(
                        store, &forged, &arguments, identity, None
                    ),
                    Err(MappedTypeError::InvalidMappedType(projection.type_))
                );
                assert_eq!(
                    (cache_state(store), store.type_alias_len_internal()),
                    before
                );
            }
        }
        let flags = store.type_payload(result).unwrap().object_flags();
        assert!(store.add_type_object_flags(result, ObjectFlags::MEMBERS_RESOLVED));
        assert_eq!(
            cached_supported_mapped_alias_instance(store, &projection, &arguments, identity, None),
            Err(MappedTypeError::InvalidMappedType(result))
        );
        assert_eq!(
            (cache_state(store), store.type_alias_len_internal()),
            before
        );
        assert!(store.set_type_object_flags(result, flags));
        assert_eq!(
            cached_supported_mapped_alias_instance(store, &projection, &arguments, identity, None),
            Ok(Some(result))
        );
        assert_cold_conditional_mapped_type(store, result, template);
        assert_eq!(
            store.type_payload(template).unwrap().data(),
            &TypeData::Conditional(conditional)
        );
    }

    #[test]
    fn homomorphic_conditional_aliases_reject_member_and_index_demand_before_publication() {
        for optional in ["", "?", "-?"] {
            let source = format!(
                "{}type IndexedInput = {{ [key: string]: number }};\n",
                homomorphic_conditional_source("MappedValues", optional)
            );
            let parsed = parse_source_file(&source);
            let (mut context, projection, source) = selection_call_fixture(&parsed);
            let dictionary = alias_type(&parsed, &context, "IndexedInput");
            let store = context.store_mut_for_test();
            let (template, conditional) = conditional_template_snapshot(store, projection.type_);
            for argument in [source, dictionary] {
                let arguments = [argument];
                let result = instantiate_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    (projection.alias, &arguments),
                    None,
                )
                .unwrap();
                let shape = super::validate_mapped_shape(store, result).unwrap();
                let (_, indexes) = super::plan_mapped_members(
                    store,
                    &shape,
                    store.declared_mapped_modifiers(result).unwrap(),
                )
                .unwrap();
                assert_eq!(indexes.is_empty(), argument == source);
                let key = store.regular_string_literal_type("a".into()).unwrap();
                let mut session = InstantiationSession::new(InstantiationLimits::default());
                let before = (
                    cache_state(store),
                    store.type_alias_len_internal(),
                    store.type_resolution_internal_state(),
                );
                for _ in 0..2 {
                    assert_eq!(
                        store.resolve_mapped_type_members_with_session(
                            result,
                            MappedTypeModifiers::NONE,
                            &mut session
                        ),
                        Err(MappedTypeError::UnsupportedTemplate(template))
                    );
                    assert_eq!(
                        store.resolve_mapped_type_property(result, "a", MappedTypeModifiers::NONE),
                        Err(MappedTypeError::UnsupportedTemplate(template))
                    );
                    assert_eq!(
                        super::instantiate_mapped_template(store, &shape, key, &mut session),
                        Err(MappedTypeError::UnsupportedTemplate(template))
                    );
                    for index in &indexes {
                        assert_eq!(
                            super::cached_mapped_index_value_type(store, &shape, index),
                            Err(MappedTypeError::UnsupportedTemplate(template))
                        );
                    }
                    assert_eq!(
                        (
                            cache_state(store),
                            store.type_alias_len_internal(),
                            store.type_resolution_internal_state()
                        ),
                        before
                    );
                    assert_eq!(
                        (
                            session.query_count(),
                            session.total_count(),
                            session.limit_event_count()
                        ),
                        (0, 0, 0)
                    );
                    assert_cold_conditional_mapped_type(store, result, template);
                }
            }
            assert_eq!(
                store.type_payload(template).unwrap().data(),
                &TypeData::Conditional(conditional)
            );
        }
    }

    #[test]
    fn selection_alias_instances_share_query_caches_and_source_properties() {
        let parsed = parse_source_file(concat!(
            "type SelectedFields<S, K extends keyof S> = { [P in K]: S[P] };\n",
            "declare function select<O, K extends keyof O>(value: O): SelectedFields<O, K>;\n",
            "const value = { a: 'a', b: 1 };\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let key = store.regular_string_literal_type("b".to_owned()).unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let regular = store.get_regular_type_of_object_literal(source).unwrap();
        assert_ne!(source, regular);
        for source in [source, regular] {
            let arguments = [source, key];
            let identity = (projection.alias, arguments.as_slice());
            assert_eq!(
                cached_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Ok(None),
            );
            let result = instantiate_supported_mapped_alias_instance(
                store,
                &projection,
                &arguments,
                identity,
                None,
            )
            .unwrap();
            let cache_key = type_alias_instantiation_cache_key(&arguments, None);
            assert_eq!(
                store
                    .type_alias_links(projection.alias)
                    .unwrap()
                    .instantiations
                    .as_ref()
                    .unwrap()
                    .get(&cache_key),
                Some(&result),
            );
            let source_members = store
                .type_payload(source)
                .unwrap()
                .data()
                .structured()
                .unwrap();
            let source_property = store
                .symbol_table(source_members.members.unwrap())
                .unwrap()
                .get_source("b")
                .unwrap();
            let property = store
                .resolve_mapped_type_property(result, "b", MappedTypeModifiers::NONE)
                .unwrap()
                .unwrap();
            assert_eq!(property.type_id(), number);
            assert_eq!(
                store
                    .mapped_symbol_links(property.symbol())
                    .unwrap()
                    .synthetic_origin,
                Some(source_property),
            );
            assert_eq!(
                store.resolve_mapped_type_property(result, "a", MappedTypeModifiers::NONE),
                Ok(None),
            );
            let warm = (cache_state(store), store.type_alias_len_internal());
            for _ in 0..2 {
                assert_eq!(
                    cached_supported_mapped_alias_instance(
                        store,
                        &projection,
                        &arguments,
                        identity,
                        None
                    ),
                    Ok(Some(result)),
                );
                assert_eq!(
                    instantiate_supported_mapped_alias_instance(
                        store,
                        &projection,
                        &arguments,
                        identity,
                        None
                    ),
                    Ok(result),
                );
                assert_eq!(
                    supported_mapped_alias_projection(store, projection.type_, None),
                    Ok(Some(projection.clone())),
                );
                assert_eq!((cache_state(store), store.type_alias_len_internal()), warm);
            }
        }
    }

    #[test]
    fn selection_alias_instances_reject_changed_source_and_result_caches() {
        let parsed = parse_source_file(concat!(
            "type SelectedFields<S, K extends keyof S> = { [P in K]: S[P] };\n",
            "declare function select<O, K extends keyof O>(value: O): SelectedFields<O, K>;\n",
            "const value = { a: 'a', b: 1 };\n",
        ));
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let a = store.regular_string_literal_type("a".to_owned()).unwrap();
        let b = store.regular_string_literal_type("b".to_owned()).unwrap();
        let arguments = [source, b];
        let identity = (projection.alias, arguments.as_slice());
        let result = instantiate_supported_mapped_alias_instance(
            store,
            &projection,
            &arguments,
            identity,
            None,
        )
        .unwrap();
        let other_arguments = [source, a];
        let other = instantiate_supported_mapped_alias_instance(
            store,
            &projection,
            &other_arguments,
            (projection.alias, &other_arguments),
            None,
        )
        .unwrap();
        let key = type_alias_instantiation_cache_key(&arguments, None);
        let original_links = store.type_alias_links(projection.alias).unwrap().clone();
        let mut poisoned = original_links.clone();
        assert_eq!(
            poisoned.instantiations.as_mut().unwrap().insert(key, other),
            Some(result)
        );
        assert!(store.set_type_alias_links(projection.alias, poisoned));
        let before = (cache_state(store), store.type_alias_len_internal());
        for _ in 0..2 {
            assert_eq!(
                cached_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Err(MappedTypeError::InvalidMappedType(other)),
            );
            assert_eq!(
                instantiate_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Err(MappedTypeError::InvalidMappedType(other)),
            );
            assert_eq!(
                (cache_state(store), store.type_alias_len_internal()),
                before
            );
        }
        assert!(store.set_type_alias_links(projection.alias, original_links));

        let key_parameter = projection.type_parameters[1];
        let key_owner = super::cached_ordinary_type_parameter_owner(store, key_parameter).unwrap();
        let key_declaration = store.symbol(key_owner).unwrap().declarations().unwrap()[0];
        let constraint = store
            .source_direct_type_annotation(key_declaration)
            .unwrap();
        let constraint_links = store.type_node_links(constraint).unwrap().clone();
        let TypeData::TypeParameter(call_key) =
            store.type_payload(projection.arguments[1]).unwrap().data()
        else {
            panic!("the source call must retain its own key parameter")
        };
        let wrong_index = call_key.constraint.unwrap();
        let mut poisoned = constraint_links.clone();
        poisoned.resolved_type = Some(wrong_index);
        assert!(store.set_type_node_links(constraint, poisoned));
        let before = (cache_state(store), store.type_alias_len_internal());
        for _ in 0..2 {
            assert_eq!(
                supported_mapped_alias_projection(store, projection.type_, None),
                Err(MappedTypeError::InvalidMappedType(projection.type_)),
            );
            assert_eq!(
                cached_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Err(MappedTypeError::InvalidMappedType(projection.type_)),
            );
            assert_eq!(
                (cache_state(store), store.type_alias_len_internal()),
                before
            );
        }
        assert!(store.set_type_node_links(constraint, constraint_links));
        assert_eq!(
            instantiate_supported_mapped_alias_instance(
                store,
                &projection,
                &arguments,
                identity,
                None
            ),
            Ok(result),
        );
    }

    #[test]
    fn selection_alias_source_roles_exclude_other_indexed_templates() {
        for (template, selected) in [("S[P]", true), ("S[K]", false), ("K[P]", false)] {
            let parsed = parse_source_file(&format!(
                "type SelectedFields<S, K extends keyof S> = {{ [P in K]: {template} }};",
            ));
            let context = checker_context(&parsed);
            let (declaration, mapped) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), FileId::new(0), node),
                        NodeRef::new(parsed.arena.id(), FileId::new(0), alias.type_),
                    ))
                })
                .unwrap();
            let store = context.store();
            let parameters = store
                .source_direct_children(declaration)
                .unwrap()
                .into_iter()
                .filter(|node| store.source_node_kind(*node) == Some(SyntaxKind::TypeParameter))
                .collect::<Vec<_>>();
            let operands = store.source_mapped_type_operands(mapped).unwrap();
            let before = cache_state(store);
            assert_eq!(
                selection_alias_source_constraint(store, &parameters, operands).is_some(),
                selected,
            );
            assert_eq!(cache_state(store), before);
        }
    }

    #[test]
    fn selection_alias_nested_sources_recheck_the_original_literal_clone() {
        let parsed = parse_source_file(concat!(
            "type SelectedFields<S, K extends keyof S> = { [P in K]: S[P] };\n",
            "declare function select<O, K extends keyof O>(value: O): SelectedFields<O, K>;\n",
            "const value = { a: 'a', b: 1 };\n",
        ));
        let (mut context, projection, source) = selection_call_fixture(&parsed);
        let store = context.store_mut_for_test();
        let b = store.regular_string_literal_type("b".to_owned()).unwrap();
        let inner_arguments = [source, b];
        let inner = instantiate_supported_mapped_alias_instance(
            store,
            &projection,
            &inner_arguments,
            (projection.alias, &inner_arguments),
            None,
        )
        .unwrap();
        let arguments = [inner, b];
        let identity = (projection.alias, arguments.as_slice());
        let outer = instantiate_supported_mapped_alias_instance(
            store,
            &projection,
            &arguments,
            identity,
            None,
        )
        .unwrap();
        let members = store
            .type_payload(source)
            .unwrap()
            .data()
            .structured()
            .unwrap();
        let table = store.symbol_table(members.members.unwrap()).unwrap();
        let a_property = table.get_source("a").unwrap();
        let b_property = table.get_source("b").unwrap();
        let original = store.value_symbol_links(b_property).unwrap().clone();
        let mut poisoned = original.clone();
        poisoned.target = store.value_symbol_links(a_property).unwrap().target;
        assert!(store.set_value_symbol_links(b_property, poisoned.clone()));
        let before = (cache_state(store), store.type_alias_len_internal());
        for _ in 0..2 {
            assert_eq!(
                cached_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Err(MappedTypeError::InvalidSource(source)),
            );
            assert_eq!(
                instantiate_supported_mapped_alias_instance(
                    store,
                    &projection,
                    &arguments,
                    identity,
                    None
                ),
                Err(MappedTypeError::InvalidSource(source)),
            );
            assert_eq!(store.value_symbol_links(b_property), Some(&poisoned));
            assert_eq!(
                (cache_state(store), store.type_alias_len_internal()),
                before
            );
        }
        assert!(store.set_value_symbol_links(b_property, original));
        let restored = (cache_state(store), store.type_alias_len_internal());
        assert_eq!(
            instantiate_supported_mapped_alias_instance(
                store,
                &projection,
                &arguments,
                identity,
                None
            ),
            Ok(outer),
        );
        assert_eq!(
            (cache_state(store), store.type_alias_len_internal()),
            restored
        );
    }

    fn mapped_constraint_context<'arena>(
        parsed: &'arena ParseResult,
        callable: &'arena ParseResult,
        default_library: bool,
    ) -> CanonicalCheckerContext<'arena> {
        assert!(callable.diagnostics.is_empty());
        let file = FileId::new(0);
        let callable_file = FileId::new(1);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(if default_library {
                        "\"/project/mapped-constraint-unit.d.ts\""
                    } else {
                        "\"/project/mapped-unit.ts\""
                    }),
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
        binder
            .bind_source_file_with_facts(
                &callable.arena,
                callable.source_file,
                callable_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/mapped-constraint-callable.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&callable.arena, callable_file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena), (callable_file, &callable.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn mapped_constraint_alias_parts(
        parsed: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        name: &str,
    ) -> (SemanticSymbolId, NodeRef) {
        let file = FileId::new(0);
        let (declaration, body) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (identifier.text == name).then_some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, alias.type_),
                ))
            })
            .unwrap();
        (
            context.file(file).unwrap().1.symbol(declaration).unwrap(),
            body,
        )
    }

    fn assert_mapped_constraint_probe_is_unsupported(
        parsed: &ParseResult,
        context: &mut CanonicalCheckerContext<'_>,
    ) {
        let (alias, _) = mapped_constraint_alias_parts(parsed, context, "Probe");
        let declaration = context
            .store()
            .symbol(alias)
            .unwrap()
            .declarations()
            .unwrap()[0];
        let NodeData::TypeAliasDeclaration(probe) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let parameter = NodeRef::new(
            declaration.arena,
            declaration.file,
            probe.type_parameters.as_ref().unwrap().nodes[0],
        );
        let before = cache_state(context.store());
        let links = context.store().type_alias_links(alias).cloned();
        assert!(matches!(
            context.get_declared_type_of_symbol(alias),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::GenericAliasConstraintUnsupported {
                    alias: rejected_alias,
                    parameter: rejected_parameter,
                }
            )) if rejected_alias == alias && rejected_parameter == parameter
        ));
        assert_eq!(context.store().type_alias_links(alias), links.as_ref());
        assert_eq!(cache_state(context.store()), before);
        assert!(context.store().type_resolution_is_empty());
    }

    fn mapped_constraint_function_parameter(
        parsed: &ParseResult,
        callable: &ParseResult,
        context: &mut CanonicalCheckerContext<'_>,
    ) -> TypeId {
        let file = FileId::new(0);
        let callable_file = FileId::new(1);
        let bound = context.file(file).unwrap().1.clone();
        let callable_bound = context.file(callable_file).unwrap().1.clone();
        let declaration = callable
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some(NodeRef::new(
                    callable.arena.id(),
                    callable_file,
                    node,
                ))
            })
            .unwrap();
        let owner = callable_bound.symbol(declaration).unwrap();
        let options = context.options();
        let globals = context.global_types().clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&parsed.arena, &bound), (&callable.arena, &callable_bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
        )
        .unwrap()
        .get_type_of_source_callable(declaration, owner)
        .unwrap();
        assert!(diagnostics.is_empty());
        let signature = context
            .store()
            .source_callable_provenance(type_)
            .unwrap()
            .signature;
        let [parameter] = context
            .store()
            .signature(signature)
            .unwrap()
            .type_parameters()
        else {
            panic!("the source function must keep its declared type parameter");
        };
        *parameter
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
    #[allow(clippy::too_many_lines)] // Test the one allowed cache field and each forbidden member field.
    fn mapped_base_constraints_cold_structure_accepts_only_exact_cache_states() {
        let parsed = parse_source_file(concat!(
            "type Mapped = { [Key in 'value']: string }; ",
            "type Probe<Value extends Mapped> = Value;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let callable =
            parse_source_file("declare function bound<Value extends Mapped>(value: Value): Value;");
        let mut context = mapped_constraint_context(&parsed, &callable, false);
        let (mapped_alias, _) = mapped_constraint_alias_parts(&parsed, &context, "Mapped");
        let mapped = context.get_declared_type_of_symbol(mapped_alias).unwrap();
        let TypeData::Mapped(data) = context.store().type_payload(mapped).unwrap().data() else {
            panic!("the source alias must retain its mapped type")
        };
        assert_eq!(data.object.structured, StructuredTypeData::default());
        assert!(unresolved_mapped_structure_is_valid(
            context.store(),
            mapped,
            &data.object.structured,
        ));

        assert_mapped_constraint_probe_is_unsupported(&parsed, &mut context);
        let parameter = mapped_constraint_function_parameter(&parsed, &callable, &mut context);
        assert_eq!(
            get_base_constraint_of_type(context.store_mut_for_test(), parameter),
            Ok(Some(mapped)),
        );
        let TypeData::Mapped(data) = context.store().type_payload(mapped).unwrap().data() else {
            unreachable!()
        };
        let cold = data.object.structured.clone();
        assert_eq!(cold.constrained.resolved_base_constraint, Some(mapped));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let foreign = checker_context(&parsed);
        let foreign_bootstrap = foreign.store().intrinsic_bootstrap().unwrap();
        let before = cache_state(context.store());

        for base in [
            None,
            Some(mapped),
            Some(bootstrap.no_constraint_type),
            Some(bootstrap.circular_constraint_type),
        ] {
            let mut structured = cold.clone();
            structured.constrained.resolved_base_constraint = base;
            assert!(unresolved_mapped_structure_is_valid(
                context.store(),
                mapped,
                &structured,
            ));
        }
        for base in [
            bootstrap.string_type,
            bootstrap.empty_object_type,
            foreign_bootstrap.no_constraint_type,
            foreign_bootstrap.circular_constraint_type,
        ] {
            let mut structured = cold.clone();
            structured.constrained.resolved_base_constraint = Some(base);
            assert!(!unresolved_mapped_structure_is_valid(
                context.store(),
                mapped,
                &structured,
            ));
        }
        for structured in [
            StructuredTypeData {
                members: Some(bootstrap.globals),
                ..cold.clone()
            },
            StructuredTypeData {
                properties: Some(Vec::new()),
                ..cold.clone()
            },
            StructuredTypeData {
                signatures: Some(Vec::new()),
                ..cold.clone()
            },
            StructuredTypeData {
                call_signature_count: 1,
                ..cold.clone()
            },
            StructuredTypeData {
                index_infos: Some(Vec::new()),
                ..cold.clone()
            },
            StructuredTypeData {
                object_type_without_abstract_construct_signatures: Some(mapped),
                ..cold
            },
        ] {
            assert!(!unresolved_mapped_structure_is_valid(
                context.store(),
                mapped,
                &structured,
            ));
        }
        assert_eq!(cache_state(context.store()), before);
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Replay each utility after a real constraint query and cache damage.
    fn mapped_base_constraints_utility_alias_queries_keep_real_self_caches() {
        for (utility, declaration, arguments, modifiers) in [
            (
                "Record",
                "type Record<K extends keyof any, T> = { [P in K]: T };",
                "'value', string",
                MappedTypeModifiers::NONE,
            ),
            (
                "Partial",
                "type Partial<T> = { [P in keyof T]?: T[P] };",
                "Source",
                MappedTypeModifiers::INCLUDE_OPTIONAL,
            ),
            (
                "Pick",
                "type Pick<T, K extends keyof T> = { [P in K]: T[P] };",
                "Source, 'value'",
                MappedTypeModifiers::NONE,
            ),
        ] {
            let parsed = parse_source_file(&format!(
                concat!(
                    "interface Source {{ value: string }} {declaration} ",
                    "type Result = {utility}<{arguments}>; ",
                    "type Probe<Value extends Result> = Value;",
                ),
                declaration = declaration,
                utility = utility,
                arguments = arguments,
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let callable = parse_source_file(
                "declare function bound<Value extends Result>(value: Value): Value;",
            );
            let mut context = mapped_constraint_context(&parsed, &callable, true);
            let (result_alias, request) =
                mapped_constraint_alias_parts(&parsed, &context, "Result");
            let result = context.get_declared_type_of_symbol(result_alias).unwrap();
            let (utility_alias, _) = mapped_constraint_alias_parts(&parsed, &context, utility);
            let NodeData::TypeReferenceNode(reference) =
                &parsed.arena.get(request.node).unwrap().data
            else {
                panic!("Result must retain its utility reference")
            };
            let arguments = reference
                .type_arguments
                .as_ref()
                .unwrap()
                .nodes
                .iter()
                .map(|argument| {
                    context
                        .get_type_from_type_node(NodeRef::new(
                            request.arena,
                            request.file,
                            *argument,
                        ))
                        .unwrap()
                })
                .collect::<Vec<_>>();
            let links = context.store().type_alias_links(utility_alias).unwrap();
            let declared = links.declared_type.unwrap();
            let parameters = links.type_parameters.clone().unwrap();
            let validate = |store: &CanonicalTypeMapperStore| match utility {
                "Record" => store.validate_record_mapped_alias_instantiation(
                    utility_alias,
                    declared,
                    &parameters,
                    &arguments,
                    result,
                ),
                "Partial" => store.validate_homomorphic_mapped_alias_instantiation(
                    utility_alias,
                    declared,
                    &parameters,
                    &arguments,
                    result,
                    modifiers,
                ),
                "Pick" => store.validate_pick_mapped_alias_instantiation(
                    utility_alias,
                    declared,
                    &parameters,
                    &arguments,
                    result,
                ),
                _ => unreachable!(),
            };
            let snapshot = |store: &CanonicalTypeMapperStore| {
                let TypeData::Mapped(data) = store.type_payload(result).unwrap().data() else {
                    panic!("the utility result must remain a mapped type")
                };
                (
                    cache_state(store),
                    store.type_resolution_len(),
                    store.type_resolution_start(),
                    [
                        store.signature_len(),
                        store.index_info_len(),
                        store.properties_type_cache_len(),
                    ],
                    data.clone(),
                    [utility_alias, result_alias]
                        .map(|alias| store.type_alias_links(alias).cloned()),
                )
            };
            let TypeData::Mapped(data) = context.store().type_payload(result).unwrap().data()
            else {
                unreachable!()
            };
            assert_eq!(data.object.structured, StructuredTypeData::default());
            let cold = snapshot(context.store());
            assert_eq!(validate(context.store()), Ok(()));
            assert_eq!(
                context.get_declared_type_of_symbol(result_alias),
                Ok(result)
            );
            assert_eq!(snapshot(context.store()), cold);

            assert_mapped_constraint_probe_is_unsupported(&parsed, &mut context);
            let parameter = mapped_constraint_function_parameter(&parsed, &callable, &mut context);
            assert_eq!(
                get_base_constraint_of_type(context.store_mut_for_test(), parameter),
                Ok(Some(result)),
            );
            let TypeData::Mapped(data) = context.store().type_payload(result).unwrap().data()
            else {
                unreachable!()
            };
            let base = data.object.structured.constrained.resolved_base_constraint;
            assert_eq!(base, Some(result));
            assert!(unresolved_mapped_structure_is_valid(
                context.store(),
                result,
                &data.object.structured
            ));
            let warm = snapshot(context.store());
            for _ in 0..2 {
                assert_eq!(validate(context.store()), Ok(()));
                assert_eq!(
                    context.get_declared_type_of_symbol(result_alias),
                    Ok(result)
                );
                assert_eq!(
                    context
                        .store()
                        .validate_mapped_type_relation_endpoint(result),
                    Ok(None)
                );
                assert_eq!(snapshot(context.store()), warm);
            }

            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert!(
                context
                    .store_mut_for_test()
                    .set_resolved_base_constraint(result, Some(string))
            );
            let damaged = snapshot(context.store());
            assert!(validate(context.store()).is_err());
            assert!(context.get_declared_type_of_symbol(result_alias).is_err());
            assert_eq!(snapshot(context.store()), damaged);
            assert!(
                context
                    .store_mut_for_test()
                    .set_resolved_base_constraint(result, base)
            );
            assert_eq!(validate(context.store()), Ok(()));
            assert_eq!(
                context.get_declared_type_of_symbol(result_alias),
                Ok(result)
            );
            assert_eq!(snapshot(context.store()), warm);
            assert!(context.diagnostics().is_empty());
        }
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
