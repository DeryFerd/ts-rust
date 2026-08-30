//! Exact nongeneric property-key extraction.
//!
//! This leaf implements the dependency-independent prefix of pinned
//! `getIndexType` and `getLiteralTypeFromProperties`. It accepts authenticated
//! ordinary type parameters and fully resolved, source-owned interfaces,
//! type literals, and fresh or derived object literals. Ordinary type
//! parameters reuse one normalized `IndexType` identity. Named properties
//! become canonical regular string-literal types,
//! a number index contributes `number`, and a string index contributes
//! `string | number`. The latter absorbs every explicit property and number
//! index in the result.
//!
//! Anonymous type literals use the existing canonical literal/union caches.
//! Class/interface/reference and aliased objects additionally preserve pinned
//! `propertiesTypes` cache timing: cold resolution allocates an
//! `IndexType(target)` shell before property literals even when the raw result
//! has cardinality zero or one and discards that origin; warm resolution
//! validates and returns the checker-owned cache entry without writes.
//!
//! Object unions intersect their constituent key sets. Object intersections
//! unite them after checking whether the intersection reduces to `never`.
//! `any`, `unknown`, and `never` use their pinned intrinsic key identities.
//! Generic objects, tuples, apparent/inherited members, computed/unique-symbol
//! names, and unresolved member surfaces remain explicit boundaries.

use std::collections::HashSet;

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    declared::cached_ordinary_type_parameter_owner,
    derived_types::DerivedObjectLiteralValidation,
    instantiate::InstantiationSession,
    links::{TypeNodeLinks, ValueSymbolLinks},
    mapped_types::{MappedTypeError, MappedTypeKey, MappedTypeKeys, plan_mapped_type_keys},
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_declared_property_object,
    },
    signatures::IndexFlags,
    store::{PropertiesTypeCacheKey, SourceNodeParent},
    type_records::{
        ConstrainedTypeData, InterfaceTypeData, ObjectTypeData, StructuredTypeData, TypeCacheState,
        TypeData, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

/// One fully validated, reduced-object key surface.
///
/// Property names remain strings until execution so a named-origin boundary
/// can be returned without populating global literal caches. The plan is
/// immutable and contains enough information for the root-owned
/// `propertiesTypes`/`IndexType` follow-up.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct NongenericKeyofPlan {
    target: TypeId,
    proof: NongenericKeyofProof,
    source_properties: Vec<(SemanticSymbolId, ValueSymbolLinks)>,
    array_targets: Option<CanonicalArrayTargets>,
    property_names: Vec<String>,
    has_string_index: bool,
    has_number_index: bool,
    preserves_origin: bool,
    composition: Option<KeyofComposition>,
}

/// The source proof used to obtain the property names in a key plan.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NongenericKeyofProof {
    Declared(DeclaredPropertyObjectProof),
    FreshObjectLiteral {
        owner: SemanticSymbolId,
    },
    DerivedObjectLiteral {
        owner: SemanticSymbolId,
        source: TypeId,
    },
    Composition,
}

impl PartialEq<DeclaredPropertyObjectProof> for NongenericKeyofProof {
    fn eq(&self, other: &DeclaredPropertyObjectProof) -> bool {
        matches!(self, Self::Declared(proof) if proof == other)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum KeyofComposition {
    Union(Vec<NongenericKeyofPlan>),
    Intersection(Vec<NongenericKeyofPlan>),
    Intrinsic(TypeId),
    GenericParameter,
    Mapped(Vec<MappedTypeKey>),
    MappedOverflow { size: usize, limit: usize },
}

impl NongenericKeyofPlan {
    pub(super) const fn target(&self) -> TypeId {
        self.target
    }

    pub(super) const fn proof(&self) -> NongenericKeyofProof {
        self.proof
    }

    pub(super) fn property_names(&self) -> &[String] {
        &self.property_names
    }

    pub(super) const fn has_string_index(&self) -> bool {
        self.has_string_index
    }

    pub(super) const fn has_number_index(&self) -> bool {
        self.has_number_index
    }

    pub(super) const fn preserves_origin(&self) -> bool {
        self.preserves_origin
    }

    /// Preserves the mapped-template overflow for production TS2590 recovery.
    pub(super) const fn mapped_cross_product_too_large(&self) -> Option<(usize, usize)> {
        match &self.composition {
            Some(KeyofComposition::MappedOverflow { size, limit }) => Some((*size, *limit)),
            _ => None,
        }
    }

    /// Count after pinned literal reduction.
    ///
    /// A string index always reduces the result to `string | number`.
    pub(super) fn reduced_key_count(&self) -> usize {
        if self.has_string_index {
            2
        } else {
            self.property_names.len() + usize::from(self.has_number_index)
        }
    }

    /// Number of entries passed to pinned `getUnionTypeEx` before reduction.
    ///
    /// A string index contributes the already-unioned
    /// `stringOrNumberType` as one raw entry. `getUnionTypeEx` returns a
    /// single raw entry before consulting its origin, so this count—not the
    /// reduced cardinality—controls named-origin construction.
    pub(super) fn raw_contribution_count(&self) -> usize {
        self.property_names.len()
            + usize::from(self.has_string_index)
            + usize::from(self.has_number_index)
    }

    /// Whether execution requires the checker-owned `propertiesTypes` cache.
    pub(super) const fn root_cache_required(&self) -> bool {
        self.preserves_origin
    }

    /// Whether the eager index origin survives pinned union construction.
    pub(super) fn retains_index_origin(&self) -> bool {
        self.preserves_origin && self.raw_contribution_count() >= 2
    }
}

/// Exact failure or named-origin composition boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NongenericKeyofError {
    InvalidType(TypeId),
    UnsupportedObject(TypeId),
    MalformedObject(TypeId),
    UnsupportedPropertyName {
        target: TypeId,
        property: SemanticSymbolId,
    },
    PropertiesCacheRequired {
        target: TypeId,
        raw_contribution_count: usize,
        reduced_key_count: usize,
        retains_index_origin: bool,
    },
    InvalidCachedResult(TypeId),
    CachePublication(TypeId),
    LiteralCache(LiteralTypeCacheError),
}

impl From<LiteralTypeCacheError> for NongenericKeyofError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

impl std::fmt::Display for NongenericKeyofError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "nongeneric keyof resolution failed: {self:?}")
    }
}

impl std::error::Error for NongenericKeyofError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::LiteralCache(error) => Some(error),
            _ => None,
        }
    }
}

/// Extracts the exact keys of a resolved source-owned object or type parameter.
///
/// The function is read-only. In particular, it does not resolve members,
/// instantiate references, or populate literal/union caches.
pub(super) fn plan_nongeneric_keyof_type(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<NongenericKeyofPlan, NongenericKeyofError> {
    plan_nongeneric_keyof_type_with_array_targets(store, target, None)
}

/// Retains the caller's array identities for derived object-literal checks.
/// The plan carries them through both cold execution and warm validation.
pub(super) fn plan_nongeneric_keyof_type_with_array_targets(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<NongenericKeyofPlan, NongenericKeyofError> {
    let record = store
        .type_payload(target)
        .ok_or(NongenericKeyofError::InvalidType(target))?;

    if record
        .flags()
        .intersects(TypeFlags::ANY | TypeFlags::NEVER | TypeFlags::UNKNOWN)
    {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let result = if target == bootstrap.wildcard_type {
            bootstrap.wildcard_type
        } else if record.flags().intersects(TypeFlags::UNKNOWN) {
            bootstrap.never_type
        } else {
            bootstrap.string_number_symbol_type
        };
        return Ok(intrinsic_keyof_plan(target, result, array_targets));
    }

    match record.data() {
        TypeData::TypeParameter(_) => {
            if cached_ordinary_type_parameter_owner(store, target).is_none() {
                return Err(NongenericKeyofError::MalformedObject(target));
            }
            return Ok(NongenericKeyofPlan {
                target,
                proof: NongenericKeyofProof::Composition,
                source_properties: Vec::new(),
                array_targets,
                property_names: Vec::new(),
                has_string_index: false,
                has_number_index: false,
                preserves_origin: false,
                composition: Some(KeyofComposition::GenericParameter),
            });
        }
        TypeData::Union(union) => {
            return plan_composite_keyof_type(
                store,
                target,
                &union.union.types,
                true,
                array_targets,
            );
        }
        TypeData::Intersection(_) => {
            let projection = store
                .validate_intersection_type(target)
                .map_err(|_| NongenericKeyofError::MalformedObject(target))?;
            if projection.reduced_to_never {
                let result = store
                    .intrinsic_bootstrap()
                    .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                    .string_number_symbol_type;
                return Ok(intrinsic_keyof_plan(target, result, array_targets));
            }
            return plan_composite_keyof_type(
                store,
                target,
                &projection.types,
                false,
                array_targets,
            );
        }
        TypeData::Mapped(_) => return plan_mapped_keyof_type(store, target, array_targets),
        _ => {}
    }

    let proof = match source_object_literal_proof(store, target, array_targets)? {
        Some(proof) => proof,
        None => match validate_resolved_declared_property_object(store, target) {
            DeclaredPropertyObjectValidation::Valid(proof) => NongenericKeyofProof::Declared(proof),
            DeclaredPropertyObjectValidation::Malformed => {
                return Err(NongenericKeyofError::MalformedObject(target));
            }
            DeclaredPropertyObjectValidation::NotDeclared => {
                match validate_resolved_indexed_declared_object(store, target, record)? {
                    Some(proof) => NongenericKeyofProof::Declared(proof),
                    None => return Err(NongenericKeyofError::UnsupportedObject(target)),
                }
            }
        },
    };
    let structured = record
        .data()
        .structured()
        .ok_or(NongenericKeyofError::MalformedObject(target))?;
    let property_names = exact_property_names(store, structured).map_err(|error| match error {
        ExactPropertyNamesError::Malformed => NongenericKeyofError::MalformedObject(target),
        ExactPropertyNamesError::Unsupported(property) => {
            NongenericKeyofError::UnsupportedPropertyName { target, property }
        }
    })?;
    let (has_string_index, has_number_index) = exact_index_kinds(store, structured)
        .ok_or(NongenericKeyofError::MalformedObject(target))?;
    let source_properties = if matches!(
        proof,
        NongenericKeyofProof::FreshObjectLiteral { .. }
            | NongenericKeyofProof::DerivedObjectLiteral { .. }
    ) {
        structured
            .properties
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|property| {
                store
                    .value_symbol_links(*property)
                    .cloned()
                    .map(|links| (*property, links))
                    .ok_or(NongenericKeyofError::MalformedObject(target))
            })
            .collect::<Result<Vec<_>, _>>()?
    } else {
        Vec::new()
    };
    let preserves_origin = proof == DeclaredPropertyObjectProof::Interface
        || record
            .object_flags()
            .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
        || record.alias().is_some();
    Ok(NongenericKeyofPlan {
        target,
        proof,
        source_properties,
        array_targets,
        property_names,
        has_string_index,
        has_number_index,
        preserves_origin,
        composition: None,
    })
}

fn source_object_literal_proof(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<NongenericKeyofProof>, NongenericKeyofError> {
    let record = store
        .type_payload(target)
        .ok_or(NongenericKeyofError::InvalidType(target))?;
    if !matches!(record.data(), TypeData::Object(_)) {
        return Ok(None);
    }
    let derived = match array_targets {
        Some(targets) => store.validate_derived_object_literal_with_array_targets(target, targets),
        None => store.validate_derived_object_literal_for_relation(target),
    };
    match derived {
        DerivedObjectLiteralValidation::Valid { owner, source } => {
            let Some(fresh) = source_object_literal_owner(store, target, owner)? else {
                return Ok(None);
            };
            let mut current = source;
            let mut seen = HashSet::new();
            while current != fresh {
                if !seen.insert(current) {
                    return Err(NongenericKeyofError::MalformedObject(target));
                }
                let validation = match array_targets {
                    Some(targets) => {
                        store.validate_derived_object_literal_with_array_targets(current, targets)
                    }
                    None => store.validate_derived_object_literal_for_relation(current),
                };
                let DerivedObjectLiteralValidation::Valid {
                    owner: current_owner,
                    source: next,
                } = validation
                else {
                    return Err(NongenericKeyofError::MalformedObject(target));
                };
                if current_owner != owner {
                    return Err(NongenericKeyofError::MalformedObject(target));
                }
                current = next;
            }
            Ok(Some(NongenericKeyofProof::DerivedObjectLiteral {
                owner,
                source,
            }))
        }
        DerivedObjectLiteralValidation::Invalid => {
            Err(NongenericKeyofError::MalformedObject(target))
        }
        DerivedObjectLiteralValidation::NotDerived => {
            let claims_literal = record
                .object_flags()
                .intersects(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
                || record.symbol().is_some_and(|owner| {
                    store.symbol(owner).is_some_and(|symbol| {
                        // Assignment-owned expandos have exports and no literal flags.
                        symbol.exports().is_none()
                            && (symbol.flags().intersects(SymbolFlags::OBJECT_LITERAL)
                                || store.source_symbol_flags(owner).is_some_and(|flags| {
                                    flags.intersects(SymbolFlags::OBJECT_LITERAL)
                                }))
                    })
                });
            if !claims_literal {
                return Ok(None);
            }
            let owner = record
                .symbol()
                .ok_or(NongenericKeyofError::MalformedObject(target))?;
            let Some(fresh) = source_object_literal_owner(store, target, owner)? else {
                return Ok(None);
            };
            if fresh != target || !store.validate_fresh_object_literal_for_relation(target) {
                return Err(NongenericKeyofError::MalformedObject(target));
            }
            Ok(Some(NongenericKeyofProof::FreshObjectLiteral { owner }))
        }
    }
}

/// Proves a source object identity without imposing property-key spelling rules.
/// A claimed source or derived cache that fails its proof is an error.
pub(super) fn validate_source_object_literal_for_keyof(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, NongenericKeyofError> {
    source_object_literal_proof(store, target, array_targets).map(|proof| proof.is_some())
}

fn source_object_literal_owner(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    owner: SemanticSymbolId,
) -> Result<Option<TypeId>, NongenericKeyofError> {
    let invalid = || NongenericKeyofError::MalformedObject(target);
    let symbol = store.symbol(owner).ok_or_else(invalid)?;
    let Some([declaration]) = symbol.declarations() else {
        return Err(invalid());
    };
    if symbol.flags() != SymbolFlags::OBJECT_LITERAL
        || symbol.check_flags() != CheckFlags::NONE
        || symbol.value_declaration() != Some(*declaration)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::ObjectLiteralExpression)
        || store.source_symbol_flags(owner) != Some(SymbolFlags::OBJECT_LITERAL)
        || !store.source_symbol_declarations_match(owner)
        || store.source_declaration_symbol(*declaration) != Some(owner)
        || !store.source_declaration_belongs_to_symbol(*declaration, owner)
    {
        return Err(invalid());
    }
    let children = store
        .source_direct_children(*declaration)
        .ok_or_else(invalid)?;
    if children.iter().any(|child| {
        !matches!(
            store.source_node_kind(*child),
            Some(SyntaxKind::PropertyAssignment | SyntaxKind::ShorthandPropertyAssignment)
        )
    }) {
        return Ok(None);
    }
    let members = symbol
        .members()
        .map(|members| store.symbol_table(members).ok_or_else(invalid))
        .transpose()?;
    if members.map_or(0, ts_binder::semantic::SymbolTable::len) != children.len() {
        return Err(invalid());
    }
    let mut seen = HashSet::new();
    if let Some(members) = members {
        for (_, property) in members.iter() {
            let property_record = store.symbol(property).ok_or_else(invalid)?;
            let Some([property_declaration]) = property_record.declarations() else {
                return Err(invalid());
            };
            if property_record.flags() != SymbolFlags::PROPERTY
                || property_record.parent() != Some(owner)
                || property_record.value_declaration() != Some(*property_declaration)
                || store.source_symbol_flags(property) != Some(SymbolFlags::PROPERTY)
                || !store.source_symbol_declarations_match(property)
                || store.source_declaration_symbol(*property_declaration) != Some(property)
                || !store.source_declaration_belongs_to_symbol(*property_declaration, property)
                || store.source_node_parent(*property_declaration)
                    != Some(SourceNodeParent::Parent(*declaration))
                || !children.contains(property_declaration)
                || !seen.insert(*property_declaration)
            {
                return Err(invalid());
            }
        }
    }
    let fresh = store
        .type_node_links(*declaration)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    if store.type_node_links(*declaration)
        != Some(&TypeNodeLinks {
            resolved_type: Some(fresh),
            outer_type_parameters: None,
        })
        || store.type_payload(fresh).and_then(TypeRecord::symbol) != Some(owner)
        || !store.validate_fresh_object_literal_for_relation(fresh)
    {
        return Err(invalid());
    }
    let properties = store
        .type_payload(fresh)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?
        .properties
        .as_deref()
        .unwrap_or_default();
    for property in properties {
        let origin = store
            .object_literal_property_clone_origin(*property)
            .ok_or_else(invalid)?;
        if origin.symbol() != *property
            || origin.owner() != *declaration
            || store
                .value_symbol_links(*property)
                .and_then(|links| links.target)
                != Some(origin.source())
        {
            return Err(invalid());
        }
    }
    Ok(Some(fresh))
}

fn plan_mapped_keyof_type(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<NongenericKeyofPlan, NongenericKeyofError> {
    let keys = match plan_mapped_type_keys(store, target) {
        Ok(keys) => keys,
        Err(MappedTypeError::CrossProductTooLarge { size, limit }) => {
            return Ok(NongenericKeyofPlan {
                target,
                proof: NongenericKeyofProof::Composition,
                source_properties: Vec::new(),
                array_targets,
                property_names: Vec::new(),
                has_string_index: false,
                has_number_index: false,
                preserves_origin: false,
                composition: Some(KeyofComposition::MappedOverflow { size, limit }),
            });
        }
        Err(error) => {
            return Err(match error {
                MappedTypeError::BootstrapUninitialized => NongenericKeyofError::LiteralCache(
                    LiteralTypeCacheError::BootstrapUninitialized,
                ),
                MappedTypeError::Capacity => {
                    NongenericKeyofError::LiteralCache(LiteralTypeCacheError::Capacity)
                }
                MappedTypeError::InvalidMappedType(_)
                | MappedTypeError::InvalidSource(_)
                | MappedTypeError::InvalidTypeParameter(_)
                | MappedTypeError::InvalidCachedMembers(_)
                | MappedTypeError::InvalidCachedProperty(_) => {
                    NongenericKeyofError::MalformedObject(target)
                }
                _ => NongenericKeyofError::UnsupportedObject(target),
            });
        }
    };
    match keys {
        MappedTypeKeys::Constraint(constraint) => {
            Ok(intrinsic_keyof_plan(target, constraint, array_targets))
        }
        MappedTypeKeys::Remapped(keys) => {
            let mut property_names = Vec::new();
            for key in &keys {
                let name = key
                    .name(store)
                    .ok_or(NongenericKeyofError::MalformedObject(target))?;
                if !property_names.contains(&name) {
                    property_names.push(name);
                }
            }
            Ok(NongenericKeyofPlan {
                target,
                proof: NongenericKeyofProof::Composition,
                source_properties: Vec::new(),
                array_targets,
                property_names,
                has_string_index: false,
                has_number_index: false,
                preserves_origin: false,
                composition: Some(KeyofComposition::Mapped(keys)),
            })
        }
    }
}

fn intrinsic_keyof_plan(
    target: TypeId,
    result: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> NongenericKeyofPlan {
    NongenericKeyofPlan {
        target,
        proof: NongenericKeyofProof::Composition,
        source_properties: Vec::new(),
        array_targets,
        property_names: Vec::new(),
        has_string_index: false,
        has_number_index: false,
        preserves_origin: false,
        composition: Some(KeyofComposition::Intrinsic(result)),
    }
}

fn plan_composite_keyof_type(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    types: &[TypeId],
    is_union: bool,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<NongenericKeyofPlan, NongenericKeyofError> {
    if types.len() < 2 {
        return Err(NongenericKeyofError::MalformedObject(target));
    }

    let mut constituents = Vec::with_capacity(types.len());
    for type_ in types {
        let constituent =
            plan_nongeneric_keyof_type_with_array_targets(store, *type_, array_targets).map_err(
                |error| match error {
                    NongenericKeyofError::UnsupportedObject(_) => {
                        NongenericKeyofError::UnsupportedObject(target)
                    }
                    other => other,
                },
            )?;
        if matches!(
            constituent.composition,
            Some(
                KeyofComposition::Intrinsic(_)
                    | KeyofComposition::GenericParameter
                    | KeyofComposition::MappedOverflow { .. }
            )
        ) {
            return Err(NongenericKeyofError::UnsupportedObject(target));
        }
        constituents.push(constituent);
    }

    if is_union {
        let validation = match array_targets {
            Some(targets) => store.validate_union_constituent_with_array_targets(targets, target),
            None => store.validate_union_constituent(target),
        };
        validation.map_err(|_| NongenericKeyofError::MalformedObject(target))?;
    }

    let mut property_names = Vec::new();
    for constituent in &constituents {
        for name in &constituent.property_names {
            if !property_names.contains(name) {
                property_names.push(name.clone());
            }
        }
    }
    let (has_string_index, has_number_index) = if is_union {
        property_names.retain(|name| {
            constituents.iter().all(|constituent| {
                constituent.has_string_index || constituent.property_names.contains(name)
            })
        });
        (
            constituents
                .iter()
                .all(|constituent| constituent.has_string_index),
            constituents
                .iter()
                .all(|constituent| constituent.has_string_index || constituent.has_number_index),
        )
    } else {
        (
            constituents
                .iter()
                .any(|constituent| constituent.has_string_index),
            constituents
                .iter()
                .any(|constituent| constituent.has_number_index),
        )
    };

    Ok(NongenericKeyofPlan {
        target,
        proof: NongenericKeyofProof::Composition,
        source_properties: Vec::new(),
        array_targets,
        property_names,
        has_string_index,
        has_number_index,
        preserves_origin: false,
        composition: Some(if is_union {
            KeyofComposition::Union(constituents)
        } else {
            KeyofComposition::Intersection(constituents)
        }),
    })
}

/// Resolves one validated nongeneric key plan through the exact checker-owned
/// `propertiesTypes` cache.
///
/// Every cold result is published under the pinned key after dependency-closed
/// cache preparation. Every warm result is independently rederived and
/// validated before its identity is returned.
pub(super) fn resolve_nongeneric_keyof_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<TypeId, NongenericKeyofError> {
    resolve_nongeneric_keyof_type_worker(store, plan, None)
}

/// Uses the caller's budget for key-union preparation and recursive key plans.
pub(super) fn resolve_nongeneric_keyof_type_with_session(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    session: &mut InstantiationSession,
) -> Result<TypeId, NongenericKeyofError> {
    resolve_nongeneric_keyof_type_worker(store, plan, Some(session))
}

fn resolve_nongeneric_keyof_type_worker(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, NongenericKeyofError> {
    if let Some(cached) = cached_nongeneric_keyof_type(store, plan)? {
        return Ok(cached);
    }
    if let Some(composition) = &plan.composition {
        return resolve_composite_keyof_type(store, plan, composition, session);
    }
    let key = properties_type_cache_key(store, plan)?;
    if !store.try_reserve_properties_type_cache(1) {
        return Err(LiteralTypeCacheError::Capacity.into());
    }
    let result = if plan.preserves_origin {
        resolve_origin_preserving_nongeneric_keyof_type(store, plan, session)?
    } else {
        resolve_nongeneric_keyof_leaf_worker(store, plan, session)?
    };
    if !store.cache_properties_type(key, result) {
        return Err(NongenericKeyofError::CachePublication(plan.target));
    }
    Ok(result)
}

/// Validates a previously published `propertiesTypes` result without
/// allocating or mutating any semantic cache.
pub(super) fn cached_nongeneric_keyof_type(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<Option<TypeId>, NongenericKeyofError> {
    validate_plan_against_store(store, plan)?;
    if let Some(composition) = &plan.composition {
        return cached_composite_keyof_type(store, plan, composition);
    }
    let key = properties_type_cache_key(store, plan)?;
    let Some(cached) = store.cached_properties_type(key) else {
        return Ok(None);
    };
    validate_cached_nongeneric_keyof_result(store, plan, cached)?;
    Ok(Some(cached))
}

fn resolve_composite_keyof_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    composition: &KeyofComposition,
    mut session: Option<&mut InstantiationSession>,
) -> Result<TypeId, NongenericKeyofError> {
    let constituents = match composition {
        KeyofComposition::Intrinsic(result) => return Ok(*result),
        KeyofComposition::GenericParameter => {
            if !store.try_reserve_types(1) {
                return Err(LiteralTypeCacheError::Capacity.into());
            }
            return store
                .alloc_index_type(plan.target, IndexFlags::NONE)
                .ok_or_else(|| LiteralTypeCacheError::Capacity.into());
        }
        KeyofComposition::Mapped(keys) => {
            return resolve_mapped_keyof_type(store, plan, keys, session);
        }
        KeyofComposition::MappedOverflow { size, limit } => {
            debug_assert_eq!(plan.mapped_cross_product_too_large(), Some((*size, *limit)),);
            return store
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.error_type)
                .ok_or_else(|| LiteralTypeCacheError::BootstrapUninitialized.into());
        }
        KeyofComposition::Union(constituents) | KeyofComposition::Intersection(constituents) => {
            constituents
        }
    };

    let mut cold_strings = Vec::new();
    let mut cold_count = 0usize;
    let mut union_operations = 1usize;
    for constituent in constituents {
        if cached_nongeneric_keyof_type(store, constituent)?.is_some() {
            continue;
        }
        cold_count += 1;
        cold_strings.extend(constituent.property_names.iter().cloned());
        if constituent.preserves_origin
            || !constituent.has_string_index && constituent.reduced_key_count() >= 2
        {
            union_operations += 1;
        }
    }
    if !store.try_reserve_properties_type_cache(cold_count) {
        return Err(LiteralTypeCacheError::Capacity.into());
    }
    prepare_keyof_types(
        store,
        &cold_strings,
        union_operations,
        session.as_deref_mut(),
    )?;

    let mut results = Vec::with_capacity(constituents.len());
    for constituent in constituents {
        results.push(resolve_nongeneric_keyof_type_worker(
            store,
            constituent,
            session.as_deref_mut(),
        )?);
    }

    match composition {
        KeyofComposition::Intersection(_) => {
            let mut prepared = prepare_keyof_types(store, &[], 1, session.as_deref_mut())?;
            store
                .literal_union_type_prepared(&results, None, &mut prepared)
                .map_err(Into::into)
        }
        KeyofComposition::Union(_) => {
            let keys = composite_key_types(store, plan)?;
            match keys.as_slice() {
                [] => Ok(store
                    .intrinsic_bootstrap()
                    .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                    .never_type),
                [only] => Ok(*only),
                _ => {
                    let mut prepared = prepare_keyof_types(store, &[], 1, session.as_deref_mut())?;
                    store
                        .literal_union_type_prepared(&keys, None, &mut prepared)
                        .map_err(Into::into)
                }
            }
        }
        KeyofComposition::Intrinsic(_) => unreachable!("intrinsic keys return before planning"),
        KeyofComposition::GenericParameter => {
            unreachable!("generic parameter keys return before planning")
        }
        KeyofComposition::Mapped(_) => unreachable!("mapped keys return before planning"),
        KeyofComposition::MappedOverflow { .. } => {
            unreachable!("mapped overflow returns before planning")
        }
    }
}

fn cached_composite_keyof_type(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    composition: &KeyofComposition,
) -> Result<Option<TypeId>, NongenericKeyofError> {
    let constituents = match composition {
        KeyofComposition::Intrinsic(result) => return Ok(Some(*result)),
        KeyofComposition::GenericParameter => {
            return cached_generic_keyof_index_type(store, plan.target);
        }
        KeyofComposition::Mapped(keys) => return cached_mapped_keyof_type(store, plan, keys),
        KeyofComposition::MappedOverflow { .. } => {
            return store
                .intrinsic_bootstrap()
                .map(|bootstrap| Some(bootstrap.error_type))
                .ok_or_else(|| LiteralTypeCacheError::BootstrapUninitialized.into());
        }
        KeyofComposition::Union(constituents) | KeyofComposition::Intersection(constituents) => {
            constituents
        }
    };

    let mut results = Vec::with_capacity(constituents.len());
    let mut missing = false;
    for constituent in constituents {
        match cached_nongeneric_keyof_type(store, constituent)? {
            Some(result) => results.push(result),
            None => missing = true,
        }
    }
    if missing {
        return Ok(None);
    }

    let keys = composite_key_types(store, plan)?;
    match keys.as_slice() {
        [] => Ok(Some(
            store
                .intrinsic_bootstrap()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                .never_type,
        )),
        [only] => Ok(Some(*only)),
        _ => cached_composite_key_union(
            store,
            &keys,
            &results,
            matches!(composition, KeyofComposition::Intersection(_)),
        ),
    }
}

fn cached_generic_keyof_index_type(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<Option<TypeId>, NongenericKeyofError> {
    if cached_ordinary_type_parameter_owner(store, target).is_none() {
        return Err(NongenericKeyofError::MalformedObject(target));
    }

    let mut cached = None;
    for (type_, record) in store.types() {
        let TypeData::Index(index) = record.data() else {
            continue;
        };
        if index.target != target || index.index_flags != IndexFlags::NONE {
            continue;
        }
        if record.flags() != TypeFlags::INDEX
            || record.object_flags() != ObjectFlags::NONE
            || record.symbol().is_some()
            || record.alias().is_some()
            || !generic_keyof_base_constraint_is_exact(
                store,
                index.constrained.resolved_base_constraint,
            )
            || cached.replace(type_).is_some()
        {
            return Err(NongenericKeyofError::InvalidCachedResult(type_));
        }
    }
    Ok(cached)
}

/// Proves the normalized Index identity for one source-owned type parameter.
/// Named-object Index origins are outside this generic substitution contract.
pub(super) fn validate_generic_keyof_index_type(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
) -> Result<TypeId, NongenericKeyofError> {
    let record = store
        .type_payload(index_type)
        .ok_or(NongenericKeyofError::InvalidType(index_type))?;
    let TypeData::Index(index) = record.data() else {
        return Err(NongenericKeyofError::UnsupportedObject(index_type));
    };
    if record.flags() != TypeFlags::INDEX
        || record.object_flags() != ObjectFlags::NONE
        || record.symbol().is_some()
        || record.alias().is_some()
        || index.index_flags != IndexFlags::NONE
        || !generic_keyof_base_constraint_is_exact(
            store,
            index.constrained.resolved_base_constraint,
        )
    {
        return Err(NongenericKeyofError::InvalidCachedResult(index_type));
    }
    let owner = cached_ordinary_type_parameter_owner(store, index.target)
        .ok_or(NongenericKeyofError::MalformedObject(index.target))?;
    let symbol = store
        .symbol(owner)
        .ok_or(NongenericKeyofError::MalformedObject(index.target))?;
    let Some([declaration]) = symbol.declarations() else {
        return Err(NongenericKeyofError::MalformedObject(index.target));
    };
    if symbol.flags() != SymbolFlags::TYPE_PARAMETER
        || symbol.check_flags() != CheckFlags::NONE
        || symbol.value_declaration().is_some()
        || symbol.members().is_some()
        || symbol.exports().is_some()
        || symbol.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_symbol_flags(owner) != Some(SymbolFlags::TYPE_PARAMETER)
        || !store.source_symbol_declarations_match(owner)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::TypeParameter)
        || !store.source_declaration_belongs_to_symbol(*declaration, owner)
        || store.source_declaration_symbol(*declaration) != Some(owner)
    {
        return Err(NongenericKeyofError::MalformedObject(index.target));
    }
    if cached_generic_keyof_index_type(store, index.target)? != Some(index_type) {
        return Err(NongenericKeyofError::InvalidCachedResult(index_type));
    }
    Ok(index.target)
}

fn generic_keyof_base_constraint_is_exact(
    store: &CanonicalTypeMapperStore,
    constraint: Option<TypeId>,
) -> bool {
    constraint.is_none_or(|constraint| {
        store
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| constraint == bootstrap.string_number_symbol_type)
    })
}

fn resolve_mapped_keyof_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    keys: &[MappedTypeKey],
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, NongenericKeyofError> {
    let mut pending = Vec::new();
    for key in keys {
        if let MappedTypeKey::String(value) = key
            && key.cached_type(store).is_none()
            && !pending.contains(value)
        {
            pending.push(value.clone());
        }
    }
    let mut prepared = prepare_keyof_types(store, &pending, usize::from(keys.len() > 1), session)?;
    let mut resolved = Vec::with_capacity(keys.len());
    for key in keys {
        let type_ = match key {
            MappedTypeKey::Existing(type_) => *type_,
            MappedTypeKey::String(value) => store.regular_string_literal_type(value.clone())?,
        };
        if !resolved.contains(&type_) {
            resolved.push(type_);
        }
    }
    let result = match resolved.as_slice() {
        [] => {
            store
                .intrinsic_bootstrap()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                .never_type
        }
        [only] => *only,
        _ => store.literal_union_type_prepared(&resolved, None, &mut prepared)?,
    };
    if let Some(TypeData::Mapped(mapped)) = store.type_payload(plan.target).map(TypeRecord::data)
        && let Some(constraint) = mapped.constraint_type
        && union_contains_exact_keys(store, constraint, &resolved)
    {
        return Ok(constraint);
    }
    Ok(result)
}

fn cached_mapped_keyof_type(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    keys: &[MappedTypeKey],
) -> Result<Option<TypeId>, NongenericKeyofError> {
    let Some(mut resolved) = keys
        .iter()
        .map(|key| key.cached_type(store))
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(None);
    };
    resolved.sort_unstable();
    resolved.dedup();
    match resolved.as_slice() {
        [] => Ok(Some(
            store
                .intrinsic_bootstrap()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                .never_type,
        )),
        [only] => Ok(Some(*only)),
        _ => {
            if let Some(TypeData::Mapped(mapped)) =
                store.type_payload(plan.target).map(TypeRecord::data)
                && let Some(constraint) = mapped.constraint_type
                && union_contains_exact_keys(store, constraint, &resolved)
            {
                store
                    .validate_union_constituent(constraint)
                    .map_err(|_| NongenericKeyofError::InvalidCachedResult(constraint))?;
                return Ok(Some(constraint));
            }
            let mut cached = None;
            for (type_, record) in store.types() {
                let TypeData::Union(union) = record.data() else {
                    continue;
                };
                if record.alias().is_some()
                    || union.origin.is_some()
                    || union.union.types.len() != resolved.len()
                    || !resolved.iter().all(|key| union.union.types.contains(key))
                {
                    continue;
                }
                store
                    .validate_union_constituent(type_)
                    .map_err(|_| NongenericKeyofError::InvalidCachedResult(type_))?;
                if cached.replace(type_).is_some() {
                    return Err(NongenericKeyofError::InvalidCachedResult(type_));
                }
            }
            Ok(cached)
        }
    }
}

fn composite_key_types(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<Vec<TypeId>, NongenericKeyofError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
    if plan.has_string_index {
        return Ok(vec![bootstrap.string_type, bootstrap.number_type]);
    }

    let mut keys = Vec::with_capacity(plan.property_names.len() + 1);
    for name in &plan.property_names {
        keys.push(
            bootstrap
                .cached_string_literal_type(name)
                .ok_or(NongenericKeyofError::InvalidCachedResult(plan.target))?,
        );
    }
    if plan.has_number_index {
        keys.push(bootstrap.number_type);
    }
    Ok(keys)
}

fn cached_composite_key_union(
    store: &CanonicalTypeMapperStore,
    keys: &[TypeId],
    results: &[TypeId],
    preserve_constituent_origins: bool,
) -> Result<Option<TypeId>, NongenericKeyofError> {
    let mut named_unions = Vec::new();
    if preserve_constituent_origins {
        for result in results {
            collect_named_key_unions(store, *result, &mut named_unions)?;
        }
    }

    if let [only] = named_unions.as_slice()
        && union_contains_exact_keys(store, *only, keys)
    {
        store
            .validate_union_constituent(*only)
            .map_err(|_| NongenericKeyofError::InvalidCachedResult(*only))?;
        return Ok(Some(*only));
    }

    let mut uncovered = Vec::new();
    for key in keys {
        if !named_unions.iter().any(|union| {
            matches!(
                store.type_payload(*union).map(TypeRecord::data),
                Some(TypeData::Union(data)) if data.union.types.contains(key)
            )
        }) {
            uncovered.push(*key);
        }
    }
    let named_key_count = named_unions
        .iter()
        .map(
            |union| match store.type_payload(*union).map(TypeRecord::data) {
                Some(TypeData::Union(data)) => data.union.types.len(),
                _ => 0,
            },
        )
        .sum::<usize>();
    let expected_origin =
        !named_unions.is_empty() && named_key_count + uncovered.len() == keys.len();

    for (candidate, record) in store.types() {
        let TypeData::Union(union) = record.data() else {
            continue;
        };
        if record.alias().is_some() || !union_contains_exact_keys(store, candidate, keys) {
            continue;
        }

        let origin_matches = match union.origin {
            None => !expected_origin,
            Some(origin) if expected_origin => {
                matches!(
                    store.type_payload(origin).map(TypeRecord::data),
                    Some(TypeData::Union(data))
                        if data.union.types.len() == named_unions.len() + uncovered.len()
                            && named_unions.iter().all(|named| data.union.types.contains(named))
                            && uncovered.iter().all(|key| data.union.types.contains(key))
                )
            }
            Some(_) => false,
        };
        if origin_matches {
            store
                .validate_union_constituent(candidate)
                .map_err(|_| NongenericKeyofError::InvalidCachedResult(candidate))?;
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

fn collect_named_key_unions(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    named: &mut Vec<TypeId>,
) -> Result<(), NongenericKeyofError> {
    let record = store
        .type_payload(type_)
        .ok_or(NongenericKeyofError::InvalidCachedResult(type_))?;
    let TypeData::Union(union) = record.data() else {
        return Ok(());
    };
    match union.origin {
        Some(origin)
            if matches!(
                store.type_payload(origin).map(TypeRecord::data),
                Some(TypeData::Index(_))
            ) =>
        {
            if !named.contains(&type_) {
                named.push(type_);
            }
        }
        Some(origin) => {
            let Some(TypeData::Union(origin)) = store.type_payload(origin).map(TypeRecord::data)
            else {
                return Err(NongenericKeyofError::InvalidCachedResult(type_));
            };
            for constituent in &origin.union.types {
                collect_named_key_unions(store, *constituent, named)?;
            }
        }
        None => {}
    }
    Ok(())
}

fn union_contains_exact_keys(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    keys: &[TypeId],
) -> bool {
    matches!(
        store.type_payload(union).map(TypeRecord::data),
        Some(TypeData::Union(data))
            if data.union.types.len() == keys.len()
                && keys.iter().all(|key| data.union.types.contains(key))
    )
}

/// Dependency-independent anonymous-object executor retained as an explicit
/// composition boundary for adversarial tests.
#[cfg(test)]
fn resolve_nongeneric_keyof_leaf(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<TypeId, NongenericKeyofError> {
    resolve_nongeneric_keyof_leaf_worker(store, plan, None)
}

fn resolve_nongeneric_keyof_leaf_worker(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, NongenericKeyofError> {
    validate_plan_against_store(store, plan)?;
    if plan.root_cache_required() {
        return Err(NongenericKeyofError::PropertiesCacheRequired {
            target: plan.target,
            raw_contribution_count: plan.raw_contribution_count(),
            reduced_key_count: plan.reduced_key_count(),
            retains_index_origin: plan.retains_index_origin(),
        });
    }

    // Pinned getLiteralTypeFromProperties asks for property literals even
    // when a string index later absorbs them during union reduction.
    let strings = plan.property_names.clone();
    let union_operations = usize::from(!plan.has_string_index && plan.reduced_key_count() >= 2);
    let mut prepared = prepare_keyof_types(store, &strings, union_operations, session)?;
    let mut keys = Vec::with_capacity(plan.property_names.len() + 1);
    for name in &plan.property_names {
        keys.push(store.regular_string_literal_type(name.clone())?);
    }

    let (number_type, string_or_number_type, never_type) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (
            bootstrap.number_type,
            bootstrap.string_or_number_type,
            bootstrap.never_type,
        )
    };
    if plan.has_string_index {
        return Ok(string_or_number_type);
    }
    if plan.has_number_index {
        keys.push(number_type);
    }
    keys.sort_unstable();
    keys.dedup();
    match keys.len() {
        0 => Ok(never_type),
        1 => Ok(keys[0]),
        _ => store
            .literal_union_type_prepared(&keys, None, &mut prepared)
            .map_err(Into::into),
    }
}

fn resolve_origin_preserving_nongeneric_keyof_type(
    store: &mut CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, NongenericKeyofError> {
    let strings = plan.property_names.clone();
    let mut prepared = prepare_keyof_types(store, &strings, 1, session)?;
    let origin = store
        .alloc_index_type(plan.target, IndexFlags::NONE)
        .expect("the property-key preflight reserved the pinned Index origin");
    let mut keys = Vec::with_capacity(plan.raw_contribution_count());
    for name in &plan.property_names {
        keys.push(store.regular_string_literal_type(name.clone())?);
    }
    let (number_type, string_or_number_type) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (bootstrap.number_type, bootstrap.string_or_number_type)
    };
    if plan.has_string_index {
        keys.push(string_or_number_type);
    }
    if plan.has_number_index {
        keys.push(number_type);
    }
    store
        .literal_union_type_prepared_with_index_origin(&keys, origin, &mut prepared)
        .map_err(Into::into)
}

fn prepare_keyof_types(
    store: &mut CanonicalTypeMapperStore,
    strings: &[String],
    union_operations: usize,
    session: Option<&mut InstantiationSession>,
) -> Result<PreparedTypeQueryTypes, LiteralTypeCacheError> {
    match session {
        Some(session) => store.prepare_type_query_types_with_session(
            strings,
            &[],
            &[],
            union_operations,
            0,
            session,
        ),
        None => store.prepare_type_query_types(strings, &[], &[], union_operations, 0),
    }
}

fn properties_type_cache_key(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<PropertiesTypeCacheKey, NongenericKeyofError> {
    let record = store
        .type_payload(plan.target)
        .ok_or(NongenericKeyofError::InvalidType(plan.target))?;
    Ok(PropertiesTypeCacheKey::new(
        plan.target,
        TypeFlags::STRING_LIKE | TypeFlags::NUMBER_LIKE | TypeFlags::ES_SYMBOL_LIKE,
        true,
        record
            .object_flags()
            .intersects(ObjectFlags::UNRESOLVED_MEMBERS),
    ))
}

fn validate_cached_nongeneric_keyof_result(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
    cached: TypeId,
) -> Result<(), NongenericKeyofError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
    store
        .validate_union_constituent(cached)
        .map_err(|_| NongenericKeyofError::InvalidCachedResult(cached))?;
    let mut property_keys = Vec::with_capacity(plan.property_names.len());
    for name in &plan.property_names {
        let literal = bootstrap
            .cached_string_literal_type(name)
            .ok_or(NongenericKeyofError::InvalidCachedResult(cached))?;
        store
            .validate_union_constituent(literal)
            .map_err(|_| NongenericKeyofError::InvalidCachedResult(cached))?;
        property_keys.push(literal);
    }
    let mut raw = property_keys.clone();
    if plan.has_string_index {
        raw.push(bootstrap.string_or_number_type);
    }
    if plan.has_number_index {
        raw.push(bootstrap.number_type);
    }
    let expected_direct = match raw.as_slice() {
        [] => Some(bootstrap.never_type),
        [only] => Some(*only),
        _ => None,
    };
    if let Some(expected) = expected_direct {
        return (cached == expected)
            .then_some(())
            .ok_or(NongenericKeyofError::InvalidCachedResult(cached));
    }

    let normalized = if plan.has_string_index {
        let Some(TypeData::Union(union)) = store
            .type_payload(bootstrap.string_or_number_type)
            .map(TypeRecord::data)
        else {
            return Err(NongenericKeyofError::InvalidCachedResult(cached));
        };
        union.union.types.clone()
    } else {
        if plan.has_number_index {
            property_keys.push(bootstrap.number_type);
        }
        property_keys
    };

    if plan.preserves_origin {
        store
            .validate_union_constituent(cached)
            .map_err(|_| NongenericKeyofError::InvalidCachedResult(cached))?;
        let Some(TypeData::Union(union)) = store.type_payload(cached).map(TypeRecord::data) else {
            return Err(NongenericKeyofError::InvalidCachedResult(cached));
        };
        let Some(origin) = union.origin else {
            return Err(NongenericKeyofError::InvalidCachedResult(cached));
        };
        let Some(TypeData::Index(index)) = store.type_payload(origin).map(TypeRecord::data) else {
            return Err(NongenericKeyofError::InvalidCachedResult(cached));
        };
        if union.union.types.len() != normalized.len()
            || !normalized
                .iter()
                .all(|expected| union.union.types.contains(expected))
            || index.target != plan.target
            || index.index_flags != IndexFlags::NONE
        {
            return Err(NongenericKeyofError::InvalidCachedResult(cached));
        }
        return Ok(());
    }

    let Some(TypeData::Union(union)) = store.type_payload(cached).map(TypeRecord::data) else {
        return Err(NongenericKeyofError::InvalidCachedResult(cached));
    };
    if union.union.types.len() != normalized.len()
        || !normalized
            .iter()
            .all(|expected| union.union.types.contains(expected))
    {
        return Err(NongenericKeyofError::InvalidCachedResult(cached));
    }
    let expected = bootstrap
        .cached_union_type(&union.union.types)
        .ok_or(NongenericKeyofError::InvalidCachedResult(cached))?;
    (cached == expected)
        .then_some(())
        .ok_or(NongenericKeyofError::InvalidCachedResult(cached))
}

fn validate_plan_against_store(
    store: &CanonicalTypeMapperStore,
    plan: &NongenericKeyofPlan,
) -> Result<(), NongenericKeyofError> {
    if let Some(
        KeyofComposition::Union(constituents) | KeyofComposition::Intersection(constituents),
    ) = &plan.composition
    {
        for constituent in constituents {
            validate_plan_against_store(store, constituent)?;
        }
    }
    let current =
        plan_nongeneric_keyof_type_with_array_targets(store, plan.target, plan.array_targets)
            .map_err(|error| {
                if matches!(
                    plan.proof,
                    NongenericKeyofProof::FreshObjectLiteral { .. }
                        | NongenericKeyofProof::DerivedObjectLiteral { .. }
                ) && matches!(error, NongenericKeyofError::UnsupportedObject(_))
                {
                    NongenericKeyofError::MalformedObject(plan.target)
                } else {
                    error
                }
            })?;
    if current == *plan {
        Ok(())
    } else {
        Err(NongenericKeyofError::MalformedObject(plan.target))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExactPropertyNamesError {
    Malformed,
    Unsupported(SemanticSymbolId),
}

fn exact_property_names(
    store: &CanonicalTypeMapperStore,
    structured: &StructuredTypeData,
) -> Result<Vec<String>, ExactPropertyNamesError> {
    let properties = structured.properties.as_deref().unwrap_or_default();
    let mut names = Vec::with_capacity(properties.len());
    let mut seen_symbols = HashSet::with_capacity(properties.len());
    let mut seen_names = HashSet::with_capacity(properties.len());
    for property in properties {
        let record = store
            .symbol(*property)
            .ok_or(ExactPropertyNamesError::Malformed)?;
        let name = record
            .name()
            .as_utf8()
            .ok_or(ExactPropertyNamesError::Malformed)?
            .to_owned();
        if !is_unambiguous_identifier_property_name(&name) {
            return Err(ExactPropertyNamesError::Unsupported(*property));
        }
        if !seen_symbols.insert(*property) || !seen_names.insert(name.clone()) {
            return Err(ExactPropertyNamesError::Malformed);
        }
        names.push(name);
    }
    Ok(names)
}

/// Binder-owned symbol text does not retain whether `"0"` came from a
/// numeric declaration or a quoted string declaration. This host-free leaf
/// therefore accepts only conservative plain identifier spellings until
/// source-name classification is installed.
fn is_unambiguous_identifier_property_name(name: &str) -> bool {
    let mut bytes = name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || matches!(first, b'_' | b'$'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$'))
}

fn exact_index_kinds(
    store: &CanonicalTypeMapperStore,
    structured: &StructuredTypeData,
) -> Option<(bool, bool)> {
    let bootstrap = store.intrinsic_bootstrap()?;
    let mut string = false;
    let mut number = false;
    let mut seen = HashSet::new();
    for id in structured.index_infos.as_deref().unwrap_or_default() {
        if !seen.insert(*id) {
            return None;
        }
        let info = store.index_info(*id)?;
        let slot = if info.key_type() == bootstrap.string_type {
            &mut string
        } else if info.key_type() == bootstrap.number_type {
            &mut number
        } else {
            return None;
        };
        if std::mem::replace(slot, true) {
            return None;
        }
    }
    Some((string, number))
}

fn validate_resolved_indexed_declared_object(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
) -> Result<Option<DeclaredPropertyObjectProof>, NongenericKeyofError> {
    let Some(structured) = record.data().structured() else {
        return Ok(None);
    };
    if structured
        .index_infos
        .as_deref()
        .unwrap_or_default()
        .is_empty()
    {
        return Ok(None);
    }
    if record.flags() != TypeFlags::OBJECT {
        return Err(NongenericKeyofError::MalformedObject(target));
    }
    let result = match record.data() {
        TypeData::Object(object) => {
            validate_indexed_type_literal_shell(store, target, record, object)
                .then_some(DeclaredPropertyObjectProof::TypeLiteral)
        }
        TypeData::Interface(interface) => {
            validate_indexed_interface_shell(store, target, record, interface)
                .then_some(DeclaredPropertyObjectProof::Interface)
        }
        _ => return Ok(None),
    };
    result
        .ok_or(NongenericKeyofError::MalformedObject(target))
        .map(Some)
}

fn validate_indexed_type_literal_shell(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
    object: &ObjectTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && valid_object_tail(object)
        && valid_indexed_structured_tail(&object.structured)
        && owner_record.flags() == SymbolFlags::TYPE_LITERAL
        && owner_record.check_flags() == CheckFlags::NONE
        && owner_record.name() == InternalSymbolName::Type.as_ref()
        && owner_record.value_declaration().is_none()
        && owner_record.members() == object.structured.members
        && owner_record.exports().is_none()
        && owner_record.parent().is_none()
        && owner_record.export_symbol().is_none()
        && store.get_merged_symbol(owner) == Some(owner)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::TypeLiteral)
        && store.type_node_links(*declaration).is_some_and(|links| {
            links.resolved_type == Some(target) && links.outer_type_parameters.is_none()
        })
        && valid_nongeneric_type_literal_alias(store, target, record, *declaration)
        && validate_indexed_member_table(store, owner, *declaration, &object.structured)
}

fn validate_indexed_interface_shell(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    let object = &interface.reference.object;
    record.alias().is_none()
        && record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        && valid_interface_identity(interface)
        && interface.base_types_resolved
        && interface.resolved_base_constructor_type.is_none()
        && interface.resolved_base_types.is_none()
        && interface.declared_members_resolved
        && interface.declared_members == object.structured.members
        && interface.declared_call_signatures.is_none()
        && interface.declared_construct_signatures.is_none()
        && interface.declared_index_infos.as_ref() == object.structured.index_infos.as_ref()
        && valid_indexed_structured_tail(&object.structured)
        && owner_record.flags() == SymbolFlags::INTERFACE
        && owner_record.check_flags() == CheckFlags::NONE
        && owner_record.name().as_utf8().is_some()
        && owner_record.value_declaration().is_none()
        && owner_record.members() == object.structured.members
        && owner_record.exports().is_none()
        && owner_record.parent().is_none()
        && owner_record.export_symbol().is_none()
        && store.get_merged_symbol(owner) == Some(owner)
        && store.source_node_is_exported(*declaration) == Some(false)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
        && store
            .declared_type_links(owner)
            .is_some_and(|links| links.declared_type == Some(target))
        && validate_indexed_member_table(store, owner, *declaration, &object.structured)
}

fn valid_nongeneric_type_literal_alias(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    record: &TypeRecord,
    type_literal: NodeRef,
) -> bool {
    let Some(alias_id) = record.alias() else {
        return true;
    };
    let Some(alias) = store.type_alias(alias_id) else {
        return false;
    };
    let Some(symbol) = alias.symbol() else {
        return false;
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return false;
    };
    let Some([declaration]) = symbol_record.declarations() else {
        return false;
    };
    let mut child = type_literal;
    let direct = loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(child) else {
            break false;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType) => child = parent,
            Some(SyntaxKind::TypeAliasDeclaration) => break parent == *declaration,
            _ => break false,
        }
    };
    direct
        && alias.type_arguments().is_none()
        && symbol_record.flags() == SymbolFlags::TYPE_ALIAS
        && symbol_record.check_flags() == CheckFlags::NONE
        && symbol_record.value_declaration().is_none()
        && symbol_record.members().is_none()
        && symbol_record.exports().is_none()
        && symbol_record.parent().is_none()
        && symbol_record.export_symbol().is_none()
        && store.get_merged_symbol(symbol) == Some(symbol)
        && store.source_node_is_exported(*declaration) == Some(false)
        && store.source_node_kind(*declaration) == Some(SyntaxKind::TypeAliasDeclaration)
        && store.type_alias_links(symbol).is_some_and(|links| {
            links.declared_type == Some(target)
                && links.type_parameters.is_none()
                && links.instantiations.is_none()
                && !links.is_constructor_declared_property
        })
        && store
            .type_alias_declared_type_owners(target)
            .is_some_and(|owners| owners.len() == 1 && owners.contains(&symbol))
}

fn valid_object_tail(object: &ObjectTypeData) -> bool {
    object.target.is_none()
        && object.mapper.is_none()
        && object.instantiations == TypeCacheState::Unallocated
}

fn valid_interface_identity(interface: &InterfaceTypeData) -> bool {
    interface.all_type_parameters.is_none()
        && interface.outer_type_parameter_count == 0
        && interface.this_type.is_none()
        && valid_object_tail(&interface.reference.object)
        && interface.reference.node.is_none()
        && interface.reference.resolved_type_arguments.is_none()
}

fn valid_indexed_structured_tail(structured: &StructuredTypeData) -> bool {
    structured.constrained == ConstrainedTypeData::default()
        && structured.signatures.is_none()
        && structured.call_signature_count == 0
        && structured
            .index_infos
            .as_ref()
            .is_some_and(|indexes| !indexes.is_empty())
        && structured
            .object_type_without_abstract_construct_signatures
            .is_none()
}

fn validate_indexed_member_table(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    structured: &StructuredTypeData,
) -> bool {
    let properties = structured.properties.as_deref().unwrap_or_default();
    let indexes = structured.index_infos.as_deref().unwrap_or_default();
    let Some(members) = structured.members else {
        return false;
    };
    let Some(table) = store.symbol_table(members) else {
        return false;
    };
    if table.len() != properties.len() + 1 {
        return false;
    }

    let mut seen_properties = HashSet::with_capacity(properties.len());
    let mut seen_names = HashSet::with_capacity(properties.len());
    for property in properties {
        let Some(property_record) = store.symbol(*property) else {
            return false;
        };
        let Some([declaration]) = property_record.declarations() else {
            return false;
        };
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL;
        let Some(name) = property_record.name().as_utf8() else {
            return false;
        };
        let Some(property_type) = store
            .value_symbol_links(*property)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        if !seen_properties.insert(*property)
            || !seen_names.insert(name.to_owned())
            || !property_record.flags().contains(SymbolFlags::PROPERTY)
            || property_record.flags().without(allowed_flags) != SymbolFlags::NONE
            || property_record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || property_record.name().is_reserved_member_name()
            || property_record.name().is_private_identifier()
            || property_record.name().is_late_bound()
            || property_record.value_declaration() != Some(*declaration)
            || property_record.parent() != Some(owner)
            || property_record.members().is_some()
            || property_record.exports().is_some()
            || property_record.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || !matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
            )
            || store.source_node_parent(*declaration)
                != Some(SourceNodeParent::Parent(owner_declaration))
            || table.get(property_record.name()) != Some(*property)
            || store.value_symbol_links(*property)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                })
            || store.type_payload(property_type).is_none()
        {
            return false;
        }
    }

    let Some(index_symbol) = table.get(InternalSymbolName::Index.as_ref()) else {
        return false;
    };
    let Some(index_record) = store.symbol(index_symbol) else {
        return false;
    };
    let mut seen_infos = HashSet::with_capacity(indexes.len());
    let mut seen_keys = HashSet::with_capacity(indexes.len());
    let mut seen_declarations = HashSet::with_capacity(indexes.len());
    let declarations = indexes
        .iter()
        .map(|id| {
            let info = store.index_info(*id)?;
            let declaration = info.declaration()?;
            if !seen_infos.insert(*id)
                || !seen_keys.insert(info.key_type())
                || !seen_declarations.insert(declaration)
                || info.index_symbol().is_some()
                || !info.components().is_empty()
                || store.type_payload(info.value_type()).is_none()
                || store.source_node_kind(declaration) != Some(SyntaxKind::IndexSignature)
                || store.source_node_parent(declaration)
                    != Some(SourceNodeParent::Parent(owner_declaration))
            {
                return None;
            }
            Some(declaration)
        })
        .collect::<Option<Vec<_>>>();
    declarations.as_deref().is_some_and(|declarations| {
        index_record.flags() == SymbolFlags::SIGNATURE
            && index_record.check_flags() == CheckFlags::NONE
            && index_record.name() == InternalSymbolName::Index.as_ref()
            && index_record.declarations() == Some(declarations)
            && index_record.value_declaration().is_none()
            && index_record.members().is_none()
            && index_record.exports().is_none()
            && index_record.parent() == Some(owner)
            && index_record.export_symbol().is_none()
            && store.get_merged_symbol(index_symbol) == Some(index_symbol)
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::{
        IndexFlags, NongenericKeyofError, NongenericKeyofPlan, NongenericKeyofProof,
        cached_nongeneric_keyof_type, plan_nongeneric_keyof_type,
        plan_nongeneric_keyof_type_with_array_targets, resolve_nongeneric_keyof_leaf,
        resolve_nongeneric_keyof_type, resolve_nongeneric_keyof_type_with_session,
        validate_cached_nongeneric_keyof_result, validate_generic_keyof_index_type,
        validate_source_object_literal_for_keyof,
    };
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
        DeclaredTypeHost, DeclaredTypeLinks, IntrinsicBootstrapOptions, RelationStateSnapshot,
        TypeAliasLinks, TypeId,
        array_types::CanonicalArrayTargets,
        bootstrap::{LiteralTypeCacheError, UnionReduction},
        callable_sets::{
            StoredCallableSetValidation, validate_stored_callable_set_with_array_targets,
        },
        calls::DirectCallForm,
        generic_calls::{
            GenericCallVectorError, GenericCallVectorInvariant, GenericCallVectorRequest,
            demand_generic_call_vector_selected_return,
        },
        generic_method_calls::{GenericMethodCallSelection, resolve_generic_method_call},
        instantiate::{InstantiationError, InstantiationLimits, InstantiationSession},
        instantiated_members::validate_generic_interface_members,
        links::ValueSymbolLinks,
        object_members,
        structured_members::{
            InterfaceHeritageMembersValidation, validate_interface_heritage_members,
        },
        type_records::TypeData,
        types::{ObjectFlags, TypeFlags},
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: CanonicalTypeMapperStore,
    }

    fn fixture(source: &str) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(75_001);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/keyof.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn checked_context(
        parsed: &ParseResult,
        file: FileId,
        language: CanonicalSourceLanguage,
    ) -> CanonicalCheckerContext<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        let path = match language {
            CanonicalSourceLanguage::TypeScript => "\"/keyof-source.ts\"",
            CanonicalSourceLanguage::JavaScript => "\"/keyof-source.js\"",
        };
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    language,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        match language {
            CanonicalSourceLanguage::TypeScript => {
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            CanonicalSourceLanguage::JavaScript => {
                binder
                    .bind_javascript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        context
    }

    fn node_of_kind(fixture: &Fixture, kind: SyntaxKind) -> NodeRef {
        fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == kind).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap_or_else(|| panic!("fixture must contain {kind:?}"))
    }

    fn bound_symbol(fixture: &Fixture, node: NodeRef) -> SemanticSymbolId {
        let bound = fixture.files.get(&fixture.file).unwrap();
        bound
            .symbol(node)
            .or_else(|| bound.local_symbol(node))
            .unwrap()
    }

    fn keyword_type(store: &CanonicalTypeMapperStore, node: NodeRef, recursive: TypeId) -> TypeId {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        match store.source_node_kind(node).unwrap() {
            SyntaxKind::StringKeyword => bootstrap.string_type,
            SyntaxKind::NumberKeyword => bootstrap.number_type,
            SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
            SyntaxKind::TypeReference => recursive,
            kind => panic!("unsupported test annotation {kind:?}"),
        }
    }

    fn resolve_inline_literal(fixture: &mut Fixture) -> TypeId {
        resolve_literal(fixture, None)
    }

    fn resolve_aliased_literal(fixture: &mut Fixture) -> TypeId {
        let alias = node_of_kind(fixture, SyntaxKind::TypeAliasDeclaration);
        let symbol = bound_symbol(fixture, alias);
        resolve_literal(fixture, Some(symbol))
    }

    fn resolve_literal(fixture: &mut Fixture, alias: Option<SemanticSymbolId>) -> TypeId {
        let literal = node_of_kind(fixture, SyntaxKind::TypeLiteral);
        let host = DeclaredTypeHost::new([(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        )])
        .unwrap();
        let mut plan = object_members::plan_concrete_indexed_access_type_literal(
            &fixture.store,
            &host,
            literal,
        )
        .unwrap();
        plan.alias_symbol = alias;
        let property_types = plan
            .property_type_nodes()
            .map(|node| keyword_type(&fixture.store, node, literal_type_sentinel(&fixture.store)))
            .collect::<Vec<_>>();
        let index_types = plan
            .index_type_nodes()
            .map(|(key, value)| {
                (
                    keyword_type(&fixture.store, key, literal_type_sentinel(&fixture.store)),
                    keyword_type(&fixture.store, value, literal_type_sentinel(&fixture.store)),
                )
            })
            .collect::<Vec<_>>();
        let state = object_members::ensure_type_literal_shell(&mut fixture.store, &plan).unwrap();
        let type_ = object_members::publish_declared_members(
            &mut fixture.store,
            &plan,
            state,
            &property_types,
            &index_types,
            &[],
        )
        .unwrap();
        if let Some(alias) = alias {
            assert!(fixture.store.set_type_alias_links(
                alias,
                TypeAliasLinks {
                    declared_type: Some(type_),
                    ..TypeAliasLinks::default()
                },
            ));
        }
        type_
    }

    fn literal_type_sentinel(store: &CanonicalTypeMapperStore) -> TypeId {
        store.intrinsic_bootstrap().unwrap().error_type
    }

    fn resolve_interface(fixture: &mut Fixture) -> TypeId {
        let declaration = node_of_kind(fixture, SyntaxKind::InterfaceDeclaration);
        let symbol = bound_symbol(fixture, declaration);
        let host = DeclaredTypeHost::new([(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        )])
        .unwrap();
        let plan = object_members::plan_interface(&fixture.store, &host, symbol).unwrap();
        let type_ = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        let property_types = plan
            .property_type_nodes()
            .map(|node| keyword_type(&fixture.store, node, type_))
            .collect::<Vec<_>>();
        let state = object_members::interface_state(&fixture.store, &plan, type_).unwrap();
        object_members::publish_declared_members(
            &mut fixture.store,
            &plan,
            state,
            &property_types,
            &[],
            &[],
        )
        .unwrap()
    }

    fn resolve_object_literal(fixture: &mut Fixture, property_types: &[TypeId]) -> TypeId {
        let declaration = node_of_kind(fixture, SyntaxKind::ObjectLiteralExpression);
        let host = DeclaredTypeHost::new([(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        )])
        .unwrap();
        let plan = object_members::plan_object_literal(&fixture.store, &host, declaration).unwrap();
        object_members::publish_object_literal(&mut fixture.store, &plan, property_types).unwrap()
    }

    fn object_literal_forms(fixture: &mut Fixture) -> [TypeId; 3] {
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let property_types = [bootstrap.string_type, bootstrap.undefined_widening_type];
        let fresh = resolve_object_literal(fixture, &property_types);
        let regular = fixture
            .store
            .get_regular_type_of_object_literal(fresh)
            .unwrap();
        let widened = fixture.store.get_widened_type(regular).unwrap();
        assert_ne!(fresh, regular);
        assert_ne!(regular, widened);
        [fresh, regular, widened]
    }

    fn property_symbols(store: &CanonicalTypeMapperStore, object: TypeId) -> Vec<SemanticSymbolId> {
        store
            .type_payload(object)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .properties
            .clone()
            .unwrap_or_default()
    }

    fn resolve_type_parameter(fixture: &mut Fixture) -> TypeId {
        let declaration = node_of_kind(fixture, SyntaxKind::TypeParameter);
        let symbol = bound_symbol(fixture, declaration);
        let host = DeclaredTypeHost::new([(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        )])
        .unwrap();
        fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap()
    }

    fn union_constituents(store: &CanonicalTypeMapperStore, type_: TypeId) -> Vec<TypeId> {
        match store.type_payload(type_).unwrap().data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => vec![type_],
        }
    }

    fn cache_state(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize) {
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        (
            store.type_len(),
            bootstrap.string_literal_cache_len(),
            bootstrap.union_cache_len(),
            store.properties_type_cache_len(),
        )
    }

    #[derive(Debug, Eq, PartialEq)]
    struct KeyofQueryState {
        arenas: [usize; 9],
        caches: (usize, usize, usize, usize),
        links: [usize; 26],
        resolution: (usize, usize, usize, u64),
        relations: RelationStateSnapshot,
    }

    fn query_state(store: &CanonicalTypeMapperStore) -> KeyofQueryState {
        KeyofQueryState {
            arenas: [
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.type_predicate_len(),
                store.index_info_len(),
                store.type_alias_len(),
                store.conditional_root_len(),
                store.entity_name_len(),
                store.symbol_len(),
            ],
            caches: cache_state(store),
            links: store.checker_link_allocated_lengths(),
            resolution: store.type_resolution_internal_state(),
            relations: store.relation_state_snapshot(),
        }
    }

    fn assert_literal_plans_reject_without_writes(
        store: &mut CanonicalTypeMapperStore,
        plans: &[NongenericKeyofPlan],
    ) {
        let before = query_state(store);
        for plan in plans {
            let error = NongenericKeyofError::MalformedObject(plan.target());
            assert_eq!(cached_nongeneric_keyof_type(store, plan), Err(error));
            assert_eq!(resolve_nongeneric_keyof_type(store, plan), Err(error));
            assert_eq!(query_state(store), before);
        }
    }

    #[test]
    fn ordinary_type_parameter_keyof_reuses_one_normalized_index_identity() {
        let mut fixture = fixture("type Keys<T> = keyof T;");
        let parameter = resolve_type_parameter(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, parameter).unwrap();
        assert_eq!(
            cached_nongeneric_keyof_type(&fixture.store, &plan),
            Ok(None)
        );

        let before = cache_state(&fixture.store);
        let cold = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        let record = fixture.store.type_payload(cold).unwrap();
        let TypeData::Index(index) = record.data() else {
            panic!("generic keyof must create an Index type");
        };
        assert_eq!(record.flags(), TypeFlags::INDEX);
        assert_eq!(record.object_flags(), ObjectFlags::NONE);
        assert_eq!(record.symbol(), None);
        assert_eq!(record.alias(), None);
        assert_eq!(index.target, parameter);
        assert_eq!(index.index_flags, IndexFlags::NONE);

        let after_cold = cache_state(&fixture.store);
        assert_eq!(after_cold, (before.0 + 1, before.1, before.2, before.3));
        assert_eq!(
            cached_nongeneric_keyof_type(&fixture.store, &plan),
            Ok(Some(cold))
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
            Ok(cold)
        );
        assert_eq!(cache_state(&fixture.store), after_cold);
    }

    #[test]
    fn generic_keyof_rejects_foreign_parameters_and_malformed_owners() {
        let mut local = fixture("type Keys<T> = keyof T;");
        let parameter = resolve_type_parameter(&mut local);
        let foreign = fixture("type Other<T> = T;");
        assert_eq!(
            plan_nongeneric_keyof_type(&foreign.store, parameter),
            Err(NongenericKeyofError::InvalidType(parameter))
        );

        let orphan = local.store.alloc_type_parameter(None).unwrap();
        assert_eq!(
            plan_nongeneric_keyof_type(&local.store, orphan),
            Err(NongenericKeyofError::MalformedObject(orphan))
        );

        let plan = plan_nongeneric_keyof_type(&local.store, parameter).unwrap();
        assert!(local.store.set_type_symbol(parameter, None));
        assert_eq!(
            cached_nongeneric_keyof_type(&local.store, &plan),
            Err(NongenericKeyofError::MalformedObject(parameter))
        );
    }

    #[test]
    fn generic_keyof_rejects_poisoned_or_duplicate_index_identities() {
        let mut poisoned = fixture("type Keys<T> = keyof T;");
        let parameter = resolve_type_parameter(&mut poisoned);
        let plan = plan_nongeneric_keyof_type(&poisoned.store, parameter).unwrap();
        let cached = resolve_nongeneric_keyof_type(&mut poisoned.store, &plan).unwrap();
        let owner = poisoned.store.type_payload(parameter).unwrap().symbol();
        assert!(poisoned.store.set_type_symbol(cached, owner));
        let before = cache_state(&poisoned.store);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut poisoned.store, &plan),
            Err(NongenericKeyofError::InvalidCachedResult(cached))
        );
        assert_eq!(cache_state(&poisoned.store), before);

        let mut duplicate = fixture("type Keys<T> = keyof T;");
        let parameter = resolve_type_parameter(&mut duplicate);
        let plan = plan_nongeneric_keyof_type(&duplicate.store, parameter).unwrap();
        resolve_nongeneric_keyof_type(&mut duplicate.store, &plan).unwrap();
        let duplicate_index = duplicate
            .store
            .alloc_index_type(parameter, IndexFlags::NONE)
            .unwrap();
        assert_eq!(
            cached_nongeneric_keyof_type(&duplicate.store, &plan),
            Err(NongenericKeyofError::InvalidCachedResult(duplicate_index))
        );
    }

    #[test]
    fn generic_index_proof_keeps_exact_base_constraint_state() {
        let mut fixture = fixture("type Keys<T> = keyof T;");
        let parameter = resolve_type_parameter(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, parameter).unwrap();
        let index = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Ok(parameter)
        );
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let keys = bootstrap.string_number_symbol_type;
        let wrong_constraints = [bootstrap.string_type, bootstrap.unknown_type];

        assert!(
            fixture
                .store
                .set_resolved_base_constraint(index, Some(keys))
        );
        let warm = query_state(&fixture.store);
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Ok(parameter)
        );
        assert_eq!(
            cached_nongeneric_keyof_type(&fixture.store, &plan),
            Ok(Some(index))
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
            Ok(index)
        );
        assert_eq!(query_state(&fixture.store), warm);

        for wrong in wrong_constraints {
            assert!(
                fixture
                    .store
                    .set_resolved_base_constraint(index, Some(wrong))
            );
            let poisoned = query_state(&fixture.store);
            let error = NongenericKeyofError::InvalidCachedResult(index);
            assert_eq!(
                validate_generic_keyof_index_type(&fixture.store, index),
                Err(error)
            );
            assert_eq!(
                cached_nongeneric_keyof_type(&fixture.store, &plan),
                Err(error)
            );
            assert_eq!(
                resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
                Err(error)
            );
            assert_eq!(query_state(&fixture.store), poisoned);
            assert_eq!(
                fixture
                    .store
                    .type_payload(index)
                    .unwrap()
                    .data()
                    .constrained()
                    .unwrap()
                    .resolved_base_constraint,
                Some(wrong),
            );
            assert!(
                fixture
                    .store
                    .set_resolved_base_constraint(index, Some(keys))
            );
            assert_eq!(
                validate_generic_keyof_index_type(&fixture.store, index),
                Ok(parameter)
            );
            assert_eq!(
                resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
                Ok(index)
            );
        }

        let owner = fixture
            .store
            .type_payload(parameter)
            .unwrap()
            .symbol()
            .unwrap();
        assert!(fixture.store.set_type_symbol(index, Some(owner)));
        let poisoned = query_state(&fixture.store);
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Err(NongenericKeyofError::InvalidCachedResult(index)),
        );
        assert_eq!(query_state(&fixture.store), poisoned);
        assert!(fixture.store.set_type_symbol(index, None));
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Ok(parameter)
        );

        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let wrong_target = fixture
            .store
            .alloc_index_type(string, IndexFlags::NONE)
            .unwrap();
        let wrong_flags = fixture
            .store
            .alloc_index_type(parameter, IndexFlags::STRINGS_ONLY)
            .unwrap();
        let before = query_state(&fixture.store);
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, wrong_target),
            Err(NongenericKeyofError::MalformedObject(string)),
        );
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, wrong_flags),
            Err(NongenericKeyofError::InvalidCachedResult(wrong_flags)),
        );
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Ok(parameter)
        );
        assert_eq!(query_state(&fixture.store), before);
    }

    #[test]
    fn generic_index_proof_requires_retained_source_parameter_ownership() {
        let mut fixture = fixture("type Keys<T, Other> = keyof T;");
        let parameter = resolve_type_parameter(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, parameter).unwrap();
        let index = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        let owner = fixture
            .store
            .type_payload(parameter)
            .unwrap()
            .symbol()
            .unwrap();
        let original = fixture
            .store
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        let other = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let declaration = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
                (record.kind == SyntaxKind::TypeParameter && !original.contains(&declaration))
                    .then_some(declaration)
            })
            .unwrap();
        assert!(
            fixture
                .store
                .set_symbol_declarations(owner, Some(vec![other]), None)
        );
        let poisoned = query_state(&fixture.store);
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Err(NongenericKeyofError::MalformedObject(parameter)),
        );
        assert_eq!(query_state(&fixture.store), poisoned);
        assert!(
            fixture
                .store
                .set_symbol_declarations(owner, Some(original.clone()), None)
        );
        let restored = query_state(&fixture.store);
        assert_eq!(
            validate_generic_keyof_index_type(&fixture.store, index),
            Ok(parameter)
        );
        assert_eq!(query_state(&fixture.store), restored);

        let detached_owner = fixture
            .store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_PARAMETER,
                EscapedName::source("Detached"),
            ))
            .unwrap();
        let detached = fixture
            .store
            .alloc_type_parameter(Some(detached_owner))
            .unwrap();
        assert!(fixture.store.set_declared_type_links(
            detached_owner,
            DeclaredTypeLinks {
                declared_type: Some(detached),
                ..DeclaredTypeLinks::default()
            }
        ));
        let detached_plan = plan_nongeneric_keyof_type(&fixture.store, detached).unwrap();
        let detached_index =
            resolve_nongeneric_keyof_type(&mut fixture.store, &detached_plan).unwrap();
        for declarations in [None, Some(original)] {
            assert!(
                fixture
                    .store
                    .set_symbol_declarations(detached_owner, declarations, None)
            );
            let before = query_state(&fixture.store);
            assert_eq!(
                validate_generic_keyof_index_type(&fixture.store, detached_index),
                Err(NongenericKeyofError::MalformedObject(detached)),
            );
            assert_eq!(
                cached_nongeneric_keyof_type(&fixture.store, &detached_plan),
                Ok(Some(detached_index))
            );
            assert_eq!(query_state(&fixture.store), before);
        }
    }

    #[test]
    fn object_literal_keys_keep_fresh_regular_and_widened_source_proofs() {
        let mut fixture = fixture("const value = { a: 'a', b: undefined };");
        let [fresh, regular, widened] = object_literal_forms(&mut fixture);
        let owner = fixture.store.type_payload(fresh).unwrap().symbol().unwrap();
        let proofs = [
            NongenericKeyofProof::FreshObjectLiteral { owner },
            NongenericKeyofProof::DerivedObjectLiteral {
                owner,
                source: fresh,
            },
            NongenericKeyofProof::DerivedObjectLiteral {
                owner,
                source: regular,
            },
        ];
        let mut expected = None;
        for (object, proof) in [fresh, regular, widened].into_iter().zip(proofs) {
            let before = query_state(&fixture.store);
            let plan = plan_nongeneric_keyof_type(&fixture.store, object).unwrap();
            assert_eq!(plan.proof(), proof);
            assert_eq!(
                validate_source_object_literal_for_keyof(&fixture.store, object, None),
                Ok(true)
            );
            assert_ne!(
                plan.proof(),
                object_members::DeclaredPropertyObjectProof::TypeLiteral
            );
            assert_eq!(plan.property_names(), ["a", "b"]);
            assert!(!plan.preserves_origin());
            assert!(!plan.retains_index_origin());
            assert_eq!(
                cached_nongeneric_keyof_type(&fixture.store, &plan),
                Ok(None)
            );
            assert_eq!(query_state(&fixture.store), before);

            let result = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
            assert_eq!(*expected.get_or_insert(result), result);
            let TypeData::Union(union) = fixture.store.type_payload(result).unwrap().data() else {
                panic!("the two object properties must produce a key union");
            };
            assert_eq!(union.origin, None);
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let mut keys = vec![
                bootstrap.cached_string_literal_type("a").unwrap(),
                bootstrap.cached_string_literal_type("b").unwrap(),
            ];
            keys.sort_unstable();
            assert_eq!(union.union.types, keys);

            let warm = query_state(&fixture.store);
            assert_eq!(
                cached_nongeneric_keyof_type(&fixture.store, &plan),
                Ok(Some(result))
            );
            assert_eq!(
                resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
                Ok(result)
            );
            assert_eq!(plan_nongeneric_keyof_type(&fixture.store, object), Ok(plan));
            assert_eq!(query_state(&fixture.store), warm);
        }
    }

    #[test]
    fn object_literal_key_plans_reject_changed_property_links_and_owners() {
        for warm in [false, true] {
            let mut fixture = fixture("const value = { a: 'a', b: undefined };");
            let objects = object_literal_forms(&mut fixture);
            let plans =
                objects.map(|object| plan_nongeneric_keyof_type(&fixture.store, object).unwrap());
            let expected = if warm {
                Some(resolve_nongeneric_keyof_type(&mut fixture.store, &plans[0]).unwrap())
            } else {
                None
            };
            if warm {
                for plan in &plans[1..] {
                    assert_eq!(
                        resolve_nongeneric_keyof_type(&mut fixture.store, plan),
                        Ok(expected.unwrap())
                    );
                }
            }
            let properties = property_symbols(&fixture.store, objects[0]);
            let property = properties[0];
            let original = fixture.store.value_symbol_links(property).unwrap().clone();
            let other_source = fixture
                .store
                .value_symbol_links(properties[1])
                .unwrap()
                .target;
            let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
            for poisoned in [
                ValueSymbolLinks {
                    target: other_source,
                    ..original.clone()
                },
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..original.clone()
                },
            ] {
                assert!(
                    fixture
                        .store
                        .set_value_symbol_links(property, poisoned.clone())
                );
                assert_literal_plans_reject_without_writes(&mut fixture.store, &plans);
                assert_eq!(fixture.store.value_symbol_links(property), Some(&poisoned));
                assert!(
                    fixture
                        .store
                        .set_value_symbol_links(property, original.clone())
                );
                let restored = query_state(&fixture.store);
                for plan in &plans {
                    assert_eq!(
                        cached_nongeneric_keyof_type(&fixture.store, plan),
                        Ok(expected)
                    );
                }
                assert_eq!(query_state(&fixture.store), restored);
            }

            let owner = fixture.store.symbol(property).unwrap().parent();
            assert!(fixture.store.set_symbol_relationships(
                property,
                None,
                None,
                Some(properties[1]),
                None
            ));
            assert_literal_plans_reject_without_writes(&mut fixture.store, &plans);
            assert_eq!(
                fixture.store.symbol(property).unwrap().parent(),
                Some(properties[1])
            );
            assert!(
                fixture
                    .store
                    .set_symbol_relationships(property, None, None, owner, None)
            );

            let object_owner = fixture
                .store
                .type_payload(objects[0])
                .unwrap()
                .symbol()
                .unwrap();
            let members = fixture.store.symbol(object_owner).unwrap().members();
            assert!(fixture.store.set_symbol_relationships(
                object_owner,
                members,
                members,
                None,
                None
            ));
            let poisoned = query_state(&fixture.store);
            for object in objects {
                assert_eq!(
                    validate_source_object_literal_for_keyof(&fixture.store, object, None),
                    Err(NongenericKeyofError::MalformedObject(object)),
                );
            }
            assert_literal_plans_reject_without_writes(&mut fixture.store, &plans);
            assert_eq!(query_state(&fixture.store), poisoned);
            assert!(fixture.store.set_symbol_relationships(
                object_owner,
                members,
                None,
                None,
                None
            ));

            for plan in &plans {
                let result = resolve_nongeneric_keyof_type(&mut fixture.store, plan).unwrap();
                let restored = query_state(&fixture.store);
                assert_eq!(
                    cached_nongeneric_keyof_type(&fixture.store, plan),
                    Ok(Some(result))
                );
                assert_eq!(
                    resolve_nongeneric_keyof_type(&mut fixture.store, plan),
                    Ok(result)
                );
                assert_eq!(query_state(&fixture.store), restored);
            }
        }
    }

    #[test]
    fn object_literal_key_cache_rejects_changed_results_and_foreign_origins() {
        let mut fixture = fixture(concat!(
            "interface Named { a: string; b: string } ",
            "const value = { a: 'a', b: undefined };",
        ));
        let [fresh, _, _] = object_literal_forms(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, fresh).unwrap();
        let result = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        let named = resolve_interface(&mut fixture);
        let named_plan = plan_nongeneric_keyof_type(&fixture.store, named).unwrap();
        let named_result = resolve_nongeneric_keyof_type(&mut fixture.store, &named_plan).unwrap();
        assert_ne!(named_result, result);
        assert_eq!(
            union_constituents(&fixture.store, named_result),
            union_constituents(&fixture.store, result)
        );
        let one_key = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_string_literal_type("a")
            .unwrap();
        let before = query_state(&fixture.store);
        for wrong in [named_result, one_key] {
            assert_eq!(
                validate_cached_nongeneric_keyof_result(&fixture.store, &plan, wrong),
                Err(NongenericKeyofError::InvalidCachedResult(wrong)),
            );
            assert_eq!(query_state(&fixture.store), before);
        }

        let owner = fixture.store.type_payload(fresh).unwrap().symbol();
        assert!(fixture.store.set_type_symbol(result, owner));
        let poisoned = query_state(&fixture.store);
        assert_eq!(
            cached_nongeneric_keyof_type(&fixture.store, &plan),
            Err(NongenericKeyofError::InvalidCachedResult(result))
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
            Err(NongenericKeyofError::InvalidCachedResult(result))
        );
        assert_eq!(query_state(&fixture.store), poisoned);
        assert_eq!(fixture.store.type_payload(result).unwrap().symbol(), owner);
        assert!(fixture.store.set_type_symbol(result, None));
        let restored = query_state(&fixture.store);
        assert_eq!(
            cached_nongeneric_keyof_type(&fixture.store, &plan),
            Ok(Some(result))
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan),
            Ok(result)
        );
        assert_eq!(query_state(&fixture.store), restored);
    }

    #[test]
    fn object_literal_key_proofs_reject_changed_retained_declarations() {
        for warm in [false, true] {
            let mut fixture = fixture(concat!(
                "const value = { a: 'a', b: undefined }; ",
                "const other = { a: 'a', b: undefined };",
            ));
            let objects = object_literal_forms(&mut fixture);
            let union = fixture
                .store
                .literal_union_type(&objects[..2], None)
                .unwrap();
            let plans = objects
                .into_iter()
                .chain([union])
                .map(|object| plan_nongeneric_keyof_type(&fixture.store, object).unwrap())
                .collect::<Vec<_>>();
            if warm {
                for plan in &plans {
                    resolve_nongeneric_keyof_type(&mut fixture.store, plan).unwrap();
                }
            }
            let owner = fixture
                .store
                .type_payload(objects[0])
                .unwrap()
                .symbol()
                .unwrap();
            let original = fixture.store.symbol(owner).unwrap().declarations().unwrap()[0];
            let other = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let declaration = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
                    (record.kind == SyntaxKind::ObjectLiteralExpression && declaration != original)
                        .then_some(declaration)
                })
                .unwrap();
            assert!(
                fixture
                    .store
                    .set_symbol_declarations(owner, Some(vec![other]), Some(other))
            );
            let poisoned = query_state(&fixture.store);
            for object in objects {
                assert_eq!(
                    validate_source_object_literal_for_keyof(&fixture.store, object, None),
                    Err(NongenericKeyofError::MalformedObject(object)),
                );
            }
            for plan in &plans {
                let target = if plan.target() == union {
                    objects[0]
                } else {
                    plan.target()
                };
                let error = NongenericKeyofError::MalformedObject(target);
                assert_eq!(
                    cached_nongeneric_keyof_type(&fixture.store, plan),
                    Err(error)
                );
                assert_eq!(
                    resolve_nongeneric_keyof_type(&mut fixture.store, plan),
                    Err(error)
                );
            }
            assert_eq!(query_state(&fixture.store), poisoned);
            assert!(fixture.store.set_symbol_declarations(
                owner,
                Some(vec![original]),
                Some(original)
            ));

            let fresh_property = property_symbols(&fixture.store, objects[0])[0];
            let raw_property = fixture
                .store
                .value_symbol_links(fresh_property)
                .unwrap()
                .target
                .unwrap();
            let original_property = fixture
                .store
                .symbol(raw_property)
                .unwrap()
                .declarations()
                .unwrap()[0];
            let other_property = fixture
                .store
                .source_direct_children(other)
                .unwrap()
                .into_iter()
                .find(|node| {
                    fixture.store.source_node_kind(*node) == Some(SyntaxKind::PropertyAssignment)
                })
                .unwrap();
            for property in [raw_property, fresh_property] {
                assert!(fixture.store.set_symbol_declarations(
                    property,
                    Some(vec![other_property]),
                    Some(other_property)
                ));
            }
            let poisoned = query_state(&fixture.store);
            for object in objects {
                assert_eq!(
                    validate_source_object_literal_for_keyof(&fixture.store, object, None),
                    Err(NongenericKeyofError::MalformedObject(object)),
                );
            }
            for plan in &plans {
                let target = if plan.target() == union {
                    objects[0]
                } else {
                    plan.target()
                };
                let error = NongenericKeyofError::MalformedObject(target);
                assert_eq!(
                    cached_nongeneric_keyof_type(&fixture.store, plan),
                    Err(error)
                );
                assert_eq!(
                    resolve_nongeneric_keyof_type(&mut fixture.store, plan),
                    Err(error)
                );
            }
            assert_eq!(query_state(&fixture.store), poisoned);
            for property in [raw_property, fresh_property] {
                assert!(fixture.store.set_symbol_declarations(
                    property,
                    Some(vec![original_property]),
                    Some(original_property)
                ));
            }
            let original_links = fixture.store.type_node_links(original).unwrap().clone();
            let wrong = fixture.store.intrinsic_bootstrap().unwrap().any_type;
            assert!(fixture.store.set_type_node_links(
                original,
                super::TypeNodeLinks {
                    resolved_type: Some(wrong),
                    ..original_links.clone()
                }
            ));
            let poisoned = query_state(&fixture.store);
            for object in objects {
                assert_eq!(
                    validate_source_object_literal_for_keyof(&fixture.store, object, None),
                    Err(NongenericKeyofError::MalformedObject(object)),
                );
            }
            for plan in &plans {
                let target = if plan.target() == union {
                    objects[0]
                } else {
                    plan.target()
                };
                let error = NongenericKeyofError::MalformedObject(target);
                assert_eq!(
                    cached_nongeneric_keyof_type(&fixture.store, plan),
                    Err(error)
                );
                assert_eq!(
                    resolve_nongeneric_keyof_type(&mut fixture.store, plan),
                    Err(error)
                );
            }
            assert_eq!(query_state(&fixture.store), poisoned);
            assert_eq!(
                fixture
                    .store
                    .type_node_links(original)
                    .unwrap()
                    .resolved_type,
                Some(wrong)
            );
            assert!(fixture.store.set_type_node_links(original, original_links));
            for plan in &plans {
                let result = resolve_nongeneric_keyof_type(&mut fixture.store, plan).unwrap();
                let restored = query_state(&fixture.store);
                assert_eq!(
                    cached_nongeneric_keyof_type(&fixture.store, plan),
                    Ok(Some(result))
                );
                assert_eq!(query_state(&fixture.store), restored);
            }
        }
    }

    #[test]
    fn source_object_identity_does_not_require_identifier_keys() {
        let mut fixture = fixture("const value = { '0': 1 };");
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let object = resolve_object_literal(&mut fixture, &[number]);
        let property = property_symbols(&fixture.store, object)[0];
        let before = query_state(&fixture.store);
        assert_eq!(
            validate_source_object_literal_for_keyof(&fixture.store, object, None),
            Ok(true)
        );
        assert_eq!(
            validate_source_object_literal_for_keyof(&fixture.store, number, None),
            Ok(false)
        );
        assert_eq!(
            plan_nongeneric_keyof_type(&fixture.store, object),
            Err(NongenericKeyofError::UnsupportedPropertyName {
                target: object,
                property
            }),
        );
        assert_eq!(query_state(&fixture.store), before);
    }

    #[test]
    fn javascript_expando_object_is_not_a_fresh_literal_key_candidate() {
        let parsed = parse_javascript_source_file("var object = {}; object['if'] = 1;");
        let file = FileId::new(75_003);
        let context = checked_context(&parsed, file, CanonicalSourceLanguage::JavaScript);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ObjectLiteralExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let object = context
            .store()
            .type_node_links(declaration)
            .unwrap()
            .resolved_type
            .unwrap();
        let record = context.store().type_payload(object).unwrap();
        let owner = context.store().symbol(record.symbol().unwrap()).unwrap();
        assert!(owner.exports().is_some());
        assert_eq!(
            record.object_flags(),
            ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        );
        let before = query_state(context.store());
        assert_eq!(
            validate_source_object_literal_for_keyof(context.store(), object, None),
            Ok(false)
        );
        assert_eq!(
            plan_nongeneric_keyof_type(context.store(), object),
            Err(NongenericKeyofError::UnsupportedObject(object))
        );
        assert_eq!(query_state(context.store()), before);
    }

    #[test]
    fn object_literal_key_plan_retains_array_targets_for_cold_and_warm_queries() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "const value: any = { items: [{ missing: undefined }], a: 'a' };",
        ));
        let file = FileId::new(75_002);
        let mut context = checked_context(&parsed, file, CanonicalSourceLanguage::TypeScript);
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                variable
                    .initializer
                    .map(|node| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let fresh = context
            .store()
            .type_node_links(initializer)
            .unwrap()
            .resolved_type
            .unwrap();
        let source_array = context
            .store()
            .value_symbol_links(property_symbols(context.store(), fresh)[0])
            .unwrap()
            .resolved_type
            .unwrap();
        let global_types = context.global_types().clone();
        let array = context
            .store()
            .canonical_array_reference(&global_types, source_array)
            .unwrap()
            .unwrap();
        assert!(array.array_literal);
        let regular = context
            .store_mut_for_test()
            .get_regular_type_of_object_literal(fresh)
            .unwrap();
        let widened = context
            .store_mut_for_test()
            .get_widened_type_with_global_types(regular, &global_types)
            .unwrap();
        let targets = CanonicalArrayTargets::from_global_types(&global_types);
        let before = query_state(context.store());
        assert_eq!(
            plan_nongeneric_keyof_type(context.store(), widened),
            Err(NongenericKeyofError::MalformedObject(widened)),
        );
        let plan =
            plan_nongeneric_keyof_type_with_array_targets(context.store(), widened, Some(targets))
                .unwrap();
        assert_eq!(plan.array_targets, Some(targets));
        assert_eq!(plan.property_names(), ["items", "a"]);
        assert_eq!(
            cached_nongeneric_keyof_type(context.store(), &plan),
            Ok(None)
        );
        assert_eq!(query_state(context.store()), before);

        let result = resolve_nongeneric_keyof_type(context.store_mut_for_test(), &plan).unwrap();
        let warm = query_state(context.store());
        assert_eq!(
            cached_nongeneric_keyof_type(context.store(), &plan),
            Ok(Some(result))
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(context.store_mut_for_test(), &plan),
            Ok(result)
        );
        assert_eq!(query_state(context.store()), warm);
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        let wrong_targets = CanonicalArrayTargets::for_test(wrong, targets.readonly_array_type());
        assert_eq!(
            plan_nongeneric_keyof_type_with_array_targets(
                context.store(),
                widened,
                Some(wrong_targets)
            ),
            Err(NongenericKeyofError::MalformedObject(widened)),
        );
        assert_eq!(query_state(context.store()), warm);

        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .array_literal_types
                .insert(array.base_type, wrong),
            Some(source_array),
        );
        let poisoned = query_state(context.store());
        let error = NongenericKeyofError::MalformedObject(widened);
        assert_eq!(
            cached_nongeneric_keyof_type(context.store(), &plan),
            Err(error)
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(context.store_mut_for_test(), &plan),
            Err(error)
        );
        assert_eq!(query_state(context.store()), poisoned);
        assert_eq!(
            context
                .store()
                .derived_types
                .array_literal_types
                .get(&array.base_type),
            Some(&wrong)
        );
        assert_eq!(
            context
                .store_mut_for_test()
                .derived_types
                .array_literal_types
                .insert(array.base_type, source_array),
            Some(wrong),
        );
        let restored = query_state(context.store());
        assert_eq!(
            cached_nongeneric_keyof_type(context.store(), &plan),
            Ok(Some(result))
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(context.store_mut_for_test(), &plan),
            Ok(result)
        );
        assert_eq!(query_state(context.store()), restored);
    }

    #[test]
    fn anonymous_property_keys_are_canonical_and_warm_is_allocation_free() {
        let mut fixture = fixture("type Keys = keyof { alpha: string; beta: number };");
        let object = resolve_inline_literal(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, object).unwrap();
        assert_eq!(plan.property_names(), ["alpha", "beta"]);
        assert!(!plan.preserves_origin());

        let cold = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        let after_cold = cache_state(&fixture.store);
        let warm = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        assert_eq!(warm, cold);
        assert_eq!(cache_state(&fixture.store), after_cold);

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(union_constituents(&fixture.store, cold), {
            let mut keys = vec![
                bootstrap.cached_string_literal_type("alpha").unwrap(),
                bootstrap.cached_string_literal_type("beta").unwrap(),
            ];
            keys.sort_unstable();
            keys
        });
    }

    #[test]
    fn index_precedence_matches_pinned_keyof_reduction() {
        let mut number = fixture("type Keys = keyof { named: string; [key: number]: number };");
        let number_object = resolve_inline_literal(&mut number);
        let number_plan = plan_nongeneric_keyof_type(&number.store, number_object).unwrap();
        assert!(!number_plan.has_string_index());
        assert!(number_plan.has_number_index());
        let number_result = resolve_nongeneric_keyof_type(&mut number.store, &number_plan).unwrap();
        let bootstrap = number.store.intrinsic_bootstrap().unwrap();
        let mut expected = vec![
            bootstrap.number_type,
            bootstrap.cached_string_literal_type("named").unwrap(),
        ];
        expected.sort_unstable();
        assert_eq!(union_constituents(&number.store, number_result), expected);

        let mut string = fixture("type Keys = keyof { named: string; [key: string]: string };");
        let string_object = resolve_inline_literal(&mut string);
        let string_plan = plan_nongeneric_keyof_type(&string.store, string_object).unwrap();
        assert!(string_plan.has_string_index());
        let string_result = resolve_nongeneric_keyof_type(&mut string.store, &string_plan).unwrap();
        let string_warm_state = cache_state(&string.store);
        assert_eq!(
            string_result,
            string
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
        assert!(
            string
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("named")
                .is_some(),
            "pinned property-literal evaluation precedes string-index absorption"
        );
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut string.store, &string_plan).unwrap(),
            string_result
        );
        assert_eq!(cache_state(&string.store), string_warm_state);

        let mut paired =
            fixture("type Keys = keyof { [text: string]: string; [position: number]: string };");
        let paired_object = resolve_inline_literal(&mut paired);
        let paired_plan = plan_nongeneric_keyof_type(&paired.store, paired_object).unwrap();
        assert!(paired_plan.has_string_index());
        assert!(paired_plan.has_number_index());
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut paired.store, &paired_plan).unwrap(),
            paired
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
    }

    #[test]
    fn named_multi_key_plan_stops_before_global_cache_mutation() {
        let mut fixture = fixture("interface Model { first: string; second: number }");
        let interface = resolve_interface(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, interface).unwrap();
        assert!(plan.preserves_origin());
        assert!(plan.root_cache_required());
        assert!(plan.retains_index_origin());
        let before = cache_state(&fixture.store);
        assert_eq!(
            resolve_nongeneric_keyof_leaf(&mut fixture.store, &plan),
            Err(NongenericKeyofError::PropertiesCacheRequired {
                target: interface,
                raw_contribution_count: 2,
                reduced_key_count: 2,
                retains_index_origin: true,
            })
        );
        assert_eq!(cache_state(&fixture.store), before);

        let cold = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        let after_cold = cache_state(&fixture.store);
        assert_eq!(after_cold.0, before.0 + 6);
        assert_eq!(after_cold.1, before.1 + 2);
        assert_eq!(after_cold.2, before.2 + 1);
        assert_eq!(after_cold.3, before.3 + 1);
        let TypeData::Union(union) = fixture.store.type_payload(cold).unwrap().data() else {
            panic!("two named property keys must produce an index-origin union");
        };
        let origin = union.origin.expect("named keyof union keeps Index origin");
        let TypeData::Index(index) = fixture.store.type_payload(origin).unwrap().data() else {
            panic!("named keyof origin must be an Index shell");
        };
        assert_eq!(index.target, interface);
        assert_eq!(index.index_flags, IndexFlags::NONE);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap(),
            cold,
        );
        assert_eq!(cache_state(&fixture.store), after_cold);
    }

    #[test]
    fn named_string_index_uses_raw_contribution_count_for_origin_boundary() {
        let mut index_only = fixture("type Table = { [key: string]: string };");
        let table = resolve_aliased_literal(&mut index_only);
        let plan = plan_nongeneric_keyof_type(&index_only.store, table).unwrap();
        assert!(plan.preserves_origin());
        assert_eq!(plan.raw_contribution_count(), 1);
        assert_eq!(plan.reduced_key_count(), 2);
        assert!(plan.root_cache_required());
        assert!(!plan.retains_index_origin());
        let before = cache_state(&index_only.store);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut index_only.store, &plan).unwrap(),
            index_only
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
        let after_cold = cache_state(&index_only.store);
        assert_eq!(after_cold.0, before.0 + 1);
        assert_eq!(after_cold.1, before.1);
        assert_eq!(after_cold.2, before.2);
        assert_eq!(after_cold.3, before.3 + 1);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut index_only.store, &plan).unwrap(),
            index_only
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_or_number_type
        );
        assert_eq!(cache_state(&index_only.store), after_cold);

        let mut mixed = fixture("type Table = { named: string; [key: string]: string };");
        let table = resolve_aliased_literal(&mut mixed);
        let plan = plan_nongeneric_keyof_type(&mixed.store, table).unwrap();
        assert_eq!(plan.raw_contribution_count(), 2);
        assert_eq!(plan.reduced_key_count(), 2);
        let before = cache_state(&mixed.store);
        assert_eq!(
            resolve_nongeneric_keyof_leaf(&mut mixed.store, &plan),
            Err(NongenericKeyofError::PropertiesCacheRequired {
                target: table,
                raw_contribution_count: 2,
                reduced_key_count: 2,
                retains_index_origin: true,
            })
        );
        assert_eq!(cache_state(&mixed.store), before);
    }

    #[test]
    fn named_single_key_and_recursive_value_cycle_do_not_need_origin_union() {
        let mut fixture = fixture("interface Node { next: Node }");
        let interface = resolve_interface(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, interface).unwrap();
        assert_eq!(plan.property_names(), ["next"]);
        let before = cache_state(&fixture.store);
        let result = resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap();
        assert_eq!(
            result,
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("next")
                .unwrap()
        );
        let after_cold = cache_state(&fixture.store);
        assert_eq!(after_cold.0, before.0 + 3);
        assert_eq!(after_cold.1, before.1 + 1);
        assert_eq!(after_cold.2, before.2);
        assert_eq!(after_cold.3, before.3 + 1);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap(),
            result,
        );
        assert_eq!(cache_state(&fixture.store), after_cold);
    }

    #[test]
    fn duplicate_and_poisoned_member_surfaces_fail_closed() {
        let mut duplicate = fixture("type Keys = keyof { left: string; right: number };");
        let object = resolve_inline_literal(&mut duplicate);
        let (members, property, indexes) = {
            let structured = duplicate
                .store
                .type_payload(object)
                .and_then(|record| record.data().structured())
                .unwrap();
            (
                structured.members,
                structured.properties.as_ref().unwrap()[0],
                structured.index_infos.clone(),
            )
        };
        assert!(duplicate.store.set_structured_type_members(
            object,
            members,
            Some(vec![property, property]),
            None,
            None,
            indexes,
        ));
        assert_eq!(
            plan_nongeneric_keyof_type(&duplicate.store, object),
            Err(NongenericKeyofError::MalformedObject(object))
        );

        let mut poisoned = fixture("type Keys = keyof { named: string; [key: number]: number };");
        let indexed_object_type = resolve_inline_literal(&mut poisoned);
        let (members, properties, index) = {
            let structured = poisoned
                .store
                .type_payload(indexed_object_type)
                .and_then(|record| record.data().structured())
                .unwrap();
            (
                structured.members,
                structured.properties.clone(),
                structured.index_infos.as_ref().unwrap()[0],
            )
        };
        assert!(poisoned.store.set_structured_type_members(
            indexed_object_type,
            members,
            properties,
            None,
            None,
            Some(vec![index, index]),
        ));
        assert_eq!(
            plan_nongeneric_keyof_type(&poisoned.store, indexed_object_type),
            Err(NongenericKeyofError::MalformedObject(indexed_object_type))
        );
    }

    #[test]
    fn foreign_and_composite_targets_are_explicit_boundaries() {
        let mut first = fixture("type Keys = keyof { local: string };");
        let local = resolve_inline_literal(&mut first);
        let second = fixture("type Other = string;");
        assert_eq!(
            plan_nongeneric_keyof_type(&second.store, local),
            Err(NongenericKeyofError::InvalidType(local))
        );

        let string = first.store.intrinsic_bootstrap().unwrap().string_type;
        let number = first.store.intrinsic_bootstrap().unwrap().number_type;
        let union = first
            .store
            .alloc_union_type(
                crate::semantic::types::ObjectFlags::PRIMITIVE_UNION,
                vec![string, number],
            )
            .unwrap();
        assert_eq!(
            plan_nongeneric_keyof_type(&first.store, union),
            Err(NongenericKeyofError::UnsupportedObject(union))
        );
    }

    #[test]
    fn empty_anonymous_literal_reuses_never() {
        let mut fixture = fixture("type Keys = keyof {};");
        let object = resolve_inline_literal(&mut fixture);
        let plan = plan_nongeneric_keyof_type(&fixture.store, object).unwrap();
        assert_eq!(plan.reduced_key_count(), 0);
        assert_eq!(
            resolve_nongeneric_keyof_type(&mut fixture.store, &plan).unwrap(),
            fixture.store.intrinsic_bootstrap().unwrap().never_type
        );
    }

    fn keyof_session_interface(store: &CanonicalTypeMapperStore, name: &str) -> TypeId {
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

    fn keyof_session_cache_state(store: &CanonicalTypeMapperStore) -> [usize; 8] {
        let (types, strings, unions, keys) = cache_state(store);
        [
            types,
            strings,
            unions,
            keys,
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.cached_signature_len(),
        ]
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum KeyofSessionControl {
        FailFastDirtyCache,
        RecoveringDirtyCache,
        RecoveringColdReturn,
    }

    #[allow(clippy::too_many_lines)] // One source graph checks selection, nested mapping, and cache replay.
    fn assert_keyof_selected_return_uses_caller(nested: bool, control: KeyofSessionControl) {
        const LIBRARY: FileId = FileId::new(163_150);
        const SOURCE: FileId = FileId::new(163_151);
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: number; }",
        ));
        let returned = if nested { "Array<keyof T>" } else { "keyof T" };
        let parsed = parse_source_file(&format!(
            "interface Derived extends Base<number> {{}} \
             interface Plain {{ value: number; }} \
             interface Payload {{ firstKey: number; secondKey: string; }} \
             interface Methods {{ m<T>(value: T): {returned}; \
             m(a: number, b: number): number; }}",
        ));
        let mut binder = CanonicalBinder::new();
        for (file, source, declaration, path) in [
            (LIBRARY, &library, true, "\"/keyof-session-library.d.ts\""),
            (SOURCE, &parsed, false, "\"/keyof-session.ts\""),
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
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(LIBRARY, &library.arena), (SOURCE, &parsed.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), SOURCE, node),
                    NodeRef::new(parsed.arena.id(), SOURCE, method.name),
                ))
            })
            .unwrap();
        let callee = context.get_type_at_location(name).unwrap();
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set_with_array_targets(context.store(), callee, Some(targets))
        else {
            panic!("the real method group must retain its signatures")
        };
        assert_eq!(projection.call_signatures.len(), 2);
        let original = projection.call_signatures[0].signature;
        assert_eq!(
            context.store().signature(original).unwrap().declaration(),
            Some(declaration)
        );
        let template = context
            .store()
            .signature(original)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let index_template = if nested {
            context
                .store()
                .canonical_array_reference_with_targets(targets, template)
                .unwrap()
                .unwrap()
                .element_type
        } else {
            template
        };
        assert_eq!(
            validate_generic_keyof_index_type(context.store(), index_template),
            Ok(context
                .store()
                .signature(original)
                .unwrap()
                .type_parameters()[0])
        );
        let derived = keyof_session_interface(context.store(), "Derived");
        let plain = keyof_session_interface(context.store(), "Plain");
        let payload = keyof_session_interface(context.store(), "Payload");
        let TypeData::Interface(data) = context.store().type_payload(derived).unwrap().data()
        else {
            panic!("Derived must retain its source interface")
        };
        let base = data.resolved_base_types.as_ref().unwrap()[0];
        let proxy = context
            .store()
            .symbol_table(data.reference.object.structured.members.unwrap())
            .and_then(|members| members.get_source("value"))
            .unwrap();
        let store = context.store_mut_for_test();
        let key_plan =
            plan_nongeneric_keyof_type_with_array_targets(store, payload, Some(targets)).unwrap();
        assert!(key_plan.preserves_origin());
        assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let error = store.intrinsic_bootstrap().unwrap().error_type;
        let dirty_result = if control == KeyofSessionControl::RecoveringColdReturn {
            None
        } else {
            let mut setup = InstantiationSession::new(InstantiationLimits::default());
            let source_union = store
                .expression_union_type_with_global_types_and_session(
                    &globals,
                    &[number, derived],
                    UnionReduction::Literal,
                    &mut setup,
                )
                .unwrap();
            let rows = store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len();
            let result = store
                .expression_union_type_with_global_types_and_session(
                    &globals,
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
            let original_links = store.value_symbol_links(proxy).unwrap().clone();
            assert_eq!(original_links.resolved_type, Some(number));
            assert!(store.instantiated_property_recovery(proxy).is_none());
            // Restore only the pre-query lazy value, before any recovery receipt exists.
            assert!(store.set_value_symbol_links(
                proxy,
                ValueSymbolLinks {
                    resolved_type: None,
                    ..original_links
                }
            ));
            store.mark_union_cache_validation_dirty();
            Some(result)
        };
        let original_links = store.value_symbol_links(proxy).unwrap().clone();
        assert!(store.instantiated_property_recovery(proxy).is_none());
        assert_eq!(
            validate_interface_heritage_members(store, derived),
            InterfaceHeritageMembersValidation::Valid
        );
        assert!(
            validate_generic_interface_members(store, base, None)
                .unwrap()
                .is_some()
        );
        let arguments = [payload];
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: Some(&arguments),
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let limit = if control == KeyofSessionControl::RecoveringColdReturn {
            1
        } else {
            3 + usize::from(nested)
        };
        let limits = InstantiationLimits {
            max_count: limit,
            ..InstantiationLimits::default()
        };
        let mut limited = if control == KeyofSessionControl::FailFastDirtyCache {
            InstantiationSession::new(limits)
        } else {
            InstantiationSession::new_recovering(store, limits, error).unwrap()
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
        assert_eq!(store.signature(signature).unwrap().target(), Some(original));
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
        assert_eq!(limited.limit_event_count(), 0);
        let before = keyof_session_cache_state(store);
        let scans = store.union_cache_validation_scan_count();
        let first = demand_generic_call_vector_selected_return(store, generic, &mut limited)
            .map(|(returned, _)| returned);
        match control {
            KeyofSessionControl::FailFastDirtyCache => assert_eq!(
                first,
                Err(GenericCallVectorError::Instantiation(
                    InstantiationError::Union(LiteralTypeCacheError::UnsupportedUnionConstituent(
                        derived.max(plain)
                    ))
                ))
            ),
            KeyofSessionControl::RecoveringDirtyCache => assert_eq!(
                first,
                Err(GenericCallVectorError::Instantiation(
                    InstantiationError::Union(LiteralTypeCacheError::InvalidCachedUnion(
                        dirty_result.unwrap()
                    ))
                ))
            ),
            KeyofSessionControl::RecoveringColdReturn => assert_eq!(first, Ok(error)),
        }
        assert_eq!(
            (limited.query_count(), limited.total_count()),
            (limit, limit)
        );
        assert_eq!(limited.limit_event_count(), 1);
        let expected_scans = scans + usize::from(dirty_result.is_some());
        assert_eq!(store.union_cache_validation_scan_count(), expected_scans);
        if control == KeyofSessionControl::RecoveringDirtyCache {
            assert_eq!(
                store.value_symbol_links(proxy),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(error),
                    ..original_links.clone()
                })
            );
            assert!(
                store
                    .instantiated_property_recovery(proxy)
                    .unwrap()
                    .matches_published_links(store.value_symbol_links(proxy))
            );
        } else {
            assert_eq!(store.value_symbol_links(proxy), Some(&original_links));
            assert!(store.instantiated_property_recovery(proxy).is_none());
        }
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
        assert_eq!(keyof_session_cache_state(store), before);
        let retry = demand_generic_call_vector_selected_return(store, generic, &mut limited)
            .map(|(returned, _)| returned);
        if control == KeyofSessionControl::FailFastDirtyCache {
            assert_eq!(
                retry,
                Err(GenericCallVectorError::Instantiation(
                    InstantiationError::CountLimit {
                        count: limit,
                        limit,
                    }
                ))
            );
        } else {
            assert_eq!(retry, Ok(error));
        }
        assert_eq!(
            (limited.query_count(), limited.total_count()),
            (limit, limit)
        );
        assert_eq!(limited.limit_event_count(), 2);
        assert_eq!(store.union_cache_validation_scan_count(), expected_scans);
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            None
        );
        assert_eq!(cached_nongeneric_keyof_type(store, &key_plan), Ok(None));
        assert_eq!(keyof_session_cache_state(store), before);
        if control == KeyofSessionControl::RecoveringDirtyCache {
            assert_eq!(
                store.value_symbol_links(proxy).unwrap().resolved_type,
                Some(error)
            );
            assert!(
                store
                    .instantiated_property_recovery(proxy)
                    .unwrap()
                    .matches_published_links(store.value_symbol_links(proxy))
            );
            // This is a real recovered member. A later control must not erase its receipt.
            assert!(context.diagnostics().is_empty());
            return;
        }
        assert_eq!(store.value_symbol_links(proxy), Some(&original_links));
        assert!(store.instantiated_property_recovery(proxy).is_none());

        if control == KeyofSessionControl::RecoveringColdReturn {
            // A stale return must fail the reader before any new instantiation work.
            assert!(store.set_signature_resolved_return_type(signature, Some(error)));
            for _ in 0..2 {
                assert_eq!(
                    demand_generic_call_vector_selected_return(store, generic, &mut limited),
                    Err(GenericCallVectorError::Invariant(
                        GenericCallVectorInvariant::InvalidCachedInstantiation {
                            target: original,
                            signature,
                        }
                    ))
                );
                assert_eq!(
                    (limited.query_count(), limited.total_count()),
                    (limit, limit)
                );
                assert_eq!(limited.limit_event_count(), 2);
                assert_eq!(store.union_cache_validation_scan_count(), expected_scans);
                assert_eq!(keyof_session_cache_state(store), before);
            }
            assert!(store.set_signature_resolved_return_type(signature, None));
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let returned = demand_generic_call_vector_selected_return(store, generic, &mut adequate)
            .unwrap()
            .0;
        let keys = if nested {
            let reference = store
                .canonical_array_reference_with_targets(targets, returned)
                .unwrap()
                .unwrap();
            assert!(!reference.readonly);
            reference.element_type
        } else {
            returned
        };
        let TypeData::Union(union) = store.type_payload(keys).unwrap().data() else {
            panic!("Payload has two canonical property keys")
        };
        let expected = ["firstKey", "secondKey"].map(|name| {
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type(name)
                .unwrap()
        });
        assert_eq!(union.union.types.len(), expected.len());
        assert!(expected.iter().all(|key| union.union.types.contains(key)));
        let TypeData::Index(origin) = store.type_payload(union.origin.unwrap()).unwrap().data()
        else {
            panic!("the named key union must keep its Index origin")
        };
        assert_eq!(origin.target, payload);
        assert_eq!(origin.index_flags, IndexFlags::NONE);
        assert_eq!(
            cached_nongeneric_keyof_type(store, &key_plan),
            Ok(Some(keys))
        );
        assert_eq!(
            store.signature(signature).unwrap().resolved_return_type(),
            Some(returned)
        );
        assert_eq!(
            store.signature(original).unwrap().resolved_return_type(),
            Some(template)
        );
        if dirty_result.is_some() {
            assert_eq!(
                store.value_symbol_links(proxy).unwrap().resolved_type,
                Some(number)
            );
        } else {
            assert_eq!(store.value_symbol_links(proxy), Some(&original_links));
        }
        assert!(store.instantiated_property_recovery(proxy).is_none());
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let warm = keyof_session_cache_state(store);
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
                returned
            );
            assert_eq!(
                resolve_nongeneric_keyof_type_with_session(store, &key_plan, &mut limited),
                Ok(keys)
            );
            assert_eq!(
                (limited.query_count(), limited.total_count()),
                (limit, limit)
            );
            assert_eq!(limited.limit_event_count(), 2);
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(keyof_session_cache_state(store), warm);
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn method_keyof_return_preparation_uses_the_callers_spent_budget() {
        assert_keyof_selected_return_uses_caller(false, KeyofSessionControl::FailFastDirtyCache);
    }

    #[test]
    fn nested_method_keyof_return_keeps_the_caller_through_mapper_recursion() {
        assert_keyof_selected_return_uses_caller(true, KeyofSessionControl::FailFastDirtyCache);
    }

    #[test]
    fn recovering_keyof_return_keeps_the_dirty_cache_error_and_property_receipt() {
        for nested in [false, true] {
            assert_keyof_selected_return_uses_caller(
                nested,
                KeyofSessionControl::RecoveringDirtyCache,
            );
        }
    }

    #[test]
    fn nested_keyof_return_recovery_stays_cold_until_a_healthy_caller_retries() {
        assert_keyof_selected_return_uses_caller(true, KeyofSessionControl::RecoveringColdReturn);
    }

    #[test]
    fn borrowed_keyof_queries_reject_a_poisoned_key_cache_without_spending_the_caller() {
        for recovering in [false, true] {
            let mut fixture = fixture("interface Payload { firstKey: number; secondKey: string }");
            let payload = resolve_interface(&mut fixture);
            let plan = plan_nongeneric_keyof_type(&fixture.store, payload).unwrap();
            let mut setup = InstantiationSession::new(InstantiationLimits::default());
            let keys =
                resolve_nongeneric_keyof_type_with_session(&mut fixture.store, &plan, &mut setup)
                    .unwrap();
            let owner = fixture.store.type_payload(payload).unwrap().symbol();
            assert!(owner.is_some());
            assert!(fixture.store.set_type_symbol(keys, owner));
            let limits = InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            };
            let error = fixture.store.intrinsic_bootstrap().unwrap().error_type;
            let mut session = if recovering {
                InstantiationSession::new_recovering(&fixture.store, limits, error).unwrap()
            } else {
                InstantiationSession::new(limits)
            };
            let before = keyof_session_cache_state(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    resolve_nongeneric_keyof_type_with_session(
                        &mut fixture.store,
                        &plan,
                        &mut session
                    ),
                    Err(NongenericKeyofError::InvalidCachedResult(keys))
                );
                assert_eq!((session.query_count(), session.total_count()), (0, 0));
                assert_eq!(session.limit_event_count(), 0);
                assert_eq!(keyof_session_cache_state(&fixture.store), before);
            }
            assert!(fixture.store.set_type_symbol(keys, None));
            assert_eq!(
                resolve_nongeneric_keyof_type_with_session(&mut fixture.store, &plan, &mut session),
                Ok(keys)
            );
            assert_eq!((session.query_count(), session.total_count()), (0, 0));
            assert_eq!(session.limit_event_count(), 0);
            assert_eq!(keyof_session_cache_state(&fixture.store), before);
        }
    }
}
