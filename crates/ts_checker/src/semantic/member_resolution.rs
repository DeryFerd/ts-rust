//! Exact first leaf of union property synthesis.
//!
//! This ports the direct-property portion of pinned
//! `getPropertyOfUnionOrIntersectionType` and
//! `createUnionOrIntersectionProperty`. The receiver has exactly two
//! already-resolved property-only constituents: either the original anonymous,
//! declaration-free raw objects or two source-declared interfaces and type
//! literals. Source queries also admit two canonical property-only
//! intersections after their declared members resolve. The query does not
//! project apparent `Object`/`Function` members or index signatures.
//!
//! The existing `UnionOrIntersectionTypeData` cache is authoritative. A cold
//! query allocates its augmented property-cache table before synthesizing a
//! property, including same-symbol and all-missing queries. Warm hits are
//! proved from the selected name only and allocate nothing.
//! Symbol display shares the read-only plan assembly and exact cache proof.

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
    semantic::PreparedSymbolTable,
};

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable, SourceCheckError, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    instantiate::InstantiationSession,
    links::{DeferredSymbolLinks, ValueSymbolLinks},
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation,
        validate_resolved_closed_alias_property_object, validate_resolved_declared_property_object,
    },
    relater::ResolvedOwnProperty,
    store::SourceNodeParent,
    type_records::{
        ConstituentMapState, ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData,
    },
    types::{ObjectFlags, TypeFlags},
};

/// One public, non-partial property projected from an exact union receiver.
///
/// `symbol` preserves pinned identity: a same-symbol union returns the original
/// source symbol, while distinct source symbols return the cached synthetic
/// symbol. `type_` composes lookup with pinned `getTypeOfSymbol` read
/// optionality, so a strict optional borrowed source keeps its raw value links
/// while this projection returns `raw | undefined`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolvedUnionProperty {
    symbol: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
    readonly: bool,
}

impl ResolvedUnionProperty {
    #[must_use]
    pub const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    #[must_use]
    pub const fn type_id(&self) -> TypeId {
        self.type_
    }

    #[must_use]
    pub const fn is_optional(&self) -> bool {
        self.optional
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.readonly
    }
}

/// The raw lookup retains partial properties for discriminant selection.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ResolvedRawUnionProperty {
    pub(super) property: ResolvedUnionProperty,
    pub(super) check_flags: CheckFlags,
}

impl ResolvedRawUnionProperty {
    fn readable(self) -> Option<ResolvedUnionProperty> {
        (!self.check_flags.contains(CheckFlags::READ_PARTIAL)).then_some(self.property)
    }
}

/// A malformed cache or a deliberately unported member-resolution family.
///
/// No variant is a negative property lookup. A valid union with no public
/// property returns `Ok(None)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum UnionPropertyError {
    InvalidUnion(TypeId),
    UnsupportedUnion(TypeId),
    UnsupportedConstituent(TypeId),
    UnsupportedPropertyType(TypeId),
    UnsupportedExactOptionalProperty(TypeId),
    InvalidProperty(SemanticSymbolId),
    InvalidCache(TypeId),
    Relation(RelationUnavailable),
    TypeCache(LiteralTypeCacheError),
    Capacity(TypeId),
}

/// Public failure surface for a context-owned union-property query.
///
/// Internal literal/union cache implementation errors are deliberately folded
/// into [`Self::InvalidCache`], so this adapter does not expose a private
/// bootstrap error family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalUnionPropertyError {
    InvalidUnion(TypeId),
    UnsupportedUnion(TypeId),
    UnsupportedConstituent(TypeId),
    UnsupportedPropertyType(TypeId),
    UnsupportedExactOptionalProperty(TypeId),
    InvalidProperty(SemanticSymbolId),
    InvalidCache(TypeId),
    Relation(RelationUnavailable),
    Capacity(TypeId),
}

impl CanonicalUnionPropertyError {
    pub(super) const fn from_internal(union: TypeId, error: UnionPropertyError) -> Self {
        match error {
            UnionPropertyError::InvalidUnion(type_) => Self::InvalidUnion(type_),
            UnionPropertyError::UnsupportedUnion(type_) => Self::UnsupportedUnion(type_),
            UnionPropertyError::UnsupportedConstituent(type_) => {
                Self::UnsupportedConstituent(type_)
            }
            UnionPropertyError::UnsupportedPropertyType(type_) => {
                Self::UnsupportedPropertyType(type_)
            }
            UnionPropertyError::UnsupportedExactOptionalProperty(type_) => {
                Self::UnsupportedExactOptionalProperty(type_)
            }
            UnionPropertyError::InvalidProperty(symbol) => Self::InvalidProperty(symbol),
            UnionPropertyError::InvalidCache(type_) => Self::InvalidCache(type_),
            UnionPropertyError::Relation(error) => Self::Relation(error),
            UnionPropertyError::TypeCache(LiteralTypeCacheError::Capacity) => Self::Capacity(union),
            UnionPropertyError::TypeCache(_) => Self::InvalidCache(union),
            UnionPropertyError::Capacity(type_) => Self::Capacity(type_),
        }
    }
}

impl std::fmt::Display for CanonicalUnionPropertyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidUnion(type_) => {
                write!(formatter, "union type {type_:?} has invalid member state")
            }
            Self::UnsupportedUnion(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} is outside the direct member adapter"
                )
            }
            Self::UnsupportedConstituent(type_) => write!(
                formatter,
                "union constituent {type_:?} is outside the supported property-object modes"
            ),
            Self::UnsupportedPropertyType(type_) => write!(
                formatter,
                "property type {type_:?} is outside the terminal union-member leaf"
            ),
            Self::UnsupportedExactOptionalProperty(type_) => write!(
                formatter,
                "union type {type_:?} requires exact optional missing-type synthesis"
            ),
            Self::InvalidProperty(symbol) => {
                write!(
                    formatter,
                    "property symbol {symbol:?} has invalid union inputs"
                )
            }
            Self::InvalidCache(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} has an invalid property cache"
                )
            }
            Self::Relation(error) => error.fmt(formatter),
            Self::Capacity(type_) => {
                write!(
                    formatter,
                    "union property query for {type_:?} exhausted capacity"
                )
            }
        }
    }
}

impl std::error::Error for CanonicalUnionPropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::InvalidUnion(_)
            | Self::UnsupportedUnion(_)
            | Self::UnsupportedConstituent(_)
            | Self::UnsupportedPropertyType(_)
            | Self::UnsupportedExactOptionalProperty(_)
            | Self::InvalidProperty(_)
            | Self::InvalidCache(_)
            | Self::Capacity(_) => None,
        }
    }
}

impl std::fmt::Display for UnionPropertyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidUnion(type_) => {
                write!(formatter, "union type {type_:?} has invalid member state")
            }
            Self::UnsupportedUnion(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} is outside the direct member leaf"
                )
            }
            Self::UnsupportedConstituent(type_) => write!(
                formatter,
                "union constituent {type_:?} is outside the resolved property-object leaf"
            ),
            Self::UnsupportedPropertyType(type_) => write!(
                formatter,
                "property type {type_:?} is outside the terminal union-member leaf"
            ),
            Self::UnsupportedExactOptionalProperty(type_) => write!(
                formatter,
                "union type {type_:?} requires exact optional missing-type synthesis"
            ),
            Self::InvalidProperty(symbol) => {
                write!(
                    formatter,
                    "property symbol {symbol:?} has invalid union inputs"
                )
            }
            Self::InvalidCache(type_) => {
                write!(
                    formatter,
                    "union type {type_:?} has an invalid property cache"
                )
            }
            Self::Relation(error) => error.fmt(formatter),
            Self::TypeCache(error) => error.fmt(formatter),
            Self::Capacity(type_) => {
                write!(
                    formatter,
                    "union property query for {type_:?} exhausted capacity"
                )
            }
        }
    }
}

impl std::error::Error for UnionPropertyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::TypeCache(error) => Some(error),
            Self::InvalidUnion(_)
            | Self::UnsupportedUnion(_)
            | Self::UnsupportedConstituent(_)
            | Self::UnsupportedPropertyType(_)
            | Self::UnsupportedExactOptionalProperty(_)
            | Self::InvalidProperty(_)
            | Self::InvalidCache(_)
            | Self::Capacity(_) => None,
        }
    }
}

impl From<RelationUnavailable> for UnionPropertyError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<LiteralTypeCacheError> for UnionPropertyError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::TypeCache(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceProperty {
    symbol: SemanticSymbolId,
    raw_type: TypeId,
    optional: bool,
    readonly: bool,
    declaration: Option<NodeRef>,
    value_declaration: Option<NodeRef>,
    parent: Option<SemanticSymbolId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SyntheticPropertyPlan {
    sources: Vec<SourceProperty>,
    index_types: Vec<TypeId>,
    optional: bool,
    readonly: bool,
    partial: bool,
    declarations: Option<Vec<NodeRef>>,
    value_declaration: Option<NodeRef>,
    parent: Option<SemanticSymbolId>,
    name_type: Option<TypeId>,
    synthetic_kind: CheckFlags,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnionMemberMode {
    Raw,
    Declared,
    Intersection,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PropertyOutcome {
    Missing,
    Borrowed(SourceProperty),
    Synthetic(SyntheticPropertyPlan),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct UnionPropertyPlan {
    union: TypeId,
    name: EscapedName,
    cache: Option<SymbolTableId>,
    cache_without_function_property_augment: Option<SymbolTableId>,
    array_targets: Option<CanonicalArrayTargets>,
    outcome: PropertyOutcome,
}

type ValidatedUnionShell = (
    Vec<TypeId>,
    Option<SymbolTableId>,
    Option<SymbolTableId>,
    UnionMemberMode,
);

struct PreparedColdQuery {
    cache: Option<PreparedSymbolTable>,
    types: Option<PreparedTypeQueryTypes>,
    effective: Vec<TypeId>,
    deferred: Vec<TypeId>,
}

#[derive(Clone)]
struct EffectiveTypes {
    values: Vec<TypeId>,
}

impl EffectiveTypes {
    fn as_slice(&self) -> &[TypeId] {
        &self.values
    }
}

impl CanonicalTypeMapperStore {
    /// Resolves one direct property from an already-resolved union receiver.
    ///
    /// Partial properties are synthesized and cached exactly, then filtered
    /// from this public result. This mirrors pinned
    /// `getPropertyOfUnionOrIntersectionType`, while keeping the internal
    /// `READ_PARTIAL` entry observable through the union's property cache.
    pub(super) fn resolved_union_property(
        &mut self,
        union: TypeId,
        name: &str,
    ) -> Result<Option<ResolvedUnionProperty>, UnionPropertyError> {
        let plan = plan_union_property(self, union, name, None, None)?;
        self.resolve_union_property_plan(&plan, None, None)
    }

    fn resolve_union_property_plan(
        &mut self,
        plan: &UnionPropertyPlan,
        global_types: Option<&CanonicalGlobalTypes>,
        session: Option<&mut InstantiationSession>,
    ) -> Result<Option<ResolvedUnionProperty>, UnionPropertyError> {
        self.resolve_union_property_plan_raw(plan, global_types, session)
            .map(|property| property.and_then(ResolvedRawUnionProperty::readable))
    }

    fn resolve_union_property_plan_raw(
        &mut self,
        plan: &UnionPropertyPlan,
        global_types: Option<&CanonicalGlobalTypes>,
        session: Option<&mut InstantiationSession>,
    ) -> Result<Option<ResolvedRawUnionProperty>, UnionPropertyError> {
        if let Some(cache) = plan.cache {
            let cached = self
                .symbol_table(cache)
                .ok_or(UnionPropertyError::InvalidCache(plan.union))?
                .get(plan.name.as_ref());
            if let Some(cached) = cached {
                return validate_cached_property_raw(self, plan, cached).map(Some);
            }
        }

        let mut prepared = prepare_cold_query(self, plan, global_types, session)?;
        let cache = match plan.cache {
            Some(cache) => cache,
            None => publish_property_cache(
                self,
                plan,
                prepared
                    .cache
                    .take()
                    .expect("a cold union query prepared its property-cache table"),
            ),
        };
        match &plan.outcome {
            PropertyOutcome::Missing => Ok(None),
            PropertyOutcome::Borrowed(property) => {
                assert_eq!(
                    self.insert_symbol(cache, plan.name.clone(), property.symbol),
                    Some(None)
                );
                let type_ = materialize_source_read_type(
                    self,
                    *property,
                    prepared.types.as_mut(),
                    global_types,
                );
                Ok(Some(ResolvedRawUnionProperty {
                    property: project_source_property(*property, type_),
                    check_flags: self.symbol(property.symbol)
                        .expect("the selected source symbol was validated").check_flags(),
                }))
            }
            PropertyOutcome::Synthetic(synthetic) => {
                let property = publish_synthetic_property(
                    self,
                    plan,
                    synthetic,
                    prepared
                        .types
                        .as_mut()
                        .expect("a synthetic property prepared its type unions"),
                    global_types,
                    std::mem::take(&mut prepared.effective),
                    std::mem::take(&mut prepared.deferred),
                );
                assert_eq!(
                    self.insert_symbol(cache, plan.name.clone(), property.symbol),
                    Some(None)
                );
                Ok(Some(ResolvedRawUnionProperty {
                    check_flags: self.symbol(property.symbol)
                        .expect("the synthetic symbol was published").check_flags(),
                    property,
                }))
            }
        }
    }
}

#[allow(clippy::too_many_arguments)] // Keep the source query's session and diagnostics.
pub(super) fn resolve_source_union_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    union: TypeId,
    name: &str,
) -> Result<Option<ResolvedUnionProperty>, SourceCheckError> {
    resolve_source_union_property_raw(
        store, host, global_types, options, session, diagnostics, node, union, name,
    ).map(|property| property.and_then(ResolvedRawUnionProperty::readable))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_source_union_property_raw(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    union: TypeId,
    name: &str,
) -> Result<Option<ResolvedRawUnionProperty>, SourceCheckError> {
    let error = |error| super::source::source_union_property_error(node, error);
    let targets = CanonicalArrayTargets::from_global_types(global_types);
    let record = store
        .type_payload(union)
        .ok_or_else(|| error(UnionPropertyError::InvalidUnion(union)))?;
    let TypeData::Union(data) = record.data() else {
        return Err(error(UnionPropertyError::UnsupportedUnion(union)));
    };
    if data.union.types.len() < 2 {
        return Err(error(UnionPropertyError::UnsupportedUnion(union)));
    }
    let constituents = data.union.types.clone();
    store
        .validate_union_query_metadata(union)
        .map_err(|cause| error(cause.into()))?;
    for &constituent in &constituents {
        if store
            .type_payload(constituent)
            .is_some_and(|record| record.flags() == TypeFlags::INTERSECTION)
        {
            let resolved = super::intersection_types::demand_source_intersection_members(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                constituent,
            )?;
            if resolved != constituent {
                return Err(error(UnionPropertyError::InvalidUnion(union)));
            }
        }
    }
    let mut properties = Vec::new();
    properties.try_reserve_exact(constituents.len())
        .map_err(|_| error(UnionPropertyError::Capacity(union)))?;
    let mut index_types = Vec::new();
    index_types.try_reserve_exact(constituents.len())
        .map_err(|_| error(UnionPropertyError::Capacity(union)))?;
    let mut index_readonly = false;
    let mut partial = false;
    for constituent in constituents {
        let property = resolve_source_union_constituent_property(
            store, host, global_types, options, session, diagnostics, node, constituent, name,
        )?;
        if let Some(property) = property {
            let record = store.symbol(property.symbol)
                .ok_or_else(|| error(UnionPropertyError::InvalidProperty(property.symbol)))?;
            properties.push(Some(SourceProperty {
                symbol: property.symbol,
                raw_type: property.type_,
                optional: property.optional,
                readonly: property.readonly,
                declaration: record.declarations().and_then(|declarations| declarations.first()).copied(),
                value_declaration: record.value_declaration(),
                parent: record.parent(),
            }));
        } else if let Some(index) = resolve_source_union_constituent_index(
            store, host, global_types, options, session, diagnostics, node, constituent, name,
        )? {
            index_readonly |= index.readonly;
            index_types.push(index.value_type);
        } else {
            partial = true;
        }
    }
    let data = store.type_payload(union).and_then(|record| match record.data() {
        TypeData::Union(data) => Some(data),
        _ => None,
    }).ok_or_else(|| error(UnionPropertyError::InvalidUnion(union)))?;
    let mut plan = finish_union_property_plan(
        store, union, EscapedName::source(name), data.union.property_cache,
        data.union.property_cache_without_function_property_augment, Some(targets), properties,
    ).map_err(error)?;
    if partial || !index_types.is_empty() {
        let sources = match plan.outcome {
            PropertyOutcome::Missing => Vec::new(),
            PropertyOutcome::Borrowed(property) => vec![property],
            PropertyOutcome::Synthetic(synthetic) => synthetic.sources,
        };
        plan.outcome = if sources.is_empty() {
            PropertyOutcome::Missing
        } else {
            let mut synthetic = synthetic_plan(store, union, sources, partial).map_err(error)?;
            synthetic.index_types = index_types;
            synthetic.readonly |= index_readonly;
            PropertyOutcome::Synthetic(synthetic)
        };
    }
    store
        .resolve_union_property_plan_raw(&plan, Some(global_types), Some(session))
        .map_err(error)
}

/// Selects the canonical member symbol, including cold source-owned members.
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_source_union_constituent_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    receiver: TypeId,
    name: &str,
) -> Result<Option<ResolvedOwnProperty>, SourceCheckError> {
    let error = |error| super::source::source_union_property_error(node, error);
    if source_union_interface_target(store, receiver).map_err(error)?.is_some() {
        let heritage = store.source_interface_heritage_header(receiver).is_some()
            || store.direct_interface_heritage_provenance(receiver).is_some();
        let mut query = super::type_nodes::CanonicalTypeQuery::new_with_global_types_and_session(
            store, host, globals, options, session, diagnostics,
        )?;
        if heritage {
            return query.get_property_of_source_interface(receiver, EscapedName::source(name).as_ref());
        }
        query.prepare_source_class_interface_members(receiver)?;
        return super::object_members::resolve_object_property_by_key_with_source(
            store, host, globals, options, receiver, EscapedName::source(name).as_ref(), session, diagnostics,
        );
    }
    let flags = store.type_payload(receiver)
        .ok_or_else(|| error(UnionPropertyError::InvalidUnion(receiver)))?.flags();
    if flags.intersects(TypeFlags::NULL | TypeFlags::UNDEFINED) {
        store.validate_union_constituent(receiver).map_err(|cause| error(cause.into()))?;
        return Ok(None);
    }
    let targets = Some(CanonicalArrayTargets::from_global_types(globals));
    let mode = classify_union_constituent(store, receiver, receiver, targets).map_err(error)?;
    let property = super::object_members::resolve_object_property_by_key_with_source(
        store, host, globals, options, receiver, EscapedName::source(name).as_ref(), session, diagnostics,
    )?;
    if let Some(property) = property {
        validate_source_property(store, receiver, mode, property, EscapedName::source(name).as_ref(), targets)
            .map_err(error)?;
    }
    Ok(property)
}

fn source_union_interface_target(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
) -> Result<Option<TypeId>, UnionPropertyError> {
    let record = store.type_payload(receiver).ok_or(UnionPropertyError::InvalidUnion(receiver))?;
    let target = match record.data() {
        TypeData::Interface(_) => receiver,
        TypeData::TypeReference(reference) => reference.object.target
            .ok_or(UnionPropertyError::UnsupportedConstituent(receiver))?,
        _ => return Ok(None),
    };
    let record = store.type_payload(target).ok_or(UnionPropertyError::InvalidUnion(receiver))?;
    if matches!(record.data(), TypeData::Interface(_)) && !record.object_flags().contains(ObjectFlags::CLASS) {
        Ok(Some(target))
    } else {
        Err(UnionPropertyError::UnsupportedConstituent(receiver))
    }
}

/// Called only after a proved named miss on this same receiver.
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve_source_union_constituent_index(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    receiver: TypeId,
    name: &str,
) -> Result<Option<super::object_members::ResolvedSourceIndexRead>, SourceCheckError> {
    let error = |error| super::source::source_union_property_error(node, error);
    if source_union_interface_target(store, receiver).map_err(error)?.is_some() {
        return super::object_members::resolve_source_property_index_read(
            store, host, globals, options, receiver, EscapedName::source(name).as_ref(), session, diagnostics,
        );
    }
    let record = store.type_payload(receiver).ok_or_else(|| error(UnionPropertyError::InvalidUnion(receiver)))?;
    if record.flags().intersects(TypeFlags::NULL | TypeFlags::UNDEFINED) {
        store.validate_union_constituent(receiver).map_err(|cause| error(cause.into()))?;
    } else {
        // The legacy property-only proof includes an empty index table.
        classify_union_constituent(store, receiver, receiver, Some(CanonicalArrayTargets::from_global_types(globals)))
            .map_err(error)?;
    }
    Ok(None)
}

fn plan_union_property(
    store: &mut CanonicalTypeMapperStore,
    union: TypeId,
    name: &str,
    global_types: Option<&CanonicalGlobalTypes>,
    mut session: Option<&mut InstantiationSession>,
) -> Result<UnionPropertyPlan, UnionPropertyError> {
    let targets = global_types.map(CanonicalArrayTargets::from_global_types);
    let (constituents, cache, cache_without_function_property_augment, mode) =
        validate_union_shell(store, union, targets)?;
    let source_name = name;
    let name = EscapedName::source(source_name);
    let mut properties = Vec::new();
    properties
        .try_reserve_exact(constituents.len())
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for constituent in constituents {
        // Preserve the provider's full proof, including absent-name queries
        // on raw objects whose members are authenticated transient symbols.
        let resolved = if let Some(session) = session.as_deref_mut() {
            super::object_members::resolve_object_property_by_key(
                store,
                global_types,
                constituent,
                name.as_ref(),
                session,
            )?
        } else {
            store.resolved_own_property(constituent, source_name)?
        };
        properties.push(
            resolved
                .map(|property| {
                    validate_source_property(
                        store, constituent, mode, property, name.as_ref(), targets,
                    )
                })
                .transpose()?,
        );
    }
    finish_union_property_plan(
        store,
        union,
        name,
        cache,
        cache_without_function_property_augment,
        targets,
        properties,
    )
}

/// Rebuilds a display proof without calling the mutable member resolver.
fn plan_cached_union_property(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    name: &str,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<UnionPropertyPlan, UnionPropertyError> {
    let (constituents, cache, cache_without_function_property_augment, mode) =
        validate_union_shell(store, union, array_targets)?;
    let name = EscapedName::source(name);
    let mut properties = Vec::new();
    properties
        .try_reserve_exact(constituents.len())
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for constituent in constituents {
        properties.push(read_union_source_property(
            store,
            constituent,
            mode,
            name.as_ref(),
            array_targets,
        )?);
    }
    finish_union_property_plan(
        store,
        union,
        name,
        cache,
        cache_without_function_property_augment,
        array_targets,
        properties,
    )
}

/// Proves a retained source context from the same union property cache.
pub(super) fn cached_source_union_property(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    name: &str,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<ResolvedUnionProperty>, UnionPropertyError> {
    let plan = plan_cached_union_property(store, union, name, array_targets)?;
    let cache = plan
        .cache
        .and_then(|cache| store.symbol_table(cache))
        .ok_or(UnionPropertyError::InvalidCache(union))?;
    match cache.get(plan.name.as_ref()) {
        Some(symbol) => validate_cached_property(store, &plan, symbol),
        None if matches!(plan.outcome, PropertyOutcome::Missing) => Ok(None),
        None => Err(UnionPropertyError::InvalidCache(union)),
    }
}

fn finish_union_property_plan(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    name: EscapedName,
    cache: Option<SymbolTableId>,
    cache_without_function_property_augment: Option<SymbolTableId>,
    array_targets: Option<CanonicalArrayTargets>,
    properties: Vec<Option<SourceProperty>>,
) -> Result<UnionPropertyPlan, UnionPropertyError> {
    let partial = properties.iter().any(Option::is_none);
    let mut found: Vec<SourceProperty> = Vec::new();
    found
        .try_reserve_exact(properties.len())
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for property in properties.into_iter().flatten() {
        if let Some(previous) = found.iter().find(|previous| previous.symbol == property.symbol) {
            if previous != &property {
                return Err(UnionPropertyError::InvalidProperty(property.symbol));
            }
        } else {
            found.push(property);
        }
    }
    let options = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
        .options;
    if options.strict_null_checks
        && options.exact_optional_property_types
        && found.iter().any(|property| property.optional)
    {
        return Err(UnionPropertyError::UnsupportedExactOptionalProperty(union));
    }
    let outcome = match found.as_slice() {
        [] => PropertyOutcome::Missing,
        [property] if !partial => {
            PropertyOutcome::Borrowed(*property)
        }
        _ => {
            PropertyOutcome::Synthetic(synthetic_plan(store, union, found, partial)?)
        }
    };
    Ok(UnionPropertyPlan {
        union,
        name,
        cache,
        cache_without_function_property_augment,
        array_targets,
        outcome,
    })
}

/// Reads only the resolved property objects admitted by `validate_union_shell`.
fn read_union_source_property(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    mode: UnionMemberMode,
    name: ts_binder::EscapedNameRef<'_>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<SourceProperty>, UnionPropertyError> {
    if mode == UnionMemberMode::Intersection {
        let projection = validated_property_intersection(store, constituent, array_targets)?;
        let Some(symbol) = store
            .symbol_table(projection.members)
            .and_then(|members| members.get(name))
        else {
            return Ok(None);
        };
        let record = store
            .symbol(symbol)
            .ok_or(UnionPropertyError::InvalidProperty(symbol))?;
        let type_ = store
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(RelationUnavailable::UnresolvedPropertyType(symbol))?;
        return validate_source_property(
            store,
            constituent,
            mode,
            ResolvedOwnProperty {
                symbol,
                type_,
                optional: record.flags().contains(SymbolFlags::OPTIONAL),
                readonly: record.check_flags().contains(CheckFlags::READONLY),
            },
            name,
            array_targets,
        )
        .map(Some);
    }
    let invalid = || RelationUnavailable::InvalidStructuredMembers(constituent);
    let structured = store
        .type_payload(constituent)
        .and_then(|record| record.data().structured())
        .ok_or_else(invalid)?;
    let properties = structured.properties.as_deref().unwrap_or_default();
    let Some(members) = structured.members else {
        return if properties.is_empty() {
            Ok(None)
        } else {
            Err(invalid().into())
        };
    };
    let members = store.symbol_table(members).ok_or_else(invalid)?;
    if members.len() != properties.len() {
        return Err(invalid().into());
    }
    let synthetic_structural = mode == UnionMemberMode::Raw
        && properties.iter().any(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| record.flags().contains(SymbolFlags::TRANSIENT))
        });
    for (index, property) in properties.iter().enumerate() {
        let record = if synthetic_structural {
            super::relater::validated_synthetic_structural_property(store, constituent, *property)?
        } else {
            store
                .symbol(*property)
                .ok_or(RelationUnavailable::Symbol(*property))?
        };
        if !synthetic_structural
            && (!record.flags().contains(SymbolFlags::PROPERTY)
                || record
                    .flags()
                    .without(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                    != SymbolFlags::NONE
                || record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
                || record.name().is_reserved_member_name()
                || record.name().is_private_identifier()
                || record.name().is_late_bound()
                || mode == UnionMemberMode::Raw
                    && record
                        .declarations()
                        .is_some_and(|declarations| !declarations.is_empty()))
        {
            return Err(RelationUnavailable::UnsupportedProperty(*property).into());
        }
        if properties[..index].contains(property)
            || members.get(record.name()) != Some(*property)
            || mode == UnionMemberMode::Raw && record.parent().is_some()
        {
            return Err(invalid().into());
        }
    }
    let Some(symbol) = members.get(name) else {
        return Ok(None);
    };
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let type_ = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .ok_or(RelationUnavailable::UnresolvedPropertyType(symbol))?;
    validate_source_property(
        store,
        constituent,
        mode,
        ResolvedOwnProperty {
            symbol,
            type_,
            optional: record.flags().contains(SymbolFlags::OPTIONAL),
            readonly: record.check_flags().contains(CheckFlags::READONLY),
        },
        name,
        array_targets,
    )
    .map(Some)
}

/// Proves a published union property without resolving members or writing caches.
/// The result is used only to match a source parent's member table.
pub(super) fn published_union_property_source(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<SemanticSymbolId>, UnionPropertyError> {
    let record = store
        .symbol(symbol)
        .ok_or(UnionPropertyError::InvalidProperty(symbol))?;
    let containing = store
        .value_symbol_links(symbol)
        .and_then(|links| links.containing_type);
    let containing_data = containing.and_then(|type_| store.type_payload(type_));
    // Intersections use the same check flag. Leave their own cached properties
    // to the existing display path, but reject a redirected containing type.
    if record
        .check_flags()
        .contains(CheckFlags::SYNTHETIC_PROPERTY)
        && let Some(TypeData::Intersection(data)) =
            containing_data.map(super::type_records::TypeRecord::data)
    {
        return if data
            .intersection
            .property_cache
            .and_then(|cache| store.symbol_table(cache))
            .and_then(|cache| cache.get(record.name()))
            == Some(symbol)
            && data
                .intersection
                .resolved_properties
                .as_ref()
                .is_some_and(|properties| properties.contains(&symbol))
        {
            Ok(None)
        } else {
            Err(UnionPropertyError::InvalidProperty(symbol))
        };
    }
    if !containing_data.is_some_and(|record| matches!(record.data(), TypeData::Union(_)))
        && !record
            .check_flags()
            .contains(CheckFlags::SYNTHETIC_PROPERTY)
    {
        return Ok(None);
    }
    let invalid = || UnionPropertyError::InvalidProperty(symbol);
    let union = containing.ok_or_else(invalid)?;
    let name = record.name().as_utf8().ok_or_else(invalid)?;
    let plan = plan_cached_union_property(store, union, name, None)?;
    let PropertyOutcome::Synthetic(synthetic) = &plan.outcome else {
        return Err(invalid());
    };
    if store.object_literal_property_clone_origin(symbol).is_some()
        || plan
            .cache
            .and_then(|cache| store.symbol_table(cache))
            .and_then(|cache| cache.get(record.name()))
            != Some(symbol)
    {
        return Err(invalid());
    }
    validate_cached_property(store, &plan, symbol)?;
    for source in &synthetic.sources {
        let Some(declaration) = source.declaration else {
            continue;
        };
        let node = host.node(declaration).ok_or_else(invalid)?;
        let owner = source.parent.ok_or_else(invalid)?;
        let source_symbol = store
            .value_symbol_links(source.symbol)
            .and_then(|links| links.target)
            .unwrap_or(source.symbol);
        let Some([owner_declaration]) =
            store.symbol(owner).and_then(|record| record.declarations())
        else {
            return Err(invalid());
        };
        if !host.symbol_matches(store, declaration, source_symbol)
            || !host.symbol_matches(store, *owner_declaration, owner)
            || store
                .symbol(source_symbol)
                .and_then(|symbol| symbol.parent())
                != Some(owner)
            || store.source_node_kind(declaration) != Some(node.kind)
            || host.node(*owner_declaration).is_none_or(|owner_node| {
                store.source_node_kind(*owner_declaration) != Some(owner_node.kind)
            })
            || node
                .parent
                .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
                != Some(*owner_declaration)
        {
            return Err(invalid());
        }
    }
    Ok(Some(if synthetic.parent.is_some() {
        let source = synthetic.sources[0].symbol;
        store
            .value_symbol_links(source)
            .and_then(|links| links.target)
            .unwrap_or(source)
    } else {
        symbol
    }))
}

fn validate_union_shell(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ValidatedUnionShell, UnionPropertyError> {
    let record = store
        .type_payload(union)
        .ok_or(UnionPropertyError::InvalidUnion(union))?;
    let TypeData::Union(data) = record.data() else {
        return Err(UnionPropertyError::UnsupportedUnion(union));
    };
    if data.union.types.len() < 2 {
        return Err(UnionPropertyError::UnsupportedUnion(union));
    }
    let left_mode = classify_union_constituent(store, union, data.union.types[0], array_targets)?;
    for constituent in &data.union.types[1..] {
        if left_mode != classify_union_constituent(store, union, *constituent, array_targets)? {
            return Err(UnionPropertyError::UnsupportedUnion(union));
        }
    }
    let mode = left_mode;
    if record.flags() != TypeFlags::UNION
        || mode != UnionMemberMode::Intersection && record.object_flags() != ObjectFlags::NONE
        || record.symbol().is_some()
        || mode == UnionMemberMode::Raw && record.alias().is_some()
        || data.union.structured != StructuredTypeData::default()
        || mode == UnionMemberMode::Raw && data.union.types.windows(2).any(|pair| pair[0] >= pair[1])
        || data.union.resolved_properties.is_some()
        || data.resolved_reduced_type.is_some()
        || data.regular_type.is_some()
        || data.origin.is_some()
        || !data.key_property_name.is_empty()
        || data.constituent_map != ConstituentMapState::Unallocated
    {
        return Err(UnionPropertyError::InvalidUnion(union));
    }
    if [
        data.union.property_cache,
        data.union.property_cache_without_function_property_augment,
    ]
    .into_iter()
    .flatten()
    .any(|cache| store.symbol_table(cache).is_none())
    {
        return Err(UnionPropertyError::InvalidCache(union));
    }
    if mode != UnionMemberMode::Raw {
        let expected_alias = match record.alias() {
            Some(alias) => Some(
                store
                    .type_alias(alias)
                    .and_then(super::type_records::TypeAlias::symbol)
                    .ok_or(UnionPropertyError::InvalidUnion(union))?,
            ),
            None => None,
        };
        match array_targets {
            Some(targets) => {
                store.validate_cached_union_result_with_array_targets(
                    targets, union, expected_alias,
                )?;
            }
            None => store.validate_cached_union_result(union, expected_alias)?,
        }
    }
    Ok((
        data.union.types.clone(),
        data.union.property_cache,
        data.union.property_cache_without_function_property_augment,
        mode,
    ))
}

fn classify_union_constituent(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<UnionMemberMode, UnionPropertyError> {
    if store
        .type_payload(type_)
        .is_some_and(|record| record.flags() == TypeFlags::INTERSECTION)
    {
        validated_property_intersection(store, type_, array_targets)?;
        return Ok(UnionMemberMode::Intersection);
    }
    if validate_plain_property_object(store, type_).is_ok() {
        return Ok(UnionMemberMode::Raw);
    }
    match validate_resolved_declared_property_object(store, type_) {
        DeclaredPropertyObjectValidation::Valid(
            DeclaredPropertyObjectProof::TypeLiteral | DeclaredPropertyObjectProof::Interface,
        ) => Ok(UnionMemberMode::Declared),
        DeclaredPropertyObjectValidation::NotDeclared => {
            match validate_resolved_closed_alias_property_object(store, type_) {
                DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::TypeLiteral) => {
                    // Ownership permits the read. Nested types still need the
                    // caller's Array identities and complete cache validation.
                    match array_targets {
                        Some(targets) => {
                            store.validate_union_constituent_with_array_targets(targets, type_)?;
                        }
                        None => store.validate_union_constituent(type_)?,
                    }
                    Ok(UnionMemberMode::Declared)
                }
                DeclaredPropertyObjectValidation::Malformed => {
                    Err(UnionPropertyError::InvalidUnion(union))
                }
                _ => Err(UnionPropertyError::UnsupportedConstituent(type_)),
            }
        }
        DeclaredPropertyObjectValidation::Malformed => Err(UnionPropertyError::InvalidUnion(union)),
    }
}

fn validated_property_intersection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<super::intersection_types::IntersectionTypeProjection, UnionPropertyError> {
    let projection = store
        .validate_intersection_type_with_array_targets(type_, array_targets)
        .map_err(|_| UnionPropertyError::UnsupportedConstituent(type_))?;
    for constituent in &projection.types {
        let record = store
            .type_payload(*constituent)
            .ok_or(UnionPropertyError::UnsupportedConstituent(*constituent))?;
        let structured = record
            .data()
            .structured()
            .ok_or(UnionPropertyError::UnsupportedConstituent(*constituent))?;
        if record.flags() != TypeFlags::OBJECT
            || structured
                .signatures
                .as_ref()
                .is_some_and(|signatures| !signatures.is_empty())
            || structured
                .index_infos
                .as_ref()
                .is_some_and(|indexes| !indexes.is_empty())
            || super::object_aliases::source_property_object_projection(store, *constituent)?
                .is_none()
                && !matches!(
                    validate_resolved_declared_property_object(store, *constituent),
                    DeclaredPropertyObjectValidation::Valid(_)
                )
        {
            return Err(UnionPropertyError::UnsupportedConstituent(*constituent));
        }
    }
    Ok(projection)
}

fn validate_plain_property_object(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), UnionPropertyError> {
    let record = store
        .type_payload(type_)
        .ok_or(UnionPropertyError::UnsupportedConstituent(type_))?;
    let TypeData::Object(object) = record.data() else {
        return Err(UnionPropertyError::UnsupportedConstituent(type_));
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol().is_some()
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(UnionPropertyError::UnsupportedConstituent(type_));
    }
    Ok(())
}

fn validate_source_property(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    mode: UnionMemberMode,
    property: ResolvedOwnProperty,
    name: ts_binder::EscapedNameRef<'_>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceProperty, UnionPropertyError> {
    if mode == UnionMemberMode::Intersection {
        return validate_intersection_source_property(
            store, constituent, property, name, array_targets,
        );
    }
    let record = store
        .symbol(property.symbol)
        .ok_or(UnionPropertyError::InvalidProperty(property.symbol))?;
    let expected_flags = SymbolFlags::PROPERTY
        | if property.optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let expected_checks = if property.readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    };
    if record.flags() != expected_flags
        || record.check_flags() != expected_checks
        || record.name() != name
        || record.members().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(property.symbol) != Some(property.symbol)
        || store.value_symbol_links(property.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(property.type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(UnionPropertyError::InvalidProperty(property.symbol));
    }
    let (declaration, value_declaration, parent) = match mode {
        UnionMemberMode::Raw => {
            if record.declarations().is_some()
                || record.value_declaration().is_some()
                || record.parent().is_some()
            {
                return Err(UnionPropertyError::InvalidProperty(property.symbol));
            }
            (None, None, None)
        }
        UnionMemberMode::Declared => {
            let (declaration, parent) =
                validate_declared_property_provenance(store, constituent, property.symbol)?;
            (Some(declaration), Some(declaration), Some(parent))
        }
        UnionMemberMode::Intersection => {
            unreachable!("intersection properties use their cache proof")
        }
    };
    if !supported_terminal_property_type(store, property.type_) {
        return Err(UnionPropertyError::UnsupportedPropertyType(property.type_));
    }
    store.validate_union_constituent(property.type_)?;
    Ok(SourceProperty {
        symbol: property.symbol,
        raw_type: property.type_,
        optional: property.optional,
        readonly: property.readonly,
        declaration,
        value_declaration,
        parent,
    })
}

fn validate_intersection_source_property(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    property: ResolvedOwnProperty,
    name: ts_binder::EscapedNameRef<'_>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceProperty, UnionPropertyError> {
    let projection = validated_property_intersection(store, constituent, array_targets)?;
    let invalid = || UnionPropertyError::InvalidProperty(property.symbol);
    let record = store.symbol(property.symbol).ok_or_else(invalid)?;
    if store
        .symbol_table(projection.members)
        .and_then(|members| members.get(name))
        != Some(property.symbol)
        || !projection.properties.contains(&property.symbol)
        || record.name() != name
        || store.get_merged_symbol(property.symbol) != Some(property.symbol)
        || record.flags().contains(SymbolFlags::OPTIONAL) != property.optional
        || record.check_flags().contains(CheckFlags::READONLY) != property.readonly
        || store
            .value_symbol_links(property.symbol)
            .and_then(|links| links.resolved_type)
            != Some(property.type_)
    {
        return Err(invalid());
    }
    let declaration = match record.declarations() {
        Some([declaration]) => Some(*declaration),
        None | Some([]) => None,
        Some(_) => return Err(UnionPropertyError::UnsupportedConstituent(constituent)),
    };
    match array_targets {
        Some(targets) => {
            store.validate_union_constituent_with_array_targets(targets, property.type_)?;
        }
        None => store.validate_union_constituent(property.type_)?,
    }
    Ok(SourceProperty {
        symbol: property.symbol,
        raw_type: property.type_,
        optional: property.optional,
        readonly: property.readonly,
        declaration,
        value_declaration: record.value_declaration(),
        parent: record.parent(),
    })
}

fn validate_declared_property_provenance(
    store: &CanonicalTypeMapperStore,
    constituent: TypeId,
    property: SemanticSymbolId,
) -> Result<(NodeRef, SemanticSymbolId), UnionPropertyError> {
    let record = store
        .type_payload(constituent)
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let (structured, interface) = match record.data() {
        TypeData::Object(object) => (&object.structured, false),
        TypeData::Interface(interface) => (&interface.reference.object.structured, true),
        _ => return Err(UnionPropertyError::InvalidProperty(property)),
    };
    let owner = record
        .symbol()
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(UnionPropertyError::InvalidProperty(property));
    };
    let property_record = store
        .symbol(property)
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let [declaration] = property_record.declarations().unwrap_or_default() else {
        return Err(UnionPropertyError::InvalidProperty(property));
    };
    let members = structured
        .members
        .ok_or(UnionPropertyError::InvalidProperty(property))?;
    let owner_matches = if interface {
        owner_record.flags() == SymbolFlags::INTERFACE
            && owner_record.name().as_utf8().is_some()
            && store.source_node_kind(*owner_declaration) == Some(SyntaxKind::InterfaceDeclaration)
    } else {
        owner_record.flags() == SymbolFlags::TYPE_LITERAL
            && owner_record.name() == InternalSymbolName::Type.as_ref()
            && store.source_node_kind(*owner_declaration) == Some(SyntaxKind::TypeLiteral)
    };
    if !owner_matches
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration().is_some()
        || owner_record.members() != Some(members)
        || owner_record.exports().is_some()
        || owner_record.parent().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || property_record.value_declaration() != Some(*declaration)
        || property_record.parent() != Some(owner)
        || !matches!(
            store.source_node_kind(*declaration),
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
        )
        || store.source_node_parent(*declaration)
            != Some(SourceNodeParent::Parent(*owner_declaration))
        || structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&property))
        || store
            .symbol_table(members)
            .and_then(|table| table.get(property_record.name()))
            != Some(property)
    {
        return Err(UnionPropertyError::InvalidProperty(property));
    }
    Ok((*declaration, owner))
}

fn supported_terminal_property_type(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    store.type_payload(type_).is_some_and(|record| {
        record.flags().intersects(
            TypeFlags::PRIMITIVE
                | TypeFlags::ANY_OR_UNKNOWN
                | TypeFlags::NEVER
                | TypeFlags::NON_PRIMITIVE
                | TypeFlags::UNION,
        )
    })
}

fn synthetic_plan(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    sources: Vec<SourceProperty>,
    partial: bool,
) -> Result<SyntheticPropertyPlan, UnionPropertyError> {
    debug_assert!(!sources.is_empty(), "a synthetic property has a source");
    let mut declarations = Vec::new();
    for source in &sources {
        let source_declarations = store.symbol(source.symbol)
            .ok_or(UnionPropertyError::InvalidProperty(source.symbol))?.declarations().unwrap_or_default();
        declarations.try_reserve(source_declarations.len()).map_err(|_| UnionPropertyError::Capacity(union))?;
        declarations.extend_from_slice(source_declarations);
    }
    let first_value_source = sources.iter().find(|source| source.value_declaration.is_some());
    let first_value_declaration = first_value_source.and_then(|source| source.value_declaration);
    let uniform_value_declaration = first_value_declaration.is_some()
        && sources
            .iter()
            .all(|source| source.value_declaration.is_none() || source.value_declaration == first_value_declaration);
    let value_declaration = uniform_value_declaration
        .then_some(first_value_declaration)
        .flatten();
    let parent = value_declaration.and_then(|_| first_value_source.and_then(|source| source.parent));
    let name_type = sources.first().and_then(|source| store.value_symbol_links(source.symbol))
        .and_then(|links| links.name_type);
    let synthetic_kind = if sources.iter().all(|source| {
        store.symbol(source.symbol).is_some_and(|record| {
            record.flags().intersects(SymbolFlags::METHOD)
                || record.check_flags().intersects(CheckFlags::SYNTHETIC_METHOD)
        })
    }) { CheckFlags::SYNTHETIC_METHOD } else { CheckFlags::SYNTHETIC_PROPERTY };
    Ok(SyntheticPropertyPlan {
        optional: sources.iter().any(|source| source.optional),
        readonly: sources.iter().any(|source| source.readonly),
        sources,
        index_types: Vec::new(),
        partial,
        declarations: (!declarations.is_empty()).then_some(declarations),
        value_declaration,
        parent,
        name_type,
        synthetic_kind,
    })
}

fn prepare_cold_query(
    store: &mut CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<PreparedColdQuery, UnionPropertyError> {
    let validate_input = |type_| {
        match plan.array_targets {
            Some(targets) => store.validate_union_constituent_with_array_targets(targets, type_),
            None => store.validate_union_constituent(type_),
        }.map_err(UnionPropertyError::TypeCache)?;
        store.is_template_pattern_literal_type(type_, &mut std::collections::HashSet::new())
            .map_err(|_| UnionPropertyError::UnsupportedPropertyType(type_))?;
        Ok::<_, UnionPropertyError>(())
    };
    match &plan.outcome {
        PropertyOutcome::Missing => {},
        PropertyOutcome::Borrowed(source) => validate_input(source.raw_type)?,
        PropertyOutcome::Synthetic(synthetic) => {
            for source in &synthetic.sources { validate_input(source.raw_type)?; }
            for type_ in &synthetic.index_types { validate_input(*type_)?; }
        }
    }
    let table_count = usize::from(plan.cache.is_none());
    let symbol_count = usize::from(matches!(&plan.outcome, PropertyOutcome::Synthetic(_)));
    if !store.try_reserve_checker_symbol_allocations(symbol_count, table_count)
        || !store.try_reserve_value_symbol_links(symbol_count)
        || !store.try_reserve_deferred_symbol_links(symbol_count)
    {
        return Err(UnionPropertyError::Capacity(plan.union));
    }
    let cache = if plan.cache.is_none() {
        Some(PreparedSymbolTable::new(1).ok_or(UnionPropertyError::Capacity(plan.union))?)
    } else {
        None
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
        .options
        .strict_null_checks;
    let union_operations = match &plan.outcome {
        PropertyOutcome::Missing => 0,
        PropertyOutcome::Borrowed(source) => usize::from(strict && source.optional),
        PropertyOutcome::Synthetic(synthetic) => {
            let optional_operations = if strict {
                synthetic
                    .sources
                    .iter()
                    .filter(|source| source.optional)
                    .count()
            } else {
                0
            };
            optional_operations
                .checked_add(1)
                .ok_or(UnionPropertyError::Capacity(plan.union))?
        }
    };
    let types = if union_operations != 0 {
        Some(match (global_types, session) {
            (Some(globals), Some(session)) => {
                store.prepare_type_query_types_with_global_types_and_session(
                    &[], &[], &[], union_operations, 0, globals, session,
                )?
            }
            (Some(globals), None) => store.prepare_type_query_types_with_global_types(
                &[], &[], &[], union_operations, 0, globals,
            )?,
            (None, _) => store.prepare_type_query_types(&[], &[], &[], union_operations, 0)?,
        })
    } else {
        None
    };
    let count = match &plan.outcome {
        PropertyOutcome::Synthetic(synthetic) => synthetic.sources.len().checked_add(synthetic.index_types.len())
            .ok_or(UnionPropertyError::Capacity(plan.union))?,
        _ => 0,
    };
    let mut effective = Vec::new();
    effective.try_reserve_exact(count).map_err(|_| UnionPropertyError::Capacity(plan.union))?;
    let mut deferred = Vec::new();
    if count > 2 {
        deferred.try_reserve_exact(count).map_err(|_| UnionPropertyError::Capacity(plan.union))?;
    }
    Ok(PreparedColdQuery { cache, types, effective, deferred })
}

fn publish_property_cache(
    store: &mut CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    prepared: PreparedSymbolTable,
) -> SymbolTableId {
    let cache = store.alloc_prepared_symbol_table(prepared);
    assert!(store.set_union_or_intersection_caches(
        plan.union,
        Some(cache),
        plan.cache_without_function_property_augment,
        None,
    ));
    cache
}

fn publish_synthetic_property(
    store: &mut CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    synthetic: &SyntheticPropertyPlan,
    prepared: &mut PreparedTypeQueryTypes,
    global_types: Option<&CanonicalGlobalTypes>,
    effective: Vec<TypeId>,
    mut deferred: Vec<TypeId>,
) -> ResolvedUnionProperty {
    let effective = materialize_effective_types(store, synthetic, prepared, global_types, effective);
    let check_flags = synthetic_check_flags(store, synthetic, effective.as_slice())
        .expect("the selected property pattern types were validated before publication");
    let flags = SymbolFlags::PROPERTY
        | if synthetic.optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let symbol = store.alloc_transient_symbol(flags, plan.name.clone(), check_flags);
    if synthetic.declarations.is_some() || synthetic.value_declaration.is_some() {
        assert!(store.set_symbol_declarations(
            symbol,
            synthetic.declarations.clone(),
            synthetic.value_declaration,
        ));
    }
    if synthetic.parent.is_some() {
        assert!(store.set_symbol_relationships(symbol, None, None, synthetic.parent, None,));
    }
    let type_ = store
        .literal_union_type_with_alias_prepared(effective.as_slice(), None, prepared, global_types)
        .expect("a prepared property union is infallible");
    assert!(store.set_value_symbol_links(
        symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            containing_type: Some(plan.union),
            name_type: synthetic.name_type,
            ..ValueSymbolLinks::default()
        },
    ));
    if effective.values.len() > 2 {
        deferred.extend_from_slice(effective.as_slice());
        assert!(store.set_deferred_symbol_links(symbol, DeferredSymbolLinks {
            parent: Some(plan.union),
            constituents: Some(deferred),
            write_constituents: None,
        }));
    }
    ResolvedUnionProperty {
        symbol,
        type_,
        optional: synthetic.optional,
        readonly: synthetic.readonly,
    }
}

fn materialize_effective_types(
    store: &mut CanonicalTypeMapperStore,
    synthetic: &SyntheticPropertyPlan,
    prepared: &mut PreparedTypeQueryTypes,
    global_types: Option<&CanonicalGlobalTypes>,
    mut values: Vec<TypeId>,
) -> EffectiveTypes {
    let (strict, sentinel) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .expect("a prepared property query retains bootstrap");
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
        )
    };
    for source in &synthetic.sources {
        let type_ = if strict && source.optional {
            store
                .literal_union_type_with_alias_prepared(
                    &[source.raw_type, sentinel], None, prepared, global_types,
                )
                .expect("a prepared optional property union is infallible")
        } else {
            source.raw_type
        };
        values.push(type_);
    }
    values.extend_from_slice(&synthetic.index_types);
    EffectiveTypes {
        values,
    }
}

fn materialize_source_read_type(
    store: &mut CanonicalTypeMapperStore,
    source: SourceProperty,
    prepared: Option<&mut PreparedTypeQueryTypes>,
    global_types: Option<&CanonicalGlobalTypes>,
) -> TypeId {
    let (strict, sentinel) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .expect("a prepared property query retains bootstrap");
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
        )
    };
    if strict && source.optional {
        store
            .literal_union_type_with_alias_prepared(
                &[source.raw_type, sentinel],
                None,
                prepared.expect("a strict optional source prepared its read union"),
                global_types,
            )
            .expect("a prepared optional property read union is infallible")
    } else {
        source.raw_type
    }
}

fn synthetic_check_flags(
    store: &CanonicalTypeMapperStore,
    synthetic: &SyntheticPropertyPlan,
    effective: &[TypeId],
) -> Result<CheckFlags, UnionPropertyError> {
    let mut flags = synthetic.synthetic_kind | CheckFlags::CONTAINS_PUBLIC;
    if synthetic.readonly {
        flags |= CheckFlags::READONLY;
    }
    if synthetic.partial {
        flags |= CheckFlags::READ_PARTIAL;
    }
    if !synthetic.index_types.is_empty() {
        flags |= CheckFlags::WRITE_PARTIAL;
    }
    if effective.len() > 2 {
        flags |= CheckFlags::DEFERRED_TYPE;
    }
    let effective = &effective[..synthetic.sources.len()];
    if effective
        .first()
        .is_some_and(|first| effective.iter().any(|type_| type_ != first))
    {
        flags |= CheckFlags::HAS_NON_UNIFORM_TYPE;
    }
    if effective.iter().any(|type_| {
        store.type_payload(*type_).is_some_and(|record| {
            record
                .flags()
                .intersects(TypeFlags::UNIT | TypeFlags::BOOLEAN)
                || matches!(record.data(), TypeData::Union(union) if union.union.types.iter().all(|constituent| {
                    store.type_payload(*constituent).is_some_and(|record| record.flags().intersects(TypeFlags::UNIT))
                }))
        })
    }) {
        flags |= CheckFlags::HAS_LITERAL_TYPE;
    }
    for type_ in effective {
        if store.is_template_pattern_literal_type(*type_, &mut std::collections::HashSet::new())
            .map_err(|_| UnionPropertyError::UnsupportedPropertyType(*type_))? {
            flags |= CheckFlags::HAS_LITERAL_TYPE;
        }
    }
    if effective.iter().any(|type_| {
        store
            .type_payload(*type_)
            .is_some_and(|record| record.flags().intersects(TypeFlags::NEVER))
    }) {
        flags |= CheckFlags::HAS_NEVER_TYPE;
    }
    Ok(flags)
}

fn validate_cached_property(
    store: &CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    cached: SemanticSymbolId,
) -> Result<Option<ResolvedUnionProperty>, UnionPropertyError> {
    validate_cached_property_raw(store, plan, cached)
        .map(ResolvedRawUnionProperty::readable)
}

fn validate_cached_property_raw(
    store: &CanonicalTypeMapperStore,
    plan: &UnionPropertyPlan,
    cached: SemanticSymbolId,
) -> Result<ResolvedRawUnionProperty, UnionPropertyError> {
    match &plan.outcome {
        PropertyOutcome::Missing => Err(UnionPropertyError::InvalidCache(plan.union)),
        PropertyOutcome::Borrowed(source) => {
            if cached != source.symbol {
                return Err(UnionPropertyError::InvalidCache(plan.union));
            }
            let type_ = cached_source_read_type(store, plan.union, *source, plan.array_targets)?;
            Ok(ResolvedRawUnionProperty {
                property: project_source_property(*source, type_),
                check_flags: store.symbol(source.symbol)
                    .ok_or(UnionPropertyError::InvalidProperty(source.symbol))?.check_flags(),
            })
        }
        PropertyOutcome::Synthetic(synthetic) => {
            let effective =
                cached_effective_types(store, plan.union, synthetic, plan.array_targets)?;
            let expected_type = cached_terminal_union_identity(
                store, plan.union, effective.as_slice(), plan.array_targets,
            )?;
            let expected_flags = SymbolFlags::PROPERTY
                | SymbolFlags::TRANSIENT
                | if synthetic.optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            let record = store
                .symbol(cached)
                .ok_or(UnionPropertyError::InvalidCache(plan.union))?;
            if record.flags() != expected_flags
                || record.check_flags()
                    != synthetic_check_flags(store, synthetic, effective.as_slice())?
                || record.name() != plan.name.as_ref()
                || record.declarations() != synthetic.declarations.as_deref()
                || record.value_declaration() != synthetic.value_declaration
                || record.parent() != synthetic.parent
                || record.members().is_some()
                || record.exports().is_some()
                || record.export_symbol().is_some()
                || store.get_merged_symbol(cached) != Some(cached)
                || store.value_symbol_links(cached)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(expected_type),
                        containing_type: Some(plan.union),
                        name_type: synthetic.name_type,
                        ..ValueSymbolLinks::default()
                    })
            {
                return Err(UnionPropertyError::InvalidCache(plan.union));
            }
            let deferred = store.deferred_symbol_links(cached);
            if if effective.values.len() > 2 {
                deferred.is_none_or(|links| {
                    links.parent != Some(plan.union)
                        || links.constituents.as_deref() != Some(effective.as_slice())
                        || links.write_constituents.is_some()
                })
            } else {
                deferred.is_some()
            } {
                return Err(UnionPropertyError::InvalidCache(plan.union));
            }
            let property = ResolvedUnionProperty {
                symbol: cached,
                type_: expected_type,
                optional: synthetic.optional,
                readonly: synthetic.readonly,
            };
            Ok(ResolvedRawUnionProperty { property, check_flags: record.check_flags() })
        }
    }
}

fn cached_effective_types(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    synthetic: &SyntheticPropertyPlan,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<EffectiveTypes, UnionPropertyError> {
    let (strict, sentinel) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
        )
    };
    let mut values = Vec::new();
    values.try_reserve_exact(synthetic.sources.len().checked_add(synthetic.index_types.len())
        .ok_or(UnionPropertyError::Capacity(union))?)
        .map_err(|_| UnionPropertyError::Capacity(union))?;
    for source in &synthetic.sources {
        let type_ = if strict && source.optional {
            cached_terminal_union_identity(
                store, union, &[source.raw_type, sentinel], array_targets,
            )?
        } else {
            source.raw_type
        };
        values.push(type_);
    }
    values.extend_from_slice(&synthetic.index_types);
    Ok(EffectiveTypes {
        values,
    })
}

fn cached_source_read_type(
    store: &CanonicalTypeMapperStore,
    union: TypeId,
    source: SourceProperty,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, UnionPropertyError> {
    let (strict, sentinel) = {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        (
            bootstrap.options.strict_null_checks,
            bootstrap.undefined_or_missing_type,
        )
    };
    if strict && source.optional {
        cached_terminal_union_identity(store, union, &[source.raw_type, sentinel], array_targets)
    } else {
        Ok(source.raw_type)
    }
}

fn cached_terminal_union_identity(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    inputs: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, UnionPropertyError> {
    store
        .cached_literal_union_type_with_alias(inputs, None, array_targets)
        .map_err(|_| UnionPropertyError::InvalidCache(receiver))?
        .ok_or(UnionPropertyError::InvalidCache(receiver))
}

const fn project_source_property(source: SourceProperty, type_: TypeId) -> ResolvedUnionProperty {
    ResolvedUnionProperty {
        symbol: source.symbol,
        type_,
        optional: source.optional,
        readonly: source.readonly,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_binder::SymbolData;

    use crate::semantic::{
        IntrinsicBootstrapOptions,
        mapper::TypeMapper,
        store::SemanticStore,
        type_records::{TypeRecord, UnionTypeData},
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct State {
        types: usize,
        checker_symbols: usize,
        tables: usize,
        links: [usize; 26],
    }

    fn initialized(options: IntrinsicBootstrapOptions) -> TestStore {
        let mut store = TestStore::new();
        store.initialize_intrinsic_bootstrap(options).unwrap();
        store
    }

    fn state(store: &TestStore) -> State {
        State {
            types: store.type_len(),
            checker_symbols: store.symbol_store().checker_created_symbol_len(),
            tables: store.symbol_store().symbol_table_len(),
            links: store.checker_link_allocated_lengths(),
        }
    }

    fn alloc_property(
        store: &mut TestStore,
        name: &str,
        type_: TypeId,
        optional: bool,
        readonly: bool,
    ) -> SemanticSymbolId {
        let flags = SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let symbol = store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap();
        if readonly {
            assert!(store.set_source_property_readonly(symbol, true));
        }
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        symbol
    }

    fn alloc_object(store: &mut TestStore, properties: &[SemanticSymbolId]) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let members = if properties.is_empty() {
            None
        } else {
            let members = store.alloc_symbol_table();
            for property in properties {
                let name = store.symbol(*property).unwrap().name().to_owned();
                assert_eq!(store.insert_symbol(members, name, *property), Some(None));
            }
            Some(members)
        };
        assert!(store.set_structured_type_members(
            object,
            members,
            (!properties.is_empty()).then(|| properties.to_vec()),
            None,
            None,
            None,
        ));
        object
    }

    fn alloc_union(store: &mut TestStore, left: TypeId, right: TypeId) -> TypeId {
        let mut types = vec![left, right];
        types.sort();
        store.alloc_union_type(ObjectFlags::NONE, types).unwrap()
    }

    fn union_data(store: &TestStore, union: TypeId) -> &UnionTypeData {
        let TypeData::Union(data) = store.type_payload(union).unwrap().data() else {
            panic!("fixture must retain its union payload")
        };
        data
    }

    fn cached_property(store: &TestStore, union: TypeId, name: &str) -> Option<SemanticSymbolId> {
        union_data(store, union)
            .union
            .property_cache
            .and_then(|cache| store.symbol_table(cache))
            .and_then(|cache| cache.get_source(name))
    }

    fn sorted_types(store: &TestStore, mut types: Vec<TypeId>) -> Vec<TypeId> {
        types.sort_by_key(|type_| (store.type_payload(*type_).unwrap().flags(), *type_));
        types.dedup();
        types
    }

    #[test]
    fn distinct_properties_synthesize_exact_flags_type_and_warm_identity() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, true, true);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_ne!(property.symbol, left_property);
        assert_ne!(property.symbol, right_property);
        assert!(property.optional);
        assert!(property.readonly);
        let expected_types = sorted_types(&store, vec![string, bigint]);
        assert_eq!(
            union_data(&store, property.type_).union.types,
            expected_types
        );
        assert_eq!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_union_type(&expected_types),
            Some(property.type_)
        );

        let record = store.symbol(property.symbol).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT
        );
        assert_eq!(
            record.check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY
                | CheckFlags::CONTAINS_PUBLIC
                | CheckFlags::READONLY
                | CheckFlags::HAS_NON_UNIFORM_TYPE
        );
        assert!(record.declarations().is_none());
        assert!(record.value_declaration().is_none());
        assert!(record.parent().is_none());
        assert_eq!(
            store.value_symbol_links(property.symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(property.type_),
                containing_type: Some(union),
                ..ValueSymbolLinks::default()
            })
        );
        assert_eq!(
            cached_property(&store, union, "value"),
            Some(property.symbol)
        );
        let data = union_data(&store, union);
        assert!(
            data.union
                .property_cache_without_function_property_augment
                .is_none()
        );
        assert!(data.union.resolved_properties.is_none());
        let cold = state(&store);
        assert_eq!(cold.types, before.types + 1);
        assert_eq!(cold.checker_symbols, before.checker_symbols + 1);
        assert_eq!(cold.tables, before.tables + 1);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn augmented_cache_query_preserves_and_ignores_noaugment_namespace() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);

        let unrelated = alloc_property(&mut store, "unrelated", string, false, false);
        let noaugment = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(noaugment, EscapedName::source("value"), unrelated),
            Some(None)
        );
        assert!(store.set_union_or_intersection_caches(union, None, Some(noaugment), None,));
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        let data = union_data(&store, union);
        assert_eq!(
            data.union.property_cache_without_function_property_augment,
            Some(noaugment)
        );
        assert_eq!(
            store.symbol_table(noaugment).unwrap().get_source("value"),
            Some(unrelated)
        );
        assert_eq!(
            cached_property(&store, union, "value"),
            Some(property.symbol)
        );
        let cold = state(&store);
        assert_eq!(cold.tables, before.tables + 1);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn distinct_symbols_with_one_effective_type_still_synthesize_without_nonuniform_flag() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", string, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_ne!(property.symbol, left_property);
        assert_ne!(property.symbol, right_property);
        assert_eq!(property.type_, string);
        assert_eq!(
            store.symbol(property.symbol).unwrap().check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC
        );
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols + 1);
        assert_eq!(cold.tables, before.tables + 1);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn strict_optional_read_type_includes_undefined_before_final_union() {
        let mut store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let (undefined, string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let required = alloc_property(&mut store, "value", number, false, false);
        let optional = alloc_property(&mut store, "value", string, true, false);
        let left = alloc_object(&mut store, &[required]);
        let right = alloc_object(&mut store, &[optional]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        let optional_types = sorted_types(&store, vec![undefined, string]);
        let optional_type = store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_union_type(&optional_types)
            .unwrap();
        assert_eq!(
            union_data(&store, optional_type).union.types,
            optional_types
        );
        let expected_types = sorted_types(&store, vec![undefined, string, number]);
        assert_eq!(
            union_data(&store, property.type_).union.types,
            expected_types
        );
        assert!(property.optional);
        assert!(
            store
                .symbol(property.symbol)
                .unwrap()
                .check_flags()
                .contains(CheckFlags::HAS_NON_UNIFORM_TYPE)
        );
        let cold = state(&store);
        assert_eq!(cold.types, before.types + 2);
        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn same_symbol_is_borrowed_after_allocating_only_the_cache_table() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let shared = alloc_property(&mut store, "value", string, true, true);
        let left = alloc_object(&mut store, &[shared]);
        let right = alloc_object(&mut store, &[shared]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);
        let original_links = store.value_symbol_links(shared).unwrap().clone();

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_eq!(
            property,
            ResolvedUnionProperty {
                symbol: shared,
                type_: string,
                optional: true,
                readonly: true,
            }
        );
        assert_eq!(cached_property(&store, union, "value"), Some(shared));
        assert_eq!(store.value_symbol_links(shared), Some(&original_links));
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn strict_optional_same_symbol_borrows_identity_but_projects_effective_read_type() {
        let mut store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let (undefined, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.undefined_type, bootstrap.string_type)
        };
        let shared = alloc_property(&mut store, "value", string, true, false);
        let left = alloc_object(&mut store, &[shared]);
        let right = alloc_object(&mut store, &[shared]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);
        let original_links = store.value_symbol_links(shared).unwrap().clone();

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        let expected_types = sorted_types(&store, vec![undefined, string]);
        assert_eq!(property.symbol, shared);
        assert_eq!(
            store
                .intrinsic_bootstrap()
                .unwrap()
                .cached_union_type(&expected_types),
            Some(property.type_)
        );
        assert_eq!(
            union_data(&store, property.type_).union.types,
            expected_types
        );
        assert!(property.optional);
        assert!(!property.readonly);
        assert_eq!(store.value_symbol_links(shared), Some(&original_links));
        assert_eq!(cached_property(&store, union, "value"), Some(shared));
        let cold = state(&store);
        assert_eq!(cold.types, before.types + 1);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Ok(Some(property))
        );
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn missing_constituent_caches_partial_but_public_lookup_filters_it() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let string = store.intrinsic_bootstrap().unwrap().string_type;
        let source = alloc_property(&mut store, "value", string, false, false);
        let left = alloc_object(&mut store, &[source]);
        let right = alloc_object(&mut store, &[]);
        let union = alloc_union(&mut store, left, right);

        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        let partial = cached_property(&store, union, "value").unwrap();
        let record = store.symbol(partial).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert_eq!(
            record.check_flags(),
            CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC | CheckFlags::READ_PARTIAL
        );
        assert_eq!(
            store.value_symbol_links(partial),
            Some(&ValueSymbolLinks {
                resolved_type: Some(string),
                containing_type: Some(union),
                ..ValueSymbolLinks::default()
            })
        );
        let cold = state(&store);
        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn all_missing_still_allocates_one_empty_cache_table() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let left = alloc_object(&mut store, &[]);
        let right = alloc_object(&mut store, &[]);
        let union = alloc_union(&mut store, left, right);
        let before = state(&store);

        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        assert!(union_data(&store, union).union.property_cache.is_some());
        assert_eq!(cached_property(&store, union, "value"), None);
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);

        assert_eq!(store.resolved_union_property(union, "value"), Ok(None));
        assert_eq!(state(&store), cold);
    }

    #[test]
    fn raw_transient_members_preserve_absent_name_cache_publication_and_replay() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let objects = ["left", "right"].map(|name| {
            let property = store.alloc_transient_symbol(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
                CheckFlags::NONE,
            );
            assert!(store.set_value_symbol_links(
                property,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                },
            ));
            alloc_object(&mut store, &[property])
        });
        let union = alloc_union(&mut store, objects[0], objects[1]);
        assert!(union_data(&store, union).union.property_cache.is_none());
        let before = state(&store);

        assert_eq!(store.resolved_union_property(union, "absent"), Ok(None));
        let cache = union_data(&store, union)
            .union
            .property_cache
            .expect("an absent-name query publishes its empty cache");
        assert!(store.symbol_table(cache).unwrap().is_empty());
        assert_eq!(cached_property(&store, union, "absent"), None);
        let cold = state(&store);
        assert_eq!(cold.types, before.types);
        assert_eq!(cold.checker_symbols, before.checker_symbols);
        assert_eq!(cold.tables, before.tables + 1);
        assert_eq!(cold.links, before.links);
        let published = union_data(&store, union).clone();

        for _ in 0..2 {
            assert_eq!(store.resolved_union_property(union, "absent"), Ok(None));
            assert_eq!(union_data(&store, union), &published);
            assert!(store.symbol_table(cache).unwrap().is_empty());
            assert_eq!(state(&store), cold);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source fixture checks valid and malformed union order.
    fn declared_union_members_keep_canonical_alias_order_and_reject_invalid_order() {
        use ts_ast::{FileId, NodeData};
        use ts_binder::{
            CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
            CanonicalSourceLanguage,
        };

        use crate::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};

        let file = FileId::new(0);
        let parsed = ts_parser::parse_source_file(concat!(
            "type Later = { marker: string };\n",
            "type Earlier = { marker: number };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/declared-union-order.ts\""),
                    CanonicalSourceLanguage::TypeScript,
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
        let aliases = ["Later", "Earlier"].map(|name| {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(id, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    matches!(&parsed.arena.get(alias.name)?.data,
                        NodeData::Identifier(identifier) if identifier.text == name)
                    .then_some(NodeRef::new(parsed.arena.id(), file, id))
                })
                .unwrap();
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            context.store().get_merged_symbol(symbol).unwrap()
        });
        let [later, earlier] =
            aliases.map(|symbol| context.get_declared_type_of_symbol(symbol).unwrap());
        assert!(context.diagnostics().is_empty());
        assert!(
            later < earlier,
            "resolve the later name before the earlier name"
        );

        let store = context.store_mut_for_test();
        for (type_, symbol) in [later, earlier].into_iter().zip(aliases) {
            assert_eq!(
                validate_resolved_declared_property_object(store, type_),
                DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::TypeLiteral)
            );
            let alias = store.type_payload(type_).unwrap().alias().unwrap();
            assert_eq!(store.type_alias(alias).unwrap().symbol(), Some(symbol));
        }
        let union = store.literal_union_type(&[later, earlier], None).unwrap();
        assert_eq!(union_data(store, union).union.types, [earlier, later]);
        assert!(union_data(store, union).union.types[0] > union_data(store, union).union.types[1]);
        for type_ in [later, earlier] {
            assert_eq!(
                classify_union_constituent(store, union, type_, None),
                Ok(UnionMemberMode::Declared)
            );
        }
        assert_eq!(store.validate_cached_union_result(union, None), Ok(()));
        assert!(union_data(store, union).union.property_cache.is_none());
        assert!(
            union_data(store, union)
                .union
                .property_cache_without_function_property_augment
                .is_none()
        );

        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let expected = store.literal_union_type(&[string, number], None).unwrap();
        let property = store
            .resolved_union_property(union, "marker")
            .unwrap()
            .unwrap();
        assert_eq!(property.type_id(), expected);
        assert!(!property.is_optional());
        assert!(!property.is_readonly());
        assert_eq!(
            cached_property(store, union, "marker"),
            Some(property.symbol())
        );
        let published = union_data(store, union).clone();
        let snapshot = |store: &TestStore| {
            (
                state(store),
                store.mapper_len(),
                store.signature_len(),
                store.type_alias_len(),
                store.index_info_len(),
                store.type_predicate_len(),
                store.entity_name_len(),
                store.properties_type_cache_len(),
            )
        };
        let warm = snapshot(store);
        for _ in 0..2 {
            assert_eq!(
                store.resolved_union_property(union, "marker"),
                Ok(Some(property))
            );
            assert_eq!(union_data(store, union), &published);
            assert_eq!(snapshot(store), warm);
        }

        for types in [vec![later, earlier], vec![earlier, earlier]] {
            let invalid = store.alloc_union_type(ObjectFlags::NONE, types).unwrap();
            let invalid_data = union_data(store, invalid).clone();
            let before = snapshot(store);
            for _ in 0..2 {
                assert_eq!(
                    store.validate_cached_union_result(invalid, None),
                    Err(LiteralTypeCacheError::InvalidCachedUnion(invalid))
                );
                assert_eq!(
                    store.resolved_union_property(invalid, "marker"),
                    Err(UnionPropertyError::TypeCache(
                        LiteralTypeCacheError::InvalidCachedUnion(invalid)
                    ))
                );
                assert_eq!(union_data(store, invalid), &invalid_data);
                assert!(union_data(store, invalid).union.property_cache.is_none());
                assert!(
                    union_data(store, invalid)
                        .union
                        .property_cache_without_function_property_augment
                        .is_none()
                );
                assert_eq!(union_data(store, union), &published);
                assert_eq!(snapshot(store), before);
            }
        }
    }

    #[test]
    fn raw_and_declared_type_literal_constituents_reject_whole_union_mode_without_writes() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let declared = store.intrinsic_bootstrap().unwrap().empty_type_literal_type;
        let raw = alloc_object(&mut store, &[]);
        let union = alloc_union(&mut store, declared, raw);
        let before = state(&store);

        assert_eq!(
            store.resolved_union_property(union, "value"),
            Err(UnionPropertyError::UnsupportedUnion(union))
        );
        assert_eq!(state(&store), before);
        assert!(union_data(&store, union).union.property_cache.is_none());
    }

    #[test]
    fn selected_cache_poison_fails_without_scanning_unrelated_entries() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = alloc_union(&mut store, left, right);
        let unrelated = alloc_property(&mut store, "poison", string, false, false);
        let cache = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(cache, EscapedName::source("unrelated"), unrelated),
            Some(None)
        );
        assert!(store.set_union_or_intersection_caches(union, Some(cache), None, None,));

        let property = store
            .resolved_union_property(union, "value")
            .unwrap()
            .unwrap();
        assert_eq!(
            cached_property(&store, union, "value"),
            Some(property.symbol)
        );

        let mut poisoned = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = poisoned.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut poisoned, "value", string, false, false);
        let right_property = alloc_property(&mut poisoned, "value", bigint, false, false);
        let left = alloc_object(&mut poisoned, &[left_property]);
        let right = alloc_object(&mut poisoned, &[right_property]);
        let union = alloc_union(&mut poisoned, left, right);
        let wrong = alloc_property(&mut poisoned, "wrong", string, false, false);
        let cache = poisoned.alloc_symbol_table();
        assert_eq!(
            poisoned.insert_symbol(cache, EscapedName::source("value"), wrong),
            Some(None)
        );
        assert!(poisoned.set_union_or_intersection_caches(union, Some(cache), None, None,));
        let before = state(&poisoned);
        assert_eq!(
            poisoned.resolved_union_property(union, "value"),
            Err(UnionPropertyError::InvalidCache(union))
        );
        assert_eq!(state(&poisoned), before);
    }

    #[test]
    fn malformed_foreign_and_exact_optional_inputs_fail_before_writes() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, bigint) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let left_property = alloc_property(&mut store, "value", string, false, false);
        let right_property = alloc_property(&mut store, "value", bigint, false, false);
        let left = alloc_object(&mut store, &[left_property]);
        let right = alloc_object(&mut store, &[right_property]);
        let union = store
            .alloc_union_type(ObjectFlags::NONE, vec![right, left])
            .unwrap();
        let before = state(&store);
        assert_eq!(
            store.resolved_union_property(union, "value"),
            Err(UnionPropertyError::InvalidUnion(union))
        );
        assert_eq!(state(&store), before);

        let mut foreign = initialized(IntrinsicBootstrapOptions::default());
        let string = foreign.intrinsic_bootstrap().unwrap().string_type;
        let property = alloc_property(&mut foreign, "value", string, false, false);
        let left = alloc_object(&mut foreign, &[property]);
        let right = alloc_object(&mut foreign, &[property]);
        let foreign_union = alloc_union(&mut foreign, left, right);
        let before = state(&store);
        assert_eq!(
            store.resolved_union_property(foreign_union, "value"),
            Err(UnionPropertyError::InvalidUnion(foreign_union))
        );
        assert_eq!(state(&store), before);

        let mut exact = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        });
        let (string, bigint) = {
            let bootstrap = exact.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.bigint_type)
        };
        let required = alloc_property(&mut exact, "value", string, false, false);
        let optional = alloc_property(&mut exact, "value", bigint, true, false);
        let left = alloc_object(&mut exact, &[required]);
        let right = alloc_object(&mut exact, &[optional]);
        let union = alloc_union(&mut exact, left, right);
        let before = state(&exact);
        assert_eq!(
            exact.resolved_union_property(union, "value"),
            Err(UnionPropertyError::UnsupportedExactOptionalProperty(union))
        );
        assert_eq!(state(&exact), before);
    }
}
