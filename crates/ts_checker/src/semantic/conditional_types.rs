//! Canonical conditional-type roots, distribution, and bounded inference.
//!
//! This module follows `getTypeFromConditionalTypeNode`, `getConditionalType`,
//! and `getConditionalTypeInstantiation` in the pinned TypeScript Go checker.
//! Syntax planning and branch resolution remain with the type-node owner.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SymbolFlags};
use xxhash_rust::xxh3::Xxh3;

use super::{
    CanonicalGlobalTypes, ConditionalRootId, RelationUnavailable, SemanticSymbolId, SignatureId,
    SourceFileRef, TypeAliasId, TypeId, TypeMapperId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    callable_sets::StoredCallableSetValidation,
    constraints::{self, ConstraintError},
    declared::{DeclaredTypeError, cached_ordinary_type_parameter_owner, malformed_alias_merge},
    global_types::{GlobalThisMembers, is_global_this_type_candidate},
    instantiate::{
        InstantiationError, InstantiationLimitEventMark, InstantiationLimits, InstantiationSession,
        cached_instantiation_with_vector, canonical_anonymous_union, instantiate_type_with_session,
        instantiate_type_with_vector_and_session,
    },
    interface_heritage::SourceInterfaceHeritageQueryContext,
    links::TypeAliasLinks,
    mapper::CanonicalTypeMapperStore,
    object_members::{StoredDeclaredCallSetValidation, validate_stored_declared_call_set},
    relater::{
        SourceInterfaceHeritageRequest, SourceRelationError, SourceSignatureReturnQuery,
        SourceSignatureReturnRequest,
    },
    signatures::{ElementFlags, SignatureFlags, TupleElementInfo},
    store::SourceNodeParent,
    template_types::{TemplateTypeError, split_first_template_code_point},
    tuple_types::{CanonicalTupleTypeRequest, TupleTypeError},
    type_nodes::{
        CanonicalTypeQueryOptions, ConditionalAliasDeclarationProof,
        ConditionalAliasReferenceProof, GlobalThisMemberValueProof,
        SourceConditionalInputRecoveryProof, SourceConditionalRecoveryProof,
        SourceSignatureReturnProof,
    },
    type_records::{
        CacheHashKey, ConditionalTypeData, LiteralValue, TypeCacheState, TypeData, TypeRecord,
    },
    types::TypeFlags,
};

/// Upstream stops an aliased conditional tail-recursion chain at this count.
pub(super) const CONDITIONAL_TAIL_RECURSION_LIMIT: usize = 1_000;

/// The resolved branches supplied by the type-node query owner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConditionalTypeBranches {
    pub true_type: TypeId,
    pub false_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionalBranchKind {
    True,
    False,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConditionalSourceRoot {
    pub root: ConditionalRootId,
    pub node: NodeRef,
}

/// Identifies the normal input reads that preceded one source evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionalSourceInputQuery<'a> {
    Node {
        node: NodeRef,
        check_type: TypeId,
        extends_type: TypeId,
    },
    Instantiation {
        conditional_type: TypeId,
        type_arguments: &'a [TypeId],
        reference: Option<NodeRef>,
        for_constraint: bool,
    },
}

#[derive(Clone, Debug)]
pub(super) enum SourceConditionalBranchOutcome {
    Complete(TypeId),
    Recovered(SourceConditionalRecoveryProof),
}

impl SourceConditionalBranchOutcome {
    pub(super) const fn type_id(&self) -> TypeId {
        match self {
            Self::Complete(type_) => *type_,
            Self::Recovered(proof) => proof.type_id(),
        }
    }
}

fn missing_source_query() -> DeclaredTypeError {
    super::TypeNodeUnavailable::InvalidPreparedTypeQuery.into()
}

/// Supplies source branch types. The conditional evaluator owns the decision
/// and applies its current mapper after the source query returns.
pub(super) trait ConditionalBranchSource {
    fn preflight(
        &self,
        store: &CanonicalTypeMapperStore,
        conditional: TypeId,
    ) -> Result<(), DeclaredTypeError>;

    fn resolve_branch(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        conditional: TypeId,
        branch: ConditionalBranchKind,
        session: &mut InstantiationSession,
    ) -> Result<TypeId, DeclaredTypeError>;

    fn preflight_root(
        &self,
        _store: &CanonicalTypeMapperStore,
        _root: ConditionalSourceRoot,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn resolve_root_branch(
        &mut self,
        _store: &mut CanonicalTypeMapperStore,
        _root: ConditionalSourceRoot,
        _branch: ConditionalBranchKind,
        _session: &mut InstantiationSession,
    ) -> Result<TypeId, DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn resolve_root_branch_outcome(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        root: ConditionalSourceRoot,
        branch: ConditionalBranchKind,
        session: &mut InstantiationSession,
    ) -> Result<SourceConditionalBranchOutcome, DeclaredTypeError> {
        self.resolve_root_branch(store, root, branch, session)
            .map(SourceConditionalBranchOutcome::Complete)
    }

    fn validate_root_branch_recovery(
        &self,
        _store: &CanonicalTypeMapperStore,
        _proof: &SourceConditionalRecoveryProof,
        _session: &InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn source_branch_recoveries(&self) -> &[SourceConditionalRecoveryProof] {
        &[]
    }

    fn validate_source_conditional_input_recovery(
        &self,
        _store: &CanonicalTypeMapperStore,
        _query: ConditionalSourceInputQuery<'_>,
        _proof: &SourceConditionalInputRecoveryProof,
        _globals: &CanonicalGlobalTypes,
        _session: &InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn retain_source_conditional_recovery(
        &mut self,
        _recovery: ConditionalSourceSemanticRecovery,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn validate_resolved_root_branch(
        &self,
        _store: &CanonicalTypeMapperStore,
        _root: ConditionalSourceRoot,
        _branch: ConditionalBranchKind,
        _result: TypeId,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn source_query_options(&self) -> Option<CanonicalTypeQueryOptions> {
        None
    }

    fn resolve_source_property_object_member(
        &mut self,
        _store: &mut CanonicalTypeMapperStore,
        _receiver: TypeId,
        _member: SemanticSymbolId,
        _session: &mut InstantiationSession,
    ) -> Result<TypeId, ConditionalTypeError> {
        Err(ConditionalTypeError::Declared(missing_source_query()))
    }

    fn prepare_global_this_members(
        &mut self,
        _store: &mut CanonicalTypeMapperStore,
        _receiver: TypeId,
        _session: &mut InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        Ok(())
    }

    fn global_this_members(&self) -> Option<&GlobalThisMembers<'_, '_>> {
        None
    }

    fn resolve_global_this_member(
        &mut self,
        _store: &mut CanonicalTypeMapperStore,
        _receiver: TypeId,
        _member: SemanticSymbolId,
        _session: &mut InstantiationSession,
    ) -> Result<GlobalThisMemberValueProof, DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn validate_global_this_member_value_proof(
        &self,
        _store: &CanonicalTypeMapperStore,
        _proof: &GlobalThisMemberValueProof,
        _globals: &CanonicalGlobalTypes,
        _strict_function_types: Option<bool>,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn source_signature_return_query(&self) -> Option<&dyn SourceSignatureReturnQuery> {
        None
    }

    fn resolve_source_signature_return(
        &mut self,
        _store: &mut CanonicalTypeMapperStore,
        _request: SourceSignatureReturnRequest,
        _origin: Option<&GlobalThisMemberValueProof>,
        _session: &mut InstantiationSession,
    ) -> Result<SourceSignatureReturnProof, DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn validate_source_signature_return_proof(
        &self,
        _store: &CanonicalTypeMapperStore,
        _proof: &SourceSignatureReturnProof,
        _globals: &CanonicalGlobalTypes,
        _strict_function_types: Option<bool>,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn take_completed_source_conditionals(&mut self) -> Vec<ConditionalSourceResultProof> {
        Vec::new()
    }

    fn retain_completed_source_conditional(
        &mut self,
        _proof: ConditionalSourceResultProof,
    ) -> Result<(), DeclaredTypeError> {
        Err(missing_source_query())
    }

    fn completed_source_conditional(
        &self,
        _key: ConditionalQueryKey,
    ) -> Option<&ConditionalSourceResultProof> {
        None
    }

    fn source_interface_heritage_query_context(
        &self,
    ) -> Option<SourceInterfaceHeritageQueryContext<'_>> {
        None
    }

    fn prepare_source_interface_heritage(
        &mut self,
        _store: &mut CanonicalTypeMapperStore,
        _request: SourceInterfaceHeritageRequest,
        _session: &mut InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        Ok(())
    }
}

impl<T: ConditionalBranchSource + ?Sized> super::relater::GlobalThisRelationSource for T {
    type Error = DeclaredTypeError;

    fn source_interface_heritage_query_context(
        &self,
    ) -> Option<SourceInterfaceHeritageQueryContext<'_>> {
        ConditionalBranchSource::source_interface_heritage_query_context(self)
    }

    fn prepare_source_interface_heritage(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        request: SourceInterfaceHeritageRequest,
        session: &mut InstantiationSession,
    ) -> Result<(), Self::Error> {
        ConditionalBranchSource::prepare_source_interface_heritage(self, store, request, session)
    }

    fn prepare_global_this_members(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        receiver: TypeId,
        session: &mut InstantiationSession,
    ) -> Result<(), Self::Error> {
        ConditionalBranchSource::prepare_global_this_members(self, store, receiver, session)
    }

    fn global_this_members(&self) -> Option<&GlobalThisMembers<'_, '_>> {
        ConditionalBranchSource::global_this_members(self)
    }

    fn resolve_global_this_member(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        receiver: TypeId,
        member: SemanticSymbolId,
        session: &mut InstantiationSession,
    ) -> Result<GlobalThisMemberValueProof, Self::Error> {
        ConditionalBranchSource::resolve_global_this_member(self, store, receiver, member, session)
    }

    fn validate_global_this_member_value_proof(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &GlobalThisMemberValueProof,
        globals: &CanonicalGlobalTypes,
        strict_function_types: Option<bool>,
    ) -> Result<(), Self::Error> {
        ConditionalBranchSource::validate_global_this_member_value_proof(
            self,
            store,
            proof,
            globals,
            strict_function_types,
        )
    }

    fn source_signature_return_query(&self) -> Option<&dyn SourceSignatureReturnQuery> {
        ConditionalBranchSource::source_signature_return_query(self)
    }

    fn resolve_source_signature_return(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        request: SourceSignatureReturnRequest,
        origin: Option<&GlobalThisMemberValueProof>,
        session: &mut InstantiationSession,
    ) -> Result<SourceSignatureReturnProof, Self::Error> {
        ConditionalBranchSource::resolve_source_signature_return(
            self, store, request, origin, session,
        )
    }

    fn validate_source_signature_return_proof(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &SourceSignatureReturnProof,
        globals: &CanonicalGlobalTypes,
        strict_function_types: Option<bool>,
    ) -> Result<(), Self::Error> {
        ConditionalBranchSource::validate_source_signature_return_proof(
            self,
            store,
            proof,
            globals,
            strict_function_types,
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalBranchInput {
    Resolved(ConditionalTypeBranches),
    Source(TypeId),
    Root(ConditionalSourceRoot),
}

#[derive(Clone, Copy)]
enum ConditionalValidation<'a> {
    Operational(Option<&'a dyn ConditionalBranchSource>),
    Metadata,
}

impl ConditionalValidation<'_> {
    fn operand(
        self,
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        visiting: &mut HashSet<TypeId>,
        arrays: Option<CanonicalArrayTargets>,
    ) -> Result<(), ConditionalTypeError> {
        match self {
            Self::Operational(source) => {
                validate_conditional_operand_with_source(store, type_, visiting, arrays, source)
            }
            Self::Metadata => validate_owned_type(store, type_),
        }
    }
}

impl ConditionalBranchInput {
    fn get(
        self,
        store: &mut CanonicalTypeMapperStore,
        kind: ConditionalBranchKind,
        session: &mut InstantiationSession,
        source: &mut Option<&mut dyn ConditionalBranchSource>,
    ) -> Result<TypeId, ConditionalTypeError> {
        let mark = session.limit_event_mark();
        let type_ = match self {
            Self::Resolved(branches) => match kind {
                ConditionalBranchKind::True => branches.true_type,
                ConditionalBranchKind::False => branches.false_type,
            },
            Self::Source(conditional) => source
                .as_deref_mut()
                .ok_or(ConditionalTypeError::InvalidConditional(conditional))?
                .resolve_branch(store, conditional, kind, session)
                .map_err(ConditionalTypeError::Declared)?,
            Self::Root(root) => {
                let source = source
                    .as_deref_mut()
                    .ok_or(ConditionalTypeError::InvalidRoot(root.root))?;
                let recovery_mark = source.source_branch_recoveries().len();
                let outcome = source
                    .resolve_root_branch_outcome(store, root, kind, session)
                    .map_err(ConditionalTypeError::Declared)?;
                if let SourceConditionalBranchOutcome::Recovered(proof) = &outcome {
                    let appended = source
                        .source_branch_recoveries()
                        .get(recovery_mark..)
                        .and_then(<[_]>::last);
                    if source.source_query_options().is_none()
                        || proof.source_root() != root
                        || proof.branch() != kind
                        || appended.is_none_or(|appended| {
                            appended.source_root() != root
                                || appended.branch() != kind
                                || appended.type_id() != proof.type_id()
                        })
                    {
                        return Err(ConditionalTypeError::Declared(missing_source_query()));
                    }
                    source
                        .validate_root_branch_recovery(store, proof, session)
                        .map_err(ConditionalTypeError::Declared)?;
                }
                outcome.type_id()
            }
        };
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(recovery);
        }
        validate_owned_type(store, type_)?;
        Ok(type_)
    }
}

/// Fully validated inputs needed to create one canonical conditional root.
#[derive(Clone, Copy, Debug)]
pub(super) struct ConditionalTypeRequest<'a> {
    pub node: NodeRef,
    pub check_type: TypeId,
    pub extends_type: TypeId,
    pub branches: ConditionalTypeBranches,
    pub infer_type_parameters: &'a [TypeId],
    /// A filtered empty list still has an allocated root identity cache.
    pub outer_type_parameters: Option<&'a [TypeId]>,
    pub alias: Option<TypeAliasId>,
}

/// Source syntax supplies branches only after the existing engine demands one.
#[derive(Clone, Copy, Debug)]
pub(super) struct SourceConditionalTypeRequest<'a> {
    pub node: NodeRef,
    pub check_type: TypeId,
    pub extends_type: TypeId,
    pub infer_type_parameters: &'a [TypeId],
    pub outer_type_parameters: Option<&'a [TypeId]>,
    pub alias: Option<TypeAliasId>,
    pub input_recovery: Option<&'a SourceConditionalInputRecoveryProof>,
}

impl<'a> From<ConditionalTypeRequest<'a>> for SourceConditionalTypeRequest<'a> {
    fn from(request: ConditionalTypeRequest<'a>) -> Self {
        Self {
            node: request.node,
            check_type: request.check_type,
            extends_type: request.extends_type,
            infer_type_parameters: request.infer_type_parameters,
            outer_type_parameters: request.outer_type_parameters,
            alias: request.alias,
            input_recovery: None,
        }
    }
}

/// Inputs for one conditional-root instantiation.
#[derive(Clone, Copy, Debug)]
pub(super) struct ConditionalTypeInstantiation<'a> {
    pub conditional_type: TypeId,
    pub type_arguments: &'a [TypeId],
    pub branches: ConditionalTypeBranches,
    pub alias: Option<&'a ConditionalAliasReferenceProof>,
    pub for_constraint: bool,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct SourceConditionalTypeInstantiation<'a> {
    pub conditional_type: TypeId,
    pub type_arguments: &'a [TypeId],
    pub alias: Option<&'a ConditionalAliasReferenceProof>,
    pub for_constraint: bool,
    pub input_recovery: Option<&'a SourceConditionalInputRecoveryProof>,
}

/// Alias inputs stay borrowed until evaluation returns a deferred type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ConditionalAliasIdentity<'a> {
    pub symbol: SemanticSymbolId,
    pub type_arguments: &'a [TypeId],
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RetainedConditionalAlias {
    id: TypeAliasId,
    symbol: SemanticSymbolId,
    type_arguments: Vec<TypeId>,
}

impl RetainedConditionalAlias {
    fn identity(&self) -> ConditionalAliasIdentity<'_> {
        ConditionalAliasIdentity {
            symbol: self.symbol,
            type_arguments: &self.type_arguments,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ConditionalDefinition {
    root: ConditionalRootId,
    node: NodeRef,
    check_type: TypeId,
    extends_type: TypeId,
    is_distributive: bool,
    infer_type_parameters: Vec<TypeId>,
    outer_type_parameters: Option<Vec<TypeId>>,
    alias: Option<RetainedConditionalAlias>,
}

impl ConditionalDefinition {
    fn outer_parameters(&self) -> &[TypeId] {
        self.outer_type_parameters.as_deref().unwrap_or_default()
    }
}

/// Only conditional evaluation can create this immutable production record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalTypeProduction {
    type_: TypeId,
    definition: ConditionalDefinition,
    check_type: TypeId,
    extends_type: TypeId,
    mapper: Option<TypeMapperId>,
    mapped_parameters: Vec<TypeId>,
    type_arguments: Vec<TypeId>,
    alias: Option<RetainedConditionalAlias>,
    alias_reference: Option<NodeRef>,
}

impl ConditionalTypeProduction {
    pub(super) const fn type_id(&self) -> TypeId {
        self.type_
    }

    pub(super) const fn root(&self) -> ConditionalRootId {
        self.definition.root
    }
}

/// The source producer and its complete root arguments, before a second mapper.
/// Only the conditional owner can construct this proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalRemapProjection {
    production: ConditionalTypeProduction,
    arguments: Vec<TypeId>,
}

impl ConditionalRemapProjection {
    pub(super) const fn type_id(&self) -> TypeId {
        self.production.type_
    }

    pub(super) fn parameters(&self) -> &[TypeId] {
        self.production.definition.outer_parameters()
    }

    pub(super) fn arguments(&self) -> &[TypeId] {
        &self.arguments
    }

    pub(super) fn alias(&self) -> Option<ConditionalAliasIdentity<'_>> {
        self.production
            .alias
            .as_ref()
            .map(RetainedConditionalAlias::identity)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionalRemapLookup {
    Cold,
    Hit(TypeId),
    NeedsSourceEvaluation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ConditionalRemapResult {
    Deferred(TypeId),
    Recovered(TypeId),
    NeedsSourceEvaluation,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum ConditionalQueryKey {
    Node(NodeRef),
    Instantiation(ConditionalRootId, CacheHashKey),
    AliasReference(NodeRef),
    AliasDeclaration(SemanticSymbolId),
}

/// Mutable checker caches must agree with this retained query result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalQueryProduction {
    key: ConditionalQueryKey,
    definition: ConditionalDefinition,
    type_arguments: Vec<TypeId>,
    alias: Option<(SemanticSymbolId, Vec<TypeId>)>,
    for_constraint: bool,
    result: TypeId,
    source_declaration: Option<NodeRef>,
    result_alias: Option<RetainedConditionalAlias>,
}

impl ConditionalQueryProduction {
    pub(super) const fn key(&self) -> ConditionalQueryKey {
        self.key
    }

    pub(super) const fn root(&self) -> ConditionalRootId {
        self.definition.root
    }

    pub(super) const fn result(&self) -> TypeId {
        self.result
    }
}

/// Header evidence alone cannot make a source-dependent result ready.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConditionalSourceQueryRequest {
    production: ConditionalQueryProduction,
    identity_edges: Vec<TypeId>,
    requires_source: bool,
}

impl ConditionalSourceQueryRequest {
    pub(super) const fn key(&self) -> ConditionalQueryKey {
        self.production.key
    }

    pub(super) const fn check_type(&self) -> TypeId {
        self.production.definition.check_type
    }

    pub(super) const fn extends_type(&self) -> TypeId {
        self.production.definition.extends_type
    }

    pub(super) fn infer_type_parameters(&self) -> &[TypeId] {
        &self.production.definition.infer_type_parameters
    }

    pub(super) fn outer_type_parameters(&self) -> Option<&[TypeId]> {
        self.production.definition.outer_type_parameters.as_deref()
    }

    pub(super) fn definition_alias(&self) -> Option<TypeAliasId> {
        self.production
            .definition
            .alias
            .as_ref()
            .map(|alias| alias.id)
    }

    pub(super) fn definition_alias_identity(&self) -> Option<ConditionalAliasIdentity<'_>> {
        self.production
            .definition
            .alias
            .as_ref()
            .map(RetainedConditionalAlias::identity)
    }

    pub(super) fn type_arguments(&self) -> &[TypeId] {
        &self.production.type_arguments
    }

    /// This is the saved cache edge, not approval to use the result.
    pub(super) const fn retained_result(&self) -> TypeId {
        self.production.result
    }

    pub(super) const fn source_node(&self) -> NodeRef {
        self.production.definition.node
    }

    /// Alias declarations keep the conditional root of their RHS query.
    pub(super) fn is_alias_declaration_of(&self, source: &Self) -> bool {
        if !matches!(self.production.key, ConditionalQueryKey::AliasDeclaration(_))
            || self.production.source_declaration.is_none()
            || !matches!(
                source.production.key,
                ConditionalQueryKey::Node(_) | ConditionalQueryKey::AliasReference(_)
            )
        {
            return false;
        }
        let mut expected = source.production.clone();
        expected.key = self.production.key;
        expected.type_arguments = self.production.type_arguments.clone();
        expected.alias = None;
        expected.source_declaration = self.production.source_declaration;
        expected.for_constraint = false;
        expected == self.production
    }

    pub(super) fn source_root(&self) -> ConditionalSourceRoot {
        ConditionalSourceRoot {
            root: self.production.definition.root,
            node: self.production.definition.node,
        }
    }

    pub(super) fn identity_type_edges(&self) -> impl Iterator<Item = TypeId> + '_ {
        self.identity_edges.iter().copied()
    }

    pub(super) const fn requires_source_result_proof(&self) -> bool {
        self.requires_source
    }

    pub(super) fn matches_result_proof(&self, proof: &ConditionalSourceResultProof) -> bool {
        self.production == proof.production
    }
}

/// This receipt lives in the active source query, never in the checker store.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ConditionalSourceBranchRead {
    root: ConditionalSourceRoot,
    branch: ConditionalBranchKind,
    result: TypeId,
}

/// The result and only the source reads reached by its evaluation.
#[derive(Clone, Debug)]
pub(super) struct ConditionalSourceResultProof {
    production: ConditionalQueryProduction,
    globals: CanonicalGlobalTypes,
    options: CanonicalTypeQueryOptions,
    branch_reads: Vec<ConditionalSourceBranchRead>,
    member_values: Vec<GlobalThisMemberValueProof>,
    signature_returns: Vec<SourceSignatureReturnProof>,
    nested: Vec<ConditionalSourceResultProof>,
}

impl ConditionalSourceResultProof {
    pub(super) const fn key(&self) -> ConditionalQueryKey {
        self.production.key
    }

    pub(super) const fn result(&self) -> TypeId {
        self.production.result
    }

    pub(super) fn source_root(&self) -> ConditionalSourceRoot {
        ConditionalSourceRoot {
            root: self.production.definition.root,
            node: self.production.definition.node,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum ConditionalSourceResult {
    Complete(ConditionalSourceResultProof),
    Recovered(TypeId),
    SemanticRecovered(ConditionalSourceSemanticRecovery),
}

impl ConditionalSourceResult {
    pub(super) const fn type_id(&self) -> TypeId {
        match self {
            Self::Complete(proof) => proof.result(),
            Self::Recovered(type_) => *type_,
            Self::SemanticRecovered(recovery) => recovery.type_id(),
        }
    }
}

/// The evaluator produced a normal result, but one reached source branch recovered.
/// The dependency record is private and is never published as Complete.
#[derive(Clone, Debug)]
pub(super) struct ConditionalSourceSemanticRecovery {
    result: ConditionalSourceResultProof,
    recoveries: Vec<SourceConditionalRecoveryProof>,
    nested: Vec<ConditionalSourceSemanticRecovery>,
    input_recovery: Option<Box<SourceConditionalInputRecoveryProof>>,
}

impl ConditionalSourceSemanticRecovery {
    pub(super) const fn type_id(&self) -> TypeId {
        self.result.result()
    }

    pub(super) fn source_root(&self) -> ConditionalSourceRoot {
        self.result.source_root()
    }

    pub(super) fn recoveries(&self) -> &[SourceConditionalRecoveryProof] {
        &self.recoveries
    }

    /// Compares the recorded operation. Both proofs still require validation.
    pub(super) fn same_operation(&self, other: &Self) -> bool {
        self.result.production == other.result.production
            && self.result.globals == other.result.globals
            && self.result.options == other.result.options
    }

    #[cfg(test)]
    pub(super) fn input_recovery(&self) -> Option<&SourceConditionalInputRecoveryProof> {
        self.input_recovery.as_deref()
    }
}

struct RecordingConditionalSource<'a> {
    source: &'a mut dyn ConditionalBranchSource,
    globals: &'a CanonicalGlobalTypes,
    options: CanonicalTypeQueryOptions,
    branch_reads: Vec<ConditionalSourceBranchRead>,
    member_values: Vec<GlobalThisMemberValueProof>,
    signature_returns: Vec<SourceSignatureReturnProof>,
    nested: Vec<ConditionalSourceResultProof>,
    recoveries: Vec<SourceConditionalRecoveryProof>,
    semantic_dependencies: Vec<ConditionalSourceSemanticRecovery>,
    input_recovery: Option<SourceConditionalInputRecoveryProof>,
}

impl RecordingConditionalSource<'_> {
    fn validate_options(&self) -> Result<(), DeclaredTypeError> {
        if self.source.source_query_options() == Some(self.options) {
            Ok(())
        } else {
            Err(missing_source_query())
        }
    }

    fn validate_reads(
        &self,
        store: &CanonicalTypeMapperStore,
        session: &InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        if let Some(proof) = &self.input_recovery {
            validate_source_input_recovery(
                store,
                proof.query(),
                proof,
                self.globals,
                session,
                self.source,
            )
            .map_err(|error| match error {
                ConditionalTypeError::Declared(error) => error,
                _ => missing_source_query(),
            })?;
        }
        if let Some(members) = self.source.global_this_members() {
            if members.receiver() != self.globals.global_this_value_type {
                return Err(missing_source_query());
            }
            members.validate(store)?;
        }
        for read in &self.branch_reads {
            self.source.validate_resolved_root_branch(
                store,
                read.root,
                read.branch,
                read.result,
            )?;
        }
        for value in &self.member_values {
            self.source.validate_global_this_member_value_proof(
                store,
                value,
                self.globals,
                self.options.strict_function_types,
            )?;
        }
        for proof in &self.signature_returns {
            self.source.validate_source_signature_return_proof(
                store,
                proof,
                self.globals,
                self.options.strict_function_types,
            )?;
        }
        for nested in &self.nested {
            validate_source_conditional_result(store, nested, self.globals, self.source).map_err(
                |error| match error {
                    ConditionalTypeError::Declared(error) => error,
                    _ => missing_source_query(),
                },
            )?;
        }
        for recovery in &self.recoveries {
            self.source
                .validate_root_branch_recovery(store, recovery, session)?;
        }
        for recovery in &self.semantic_dependencies {
            validate_source_conditional_recovery(
                store,
                recovery,
                self.globals,
                session,
                self.source,
            )
            .map_err(|error| match error {
                ConditionalTypeError::Declared(error) => error,
                _ => missing_source_query(),
            })?;
        }
        Ok(())
    }
}

impl ConditionalBranchSource for RecordingConditionalSource<'_> {
    fn source_branch_recoveries(&self) -> &[SourceConditionalRecoveryProof] {
        &self.recoveries
    }

    fn validate_source_conditional_input_recovery(
        &self,
        store: &CanonicalTypeMapperStore,
        query: ConditionalSourceInputQuery<'_>,
        proof: &SourceConditionalInputRecoveryProof,
        globals: &CanonicalGlobalTypes,
        session: &InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source
            .validate_source_conditional_input_recovery(store, query, proof, globals, session)
    }

    fn validate_root_branch_recovery(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &SourceConditionalRecoveryProof,
        session: &InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source
            .validate_root_branch_recovery(store, proof, session)
    }

    fn retain_source_conditional_recovery(
        &mut self,
        recovery: ConditionalSourceSemanticRecovery,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source
            .retain_source_conditional_recovery(recovery.clone())?;
        self.semantic_dependencies.push(recovery);
        Ok(())
    }

    fn completed_source_conditional(
        &self,
        key: ConditionalQueryKey,
    ) -> Option<&ConditionalSourceResultProof> {
        self.nested
            .iter()
            .rev()
            .find(|proof| proof.key() == key)
            .or_else(|| self.source.completed_source_conditional(key))
    }

    fn retain_completed_source_conditional(
        &mut self,
        proof: ConditionalSourceResultProof,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        if let Some(previous) = self
            .nested
            .iter_mut()
            .find(|item| item.key() == proof.key())
        {
            *previous = proof;
        } else {
            self.nested.push(proof);
        }
        Ok(())
    }

    fn source_interface_heritage_query_context(
        &self,
    ) -> Option<SourceInterfaceHeritageQueryContext<'_>> {
        self.source.source_interface_heritage_query_context()
    }

    fn prepare_source_interface_heritage(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        request: SourceInterfaceHeritageRequest,
        session: &mut InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source
            .prepare_source_interface_heritage(store, request, session)?;
        self.validate_options()?;
        self.nested
            .extend(self.source.take_completed_source_conditionals());
        self.validate_reads(store, session)
    }

    fn preflight(
        &self,
        store: &CanonicalTypeMapperStore,
        conditional: TypeId,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source.preflight(store, conditional)
    }

    fn resolve_branch(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        conditional: TypeId,
        branch: ConditionalBranchKind,
        session: &mut InstantiationSession,
    ) -> Result<TypeId, DeclaredTypeError> {
        self.validate_options()?;
        let result = self
            .source
            .resolve_branch(store, conditional, branch, session)?;
        self.validate_options()?;
        self.nested
            .extend(self.source.take_completed_source_conditionals());
        self.validate_reads(store, session)?;
        Ok(result)
    }

    fn preflight_root(
        &self,
        store: &CanonicalTypeMapperStore,
        root: ConditionalSourceRoot,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source.preflight_root(store, root)
    }

    fn resolve_root_branch(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        root: ConditionalSourceRoot,
        branch: ConditionalBranchKind,
        session: &mut InstantiationSession,
    ) -> Result<TypeId, DeclaredTypeError> {
        self.resolve_root_branch_outcome(store, root, branch, session)
            .map(|outcome| outcome.type_id())
    }

    fn resolve_root_branch_outcome(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        root: ConditionalSourceRoot,
        branch: ConditionalBranchKind,
        session: &mut InstantiationSession,
    ) -> Result<SourceConditionalBranchOutcome, DeclaredTypeError> {
        self.validate_options()?;
        let mark = session.limit_event_mark();
        let recovery_mark = self.source.source_branch_recoveries().len();
        let outcome = self
            .source
            .resolve_root_branch_outcome(store, root, branch, session)?;
        self.validate_options()?;
        self.nested
            .extend(self.source.take_completed_source_conditionals());
        self.validate_reads(store, session)?;
        match &outcome {
            SourceConditionalBranchOutcome::Complete(result)
                if !session.limit_event_occurred_since(mark) =>
            {
                self.source
                    .validate_resolved_root_branch(store, root, branch, *result)?;
                self.branch_reads.push(ConditionalSourceBranchRead {
                    root,
                    branch,
                    result: *result,
                });
            }
            SourceConditionalBranchOutcome::Recovered(proof) => {
                let appended = self
                    .source
                    .source_branch_recoveries()
                    .get(recovery_mark..)
                    .and_then(<[_]>::last);
                if proof.source_root() != root
                    || proof.branch() != branch
                    || appended.is_none_or(|appended| {
                        appended.source_root() != root
                            || appended.branch() != branch
                            || appended.type_id() != proof.type_id()
                    })
                {
                    return Err(missing_source_query());
                }
                self.source
                    .validate_root_branch_recovery(store, proof, session)?;
                self.recoveries.push(proof.clone());
            }
            SourceConditionalBranchOutcome::Complete(_) => {}
        }
        Ok(outcome)
    }

    fn validate_resolved_root_branch(
        &self,
        store: &CanonicalTypeMapperStore,
        root: ConditionalSourceRoot,
        branch: ConditionalBranchKind,
        result: TypeId,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source
            .validate_resolved_root_branch(store, root, branch, result)
    }

    fn source_query_options(&self) -> Option<CanonicalTypeQueryOptions> {
        self.source.source_query_options()
    }

    fn resolve_source_property_object_member(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        receiver: TypeId,
        member: SemanticSymbolId,
        session: &mut InstantiationSession,
    ) -> Result<TypeId, ConditionalTypeError> {
        self.validate_options()?;
        let result = self
            .source
            .resolve_source_property_object_member(store, receiver, member, session)?;
        self.validate_reads(store, session)?;
        Ok(result)
    }

    fn prepare_global_this_members(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        receiver: TypeId,
        session: &mut InstantiationSession,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source
            .prepare_global_this_members(store, receiver, session)?;
        self.validate_reads(store, session)
    }

    fn global_this_members(&self) -> Option<&GlobalThisMembers<'_, '_>> {
        self.source.global_this_members()
    }

    fn resolve_global_this_member(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        receiver: TypeId,
        member: SemanticSymbolId,
        session: &mut InstantiationSession,
    ) -> Result<GlobalThisMemberValueProof, DeclaredTypeError> {
        self.validate_options()?;
        let proof = self
            .source
            .resolve_global_this_member(store, receiver, member, session)?;
        self.validate_reads(store, session)?;
        self.member_values.push(proof.clone());
        Ok(proof)
    }

    fn validate_global_this_member_value_proof(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &GlobalThisMemberValueProof,
        globals: &CanonicalGlobalTypes,
        strict_function_types: Option<bool>,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source.validate_global_this_member_value_proof(
            store,
            proof,
            globals,
            strict_function_types,
        )
    }

    fn source_signature_return_query(&self) -> Option<&dyn SourceSignatureReturnQuery> {
        self.source.source_signature_return_query()
    }

    fn resolve_source_signature_return(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        request: SourceSignatureReturnRequest,
        origin: Option<&GlobalThisMemberValueProof>,
        session: &mut InstantiationSession,
    ) -> Result<SourceSignatureReturnProof, DeclaredTypeError> {
        self.validate_options()?;
        let proof = self
            .source
            .resolve_source_signature_return(store, request, origin, session)?;
        self.validate_reads(store, session)?;
        if proof.request() != request || proof.signature() != request.signature() {
            return Err(missing_source_query());
        }
        self.source.validate_source_signature_return_proof(
            store,
            &proof,
            self.globals,
            self.options.strict_function_types,
        )?;
        self.signature_returns.push(proof.clone());
        Ok(proof)
    }

    fn validate_source_signature_return_proof(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &SourceSignatureReturnProof,
        globals: &CanonicalGlobalTypes,
        strict_function_types: Option<bool>,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_options()?;
        self.source.validate_source_signature_return_proof(
            store,
            proof,
            globals,
            strict_function_types,
        )
    }

    fn take_completed_source_conditionals(&mut self) -> Vec<ConditionalSourceResultProof> {
        self.source.take_completed_source_conditionals()
    }
}

/// Missing dependencies, invalid canonical records, or bounded evaluation.
#[derive(Debug, PartialEq)]
pub(super) enum ConditionalTypeError {
    MissingBootstrap,
    InvalidNode(NodeRef),
    InvalidType(TypeId),
    InvalidTypeParameter(TypeId),
    DuplicateTypeParameter(TypeId),
    InvalidAlias(TypeAliasId),
    InvalidAliasSymbol(SemanticSymbolId),
    Capacity,
    InvalidRoot(ConditionalRootId),
    InvalidConditional(TypeId),
    InvalidMapper(TypeMapperId),
    InvalidInstantiationArity { expected: usize, actual: usize },
    InvalidInstantiationCache(ConditionalRootId),
    InvalidTypeNodeCache(NodeRef),
    InvalidConditionalResolution(TypeId),
    InvalidSignature(SignatureId),
    UnsupportedInference { source: TypeId, target: TypeId },
    TailRecursionLimit { count: usize, limit: usize },
    Instantiation(InstantiationError),
    Declared(DeclaredTypeError),
    Constraint(Box<ConstraintError>),
    Relation(RelationUnavailable),
    Template(TemplateTypeError),
    Tuple(TupleTypeError),
    Union(LiteralTypeCacheError),
}

impl std::fmt::Display for ConditionalTypeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("conditional types require intrinsic checker bootstrap")
            }
            Self::InvalidNode(node) => write!(formatter, "invalid conditional node {node:?}"),
            Self::InvalidType(type_) => write!(formatter, "invalid conditional type {type_:?}"),
            Self::InvalidTypeParameter(type_) => {
                write!(formatter, "invalid conditional type parameter {type_:?}")
            }
            Self::DuplicateTypeParameter(type_) => {
                write!(formatter, "duplicate conditional type parameter {type_:?}")
            }
            Self::InvalidAlias(alias) => write!(formatter, "invalid conditional alias {alias:?}"),
            Self::InvalidAliasSymbol(symbol) => {
                write!(formatter, "invalid conditional alias symbol {symbol:?}")
            }
            Self::Capacity => formatter.write_str("conditional type capacity is unavailable"),
            Self::InvalidRoot(root) => write!(formatter, "invalid conditional root {root:?}"),
            Self::InvalidConditional(type_) => {
                write!(formatter, "type {type_:?} is not a valid conditional")
            }
            Self::InvalidMapper(mapper) => {
                write!(formatter, "invalid conditional type mapper {mapper:?}")
            }
            Self::InvalidInstantiationArity { expected, actual } => write!(
                formatter,
                "conditional instantiation expects {expected} arguments, received {actual}"
            ),
            Self::InvalidInstantiationCache(root) => {
                write!(formatter, "conditional root {root:?} has an invalid cache")
            }
            Self::InvalidTypeNodeCache(node) => {
                write!(formatter, "conditional node {node:?} has an invalid cache")
            }
            Self::InvalidConditionalResolution(type_) => {
                write!(
                    formatter,
                    "conditional type {type_:?} has invalid resolution caches"
                )
            }
            Self::InvalidSignature(signature) => {
                write!(
                    formatter,
                    "conditional inference requires signature {signature:?}"
                )
            }
            Self::UnsupportedInference { source, target } => write!(
                formatter,
                "conditional inference from {source:?} to {target:?} is not supported"
            ),
            Self::TailRecursionLimit { count, limit } => write!(
                formatter,
                "conditional tail recursion count {count} reached limit {limit}"
            ),
            Self::Instantiation(error) => error.fmt(formatter),
            Self::Declared(error) => error.fmt(formatter),
            Self::Constraint(error) => error.fmt(formatter),
            Self::Relation(error) => error.fmt(formatter),
            Self::Template(error) => error.fmt(formatter),
            Self::Tuple(error) => error.fmt(formatter),
            Self::Union(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ConditionalTypeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Instantiation(error) => Some(error),
            Self::Declared(error) => Some(error),
            Self::Constraint(error) => Some(error.as_ref()),
            Self::Relation(error) => Some(error),
            Self::Template(error) => Some(error),
            Self::Tuple(error) => Some(error),
            Self::Union(error) => Some(error),
            _ => None,
        }
    }
}

impl From<InstantiationError> for ConditionalTypeError {
    fn from(error: InstantiationError) -> Self {
        Self::Instantiation(error)
    }
}

impl From<DeclaredTypeError> for ConditionalTypeError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::Declared(error)
    }
}

impl From<RelationUnavailable> for ConditionalTypeError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<ConstraintError> for ConditionalTypeError {
    fn from(error: ConstraintError) -> Self {
        Self::Constraint(Box::new(error))
    }
}

impl From<TemplateTypeError> for ConditionalTypeError {
    fn from(error: TemplateTypeError) -> Self {
        Self::Template(error)
    }
}

impl From<TupleTypeError> for ConditionalTypeError {
    fn from(error: TupleTypeError) -> Self {
        Self::Tuple(error)
    }
}

impl From<LiteralTypeCacheError> for ConditionalTypeError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Union(error)
    }
}

/// Creates the root even when a concrete conditional immediately resolves.
pub(super) fn get_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<TypeId, ConditionalTypeError> {
    validate_request(
        store,
        request,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    if let Some(cached) = store
        .type_node_links(request.node)
        .and_then(|links| links.resolved_type)
    {
        return validate_cached_conditional(
            store,
            request,
            cached,
            global_types.map(CanonicalArrayTargets::from_global_types),
        );
    }
    let query_key = ConditionalQueryKey::Node(request.node);
    if store.conditional_query_production(query_key).is_some() {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    if !store.try_reserve_conditional_productions(0, 1)
        || !store
            .try_reserve_type_node_links(usize::from(store.type_node_links(request.node).is_none()))
    {
        return Err(ConditionalTypeError::Capacity);
    }

    let distributive = matches!(
        store.type_payload(request.check_type).map(TypeRecord::data),
        Some(TypeData::TypeParameter(_))
    );
    let root = store
        .alloc_conditional_root(
            request.node,
            request.check_type,
            request.extends_type,
            distributive,
            (!request.infer_type_parameters.is_empty())
                .then(|| request.infer_type_parameters.to_vec()),
            request.outer_type_parameters.map(<[_]>::to_vec),
            request.alias,
        )
        .ok_or(ConditionalTypeError::InvalidNode(request.node))?;
    let definition = conditional_definition(
        store,
        root,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;

    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let result = evaluate_conditional(
        store,
        root,
        request.branches,
        &[],
        &[],
        global_types,
        false,
        None,
        &mut session,
        0,
    )?;

    if let Some(parameters) = request.outer_type_parameters {
        let key = conditional_type_key(
            store,
            parameters,
            None,
            false,
            global_types.map(CanonicalArrayTargets::from_global_types),
        )?;
        if !store.set_conditional_root_instantiations(
            root,
            TypeCacheState::Allocated(HashMap::from([(key, result)])),
        ) {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
    }
    let proof = ConditionalQueryProduction {
        key: query_key,
        definition,
        type_arguments: request.outer_type_parameters.unwrap_or_default().to_vec(),
        alias: None,
        for_constraint: false,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    validate_query_production(
        store,
        &proof,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }

    let mut links = store
        .type_node_links(request.node)
        .cloned()
        .unwrap_or_default();
    links.resolved_type = Some(result);
    if !store.set_type_node_links(request.node, links) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    Ok(result)
}

/// Evaluates real source branches in the caller's existing query.
pub(super) fn get_type_from_conditional_type_with_source(
    store: &mut CanonicalTypeMapperStore,
    request: SourceConditionalTypeRequest<'_>,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<ConditionalSourceResult, ConditionalTypeError> {
    let mark = session.limit_event_mark();
    let semantic_mark = source_input_recovery_mark(
        store,
        ConditionalSourceInputQuery::Node {
            node: request.node,
            check_type: request.check_type,
            extends_type: request.extends_type,
        },
        request.input_recovery,
        globals,
        session,
        source,
    )?;
    let options = source
        .source_query_options()
        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
    prepare_source_conditional_request(store, request, globals, session, source)?;
    if let Some(recovery) = source_recovery_type(session, mark, &Some(&mut *source))? {
        return Ok(ConditionalSourceResult::Recovered(recovery));
    }
    let (root, definition, cached) = source_conditional_root(store, request, globals, source)?;
    source
        .preflight_root(store, root)
        .map_err(ConditionalTypeError::Declared)?;
    let nested = source.take_completed_source_conditionals();
    let recoveries = source.source_branch_recoveries().to_vec();
    let mut recorded = RecordingConditionalSource {
        source,
        globals,
        options,
        branch_reads: Vec::new(),
        member_values: Vec::new(),
        signature_returns: Vec::new(),
        nested,
        recoveries,
        semantic_dependencies: Vec::new(),
        input_recovery: request.input_recovery.cloned(),
    };
    let result = evaluate_conditional_worker(
        store,
        root.root,
        ConditionalBranchInput::Root(root),
        &[],
        &[],
        Some(globals),
        false,
        None,
        session,
        0,
        &mut Some(&mut recorded),
        cached,
    );
    if session.limit_event_occurred_since(mark) {
        if let Some(recovery) = session.recovery_error_type() {
            return Ok(ConditionalSourceResult::Recovered(recovery));
        }
        result?;
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    let result = result?;
    if let Some(input) = request.input_recovery {
        validate_source_input_recovery(
            store,
            input.query(),
            input,
            globals,
            session,
            recorded.source,
        )?;
    }
    let semantically_recovered =
        validate_source_branch_recoveries_since(store, &recorded, semantic_mark, session)?;
    let production = ConditionalQueryProduction {
        key: ConditionalQueryKey::Node(request.node),
        definition,
        type_arguments: request.outer_type_parameters.unwrap_or_default().to_vec(),
        alias: None,
        for_constraint: false,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    let proof = ConditionalSourceResultProof {
        production,
        globals: globals.clone(),
        options,
        branch_reads: recorded.branch_reads,
        member_values: recorded.member_values,
        signature_returns: recorded.signature_returns,
        nested: recorded.nested,
    };
    if semantically_recovered {
        let recovery = ConditionalSourceSemanticRecovery {
            result: proof,
            recoveries: recorded.recoveries[semantic_mark..].to_vec(),
            nested: recorded.semantic_dependencies,
            input_recovery: recorded.input_recovery.map(Box::new),
        };
        validate_source_conditional_recovery(store, &recovery, globals, session, recorded.source)?;
        return Ok(ConditionalSourceResult::SemanticRecovered(recovery));
    }
    if cached.is_some_and(|cached| cached != result) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    validate_source_result_dependencies(store, &proof, globals, recorded.source)?;
    if cached.is_none() {
        publish_source_conditional_result(store, &proof.production, globals, recorded.source)?;
    }
    validate_source_conditional_result(store, &proof, globals, recorded.source)?;
    Ok(ConditionalSourceResult::Complete(proof))
}

fn prepare_source_conditional_request(
    store: &mut CanonicalTypeMapperStore,
    request: SourceConditionalTypeRequest<'_>,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let options = source
        .source_query_options()
        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
    if let (Some(established), Some(requested)) = (
        store.claimed_strict_function_types(),
        options.strict_function_types,
    ) && established != requested
    {
        return Err(RelationUnavailable::StrictFunctionTypesOptionMismatch {
            established,
            requested,
        }
        .into());
    }
    let result = validate_request_worker(store, request, None, arrays, Some(source));
    let Err(ConditionalTypeError::Relation(RelationUnavailable::GlobalThisMembersDemand {
        receiver,
    })) = result
    else {
        return result;
    };
    source
        .prepare_global_this_members(store, receiver, session)
        .map_err(ConditionalTypeError::Declared)?;
    validate_request_worker(store, request, None, arrays, Some(source))
}

fn source_conditional_root(
    store: &mut CanonicalTypeMapperStore,
    request: SourceConditionalTypeRequest<'_>,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(ConditionalSourceRoot, ConditionalDefinition, Option<TypeId>), ConditionalTypeError> {
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let key = ConditionalQueryKey::Node(request.node);
    if let Some(cached) = store
        .type_node_links(request.node)
        .and_then(|links| links.resolved_type)
    {
        validate_cached_conditional_with_source(store, request, cached, arrays, Some(source))?;
        let definition = store
            .conditional_query_production(key)
            .ok_or(ConditionalTypeError::InvalidTypeNodeCache(request.node))?
            .definition
            .clone();
        return Ok((
            ConditionalSourceRoot {
                root: definition.root,
                node: request.node,
            },
            definition,
            Some(cached),
        ));
    }
    if store.conditional_query_production(key).is_some() {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    if !store.try_reserve_conditional_productions(0, 1)
        || !store
            .try_reserve_type_node_links(usize::from(store.type_node_links(request.node).is_none()))
    {
        return Err(ConditionalTypeError::Capacity);
    }
    let distributive = matches!(
        store.type_payload(request.check_type).map(TypeRecord::data),
        Some(TypeData::TypeParameter(_))
    );
    let root = store
        .alloc_conditional_root(
            request.node,
            request.check_type,
            request.extends_type,
            distributive,
            (!request.infer_type_parameters.is_empty())
                .then(|| request.infer_type_parameters.to_vec()),
            request.outer_type_parameters.map(<[_]>::to_vec),
            request.alias,
        )
        .ok_or(ConditionalTypeError::InvalidNode(request.node))?;
    let definition = conditional_definition_worker(
        store,
        root,
        arrays,
        ConditionalValidation::Operational(Some(source)),
    )?;
    Ok((
        ConditionalSourceRoot {
            root,
            node: request.node,
        },
        definition,
        None,
    ))
}

fn publish_source_conditional_result(
    store: &mut CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    if let Some(parameters) = proof.definition.outer_type_parameters.as_deref() {
        let key =
            conditional_type_key_with_source(store, parameters, None, false, arrays, Some(source))?;
        if !store.set_conditional_root_instantiations(
            proof.definition.root,
            TypeCacheState::Allocated(HashMap::from([(key, proof.result)])),
        ) {
            return Err(ConditionalTypeError::InvalidInstantiationCache(
                proof.definition.root,
            ));
        }
    }
    validate_query_production_with_source(store, proof, arrays, Some(source))?;
    if !store.publish_conditional_query_production(proof.clone()) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.definition.node,
        ));
    }
    let mut links = store
        .type_node_links(proof.definition.node)
        .cloned()
        .unwrap_or_default();
    links.resolved_type = Some(proof.result);
    if !store.set_type_node_links(proof.definition.node, links) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.definition.node,
        ));
    }
    Ok(())
}

fn validate_source_result_dependencies(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalSourceResultProof,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    if globals != &proof.globals || source.source_query_options() != Some(proof.options) {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    source
        .preflight_root(store, proof.source_root())
        .map_err(ConditionalTypeError::Declared)?;
    validate_query_operands_with_source(
        store,
        &proof.production,
        Some(CanonicalArrayTargets::from_global_types(globals)),
        Some(source),
    )?;
    validate_source_result_type(store, proof.result(), globals, source)?;
    for value in &proof.member_values {
        source
            .validate_global_this_member_value_proof(
                store,
                value,
                globals,
                proof.options.strict_function_types,
            )
            .map_err(ConditionalTypeError::Declared)?;
    }
    for return_proof in &proof.signature_returns {
        source
            .validate_source_signature_return_proof(
                store,
                return_proof,
                globals,
                proof.options.strict_function_types,
            )
            .map_err(ConditionalTypeError::Declared)?;
    }
    for read in &proof.branch_reads {
        source
            .validate_resolved_root_branch(store, read.root, read.branch, read.result)
            .map_err(ConditionalTypeError::Declared)?;
    }
    for nested in &proof.nested {
        validate_source_conditional_result(store, nested, globals, source)?;
    }
    Ok(())
}

fn validate_source_result_type(
    store: &CanonicalTypeMapperStore,
    result: TypeId,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    if is_global_this_type_candidate(store, Some(globals), result) {
        let members = source
            .global_this_members()
            .ok_or(RelationUnavailable::InvalidStructuredMembers(result))?;
        if result != globals.global_this_value_type || members.receiver() != result {
            return Err(RelationUnavailable::InvalidStructuredMembers(result).into());
        }
        return members
            .validate(store)
            .map_err(ConditionalTypeError::Declared);
    }
    let arrays = CanonicalArrayTargets::from_global_types(globals);
    // Substitution can return an object instance distinct from its source branch.
    // Its member table and cached values must still match the source mapper.
    store.validate_cached_array_capability_with_array_targets(arrays, result)?;
    validate_conditional_operand_with_source(
        store,
        result,
        &mut HashSet::new(),
        Some(arrays),
        Some(source),
    )
}

pub(super) fn validate_source_conditional_result(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalSourceResultProof,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    if store.conditional_query_production(proof.production.key) != Some(&proof.production) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.production.definition.node,
        ));
    }
    conditional_source_query_request(
        store,
        proof.production.key,
        Some(CanonicalArrayTargets::from_global_types(globals)),
    )?
    .ok_or(ConditionalTypeError::InvalidTypeNodeCache(
        proof.production.definition.node,
    ))?;
    validate_query_production_with_source(
        store,
        &proof.production,
        Some(CanonicalArrayTargets::from_global_types(globals)),
        Some(source),
    )?;
    validate_source_result_dependencies(store, proof, globals, source)
}

fn source_input_recovery_mark(
    store: &CanonicalTypeMapperStore,
    query: ConditionalSourceInputQuery<'_>,
    input: Option<&SourceConditionalInputRecoveryProof>,
    globals: &CanonicalGlobalTypes,
    session: &InstantiationSession,
    source: &dyn ConditionalBranchSource,
) -> Result<usize, ConditionalTypeError> {
    let end = source.source_branch_recoveries().len();
    let Some(proof) = input else {
        return Ok(end);
    };
    if proof.event_end() != end {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    validate_source_input_recovery(store, query, proof, globals, session, source)?;
    Ok(proof.event_start())
}

fn validate_source_input_recovery(
    store: &CanonicalTypeMapperStore,
    query: ConditionalSourceInputQuery<'_>,
    proof: &SourceConditionalInputRecoveryProof,
    globals: &CanonicalGlobalTypes,
    session: &InstantiationSession,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    if proof.query() != query
        || proof.event_start() >= proof.event_end()
        || proof.event_end() > source.source_branch_recoveries().len()
        || proof.aggregates().is_empty()
    {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    // The source owner checks the exact ordered range, actual input reads and
    // every sealed aggregate. Later callbacks may append but cannot replace it.
    source
        .validate_source_conditional_input_recovery(store, query, proof, globals, session)
        .map_err(ConditionalTypeError::Declared)
}

fn validate_source_input_recovery_production(
    store: &CanonicalTypeMapperStore,
    input: &SourceConditionalInputRecoveryProof,
    production: &ConditionalQueryProduction,
    globals: &CanonicalGlobalTypes,
    session: &InstantiationSession,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    validate_source_input_recovery(store, input.query(), input, globals, session, source)?;
    let matches = match input.query() {
        ConditionalSourceInputQuery::Node {
            node,
            check_type,
            extends_type,
        } => {
            production.key == ConditionalQueryKey::Node(node)
                && production.definition.node == node
                && production.definition.check_type == check_type
                && production.definition.extends_type == extends_type
                && production.type_arguments.as_slice() == production.definition.outer_parameters()
                && production.alias.is_none()
                && !production.for_constraint
        }
        ConditionalSourceInputQuery::Instantiation {
            conditional_type,
            type_arguments,
            reference,
            for_constraint,
        } => {
            let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
            let definition = &validated_conditional_production_worker(
                store,
                conditional_type,
                arrays,
                ConditionalValidation::Metadata,
            )?
            .definition;
            let key = if let Some(reference) = reference {
                ConditionalQueryKey::AliasReference(reference)
            } else if definition.outer_type_parameters.is_none()
                || type_arguments == definition.outer_parameters() && !for_constraint
            {
                ConditionalQueryKey::Node(definition.node)
            } else {
                ConditionalQueryKey::Instantiation(
                    definition.root,
                    conditional_type_key_parts(type_arguments, None, for_constraint),
                )
            };
            definition == &production.definition
                && production.key == key
                && production.type_arguments.as_slice() == type_arguments
                && production.for_constraint == for_constraint
        }
    };
    if !matches {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            production.definition.node,
        ));
    }
    Ok(())
}

pub(super) fn validate_source_conditional_recovery(
    store: &CanonicalTypeMapperStore,
    recovery: &ConditionalSourceSemanticRecovery,
    globals: &CanonicalGlobalTypes,
    session: &InstantiationSession,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    if recovery.recoveries.is_empty() {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    let production = &recovery.result.production;
    if let Some(input) = &recovery.input_recovery {
        validate_source_input_recovery_production(
            store, input, production, globals, session, source,
        )?;
    }
    validate_conditional_definition_worker(
        store,
        &production.definition,
        Some(CanonicalArrayTargets::from_global_types(globals)),
        ConditionalValidation::Operational(Some(source)),
    )?;
    if retain_result_alias(store, production.result)? != production.result_alias {
        return Err(ConditionalTypeError::InvalidInstantiationCache(
            production.definition.root,
        ));
    }
    if matches!(
        store.type_payload(production.result).map(TypeRecord::data),
        Some(TypeData::Conditional(_))
    ) {
        validated_conditional_production_worker(
            store,
            production.result,
            Some(CanonicalArrayTargets::from_global_types(globals)),
            ConditionalValidation::Operational(Some(source)),
        )?;
    }
    if let ConditionalQueryKey::Node(node) = production.key {
        validate_conditional_node_link_shape(store, node)?;
    }
    if let ConditionalQueryKey::AliasReference(reference) = production.key
        && let Some((symbol, _)) = production.alias.as_ref()
    {
        validate_conditional_alias_reference_owner(store, reference, *symbol)?;
    }
    for branch in &recovery.recoveries {
        source
            .validate_root_branch_recovery(store, branch, session)
            .map_err(ConditionalTypeError::Declared)?;
    }
    for nested in &recovery.nested {
        validate_source_conditional_recovery(store, nested, globals, session, source)?;
    }
    // This checks the real result and its inputs without requiring or creating
    // a completed source/root cache for the recovered operation.
    validate_source_result_dependencies(store, &recovery.result, globals, source)
}

/// Returns cache identity edges, not permission to use the cached result.
pub(super) fn conditional_source_query_request(
    store: &CanonicalTypeMapperStore,
    key: ConditionalQueryKey,
    arrays: Option<CanonicalArrayTargets>,
) -> Result<Option<ConditionalSourceQueryRequest>, ConditionalTypeError> {
    let Some(proof) = store.conditional_query_production(key) else {
        if let ConditionalQueryKey::Node(node) = key
            && store.source_node_kind(node) == Some(SyntaxKind::ConditionalType)
            && store
                .type_node_links(node)
                .is_some_and(|links| links.resolved_type.is_some())
        {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(node));
        }
        return Ok(None);
    };
    validate_query_production_metadata(store, proof, arrays)?;
    let cached = match key {
        ConditionalQueryKey::Node(node) | ConditionalQueryKey::AliasReference(node) => store
            .type_node_links(node)
            .and_then(|links| links.resolved_type),
        ConditionalQueryKey::AliasDeclaration(symbol) => store
            .type_alias_links(symbol)
            .and_then(|links| links.declared_type),
        ConditionalQueryKey::Instantiation(_, _) => Some(proof.result),
    };
    if cached != Some(proof.result)
        || store.source_node_kind(proof.definition.node) != Some(SyntaxKind::ConditionalType)
        || matches!(key, ConditionalQueryKey::Node(node) if node != proof.definition.node)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.definition.node,
        ));
    }
    let edges = conditional_query_identity_edges(proof);
    let requires_source = conditional_query_requires_source(store, proof, &edges)?;
    Ok(Some(ConditionalSourceQueryRequest {
        production: proof.clone(),
        identity_edges: edges,
        requires_source,
    }))
}

fn conditional_query_identity_edges(proof: &ConditionalQueryProduction) -> Vec<TypeId> {
    let mut edges = vec![proof.definition.check_type, proof.definition.extends_type];
    edges.extend_from_slice(&proof.definition.infer_type_parameters);
    edges.extend_from_slice(proof.definition.outer_parameters());
    edges.extend_from_slice(&proof.type_arguments);
    if let Some((_, arguments)) = &proof.alias {
        edges.extend_from_slice(arguments);
    }
    for alias in [proof.definition.alias.as_ref(), proof.result_alias.as_ref()]
        .into_iter()
        .flatten()
    {
        edges.extend_from_slice(&alias.type_arguments);
    }
    edges
}

fn conditional_query_requires_source(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    edges: &[TypeId],
) -> Result<bool, ConditionalTypeError> {
    let mut visited = HashSet::new();
    let mut requires_source = false;
    for edge in edges.iter().chain(std::iter::once(&proof.result)) {
        requires_source |= conditional_identity_requires_source(store, *edge, &mut visited)?;
    }
    let mut nodes = vec![proof.definition.node];
    let mut visited_nodes = HashSet::new();
    while let Some(node) = nodes.pop() {
        if !visited_nodes.insert(node) {
            continue;
        }
        if let Some(symbol) = store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
            && store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| symbol == bootstrap.global_this_symbol)
        {
            requires_source = true;
        }
        if store.source_node_kind(node) == Some(SyntaxKind::TypeQuery)
            && store
                .type_node_links(node)
                .is_some_and(|links| links.resolved_type.is_some())
        {
            // Follow the real queried value's annotation when its reduced type
            // no longer contains the source conditional's operands.
            for child in store.source_direct_children(node).unwrap_or_default() {
                let Some(symbol) = store
                    .symbol_node_links(child)
                    .and_then(|links| links.resolved_symbol)
                else {
                    continue;
                };
                let symbol = store
                    .get_merged_symbol(symbol)
                    .ok_or(ConditionalTypeError::InvalidTypeNodeCache(node))?;
                let record = store
                    .symbol(symbol)
                    .ok_or(ConditionalTypeError::InvalidTypeNodeCache(node))?;
                for declaration in record.declarations().unwrap_or_default() {
                    if let Some(annotation) = store.source_direct_type_annotation(*declaration) {
                        nodes.push(annotation);
                    }
                }
            }
        }
        for key in [
            ConditionalQueryKey::Node(node),
            ConditionalQueryKey::AliasReference(node),
        ] {
            if let Some(nested) = store.conditional_query_production(key) {
                for edge in [nested.definition.check_type, nested.definition.extends_type]
                    .iter()
                    .chain(&nested.type_arguments)
                {
                    requires_source |=
                        conditional_identity_requires_source(store, *edge, &mut visited)?;
                }
                if nested.definition.node != node {
                    nodes.push(nested.definition.node);
                }
            }
        }
        nodes.extend(store.source_direct_children(node).unwrap_or_default());
    }
    Ok(requires_source)
}

fn conditional_identity_requires_source(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visited: &mut HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    if !visited.insert(type_) {
        return Ok(false);
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    if is_global_this_type_candidate(store, None, type_) {
        return Ok(true);
    }
    let mut edges = Vec::new();
    match record.data() {
        TypeData::Union(data) => edges.extend_from_slice(&data.union.types),
        TypeData::Intersection(data) => edges.extend_from_slice(&data.intersection.types),
        TypeData::TypeReference(data) => {
            edges.extend(data.object.target);
            edges.extend_from_slice(data.resolved_type_arguments.as_deref().unwrap_or_default());
        }
        TypeData::Interface(data) => {
            edges.extend(data.reference.object.target);
            edges.extend_from_slice(
                data.reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
        }
        TypeData::Tuple(data) => {
            edges.extend(data.interface.reference.object.target);
            edges.extend_from_slice(
                data.interface
                    .reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
        }
        TypeData::TypeParameter(data) => edges.extend(data.constraint),
        TypeData::Object(data) => edges.extend(data.target),
        TypeData::Conditional(data) => edges.extend([data.check_type, data.extends_type]),
        TypeData::Index(data) => edges.push(data.target),
        TypeData::IndexedAccess(data) => edges.extend([data.object_type, data.index_type]),
        TypeData::TemplateLiteral(data) => edges.extend_from_slice(&data.types),
        TypeData::StringMapping(data) => edges.push(data.target),
        _ => {}
    }
    if let Some(alias) = record.alias() {
        edges.extend_from_slice(
            store
                .type_alias(alias)
                .ok_or(ConditionalTypeError::InvalidAlias(alias))?
                .type_arguments()
                .unwrap_or_default(),
        );
    }
    if let Some(structured) = record.data().structured() {
        for property in structured.properties.as_deref().unwrap_or_default() {
            edges.extend(
                store
                    .value_symbol_links(*property)
                    .and_then(|links| links.resolved_type),
            );
        }
        for signature in structured.signatures.as_deref().unwrap_or_default() {
            let signature_record = store
                .signature(*signature)
                .ok_or_else(|| invalid_conditional_signature(store, *signature))?;
            edges.extend(signature_record.resolved_return_type());
            edges.extend_from_slice(
                store
                    .callable_signature_parameter_types(*signature)
                    .unwrap_or_default(),
            );
        }
    }
    let mut required = false;
    for edge in edges {
        required |= conditional_identity_requires_source(store, edge, visited)?;
    }
    Ok(required)
}

/// Instantiates a deferred root and distributes a naked parameter over unions.
pub(super) fn get_conditional_type_instantiation(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalTypeInstantiation<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    let source_query = if let Some(source) = request.alias {
        if request.for_constraint
            || !source.matches_request(store, request.conditional_type, request.type_arguments)
        {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(
                source.reference(),
            ));
        }
        let definition = validated_conditional_production(
            store,
            request.conditional_type,
            global_types.map(CanonicalArrayTargets::from_global_types),
        )?
        .definition
        .clone();
        let key = ConditionalQueryKey::AliasReference(source.reference());
        let alias = source
            .identity()
            .map(|alias| (alias.symbol, alias.type_arguments.to_vec()));
        if let Some(proof) = store.conditional_query_production(key) {
            if proof.definition != definition
                || proof.type_arguments != request.type_arguments
                || proof.alias != alias
                || proof.for_constraint
            {
                return Err(ConditionalTypeError::InvalidTypeNodeCache(
                    source.reference(),
                ));
            }
            validate_query_production(
                store,
                proof,
                global_types.map(CanonicalArrayTargets::from_global_types),
            )?;
        } else if !store.try_reserve_conditional_productions(0, 1) {
            return Err(ConditionalTypeError::Capacity);
        }
        Some((key, definition, alias))
    } else {
        None
    };
    let result = get_conditional_type_instantiation_with_tail_count(
        store,
        request,
        global_types,
        session,
        0,
    )?;
    if let Some((key, definition, alias)) = source_query {
        if let Some(proof) = store.conditional_query_production(key) {
            if proof.result != result {
                return Err(ConditionalTypeError::InvalidInstantiationCache(
                    definition.root,
                ));
            }
        } else {
            let proof = ConditionalQueryProduction {
                key,
                definition,
                type_arguments: request.type_arguments.to_vec(),
                alias,
                for_constraint: false,
                result,
                source_declaration: None,
                result_alias: retain_result_alias(store, result)?,
            };
            validate_query_production(
                store,
                &proof,
                global_types.map(CanonicalArrayTargets::from_global_types),
            )?;
            if !store.publish_conditional_query_production(proof) {
                return Err(ConditionalTypeError::InvalidConditional(result));
            }
        }
    }
    Ok(result)
}

/// Evaluates the real root mapping without resolving either branch in advance.
#[allow(clippy::too_many_lines)] // Keep the source proof, caller recovery and exact result publication together.
pub(super) fn get_conditional_type_instantiation_with_source(
    store: &mut CanonicalTypeMapperStore,
    request: SourceConditionalTypeInstantiation<'_>,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<ConditionalSourceResult, ConditionalTypeError> {
    let mark = session.limit_event_mark();
    let semantic_mark = source_input_recovery_mark(
        store,
        ConditionalSourceInputQuery::Instantiation {
            conditional_type: request.conditional_type,
            type_arguments: request.type_arguments,
            reference: request.alias.map(ConditionalAliasReferenceProof::reference),
            for_constraint: request.for_constraint,
        },
        request.input_recovery,
        globals,
        session,
        source,
    )?;
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    let options = source
        .source_query_options()
        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
    let definition = validated_conditional_production_worker(
        store,
        request.conditional_type,
        arrays,
        ConditionalValidation::Metadata,
    )?
    .definition
    .clone();
    prepare_source_conditional_request(
        store,
        SourceConditionalTypeRequest {
            node: definition.node,
            check_type: definition.check_type,
            extends_type: definition.extends_type,
            infer_type_parameters: &definition.infer_type_parameters,
            outer_type_parameters: definition.outer_type_parameters.as_deref(),
            alias: definition.alias.as_ref().map(|alias| alias.id),
            input_recovery: None,
        },
        globals,
        session,
        source,
    )?;
    if let Some(recovery) = source_recovery_type(session, mark, &Some(&mut *source))? {
        return Ok(ConditionalSourceResult::Recovered(recovery));
    }
    prepare_source_conditional_arguments(store, request.type_arguments, globals, session, source)?;
    if let Some(recovery) = source_recovery_type(session, mark, &Some(&mut *source))? {
        return Ok(ConditionalSourceResult::Recovered(recovery));
    }
    if let Some(alias) = request.alias
        && (request.for_constraint
            || !alias.matches_request(store, request.conditional_type, request.type_arguments))
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            alias.reference(),
        ));
    }
    let root = ConditionalSourceRoot {
        root: definition.root,
        node: definition.node,
    };
    source
        .preflight_root(store, root)
        .map_err(ConditionalTypeError::Declared)?;
    let alias = request
        .alias
        .and_then(ConditionalAliasReferenceProof::identity);
    let alias_source = request.alias.and_then(|proof| {
        proof
            .identity()
            .map(|identity| (identity, proof.reference()))
    });
    let nested = source.take_completed_source_conditionals();
    let recoveries = source.source_branch_recoveries().to_vec();
    let mut recorded = RecordingConditionalSource {
        source,
        globals,
        options,
        branch_reads: Vec::new(),
        member_values: Vec::new(),
        signature_returns: Vec::new(),
        nested,
        recoveries,
        semantic_dependencies: Vec::new(),
        input_recovery: request.input_recovery.cloned(),
    };
    let result = instantiate_conditional_root(
        store,
        ConditionalRootInstantiation {
            conditional_type: request.conditional_type,
            type_arguments: request.type_arguments,
            branches: ConditionalBranchInput::Root(root),
            alias,
            alias_source,
            for_constraint: request.for_constraint,
            input_recovery: request.input_recovery,
        },
        Some(globals),
        Some(session),
        0,
        &mut Some(&mut recorded),
    );
    if session.limit_event_occurred_since(mark) {
        if let Some(recovery) = session.recovery_error_type() {
            return Ok(ConditionalSourceResult::Recovered(recovery));
        }
        result?;
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    let result = result?;
    if let Some(input) = request.input_recovery {
        validate_source_input_recovery(
            store,
            input.query(),
            input,
            globals,
            session,
            recorded.source,
        )?;
    }
    let semantically_recovered =
        validate_source_branch_recoveries_since(store, &recorded, semantic_mark, session)?;
    let key = if let Some(alias) = request.alias {
        ConditionalQueryKey::AliasReference(alias.reference())
    } else if definition.outer_type_parameters.is_none()
        || request.type_arguments == definition.outer_parameters() && !request.for_constraint
    {
        ConditionalQueryKey::Node(definition.node)
    } else {
        ConditionalQueryKey::Instantiation(
            definition.root,
            conditional_type_key_with_source(
                store,
                request.type_arguments,
                None,
                request.for_constraint,
                arrays,
                Some(recorded.source),
            )?,
        )
    };
    let proof = ConditionalSourceResultProof {
        production: ConditionalQueryProduction {
            key,
            definition,
            type_arguments: request.type_arguments.to_vec(),
            alias: alias.map(|alias| (alias.symbol, alias.type_arguments.to_vec())),
            for_constraint: request.for_constraint,
            result,
            source_declaration: None,
            result_alias: retain_result_alias(store, result)?,
        },
        globals: globals.clone(),
        options,
        branch_reads: recorded.branch_reads,
        member_values: recorded.member_values,
        signature_returns: recorded.signature_returns,
        nested: recorded.nested,
    };
    if semantically_recovered {
        let recovery = ConditionalSourceSemanticRecovery {
            result: proof,
            recoveries: recorded.recoveries[semantic_mark..].to_vec(),
            nested: recorded.semantic_dependencies,
            input_recovery: recorded.input_recovery.map(Box::new),
        };
        validate_source_conditional_recovery(store, &recovery, globals, session, recorded.source)?;
        return Ok(ConditionalSourceResult::SemanticRecovered(recovery));
    }
    publish_source_query_production(store, &proof, globals, recorded.source)?;
    Ok(ConditionalSourceResult::Complete(proof))
}

fn prepare_source_conditional_arguments(
    store: &mut CanonicalTypeMapperStore,
    arguments: &[TypeId],
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    let validate = |store: &CanonicalTypeMapperStore, source: &dyn ConditionalBranchSource| {
        let mut visited = HashSet::new();
        for argument in arguments {
            validate_conditional_operand_with_source(
                store,
                *argument,
                &mut visited,
                Some(CanonicalArrayTargets::from_global_types(globals)),
                Some(source),
            )?;
        }
        Ok(())
    };
    let result = validate(store, source);
    let Err(ConditionalTypeError::Relation(RelationUnavailable::GlobalThisMembersDemand {
        receiver,
    })) = result
    else {
        return result;
    };
    source
        .prepare_global_this_members(store, receiver, session)
        .map_err(ConditionalTypeError::Declared)?;
    validate(store, source)
}

/// G publishes its exact alias or reference link before using this receipt.
fn publish_source_query_production(
    store: &mut CanonicalTypeMapperStore,
    proof: &ConditionalSourceResultProof,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<(), ConditionalTypeError> {
    let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
    validate_source_result_dependencies(store, proof, globals, source)?;
    validate_query_production_with_source(store, &proof.production, arrays, Some(source))?;
    if let Some(previous) = store.conditional_query_production(proof.production.key) {
        if previous != &proof.production {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(
                proof.production.definition.node,
            ));
        }
        // A prior production must still have its exact public cache edge.
        conditional_source_query_request(store, proof.production.key, arrays)?.ok_or(
            ConditionalTypeError::InvalidTypeNodeCache(proof.production.definition.node),
        )?;
        return Ok(());
    }
    let cached = match proof.production.key {
        ConditionalQueryKey::Node(node) | ConditionalQueryKey::AliasReference(node) => store
            .type_node_links(node)
            .and_then(|links| links.resolved_type),
        ConditionalQueryKey::AliasDeclaration(symbol) => store
            .type_alias_links(symbol)
            .and_then(|links| links.declared_type),
        ConditionalQueryKey::Instantiation(_, _) => None,
    };
    if cached.is_some_and(|cached| cached != proof.result()) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.production.definition.node,
        ));
    }
    if !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
    }
    if !store.publish_conditional_query_production(proof.production.clone()) {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.production.definition.node,
        ));
    }
    Ok(())
}

/// Returns authenticated alias data without evaluating conditional branches.
pub(super) fn conditional_alias_projection(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<Option<ConditionalAliasIdentity<'_>>, ConditionalTypeError> {
    conditional_alias_projection_with_array_targets(store, conditional, None)
}

pub(super) fn conditional_alias_projection_with_array_targets(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<ConditionalAliasIdentity<'_>>, ConditionalTypeError> {
    let proof = validated_conditional_production(store, conditional, array_targets)?;
    Ok(proof.alias.as_ref().map(RetainedConditionalAlias::identity))
}

/// Reconstructs the old mapper without allocating a composite mapper or reading branches.
#[cfg(test)]
pub(super) fn conditional_remap_projection(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    conditional_remap_projection_with_array_targets(store, conditional, None)
}

pub(super) fn conditional_remap_projection_with_array_targets(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    conditional_remap_projection_worker(store, conditional, None, array_targets)
}

pub(super) fn conditional_remap_projection_with_source(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    source: &dyn ConditionalBranchSource,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    conditional_remap_projection_worker(store, conditional, Some(source), array_targets)
}

/// Classifies a direct method-return source without granting instantiation.
pub(super) fn is_signature_conditional_source(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> bool {
    let Some(TypeData::Conditional(data)) = store.type_payload(conditional).map(TypeRecord::data)
    else {
        return false;
    };
    store
        .conditional_root(data.root)
        .and_then(|root| store.source_node_parent(root.node()))
        .is_some_and(|parent| {
            matches!(parent, SourceNodeParent::Parent(parent)
            if store.source_node_kind(parent) == Some(SyntaxKind::MethodSignature))
        })
}

/// Checks every identity after the source-only family classification.
#[cfg(test)]
pub(super) fn conditional_signature_projection(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<(ConditionalRemapProjection, NodeRef), ConditionalTypeError> {
    conditional_signature_projection_with_array_targets(store, conditional, None)
}

pub(super) fn conditional_signature_projection_with_array_targets(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(ConditionalRemapProjection, NodeRef), ConditionalTypeError> {
    let projection = conditional_remap_identity_projection(store, conditional, array_targets)?;
    let declaration = validate_signature_capture_source(store, &projection)?;
    Ok((projection, declaration))
}

/// A copied signature can read an existing root result, but cannot demand a branch.
pub(super) fn cached_signature_conditional_result(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    validate_signature_capture_source(store, projection)?;
    validate_conditional_remap_inputs(store, projection, arguments, None, array_targets)?;
    remap_cached_result(store, projection, arguments, None, array_targets)
}

#[allow(clippy::too_many_lines)] // Prove the complete source scope before a store-only warm read.
fn validate_signature_capture_source(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
) -> Result<NodeRef, ConditionalTypeError> {
    let unsupported = || {
        ConditionalTypeError::Instantiation(InstantiationError::UnsupportedType(
            projection.type_id(),
        ))
    };
    let definition = &projection.production.definition;
    let invalid = || ConditionalTypeError::InvalidTypeNodeCache(definition.node);
    let Some(SourceNodeParent::Parent(declaration)) = store.source_node_parent(definition.node)
    else {
        return Err(unsupported());
    };
    if store.source_node_kind(declaration) != Some(SyntaxKind::MethodSignature)
        || definition.alias.is_some()
        || projection.alias().is_some()
        || projection.production.alias_reference.is_some()
    {
        return Err(unsupported());
    }
    if store.source_direct_type_annotation(declaration) != Some(definition.node) {
        return Err(invalid());
    }
    let method = store
        .source_declaration_symbol(declaration)
        .ok_or_else(invalid)?;
    let (owner, target) = store
        .authenticated_interface_method_owner(method)
        .ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let Some([interface]) = owner_record.declarations() else {
        return Err(unsupported());
    };
    if store.source_node_parent(declaration) != Some(SourceNodeParent::Parent(*interface))
        || store.source_node_kind(*interface) != Some(SyntaxKind::InterfaceDeclaration)
        || !store.source_declaration_belongs_to_symbol(*interface, owner)
        || !store.source_symbol_declarations_match(owner)
    {
        return Err(invalid());
    }
    let signature = store
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .ok_or_else(invalid)?;
    let signature_record = store.signature(signature).ok_or_else(invalid)?;
    let source_value = store
        .value_symbol_links(method)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    let original = store
        .conditional_query_production(ConditionalQueryKey::Node(definition.node))
        .ok_or_else(invalid)?;
    if signature_record.declaration() != Some(declaration)
        || store.interface_method_linked_type(signature) != Some(source_value)
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.resolved_return_type() != Some(original.result)
        || !super::callable_sets::valid_declared_method_type_parameters(
            store,
            signature_record,
            declaration,
        )
    {
        return Err(invalid_conditional_signature(store, signature));
    }

    let mut parameters = Vec::new();
    for scope in [*interface, declaration] {
        let children = store.source_direct_children(scope).ok_or_else(invalid)?;
        for child in children {
            if store.source_node_kind(child) != Some(SyntaxKind::TypeParameter) {
                continue;
            }
            let symbol = store.source_declaration_symbol(child).ok_or_else(invalid)?;
            let type_ = store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .ok_or_else(invalid)?;
            if cached_ordinary_type_parameter_owner(store, type_) != Some(symbol)
                || store.source_node_parent(child) != Some(SourceNodeParent::Parent(scope))
                || parameters.contains(&type_)
            {
                return Err(invalid());
            }
            parameters.push(type_);
        }
    }
    let Some(TypeData::Interface(interface_record)) =
        store.type_payload(target).map(TypeRecord::data)
    else {
        return Err(invalid());
    };
    let own_count = parameters
        .len()
        .checked_sub(signature_record.type_parameters().len())
        .ok_or_else(invalid)?;
    if &parameters[own_count..] != signature_record.type_parameters()
        || interface_record
            .reference
            .resolved_type_arguments
            .as_deref()
            .unwrap_or_default()
            != &parameters[..own_count]
    {
        return Err(invalid());
    }
    if own_count != 0 {
        let reference = super::reference_types::validate_direct_generic_reference(store, target)
            .map_err(|_| invalid())?;
        if reference.target != target || reference.type_arguments != parameters[..own_count] {
            return Err(invalid());
        }
    }
    // This slice keeps every parameter in the two real scopes. A filtered or
    // nested scope needs its own source proof before a store-only replay.
    if parameters.is_empty()
        || definition.outer_parameters() != parameters
        || !definition.infer_type_parameters.is_empty()
    {
        return Err(unsupported());
    }
    let mut ancestor = *interface;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(ancestor) {
            return Err(invalid());
        }
        match store.source_node_parent(ancestor).ok_or_else(invalid)? {
            SourceNodeParent::Root => {
                if store.source_node_kind(ancestor) != Some(SyntaxKind::SourceFile) {
                    return Err(invalid());
                }
                break;
            }
            SourceNodeParent::Parent(parent) => {
                if !matches!(
                    store.source_node_kind(parent),
                    Some(
                        SyntaxKind::SourceFile
                            | SyntaxKind::ModuleBlock
                            | SyntaxKind::ModuleDeclaration
                    )
                ) {
                    return Err(unsupported());
                }
                if store
                    .source_direct_children(parent)
                    .ok_or_else(invalid)?
                    .iter()
                    .filter(|&&child| child == ancestor)
                    .count()
                    != 1
                {
                    return Err(invalid());
                }
                ancestor = parent;
            }
        }
    }
    let mut pending = vec![definition.node];
    let mut visited = HashSet::new();
    while let Some(node) = pending.pop() {
        if !visited.insert(node) {
            return Err(invalid());
        }
        if matches!(
            store.source_node_kind(node),
            Some(SyntaxKind::ThisType | SyntaxKind::TypeQuery | SyntaxKind::TypeParameter)
        ) || node != definition.node
            && store.source_node_kind(node) == Some(SyntaxKind::ConditionalType)
        {
            return Err(unsupported());
        }
        for child in store.source_direct_children(node).ok_or_else(invalid)? {
            if store.source_node_parent(child) != Some(SourceNodeParent::Parent(node)) {
                return Err(invalid());
            }
            pending.push(child);
        }
    }
    Ok(declaration)
}

fn conditional_remap_projection_worker(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    source: Option<&dyn ConditionalBranchSource>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    let projection = conditional_remap_identity_projection_with_source(
        store,
        conditional,
        array_targets,
        source,
    )?;
    if let Some(source) = source {
        source
            .preflight(store, conditional)
            .map_err(ConditionalTypeError::Declared)?;
    } else {
        validate_remap_capture_source(store, &projection)?;
    }
    Ok(projection)
}

fn conditional_remap_identity_projection(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    conditional_remap_identity_projection_with_source(store, conditional, array_targets, None)
}

fn conditional_remap_identity_projection_with_source(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<ConditionalRemapProjection, ConditionalTypeError> {
    let production = validated_conditional_production_worker(
        store,
        conditional,
        array_targets,
        ConditionalValidation::Operational(source),
    )?;
    conditional_snapshot_with_source(store, conditional, array_targets, source)?;
    let definition = &production.definition;
    let node_query = store
        .conditional_query_production(ConditionalQueryKey::Node(definition.node))
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(definition.node))?;
    if node_query.definition != *definition
        || store
            .type_node_links(definition.node)
            .and_then(|links| links.resolved_type)
            != Some(node_query.result)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(definition.node));
    }
    validate_query_production_with_source(store, node_query, array_targets, source)?;
    if let Some(alias) = &definition.alias {
        validate_remap_source_alias_links_with_source(
            store,
            alias.identity(),
            definition,
            array_targets,
            source,
        )?;
    }
    if let Some(reference) = production.alias_reference {
        let origin = store
            .conditional_query_production(ConditionalQueryKey::AliasReference(reference))
            .ok_or(ConditionalTypeError::InvalidTypeNodeCache(reference))?;
        if origin.definition != *definition
            || origin.alias.as_ref().map(|(symbol, _)| *symbol)
                != production.alias.as_ref().map(|alias| alias.symbol)
            || store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type)
                != Some(origin.result)
        {
            return Err(ConditionalTypeError::InvalidTypeNodeCache(reference));
        }
        validate_query_production_with_source(store, origin, array_targets, source)?;
        if let Some((symbol, arguments)) = &origin.alias {
            validate_remap_source_alias_links_with_source(
                store,
                ConditionalAliasIdentity {
                    symbol: *symbol,
                    type_arguments: arguments,
                },
                definition,
                array_targets,
                source,
            )?;
        }
    }
    if !production.mapped_parameters.is_empty()
        && production.mapped_parameters != definition.outer_parameters()
    {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    let arguments = if production.mapped_parameters.is_empty() {
        definition.outer_parameters().to_vec()
    } else {
        production.type_arguments.clone()
    };
    let projection = ConditionalRemapProjection {
        production: production.clone(),
        arguments,
    };
    // A distributed constituent may have no separate root-cache entry. An
    // existing entry or retained query must still pass the complete cache proof.
    remap_cached_result_with_source(
        store,
        &projection,
        projection.arguments(),
        projection.alias(),
        array_targets,
        source,
    )?;
    Ok(projection)
}

/// Validates an existing inline-source result after its owner proved the exact
/// capture vector. This reader cannot construct a projection or evaluate work.
#[cfg(test)]
pub(super) fn cached_source_conditional_instantiation(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
) -> Result<Option<TypeId>, ConditionalTypeError> {
    cached_source_conditional_instantiation_with_array_targets(
        store,
        conditional,
        parameters,
        arguments,
        None,
    )
}

pub(super) fn cached_source_conditional_instantiation_with_array_targets(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let projection = conditional_remap_identity_projection(store, conditional, array_targets)?;
    if projection.parameters() != parameters
        || projection.arguments() != parameters
        || projection.alias().is_some()
        || !projection.production.mapped_parameters.is_empty()
        || parameters.len() != arguments.len()
    {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    let mut visiting = HashSet::new();
    for argument in arguments {
        validate_conditional_operand(store, *argument, &mut visiting, array_targets)?;
    }
    remap_cached_result(store, &projection, arguments, None, array_targets)
}

fn validate_remap_capture_source(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
) -> Result<(), ConditionalTypeError> {
    let unsupported = || {
        ConditionalTypeError::Instantiation(InstantiationError::UnsupportedType(
            projection.type_id(),
        ))
    };
    let invalid = || ConditionalTypeError::InvalidConditional(projection.type_id());
    let definition = &projection.production.definition;
    let Some(alias) = definition.alias.as_ref() else {
        return validate_signature_capture_source(store, projection).map(|_| ());
    };
    let invalid_owner = || ConditionalTypeError::InvalidAliasSymbol(alias.symbol);
    let [declaration] = store
        .symbol(alias.symbol)
        .and_then(|symbol| symbol.declarations())
        .ok_or_else(invalid_owner)?
    else {
        return Err(invalid_owner());
    };
    if declaration.arena != definition.node.arena || declaration.file != definition.node.file {
        return Err(invalid_owner());
    }
    if !remap_alias_scope_is_supported(store, *declaration, alias.symbol)? {
        return Err(unsupported());
    }
    // This source-only header proves every own parameter and excludes enclosing
    // generic scopes. This remapper does not yet revalidate inline capture scopes.
    let header =
        super::object_aliases::property_object_alias_identity_source_header(store, alias.symbol)
            .map_err(|_| invalid_owner())?;
    let mut node = store
        .source_direct_type_annotation(header.alias_declaration)
        .ok_or_else(invalid)?;
    let mut visited = HashSet::new();
    while node != definition.node {
        if !visited.insert(node)
            || store.source_node_kind(node) != Some(SyntaxKind::ParenthesizedType)
        {
            return Err(invalid());
        }
        let children = store.source_direct_children(node).ok_or_else(invalid)?;
        let [child] = children.as_slice() else {
            return Err(invalid());
        };
        if child.arena != node.arena
            || child.file != node.file
            || store.source_node_parent(*child) != Some(SourceNodeParent::Parent(node))
        {
            return Err(invalid());
        }
        node = *child;
    }
    if header.alias_symbol != alias.symbol
        || definition.outer_parameters() != alias.type_arguments
        || header.parameters.len() != definition.outer_parameters().len()
        || header
            .parameters
            .iter()
            .zip(definition.outer_parameters())
            .any(|((_, symbol), parameter)| {
                cached_ordinary_type_parameter_owner(store, *parameter) != Some(*symbol)
            })
    {
        return Err(invalid());
    }
    Ok(())
}

fn remap_alias_scope_is_supported(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    alias: SemanticSymbolId,
) -> Result<bool, ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidAliasSymbol(alias);
    let mut node = declaration;
    let mut visited = HashSet::from([node]);
    let mut unsupported_capture =
        store.source_node_kind(node).ok_or_else(invalid)? != SyntaxKind::TypeAliasDeclaration;
    loop {
        match store.source_node_parent(node).ok_or_else(invalid)? {
            SourceNodeParent::Root => {
                if store.source_node_kind(node) != Some(SyntaxKind::SourceFile)
                    || !store.contains_source_file(SourceFileRef::new(store.id(), node))
                {
                    return Err(invalid());
                }
                return Ok(!unsupported_capture);
            }
            SourceNodeParent::Parent(parent) => {
                if parent.arena != declaration.arena
                    || parent.file != declaration.file
                    || !visited.insert(parent)
                {
                    return Err(invalid());
                }
                let kind = store.source_node_kind(parent).ok_or_else(invalid)?;
                let children = store.source_direct_children(parent).ok_or_else(invalid)?;
                if children.iter().filter(|&&child| child == node).count() != 1
                    || children.iter().any(|child| {
                        child.arena != declaration.arena
                            || child.file != declaration.file
                            || store.source_node_kind(*child).is_none()
                            || store.source_node_parent(*child)
                                != Some(SourceNodeParent::Parent(parent))
                    })
                {
                    return Err(invalid());
                }
                unsupported_capture |= !matches!(
                    kind,
                    SyntaxKind::SourceFile
                        | SyntaxKind::ModuleBlock
                        | SyntaxKind::ModuleDeclaration
                );
                node = parent;
            }
        }
    }
}

fn validate_remap_source_alias_links_with_source(
    store: &CanonicalTypeMapperStore,
    source: ConditionalAliasIdentity<'_>,
    definition: &ConditionalDefinition,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidAliasSymbol(source.symbol);
    let links = store.type_alias_links(source.symbol);
    if links.is_some_and(|links| {
        links.is_constructor_declared_property
            || links
                .type_parameters
                .as_deref()
                .is_some_and(|parameters| parameters != source.type_arguments)
    }) {
        return Err(invalid());
    }
    let Some(proof) =
        store.conditional_query_production(ConditionalQueryKey::AliasDeclaration(source.symbol))
    else {
        // A direct query of the conditional node may precede alias publication.
        // That cold state cannot excuse contradictory installed alias results.
        return if links.is_some_and(|links| {
            links.declared_type.is_some()
                || links
                    .instantiations
                    .as_ref()
                    .is_some_and(|cache| !cache.is_empty())
        }) {
            Err(invalid())
        } else {
            Ok(())
        };
    };
    let links = links.ok_or_else(invalid)?;
    if proof.definition != *definition || links.declared_type != Some(proof.result) {
        return Err(invalid());
    }
    validate_query_production_with_source(store, proof, array_targets, query)?;
    if proof.type_arguments.is_empty() {
        if links
            .instantiations
            .as_ref()
            .is_some_and(|cache| !cache.is_empty())
        {
            return Err(invalid());
        }
    } else if links
        .instantiations
        .as_ref()
        .and_then(|cache| cache.get(&super::declared::type_list_key(&proof.type_arguments)))
        != Some(&proof.result)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_conditional_remap_inputs(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_remap_inputs_worker(
        store,
        projection,
        arguments,
        alias,
        None,
        array_targets,
    )
}

fn validate_conditional_remap_inputs_worker(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    source: Option<&dyn ConditionalBranchSource>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    if conditional_remap_projection_worker(store, projection.type_id(), source, array_targets)?
        != *projection
    {
        return Err(ConditionalTypeError::InvalidConditional(
            projection.type_id(),
        ));
    }
    if arguments.len() != projection.parameters().len() {
        return Err(ConditionalTypeError::InvalidInstantiationArity {
            expected: projection.parameters().len(),
            actual: arguments.len(),
        });
    }
    let mut visiting = HashSet::new();
    for argument in arguments {
        validate_conditional_operand_with_source(
            store,
            *argument,
            &mut visiting,
            array_targets,
            source,
        )?;
    }
    if alias.map(|alias| (alias.symbol, alias.type_arguments.len()))
        != projection
            .alias()
            .map(|alias| (alias.symbol, alias.type_arguments.len()))
    {
        return Err(ConditionalTypeError::InvalidConditional(
            projection.type_id(),
        ));
    }
    if let Some(alias) = alias {
        validate_alias_identity_worker(
            store,
            alias,
            &mut visiting,
            array_targets,
            ConditionalValidation::Operational(source),
        )?;
    }
    // Without a real alias-reference origin the visible alias is the root alias.
    // A remap cannot create a new source alias or claim a new reference node.
    if projection.production.alias_reference.is_none() {
        let expected = mapped_root_alias(
            store,
            projection.production.definition.root,
            projection.parameters(),
            arguments,
        )?;
        if alias
            != expected
                .as_ref()
                .map(|(symbol, arguments)| ConditionalAliasIdentity {
                    symbol: *symbol,
                    type_arguments: arguments,
                })
        {
            return Err(ConditionalTypeError::InvalidConditional(
                projection.type_id(),
            ));
        }
    }
    Ok(())
}

fn remap_query_alias<'a>(
    projection: &ConditionalRemapProjection,
    alias: Option<ConditionalAliasIdentity<'a>>,
) -> Option<ConditionalAliasIdentity<'a>> {
    projection.production.alias_reference.and(alias)
}

fn remap_cache_key(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
) -> Result<CacheHashKey, ConditionalTypeError> {
    let alias = remap_query_alias(projection, alias)
        .map(|alias| {
            store
                .symbol_store()
                .assigned_global_symbol_id(alias.symbol)
                .map(|symbol| (symbol, alias.type_arguments))
                .ok_or(ConditionalTypeError::InvalidAliasSymbol(alias.symbol))
        })
        .transpose()?;
    Ok(conditional_type_key_parts(arguments, alias, false))
}

fn remap_cached_result(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    remap_cached_result_with_source(store, projection, arguments, alias, array_targets, None)
}

fn remap_cached_result_with_source(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let root = projection.production.definition.root;
    let record = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?;
    let cache = match record.instantiations() {
        TypeCacheState::Unallocated if projection.parameters().is_empty() => return Ok(None),
        TypeCacheState::Allocated(cache) if !projection.parameters().is_empty() => cache,
        _ => return Err(ConditionalTypeError::InvalidInstantiationCache(root)),
    };
    let key = remap_cache_key(store, projection, arguments, alias)?;
    let Some(cached) = cache.get(&key).copied() else {
        return if store
            .conditional_query_production(ConditionalQueryKey::Instantiation(root, key))
            .is_some()
        {
            Err(ConditionalTypeError::InvalidInstantiationCache(root))
        } else {
            Ok(None)
        };
    };
    validate_cached_instantiation_with_source(
        store,
        root,
        key,
        cached,
        projection.parameters(),
        arguments,
        remap_query_alias(projection, alias),
        false,
        array_targets,
        source,
    )?;
    Ok(Some(cached))
}

/// A proved subset of Go's `isDeferredType`. A reference such as Array<T>
/// does not qualify merely because one of its arguments is a type parameter.
fn remap_check_stays_deferred(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, ConditionalTypeError> {
    if !visiting.insert(type_) {
        return Err(ConditionalTypeError::InvalidType(type_));
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let result = match record.data() {
        TypeData::TypeParameter(_) => record.flags() == TypeFlags::TYPE_PARAMETER,
        TypeData::Conditional(_) => {
            validated_conditional_production(store, type_, array_targets)?;
            true
        }
        TypeData::IndexedAccess(indexed) => {
            if super::indexed_access_types::cached_deferred_indexed_access_type(
                store,
                indexed.object_type,
                indexed.index_type,
                indexed.access_flags,
            )
            .map_err(ConditionalTypeError::InvalidType)?
                != Some(type_)
            {
                return Err(ConditionalTypeError::InvalidType(type_));
            }
            true
        }
        TypeData::Index(_) => {
            super::keyof_types::validate_generic_keyof_index_type(store, type_)
                .map_err(|_| ConditionalTypeError::InvalidType(type_))?;
            true
        }
        TypeData::Union(data) => data.union.types.iter().try_fold(false, |generic, type_| {
            Ok::<_, ConditionalTypeError>(
                generic | remap_check_stays_deferred(store, *type_, visiting, array_targets)?,
            )
        })?,
        TypeData::Intersection(data) => {
            data.intersection
                .types
                .iter()
                .try_fold(false, |generic, type_| {
                    Ok::<_, ConditionalTypeError>(
                        generic
                            | remap_check_stays_deferred(store, *type_, visiting, array_targets)?,
                    )
                })?
        }
        _ => false,
    };
    visiting.remove(&type_);
    Ok(result)
}

fn remap_can_defer(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    check_type: TypeId,
    extends_type: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, ConditionalTypeError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if [check_type, extends_type]
        .iter()
        .any(|type_| *type_ == bootstrap.error_type || *type_ == bootstrap.wildcard_type)
        || (projection.production.definition.is_distributive
            && type_flags(store, check_type)?.intersects(TypeFlags::UNION | TypeFlags::NEVER))
    {
        return Ok(false);
    }
    remap_check_stays_deferred(store, check_type, &mut HashSet::new(), array_targets)
}

/// Read-only replay checks deferral before accepting even a valid concrete cache hit.
pub(super) fn cached_deferred_conditional_remap(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalRemapLookup, ConditionalTypeError> {
    validate_conditional_remap_inputs(store, projection, arguments, alias, array_targets)?;
    let cached = remap_cached_result(store, projection, arguments, alias, array_targets)?;
    let definition = &projection.production.definition;
    let mapped = [definition.check_type, definition.extends_type].map(|type_| {
        cached_instantiation_with_vector(
            store,
            type_,
            projection.parameters(),
            arguments,
            array_targets,
            None,
        )
    });
    let [check, extends] = mapped;
    let (Some(check), Some(extends)) = (check?, extends?) else {
        return Ok(ConditionalRemapLookup::Cold);
    };
    if !remap_can_defer(store, projection, check, extends, array_targets)? {
        return Ok(ConditionalRemapLookup::NeedsSourceEvaluation);
    }
    if let Some(cached) = cached {
        let result = validated_conditional_production(store, cached, array_targets)?;
        if result.definition != *definition
            || result.check_type != check
            || result.extends_type != extends
            || result
                .alias
                .as_ref()
                .map(RetainedConditionalAlias::identity)
                != alias
        {
            return Err(ConditionalTypeError::InvalidInstantiationCache(
                definition.root,
            ));
        }
        Ok(ConditionalRemapLookup::Hit(cached))
    } else if arguments == projection.arguments() && alias == projection.alias() {
        Ok(ConditionalRemapLookup::Hit(projection.type_id()))
    } else {
        Ok(ConditionalRemapLookup::Cold)
    }
}

/// Reads the existing root production. It never resolves a source branch.
pub(super) fn cached_conditional_remap_with_source(
    store: &CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    validate_conditional_remap_inputs_worker(
        store,
        projection,
        arguments,
        alias,
        Some(source),
        Some(CanonicalArrayTargets::from_global_types(globals)),
    )?;
    let cached = remap_cached_result_with_source(
        store,
        projection,
        arguments,
        alias,
        Some(CanonicalArrayTargets::from_global_types(globals)),
        Some(source),
    )?;
    if source.source_query_options().is_some() {
        let Some(cached) = cached else {
            return Ok(None);
        };
        let key = ConditionalQueryKey::Instantiation(
            projection.production.definition.root,
            remap_cache_key(store, projection, arguments, alias)?,
        );
        let Some(proof) = source.completed_source_conditional(key).or_else(|| {
            (arguments == projection.parameters() && remap_query_alias(projection, alias).is_none())
                .then(|| {
                    source.completed_source_conditional(ConditionalQueryKey::Node(
                        projection.production.definition.node,
                    ))
                })
                .flatten()
        }) else {
            return Ok(None);
        };
        validate_source_conditional_result(store, proof, globals, source)?;
        if proof.result() != cached {
            return Err(ConditionalTypeError::InvalidInstantiationCache(
                projection.production.definition.root,
            ));
        }
        return Ok(Some(cached));
    }
    if cached.is_some() {
        let definition = &projection.production.definition;
        for operand in [definition.check_type, definition.extends_type] {
            if super::instantiate::cached_instantiation_with_vector_and_source(
                store,
                operand,
                projection.parameters(),
                arguments,
                globals,
                source,
            )?
            .is_none()
            {
                return Err(ConditionalTypeError::InvalidInstantiationCache(
                    definition.root,
                ));
            }
        }
    }
    Ok(cached)
}

/// Uses the normal root cache and evaluator with lazily supplied source branches.
pub(super) fn remap_conditional_with_source(
    store: &mut CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<TypeId, ConditionalTypeError> {
    if let Some(cached) =
        cached_conditional_remap_with_source(store, projection, arguments, alias, globals, source)?
    {
        return Ok(cached);
    }
    if let Some(options) = source.source_query_options() {
        return remap_source_conditional_result(
            store, projection, arguments, alias, globals, session, source, options,
        );
    }
    let alias_source = projection
        .production
        .alias_reference
        .zip(alias)
        .map(|(reference, alias)| (alias, reference));
    instantiate_conditional_root(
        store,
        ConditionalRootInstantiation {
            conditional_type: projection.type_id(),
            type_arguments: arguments,
            branches: ConditionalBranchInput::Source(projection.type_id()),
            alias: remap_query_alias(projection, alias),
            alias_source,
            for_constraint: false,
            input_recovery: None,
        },
        Some(globals),
        Some(session),
        0,
        &mut Some(source),
    )
}

#[allow(clippy::too_many_arguments)] // Keeps the active mapper and source proof in one operation.
fn remap_source_conditional_result(
    store: &mut CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
    options: CanonicalTypeQueryOptions,
) -> Result<TypeId, ConditionalTypeError> {
    let semantic_mark = source.source_branch_recoveries().len();
    let root = ConditionalSourceRoot {
        root: projection.production.definition.root,
        node: projection.production.definition.node,
    };
    let nested = source.take_completed_source_conditionals();
    let recoveries = source.source_branch_recoveries().to_vec();
    let mut recorded = RecordingConditionalSource {
        source,
        globals,
        options,
        branch_reads: Vec::new(),
        member_values: Vec::new(),
        signature_returns: Vec::new(),
        nested,
        recoveries,
        semantic_dependencies: Vec::new(),
        input_recovery: None,
    };
    let mark = session.limit_event_mark();
    let result = instantiate_conditional_root(
        store,
        ConditionalRootInstantiation {
            conditional_type: projection.type_id(),
            type_arguments: arguments,
            branches: ConditionalBranchInput::Root(root),
            alias: remap_query_alias(projection, alias),
            alias_source: projection
                .production
                .alias_reference
                .zip(alias)
                .map(|(node, alias)| (alias, node)),
            for_constraint: false,
            input_recovery: None,
        },
        Some(globals),
        Some(session),
        0,
        &mut Some(&mut recorded),
    );
    if session.limit_event_occurred_since(mark) {
        if let Some(recovery) = session.recovery_error_type() {
            return Ok(recovery);
        }
        return result;
    }
    let result = result?;
    let key = ConditionalQueryKey::Instantiation(
        root.root,
        remap_cache_key(store, projection, arguments, alias)?,
    );
    if validate_source_branch_recoveries_since(store, &recorded, semantic_mark, session)? {
        let recovery = ConditionalSourceSemanticRecovery {
            result: ConditionalSourceResultProof {
                production: ConditionalQueryProduction {
                    key,
                    definition: projection.production.definition.clone(),
                    type_arguments: arguments.to_vec(),
                    alias: remap_query_alias(projection, alias)
                        .map(|alias| (alias.symbol, alias.type_arguments.to_vec())),
                    for_constraint: false,
                    result,
                    source_declaration: None,
                    result_alias: retain_result_alias(store, result)?,
                },
                globals: globals.clone(),
                options,
                branch_reads: recorded.branch_reads,
                member_values: recorded.member_values,
                signature_returns: recorded.signature_returns,
                nested: recorded.nested,
            },
            recoveries: recorded.recoveries[semantic_mark..].to_vec(),
            nested: recorded.semantic_dependencies,
            input_recovery: None,
        };
        validate_source_conditional_recovery(store, &recovery, globals, session, recorded.source)?;
        recorded
            .source
            .retain_source_conditional_recovery(recovery)
            .map_err(ConditionalTypeError::Declared)?;
        return Ok(result);
    }
    let production = store
        .conditional_query_production(key)
        .or_else(|| {
            (arguments == projection.parameters() && remap_query_alias(projection, alias).is_none())
                .then(|| store.conditional_query_production(ConditionalQueryKey::Node(root.node)))
                .flatten()
        })
        .ok_or(ConditionalTypeError::InvalidInstantiationCache(root.root))?
        .clone();
    if production.result != result {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root.root));
    }
    let proof = ConditionalSourceResultProof {
        production,
        globals: globals.clone(),
        options,
        branch_reads: recorded.branch_reads,
        member_values: recorded.member_values,
        signature_returns: recorded.signature_returns,
        nested: recorded.nested,
    };
    validate_source_conditional_result(store, &proof, globals, recorded.source)?;
    recorded
        .source
        .retain_completed_source_conditional(proof)
        .map_err(ConditionalTypeError::Declared)?;
    Ok(result)
}

/// Remaps only a still-deferred conditional. Branch nodes and lazy branch caches
/// are not inputs to this operation and remain owned by the source query.
pub(super) fn remap_deferred_conditional_with_session(
    store: &mut CanonicalTypeMapperStore,
    projection: &ConditionalRemapProjection,
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<ConditionalRemapResult, ConditionalTypeError> {
    match cached_deferred_conditional_remap(store, projection, arguments, alias, array_targets)? {
        ConditionalRemapLookup::Hit(type_) => return Ok(ConditionalRemapResult::Deferred(type_)),
        ConditionalRemapLookup::NeedsSourceEvaluation => {
            return Ok(ConditionalRemapResult::NeedsSourceEvaluation);
        }
        ConditionalRemapLookup::Cold => {}
    }
    let definition = &projection.production.definition;
    let mark = session.limit_event_mark();
    let mut operands = Vec::with_capacity(2);
    for operand in [definition.check_type, definition.extends_type] {
        operands.push(instantiate_type_with_vector_and_session(
            store,
            operand,
            projection.parameters(),
            arguments,
            array_targets,
            session,
        )?);
        if session.limit_event_occurred_since(mark)
            && let Some(error) = session.recovery_error_type()
        {
            return Ok(ConditionalRemapResult::Recovered(error));
        }
    }
    let (check_type, extends_type) = (operands[0], operands[1]);
    if !remap_can_defer(store, projection, check_type, extends_type, array_targets)? {
        return Ok(ConditionalRemapResult::NeedsSourceEvaluation);
    }
    // Dependency demand may have completed an existing root entry. Validate it
    // again before reserving or publishing any conditional result.
    if let ConditionalRemapLookup::Hit(cached) =
        cached_deferred_conditional_remap(store, projection, arguments, alias, array_targets)?
    {
        return Ok(ConditionalRemapResult::Deferred(cached));
    }
    let root = definition.root;
    let key = remap_cache_key(store, projection, arguments, alias)?;
    let TypeCacheState::Allocated(cache) = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?
        .instantiations()
    else {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    };
    let mut cache = cache.clone();
    if !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
    }
    let alias_source = projection
        .production
        .alias_reference
        .zip(alias)
        .map(|(reference, alias)| (alias, reference));
    let result = deferred_conditional(
        store,
        root,
        check_type,
        extends_type,
        projection.parameters(),
        arguments,
        alias_source,
        array_targets,
    )?;
    cache.insert(key, result);
    if !store.set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache)) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    let proof = ConditionalQueryProduction {
        key: ConditionalQueryKey::Instantiation(root, key),
        definition: definition.clone(),
        type_arguments: arguments.to_vec(),
        alias: remap_query_alias(projection, alias)
            .map(|alias| (alias.symbol, alias.type_arguments.to_vec())),
        for_constraint: false,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    validate_query_production(store, &proof, array_targets)?;
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    Ok(ConditionalRemapResult::Deferred(result))
}

/// A reduced conditional keeps its source root's alias separate from its result.
pub(super) fn conditional_query_alias(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<TypeAliasId>, ConditionalTypeError> {
    conditional_query_alias_with_array_targets(store, node, None)
}

pub(super) fn conditional_query_alias_with_array_targets(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeAliasId>, ConditionalTypeError> {
    let proof = store
        .conditional_query_production(ConditionalQueryKey::Node(node))
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(node))?;
    validate_query_production(store, proof, array_targets)?;
    if store
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        != Some(proof.result)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(node));
    }
    Ok(proof.definition.alias.as_ref().map(|alias| alias.id))
}

/// Checks a source-derived capture list before a warm query can allocate.
#[cfg(test)]
pub(super) fn validate_conditional_source_captures(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer: Option<&[SemanticSymbolId]>,
    infer: &[SemanticSymbolId],
) -> Result<(), ConditionalTypeError> {
    validate_conditional_source_captures_with_array_targets(store, node, outer, infer, None)
}

pub(super) fn validate_conditional_source_captures_with_array_targets(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer: Option<&[SemanticSymbolId]>,
    infer: &[SemanticSymbolId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_source_captures_worker(store, node, outer, infer, array_targets, false)
}

/// Checks source capture identity without granting use of a cached result.
pub(super) fn validate_conditional_source_capture_metadata(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer: Option<&[SemanticSymbolId]>,
    infer: &[SemanticSymbolId],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_source_captures_worker(store, node, outer, infer, array_targets, true)
}

fn validate_conditional_source_captures_worker(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer: Option<&[SemanticSymbolId]>,
    infer: &[SemanticSymbolId],
    array_targets: Option<CanonicalArrayTargets>,
    metadata_only: bool,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_node_link_shape(store, node)?;
    let invalid = || ConditionalTypeError::InvalidTypeNodeCache(node);
    let cached = store
        .type_node_links(node)
        .and_then(|links| links.resolved_type);
    let proof = store.conditional_query_production(ConditionalQueryKey::Node(node));
    let Some(proof) = proof else {
        return if cached.is_none() {
            Ok(())
        } else {
            Err(invalid())
        };
    };
    if cached != Some(proof.result) {
        return Err(invalid());
    }
    if metadata_only {
        validate_query_production_metadata(store, proof, array_targets)?;
    } else {
        validate_query_production(store, proof, array_targets)?;
    }
    let matches = |types: &[TypeId], symbols: &[SemanticSymbolId]| {
        types.len() == symbols.len()
            && types.iter().zip(symbols).all(|(type_, symbol)| {
                cached_ordinary_type_parameter_owner(store, *type_) == Some(*symbol)
            })
    };
    if proof.definition.outer_type_parameters.is_some() != outer.is_some()
        || !matches(
            proof.definition.outer_parameters(),
            outer.unwrap_or_default(),
        )
        || !matches(&proof.definition.infer_type_parameters, infer)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_conditional_node_link_shape(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), ConditionalTypeError> {
    if store
        .type_node_links(node)
        .is_some_and(|links| links.outer_type_parameters.is_some())
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(node));
    }
    Ok(())
}

pub(super) fn validate_conditional_reference_result(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    result: TypeId,
) -> Result<bool, ConditionalTypeError> {
    validate_conditional_reference_result_with_array_targets(store, reference, result, None)
}

pub(super) fn validate_conditional_reference_result_with_array_targets(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    result: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, ConditionalTypeError> {
    let Some(proof) =
        store.conditional_query_production(ConditionalQueryKey::AliasReference(reference))
    else {
        return Ok(false);
    };
    if proof.result != result {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(reference));
    }
    validate_query_production(store, proof, array_targets)?;
    Ok(true)
}

pub(super) fn record_conditional_alias_declaration(
    store: &mut CanonicalTypeMapperStore,
    source: &ConditionalAliasDeclarationProof,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    if !source.matches_source(store) {
        return Err(ConditionalTypeError::InvalidAliasSymbol(source.symbol()));
    }
    let definition = validated_conditional_production(store, source.result(), array_targets)?
        .definition
        .clone();
    let key = ConditionalQueryKey::AliasDeclaration(source.symbol());
    if let Some(proof) = store.conditional_query_production(key) {
        if proof.result != source.result()
            || proof.definition != definition
            || proof.source_declaration != Some(source.declaration())
            || proof.type_arguments != source.type_parameters()
        {
            return Err(ConditionalTypeError::InvalidAliasSymbol(source.symbol()));
        }
        return validate_query_production(store, proof, array_targets);
    }
    if !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
    }
    let proof = ConditionalQueryProduction {
        key,
        definition,
        type_arguments: source.type_parameters().to_vec(),
        alias: None,
        for_constraint: false,
        result: source.result(),
        source_declaration: Some(source.declaration()),
        result_alias: retain_result_alias(store, source.result())?,
    };
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidAliasSymbol(source.symbol()));
    }
    Ok(())
}

pub(super) fn record_conditional_alias_declaration_with_source(
    store: &mut CanonicalTypeMapperStore,
    declaration: &ConditionalAliasDeclarationProof,
    completed: &ConditionalSourceResultProof,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
    pending_links: Option<TypeAliasLinks>,
) -> Result<ConditionalSourceResultProof, ConditionalTypeError> {
    validate_source_conditional_result(store, completed, globals, source)?;
    let rhs = store.source_direct_type_annotation(declaration.declaration());
    let source_node = match completed.production.key {
        ConditionalQueryKey::Node(node) | ConditionalQueryKey::AliasReference(node) => Some(node),
        _ => None,
    };
    if !declaration.matches_source(store)
        || declaration.result() != completed.result()
        || !source_annotation_reaches_query(store, rhs, source_node, completed.result())
    {
        return Err(ConditionalTypeError::InvalidAliasSymbol(
            declaration.symbol(),
        ));
    }
    let mut proof = completed.clone();
    proof.production.key = ConditionalQueryKey::AliasDeclaration(declaration.symbol());
    proof.production.type_arguments = declaration.type_parameters().to_vec();
    proof.production.alias = None;
    proof.production.source_declaration = Some(declaration.declaration());
    proof.production.for_constraint = false;
    proof.nested.push(completed.clone());
    if let Some(links) = pending_links {
        let symbol = declaration.symbol();
        let invalid = || ConditionalTypeError::InvalidAliasSymbol(symbol);
        if store
            .type_alias_links(symbol)
            .is_some_and(|current| current != &TypeAliasLinks::default())
            || store
                .conditional_query_production(proof.production.key)
                .is_some()
            || links.declared_type != Some(proof.result())
            || links.type_parameters.as_deref().unwrap_or_default() != declaration.type_parameters()
            || links.instantiations.as_ref().is_some_and(|instantiations| {
                instantiations
                    .values()
                    .any(|type_| store.type_payload(*type_).is_none())
            })
        {
            return Err(invalid());
        }
        let arrays = Some(CanonicalArrayTargets::from_global_types(globals));
        validate_alias_identity_worker(
            store,
            ConditionalAliasIdentity {
                symbol,
                type_arguments: declaration.type_parameters(),
            },
            &mut HashSet::new(),
            arrays,
            ConditionalValidation::Operational(Some(source)),
        )?;
        validate_query_operands_with_source(store, &proof.production, arrays, Some(source))?;
        if !store.try_reserve_conditional_productions(0, 1) {
            return Err(ConditionalTypeError::Capacity);
        }
        // Both setters were prechecked. No source callback can see half of the pair.
        if !store.publish_conditional_query_production(proof.production.clone())
            || !store.set_type_alias_links(symbol, links)
        {
            return Err(invalid());
        }
    }
    publish_source_query_production(store, &proof, globals, source)?;
    Ok(proof)
}

fn source_annotation_reaches_query(
    store: &CanonicalTypeMapperStore,
    annotation: Option<NodeRef>,
    query: Option<NodeRef>,
    result: TypeId,
) -> bool {
    let (Some(mut annotation), Some(query)) = (annotation, query) else {
        return false;
    };
    let mut visited = HashSet::new();
    while annotation != query {
        if !visited.insert(annotation)
            || store.source_node_kind(annotation) != Some(SyntaxKind::ParenthesizedType)
            || store.type_node_links(annotation).is_some_and(|links| {
                links.outer_type_parameters.is_some()
                    || links.resolved_type.is_some_and(|type_| type_ != result)
            })
            || store
                .symbol_node_links(annotation)
                .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return false;
        }
        let Some(children) = store.source_direct_children(annotation) else {
            return false;
        };
        let [child] = children.as_slice() else {
            return false;
        };
        if store.source_node_parent(*child) != Some(SourceNodeParent::Parent(annotation)) {
            return false;
        }
        annotation = *child;
    }
    true
}

pub(super) fn record_conditional_alias_reference_with_source(
    store: &mut CanonicalTypeMapperStore,
    reference: &ConditionalAliasReferenceProof,
    type_arguments: &[TypeId],
    completed: &ConditionalSourceResultProof,
    globals: &CanonicalGlobalTypes,
    source: &dyn ConditionalBranchSource,
) -> Result<ConditionalSourceResultProof, ConditionalTypeError> {
    validate_source_conditional_result(store, completed, globals, source)?;
    if !reference.matches_request(store, completed.result(), type_arguments)
        || !type_arguments.is_empty()
        || !completed.production.type_arguments.is_empty()
        || completed.production.for_constraint
        || !matches!(
            completed.production.key,
            ConditionalQueryKey::AliasDeclaration(_)
        )
        || completed.production.source_declaration.is_none()
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            reference.reference(),
        ));
    }
    let mut proof = completed.clone();
    proof.production.key = ConditionalQueryKey::AliasReference(reference.reference());
    proof.production.alias = reference
        .identity()
        .map(|alias| (alias.symbol, alias.type_arguments.to_vec()));
    proof.nested.push(completed.clone());
    publish_source_query_production(store, &proof, globals, source)?;
    Ok(proof)
}

pub(super) fn validate_conditional_alias_declaration_with_array_targets(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    result: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    let Some(proof) =
        store.conditional_query_production(ConditionalQueryKey::AliasDeclaration(symbol))
    else {
        return if matches!(
            store.type_payload(result).map(TypeRecord::data),
            Some(TypeData::Conditional(_))
        ) {
            Err(ConditionalTypeError::InvalidAliasSymbol(symbol))
        } else {
            Ok(())
        };
    };
    if proof.result != result {
        return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
    }
    validate_query_production(store, proof, array_targets)
}

fn retain_conditional_alias(
    store: &CanonicalTypeMapperStore,
    alias: Option<TypeAliasId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<RetainedConditionalAlias>, ConditionalTypeError> {
    retain_conditional_alias_worker(
        store,
        alias,
        array_targets,
        ConditionalValidation::Operational(None),
    )
}

fn retain_conditional_alias_worker(
    store: &CanonicalTypeMapperStore,
    alias: Option<TypeAliasId>,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<Option<RetainedConditionalAlias>, ConditionalTypeError> {
    alias
        .map(|id| {
            let identity = stored_alias_identity(store, id)?;
            validate_alias_identity_worker(
                store,
                identity,
                &mut HashSet::new(),
                array_targets,
                validation,
            )?;
            Ok(RetainedConditionalAlias {
                id,
                symbol: identity.symbol,
                type_arguments: identity.type_arguments.to_vec(),
            })
        })
        .transpose()
}

fn retain_result_alias(
    store: &CanonicalTypeMapperStore,
    result: TypeId,
) -> Result<Option<RetainedConditionalAlias>, ConditionalTypeError> {
    let record = store
        .type_payload(result)
        .ok_or(ConditionalTypeError::InvalidType(result))?;
    record
        .alias()
        .map(|id| {
            let alias = stored_alias_identity(store, id)?;
            Ok(RetainedConditionalAlias {
                id,
                symbol: alias.symbol,
                type_arguments: alias.type_arguments.to_vec(),
            })
        })
        .transpose()
}

fn conditional_definition(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalDefinition, ConditionalTypeError> {
    conditional_definition_worker(
        store,
        root,
        array_targets,
        ConditionalValidation::Operational(None),
    )
}

fn conditional_definition_worker(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<ConditionalDefinition, ConditionalTypeError> {
    let record = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?;
    Ok(ConditionalDefinition {
        root,
        node: record.node(),
        check_type: record.check_type(),
        extends_type: record.extends_type(),
        is_distributive: record.is_distributive(),
        infer_type_parameters: record.infer_type_parameters().unwrap_or_default().to_vec(),
        outer_type_parameters: record.outer_type_parameters().map(<[_]>::to_vec),
        alias: retain_conditional_alias_worker(store, record.alias(), array_targets, validation)?,
    })
}

fn validate_conditional_definition_worker(
    store: &CanonicalTypeMapperStore,
    definition: &ConditionalDefinition,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<(), ConditionalTypeError> {
    if conditional_definition_worker(store, definition.root, array_targets, validation)?
        != *definition
    {
        return Err(ConditionalTypeError::InvalidRoot(definition.root));
    }
    validate_root_alias_worker(
        store,
        definition.node,
        definition.outer_parameters(),
        definition.alias.as_ref().map(|alias| alias.id),
        array_targets,
        validation,
    )
}

fn validated_conditional_production(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<&ConditionalTypeProduction, ConditionalTypeError> {
    validated_conditional_production_worker(
        store,
        conditional,
        array_targets,
        ConditionalValidation::Operational(None),
    )
}

fn validated_conditional_production_worker<'store>(
    store: &'store CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<&'store ConditionalTypeProduction, ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidConditional(conditional);
    let proof = store
        .conditional_type_production(conditional)
        .ok_or_else(invalid)?;
    let record = store.type_payload(conditional).ok_or_else(invalid)?;
    let TypeData::Conditional(data) = record.data() else {
        return Err(invalid());
    };
    // Deferred production currently leaves combined_mapper unset.
    if record.flags() != TypeFlags::CONDITIONAL
        || record.symbol().is_some()
        || data.root != proof.definition.root
        || data.check_type != proof.check_type
        || data.extends_type != proof.extends_type
        || data.mapper != proof.mapper
        || data.combined_mapper.is_some()
        || retain_conditional_alias_worker(store, record.alias(), array_targets, validation)?
            != proof.alias
    {
        return Err(invalid());
    }
    validate_conditional_definition_worker(store, &proof.definition, array_targets, validation)?;
    if let Some(reference) = proof.alias_reference {
        let alias = proof.alias.as_ref().ok_or_else(invalid)?;
        validate_conditional_alias_reference_owner(store, reference, alias.symbol)?;
    }
    if let Some(mapper) = proof.mapper {
        if store.type_mapper_has_exact_endpoints(
            mapper,
            &proof.mapped_parameters,
            &proof.type_arguments,
        ) != Some(true)
        {
            return Err(ConditionalTypeError::InvalidMapper(mapper));
        }
    } else if proof.mapped_parameters != proof.type_arguments {
        return Err(invalid());
    }
    Ok(proof)
}

fn validate_query_production(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_query_production_with_source(store, proof, array_targets, None)
}

fn validate_query_production_with_source(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    validate_query_production_worker(
        store,
        proof,
        array_targets,
        ConditionalValidation::Operational(source),
    )
}

fn validate_query_production_metadata(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_query_production_worker(store, proof, array_targets, ConditionalValidation::Metadata)
}

fn validate_query_production_worker(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_definition_worker(store, &proof.definition, array_targets, validation)?;
    if let ConditionalQueryKey::Node(node) = proof.key {
        validate_conditional_node_link_shape(store, node)?;
    }
    if let ConditionalQueryKey::AliasReference(reference) = proof.key
        && let Some((symbol, _)) = proof.alias.as_ref()
    {
        validate_conditional_alias_reference_owner(store, reference, *symbol)?;
    }
    if retain_result_alias(store, proof.result)? != proof.result_alias {
        return Err(ConditionalTypeError::InvalidInstantiationCache(
            proof.definition.root,
        ));
    }
    let result =
        store
            .type_payload(proof.result)
            .ok_or(ConditionalTypeError::InvalidInstantiationCache(
                proof.definition.root,
            ))?;
    if matches!(result.data(), TypeData::Conditional(_)) {
        validated_conditional_production_worker(store, proof.result, array_targets, validation)?;
    }
    let root = store
        .conditional_root(proof.definition.root)
        .ok_or(ConditionalTypeError::InvalidRoot(proof.definition.root))?;
    let cache_key = match proof.key {
        ConditionalQueryKey::AliasDeclaration(symbol) => {
            validate_alias_identity_worker(
                store,
                ConditionalAliasIdentity {
                    symbol,
                    type_arguments: &proof.type_arguments,
                },
                &mut HashSet::new(),
                array_targets,
                validation,
            )?;
            let Some(declaration) = proof.source_declaration else {
                return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
            };
            if store
                .symbol(symbol)
                .and_then(|symbol| symbol.declarations())
                != Some(&[declaration][..])
                || store
                    .type_alias_links(symbol)
                    .and_then(|links| links.type_parameters.as_deref())
                    .unwrap_or_default()
                    != proof.type_arguments
            {
                return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
            }
            return validate_query_operands_worker(store, proof, array_targets, validation);
        }
        ConditionalQueryKey::AliasReference(reference) if proof.source_declaration.is_some() => {
            return validate_forwarded_alias_reference(
                store,
                reference,
                proof,
                array_targets,
                validation,
            );
        }
        ConditionalQueryKey::Node(_) | ConditionalQueryKey::AliasReference(_)
            if proof.definition.outer_type_parameters.is_none() =>
        {
            return if root.instantiations() == &TypeCacheState::Unallocated {
                validate_query_operands_worker(store, proof, array_targets, validation)
            } else {
                Err(ConditionalTypeError::InvalidInstantiationCache(
                    proof.definition.root,
                ))
            };
        }
        ConditionalQueryKey::Node(_) => {
            conditional_type_key_parts(proof.definition.outer_parameters(), None, false)
        }
        ConditionalQueryKey::Instantiation(_, key) => key,
        ConditionalQueryKey::AliasReference(_) => {
            let alias = proof
                .alias
                .as_ref()
                .map(|(symbol, arguments)| {
                    store
                        .symbol_store()
                        .assigned_global_symbol_id(*symbol)
                        .map(|symbol| (symbol, arguments.as_slice()))
                        .ok_or(ConditionalTypeError::InvalidAliasSymbol(*symbol))
                })
                .transpose()?;
            conditional_type_key_parts(&proof.type_arguments, alias, proof.for_constraint)
        }
    };
    if !matches!(root.instantiations(), TypeCacheState::Allocated(cache) if cache.get(&cache_key) == Some(&proof.result))
    {
        return Err(ConditionalTypeError::InvalidInstantiationCache(
            proof.definition.root,
        ));
    }
    validate_query_operands_worker(store, proof, array_targets, validation)
}

// A nongeneric alias reference reads its declaration result, not a new root instantiation.
fn validate_forwarded_alias_reference(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<(), ConditionalTypeError> {
    let invalid = || ConditionalTypeError::InvalidTypeNodeCache(reference);
    let declaration = proof.source_declaration.ok_or_else(invalid)?;
    let symbol = store
        .symbol_node_links(reference)
        .and_then(|links| links.resolved_symbol)
        .ok_or_else(invalid)?;
    let links = store.type_alias_links(symbol).ok_or_else(invalid)?;
    if store.source_node_kind(reference) != Some(SyntaxKind::TypeReference)
        || !store.source_declaration_belongs_to_symbol(declaration, symbol)
        || !proof.type_arguments.is_empty()
        || proof.for_constraint
        || store
            .type_node_links(reference)
            .and_then(|links| links.resolved_type)
            != Some(proof.result)
        || links.declared_type != Some(proof.result)
        || links.type_parameters.is_some()
        || links.instantiations.is_some()
    {
        return Err(invalid());
    }
    let source = store
        .conditional_query_production(ConditionalQueryKey::AliasDeclaration(symbol))
        .ok_or_else(invalid)?;
    let mut expected = source.clone();
    expected.key = proof.key;
    expected.alias = proof.alias.clone();
    if source.alias.is_some() || expected != *proof {
        return Err(invalid());
    }
    validate_query_production_worker(store, source, array_targets, validation)?;
    validate_query_operands_worker(store, proof, array_targets, validation)
}

fn validate_query_operands_with_source(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    validate_query_operands_worker(
        store,
        proof,
        array_targets,
        ConditionalValidation::Operational(source),
    )
}

fn validate_query_operands_worker(
    store: &CanonicalTypeMapperStore,
    proof: &ConditionalQueryProduction,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<(), ConditionalTypeError> {
    let mut visiting = HashSet::new();
    for operand in [proof.definition.check_type, proof.definition.extends_type]
        .iter()
        .chain(&proof.type_arguments)
        .chain(
            proof
                .alias
                .as_ref()
                .into_iter()
                .flat_map(|(_, arguments)| arguments),
        )
    {
        validation.operand(store, *operand, &mut visiting, array_targets)?;
    }
    if let ConditionalValidation::Operational(source) = validation
        && source.is_none_or(|source| source.source_query_options().is_none())
        && conditional_query_requires_source(
            store,
            proof,
            &conditional_query_identity_edges(proof),
        )?
    {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    Ok(())
}

fn validate_conditional_alias_reference_owner(
    store: &CanonicalTypeMapperStore,
    reference: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), ConditionalTypeError> {
    let declaration = conditional_alias_declaration(store, reference)
        .ok_or(ConditionalTypeError::InvalidAliasSymbol(symbol))?;
    if store.source_node_kind(reference) != Some(SyntaxKind::TypeReference)
        || store
            .symbol(symbol)
            .and_then(|symbol| symbol.declarations())
            != Some(&[declaration][..])
    {
        return Err(ConditionalTypeError::InvalidAliasSymbol(symbol));
    }
    Ok(())
}

/// Resolves the true branch only when its canonical lazy cache is requested.
pub(super) fn get_true_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    resolve_conditional_branch(
        store,
        conditional,
        branches,
        ConditionalResolutionKind::True,
        global_types,
        session,
    )
}

/// Resolves the false branch only when its canonical lazy cache is requested.
pub(super) fn get_false_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    resolve_conditional_branch(
        store,
        conditional,
        branches,
        ConditionalResolutionKind::False,
        global_types,
        session,
    )
}

/// Resolves the true branch through the inference mapper when one exists.
pub(super) fn get_inferred_true_type_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    if conditional_snapshot(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?
    .combined_mapper
    .is_none()
    {
        let resolved = get_true_type_from_conditional_type(
            store,
            conditional,
            branches,
            global_types,
            session,
        )?;
        let mut data = conditional_snapshot(
            store,
            conditional,
            global_types.map(CanonicalArrayTargets::from_global_types),
        )?;
        if data.resolved_inferred_true_type != Some(resolved) {
            data.resolved_inferred_true_type = Some(resolved);
            publish_conditional_snapshot(store, conditional, &data)?;
        }
        return Ok(resolved);
    }
    resolve_conditional_branch(
        store,
        conditional,
        branches,
        ConditionalResolutionKind::InferredTrue,
        global_types,
        session,
    )
}

/// Computes the pinned default constraint, excluding a single `any` branch.
pub(super) fn get_default_constraint_of_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    get_default_constraint_of_conditional_type_worker(
        store,
        conditional,
        ConditionalBranchInput::Resolved(branches),
        global_types,
        session,
        &mut None,
    )
}

fn get_default_constraint_of_conditional_type_worker(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalBranchInput,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    let semantic_mark = source_semantic_recovery_mark(source);
    let data = conditional_snapshot_with_source(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    if let Some(cached) = data.resolved_default_constraint {
        validate_owned_type(store, cached)?;
        if !is_source_query(source) {
            return Ok(cached);
        }
    }

    let mut owned_session = session
        .is_none()
        .then(|| InstantiationSession::new(InstantiationLimits::default()));
    let session = session
        .or(owned_session.as_mut())
        .expect("the caller or legacy session is present");
    let mark = session.limit_event_mark();
    let true_type = resolve_constraint_branch_input(
        store,
        conditional,
        branches,
        ConditionalResolutionKind::InferredTrue,
        global_types,
        session,
        source,
    )?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }
    let false_type = resolve_constraint_branch_input(
        store,
        conditional,
        branches,
        ConditionalResolutionKind::False,
        global_types,
        session,
        source,
    )?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }
    let result = if type_flags(store, true_type)?.intersects(TypeFlags::ANY) {
        false_type
    } else if type_flags(store, false_type)?.intersects(TypeFlags::ANY) {
        true_type
    } else {
        union_result_in_query(
            store,
            &[true_type, false_type],
            global_types,
            session,
            source,
        )?
    };
    let mut data = conditional_snapshot_with_source(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    if is_source_query(source) {
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(recovery);
        }
        if source_semantic_recovery_since(store, semantic_mark, session, source)? {
            return Ok(result);
        }
        if let Some(cached) = data.resolved_default_constraint {
            return if cached == result {
                Ok(result)
            } else {
                Err(ConditionalTypeError::InvalidConditionalResolution(
                    conditional,
                ))
            };
        }
    }
    data.resolved_default_constraint = Some(result);
    publish_conditional_snapshot(store, conditional, &data)?;
    Ok(result)
}

/// Instantiates a distributive conditional with its checked parameter's constraint.
pub(super) fn get_constraint_of_distributive_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    get_constraint_of_distributive_conditional_type_worker(
        store,
        conditional,
        ConditionalBranchInput::Resolved(branches),
        global_types,
        session,
        &mut None,
    )
}

fn get_constraint_of_distributive_conditional_type_worker(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalBranchInput,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let semantic_mark = source_semantic_recovery_mark(source);
    let data = conditional_snapshot_with_source(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    let no_constraint = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?
        .no_constraint_type;
    if let Some(cached) = data.resolved_constraint_of_distributive {
        validate_owned_type(store, cached)?;
        if !is_source_query(source) {
            return Ok((cached != no_constraint).then_some(cached));
        }
    }

    let (distributive, root_check, parameters) = {
        let root = store
            .conditional_root(data.root)
            .ok_or(ConditionalTypeError::InvalidRoot(data.root))?;
        (
            root.is_distributive(),
            root.check_type(),
            root.outer_type_parameters().unwrap_or_default().to_vec(),
        )
    };
    let mut owned_session = session
        .is_none()
        .then(|| InstantiationSession::new(InstantiationLimits::default()));
    let session = session
        .or(owned_session.as_mut())
        .expect("the caller or legacy session is present");
    let mark = session.limit_event_mark();
    let mut result = None;
    if distributive {
        let declared_call_set_constraint = store
            .type_payload(data.check_type)
            .and_then(|record| match record.data() {
                TypeData::TypeParameter(parameter) => parameter.constraint,
                _ => None,
            })
            .filter(|constraint| {
                matches!(
                    validate_stored_declared_call_set(store, *constraint),
                    StoredDeclaredCallSetValidation::Valid(_)
                )
            });
        let constraint = if declared_call_set_constraint.is_some() {
            declared_call_set_constraint
        } else {
            let constraint = if is_source_query(source) {
                constraints::get_constraint_of_type_with_source(
                    store,
                    data.check_type,
                    global_types.ok_or(ConditionalTypeError::MissingBootstrap)?,
                    session,
                    source
                        .as_deref_mut()
                        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
                )
            } else {
                constraints::get_constraint_of_type(store, data.check_type)
            };
            match constraint {
                Ok(constraint) => constraint,
                Err(ConstraintError::UnresolvedTypeParameter(type_))
                    if type_ == data.check_type =>
                {
                    None
                }
                Err(error) => return Err(error.into()),
            }
        };
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(Some(recovery));
        }
        if let Some(constraint) = constraint
            && constraint != data.check_type
        {
            let mut arguments = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let argument = if parameter == root_check {
                    constraint
                } else {
                    map_stored_type_in_query(
                        store,
                        parameter,
                        data.mapper,
                        global_types,
                        session,
                        source,
                    )?
                };
                if let Some(recovery) = source_recovery_type(session, mark, source)? {
                    return Ok(Some(recovery));
                }
                arguments.push(argument);
            }
            let instantiated = if let ConditionalBranchInput::Resolved(branches) = branches
                && !is_source_query(source)
            {
                get_conditional_type_instantiation(
                    store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches,
                        alias: None,
                        for_constraint: true,
                    },
                    global_types,
                    Some(session),
                )?
            } else {
                instantiate_conditional_root(
                    store,
                    ConditionalRootInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches,
                        alias: None,
                        alias_source: None,
                        for_constraint: true,
                        input_recovery: None,
                    },
                    global_types,
                    Some(session),
                    0,
                    source,
                )?
            };
            if !is_never(store, instantiated)? {
                result = Some(instantiated);
            }
        }
    }

    let mut data = conditional_snapshot_with_source(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    if is_source_query(source) {
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(Some(recovery));
        }
        if source_semantic_recovery_since(store, semantic_mark, session, source)? {
            return Ok(result);
        }
        if let Some(cached) = data.resolved_constraint_of_distributive {
            return if cached == result.unwrap_or(no_constraint) {
                Ok(result)
            } else {
                Err(ConditionalTypeError::InvalidConditionalResolution(
                    conditional,
                ))
            };
        }
    }
    data.resolved_constraint_of_distributive = Some(result.unwrap_or(no_constraint));
    publish_conditional_snapshot(store, conditional, &data)?;
    Ok(result)
}

/// Uses the distributive constraint first, then the pinned default constraint.
pub(super) fn get_constraint_from_conditional_type(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    get_constraint_from_conditional_type_worker(
        store,
        conditional,
        ConditionalBranchInput::Resolved(branches),
        global_types,
        session,
        &mut None,
    )
}

/// Uses the same constraint worker with the current source and caller.
pub(super) fn get_constraint_from_conditional_type_with_source(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    source: &mut dyn ConditionalBranchSource,
) -> Result<TypeId, ConditionalTypeError> {
    if source.source_query_options().is_none() {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    let mark = session.limit_event_mark();
    let semantic_mark = source.source_branch_recoveries().len();
    let data = conditional_snapshot_with_source(
        store,
        conditional,
        Some(CanonicalArrayTargets::from_global_types(globals)),
        Some(source),
    )?;
    let root = store
        .conditional_root(data.root)
        .ok_or(ConditionalTypeError::InvalidRoot(data.root))?;
    let root = ConditionalSourceRoot {
        root: data.root,
        node: root.node(),
    };
    source
        .preflight_root(store, root)
        .map_err(ConditionalTypeError::Declared)?;
    let result = get_constraint_from_conditional_type_worker(
        store,
        conditional,
        ConditionalBranchInput::Root(root),
        Some(globals),
        Some(&mut *session),
        &mut Some(&mut *source),
    )?;
    if !session.limit_event_occurred_since(mark) {
        validate_source_branch_recoveries_since(store, source, semantic_mark, session)?;
    }
    Ok(result)
}

fn get_constraint_from_conditional_type_worker(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalBranchInput,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    let mut owned_session = session
        .is_none()
        .then(|| InstantiationSession::new(InstantiationLimits::default()));
    let session = session
        .or(owned_session.as_mut())
        .expect("the caller or legacy session is present");
    let mark = session.limit_event_mark();
    if let Some(distributive) = get_constraint_of_distributive_conditional_type_worker(
        store,
        conditional,
        branches,
        global_types,
        Some(session),
        source,
    )? {
        return Ok(distributive);
    }
    if is_source_query(source) && session.limit_event_occurred_since(mark) {
        return session.recovery_error_type().ok_or(
            ConditionalTypeError::InvalidConditionalResolution(conditional),
        );
    }
    get_default_constraint_of_conditional_type_worker(
        store,
        conditional,
        branches,
        global_types,
        Some(session),
        source,
    )
}

/// Returns resolved branch identities without forcing an unavailable syntax query.
pub(super) fn cached_conditional_branches(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
) -> Result<Option<ConditionalTypeBranches>, ConditionalTypeError> {
    cached_conditional_branches_with_array_targets(store, conditional, None)
}

pub(super) fn cached_conditional_branches_with_array_targets(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<ConditionalTypeBranches>, ConditionalTypeError> {
    let data = conditional_snapshot(store, conditional, array_targets)?;
    let Some(true_type) = data.resolved_inferred_true_type.or(data.resolved_true_type) else {
        return Ok(None);
    };
    let Some(false_type) = data.resolved_false_type else {
        return Ok(None);
    };
    let branches = ConditionalTypeBranches {
        true_type,
        false_type,
    };
    validate_branch_types(store, branches, array_targets)?;
    Ok(Some(branches))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalResolutionKind {
    True,
    False,
    InferredTrue,
}

fn resolve_constraint_branch_input(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalBranchInput,
    branch: ConditionalResolutionKind,
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    let semantic_mark = source_semantic_recovery_mark(source);
    if let ConditionalBranchInput::Resolved(branches) = branches
        && !is_source_query(source)
    {
        return match branch {
            ConditionalResolutionKind::InferredTrue => {
                get_inferred_true_type_from_conditional_type(
                    store,
                    conditional,
                    branches,
                    globals,
                    Some(session),
                )
            }
            _ => resolve_conditional_branch(
                store,
                conditional,
                branches,
                branch,
                globals,
                Some(session),
            ),
        };
    }
    let arrays = globals.map(CanonicalArrayTargets::from_global_types);
    let data = conditional_snapshot_with_source(store, conditional, arrays, source.as_deref())?;
    let (cached, kind, mapper) = match branch {
        ConditionalResolutionKind::True => (
            data.resolved_true_type,
            ConditionalBranchKind::True,
            data.mapper,
        ),
        ConditionalResolutionKind::False => (
            data.resolved_false_type,
            ConditionalBranchKind::False,
            data.mapper,
        ),
        ConditionalResolutionKind::InferredTrue => (
            data.resolved_inferred_true_type,
            ConditionalBranchKind::True,
            data.combined_mapper.or(data.mapper),
        ),
    };
    if let Some(cached) = cached {
        validate_owned_type(store, cached)?;
    }
    let mark = session.limit_event_mark();
    let branch_type = branches.get(store, kind, session, source)?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }
    let resolved = map_stored_type_in_query(store, branch_type, mapper, globals, session, source)?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }
    let mut current =
        conditional_snapshot_with_source(store, conditional, arrays, source.as_deref())?;
    if session.limit_event_occurred_since(mark) {
        return Ok(resolved);
    }
    if source_semantic_recovery_since(store, semantic_mark, session, source)? {
        return Ok(resolved);
    }
    if current != data || cached.is_some_and(|cached| cached != resolved) {
        return Err(ConditionalTypeError::InvalidConditionalResolution(
            conditional,
        ));
    }
    match branch {
        ConditionalResolutionKind::True => current.resolved_true_type = Some(resolved),
        ConditionalResolutionKind::False => current.resolved_false_type = Some(resolved),
        ConditionalResolutionKind::InferredTrue => {
            current.resolved_inferred_true_type = Some(resolved);
            if current.combined_mapper.is_none() {
                if current
                    .resolved_true_type
                    .is_some_and(|cached| cached != resolved)
                {
                    return Err(ConditionalTypeError::InvalidConditionalResolution(
                        conditional,
                    ));
                }
                current.resolved_true_type = Some(resolved);
            }
        }
    }
    if current != data {
        publish_conditional_snapshot(store, conditional, &current)?;
    }
    Ok(resolved)
}

fn resolve_conditional_branch(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    branches: ConditionalTypeBranches,
    branch: ConditionalResolutionKind,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    validate_branch_types(
        store,
        branches,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    let data = conditional_snapshot(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    let (cached, source, mapper) = match branch {
        ConditionalResolutionKind::True => {
            (data.resolved_true_type, branches.true_type, data.mapper)
        }
        ConditionalResolutionKind::False => {
            (data.resolved_false_type, branches.false_type, data.mapper)
        }
        ConditionalResolutionKind::InferredTrue => (
            data.resolved_inferred_true_type,
            branches.true_type,
            data.combined_mapper.or(data.mapper),
        ),
    };
    if let Some(cached) = cached {
        validate_owned_type(store, cached)?;
        return Ok(cached);
    }

    let mut owned_session = InstantiationSession::new(InstantiationLimits::default());
    let session = session.unwrap_or(&mut owned_session);
    let resolved = map_type_with_stored_mapper(store, source, mapper, global_types, session)?;
    let mut data = conditional_snapshot(
        store,
        conditional,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    match branch {
        ConditionalResolutionKind::True => data.resolved_true_type = Some(resolved),
        ConditionalResolutionKind::False => data.resolved_false_type = Some(resolved),
        ConditionalResolutionKind::InferredTrue => {
            data.resolved_inferred_true_type = Some(resolved);
            if data.combined_mapper.is_none() {
                data.resolved_true_type = Some(resolved);
            }
        }
    }
    publish_conditional_snapshot(store, conditional, &data)?;
    Ok(resolved)
}

fn conditional_snapshot(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ConditionalTypeData, ConditionalTypeError> {
    conditional_snapshot_with_source(store, conditional, array_targets, None)
}

fn conditional_snapshot_with_source(
    store: &CanonicalTypeMapperStore,
    conditional: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<ConditionalTypeData, ConditionalTypeError> {
    let validation = ConditionalValidation::Operational(source);
    if store.conditional_type_production(conditional).is_some() {
        validated_conditional_production_worker(store, conditional, array_targets, validation)?;
    }
    match store.type_payload(conditional).map(TypeRecord::data) {
        Some(TypeData::Conditional(data)) => {
            let root = store
                .conditional_root(data.root)
                .ok_or(ConditionalTypeError::InvalidRoot(data.root))?;
            if store.source_node_kind(root.node()) != Some(SyntaxKind::ConditionalType) {
                return Err(ConditionalTypeError::InvalidNode(root.node()));
            }
            validate_root_alias_worker(
                store,
                root.node(),
                root.outer_type_parameters().unwrap_or_default(),
                root.alias(),
                array_targets,
                validation,
            )?;
            let mut visiting = HashSet::new();
            if let Some(alias) = store.type_payload(conditional).and_then(TypeRecord::alias) {
                validate_alias_identity_worker(
                    store,
                    stored_alias_identity(store, alias)?,
                    &mut visiting,
                    array_targets,
                    validation,
                )?;
            }
            for type_ in [
                data.check_type,
                data.extends_type,
                root.check_type(),
                root.extends_type(),
            ] {
                validate_conditional_operand_with_source(
                    store,
                    type_,
                    &mut visiting,
                    array_targets,
                    source,
                )?;
            }
            Ok(data.clone())
        }
        _ => Err(ConditionalTypeError::InvalidConditional(conditional)),
    }
}

fn publish_conditional_snapshot(
    store: &mut CanonicalTypeMapperStore,
    conditional: TypeId,
    data: &ConditionalTypeData,
) -> Result<(), ConditionalTypeError> {
    if store.set_conditional_resolution(
        conditional,
        data.resolved_true_type,
        data.resolved_false_type,
        data.resolved_inferred_true_type,
        data.resolved_default_constraint,
        data.resolved_constraint_of_distributive,
        data.mapper,
        data.combined_mapper,
    ) {
        Ok(())
    } else {
        Err(ConditionalTypeError::InvalidConditionalResolution(
            conditional,
        ))
    }
}

fn get_conditional_type_instantiation_with_tail_count(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalTypeInstantiation<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
    tail_count: usize,
) -> Result<TypeId, ConditionalTypeError> {
    if tail_count >= CONDITIONAL_TAIL_RECURSION_LIMIT {
        return Err(ConditionalTypeError::TailRecursionLimit {
            count: tail_count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }
    validated_conditional_production(
        store,
        request.conditional_type,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    validate_branch_types(
        store,
        request.branches,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    if let Some(proof) = request.alias
        && !proof.matches_request(store, request.conditional_type, request.type_arguments)
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(
            proof.reference(),
        ));
    }
    let alias = request
        .alias
        .and_then(ConditionalAliasReferenceProof::identity);
    let alias_source = request.alias.and_then(|proof| {
        proof
            .identity()
            .map(|identity| (identity, proof.reference()))
    });
    instantiate_conditional_root(
        store,
        ConditionalRootInstantiation {
            conditional_type: request.conditional_type,
            type_arguments: request.type_arguments,
            branches: ConditionalBranchInput::Resolved(request.branches),
            alias,
            alias_source,
            for_constraint: request.for_constraint,
            input_recovery: None,
        },
        global_types,
        session,
        tail_count,
        &mut None,
    )
}

#[derive(Clone, Copy)]
struct ConditionalRootInstantiation<'a> {
    conditional_type: TypeId,
    type_arguments: &'a [TypeId],
    branches: ConditionalBranchInput,
    alias: Option<ConditionalAliasIdentity<'a>>,
    alias_source: Option<(ConditionalAliasIdentity<'a>, NodeRef)>,
    for_constraint: bool,
    input_recovery: Option<&'a SourceConditionalInputRecoveryProof>,
}

fn validate_root_input_recovery(
    store: &CanonicalTypeMapperStore,
    request: ConditionalRootInstantiation<'_>,
    globals: Option<&CanonicalGlobalTypes>,
    session: &InstantiationSession,
    source: &Option<&mut dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    let Some(proof) = request.input_recovery else {
        return Ok(());
    };
    if !matches!(
        proof.query(),
        ConditionalSourceInputQuery::Instantiation {
            conditional_type,
            type_arguments,
            for_constraint,
            ..
        } if conditional_type == request.conditional_type
            && type_arguments == request.type_arguments
            && for_constraint == request.for_constraint
    ) {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    validate_source_input_recovery(
        store,
        proof.query(),
        proof,
        globals.ok_or(ConditionalTypeError::MissingBootstrap)?,
        session,
        source
            .as_deref()
            .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
    )
}

fn instantiate_conditional_root(
    store: &mut CanonicalTypeMapperStore,
    request: ConditionalRootInstantiation<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: Option<&mut InstantiationSession>,
    tail_count: usize,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    let semantic_mark = if let Some(input) = request.input_recovery {
        validate_root_input_recovery(
            store,
            request,
            global_types,
            session
                .as_deref()
                .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
            source,
        )?;
        input.event_start()
    } else {
        source_semantic_recovery_mark(source)
    };
    if tail_count >= CONDITIONAL_TAIL_RECURSION_LIMIT {
        return Err(ConditionalTypeError::TailRecursionLimit {
            count: tail_count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }
    let validation = ConditionalValidation::Operational(source.as_deref());
    let definition = validated_conditional_production_worker(
        store,
        request.conditional_type,
        global_types.map(CanonicalArrayTargets::from_global_types),
        validation,
    )?
    .definition
    .clone();
    if let Some(source) = source.as_deref() {
        source
            .preflight(store, request.conditional_type)
            .map_err(ConditionalTypeError::Declared)?;
    }
    let alias = request.alias;
    let alias_source = request.alias_source;
    if let Some(alias) = alias {
        validate_alias_identity_worker(
            store,
            alias,
            &mut HashSet::new(),
            global_types.map(CanonicalArrayTargets::from_global_types),
            validation,
        )?;
    }

    let data = conditional_snapshot_with_source(
        store,
        request.conditional_type,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    let (root, existing_mapper) = (data.root, data.mapper);
    if let Some(mapper) = existing_mapper
        && store.mapper_payload(mapper).is_none()
    {
        return Err(ConditionalTypeError::InvalidMapper(mapper));
    }
    let (outer_parameters, check_type, distributive, cached_values) = {
        let root_record = store
            .conditional_root(root)
            .ok_or(ConditionalTypeError::InvalidRoot(root))?;
        let parameters = root_record
            .outer_type_parameters()
            .unwrap_or_default()
            .to_vec();
        let cache = match root_record.instantiations() {
            TypeCacheState::Allocated(cache) if !parameters.is_empty() => cache.clone(),
            TypeCacheState::Unallocated if parameters.is_empty() => HashMap::new(),
            _ => return Err(ConditionalTypeError::InvalidInstantiationCache(root)),
        };
        (
            parameters,
            root_record.check_type(),
            root_record.is_distributive(),
            cache,
        )
    };
    if outer_parameters.is_empty() {
        if !request.type_arguments.is_empty() {
            return Err(ConditionalTypeError::InvalidInstantiationArity {
                expected: 0,
                actual: request.type_arguments.len(),
            });
        }
        if !is_source_query(source) {
            return Ok(request.conditional_type);
        }
        let session =
            session.ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
        let mark = session.limit_event_mark();
        let result = evaluate_conditional_worker(
            store,
            root,
            request.branches,
            &[],
            &[],
            global_types,
            request.for_constraint,
            alias_source,
            session,
            tail_count,
            source,
            Some(request.conditional_type),
        )?;
        if session.limit_event_occurred_since(mark) {
            return Ok(result);
        }
        validate_root_input_recovery(store, request, global_types, session, source)?;
        if source_semantic_recovery_since(store, semantic_mark, session, source)? {
            return Ok(result);
        }
        if result != request.conditional_type {
            return Err(ConditionalTypeError::InvalidConditional(
                request.conditional_type,
            ));
        }
        return Ok(result);
    }
    if outer_parameters.len() != request.type_arguments.len() {
        return Err(ConditionalTypeError::InvalidInstantiationArity {
            expected: outer_parameters.len(),
            actual: request.type_arguments.len(),
        });
    }
    let mut visiting = HashSet::new();
    for argument in request.type_arguments {
        validate_conditional_operand_with_source(
            store,
            *argument,
            &mut visiting,
            global_types.map(CanonicalArrayTargets::from_global_types),
            source.as_deref(),
        )?;
    }

    let key = conditional_type_key_with_source(
        store,
        request.type_arguments,
        alias,
        request.for_constraint,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    let cached = cached_values.get(&key).copied();
    if let Some(cached) = cached {
        validate_cached_instantiation_with_source(
            store,
            root,
            key,
            cached,
            &outer_parameters,
            request.type_arguments,
            alias,
            request.for_constraint,
            global_types.map(CanonicalArrayTargets::from_global_types),
            source.as_deref(),
        )?;
        if !is_source_query(source) {
            return Ok(cached);
        }
    }
    let query_key = ConditionalQueryKey::Instantiation(root, key);
    if cached.is_none() && store.conditional_query_production(query_key).is_some() {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    if cached.is_none() && !store.try_reserve_conditional_productions(0, 1) {
        return Err(ConditionalTypeError::Capacity);
    }

    let mut owned_session = session
        .is_none()
        .then(|| InstantiationSession::new(InstantiationLimits::default()));
    let session = session
        .or(owned_session.as_mut())
        .expect("the caller or legacy session is present");
    let mark = session.limit_event_mark();
    let mapped_check = map_type_with_source(
        store,
        check_type,
        &outer_parameters,
        request.type_arguments,
        global_types,
        session,
        source,
    )?;

    let result = if distributive && mapped_check != check_type {
        match store.type_payload(mapped_check).map(TypeRecord::data) {
            Some(TypeData::Union(union)) => {
                let constituents = union.union.types.clone();
                let Some(check_index) = outer_parameters
                    .iter()
                    .position(|parameter| *parameter == check_type)
                else {
                    return Err(ConditionalTypeError::InvalidRoot(root));
                };
                let mut results = Vec::with_capacity(constituents.len());
                for constituent in constituents {
                    let mut arguments = request.type_arguments.to_vec();
                    arguments[check_index] = constituent;
                    results.push(evaluate_conditional_worker(
                        store,
                        root,
                        request.branches,
                        &outer_parameters,
                        &arguments,
                        global_types,
                        request.for_constraint,
                        None,
                        session,
                        tail_count,
                        source,
                        cached,
                    )?);
                }
                union_result_with_alias_in_query(
                    store,
                    &results,
                    global_types,
                    alias,
                    session,
                    source,
                )?
            }
            Some(_) if is_never(store, mapped_check)? => mapped_check,
            Some(_) => evaluate_conditional_worker(
                store,
                root,
                request.branches,
                &outer_parameters,
                request.type_arguments,
                global_types,
                request.for_constraint,
                alias_source,
                session,
                tail_count,
                source,
                cached,
            )?,
            None => return Err(ConditionalTypeError::InvalidType(mapped_check)),
        }
    } else {
        evaluate_conditional_worker(
            store,
            root,
            request.branches,
            &outer_parameters,
            request.type_arguments,
            global_types,
            request.for_constraint,
            alias_source,
            session,
            tail_count,
            source,
            cached,
        )?
    };

    if source.is_some()
        && session.limit_event_occurred_since(mark)
        && let Some(error) = session.recovery_error_type()
    {
        return Ok(error);
    }
    validate_root_input_recovery(store, request, global_types, session, source)?;
    if source_semantic_recovery_since(store, semantic_mark, session, source)? {
        return Ok(result);
    }

    if let Some(cached) = cached {
        if cached != result {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
        validate_cached_instantiation_with_source(
            store,
            root,
            key,
            cached,
            &outer_parameters,
            request.type_arguments,
            alias,
            request.for_constraint,
            global_types.map(CanonicalArrayTargets::from_global_types),
            source.as_deref(),
        )?;
        return Ok(cached);
    }

    let mut cache = match store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?
        .instantiations()
    {
        TypeCacheState::Allocated(cache) => cache.clone(),
        TypeCacheState::Unallocated => {
            return Err(ConditionalTypeError::InvalidInstantiationCache(root));
        }
    };
    if let Some(previous) = cache.insert(key, result)
        && previous != result
    {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    if !store.set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache)) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    let proof = ConditionalQueryProduction {
        key: query_key,
        definition,
        type_arguments: request.type_arguments.to_vec(),
        alias: alias.map(|alias| (alias.symbol, alias.type_arguments.to_vec())),
        for_constraint: request.for_constraint,
        result,
        source_declaration: None,
        result_alias: retain_result_alias(store, result)?,
    };
    validate_query_production_with_source(
        store,
        &proof,
        global_types.map(CanonicalArrayTargets::from_global_types),
        source.as_deref(),
    )?;
    if !store.publish_conditional_query_production(proof) {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)] // Mirrors the upstream conditional evaluation inputs.
fn evaluate_conditional(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    branches: ConditionalTypeBranches,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    for_constraint: bool,
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
    session: &mut InstantiationSession,
    tail_count: usize,
) -> Result<TypeId, ConditionalTypeError> {
    evaluate_conditional_worker(
        store,
        root,
        ConditionalBranchInput::Resolved(branches),
        mapped_parameters,
        type_arguments,
        global_types,
        for_constraint,
        alias,
        session,
        tail_count,
        &mut None,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // The source reader does not own evaluation or mapping.
fn evaluate_conditional_worker(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    branches: ConditionalBranchInput,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    for_constraint: bool,
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
    session: &mut InstantiationSession,
    tail_count: usize,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
    retained_result: Option<TypeId>,
) -> Result<TypeId, ConditionalTypeError> {
    if tail_count >= CONDITIONAL_TAIL_RECURSION_LIMIT {
        return Err(ConditionalTypeError::TailRecursionLimit {
            count: tail_count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }
    let (root_check, root_extends, infer_parameters) = {
        let record = store
            .conditional_root(root)
            .ok_or(ConditionalTypeError::InvalidRoot(root))?;
        (
            record.check_type(),
            record.extends_type(),
            record.infer_type_parameters().unwrap_or_default().to_vec(),
        )
    };
    let mark = session.limit_event_mark();
    let check_type = map_type_with_source(
        store,
        root_check,
        mapped_parameters,
        type_arguments,
        global_types,
        session,
        source,
    )?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }
    let extends_type = map_type_with_source(
        store,
        root_extends,
        mapped_parameters,
        type_arguments,
        global_types,
        session,
        source,
    )?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if check_type == bootstrap.error_type || extends_type == bootstrap.error_type {
        return Ok(bootstrap.error_type);
    }
    if check_type == bootstrap.wildcard_type || extends_type == bootstrap.wildcard_type {
        return Ok(bootstrap.wildcard_type);
    }

    if infer_parameters.is_empty()
        && let ConditionalBranchInput::Resolved(branches) = branches
        && let Some(simplified) = trivial_conditional_identity(
            store,
            check_type,
            extends_type,
            branches,
            mapped_parameters,
            type_arguments,
        )?
    {
        return Ok(simplified);
    }

    let mut resolved_check_parameters = HashSet::new();
    for (parameter, argument) in mapped_parameters.iter().zip(type_arguments) {
        if !contains_type_parameter_with_array_targets(
            store,
            *argument,
            &HashSet::new(),
            global_types.map(CanonicalArrayTargets::from_global_types),
        )? {
            resolved_check_parameters.insert(*parameter);
        }
    }
    if conditional_operand_is_deferred(
        store,
        check_type,
        &resolved_check_parameters,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )? {
        return deferred_conditional_in_query(
            store,
            root,
            check_type,
            extends_type,
            mapped_parameters,
            type_arguments,
            alias,
            global_types.map(CanonicalArrayTargets::from_global_types),
            source,
            retained_result,
        );
    }

    let mut combined_parameters = mapped_parameters.to_vec();
    let mut combined_arguments = type_arguments.to_vec();
    let mut inference_matched = false;
    if !infer_parameters.is_empty() {
        let mut candidates = vec![Vec::new(); infer_parameters.len()];
        let matched = infer_from_types(
            store,
            check_type,
            extends_type,
            ConditionalInferenceContext {
                infer_parameters: &infer_parameters,
                mapped_parameters,
                type_arguments,
                global_types,
            },
            &mut candidates,
            session,
            source,
        )?;
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(recovery);
        }
        if !matched {
            let branch = branches.get(store, ConditionalBranchKind::False, session, source)?;
            return map_type_with_source(
                store,
                branch,
                mapped_parameters,
                type_arguments,
                global_types,
                session,
                source,
            );
        }
        inference_matched = true;
        let unknown_type = store
            .intrinsic_bootstrap()
            .ok_or(ConditionalTypeError::MissingBootstrap)?
            .unknown_type;
        for (parameter, candidates) in infer_parameters.iter().zip(candidates) {
            let inferred = match candidates.as_slice() {
                [] => unknown_type,
                [candidate] => *candidate,
                _ => union_result_in_query(store, &candidates, global_types, session, source)?,
            };
            if let Some(recovery) = source_recovery_type(session, mark, source)? {
                return Ok(recovery);
            }
            let satisfies_constraint = inferred_candidate_satisfies_constraint(
                store,
                *parameter,
                inferred,
                &combined_parameters,
                &combined_arguments,
                global_types,
                session,
                source,
            )?;
            if let Some(recovery) = source_recovery_type(session, mark, source)? {
                return Ok(recovery);
            }
            if !satisfies_constraint {
                let branch = branches.get(store, ConditionalBranchKind::False, session, source)?;
                return map_type_with_source(
                    store,
                    branch,
                    mapped_parameters,
                    type_arguments,
                    global_types,
                    session,
                    source,
                );
            }
            combined_parameters.push(*parameter);
            combined_arguments.push(inferred);
        }
    }
    let inferred_extends = map_type_with_source(
        store,
        root_extends,
        &combined_parameters,
        &combined_arguments,
        global_types,
        session,
        source,
    )?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }
    let resolved_parameters = combined_parameters.iter().copied().collect::<HashSet<_>>();
    if conditional_operand_is_deferred(
        store,
        inferred_extends,
        &resolved_parameters,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )? {
        return deferred_conditional_in_query(
            store,
            root,
            check_type,
            extends_type,
            mapped_parameters,
            type_arguments,
            alias,
            global_types.map(CanonicalArrayTargets::from_global_types),
            source,
            retained_result,
        );
    }

    let check_flags = type_flags(store, check_type)?;
    let extends_flags = type_flags(store, inferred_extends)?;
    let is_any = check_flags.intersects(TypeFlags::ANY);
    let extends_any_or_unknown = extends_flags.intersects(TypeFlags::ANY_OR_UNKNOWN);
    let inference_proves_assignability =
        inference_matched && is_structural_inference_target(store, extends_type)?;
    let assignable = extends_any_or_unknown
        || inference_proves_assignability
        || is_assignable_in_query(
            store,
            check_type,
            inferred_extends,
            global_types,
            session,
            source,
        )?;
    if let Some(recovery) = source_recovery_type(session, mark, source)? {
        return Ok(recovery);
    }

    if is_any && !extends_any_or_unknown {
        let true_branch = branches.get(store, ConditionalBranchKind::True, session, source)?;
        let when_true = map_type_with_source(
            store,
            true_branch,
            &combined_parameters,
            &combined_arguments,
            global_types,
            session,
            source,
        )?;
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(recovery);
        }
        let false_branch = branches.get(store, ConditionalBranchKind::False, session, source)?;
        let when_false = map_type_with_source(
            store,
            false_branch,
            mapped_parameters,
            type_arguments,
            global_types,
            session,
            source,
        )?;
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(recovery);
        }
        return union_result_in_query(
            store,
            &[when_true, when_false],
            global_types,
            session,
            source,
        );
    }

    if !assignable && for_constraint && !is_never(store, inferred_extends)? {
        let reverse = is_assignable_in_query(
            store,
            inferred_extends,
            check_type,
            global_types,
            session,
            source,
        )?;
        if let Some(recovery) = source_recovery_type(session, mark, source)? {
            return Ok(recovery);
        }
        if reverse {
            let true_branch = branches.get(store, ConditionalBranchKind::True, session, source)?;
            let when_true = map_type_with_source(
                store,
                true_branch,
                &combined_parameters,
                &combined_arguments,
                global_types,
                session,
                source,
            )?;
            if let Some(recovery) = source_recovery_type(session, mark, source)? {
                return Ok(recovery);
            }
            let false_branch =
                branches.get(store, ConditionalBranchKind::False, session, source)?;
            let when_false = map_type_with_source(
                store,
                false_branch,
                mapped_parameters,
                type_arguments,
                global_types,
                session,
                source,
            )?;
            if let Some(recovery) = source_recovery_type(session, mark, source)? {
                return Ok(recovery);
            }
            return union_result_in_query(
                store,
                &[when_true, when_false],
                global_types,
                session,
                source,
            );
        }
    }

    if assignable {
        let branch = branches.get(store, ConditionalBranchKind::True, session, source)?;
        if let Some(result) = evaluate_conditional_tail(
            store,
            root,
            branch,
            branches,
            &combined_parameters,
            &combined_arguments,
            global_types,
            for_constraint,
            session,
            tail_count,
            source,
        )? {
            return Ok(result);
        }
        map_type_with_source(
            store,
            branch,
            &combined_parameters,
            &combined_arguments,
            global_types,
            session,
            source,
        )
    } else {
        let branch = branches.get(store, ConditionalBranchKind::False, session, source)?;
        if let Some(result) = evaluate_conditional_tail(
            store,
            root,
            branch,
            branches,
            mapped_parameters,
            type_arguments,
            global_types,
            for_constraint,
            session,
            tail_count,
            source,
        )? {
            return Ok(result);
        }
        map_type_with_source(
            store,
            branch,
            mapped_parameters,
            type_arguments,
            global_types,
            session,
            source,
        )
    }
}

fn trivial_conditional_identity(
    store: &CanonicalTypeMapperStore,
    check_type: TypeId,
    extends_type: TypeId,
    branches: ConditionalTypeBranches,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
) -> Result<Option<TypeId>, ConditionalTypeError> {
    if mapped_parameters.is_empty() {
        return Ok(None);
    }

    let mapped_branch = |branch: TypeId| {
        mapped_parameters
            .iter()
            .position(|parameter| *parameter == branch)
            .map_or(Ok(branch), |index| {
                type_arguments.get(index).copied().ok_or(
                    ConditionalTypeError::InvalidInstantiationArity {
                        expected: mapped_parameters.len(),
                        actual: type_arguments.len(),
                    },
                )
            })
    };
    let true_type = mapped_branch(branches.true_type)?;
    let false_type = mapped_branch(branches.false_type)?;
    if true_type == check_type && false_type == check_type {
        return Ok(Some(check_type));
    }

    let never = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?
        .never_type;
    let check_flags = type_flags(store, check_type)?;
    let extends_flags = type_flags(store, extends_type)?;
    let disjoint = extends_flags.intersects(TypeFlags::NEVER)
        || conditional_operands_have_disjoint_primitive_domains(store, check_type, extends_type);
    if true_type == check_type && false_type == never {
        if check_flags.intersects(TypeFlags::ANY)
            || check_type == extends_type
            || extends_flags.intersects(TypeFlags::ANY_OR_UNKNOWN)
        {
            return Ok(Some(check_type));
        }
        if disjoint {
            return Ok(Some(never));
        }
    }
    if true_type == never && false_type == check_type {
        if check_type == extends_type || extends_flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
            return Ok(Some(never));
        }
        if check_flags.intersects(TypeFlags::ANY) || disjoint {
            return Ok(Some(check_type));
        }
    }

    Ok(None)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ConditionalPrimitiveDomain {
    String,
    Number,
    BigInt,
    Boolean,
    Symbol,
}

const MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS: usize = 16;
const MAX_CONDITIONAL_PRIMITIVE_COMPARISONS: usize = 64;

pub(super) fn conditional_operands_have_disjoint_primitive_domains(
    store: &CanonicalTypeMapperStore,
    check_type: TypeId,
    extends_type: TypeId,
) -> bool {
    let Some(check) = conditional_primitive_operand_identity(store, check_type) else {
        return false;
    };
    let Some(extends) = conditional_primitive_operand_identity(store, extends_type) else {
        return false;
    };
    let Some(check_count) = conditional_primitive_operand_count(store, check) else {
        return false;
    };
    let Some(extends_count) = conditional_primitive_operand_count(store, extends) else {
        return false;
    };
    if check_count
        .checked_mul(extends_count)
        .is_none_or(|count| count > MAX_CONDITIONAL_PRIMITIVE_COMPARISONS)
    {
        return false;
    }

    if check_count == 1 && extends_count == 1 {
        let Some(check) = conditional_primitive_leaf(store, check) else {
            return false;
        };
        let Some(extends) = conditional_primitive_leaf(store, extends) else {
            return false;
        };
        return conditional_primitive_pair_is_disjoint(store, check, extends);
    }

    let Some(checks) = conditional_primitive_operands(store, check) else {
        return false;
    };
    let Some(bounds) = conditional_primitive_operands(store, extends) else {
        return false;
    };
    checks.iter().all(|check| {
        bounds
            .iter()
            .all(|bound| conditional_primitive_pair_is_disjoint(store, *check, *bound))
    })
}

fn conditional_primitive_operand_identity(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<TypeId> {
    let record = store.type_payload(type_)?;
    match record.data() {
        TypeData::TypeParameter(parameter) => {
            cached_ordinary_type_parameter_owner(store, type_)?;
            let constraint = parameter.constraint?;
            let bootstrap = store.intrinsic_bootstrap()?;
            if [
                bootstrap.no_constraint_type,
                bootstrap.circular_constraint_type,
                bootstrap.error_type,
                bootstrap.wildcard_type,
            ]
            .contains(&constraint)
            {
                return None;
            }
            Some(constraint)
        }
        _ => Some(type_),
    }
}

fn conditional_primitive_operand_count(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<usize> {
    let record = store.type_payload(type_)?;
    match record.data() {
        TypeData::Union(union)
            if (2..=MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS)
                .contains(&union.union.types.len()) =>
        {
            Some(union.union.types.len())
        }
        TypeData::Union(_) => None,
        _ => conditional_primitive_domain(record.flags()).map(|_| 1),
    }
}

fn conditional_primitive_operands(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<(TypeId, ConditionalPrimitiveDomain)>> {
    let record = store.type_payload(type_)?;
    let TypeData::Union(union) = record.data() else {
        return conditional_primitive_leaf(store, type_).map(|value| vec![value]);
    };
    if !(2..=MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS).contains(&union.union.types.len())
        || union.union.types.iter().any(|constituent| {
            store
                .type_payload(*constituent)
                .and_then(|record| conditional_primitive_domain(record.flags()))
                .is_none()
        })
        || store.validate_union_constituent(type_).is_err()
    {
        return None;
    }

    union
        .union
        .types
        .iter()
        .map(|constituent| conditional_primitive_leaf(store, *constituent))
        .collect()
}

fn conditional_primitive_leaf(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<(TypeId, ConditionalPrimitiveDomain)> {
    let domain = conditional_primitive_domain(store.type_payload(type_)?.flags())?;
    if store.validate_union_constituent(type_).is_err() {
        return None;
    }
    Some((type_, domain))
}

fn conditional_primitive_domain(flags: TypeFlags) -> Option<ConditionalPrimitiveDomain> {
    Some(match flags {
        TypeFlags::STRING | TypeFlags::STRING_LITERAL => ConditionalPrimitiveDomain::String,
        TypeFlags::NUMBER | TypeFlags::NUMBER_LITERAL => ConditionalPrimitiveDomain::Number,
        TypeFlags::BIG_INT | TypeFlags::BIG_INT_LITERAL => ConditionalPrimitiveDomain::BigInt,
        TypeFlags::BOOLEAN | TypeFlags::BOOLEAN_LITERAL => ConditionalPrimitiveDomain::Boolean,
        TypeFlags::ES_SYMBOL | TypeFlags::UNIQUE_ES_SYMBOL => ConditionalPrimitiveDomain::Symbol,
        _ => return None,
    })
}

fn conditional_primitive_pair_is_disjoint(
    store: &CanonicalTypeMapperStore,
    (check, check_domain): (TypeId, ConditionalPrimitiveDomain),
    (extends, extends_domain): (TypeId, ConditionalPrimitiveDomain),
) -> bool {
    if check_domain != extends_domain {
        return true;
    }
    matches!(
        (
            store.type_payload(check).map(TypeRecord::data),
            store.type_payload(extends).map(TypeRecord::data),
        ),
        (Some(TypeData::Literal(check)), Some(TypeData::Literal(extends)))
            if check.value != extends.value
    )
}

#[allow(clippy::too_many_arguments)] // Tail recursion retains the current root and active mapper.
fn evaluate_conditional_tail(
    store: &mut CanonicalTypeMapperStore,
    current_root: ConditionalRootId,
    branch: TypeId,
    current_branches: ConditionalBranchInput,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    for_constraint: bool,
    session: &mut InstantiationSession,
    tail_count: usize,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    let Some(TypeData::Conditional(conditional)) = store.type_payload(branch).map(TypeRecord::data)
    else {
        return Ok(None);
    };
    let next_root = conditional.root;
    let nested_mapper = conditional.mapper;
    if mapped_parameters.is_empty() && nested_mapper.is_none() {
        return Ok(None);
    }
    let (parameters, check_type, distributive, aliased) = {
        let root = store
            .conditional_root(next_root)
            .ok_or(ConditionalTypeError::InvalidRoot(next_root))?;
        (
            root.outer_type_parameters().unwrap_or_default().to_vec(),
            root.check_type(),
            root.is_distributive(),
            root.alias().is_some() || conditional_node_has_alias_owner(store, root.node()),
        )
    };
    if parameters.is_empty() {
        return Ok(None);
    }

    let mut arguments = Vec::with_capacity(parameters.len());
    for parameter in &parameters {
        let nested = if let (Some(mapper), Some(source)) = (nested_mapper, source.as_deref_mut()) {
            let globals = global_types.ok_or(ConditionalTypeError::MissingBootstrap)?;
            super::instantiate::instantiate_type_with_source(
                store, *parameter, mapper, globals, session, source,
            )?
        } else {
            map_type_with_stored_mapper(store, *parameter, nested_mapper, global_types, session)?
        };
        arguments.push(map_type_with_source(
            store,
            nested,
            mapped_parameters,
            type_arguments,
            global_types,
            session,
            source,
        )?);
    }
    if distributive {
        let mapped_check = map_type_with_source(
            store,
            check_type,
            &parameters,
            &arguments,
            global_types,
            session,
            source,
        )?;
        if mapped_check != check_type
            && type_flags(store, mapped_check)?.intersects(TypeFlags::UNION | TypeFlags::NEVER)
        {
            return Ok(None);
        }
    }

    let branches = if next_root == current_root {
        current_branches
    } else if source.is_some() {
        ConditionalBranchInput::Source(branch)
    } else if let Some(branches) = cached_conditional_branches_with_array_targets(
        store,
        branch,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )? {
        ConditionalBranchInput::Resolved(branches)
    } else {
        return Ok(None);
    };
    if next_root == current_root
        && parameters.as_slice() == mapped_parameters
        && arguments.as_slice() == type_arguments
        && branches == current_branches
    {
        if !aliased {
            return Ok(None);
        }
        let mut count = tail_count;
        while count < CONDITIONAL_TAIL_RECURSION_LIMIT {
            count += 1;
        }
        return Err(ConditionalTypeError::TailRecursionLimit {
            count,
            limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
        });
    }

    let next_count = tail_count + usize::from(aliased);
    instantiate_conditional_root(
        store,
        ConditionalRootInstantiation {
            conditional_type: branch,
            type_arguments: &arguments,
            branches,
            alias: None,
            alias_source: None,
            for_constraint,
            input_recovery: None,
        },
        global_types,
        Some(session),
        next_count,
        source,
    )
    .map(Some)
}

fn conditional_node_has_alias_owner(store: &CanonicalTypeMapperStore, node: NodeRef) -> bool {
    conditional_alias_declaration(store, node).is_some()
}

fn conditional_alias_declaration(
    store: &CanonicalTypeMapperStore,
    mut node: NodeRef,
) -> Option<NodeRef> {
    loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) else {
            return None;
        };
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedType) => node = parent,
            Some(SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration) => {
                return Some(parent);
            }
            _ => return None,
        }
    }
}

fn stored_alias_identity(
    store: &CanonicalTypeMapperStore,
    alias: TypeAliasId,
) -> Result<ConditionalAliasIdentity<'_>, ConditionalTypeError> {
    let record = store
        .type_alias(alias)
        .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
    Ok(ConditionalAliasIdentity {
        symbol: record
            .symbol()
            .ok_or(ConditionalTypeError::InvalidAlias(alias))?,
        type_arguments: record.type_arguments().unwrap_or_default(),
    })
}

fn validate_alias_identity(
    store: &CanonicalTypeMapperStore,
    alias: ConditionalAliasIdentity<'_>,
    visiting: &mut HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_alias_identity_worker(
        store,
        alias,
        visiting,
        array_targets,
        ConditionalValidation::Operational(None),
    )
}

fn validate_alias_identity_worker(
    store: &CanonicalTypeMapperStore,
    alias: ConditionalAliasIdentity<'_>,
    visiting: &mut HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<(), ConditionalTypeError> {
    let symbol = store
        .symbol(alias.symbol)
        .ok_or(ConditionalTypeError::InvalidAliasSymbol(alias.symbol))?;
    if !symbol.flags().contains(SymbolFlags::TYPE_ALIAS)
        || malformed_alias_merge(symbol.flags())
        || symbol.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(alias.symbol) != Some(alias.symbol)
        || symbol.declarations().is_none_or(|declarations| {
            !matches!(declarations, [declaration] if matches!(
                store.source_node_kind(*declaration),
                Some(SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration)
            ))
        })
    {
        return Err(ConditionalTypeError::InvalidAliasSymbol(alias.symbol));
    }
    for argument in alias.type_arguments {
        validation.operand(store, *argument, visiting, array_targets)?;
    }
    Ok(())
}

fn validate_root_alias(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer_parameters: &[TypeId],
    alias: Option<TypeAliasId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_root_alias_worker(
        store,
        node,
        outer_parameters,
        alias,
        array_targets,
        ConditionalValidation::Operational(None),
    )
}

fn validate_root_alias_worker(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    outer_parameters: &[TypeId],
    alias: Option<TypeAliasId>,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<(), ConditionalTypeError> {
    let Some(alias) = alias else {
        return Ok(());
    };
    let identity = stored_alias_identity(store, alias)?;
    validate_alias_identity_worker(
        store,
        identity,
        &mut HashSet::new(),
        array_targets,
        validation,
    )?;
    let declaration = conditional_alias_declaration(store, node)
        .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
    if store
        .symbol(identity.symbol)
        .and_then(|symbol| symbol.declarations())
        != Some(&[declaration][..])
    {
        return Err(ConditionalTypeError::InvalidAlias(alias));
    }
    let own_parameters = outer_parameters
        .iter()
        .copied()
        .filter(|parameter| {
            cached_ordinary_type_parameter_owner(store, *parameter)
                .and_then(|symbol| store.symbol(symbol))
                .and_then(|symbol| symbol.declarations())
                .is_some_and(|declarations| {
                    matches!(declarations, [parameter]
                    if store.source_node_parent(*parameter)
                        == Some(SourceNodeParent::Parent(declaration)))
                })
        })
        .collect::<Vec<_>>();
    if identity.type_arguments != own_parameters.as_slice() {
        return Err(ConditionalTypeError::InvalidAlias(alias));
    }
    Ok(())
}

fn mapped_root_alias(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    parameters: &[TypeId],
    arguments: &[TypeId],
) -> Result<Option<(SemanticSymbolId, Vec<TypeId>)>, ConditionalTypeError> {
    let Some(alias) = store
        .conditional_root(root)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?
        .alias()
    else {
        return Ok(None);
    };
    let identity = stored_alias_identity(store, alias)?;
    let type_arguments = identity
        .type_arguments
        .iter()
        .map(|parameter| {
            parameters
                .iter()
                .position(|candidate| candidate == parameter)
                .map_or(*parameter, |index| arguments[index])
        })
        .collect();
    Ok(Some((identity.symbol, type_arguments)))
}

#[allow(clippy::too_many_arguments)] // Reuses only the current query's already proved result graph.
fn deferred_conditional_in_query(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    check_type: TypeId,
    extends_type: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
    arrays: Option<CanonicalArrayTargets>,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
    retained_result: Option<TypeId>,
) -> Result<TypeId, ConditionalTypeError> {
    if !is_source_query(source) {
        return deferred_conditional(
            store,
            root,
            check_type,
            extends_type,
            parameters,
            arguments,
            alias,
            arrays,
        );
    }
    let validation = ConditionalValidation::Operational(source.as_deref());
    if let Some(retained) = retained_result {
        let definition = conditional_definition_worker(store, root, arrays, validation)?;
        let mapped_alias = mapped_root_alias(store, root, parameters, arguments)?;
        let expected_alias = alias.map(|(identity, _)| identity).or_else(|| {
            mapped_alias
                .as_ref()
                .map(|(symbol, arguments)| ConditionalAliasIdentity {
                    symbol: *symbol,
                    type_arguments: arguments,
                })
        });
        let mut pending = vec![retained];
        let mut visited = HashSet::new();
        while let Some(candidate) = pending.pop() {
            if !visited.insert(candidate) {
                continue;
            }
            let record = store
                .type_payload(candidate)
                .ok_or(ConditionalTypeError::InvalidType(candidate))?;
            if let TypeData::Union(union) = record.data() {
                pending.extend(union.union.types.iter().copied());
            } else if matches!(record.data(), TypeData::Conditional(_)) {
                let proof =
                    validated_conditional_production_worker(store, candidate, arrays, validation)?;
                let exact_mapping =
                    proof.mapped_parameters == parameters && proof.type_arguments == arguments;
                let identity_mapping = proof.mapper.is_none()
                    && parameters == arguments
                    && proof.mapped_parameters == proof.type_arguments;
                if proof.definition == definition
                    && proof.check_type == check_type
                    && proof.extends_type == extends_type
                    && (exact_mapping || identity_mapping)
                    && proof.alias.as_ref().map(RetainedConditionalAlias::identity)
                        == expected_alias
                    && proof.alias_reference == alias.map(|(_, reference)| reference)
                {
                    return Ok(candidate);
                }
            }
        }
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    deferred_conditional_worker(
        store,
        root,
        check_type,
        extends_type,
        parameters,
        arguments,
        alias,
        arrays,
        validation,
    )
}

#[allow(clippy::too_many_arguments)] // Keeps the deferred root, mapper inputs, alias, and array targets explicit.
fn deferred_conditional(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    check_type: TypeId,
    extends_type: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, ConditionalTypeError> {
    deferred_conditional_worker(
        store,
        root,
        check_type,
        extends_type,
        parameters,
        arguments,
        alias,
        array_targets,
        ConditionalValidation::Operational(None),
    )
}

#[allow(clippy::too_many_arguments)] // The same allocator also serves the checked source route.
fn deferred_conditional_worker(
    store: &mut CanonicalTypeMapperStore,
    root: ConditionalRootId,
    check_type: TypeId,
    extends_type: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<(ConditionalAliasIdentity<'_>, NodeRef)>,
    array_targets: Option<CanonicalArrayTargets>,
    validation: ConditionalValidation<'_>,
) -> Result<TypeId, ConditionalTypeError> {
    let alias_reference = alias.map(|(_, reference)| reference);
    let alias = alias.map(|(identity, _)| identity);
    let definition = conditional_definition_worker(store, root, array_targets, validation)?;
    let mapped_alias = mapped_root_alias(store, root, parameters, arguments)?;
    let alias = alias.or_else(|| {
        mapped_alias
            .as_ref()
            .map(|(symbol, arguments)| ConditionalAliasIdentity {
                symbol: *symbol,
                type_arguments: arguments,
            })
    });
    if let Some(identity) = alias {
        validate_alias_identity_worker(
            store,
            identity,
            &mut HashSet::new(),
            array_targets,
            validation,
        )?;
    }
    if !store.try_reserve_conditional_productions(1, 0)
        || !store.try_reserve_types(1)
        || !store.try_reserve_type_aliases(usize::from(alias.is_some()))
        || !store.try_reserve_mappers(usize::from(
            !parameters.is_empty() && parameters != arguments,
        ))
    {
        return Err(ConditionalTypeError::Capacity);
    }
    let alias = if let Some(identity) = alias {
        let root_alias = store
            .conditional_root(root)
            .and_then(super::type_records::ConditionalRoot::alias);
        if root_alias.is_some_and(|alias| stored_alias_identity(store, alias) == Ok(identity)) {
            root_alias
        } else {
            let alias = store
                .alloc_type_alias(Some(identity.symbol))
                .ok_or(ConditionalTypeError::InvalidAliasSymbol(identity.symbol))?;
            if !store.set_type_alias_arguments(
                alias,
                (!identity.type_arguments.is_empty()).then(|| identity.type_arguments.to_vec()),
            ) {
                return Err(ConditionalTypeError::InvalidAlias(alias));
            }
            Some(alias)
        }
    } else {
        None
    };
    let mapper = if parameters.is_empty() || parameters == arguments {
        None
    } else {
        Some(
            store
                .new_type_mapper(parameters.to_vec(), arguments.to_vec())
                .ok_or(ConditionalTypeError::InvalidInstantiationCache(root))?,
        )
    };
    let conditional = store
        .alloc_conditional_type(root, check_type, extends_type, mapper, None)
        .ok_or(ConditionalTypeError::InvalidRoot(root))?;
    if !store.set_type_alias(conditional, alias) {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    let proof = ConditionalTypeProduction {
        type_: conditional,
        definition,
        check_type,
        extends_type,
        mapper,
        mapped_parameters: parameters.to_vec(),
        type_arguments: arguments.to_vec(),
        alias: retain_conditional_alias_worker(store, alias, array_targets, validation)?,
        alias_reference,
    };
    if !store.publish_conditional_type_production(proof) {
        return Err(ConditionalTypeError::InvalidConditional(conditional));
    }
    Ok(conditional)
}

fn validate_request(
    store: &CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_request_worker(
        store,
        request.into(),
        Some(request.branches),
        array_targets,
        None,
    )
}

fn validate_request_worker(
    store: &CanonicalTypeMapperStore,
    request: SourceConditionalTypeRequest<'_>,
    branches: Option<ConditionalTypeBranches>,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    if !store.contains_node_ref(request.node)
        || store.source_node_kind(request.node) != Some(SyntaxKind::ConditionalType)
    {
        return Err(ConditionalTypeError::InvalidNode(request.node));
    }
    validate_conditional_node_link_shape(store, request.node)?;
    let mut visiting = HashSet::new();
    validate_conditional_operand_with_source(
        store,
        request.check_type,
        &mut visiting,
        array_targets,
        source,
    )?;
    validate_conditional_operand_with_source(
        store,
        request.extends_type,
        &mut visiting,
        array_targets,
        source,
    )?;
    if let Some(branches) = branches {
        validate_branch_types(store, branches, array_targets)?;
    }
    validate_root_alias_worker(
        store,
        request.node,
        request.outer_type_parameters.unwrap_or_default(),
        request.alias,
        array_targets,
        ConditionalValidation::Operational(source),
    )?;
    let mut seen = HashSet::new();
    for parameter in request
        .outer_type_parameters
        .unwrap_or_default()
        .iter()
        .chain(request.infer_type_parameters)
    {
        if !matches!(
            store.type_payload(*parameter).map(TypeRecord::data),
            Some(TypeData::TypeParameter(_))
        ) {
            return Err(ConditionalTypeError::InvalidTypeParameter(*parameter));
        }
        if !seen.insert(*parameter) {
            return Err(ConditionalTypeError::DuplicateTypeParameter(*parameter));
        }
    }
    Ok(())
}

fn validate_conditional_operand(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_conditional_operand_with_source(store, type_, visiting, array_targets, None)
}

fn validate_conditional_operand_with_source(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    visiting: &mut HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    if !visiting.insert(type_) {
        return Ok(());
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    if is_global_this_type_candidate(store, None, type_) {
        let Some(source) = source else {
            return Err(RelationUnavailable::UnresolvedStructuredMembers(type_).into());
        };
        let Some(members) = source.global_this_members() else {
            return Err(RelationUnavailable::GlobalThisMembersDemand { receiver: type_ }.into());
        };
        if members.receiver() != type_ {
            return Err(RelationUnavailable::InvalidStructuredMembers(type_).into());
        }
        members
            .validate(store)
            .map_err(ConditionalTypeError::Declared)?;
        visiting.remove(&type_);
        return Ok(());
    }
    let mut dependencies = Vec::new();
    if let Some(alias) = record.alias() {
        let alias_record = store
            .type_alias(alias)
            .ok_or(ConditionalTypeError::InvalidAlias(alias))?;
        dependencies.extend_from_slice(alias_record.type_arguments().unwrap_or_default());
    }
    let generic_callable = super::instantiated_members::validate_generic_interface_callable(
        store,
        type_,
        array_targets,
    );
    match generic_callable.as_ref() {
        Some(StoredCallableSetValidation::Valid { edges, .. }) => {
            dependencies.extend_from_slice(edges);
        }
        Some(StoredCallableSetValidation::Pending { .. }) => {
            // A reference can be an inference operand before its members are read.
            // Validate its declared template and arguments without publishing members.
            dependencies.extend(
                super::instantiated_members::validated_generic_interface_type_edges(
                    store,
                    type_,
                    array_targets,
                )
                .map_err(|_| RelationUnavailable::MalformedFunctionType(type_))?,
            );
        }
        Some(_) => return Err(RelationUnavailable::MalformedFunctionType(type_).into()),
        None => match validate_stored_declared_call_set(store, type_) {
            StoredDeclaredCallSetValidation::Malformed => {
                return Err(RelationUnavailable::MalformedFunctionType(type_).into());
            }
            StoredDeclaredCallSetValidation::Valid(edges) => dependencies.extend(edges),
            StoredDeclaredCallSetValidation::NotDeclaredCallSet => {}
        },
    }

    if generic_callable.is_none()
        && let Some(structured) = record.data().structured()
    {
        let signatures = structured.signatures.as_deref().unwrap_or_default();
        if structured.call_signature_count > signatures.len() {
            return Err(RelationUnavailable::MalformedStructuredType(type_).into());
        }
        let mut unique = HashSet::with_capacity(signatures.len());
        for (index, signature) in signatures.iter().copied().enumerate() {
            let signature_record = store
                .signature(signature)
                .ok_or_else(|| invalid_conditional_signature(store, signature))?;
            if !unique.insert(signature)
                || signature_record.flags().contains(SignatureFlags::CONSTRUCT)
                    != (index >= structured.call_signature_count)
            {
                return Err(invalid_conditional_signature(store, signature));
            }
            if matches!(record.data(), TypeData::Object(_) | TypeData::Interface(_))
                && store
                    .declared_call_set_type_for_signature(signature)
                    .is_some_and(|owner| owner != type_)
            {
                return Err(RelationUnavailable::MalformedFunctionType(type_).into());
            }
            let return_type = signature_record
                .resolved_return_type()
                .ok_or(RelationUnavailable::UnresolvedSignatureReturn(signature))?;
            dependencies.push(return_type);
            dependencies.extend(conditional_signature_parameter_types(
                store,
                type_,
                signature,
                array_targets,
            )?);
            dependencies.extend(conditional_signature_this_type(
                store,
                signature,
                array_targets,
            )?);
            if let Some(mapper) = signature_record.mapper()
                && store.mapper_payload(mapper).is_none()
            {
                return Err(ConditionalTypeError::InvalidMapper(mapper));
            }
        }
    }

    if generic_callable.is_none()
        && matches!(record.data(), TypeData::Object(_) | TypeData::Interface(_))
        && record.data().structured().is_some_and(|structured| {
            structured.properties.is_some() && structured.signatures.is_none()
        })
    {
        match super::object_members::validate_resolved_declared_property_type_graph(store, type_) {
            super::object_members::DeclaredPropertyTypeGraphValidation::Traversable(edges) => {
                dependencies.extend(edges);
            }
            super::object_members::DeclaredPropertyTypeGraphValidation::Opaque => {}
            super::object_members::DeclaredPropertyTypeGraphValidation::Malformed => {
                return Err(RelationUnavailable::InvalidStructuredMembers(type_).into());
            }
        }
    }

    match record.data() {
        TypeData::Union(union) => dependencies.extend_from_slice(&union.union.types),
        TypeData::Intersection(intersection) => {
            dependencies.extend_from_slice(&intersection.intersection.types);
        }
        TypeData::TypeReference(reference) => {
            dependencies.extend_from_slice(
                reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            dependencies.extend(reference.object.target);
        }
        TypeData::Interface(interface) => {
            dependencies.extend_from_slice(
                interface
                    .reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            dependencies.extend(interface.reference.object.target);
        }
        TypeData::Tuple(tuple) => {
            dependencies.extend_from_slice(
                tuple
                    .interface
                    .reference
                    .resolved_type_arguments
                    .as_deref()
                    .unwrap_or_default(),
            );
            dependencies.extend(tuple.interface.reference.object.target);
        }
        TypeData::Object(object) => dependencies.extend(object.target),
        TypeData::TypeParameter(parameter) => dependencies.extend(parameter.constraint),
        TypeData::Index(index) => dependencies.push(index.target),
        TypeData::IndexedAccess(indexed) => {
            dependencies.extend([indexed.object_type, indexed.index_type]);
        }
        TypeData::TemplateLiteral(template) => dependencies.extend_from_slice(&template.types),
        TypeData::StringMapping(mapping) => dependencies.push(mapping.target),
        TypeData::Conditional(conditional) => {
            dependencies.extend([conditional.check_type, conditional.extends_type]);
        }
        _ => {}
    }
    for dependency in dependencies {
        validate_conditional_operand_with_source(
            store,
            dependency,
            visiting,
            array_targets,
            source,
        )?;
    }
    visiting.remove(&type_);
    Ok(())
}

fn validate_cached_conditional(
    store: &CanonicalTypeMapperStore,
    request: ConditionalTypeRequest<'_>,
    cached: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<TypeId, ConditionalTypeError> {
    validate_cached_conditional_with_source(store, request.into(), cached, array_targets, None)
}

fn validate_cached_conditional_with_source(
    store: &CanonicalTypeMapperStore,
    request: SourceConditionalTypeRequest<'_>,
    cached: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    let proof = store
        .conditional_query_production(ConditionalQueryKey::Node(request.node))
        .ok_or(ConditionalTypeError::InvalidTypeNodeCache(request.node))?;
    if proof.result != cached
        || proof.definition.check_type != request.check_type
        || proof.definition.extends_type != request.extends_type
        || proof.definition.infer_type_parameters != request.infer_type_parameters
        || proof.definition.outer_type_parameters.as_deref() != request.outer_type_parameters
        || proof.definition.alias
            != retain_conditional_alias_worker(
                store,
                request.alias,
                array_targets,
                ConditionalValidation::Operational(source),
            )?
    {
        return Err(ConditionalTypeError::InvalidTypeNodeCache(request.node));
    }
    validate_query_production_with_source(store, proof, array_targets, source)?;
    Ok(cached)
}

#[allow(clippy::too_many_arguments)] // The retained query must match each cache-key input.
fn validate_cached_instantiation(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    key: CacheHashKey,
    cached: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    for_constraint: bool,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    validate_cached_instantiation_with_source(
        store,
        root,
        key,
        cached,
        parameters,
        arguments,
        alias,
        for_constraint,
        array_targets,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // Checks the same retained key in the source-aware caller.
fn validate_cached_instantiation_with_source(
    store: &CanonicalTypeMapperStore,
    root: ConditionalRootId,
    key: CacheHashKey,
    cached: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    for_constraint: bool,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<(), ConditionalTypeError> {
    let proof = store
        .conditional_query_production(ConditionalQueryKey::Instantiation(root, key))
        .or_else(|| {
            if parameters != arguments
                || alias.is_some()
                || for_constraint
                || key != conditional_type_key_parts(parameters, None, false)
            {
                return None;
            }
            let node = store.conditional_root(root)?.node();
            store.conditional_query_production(ConditionalQueryKey::Node(node))
        })
        .ok_or(ConditionalTypeError::InvalidInstantiationCache(root))?;
    let retained_alias = proof
        .alias
        .as_ref()
        .map(|(symbol, arguments)| ConditionalAliasIdentity {
            symbol: *symbol,
            type_arguments: arguments,
        });
    if proof.definition.root != root
        || proof.result != cached
        || proof.type_arguments != arguments
        || retained_alias != alias
        || proof.for_constraint != for_constraint
    {
        return Err(ConditionalTypeError::InvalidInstantiationCache(root));
    }
    validate_query_production_with_source(store, proof, array_targets, source)
}

fn validate_owned_type(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<(), ConditionalTypeError> {
    store
        .type_payload(type_)
        .map(|_| ())
        .ok_or(ConditionalTypeError::InvalidType(type_))
}

fn validate_branch_types(
    store: &CanonicalTypeMapperStore,
    branches: ConditionalTypeBranches,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(), ConditionalTypeError> {
    for branch in [branches.true_type, branches.false_type] {
        validate_owned_type(store, branch)?;
        let record = store
            .type_payload(branch)
            .ok_or(ConditionalTypeError::InvalidType(branch))?;
        if let Some(alias) = record.alias() {
            stored_alias_identity(store, alias)?;
        }
        if matches!(record.data(), TypeData::Conditional(_)) {
            validated_conditional_production(store, branch, array_targets)?;
        }
    }
    Ok(())
}

fn conditional_type_key(
    store: &mut CanonicalTypeMapperStore,
    type_arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    for_constraint: bool,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<CacheHashKey, ConditionalTypeError> {
    conditional_type_key_with_source(
        store,
        type_arguments,
        alias,
        for_constraint,
        array_targets,
        None,
    )
}

fn conditional_type_key_with_source(
    store: &mut CanonicalTypeMapperStore,
    type_arguments: &[TypeId],
    alias: Option<ConditionalAliasIdentity<'_>>,
    for_constraint: bool,
    array_targets: Option<CanonicalArrayTargets>,
    source: Option<&dyn ConditionalBranchSource>,
) -> Result<CacheHashKey, ConditionalTypeError> {
    let alias = if let Some(alias) = alias {
        validate_alias_identity_worker(
            store,
            alias,
            &mut HashSet::new(),
            array_targets,
            ConditionalValidation::Operational(source),
        )?;
        let symbol = store
            .global_symbol_id(alias.symbol)
            .ok_or(ConditionalTypeError::InvalidAliasSymbol(alias.symbol))?;
        Some((symbol, alias.type_arguments))
    } else {
        None
    };
    Ok(conditional_type_key_parts(
        type_arguments,
        alias,
        for_constraint,
    ))
}

fn conditional_type_key_parts(
    type_arguments: &[TypeId],
    alias: Option<(u64, &[TypeId])>,
    for_constraint: bool,
) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    write_type_list(&mut hasher, type_arguments);
    if let Some((symbol, arguments)) = alias {
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        write_type_list(&mut hasher, arguments);
    } else {
        hasher.update(&[0]);
    }
    if for_constraint {
        hasher.update(b"!");
    }
    CacheHashKey::new(hasher.digest128())
}

fn write_type_list(hasher: &mut Xxh3, types: &[TypeId]) {
    hasher.update(
        &u64::try_from(types.len())
            .expect("conditional type-list length must fit the upstream encoding")
            .to_le_bytes(),
    );
    for type_ in types {
        hasher.update(&type_.get().to_le_bytes());
    }
}

#[derive(Clone, Debug)]
struct InferenceTupleShape {
    element_types: Vec<TypeId>,
    element_infos: Vec<TupleElementInfo>,
    min_length: usize,
    readonly: bool,
}

fn inference_tuple_shape(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<Option<InferenceTupleShape>, ConditionalTypeError> {
    let Some(shape) = store.canonical_tuple_shape(type_)? else {
        return Ok(None);
    };
    Ok(Some(InferenceTupleShape {
        element_types: shape.element_types().to_vec(),
        element_infos: shape.element_infos().to_vec(),
        min_length: shape.min_length(),
        readonly: shape.is_readonly(),
    }))
}

fn is_structural_inference_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<bool, ConditionalTypeError> {
    if inference_tuple_shape(store, target)?.is_some() {
        return Ok(true);
    }
    let record = store
        .type_payload(target)
        .ok_or(ConditionalTypeError::InvalidType(target))?;
    Ok(record.data().structured().is_some_and(|structured| {
        structured
            .properties
            .as_ref()
            .is_some_and(|properties| !properties.is_empty())
            || structured
                .signatures
                .as_ref()
                .is_some_and(|signatures| !signatures.is_empty())
    }))
}

fn map_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<TypeId, ConditionalTypeError> {
    validate_owned_type(store, type_)?;
    if parameters.is_empty()
        || !contains_mapped_type_parameter_with_array_targets(
            store,
            type_,
            parameters,
            global_types.map(CanonicalArrayTargets::from_global_types),
            &mut HashSet::new(),
        )?
    {
        return Ok(type_);
    }

    if let Some(tuple) = inference_tuple_shape(store, type_)? {
        let mut substituted = Vec::with_capacity(tuple.element_types.len());
        let mut element_infos = Vec::with_capacity(tuple.element_infos.len());
        for (element, info) in tuple.element_types.into_iter().zip(tuple.element_infos) {
            let mapped = map_type(store, element, parameters, arguments, global_types, session)?;
            if info.flags().intersects(ElementFlags::VARIADIC)
                && let Some(mapped_tuple) = inference_tuple_shape(store, mapped)?
                && mapped_tuple
                    .element_infos
                    .iter()
                    .all(|element| !element.flags().intersects(ElementFlags::VARIABLE))
            {
                substituted.extend(mapped_tuple.element_types);
                element_infos.extend(mapped_tuple.element_infos);
            } else {
                substituted.push(mapped);
                element_infos.push(info);
            }
        }
        let mut request =
            CanonicalTupleTypeRequest::new(&substituted, &element_infos, tuple.readonly);
        if let Some(global_types) = global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        return store
            .create_canonical_tuple_type(request)
            .map_err(Into::into);
    }

    let template = match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::TemplateLiteral(template)) => {
            Some((template.texts.clone(), template.types.clone()))
        }
        _ => None,
    };
    if let Some((texts, types)) = template {
        let mut mapped = Vec::with_capacity(types.len());
        for placeholder in types {
            mapped.push(map_type(
                store,
                placeholder,
                parameters,
                arguments,
                global_types,
                session,
            )?);
        }
        return store
            .get_template_literal_type(&texts, &mapped)
            .map_err(Into::into);
    }

    let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
    instantiate_type_with_vector_and_session(
        store,
        type_,
        parameters,
        arguments,
        array_targets,
        session,
    )
    .map_err(Into::into)
}

fn map_type_with_source(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    let Some(source) = source.as_deref_mut() else {
        return map_type(store, type_, parameters, arguments, global_types, session);
    };
    let globals = global_types.ok_or(ConditionalTypeError::MissingBootstrap)?;
    if source.source_query_options().is_some()
        && (parameters.is_empty() || is_global_this_type_candidate(store, Some(globals), type_))
        && !matches!(
            store.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::Conditional(_))
        )
    {
        if parameters.len() != arguments.len() {
            return Err(InstantiationError::InvalidType(type_).into());
        }
        for endpoint in parameters.iter().chain(arguments) {
            if store.type_payload(*endpoint).is_none() {
                return Err(InstantiationError::InvalidType(*endpoint).into());
            }
        }
        validate_conditional_operand_with_source(
            store,
            type_,
            &mut HashSet::new(),
            Some(CanonicalArrayTargets::from_global_types(globals)),
            Some(source),
        )?;
        return Ok(type_);
    }
    if source.source_query_options().is_some()
        && matches!(
            store.type_payload(type_).map(TypeRecord::data),
            Some(TypeData::Object(_))
        )
        && conditional_identity_requires_source(store, type_, &mut HashSet::new())?
    {
        validate_conditional_operand_with_source(
            store,
            type_,
            &mut HashSet::new(),
            Some(CanonicalArrayTargets::from_global_types(globals)),
            Some(source),
        )?;
        // Nested global objects need a source-aware object instantiator. This
        // query admits only an empty mapper or the exact global leaf above.
        return Err(InstantiationError::UnsupportedType(type_).into());
    }
    super::instantiate::instantiate_type_with_vector_and_source(
        store, type_, parameters, arguments, globals, session, source,
    )
    .map_err(Into::into)
}

#[allow(clippy::too_many_arguments)] // Inference keeps its mapper and current query together.
fn map_inference_type(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    arguments: &[TypeId],
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    if is_source_query(query) {
        map_type_with_source(store, type_, parameters, arguments, globals, session, query)
    } else {
        map_type(store, type_, parameters, arguments, globals, session)
    }
}

fn map_stored_type_in_query(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: Option<TypeMapperId>,
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    if !is_source_query(source) {
        return map_type_with_stored_mapper(store, type_, mapper, globals, session);
    }
    validate_owned_type(store, type_)?;
    let Some(mapper) = mapper else {
        return Ok(type_);
    };
    super::instantiate::instantiate_type_with_source(
        store,
        type_,
        mapper,
        globals.ok_or(ConditionalTypeError::MissingBootstrap)?,
        session,
        source
            .as_deref_mut()
            .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
    )
    .map_err(Into::into)
}

fn map_type_with_stored_mapper(
    store: &mut CanonicalTypeMapperStore,
    type_: TypeId,
    mapper: Option<TypeMapperId>,
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
) -> Result<TypeId, ConditionalTypeError> {
    validate_owned_type(store, type_)?;
    let Some(mapper) = mapper else {
        return Ok(type_);
    };
    if store.mapper_payload(mapper).is_none() {
        return Err(ConditionalTypeError::InvalidMapper(mapper));
    }
    if let Some(tuple) = inference_tuple_shape(store, type_)? {
        let mut substituted = Vec::with_capacity(tuple.element_types.len());
        for element in tuple.element_types {
            substituted.push(map_type_with_stored_mapper(
                store,
                element,
                Some(mapper),
                global_types,
                session,
            )?);
        }
        let mut request =
            CanonicalTupleTypeRequest::new(&substituted, &tuple.element_infos, tuple.readonly);
        if let Some(global_types) = global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        return store
            .create_canonical_tuple_type(request)
            .map_err(Into::into);
    }
    let template = match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::TemplateLiteral(template)) => {
            Some((template.texts.clone(), template.types.clone()))
        }
        _ => None,
    };
    if let Some((texts, types)) = template {
        let mut substituted = Vec::with_capacity(types.len());
        for placeholder in types {
            substituted.push(map_type_with_stored_mapper(
                store,
                placeholder,
                Some(mapper),
                global_types,
                session,
            )?);
        }
        return store
            .get_template_literal_type(&texts, &substituted)
            .map_err(Into::into);
    }
    instantiate_type_with_session(
        store,
        type_,
        mapper,
        global_types.map(CanonicalArrayTargets::from_global_types),
        session,
    )
    .map_err(Into::into)
}

#[allow(dead_code)] // Retains the existing store-only entry point.
fn contains_mapped_type_parameter(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    contains_mapped_type_parameter_with_array_targets(store, type_, parameters, None, visiting)
}

fn contains_mapped_type_parameter_with_array_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    parameters: &[TypeId],
    array_targets: Option<CanonicalArrayTargets>,
    visiting: &mut HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    if !visiting.insert(type_) {
        return Ok(false);
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let mut result =
        match record.data() {
            TypeData::TypeParameter(_) => parameters.contains(&type_),
            TypeData::Union(union) => union.union.types.iter().try_fold(false, |found, item| {
                Ok::<_, ConditionalTypeError>(
                    found
                        || contains_mapped_type_parameter_with_array_targets(
                            store,
                            *item,
                            parameters,
                            array_targets,
                            visiting,
                        )?,
                )
            })?,
            TypeData::Intersection(intersection) => intersection
                .intersection
                .types
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found
                            || contains_mapped_type_parameter_with_array_targets(
                                store,
                                *item,
                                parameters,
                                array_targets,
                                visiting,
                            )?,
                    )
                })?,
            TypeData::TypeReference(reference) => reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found
                            || contains_mapped_type_parameter_with_array_targets(
                                store,
                                *item,
                                parameters,
                                array_targets,
                                visiting,
                            )?,
                    )
                })?,
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found
                            || contains_mapped_type_parameter_with_array_targets(
                                store,
                                *item,
                                parameters,
                                array_targets,
                                visiting,
                            )?,
                    )
                })?,
            TypeData::Tuple(tuple) => tuple
                .interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found
                            || contains_mapped_type_parameter_with_array_targets(
                                store,
                                *item,
                                parameters,
                                array_targets,
                                visiting,
                            )?,
                    )
                })?,
            TypeData::Index(index) => contains_mapped_type_parameter_with_array_targets(
                store,
                index.target,
                parameters,
                array_targets,
                visiting,
            )?,
            TypeData::IndexedAccess(indexed) => {
                contains_mapped_type_parameter_with_array_targets(
                    store,
                    indexed.object_type,
                    parameters,
                    array_targets,
                    visiting,
                )? || contains_mapped_type_parameter_with_array_targets(
                    store,
                    indexed.index_type,
                    parameters,
                    array_targets,
                    visiting,
                )?
            }
            TypeData::Conditional(conditional) => {
                contains_mapped_type_parameter_with_array_targets(
                    store,
                    conditional.check_type,
                    parameters,
                    array_targets,
                    visiting,
                )? || contains_mapped_type_parameter_with_array_targets(
                    store,
                    conditional.extends_type,
                    parameters,
                    array_targets,
                    visiting,
                )?
            }
            TypeData::TemplateLiteral(template) => {
                template
                    .types
                    .iter()
                    .try_fold(false, |found, placeholder| {
                        Ok::<_, ConditionalTypeError>(
                            found
                                || contains_mapped_type_parameter_with_array_targets(
                                    store,
                                    *placeholder,
                                    parameters,
                                    array_targets,
                                    visiting,
                                )?,
                        )
                    })?
            }
            _ => false,
        };
    if !result && let Some(structured) = record.data().structured() {
        for signature in structured.signatures.as_deref().unwrap_or_default() {
            let signature_record = store
                .signature(*signature)
                .ok_or_else(|| invalid_conditional_signature(store, *signature))?;
            let outer_parameters: Vec<_> = parameters
                .iter()
                .copied()
                .filter(|parameter| !signature_record.type_parameters().contains(parameter))
                .collect();
            let mut edges =
                conditional_signature_parameter_types(store, type_, *signature, array_targets)?;
            edges.extend(conditional_signature_this_type(
                store,
                *signature,
                array_targets,
            )?);
            edges.extend(signature_record.resolved_return_type());
            for edge in edges {
                if contains_mapped_type_parameter_with_array_targets(
                    store,
                    edge,
                    &outer_parameters,
                    array_targets,
                    visiting,
                )? {
                    result = true;
                    break;
                }
            }
            if result {
                break;
            }
        }
    }
    visiting.remove(&type_);
    Ok(result)
}

// Callable edges can need mapping without making the callable a deferred operand.
fn conditional_operand_is_deferred(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    excluded: &HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, ConditionalTypeError> {
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    if matches!(record.data(), TypeData::Object(_)) {
        match super::callable_sets::validate_stored_callable_set_with_array_targets(
            store,
            type_,
            array_targets,
        ) {
            StoredCallableSetValidation::Valid { projection, .. }
                if !projection.call_signatures.is_empty()
                    && projection.construct_signatures.is_empty() =>
            {
                return Ok(false);
            }
            StoredCallableSetValidation::Malformed { .. } => {
                return Err(ConditionalTypeError::InvalidType(type_));
            }
            StoredCallableSetValidation::Pending { .. } => {
                return Err(RelationUnavailable::UnresolvedStructuredMembers(type_).into());
            }
            _ => {}
        }
    }
    contains_type_parameter_with_array_targets(store, type_, excluded, array_targets)
}

#[allow(dead_code)] // Retains the existing store-only entry point.
fn contains_type_parameter(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    excluded: &HashSet<TypeId>,
) -> Result<bool, ConditionalTypeError> {
    contains_type_parameter_with_array_targets(store, type_, excluded, None)
}

fn contains_type_parameter_with_array_targets(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    excluded: &HashSet<TypeId>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, ConditionalTypeError> {
    fn visit(
        store: &CanonicalTypeMapperStore,
        type_: TypeId,
        excluded: &HashSet<TypeId>,
        array_targets: Option<CanonicalArrayTargets>,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<bool, ConditionalTypeError> {
        if !visiting.insert(type_) {
            return Ok(false);
        }
        let record = store
            .type_payload(type_)
            .ok_or(ConditionalTypeError::InvalidType(type_))?;
        let mut result = match record.data() {
            TypeData::TypeParameter(_) => !excluded.contains(&type_),
            TypeData::Union(union) => union.union.types.iter().try_fold(false, |found, item| {
                Ok::<_, ConditionalTypeError>(
                    found || visit(store, *item, excluded, array_targets, visiting)?,
                )
            })?,
            TypeData::Intersection(intersection) => intersection
                .intersection
                .types
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found || visit(store, *item, excluded, array_targets, visiting)?,
                    )
                })?,
            TypeData::TypeReference(reference) => reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found || visit(store, *item, excluded, array_targets, visiting)?,
                    )
                })?,
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found || visit(store, *item, excluded, array_targets, visiting)?,
                    )
                })?,
            TypeData::Tuple(tuple) => tuple
                .interface
                .reference
                .resolved_type_arguments
                .as_deref()
                .unwrap_or_default()
                .iter()
                .try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found || visit(store, *item, excluded, array_targets, visiting)?,
                    )
                })?,
            TypeData::Index(index) => {
                visit(store, index.target, excluded, array_targets, visiting)?
            }
            TypeData::IndexedAccess(indexed) => {
                visit(
                    store,
                    indexed.object_type,
                    excluded,
                    array_targets,
                    visiting,
                )? || visit(store, indexed.index_type, excluded, array_targets, visiting)?
            }
            TypeData::Conditional(_) => true,
            TypeData::TemplateLiteral(template) => {
                template.types.iter().try_fold(false, |found, item| {
                    Ok::<_, ConditionalTypeError>(
                        found || visit(store, *item, excluded, array_targets, visiting)?,
                    )
                })?
            }
            _ => false,
        };
        if !result && let Some(structured) = record.data().structured() {
            for signature in structured.signatures.as_deref().unwrap_or_default() {
                let signature_record = store
                    .signature(*signature)
                    .ok_or_else(|| invalid_conditional_signature(store, *signature))?;
                let mut signature_excluded = excluded.clone();
                signature_excluded.extend(signature_record.type_parameters().iter().copied());
                for parameter in signature_record.type_parameters() {
                    let Some(TypeData::TypeParameter(parameter)) =
                        store.type_payload(*parameter).map(TypeRecord::data)
                    else {
                        return Err(invalid_conditional_signature(store, *signature));
                    };
                    if let Some(constraint) = parameter.constraint
                        && visit(
                            store,
                            constraint,
                            &signature_excluded,
                            array_targets,
                            visiting,
                        )?
                    {
                        result = true;
                        break;
                    }
                }
                if result {
                    break;
                }
                let return_type = signature_record
                    .resolved_return_type()
                    .ok_or_else(|| invalid_conditional_signature(store, *signature))?;
                if visit(
                    store,
                    return_type,
                    &signature_excluded,
                    array_targets,
                    visiting,
                )? {
                    result = true;
                    break;
                }
                let mut dependencies =
                    conditional_signature_parameter_types(store, type_, *signature, array_targets)?;
                dependencies.extend(conditional_signature_this_type(
                    store,
                    *signature,
                    array_targets,
                )?);
                for parameter in dependencies {
                    if visit(
                        store,
                        parameter,
                        &signature_excluded,
                        array_targets,
                        visiting,
                    )? {
                        result = true;
                        break;
                    }
                }
                if result {
                    break;
                }
            }
        }
        visiting.remove(&type_);
        Ok(result)
    }

    visit(store, type_, excluded, array_targets, &mut HashSet::new())
}

/// Reuses the conditional engine's deferred-operand proof for a simple source tuple.
pub(super) fn simple_tuple_operand_is_deferred(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    element_infos: &[TupleElementInfo],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<bool, ConditionalTypeError> {
    if element_infos.is_empty()
        || element_infos
            .iter()
            .any(|info| info.flags() != ElementFlags::REQUIRED)
    {
        return Ok(false);
    }
    let Some(shape) = store.canonical_tuple_shape(type_)? else {
        return Ok(false);
    };
    if shape.element_infos() != element_infos || shape.is_readonly() {
        return Err(ConditionalTypeError::InvalidType(type_));
    }
    match array_targets {
        Some(targets) => {
            store.validate_cached_array_capability_with_array_targets(targets, type_)?;
        }
        None => store.validate_cached_array_capability(type_)?,
    }
    validate_conditional_operand(store, type_, &mut HashSet::new(), array_targets)?;
    contains_type_parameter_with_array_targets(store, type_, &HashSet::new(), array_targets)
}

#[derive(Clone, Copy)]
struct ConditionalInferenceContext<'a> {
    infer_parameters: &'a [TypeId],
    mapped_parameters: &'a [TypeId],
    type_arguments: &'a [TypeId],
    global_types: Option<&'a CanonicalGlobalTypes>,
}

fn infer_from_types(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    let mark = session.limit_event_mark();
    let result =
        infer_from_types_worker(store, source, target, context, candidates, session, query)?;
    if source_recovery_type(session, mark, query)?.is_some() {
        // The enclosing evaluation returns the caller's recovery type. Stop
        // inference here so later properties cannot demand another value.
        return Ok(false);
    }
    Ok(result)
}

fn infer_from_types_worker(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    if let Some(index) = context
        .infer_parameters
        .iter()
        .position(|parameter| *parameter == target)
    {
        if !candidates[index].contains(&source) {
            candidates[index].push(source);
        }
        return Ok(true);
    }

    let source_tuple = inference_tuple_shape(store, source)?;
    let target_tuple = inference_tuple_shape(store, target)?;
    if let (Some(source_tuple), Some(target_tuple)) = (source_tuple, target_tuple) {
        return infer_from_tuple_types(
            store,
            &source_tuple,
            &target_tuple,
            context,
            candidates,
            session,
            query,
        );
    }

    let source_record = store
        .type_payload(source)
        .ok_or(ConditionalTypeError::InvalidType(source))?;
    let target_record = store
        .type_payload(target)
        .ok_or(ConditionalTypeError::InvalidType(target))?;
    if let TypeData::TemplateLiteral(target_template) = target_record.data() {
        let target_texts = target_template.texts.clone();
        let target_types = target_template.types.clone();
        let (source_texts, source_types) = match source_record.data() {
            TypeData::Literal(literal) => match &literal.value {
                LiteralValue::String(value) => (vec![value.clone()], Vec::new()),
                _ => return Ok(false),
            },
            TypeData::TemplateLiteral(template) => (template.texts.clone(), template.types.clone()),
            _ => return Ok(false),
        };
        let Some(matches) = infer_template_literal_matches_in_query(
            store,
            &source_texts,
            &source_types,
            &target_texts,
            &target_types,
            context
                .global_types
                .map(CanonicalArrayTargets::from_global_types),
            session,
            is_source_query(query),
        )?
        else {
            return Ok(false);
        };
        for (source, target) in matches.into_iter().zip(target_types) {
            let candidate =
                template_inference_candidate(store, source, target, context.infer_parameters)?;
            if !infer_from_types(
                store, candidate, target, context, candidates, session, query,
            )? {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if let (TypeData::TypeReference(source_ref), TypeData::TypeReference(target_ref)) =
        (source_record.data(), target_record.data())
    {
        if source_ref.object.target != target_ref.object.target {
            return Ok(false);
        }
        let source_arguments = source_ref
            .resolved_type_arguments
            .as_ref()
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?
            .clone();
        let target_arguments = target_ref
            .resolved_type_arguments
            .as_ref()
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?
            .clone();
        if source_arguments.len() != target_arguments.len() {
            return Ok(false);
        }
        for (source, target) in source_arguments.into_iter().zip(target_arguments) {
            if !infer_from_types(store, source, target, context, candidates, session, query)? {
                return Ok(false);
            }
        }
        return Ok(true);
    }

    if target_record.data().structured().is_some() {
        if source_record.data().structured().is_none() {
            return if source_record
                .flags()
                .intersects(TypeFlags::ANY | TypeFlags::NEVER)
            {
                inference_assignability(store, source, target, context.global_types, session, query)
            } else {
                Ok(false)
            };
        }
        return infer_from_structured_types(
            store, source, target, context, candidates, session, query,
        );
    }
    if contains_type_parameter_with_array_targets(
        store,
        target,
        &HashSet::new(),
        context
            .global_types
            .map(CanonicalArrayTargets::from_global_types),
    )? {
        Err(ConditionalTypeError::UnsupportedInference { source, target })
    } else {
        inference_assignability(store, source, target, context.global_types, session, query)
    }
}

fn infer_from_tuple_types(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    let variable_indices = target
        .element_infos
        .iter()
        .enumerate()
        .filter_map(|(index, info)| {
            info.flags()
                .intersects(ElementFlags::VARIABLE)
                .then_some(index)
        })
        .collect::<Vec<_>>();
    let source_len = source.element_types.len();
    let target_len = target.element_types.len();
    if source_len < target.min_length {
        return Ok(false);
    }
    match variable_indices.as_slice() {
        [first, second] => {
            return infer_from_rest_and_variadic_tuple(
                store,
                source,
                target,
                [*first, *second],
                context,
                candidates,
                session,
                query,
            );
        }
        [_, _, _, ..] => return Ok(false),
        _ => {}
    }
    let Some(variable) = variable_indices.first().copied() else {
        if source_len > target_len {
            return Ok(false);
        }
        for (source, target) in source.element_types.iter().zip(&target.element_types) {
            if !infer_from_types(store, *source, *target, context, candidates, session, query)? {
                return Ok(false);
            }
        }
        return Ok(true);
    };

    let suffix_len = target_len - variable - 1;
    if source_len < variable + suffix_len {
        return Ok(false);
    }
    for index in 0..variable {
        if !infer_from_types(
            store,
            source.element_types[index],
            target.element_types[index],
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }
    for index in 0..suffix_len {
        let source_index = source_len - suffix_len + index;
        let target_index = variable + 1 + index;
        if !infer_from_types(
            store,
            source.element_types[source_index],
            target.element_types[target_index],
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }

    let end = source_len - suffix_len;
    let middle_types = &source.element_types[variable..end];
    if target.element_infos[variable]
        .flags()
        .intersects(ElementFlags::VARIADIC)
    {
        let middle_infos = &source.element_infos[variable..end];
        let mut request = CanonicalTupleTypeRequest::new(middle_types, middle_infos, false);
        if let Some(global_types) = context.global_types {
            request =
                request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
        }
        let middle = store.create_canonical_tuple_type(request)?;
        return infer_from_types(
            store,
            middle,
            target.element_types[variable],
            context,
            candidates,
            session,
            query,
        );
    }
    for element in middle_types {
        if !infer_from_types(
            store,
            *element,
            target.element_types[variable],
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)] // Keep inference inputs with the current source query and caller.
fn infer_from_rest_and_variadic_tuple(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    variable_indices: [usize; 2],
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    let [first, second] = variable_indices;
    if second != first + 1 {
        return Ok(false);
    }
    let (variadic, rest) = match (
        target.element_infos[first].flags(),
        target.element_infos[second].flags(),
    ) {
        (ElementFlags::VARIADIC, ElementFlags::REST) => (first, second),
        (ElementFlags::REST, ElementFlags::VARIADIC) => (second, first),
        _ => return Ok(false),
    };
    let variadic_type = target.element_types[variadic];
    if !context.infer_parameters.contains(&variadic_type) {
        return Ok(false);
    }
    let constraint = if is_source_query(query) {
        constraints::get_base_constraint_of_type_with_source(
            store,
            variadic_type,
            context
                .global_types
                .ok_or(ConditionalTypeError::MissingBootstrap)?,
            session,
            query
                .as_deref_mut()
                .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
        )?
    } else {
        constraints::get_base_constraint_of_type(store, variadic_type)?
    };
    let Some(constraint) = constraint else {
        return Ok(false);
    };
    validate_conditional_operand_with_source(
        store,
        constraint,
        &mut HashSet::new(),
        context
            .global_types
            .map(CanonicalArrayTargets::from_global_types),
        query.as_deref(),
    )?;
    let Some(constraint_shape) = inference_tuple_shape(store, constraint)? else {
        return Ok(false);
    };
    if constraint_shape
        .element_infos
        .iter()
        .chain(&source.element_infos)
        .any(|info| info.flags().intersects(ElementFlags::VARIABLE))
    {
        return Ok(false);
    }

    let prefix_len = first;
    let suffix_len = target.element_types.len() - second - 1;
    let implied_arity = constraint_shape.element_types.len();
    let Some(minimum_len) = prefix_len
        .checked_add(suffix_len)
        .and_then(|length| length.checked_add(implied_arity))
    else {
        return Ok(false);
    };
    if source.element_types.len() < minimum_len {
        return Ok(false);
    }
    for index in 0..prefix_len {
        if !infer_from_types(
            store,
            source.element_types[index],
            target.element_types[index],
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }
    for index in 0..suffix_len {
        let source_index = source.element_types.len() - suffix_len + index;
        let target_index = second + 1 + index;
        if !infer_from_types(
            store,
            source.element_types[source_index],
            target.element_types[target_index],
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }

    let middle_end = source.element_types.len() - suffix_len;
    let (variadic_start, rest_start, rest_end) = if variadic == first {
        (prefix_len, prefix_len + implied_arity, middle_end)
    } else {
        (
            middle_end - implied_arity,
            prefix_len,
            middle_end - implied_arity,
        )
    };
    for index in rest_start..rest_end {
        if !infer_from_types(
            store,
            source.element_types[index],
            target.element_types[rest],
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }

    let variadic_end = variadic_start + implied_arity;
    let mut request = CanonicalTupleTypeRequest::new(
        &source.element_types[variadic_start..variadic_end],
        &source.element_infos[variadic_start..variadic_end],
        false,
    );
    if let Some(global_types) = context.global_types {
        request =
            request.with_array_targets(CanonicalArrayTargets::from_global_types(global_types));
    }
    let captured = store.create_canonical_tuple_type(request)?;
    infer_from_types(
        store,
        captured,
        variadic_type,
        context,
        candidates,
        session,
        query,
    )
}

#[derive(Clone, Debug)]
struct StructuredInferenceShape {
    properties: Vec<SemanticSymbolId>,
    call_signatures: Vec<SignatureId>,
    construct_signatures: Vec<SignatureId>,
}

fn structured_inference_shape(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
    query: Option<&dyn ConditionalBranchSource>,
) -> Result<StructuredInferenceShape, ConditionalTypeError> {
    let query = query.filter(|source| source.source_query_options().is_some());
    validate_conditional_operand_with_source(
        store,
        type_,
        &mut HashSet::new(),
        array_targets,
        query,
    )?;
    if is_global_this_type_candidate(store, None, type_) {
        let members = query
            .and_then(|source| source.global_this_members())
            .ok_or(RelationUnavailable::UnresolvedStructuredMembers(type_))?;
        return Ok(StructuredInferenceShape {
            properties: members.properties().to_vec(),
            call_signatures: Vec::new(),
            construct_signatures: Vec::new(),
        });
    }
    if matches!(
        super::instantiated_members::validate_generic_interface_callable(
            store,
            type_,
            array_targets,
        ),
        Some(StoredCallableSetValidation::Pending { .. })
    ) {
        return Err(RelationUnavailable::UnresolvedStructuredMembers(type_).into());
    }
    let record = store
        .type_payload(type_)
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let structured = record
        .data()
        .structured()
        .ok_or(ConditionalTypeError::InvalidType(type_))?;
    let signatures = structured.signatures.as_deref().unwrap_or_default();
    if structured.call_signature_count > signatures.len() {
        return Err(ConditionalTypeError::UnsupportedInference {
            source: type_,
            target: type_,
        });
    }
    Ok(StructuredInferenceShape {
        properties: structured.properties.clone().unwrap_or_default(),
        call_signatures: signatures[..structured.call_signature_count].to_vec(),
        construct_signatures: signatures[structured.call_signature_count..].to_vec(),
    })
}

fn infer_from_structured_types(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    context: ConditionalInferenceContext<'_>,
    candidates: &mut [Vec<TypeId>],
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    let mark = session.limit_event_mark();
    if is_source_query(query) {
        for endpoint in [source, target] {
            if super::object_aliases::source_property_object_projection(store, endpoint)?.is_some()
            {
                super::instantiated_members::resolve_property_object_alias_members_with_array_targets(
                    store,
                    endpoint,
                    context
                        .global_types
                        .map(CanonicalArrayTargets::from_global_types),
                )?;
            }
        }
    }
    let source_shape = structured_inference_shape(
        store,
        source,
        context
            .global_types
            .map(CanonicalArrayTargets::from_global_types),
        query.as_deref(),
    )?;
    let target_shape = structured_inference_shape(
        store,
        target,
        context
            .global_types
            .map(CanonicalArrayTargets::from_global_types),
        query.as_deref(),
    )?;
    if target_shape.properties.is_empty()
        && target_shape.call_signatures.is_empty()
        && target_shape.construct_signatures.is_empty()
    {
        return inference_assignability(
            store,
            source,
            target,
            context.global_types,
            session,
            query,
        );
    }

    for target_property in target_shape.properties {
        let target_name = store
            .symbol(target_property)
            .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?
            .name()
            .to_owned();
        let Some(source_property) = source_shape.properties.iter().copied().find(|property| {
            store
                .symbol(*property)
                .is_some_and(|record| record.name() == target_name.as_ref())
        }) else {
            return Ok(false);
        };
        let source_type = inference_property_type(
            store,
            source,
            source_property,
            context.global_types,
            session,
            query,
        )?
        .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?;
        if source_recovery_type(session, mark, query)?.is_some() {
            return Ok(false);
        }
        let target_type = inference_property_type(
            store,
            target,
            target_property,
            context.global_types,
            session,
            query,
        )?
        .ok_or(ConditionalTypeError::UnsupportedInference { source, target })?;
        if source_recovery_type(session, mark, query)?.is_some() {
            return Ok(false);
        }
        let source_type = map_inference_type(
            store,
            source_type,
            context.mapped_parameters,
            context.type_arguments,
            context.global_types,
            session,
            query,
        )?;
        if source_recovery_type(session, mark, query)?.is_some() {
            return Ok(false);
        }
        let target_type = map_inference_type(
            store,
            target_type,
            context.mapped_parameters,
            context.type_arguments,
            context.global_types,
            session,
            query,
        )?;
        if source_recovery_type(session, mark, query)?.is_some() {
            return Ok(false);
        }
        if !infer_from_types(
            store,
            source_type,
            target_type,
            context,
            candidates,
            session,
            query,
        )? {
            return Ok(false);
        }
    }

    for (sources, targets) in [
        (
            source_shape.call_signatures.as_slice(),
            target_shape.call_signatures.as_slice(),
        ),
        (
            source_shape.construct_signatures.as_slice(),
            target_shape.construct_signatures.as_slice(),
        ),
    ] {
        if targets.is_empty() {
            continue;
        }
        if sources.is_empty() {
            return Ok(false);
        }
        for (index, target_signature) in targets.iter().copied().enumerate() {
            let source_index = sources.len().saturating_sub(targets.len()) + index;
            let source_signature = sources[source_index.min(sources.len() - 1)];
            let (source_this, source_parameters, source_minimum, source_return) =
                base_inference_signature_parts(
                    store,
                    source,
                    source_signature,
                    context.global_types,
                    session,
                    query,
                )?;
            let (target_this, target_parameters, _, target_return) = inference_signature_parts(
                store,
                target,
                target_signature,
                context
                    .global_types
                    .map(CanonicalArrayTargets::from_global_types),
            )?;
            let target_never_rest = store
                .signature(target_signature)
                .is_some_and(|signature| signature.has_rest_parameter())
                && store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                    target_parameters.as_slice() == [bootstrap.never_type]
                });
            if !target_never_rest && source_minimum > target_parameters.len() {
                return Ok(false);
            }
            // A sole never rest type accepts every source parameter list and
            // contains no inference parameters. Its receiver still participates.
            let value_pairs = source_parameters
                .into_iter()
                .zip(target_parameters)
                .filter(|_| !target_never_rest);
            // An absent source receiver produces no inference candidate.
            for (source_parameter, target_parameter) in
                source_this.zip(target_this).into_iter().chain(value_pairs)
            {
                let source_parameter = map_inference_type(
                    store,
                    source_parameter,
                    context.mapped_parameters,
                    context.type_arguments,
                    context.global_types,
                    session,
                    query,
                )?;
                let target_parameter = map_inference_type(
                    store,
                    target_parameter,
                    context.mapped_parameters,
                    context.type_arguments,
                    context.global_types,
                    session,
                    query,
                )?;
                let compatible = if contains_mapped_type_parameter_with_array_targets(
                    store,
                    target_parameter,
                    context.infer_parameters,
                    context
                        .global_types
                        .map(CanonicalArrayTargets::from_global_types),
                    &mut HashSet::new(),
                )? {
                    infer_from_types(
                        store,
                        source_parameter,
                        target_parameter,
                        context,
                        candidates,
                        session,
                        query,
                    )?
                } else {
                    inference_assignability(
                        store,
                        target_parameter,
                        source_parameter,
                        context.global_types,
                        session,
                        query,
                    )?
                };
                if !compatible {
                    return Ok(false);
                }
            }
            let source_return = map_inference_type(
                store,
                source_return,
                context.mapped_parameters,
                context.type_arguments,
                context.global_types,
                session,
                query,
            )?;
            let target_return = map_inference_type(
                store,
                target_return,
                context.mapped_parameters,
                context.type_arguments,
                context.global_types,
                session,
                query,
            )?;
            if !infer_from_types(
                store,
                source_return,
                target_return,
                context,
                candidates,
                session,
                query,
            )? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn inference_property_type(
    store: &mut CanonicalTypeMapperStore,
    receiver: TypeId,
    member: SemanticSymbolId,
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    if is_source_query(query)
        && super::object_aliases::source_property_object_projection(store, receiver)?.is_some()
    {
        return query
            .as_deref_mut()
            .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?
            .resolve_source_property_object_member(store, receiver, member, session)
            .map(Some);
    }
    if !is_source_query(query) || !is_global_this_type_candidate(store, globals, receiver) {
        return Ok(store
            .value_symbol_links(member)
            .and_then(|links| links.resolved_type));
    }
    let globals = globals.ok_or(ConditionalTypeError::MissingBootstrap)?;
    let query = query
        .as_deref_mut()
        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
    let members = query
        .global_this_members()
        .ok_or(RelationUnavailable::UnresolvedStructuredMembers(receiver))?;
    if members.receiver() != receiver || members.member(member).is_none() {
        return Err(RelationUnavailable::InvalidStructuredMembers(receiver).into());
    }
    members
        .validate(store)
        .map_err(ConditionalTypeError::Declared)?;
    let proof = query
        .resolve_global_this_member(store, receiver, member, session)
        .map_err(ConditionalTypeError::Declared)?;
    if proof.receiver() != receiver || proof.member() != member {
        return Err(RelationUnavailable::InvalidStructuredMembers(receiver).into());
    }
    query
        .validate_global_this_member_value_proof(
            store,
            &proof,
            globals,
            query
                .source_query_options()
                .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?
                .strict_function_types,
        )
        .map_err(ConditionalTypeError::Declared)?;
    Ok(Some(proof.type_id()))
}

#[track_caller]
fn invalid_conditional_signature(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
) -> ConditionalTypeError {
    if !store.relation_read_observation_is_active() {
        let record = store.signature(signature);
        let declaration = record.and_then(|record| record.declaration());
        let this = record.and_then(|record| record.this_parameter());
        super::source::observe_call_failure_detail(
            "conditional_signature_producer",
            format_args!(
                "line={} signature={signature:?} declaration={:?} target={:?} mapper={:?} return={:?} this={:?} arity={:?}",
                std::panic::Location::caller().line(),
                declaration.map(|node| (
                    node,
                    store.source_node_kind(node),
                    store.source_node_start(node),
                )),
                record.and_then(|record| record.target()),
                record.and_then(|record| record.mapper()),
                record.and_then(|record| record.resolved_return_type()),
                this.map(|symbol| (
                    symbol,
                    store
                        .value_symbol_links(symbol)
                        .and_then(|links| links.resolved_type),
                )),
                record.map(|record| (
                    record.min_argument_count(),
                    record.parameters().len(),
                    record.has_rest_parameter(),
                    record.type_parameters().len(),
                )),
            ),
        );
    }
    ConditionalTypeError::InvalidSignature(signature)
}

fn conditional_signature_parameter_types(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    signature: SignatureId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Vec<TypeId>, ConditionalTypeError> {
    if let Some((_, mapped)) = super::instantiate::instantiated_function_signature_projection(
        store,
        signature,
        array_targets,
    ) {
        let (callable, _) = mapped?;
        if callable.owner != owner {
            return Err(invalid_conditional_signature(store, signature));
        }
        let mut parameters = callable.parameters;
        parameters.extend(callable.rest_parameter);
        return Ok(parameters);
    }
    let record = store
        .signature(signature)
        .ok_or_else(|| invalid_conditional_signature(store, signature))?;
    if let Some(parameters) = store.callable_signature_parameter_types(signature) {
        return if parameters.len() == record.parameters().len() {
            Ok(parameters.to_vec())
        } else {
            Err(invalid_conditional_signature(store, signature))
        };
    }
    if record.parameters().is_empty() {
        return Ok(Vec::new());
    }
    if record
        .declaration()
        .and_then(|node| store.source_node_kind(node))
        != Some(SyntaxKind::MethodDeclaration)
    {
        return Err(invalid_conditional_signature(store, signature));
    }
    let method = store
        .type_payload(owner)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.symbol(symbol));
    if !method.is_some_and(|method| {
        method.flags() == SymbolFlags::METHOD
            && method
                .parent()
                .and_then(|class| store.source_class_provenance_for_symbol(class))
                .is_some()
    }) {
        return Err(invalid_conditional_signature(store, signature));
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        super::callable_sets::validate_stored_callable_set_with_array_targets(
            store,
            owner,
            array_targets,
        )
    else {
        return Err(invalid_conditional_signature(store, signature));
    };
    if projection.owner != owner {
        return Err(invalid_conditional_signature(store, signature));
    }
    let Some(callable) = projection
        .call_signatures
        .iter()
        .find(|callable| callable.owner == owner && callable.signature == signature)
    else {
        return Err(invalid_conditional_signature(store, signature));
    };
    let mut parameters = callable.parameters.clone();
    parameters.extend(callable.rest_parameter);
    if parameters.len() != record.parameters().len()
        || callable.rest_parameter.is_some() != record.has_rest_parameter()
    {
        return Err(invalid_conditional_signature(store, signature));
    }
    Ok(parameters)
}

fn conditional_signature_this_type(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    if let Some((_, mapped)) = super::instantiate::instantiated_function_signature_projection(
        store,
        signature,
        array_targets,
    ) {
        return mapped.map(|(_, this_type)| this_type).map_err(Into::into);
    }
    let record = store
        .signature(signature)
        .ok_or_else(|| invalid_conditional_signature(store, signature))?;
    match (
        record.this_parameter(),
        store.callable_signature_this_parameter_type(signature),
    ) {
        (None, None) => Ok(None),
        (Some(parameter), Some(type_))
            if store
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type)
                == Some(type_)
                && store.type_payload(type_).is_some() =>
        {
            Ok(Some(type_))
        }
        _ => Err(invalid_conditional_signature(store, signature)),
    }
}

fn inference_signature_parts(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    signature: SignatureId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<(Option<TypeId>, Vec<TypeId>, usize, TypeId), ConditionalTypeError> {
    let record = store
        .signature(signature)
        .ok_or_else(|| invalid_conditional_signature(store, signature))?;
    let minimum = usize::try_from(record.min_argument_count())
        .map_err(|_| invalid_conditional_signature(store, signature))?;
    let parameters = conditional_signature_parameter_types(store, owner, signature, array_targets)?;
    let this_type = conditional_signature_this_type(store, signature, array_targets)?;
    if minimum > parameters.len() {
        return Err(invalid_conditional_signature(store, signature));
    }
    let return_type = record
        .resolved_return_type()
        .ok_or_else(|| invalid_conditional_signature(store, signature))?;
    Ok((this_type, parameters, minimum, return_type))
}

fn base_inference_signature_parts(
    store: &mut CanonicalTypeMapperStore,
    owner: TypeId,
    signature: SignatureId,
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<(Option<TypeId>, Vec<TypeId>, usize, TypeId), ConditionalTypeError> {
    let (this_type, parameters, minimum, return_type) = inference_signature_parts(
        store,
        owner,
        signature,
        global_types.map(CanonicalArrayTargets::from_global_types),
    )?;
    let local_parameters = store
        .signature(signature)
        .ok_or_else(|| invalid_conditional_signature(store, signature))?
        .type_parameters()
        .to_vec();
    if local_parameters.is_empty() {
        return Ok((this_type, parameters, minimum, return_type));
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    let (unknown, any, no_constraint, circular_constraint) = (
        bootstrap.unknown_type,
        bootstrap.any_type,
        bootstrap.no_constraint_type,
        bootstrap.circular_constraint_type,
    );
    let mut constraints = Vec::with_capacity(local_parameters.len());
    for parameter in &local_parameters {
        let Some(TypeData::TypeParameter(data)) =
            store.type_payload(*parameter).map(TypeRecord::data)
        else {
            return Err(invalid_conditional_signature(store, signature));
        };
        let constraint = data.constraint.unwrap_or(unknown);
        constraints.push(
            if constraint == no_constraint || constraint == circular_constraint {
                unknown
            } else {
                constraint
            },
        );
    }

    for _ in 1..local_parameters.len() {
        let previous = constraints.clone();
        for constraint in &mut constraints {
            *constraint = map_inference_type(
                store,
                *constraint,
                &local_parameters,
                &previous,
                global_types,
                session,
                query,
            )?;
        }
    }
    let erased = vec![any; local_parameters.len()];
    for constraint in &mut constraints {
        *constraint = map_inference_type(
            store,
            *constraint,
            &local_parameters,
            &erased,
            global_types,
            session,
            query,
        )?;
    }

    let base_this = this_type
        .map(|receiver| {
            map_inference_type(
                store,
                receiver,
                &local_parameters,
                &constraints,
                global_types,
                session,
                query,
            )
        })
        .transpose()?;
    let mut base_parameters = Vec::with_capacity(parameters.len());
    for parameter in parameters {
        base_parameters.push(map_inference_type(
            store,
            parameter,
            &local_parameters,
            &constraints,
            global_types,
            session,
            query,
        )?);
    }
    let base_return = map_inference_type(
        store,
        return_type,
        &local_parameters,
        &constraints,
        global_types,
        session,
        query,
    )?;
    Ok((base_this, base_parameters, minimum, base_return))
}

fn template_inference_candidate(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    parameters: &[TypeId],
) -> Result<TypeId, ConditionalTypeError> {
    if !parameters.contains(&target) {
        return Ok(source);
    }
    let value = match store.type_payload(source).map(TypeRecord::data) {
        Some(TypeData::Literal(literal)) => match &literal.value {
            LiteralValue::String(value) => value.clone(),
            _ => return Ok(source),
        },
        Some(_) => return Ok(source),
        None => return Err(ConditionalTypeError::InvalidType(source)),
    };
    let constraint = match store.type_payload(target).map(TypeRecord::data) {
        Some(TypeData::TypeParameter(parameter)) => parameter.constraint,
        _ => return Ok(source),
    };
    let Some(constraint) = constraint else {
        return Ok(source);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if constraint == bootstrap.no_constraint_type
        || type_flags(store, constraint)?.intersects(TypeFlags::ANY)
    {
        return Ok(source);
    }
    let constituents = match store.type_payload(constraint).map(TypeRecord::data) {
        Some(TypeData::Union(union)) => union.union.types.clone(),
        Some(_) => vec![constraint],
        None => return Err(ConditionalTypeError::InvalidType(constraint)),
    };
    if constituents.iter().any(|constituent| {
        store
            .type_payload(*constituent)
            .is_some_and(|record| record.flags().intersects(TypeFlags::STRING))
    }) {
        return Ok(source);
    }

    for constituent in &constituents {
        if let Some(TypeData::Literal(literal)) =
            store.type_payload(*constituent).map(TypeRecord::data)
            && matches!(&literal.value, LiteralValue::String(text) if text == &value)
        {
            return Ok(*constituent);
        }
    }

    let number = ts_jsnum::from_string(&value);
    if !number.is_nan() && !number.is_infinite() && number.to_string() == value {
        for constituent in &constituents {
            let record = store
                .type_payload(*constituent)
                .ok_or(ConditionalTypeError::InvalidType(*constituent))?;
            if record.flags().intersects(TypeFlags::NUMBER) {
                return store
                    .regular_number_literal_type(number)
                    .map_err(Into::into);
            }
            if let TypeData::Literal(literal) = record.data()
                && matches!(&literal.value, LiteralValue::Number(existing) if *existing == number)
            {
                return Ok(*constituent);
            }
        }
    }

    if let Some(bigint) = canonical_bigint_inference_value(&value) {
        for constituent in &constituents {
            let record = store
                .type_payload(*constituent)
                .ok_or(ConditionalTypeError::InvalidType(*constituent))?;
            if record.flags().intersects(TypeFlags::BIG_INT) {
                return store
                    .regular_bigint_literal_type(bigint)
                    .map_err(Into::into);
            }
            if let TypeData::Literal(literal) = record.data()
                && matches!(&literal.value, LiteralValue::BigInt(existing) if *existing == bigint)
            {
                return Ok(*constituent);
            }
        }
    }

    if matches!(value.as_str(), "true" | "false") {
        let expected = value == "true";
        for constituent in &constituents {
            let record = store
                .type_payload(*constituent)
                .ok_or(ConditionalTypeError::InvalidType(*constituent))?;
            if let TypeData::Literal(literal) = record.data()
                && matches!(literal.value, LiteralValue::Boolean(actual) if actual == expected)
            {
                return Ok(*constituent);
            }
            if record.flags().intersects(TypeFlags::BOOLEAN) {
                let bootstrap = store
                    .intrinsic_bootstrap()
                    .ok_or(ConditionalTypeError::MissingBootstrap)?;
                return Ok(if expected {
                    bootstrap.true_type
                } else {
                    bootstrap.false_type
                });
            }
        }
    }

    Ok(source)
}

fn canonical_bigint_inference_value(value: &str) -> Option<ts_jsnum::PseudoBigInt> {
    let digits = value.strip_prefix('-').unwrap_or(value);
    if digits.is_empty() || !digits.bytes().all(|digit| digit.is_ascii_digit()) {
        return None;
    }
    let parsed = ts_jsnum::PseudoBigInt::parse_valid(value);
    (parsed.to_string() == value).then_some(parsed)
}

fn infer_template_literal_matches(
    store: &mut CanonicalTypeMapperStore,
    source_texts: &[String],
    source_types: &[TypeId],
    target_texts: &[String],
    target_types: &[TypeId],
) -> Result<Option<Vec<TypeId>>, ConditionalTypeError> {
    infer_template_literal_matches_worker(
        store,
        source_texts,
        source_types,
        target_texts,
        target_types,
        None,
        None,
    )
}

#[allow(clippy::too_many_arguments)] // Source inference retains the existing template inputs and caller.
fn infer_template_literal_matches_in_query(
    store: &mut CanonicalTypeMapperStore,
    source_texts: &[String],
    source_types: &[TypeId],
    target_texts: &[String],
    target_types: &[TypeId],
    arrays: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
    source_query: bool,
) -> Result<Option<Vec<TypeId>>, ConditionalTypeError> {
    if source_query {
        infer_template_literal_matches_worker(
            store,
            source_texts,
            source_types,
            target_texts,
            target_types,
            arrays,
            Some(session),
        )
    } else {
        infer_template_literal_matches(
            store,
            source_texts,
            source_types,
            target_texts,
            target_types,
        )
    }
}

fn infer_template_literal_matches_worker(
    store: &mut CanonicalTypeMapperStore,
    source_texts: &[String],
    source_types: &[TypeId],
    target_texts: &[String],
    target_types: &[TypeId],
    arrays: Option<CanonicalArrayTargets>,
    mut session: Option<&mut InstantiationSession>,
) -> Result<Option<Vec<TypeId>>, ConditionalTypeError> {
    if source_texts.len() != source_types.len().saturating_add(1)
        || target_texts.len() != target_types.len().saturating_add(1)
        || source_texts.is_empty()
        || target_types.is_empty()
    {
        return Ok(None);
    }
    if source_texts == target_texts && source_types.len() == target_types.len() {
        return Ok(Some(source_types.to_vec()));
    }

    let last_source = source_texts.len() - 1;
    let last_target = target_texts.len() - 1;
    let source_start = &source_texts[0];
    let source_end = &source_texts[last_source];
    let target_start = &target_texts[0];
    let target_end = &target_texts[last_target];
    if last_source == 0 && source_start.len() < target_start.len() + target_end.len()
        || !source_start.starts_with(target_start)
        || !source_end.ends_with(target_end)
    {
        return Ok(None);
    }
    let remaining_end = &source_end[..source_end.len() - target_end.len()];
    let mut segment = 0;
    let mut position = target_start.len();
    let mut matches = Vec::with_capacity(target_types.len());

    for delimiter in &target_texts[1..last_target] {
        let (match_segment, match_position) = if delimiter.is_empty() {
            let current = if segment == last_source {
                remaining_end
            } else {
                &source_texts[segment]
            };
            if let Some((character, _)) = split_first_template_code_point(&current[position..]) {
                (segment, position + character.len())
            } else if segment < last_source {
                (segment + 1, 0)
            } else {
                return Ok(None);
            }
        } else {
            let mut search_segment = segment;
            let mut search_position = position;
            loop {
                let current = if search_segment == last_source {
                    remaining_end
                } else {
                    &source_texts[search_segment]
                };
                if let Some(offset) = current[search_position..].find(delimiter) {
                    break (search_segment, search_position + offset);
                }
                search_segment += 1;
                if search_segment == source_texts.len() {
                    return Ok(None);
                }
                search_position = 0;
            }
        };
        matches.push(capture_template_literal_part(
            store,
            source_texts,
            source_types,
            remaining_end,
            segment,
            position,
            match_segment,
            match_position,
            arrays,
            session.as_deref_mut(),
        )?);
        segment = match_segment;
        position = match_position + delimiter.len();
    }
    matches.push(capture_template_literal_part(
        store,
        source_texts,
        source_types,
        remaining_end,
        segment,
        position,
        last_source,
        remaining_end.len(),
        arrays,
        session,
    )?);
    Ok(Some(matches))
}

#[allow(clippy::too_many_arguments)] // Both source endpoints are needed for upstream segment capture.
fn capture_template_literal_part(
    store: &mut CanonicalTypeMapperStore,
    source_texts: &[String],
    source_types: &[TypeId],
    remaining_end: &str,
    start_segment: usize,
    start_position: usize,
    end_segment: usize,
    end_position: usize,
    arrays: Option<CanonicalArrayTargets>,
    session: Option<&mut InstantiationSession>,
) -> Result<TypeId, ConditionalTypeError> {
    let source_text = |index: usize| {
        if index + 1 == source_texts.len() {
            remaining_end
        } else {
            source_texts[index].as_str()
        }
    };
    if start_segment == end_segment {
        return store
            .regular_string_literal_type(
                source_text(start_segment)[start_position..end_position].to_owned(),
            )
            .map_err(Into::into);
    }

    let mut texts = Vec::with_capacity(end_segment - start_segment + 1);
    texts.push(source_texts[start_segment][start_position..].to_owned());
    texts.extend(source_texts[start_segment + 1..end_segment].iter().cloned());
    texts.push(source_text(end_segment)[..end_position].to_owned());
    match session {
        Some(session) => store.get_template_literal_type_with_array_targets_and_session(
            &texts,
            &source_types[start_segment..end_segment],
            arrays,
            session,
        ),
        None => store.get_template_literal_type(&texts, &source_types[start_segment..end_segment]),
    }
    .map_err(Into::into)
}

#[allow(clippy::too_many_arguments)] // A constraint uses the same active mapper as its root.
fn inferred_candidate_satisfies_constraint(
    store: &mut CanonicalTypeMapperStore,
    parameter: TypeId,
    candidate: TypeId,
    mapped_parameters: &[TypeId],
    type_arguments: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    source: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    let constraint = match store.type_payload(parameter).map(TypeRecord::data) {
        Some(TypeData::TypeParameter(data)) => data.constraint,
        _ => return Err(ConditionalTypeError::InvalidTypeParameter(parameter)),
    };
    let Some(constraint) = constraint else {
        return Ok(true);
    };
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(ConditionalTypeError::MissingBootstrap)?;
    if constraint == bootstrap.no_constraint_type {
        return Ok(true);
    }
    let constraint = map_type_with_source(
        store,
        constraint,
        mapped_parameters,
        type_arguments,
        global_types,
        session,
        source,
    )?;
    is_assignable_in_query(store, candidate, constraint, global_types, session, source)
}

fn union_result(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<TypeId, ConditionalTypeError> {
    if let Some(global_types) = global_types {
        store
            .expression_union_type_with_global_types(
                global_types,
                types,
                super::bootstrap::UnionReduction::Literal,
            )
            .map_err(Into::into)
    } else {
        canonical_anonymous_union(store, types).map_err(Into::into)
    }
}

fn union_result_in_query(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    source: &Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    if !is_source_query(source) {
        return union_result(store, types, globals);
    }
    store
        .literal_union_type_with_alias_and_array_targets_and_session(
            types,
            None,
            globals.map(CanonicalArrayTargets::from_global_types),
            session,
        )
        .map_err(Into::into)
}

fn union_result_with_alias_in_query(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    globals: Option<&CanonicalGlobalTypes>,
    alias: Option<ConditionalAliasIdentity<'_>>,
    session: &mut InstantiationSession,
    source: &Option<&mut dyn ConditionalBranchSource>,
) -> Result<TypeId, ConditionalTypeError> {
    if !is_source_query(source) {
        return union_result_with_alias(store, types, globals, alias);
    }
    store
        .literal_union_type_with_alias_and_array_targets_and_session(
            types,
            alias.map(|alias| (alias.symbol, alias.type_arguments)),
            globals.map(CanonicalArrayTargets::from_global_types),
            session,
        )
        .map_err(Into::into)
}

fn union_result_with_alias(
    store: &mut CanonicalTypeMapperStore,
    types: &[TypeId],
    global_types: Option<&CanonicalGlobalTypes>,
    alias: Option<ConditionalAliasIdentity<'_>>,
) -> Result<TypeId, ConditionalTypeError> {
    let Some(alias) = alias else {
        return union_result(store, types, global_types);
    };
    store
        .literal_union_type_with_alias_and_array_targets(
            types,
            Some((alias.symbol, alias.type_arguments)),
            global_types.map(CanonicalArrayTargets::from_global_types),
        )
        .map_err(Into::into)
}

/// Compares conditional operands, including concrete fixed tuple wrappers.
pub(super) fn conditional_check_is_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    validate_owned_type(store, source)?;
    validate_owned_type(store, target)?;
    conditional_check_is_assignable_worker(
        store,
        source,
        target,
        global_types,
        &mut HashSet::new(),
        &mut None,
        &mut None,
    )
}

fn is_source_query(query: &Option<&mut dyn ConditionalBranchSource>) -> bool {
    query
        .as_deref()
        .and_then(|source| source.source_query_options())
        .is_some()
}

fn source_recovery_type(
    session: &InstantiationSession,
    mark: InstantiationLimitEventMark,
    source: &Option<&mut dyn ConditionalBranchSource>,
) -> Result<Option<TypeId>, ConditionalTypeError> {
    if is_source_query(source) && session.limit_event_occurred_since(mark) {
        session
            .recovery_error_type()
            .map(Some)
            .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))
    } else {
        Ok(None)
    }
}

fn source_semantic_recovery_mark(source: &Option<&mut dyn ConditionalBranchSource>) -> usize {
    source
        .as_deref()
        .map_or(0, |source| source.source_branch_recoveries().len())
}

pub(super) fn validate_source_branch_recoveries_since(
    store: &CanonicalTypeMapperStore,
    source: &dyn ConditionalBranchSource,
    mark: usize,
    session: &InstantiationSession,
) -> Result<bool, ConditionalTypeError> {
    if source.source_query_options().is_none() {
        return Ok(false);
    }
    let reached = source
        .source_branch_recoveries()
        .get(mark..)
        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
    for proof in reached {
        source
            .validate_root_branch_recovery(store, proof, session)
            .map_err(ConditionalTypeError::Declared)?;
    }
    Ok(!reached.is_empty())
}

fn source_semantic_recovery_since(
    store: &CanonicalTypeMapperStore,
    mark: usize,
    session: &InstantiationSession,
    source: &Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    source.as_deref().map_or(Ok(false), |source| {
        validate_source_branch_recoveries_since(store, source, mark, session)
    })
}

pub(super) fn source_query_is_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    globals: &CanonicalGlobalTypes,
    session: &mut InstantiationSession,
    query: &mut dyn ConditionalBranchSource,
) -> Result<bool, ConditionalTypeError> {
    let options = query
        .source_query_options()
        .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?;
    let result = store
        .is_type_related_to_with_global_this_source(
            source,
            target,
            super::RelationKind::Assignable,
            globals,
            options.strict_function_types,
            session,
            query,
        )
        .map_err(|error| match error {
            SourceRelationError::Relation(error) => ConditionalTypeError::Relation(error),
            SourceRelationError::Source(error) => ConditionalTypeError::Declared(error),
        })?;
    if query.source_query_options() != Some(options) {
        return Err(ConditionalTypeError::Declared(missing_source_query()));
    }
    let related = result.related();
    let (member_values, signature_returns) = result.into_proofs();
    for proof in &member_values {
        query
            .validate_global_this_member_value_proof(
                store,
                proof,
                globals,
                options.strict_function_types,
            )
            .map_err(ConditionalTypeError::Declared)?;
    }
    for proof in &signature_returns {
        query
            .validate_source_signature_return_proof(
                store,
                proof,
                globals,
                options.strict_function_types,
            )
            .map_err(ConditionalTypeError::Declared)?;
    }
    Ok(related)
}

fn is_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    conditional_check_is_assignable(store, source, target, global_types)
}

fn is_assignable_in_query(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    if query.is_none() {
        return is_assignable(store, source, target, globals);
    }
    validate_owned_type(store, source)?;
    validate_owned_type(store, target)?;
    conditional_check_is_assignable_worker(
        store,
        source,
        target,
        globals,
        &mut HashSet::new(),
        &mut Some(session),
        query,
    )
}

fn inference_assignability(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    globals: Option<&CanonicalGlobalTypes>,
    session: &mut InstantiationSession,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    if is_source_query(query) {
        is_assignable_in_query(store, source, target, globals, session, query)
    } else {
        is_assignable(store, source, target, globals)
    }
}

fn conditional_check_is_assignable_worker(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
    visiting: &mut HashSet<(TypeId, TypeId)>,
    session: &mut Option<&mut InstantiationSession>,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    // This walk is only a demand hint. It cannot admit an operand or a cache.
    for endpoint in [source, target] {
        if is_global_this_type_candidate(store, global_types, endpoint)
            || conditional_identity_requires_source(store, endpoint, &mut HashSet::new())
                .is_ok_and(|required| required)
        {
            if !is_source_query(query) {
                return Err(RelationUnavailable::UnresolvedStructuredMembers(endpoint).into());
            }
            return source_query_is_assignable(
                store,
                source,
                target,
                global_types.ok_or(ConditionalTypeError::MissingBootstrap)?,
                session
                    .as_deref_mut()
                    .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
                query
                    .as_deref_mut()
                    .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
            );
        }
    }
    if source == target {
        return Ok(true);
    }
    if !visiting.insert((source, target)) {
        return Ok(true);
    }
    let result = if let (Some(source_shape), Some(target_shape)) = (
        inference_tuple_shape(store, source)?,
        inference_tuple_shape(store, target)?,
    ) {
        concrete_tuple_types_are_assignable(
            store,
            &source_shape,
            &target_shape,
            global_types,
            visiting,
            session,
            query,
        )
    } else if matches!(
        store.type_payload(target).map(TypeRecord::data),
        Some(TypeData::TemplateLiteral(_))
    ) && store.type_payload(source).is_some_and(|record| {
        record
            .flags()
            .intersects(TypeFlags::STRING_LITERAL | TypeFlags::TEMPLATE_LITERAL | TypeFlags::UNION)
    }) {
        store
            .is_type_matched_by_template_literal_type(source, target)
            .map_err(Into::into)
    } else {
        match session.as_deref_mut() {
            Some(session) if is_source_query(query) => source_query_is_assignable(
                store,
                source,
                target,
                global_types.ok_or(ConditionalTypeError::MissingBootstrap)?,
                session,
                query
                    .as_deref_mut()
                    .ok_or_else(|| ConditionalTypeError::Declared(missing_source_query()))?,
            ),
            Some(session) => store
                .is_type_assignable_to_with_session(source, target, global_types, None, session)
                .map_err(Into::into),
            None => ordinary_assignability(store, source, target, global_types),
        }
    };
    visiting.remove(&(source, target));
    result
}

fn concrete_tuple_types_are_assignable(
    store: &mut CanonicalTypeMapperStore,
    source: &InferenceTupleShape,
    target: &InferenceTupleShape,
    global_types: Option<&CanonicalGlobalTypes>,
    visiting: &mut HashSet<(TypeId, TypeId)>,
    session: &mut Option<&mut InstantiationSession>,
    query: &mut Option<&mut dyn ConditionalBranchSource>,
) -> Result<bool, ConditionalTypeError> {
    if source.readonly && !target.readonly {
        return Ok(false);
    }
    let source_len = source.element_types.len();
    let target_len = target.element_types.len();
    if source_len < target.min_length {
        return Ok(false);
    }
    let target_rest = target
        .element_infos
        .iter()
        .position(|info| info.flags().intersects(ElementFlags::REST));
    if target_rest.is_none() && source_len > target_len {
        return Ok(false);
    }
    let target_suffix_len = target_rest.map_or(0, |rest| target_len - rest - 1);
    if source_len < target_suffix_len {
        return Ok(false);
    }
    let target_suffix_start = source_len - target_suffix_len;
    for (index, source_type) in source.element_types.iter().copied().enumerate() {
        let target_index = if let Some(rest) = target_rest {
            if index < rest {
                index
            } else if index >= target_suffix_start {
                target_len - (source_len - index)
            } else {
                rest
            }
        } else {
            index
        };
        if source.element_infos[index]
            .flags()
            .intersects(ElementFlags::OPTIONAL)
            && target.element_infos[target_index]
                .flags()
                .intersects(ElementFlags::REQUIRED)
        {
            return Ok(false);
        }
        if !conditional_check_is_assignable_worker(
            store,
            source_type,
            target.element_types[target_index],
            global_types,
            visiting,
            session,
            query,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn ordinary_assignability(
    store: &mut CanonicalTypeMapperStore,
    source: TypeId,
    target: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<bool, ConditionalTypeError> {
    match global_types {
        Some(global_types) => store
            .is_type_assignable_to_with_global_types(source, target, global_types)
            .map_err(Into::into),
        None => store
            .is_type_assignable_to(source, target)
            .map_err(Into::into),
    }
}

fn type_flags(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Result<TypeFlags, ConditionalTypeError> {
    store
        .type_payload(type_)
        .map(TypeRecord::flags)
        .ok_or(ConditionalTypeError::InvalidType(type_))
}

fn is_never(store: &CanonicalTypeMapperStore, type_: TypeId) -> Result<bool, ConditionalTypeError> {
    Ok(type_flags(store, type_)?.intersects(TypeFlags::NEVER))
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, SyntaxKind, encode_js_string};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SymbolData, SymbolFlags,
    };
    use ts_core::JsString;
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
        DeclaredTypeError, DeclaredTypeHost, DeclaredTypeLinks, IntrinsicBootstrapOptions,
        SemanticStore, TypeNodeUnavailable, ValueSymbolLinks,
        declared::execute_type_parameter,
        instantiated_members::validate_generic_interface_callable,
        mapper::TypeMapper,
        object_members::{
            plan_generic_interface, publish_generic_interface_declared_members_with_global_types,
        },
        production::GlobalMergeCompletion,
        reference_types::validate_direct_generic_reference,
        signatures::IndexFlags,
        type_nodes::CanonicalTypeQuery,
        type_records::{RegularLiteralLink, StructuredTypeData},
        types::{AccessFlags, ObjectFlags},
    };

    mod source_query_controls {
        use super::*;

        const FILE: FileId = FileId::new(20_422);

        fn context(parsed: &ParseResult, strict_functions: bool) -> CanonicalCheckerContext<'_> {
            assert!(parsed.diagnostics.is_empty());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FILE,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/source-conditional-control.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FILE)
                .unwrap();
            CanonicalCheckerContext::new(
                binder.finish(),
                vec![(FILE, &parsed.arena)],
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        ..IntrinsicBootstrapOptions::default()
                    },
                    strict_function_types: strict_functions,
                    ..CanonicalCheckerOptions::default()
                },
            )
            .unwrap()
        }

        fn annotation(context: &CanonicalCheckerContext<'_>, name: &str) -> NodeRef {
            source_conditional_annotation(context, source_conditional_symbol(context, name))
        }

        fn declared(context: &mut CanonicalCheckerContext<'_>, name: &str) -> TypeId {
            let symbol = source_conditional_symbol(context, name);
            context.get_declared_type_of_symbol(symbol).unwrap()
        }

        fn source_options(context: &CanonicalCheckerContext<'_>) -> CanonicalTypeQueryOptions {
            let options = context.options();
            CanonicalTypeQueryOptions {
                strict_builtin_iterator_return: options.strict_builtin_iterator_return,
                strict_function_types: Some(options.strict_function_types),
                no_implicit_any: options.no_implicit_any,
            }
        }

        struct HeaderSource<'host, 'arena> {
            options: CanonicalTypeQueryOptions,
            members: Option<GlobalThisMembers<'host, 'arena>>,
        }

        impl ConditionalBranchSource for HeaderSource<'_, '_> {
            fn preflight(
                &self,
                _: &CanonicalTypeMapperStore,
                _: TypeId,
            ) -> Result<(), DeclaredTypeError> {
                Err(missing_source_query())
            }

            fn resolve_branch(
                &mut self,
                _: &mut CanonicalTypeMapperStore,
                _: TypeId,
                _: ConditionalBranchKind,
                _: &mut InstantiationSession,
            ) -> Result<TypeId, DeclaredTypeError> {
                Err(missing_source_query())
            }

            fn source_query_options(&self) -> Option<CanonicalTypeQueryOptions> {
                Some(self.options)
            }

            fn global_this_members(&self) -> Option<&GlobalThisMembers<'_, '_>> {
                self.members.as_ref()
            }
        }

        fn charge_source_parameter(
            context: &mut CanonicalCheckerContext<'_>,
            caller: &mut InstantiationSession,
        ) -> TypeId {
            let node = annotation(context, "Caller");
            let parameter = context.get_type_from_type_node(node).unwrap();
            assert!(cached_ordinary_type_parameter_owner(context.store(), parameter).is_some());
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let arrays = Some(CanonicalArrayTargets::from_global_types(
                context.global_types(),
            ));
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    context.store_mut_for_test(),
                    parameter,
                    &[parameter],
                    &[number],
                    arrays,
                    caller
                ),
                Ok(number)
            );
            assert_eq!((caller.query_count(), caller.total_count()), (1, 1));
            parameter
        }

        fn query(
            context: &mut CanonicalCheckerContext<'_>,
            parsed: &ParseResult,
            node: NodeRef,
            caller: &mut InstantiationSession,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let options = context.options();
            let query_options = source_options(context);
            let bound = context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let globals = context.global_types().clone();
            CanonicalTypeQuery::new_with_global_types_and_session(
                context.store_mut_for_test(),
                &host,
                &globals,
                query_options,
                caller,
                diagnostics,
            )?
            .get_type_from_type_node(node)
        }

        fn state(
            context: &CanonicalCheckerContext<'_>,
            parsed: &ParseResult,
            root: NodeRef,
        ) -> impl std::fmt::Debug + PartialEq + use<> {
            let store = context.store();
            let globals = store.symbol_table(context.globals()).unwrap();
            let members = store
                .type_payload(context.global_types().global_this_value_type)
                .and_then(|record| record.data().structured())
                .and_then(|data| data.members);
            (
                conditional_allocation_counts(store),
                conditional_callable_counts(store),
                store
                    .conditional_query_production(ConditionalQueryKey::Node(root))
                    .cloned(),
                members.and_then(|table| store.symbol_table(table)).cloned(),
                parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let node = NodeRef::new(parsed.arena.id(), FILE, id);
                        (
                            store.type_node_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                globals
                    .iter()
                    .map(|(_, symbol)| {
                        (
                            symbol,
                            store.value_symbol_links(symbol).cloned(),
                            store.type_alias_links(symbol).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        }

        const GLOBAL_INFERENCE: &str = concat!(
            "declare var ready: number;\n",
            "declare var payload: { code: string };\n",
            "type Selected = typeof globalThis extends { ready: number; payload: infer T } ? T : import(\"./cold\").Missing;\n",
            "type Caller<T> = T;\n",
        );

        #[test]
        fn source_conditional_recovery_keeps_the_spent_caller_and_root_result_cold() {
            let parsed = parse_source_file(GLOBAL_INFERENCE);
            let mut context = context(&parsed, true);
            let root = annotation(&context, "Selected");
            let parameter_node = annotation(&context, "Caller");
            let parameter = context.get_type_from_type_node(parameter_node).unwrap();
            assert!(cached_ordinary_type_parameter_owner(context.store(), parameter).is_some());
            let globals = context.global_types().clone();
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let (number, error) = (bootstrap.number_type, bootstrap.error_type);
            let mut caller = InstantiationSession::new_recovering(
                context.store(),
                InstantiationLimits {
                    max_count: 1,
                    ..InstantiationLimits::default()
                },
                error,
            )
            .unwrap();
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    context.store_mut_for_test(),
                    parameter,
                    &[parameter],
                    &[number],
                    Some(CanonicalArrayTargets::from_global_types(&globals)),
                    &mut caller
                ),
                Ok(number)
            );
            assert_eq!((caller.query_count(), caller.total_count()), (1, 1));
            let NodeData::ConditionalTypeNode(syntax) = &parsed.arena.get(root.node).unwrap().data
            else {
                panic!("real conditional required")
            };
            let cold_import = NodeRef::new(root.arena, root.file, syntax.false_type);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            for _ in 0..2 {
                let mark = caller.limit_event_mark();
                assert_eq!(
                    query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                    Ok(error)
                );
                assert!(caller.limit_event_occurred_since(mark));
                assert_eq!((caller.query_count(), caller.total_count()), (1, 1));
                assert!(
                    context
                        .store()
                        .conditional_query_production(ConditionalQueryKey::Node(root))
                        .is_none()
                );
                assert!(
                    context
                        .store()
                        .type_node_links(root)
                        .is_none_or(|links| links.resolved_type.is_none())
                );
                assert!(context.store().type_node_links(cold_import).is_none());
                assert!(
                    context
                        .store()
                        .source_file_links(context.source_file(FILE).unwrap())
                        .is_none_or(|links| !links.type_checked)
                );
            }
        }

        #[test]
        fn source_conditional_warm_queries_recheck_the_actual_global_member_table() {
            let parsed = parse_source_file(GLOBAL_INFERENCE);
            let mut context = context(&parsed, true);
            let root = annotation(&context, "Selected");
            let mut caller = InstantiationSession::new(InstantiationLimits::default());
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = query(&mut context, &parsed, root, &mut caller, &mut diagnostics).unwrap();
            let payload = source_conditional_symbol(&context, "payload");
            let ready = source_conditional_symbol(&context, "ready");
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(payload)
                    .unwrap()
                    .resolved_type,
                Some(result)
            );
            let globals = context.global_types().clone();
            let global = globals.global_this_value_type;
            let table = context
                .store()
                .type_payload(global)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .members
                .unwrap();
            let warm = state(&context, &parsed, root);
            for _ in 0..2 {
                assert_eq!(
                    query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                    Ok(result)
                );
                assert_eq!(state(&context, &parsed, root), warm);
            }
            assert_eq!(
                conditional_check_is_assignable(
                    context.store_mut_for_test(),
                    global,
                    global,
                    Some(&globals)
                ),
                Err(ConditionalTypeError::Relation(
                    RelationUnavailable::UnresolvedStructuredMembers(global)
                ))
            );
            assert_eq!(
                context.store_mut_for_test().insert_symbol(
                    table,
                    EscapedName::source("payload"),
                    ready
                ),
                Some(Some(payload))
            );
            let poisoned = state(&context, &parsed, root);
            let counts = (
                caller.query_count(),
                caller.total_count(),
                caller.limit_event_mark(),
            );
            for _ in 0..2 {
                assert_eq!(query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                    Err(super::super::super::declared::DeclaredTypeUnavailable::InvalidGlobalThisMembers(global).into()));
                assert_eq!(state(&context, &parsed, root), poisoned);
                assert_eq!(
                    (
                        caller.query_count(),
                        caller.total_count(),
                        caller.limit_event_mark()
                    ),
                    counts
                );
            }
            assert_eq!(
                context.store_mut_for_test().insert_symbol(
                    table,
                    EscapedName::source("payload"),
                    payload
                ),
                Some(Some(ready))
            );
            assert_eq!(
                query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                Ok(result)
            );
            assert_eq!(state(&context, &parsed, root), warm);
            assert!(diagnostics.is_empty());
            scalar_selected_branch_keeps_its_source_dependency();
        }

        fn scalar_selected_branch_keeps_its_source_dependency() {
            let parsed = parse_source_file(concat!(
                "declare var ready: number;\n",
                "type Inner = typeof globalThis extends { ready: number } ? number : string;\n",
                "type Outer = number extends number ? Inner : string;\n",
            ));
            let mut context = context(&parsed, true);
            let root = annotation(&context, "Outer");
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let mut caller = InstantiationSession::new(InstantiationLimits::default());
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert_eq!(
                query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                Ok(number)
            );
            let arrays = Some(CanonicalArrayTargets::from_global_types(
                context.global_types(),
            ));
            let metadata = conditional_source_query_request(
                context.store(),
                ConditionalQueryKey::Node(root),
                arrays,
            )
            .unwrap()
            .unwrap();
            assert_eq!(
                (
                    metadata.check_type(),
                    metadata.extends_type(),
                    metadata.retained_result()
                ),
                (number, number, number)
            );
            assert!(metadata.requires_source_result_proof());
            let warm = state(&context, &parsed, root);
            for _ in 0..2 {
                assert_eq!(
                    conditional_query_alias_with_array_targets(context.store(), root, arrays),
                    Err(ConditionalTypeError::Declared(missing_source_query()))
                );
                assert_eq!(state(&context, &parsed, root), warm);
                assert_eq!(
                    query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                    Ok(number)
                );
                assert_eq!(state(&context, &parsed, root), warm);
            }
            assert!(diagnostics.is_empty());
        }

        #[test]
        fn source_conditional_deferred_replay_keeps_the_real_root_and_unqueried_branches() {
            let parsed = parse_source_file(
                "type Deferred<T> = T extends { global: typeof globalThis } ? number : boolean;",
            );
            let mut context = context(&parsed, true);
            let root = annotation(&context, "Deferred");
            let NodeData::ConditionalTypeNode(syntax) = &parsed.arena.get(root.node).unwrap().data
            else {
                panic!("real conditional required")
            };
            let branches = [syntax.true_type, syntax.false_type]
                .map(|node| NodeRef::new(root.arena, root.file, node));
            let mut caller = InstantiationSession::new(InstantiationLimits::default());
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = query(&mut context, &parsed, root, &mut caller, &mut diagnostics).unwrap();
            let Some(TypeData::Conditional(data)) =
                context.store().type_payload(result).map(TypeRecord::data)
            else {
                panic!("the source parameter must keep the conditional deferred")
            };
            let root_id = data.root;
            assert_eq!(
                context.store().conditional_root(root_id).unwrap().node(),
                root
            );
            assert_eq!(
                (
                    data.resolved_true_type,
                    data.resolved_false_type,
                    data.resolved_inferred_true_type
                ),
                (None, None, None)
            );
            let warm = state(&context, &parsed, root);
            let caller_state = (
                caller.query_count(),
                caller.total_count(),
                caller.limit_event_mark(),
            );
            for _ in 0..2 {
                assert_eq!(
                    query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                    Ok(result)
                );
                for branch in branches {
                    assert!(context.store().type_node_links(branch).is_none());
                }
                assert_eq!(state(&context, &parsed, root), warm);
                assert_eq!(
                    (
                        caller.query_count(),
                        caller.total_count(),
                        caller.limit_event_mark()
                    ),
                    caller_state
                );
            }
            let original = context.store().type_node_links(root).cloned().unwrap();
            let mut poison = original.clone();
            poison.resolved_type = Some(context.store().intrinsic_bootstrap().unwrap().string_type);
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(root, poison)
            );
            let poisoned = state(&context, &parsed, root);
            assert_eq!(
                conditional_source_query_request(
                    context.store(),
                    ConditionalQueryKey::Node(root),
                    Some(CanonicalArrayTargets::from_global_types(
                        context.global_types()
                    ))
                ),
                Err(ConditionalTypeError::InvalidTypeNodeCache(root))
            );
            assert_eq!(state(&context, &parsed, root), poisoned);
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(root, original)
            );
            assert_eq!(
                query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                Ok(result)
            );
            assert_eq!(state(&context, &parsed, root), warm);
        }

        #[test]
        fn source_conditional_inference_fallback_keeps_strict_options_and_the_caller() {
            let parsed = parse_source_file(concat!(
                "type Selected = { accept: (value: string) => void; result: number } extends ",
                "{ accept: ((value: string | number) => void) | number; result: infer T } ? T : \"absent\";\n",
                "type Caller<T> = T;\n",
            ));
            for strict in [false, true] {
                let mut context = context(&parsed, strict);
                let root = annotation(&context, "Selected");
                let mut caller = InstantiationSession::new(InstantiationLimits::default());
                charge_source_parameter(&mut context, &mut caller);
                let caller_address = std::ptr::from_ref(&caller);
                let mark = caller.limit_event_mark();
                let mut diagnostics = CanonicalCheckerDiagnostics::default();
                let result =
                    query(&mut context, &parsed, root, &mut caller, &mut diagnostics).unwrap();
                if strict {
                    assert!(
                        matches!(context.store().type_payload(result).unwrap().data(),
                        TypeData::Literal(literal) if literal.value == LiteralValue::String("absent".to_owned()))
                    );
                } else {
                    assert_eq!(
                        result,
                        context.store().intrinsic_bootstrap().unwrap().number_type
                    );
                }
                let proof = context
                    .store()
                    .conditional_query_production(ConditionalQueryKey::Node(root))
                    .unwrap();
                let target = proof.definition.extends_type;
                assert_eq!(proof.definition.infer_type_parameters.len(), 1);
                assert!(is_structural_inference_target(context.store(), target).unwrap());
                assert_eq!(
                    context.store().claimed_strict_function_types(),
                    Some(strict)
                );
                let warm = state(&context, &parsed, root);
                let count = caller.query_count();
                assert!(count >= 1);
                assert_eq!(
                    query(&mut context, &parsed, root, &mut caller, &mut diagnostics),
                    Ok(result)
                );
                assert_eq!(std::ptr::from_ref(&caller), caller_address);
                assert!(caller.query_count() >= count);
                assert_eq!(caller.query_count(), caller.total_count());
                assert_eq!(caller.limit_event_mark(), mark);
                assert_eq!(state(&context, &parsed, root), warm);
                assert!(diagnostics.is_empty());
            }
            inference_fallback_spends_the_actual_member_caller();
        }

        #[allow(clippy::too_many_lines)] // Keep the cold proxy, spent caller and exact retry in one control.
        fn inference_fallback_spends_the_actual_member_caller() {
            let parsed = parse_source_file(concat!(
                "interface Box<T> { value: T; }\n",
                "type Accepted = Box<number>;\n",
                "type Pattern = { value: number } | number;\n",
                "type Caller<T> = T;\n",
            ));
            for limited in [true, false] {
                let mut context = context(&parsed, true);
                let accepted = declared(&mut context, "Accepted");
                let pattern = declared(&mut context, "Pattern");
                let node = annotation(&context, "Accepted");
                let globals = context.global_types().clone();
                let arrays = Some(CanonicalArrayTargets::from_global_types(&globals));
                let mut source = HeaderSource {
                    options: source_options(&context),
                    members: None,
                };
                let mut caller = InstantiationSession::new(InstantiationLimits {
                    max_count: if limited {
                        1
                    } else {
                        InstantiationLimits::default().max_count
                    },
                    ..InstantiationLimits::default()
                });
                charge_source_parameter(&mut context, &mut caller);
                assert_eq!(
                    super::super::super::instantiated_members::validate_generic_interface_members(
                        context.store(),
                        accepted,
                        arrays
                    ),
                    Ok(None)
                );
                assert!(matches!(
                    context.store().type_payload(pattern).unwrap().data(),
                    TypeData::Union(_)
                ));
                assert!(
                    !contains_type_parameter(context.store(), pattern, &HashSet::new()).unwrap()
                );
                let inference = ConditionalInferenceContext {
                    infer_parameters: &[],
                    mapped_parameters: &[],
                    type_arguments: &[],
                    global_types: Some(&globals),
                };
                let address = std::ptr::from_ref(&caller);
                let mark = caller.limit_event_mark();
                let result = infer_from_types(
                    context.store_mut_for_test(),
                    accepted,
                    pattern,
                    inference,
                    &mut [],
                    &mut caller,
                    &mut Some(&mut source),
                );
                let members = context
                    .store()
                    .type_payload(accepted)
                    .unwrap()
                    .data()
                    .structured()
                    .unwrap()
                    .members
                    .unwrap();
                let property = context
                    .store()
                    .symbol_table(members)
                    .unwrap()
                    .get_source("value")
                    .unwrap();
                let links = context
                    .store()
                    .value_symbol_links(property)
                    .cloned()
                    .unwrap();
                let original = links.target.unwrap();
                let template = context
                    .store()
                    .value_symbol_links(original)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                assert!(cached_ordinary_type_parameter_owner(context.store(), template).is_some());
                let warm = state(&context, &parsed, node);
                if limited {
                    assert_eq!(
                        result,
                        Err(ConditionalTypeError::Relation(
                            RelationUnavailable::UnsupportedProperty(property)
                        ))
                    );
                    assert_eq!(links.resolved_type, None);
                    assert!(caller.limit_event_occurred_since(mark));
                    assert_eq!((caller.query_count(), caller.total_count()), (1, 1));
                    assert_eq!(
                        infer_from_types(
                            context.store_mut_for_test(),
                            accepted,
                            pattern,
                            inference,
                            &mut [],
                            &mut caller,
                            &mut Some(&mut source)
                        ),
                        Err(ConditionalTypeError::Relation(
                            RelationUnavailable::UnsupportedProperty(property)
                        ))
                    );
                    assert_eq!(context.store().value_symbol_links(property), Some(&links));
                    assert_eq!(state(&context, &parsed, node), warm);
                    assert_eq!((caller.query_count(), caller.total_count()), (1, 1));
                } else {
                    assert_eq!(result, Ok(true));
                    assert!(caller.query_count() > 1);
                    assert_eq!(caller.query_count(), caller.total_count());
                    assert_eq!(caller.limit_event_mark(), mark);
                    assert_eq!(
                        links.resolved_type,
                        Some(context.store().intrinsic_bootstrap().unwrap().number_type)
                    );
                }
                assert_eq!(std::ptr::from_ref(&caller), address);
                assert!(source.members.is_none());
            }
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Keep the exact global leaf and rejected nested mapping together.
        fn source_conditional_mapping_keeps_the_nested_global_object_boundary() {
            let parsed = parse_source_file(concat!(
                "declare var untouched: number;\n",
                "type Wrapped = { global: typeof globalThis };\n",
                "type Caller<T> = T;\n",
            ));
            let mut context = context(&parsed, true);
            let node = annotation(&context, "Wrapped");
            let wrapped = declared(&mut context, "Wrapped");
            assert_eq!(
                context.store().type_node_links(node).unwrap().resolved_type,
                Some(wrapped)
            );
            let parameter_node = annotation(&context, "Caller");
            let parameter = context.get_type_from_type_node(parameter_node).unwrap();
            assert!(cached_ordinary_type_parameter_owner(context.store(), parameter).is_some());
            let globals = context.global_types().clone();
            let global = globals.global_this_value_type;
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let bound = context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let options = source_options(&context);
            let members = super::super::super::global_types::prepare_global_this_members(
                context.store_mut_for_test(),
                &host,
                &globals,
                global,
            )
            .unwrap()
            .unwrap();
            let mut source = HeaderSource {
                options,
                members: Some(members),
            };
            let mut caller = InstantiationSession::new(InstantiationLimits {
                max_count: 0,
                ..InstantiationLimits::default()
            });
            let before = state(&context, &parsed, node);
            for _ in 0..2 {
                assert_eq!(
                    validate_source_result_type(context.store(), global, &globals, &source),
                    Ok(())
                );
                assert_eq!(
                    map_type_with_source(
                        context.store_mut_for_test(),
                        wrapped,
                        &[],
                        &[],
                        Some(&globals),
                        &mut caller,
                        &mut Some(&mut source)
                    ),
                    Ok(wrapped)
                );
                assert_eq!(
                    map_type_with_source(
                        context.store_mut_for_test(),
                        global,
                        &[parameter],
                        &[number],
                        Some(&globals),
                        &mut caller,
                        &mut Some(&mut source)
                    ),
                    Ok(global)
                );
                assert_eq!(
                    map_type_with_source(
                        context.store_mut_for_test(),
                        wrapped,
                        &[parameter],
                        &[number],
                        Some(&globals),
                        &mut caller,
                        &mut Some(&mut source)
                    ),
                    Err(ConditionalTypeError::Instantiation(
                        InstantiationError::UnsupportedType(wrapped)
                    ))
                );
                assert_eq!(state(&context, &parsed, node), before);
                assert_eq!(
                    (
                        caller.query_count(),
                        caller.total_count(),
                        caller.limit_event_count()
                    ),
                    (0, 0, 0)
                );
            }
            let untouched = source_conditional_symbol(&context, "untouched");
            assert!(
                context
                    .store()
                    .value_symbol_links(untouched)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            mapped_result_controls::recheck_completed_object_and_array_results();
        }

        mod mapped_result_controls {
            use super::*;
            use crate::semantic::{
                array_types::ArrayTypeError,
                instantiated_members::{
                    demand_property_object_alias_property,
                    resolve_property_object_alias_members_with_array_targets,
                    validate_property_object_alias_members_with_array_targets,
                },
                object_aliases::source_property_object_projection,
            };

            struct Source<'host, 'arena> {
                host: &'host DeclaredTypeHost<'arena>,
                globals: CanonicalGlobalTypes,
                options: CanonicalTypeQueryOptions,
            }

            impl Source<'_, '_> {
                fn branch_node(
                    &self,
                    store: &CanonicalTypeMapperStore,
                    root: ConditionalSourceRoot,
                    branch: ConditionalBranchKind,
                ) -> Result<NodeRef, DeclaredTypeError> {
                    self.preflight_root(store, root)?;
                    let Some(NodeData::ConditionalTypeNode(syntax)) =
                        self.host.node(root.node).map(|node| &node.data)
                    else {
                        return Err(missing_source_query());
                    };
                    let node = NodeRef::new(
                        root.node.arena,
                        root.node.file,
                        match branch {
                            ConditionalBranchKind::True => syntax.true_type,
                            ConditionalBranchKind::False => syntax.false_type,
                        },
                    );
                    if store.source_node_parent(node) != Some(SourceNodeParent::Parent(root.node)) {
                        return Err(missing_source_query());
                    }
                    Ok(node)
                }
            }

            impl ConditionalBranchSource for Source<'_, '_> {
                fn preflight(
                    &self,
                    store: &CanonicalTypeMapperStore,
                    conditional: TypeId,
                ) -> Result<(), DeclaredTypeError> {
                    let Some(TypeData::Conditional(data)) =
                        store.type_payload(conditional).map(TypeRecord::data)
                    else {
                        return Err(missing_source_query());
                    };
                    let root = store
                        .conditional_root(data.root)
                        .ok_or_else(missing_source_query)?;
                    self.preflight_root(
                        store,
                        ConditionalSourceRoot {
                            root: data.root,
                            node: root.node(),
                        },
                    )
                }

                fn resolve_branch(
                    &mut self,
                    _: &mut CanonicalTypeMapperStore,
                    _: TypeId,
                    _: ConditionalBranchKind,
                    _: &mut InstantiationSession,
                ) -> Result<TypeId, DeclaredTypeError> {
                    Err(missing_source_query())
                }

                fn preflight_root(
                    &self,
                    store: &CanonicalTypeMapperStore,
                    root: ConditionalSourceRoot,
                ) -> Result<(), DeclaredTypeError> {
                    let request = conditional_source_query_request(
                        store,
                        ConditionalQueryKey::Node(root.node),
                        Some(CanonicalArrayTargets::from_global_types(&self.globals)),
                    )
                    .map_err(|_| missing_source_query())?;
                    if request.is_none_or(|request| request.source_root() != root) {
                        return Err(missing_source_query());
                    }
                    Ok(())
                }

                fn resolve_root_branch(
                    &mut self,
                    store: &mut CanonicalTypeMapperStore,
                    root: ConditionalSourceRoot,
                    branch: ConditionalBranchKind,
                    caller: &mut InstantiationSession,
                ) -> Result<TypeId, DeclaredTypeError> {
                    let node = self.branch_node(store, root, branch)?;
                    let mut diagnostics = CanonicalCheckerDiagnostics::default();
                    let result = CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        self.host,
                        &self.globals,
                        self.options,
                        caller,
                        &mut diagnostics,
                    )?
                    .get_type_from_type_node(node)?;
                    assert!(diagnostics.is_empty());
                    Ok(result)
                }

                fn validate_resolved_root_branch(
                    &self,
                    store: &CanonicalTypeMapperStore,
                    root: ConditionalSourceRoot,
                    branch: ConditionalBranchKind,
                    result: TypeId,
                ) -> Result<(), DeclaredTypeError> {
                    let node = self.branch_node(store, root, branch)?;
                    if store
                        .type_node_links(node)
                        .and_then(|links| links.resolved_type)
                        != Some(result)
                    {
                        return Err(missing_source_query());
                    }
                    validate_source_result_type(store, result, &self.globals, self)
                        .map_err(|_| missing_source_query())
                }

                fn source_query_options(&self) -> Option<CanonicalTypeQueryOptions> {
                    Some(self.options)
                }
            }

            fn payload_state(
                store: &CanonicalTypeMapperStore,
                proof: &ConditionalSourceResultProof,
            ) -> impl std::fmt::Debug + PartialEq + use<> {
                let record = store.type_payload(proof.result()).unwrap();
                let structured = record.data().structured().unwrap();
                (
                    (
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                    ),
                    match record.data() {
                        TypeData::Object(data) => Some(data.clone()),
                        _ => None,
                    },
                    match record.data() {
                        TypeData::TypeReference(data) => Some(data.clone()),
                        _ => None,
                    },
                    structured
                        .members
                        .and_then(|table| store.symbol_table(table))
                        .cloned(),
                    structured
                        .properties
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .map(|&property| (property, store.value_symbol_links(property).cloned()))
                        .collect::<Vec<_>>(),
                    store
                        .conditional_root(proof.source_root().root)
                        .unwrap()
                        .instantiations()
                        .clone(),
                    store.conditional_query_production(proof.key()).cloned(),
                )
            }

            #[allow(clippy::too_many_lines)] // Keep the real mapped result, damage rows and restored proof together.
            pub(super) fn recheck_completed_object_and_array_results() {
                let parsed = parse_source_file(concat!(
                    "interface Array<T> {} interface ReadonlyArray<T> {}\n",
                    "type Box<T> = { value: T };\n",
                    "type Pick<T> = T extends string ? Box<T> : never;\n",
                    "type ArrayPick<T> = T extends string ? T[] : never;\n",
                    "type Caller<T> = T;\n",
                ));
                let mut context = context(&parsed, true);
                let mut caller = InstantiationSession::new(InstantiationLimits::default());
                charge_source_parameter(&mut context, &mut caller);
                let globals = context.global_types().clone();
                let options = context.options();
                let targets = CanonicalArrayTargets::from_global_types(&globals);
                let arrays = Some(targets);
                let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                let bound = context.file(FILE).unwrap().1.clone();
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&parsed.arena, &bound)],
                    GlobalMergeCompletion::for_test(options.name_resolution),
                )
                .unwrap();
                let mut source = Source {
                    host: &host,
                    globals: globals.clone(),
                    options: source_options(&context),
                };
                let mut diagnostics = CanonicalCheckerDiagnostics::default();
                for name in ["Pick", "ArrayPick"] {
                    let node = annotation(&context, name);
                    let conditional = declared(&mut context, name);
                    let TypeData::Conditional(data) =
                        context.store().type_payload(conditional).unwrap().data()
                    else {
                        panic!("the written parameter must leave a real deferred conditional")
                    };
                    let root = ConditionalSourceRoot {
                        root: data.root,
                        node,
                    };
                    let selected = source
                        .branch_node(context.store(), root, ConditionalBranchKind::True)
                        .unwrap();
                    let excluded = source
                        .branch_node(context.store(), root, ConditionalBranchKind::False)
                        .unwrap();
                    assert!(
                        context
                            .store()
                            .type_node_links(selected)
                            .is_none_or(|links| links.resolved_type.is_none())
                    );
                    let arguments = [string];
                    let request = SourceConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        alias: None,
                        for_constraint: false,
                        input_recovery: None,
                    };
                    let ConditionalSourceResult::Complete(proof) =
                        get_conditional_type_instantiation_with_source(
                            context.store_mut_for_test(),
                            request,
                            &globals,
                            &mut caller,
                            &mut source,
                        )
                        .unwrap()
                    else {
                        panic!("the real source mapping must complete")
                    };
                    let result = proof.result();
                    let raw = context
                        .store()
                        .type_node_links(selected)
                        .unwrap()
                        .resolved_type
                        .unwrap();
                    assert_ne!(result, raw);
                    assert_eq!(proof.branch_reads.len(), 1);
                    assert_eq!(proof.branch_reads[0].result, raw);
                    assert_eq!(proof.branch_reads[0].root, root);
                    assert_eq!(proof.branch_reads[0].branch, ConditionalBranchKind::True);
                    assert!(proof.member_values.is_empty() && proof.nested.is_empty());
                    let cold = (
                        state(&context, &parsed, node),
                        payload_state(context.store(), &proof),
                    );
                    for _ in 0..2 {
                        assert_eq!(
                            validate_source_conditional_result(
                                context.store(),
                                &proof,
                                &globals,
                                &source
                            ),
                            Ok(())
                        );
                        assert_eq!(
                            (
                                state(&context, &parsed, node),
                                payload_state(context.store(), &proof)
                            ),
                            cold
                        );
                    }
                    let mut object_member = None;
                    if name == "Pick" {
                        let projection = source_property_object_projection(context.store(), result)
                            .unwrap()
                            .unwrap();
                        let raw_projection =
                            source_property_object_projection(context.store(), raw)
                                .unwrap()
                                .unwrap();
                        assert_eq!(raw_projection.target(), projection.target());
                        assert_eq!(
                            raw_projection.arguments(),
                            &[context
                                .store()
                                .conditional_root(root.root)
                                .unwrap()
                                .check_type()]
                        );
                        assert_eq!(projection.arguments(), &[string]);
                        assert_ne!(projection.type_(), projection.target());
                        assert_eq!(projection.properties().len(), 1);
                        assert_eq!(
                            context
                                .store()
                                .source_declaration_symbol(annotation(&context, "Box")),
                            Some(projection.source_symbol())
                        );
                        assert_eq!(
                            validate_property_object_alias_members_with_array_targets(
                                context.store(),
                                result,
                                arrays
                            ),
                            Ok(None)
                        );
                        let original = projection.properties()[0].symbol;
                        assert_eq!(
                            context
                                .store()
                                .source_declaration_symbol(projection.properties()[0].declaration),
                            Some(original)
                        );
                        let members = resolve_property_object_alias_members_with_array_targets(
                            context.store_mut_for_test(),
                            result,
                            arrays,
                        )
                        .unwrap();
                        let [property] = members.properties.as_slice() else {
                            panic!("Box has one actual source property")
                        };
                        let property = *property;
                        assert_ne!(property, original);
                        assert_eq!(
                            context.store().value_symbol_links(property).unwrap().target,
                            Some(original)
                        );
                        assert_eq!(
                            demand_property_object_alias_property(
                                context.store_mut_for_test(),
                                &host,
                                &globals,
                                options,
                                &mut caller,
                                &mut diagnostics,
                                result,
                                property,
                            ),
                            Ok(string)
                        );
                        assert_eq!(
                            context
                                .store()
                                .value_symbol_links(original)
                                .unwrap()
                                .resolved_type,
                            Some(projection.parameters()[0])
                        );
                        assert_eq!(
                            context.store().symbol(original).unwrap().parent(),
                            Some(projection.source_symbol())
                        );
                        object_member = Some((
                            members.members.unwrap(),
                            property,
                            original,
                            context
                                .store()
                                .value_symbol_links(property)
                                .cloned()
                                .unwrap(),
                        ));
                    } else {
                        let array = context
                            .store()
                            .canonical_array_reference_with_targets(targets, result)
                            .unwrap()
                            .unwrap();
                        assert_eq!(array.element_type, string);
                        assert!(!array.readonly);
                        assert!(matches!(
                            context.store().type_payload(result).unwrap().data(),
                            TypeData::TypeReference(reference)
                                if reference.object.target == Some(globals.array_type)
                                    && reference.object.mapper.is_none()
                        ));
                    }
                    let warm = (
                        state(&context, &parsed, node),
                        payload_state(context.store(), &proof),
                    );
                    let caller_state = (
                        caller.query_count(),
                        caller.total_count(),
                        caller.limit_event_mark(),
                    );
                    let caller_address = std::ptr::from_ref(&caller);
                    for _ in 0..2 {
                        assert_eq!(
                            validate_source_conditional_result(
                                context.store(),
                                &proof,
                                &globals,
                                &source
                            ),
                            Ok(())
                        );
                        assert_eq!(
                            (
                                state(&context, &parsed, node),
                                payload_state(context.store(), &proof)
                            ),
                            warm
                        );
                        assert_eq!(
                            (
                                caller.query_count(),
                                caller.total_count(),
                                caller.limit_event_mark()
                            ),
                            caller_state
                        );
                    }
                    for damage in 0..if object_member.is_some() { 2 } else { 1 } {
                        let expected =
                            if let Some((table, property, original, links)) = &object_member {
                                if damage == 0 {
                                    assert_eq!(
                                        context.store_mut_for_test().insert_symbol(
                                            *table,
                                            EscapedName::source("value"),
                                            *original
                                        ),
                                        Some(Some(*property))
                                    );
                                } else {
                                    let mut changed = links.clone();
                                    changed.resolved_type = Some(number);
                                    assert!(
                                        context
                                            .store_mut_for_test()
                                            .set_value_symbol_links(*property, changed)
                                    );
                                }
                                ConditionalTypeError::Union(
                                    LiteralTypeCacheError::InvalidCachedUnion(result),
                                )
                            } else {
                                assert!(context.store_mut_for_test().set_object_target_and_mapper(
                                    result,
                                    Some(globals.readonly_array_type),
                                    None
                                ));
                                ConditionalTypeError::Union(LiteralTypeCacheError::ArrayType {
                                    type_: result,
                                    error: ArrayTypeError::InvalidReference(result),
                                })
                            };
                        let damaged = (
                            state(&context, &parsed, node),
                            payload_state(context.store(), &proof),
                        );
                        for _ in 0..2 {
                            assert_eq!(
                                validate_source_conditional_result(
                                    context.store(),
                                    &proof,
                                    &globals,
                                    &source
                                )
                                .as_ref()
                                .err(),
                                Some(&expected)
                            );
                            assert_eq!(
                                (
                                    state(&context, &parsed, node),
                                    payload_state(context.store(), &proof)
                                ),
                                damaged
                            );
                            assert_eq!(
                                (
                                    caller.query_count(),
                                    caller.total_count(),
                                    caller.limit_event_mark()
                                ),
                                caller_state
                            );
                            assert_eq!(std::ptr::from_ref(&caller), caller_address);
                        }
                        if let Some((table, property, _, links)) = &object_member {
                            assert!(
                                context
                                    .store_mut_for_test()
                                    .insert_symbol(*table, EscapedName::source("value"), *property)
                                    .is_some()
                            );
                            assert!(
                                context
                                    .store_mut_for_test()
                                    .set_value_symbol_links(*property, links.clone())
                            );
                        } else {
                            assert!(context.store_mut_for_test().set_object_target_and_mapper(
                                result,
                                Some(globals.array_type),
                                None
                            ));
                        }
                        assert_eq!(
                            validate_source_conditional_result(
                                context.store(),
                                &proof,
                                &globals,
                                &source
                            ),
                            Ok(())
                        );
                        assert_eq!(
                            (
                                state(&context, &parsed, node),
                                payload_state(context.store(), &proof)
                            ),
                            warm
                        );
                    }
                    let ConditionalSourceResult::Complete(replayed) =
                        get_conditional_type_instantiation_with_source(
                            context.store_mut_for_test(),
                            request,
                            &globals,
                            &mut caller,
                            &mut source,
                        )
                        .unwrap()
                    else {
                        panic!("restoring the mapped result must keep its complete identity")
                    };
                    assert_eq!(replayed.result(), result);
                    assert_eq!(replayed.production, proof.production);
                    assert_eq!(
                        (
                            state(&context, &parsed, node),
                            payload_state(context.store(), &proof)
                        ),
                        warm
                    );
                    assert!(
                        context
                            .store()
                            .type_node_links(excluded)
                            .is_none_or(|links| links.resolved_type.is_none())
                    );
                }
                assert!(diagnostics.is_empty());
                assert_eq!(caller.limit_event_count(), 0);
            }
        }

        fn literal_members(store: &CanonicalTypeMapperStore, type_: TypeId) -> Vec<String> {
            let TypeData::Union(union) = store.type_payload(type_).unwrap().data() else {
                panic!("the written literal alternatives must remain a union")
            };
            union
                .union
                .types
                .iter()
                .map(|member| {
                    let TypeData::Literal(literal) = store.type_payload(*member).unwrap().data()
                    else {
                        panic!("each constraint result must be a real literal")
                    };
                    let LiteralValue::String(value) = &literal.value else {
                        panic!("each mapped bound must be a string literal")
                    };
                    value.clone()
                })
                .collect()
        }

        #[test]
        #[allow(clippy::too_many_lines)] // Keep each written bound, damaged cache and restored identity together.
        fn source_conditional_constraints_replay_template_and_mapping_bounds_in_the_same_caller() {
            let parsed = parse_source_file(concat!(
                "type Uppercase<S extends string> = intrinsic;\n",
                "type Template<T extends \"a\" | \"b\"> = `pre-${T}`;\n",
                "type Mapping<T extends \"a\" | \"b\"> = Uppercase<T>;\n",
                "type Caller<T> = T;\n",
            ));
            let mut context = context(&parsed, true);
            let template = declared(&mut context, "Template");
            let mapping = declared(&mut context, "Mapping");
            let globals = context.global_types().clone();
            let mut source = HeaderSource {
                options: source_options(&context),
                members: None,
            };
            let mut caller = InstantiationSession::new(InstantiationLimits {
                max_count: 1,
                ..InstantiationLimits::default()
            });
            charge_source_parameter(&mut context, &mut caller);
            let caller_address = std::ptr::from_ref(&caller);
            let caller_state = (
                caller.query_count(),
                caller.total_count(),
                caller.limit_event_mark(),
            );
            for (type_, expected) in [(template, ["pre-a", "pre-b"]), (mapping, ["A", "B"])] {
                let result = constraints::get_base_constraint_of_type_with_source(
                    context.store_mut_for_test(),
                    type_,
                    &globals,
                    &mut caller,
                    &mut source,
                )
                .unwrap()
                .unwrap();
                assert_eq!(literal_members(context.store(), result), expected);
                assert_eq!(
                    context
                        .store()
                        .type_payload(type_)
                        .unwrap()
                        .data()
                        .constrained()
                        .unwrap()
                        .resolved_base_constraint,
                    Some(result)
                );
                let root = annotation(&context, "Template");
                let warm = state(&context, &parsed, root);
                for _ in 0..2 {
                    assert_eq!(
                        constraints::get_base_constraint_of_type_with_source(
                            context.store_mut_for_test(),
                            type_,
                            &globals,
                            &mut caller,
                            &mut source
                        ),
                        Ok(Some(result))
                    );
                    assert_eq!(std::ptr::from_ref(&caller), caller_address);
                    assert_eq!(
                        (
                            caller.query_count(),
                            caller.total_count(),
                            caller.limit_event_mark()
                        ),
                        caller_state
                    );
                    assert_eq!(state(&context, &parsed, root), warm);
                }
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                assert!(
                    context
                        .store_mut_for_test()
                        .set_resolved_base_constraint(type_, Some(number))
                );
                for _ in 0..2 {
                    assert_eq!(
                        constraints::get_base_constraint_of_type_with_source(
                            context.store_mut_for_test(),
                            type_,
                            &globals,
                            &mut caller,
                            &mut source
                        ),
                        Err(ConstraintError::InvalidCachedConstraint(type_))
                    );
                    assert_eq!(
                        context
                            .store()
                            .type_payload(type_)
                            .unwrap()
                            .data()
                            .constrained()
                            .unwrap()
                            .resolved_base_constraint,
                        Some(number)
                    );
                    assert_eq!(state(&context, &parsed, root), warm);
                    assert_eq!(
                        (
                            caller.query_count(),
                            caller.total_count(),
                            caller.limit_event_mark()
                        ),
                        caller_state
                    );
                }
                assert!(
                    context
                        .store_mut_for_test()
                        .set_resolved_base_constraint(type_, Some(result))
                );
                assert_eq!(
                    constraints::get_base_constraint_of_type_with_source(
                        context.store_mut_for_test(),
                        type_,
                        &globals,
                        &mut caller,
                        &mut source
                    ),
                    Ok(Some(result))
                );
                assert_eq!(state(&context, &parsed, root), warm);
            }
        }
    }

    fn source_conditional_context(
        parsed: &ParseResult,
        file: FileId,
    ) -> CanonicalCheckerContext<'_> {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/conditional-callable-unit.ts\""),
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
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn source_conditional_symbol(
        context: &CanonicalCheckerContext<'_>,
        name: &str,
    ) -> SemanticSymbolId {
        let store = context.store();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let symbol = store
            .symbol_table(globals)
            .unwrap()
            .get_source(name)
            .unwrap();
        store.get_merged_symbol(symbol).unwrap()
    }

    fn source_conditional_annotation(
        context: &CanonicalCheckerContext<'_>,
        symbol: SemanticSymbolId,
    ) -> NodeRef {
        let declaration = context
            .store()
            .symbol(symbol)
            .unwrap()
            .declarations()
            .unwrap()[0];
        context
            .store()
            .source_direct_type_annotation(declaration)
            .unwrap()
    }

    fn conditional_callable_counts(store: &CanonicalTypeMapperStore) -> [usize; 6] {
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ]
    }

    // Prepare the real declared call template without resolving the concrete reference.
    #[allow(clippy::too_many_lines)] // Keep source publication and the unchanged reference proof together.
    fn prepare_source_conditional_callable_template(
        context: &mut CanonicalCheckerContext<'_>,
        reference: TypeId,
    ) {
        let direct = validate_direct_generic_reference(context.store(), reference).unwrap();
        assert_ne!(direct.target, reference);
        let owner = context
            .store()
            .type_payload(direct.target)
            .unwrap()
            .symbol()
            .unwrap();
        let plan = {
            let host = context.declared_type_host().unwrap();
            plan_generic_interface(context.store(), &host, owner).unwrap()
        };
        assert!(plan.heritage.is_none());
        assert!(plan.properties.is_empty());
        assert_eq!(plan.call_signatures.len(), 1);
        let source_file = context.source_file(plan.node.file).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source_file)
                .is_none_or(|links| !links.type_checked)
        );
        let record = context.store().type_payload(reference).unwrap();
        let TypeData::TypeReference(cold) = record.data() else {
            panic!("the source annotation must produce a concrete interface reference")
        };
        let flags = record.object_flags();
        let identity = (record.flags(), record.symbol(), record.alias());
        let cold = cold.clone();
        assert!(!flags.contains(ObjectFlags::MEMBERS_RESOLVED));
        assert_eq!(cold.object.structured, StructuredTypeData::default());
        assert_eq!(cold.object.mapper, None);
        assert!(matches!(
            context.store().type_payload(direct.target).unwrap().data(),
            TypeData::Interface(target)
                if !target.declared_members_resolved && target.declared_call_signatures.is_none()
        ));
        assert!(
            !context
                .store()
                .type_has_declared_call_set_provenance(direct.target)
        );
        for annotation in plan.call_type_nodes() {
            context.get_type_from_type_node(annotation).unwrap();
        }
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        assert!(store.publish_interface_no_base_resolution(direct.target));
        assert_eq!(
            publish_generic_interface_declared_members_with_global_types(
                store,
                &plan,
                direct.target,
                &[],
                &globals,
            ),
            Ok(direct.target),
        );
        let TypeData::Interface(target) = store.type_payload(direct.target).unwrap().data() else {
            panic!("the declared callable must keep its interface target")
        };
        assert!(target.declared_members_resolved);
        let [signature] = target.declared_call_signatures.as_deref().unwrap() else {
            panic!("the declared template must keep its one source call signature")
        };
        let declaration = plan.call_signatures[0].declaration;
        assert_eq!(
            store.signature(*signature).unwrap().declaration(),
            Some(declaration)
        );
        assert_eq!(
            store
                .signature_links(declaration)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(*signature),
        );
        assert!(store.type_has_declared_call_set_provenance(direct.target));
        assert!(!store.type_has_declared_call_set_provenance(reference));
        assert_eq!(
            validate_direct_generic_reference(store, reference),
            Ok(direct)
        );
        let record = store.type_payload(reference).unwrap();
        let TypeData::TypeReference(actual) = record.data() else {
            panic!("declared template preparation must keep the concrete reference")
        };
        assert_eq!(actual, &cold);
        assert_eq!(record.object_flags(), flags);
        assert_eq!((record.flags(), record.symbol(), record.alias()), identity);
        assert!(
            store
                .source_file_links(source_file)
                .is_none_or(|links| !links.type_checked)
        );
        assert!(matches!(
            validate_generic_interface_callable(
                store,
                reference,
                Some(CanonicalArrayTargets::from_global_types(&globals)),
            ),
            Some(StoredCallableSetValidation::Pending { .. })
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check the same source query after each copied-signature mutation.
    fn conditional_callable_operands_reject_changed_copied_signatures_and_mappers() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {}\n",
            "interface Validator<T> { (value: T[]): T[]; }\n",
            "type Validated<V> = V extends Validator<infer T> ? T : never;\n",
            "type Forward<Unused, V> = Validated<V>;\n",
            "declare const validator: Validator<number>;\n",
            "declare const numbers: number[]; validator(numbers);\n",
            "type Verified = Validated<Validator<number>>;\n",
            "type Forwarded = Forward<Validator<number>, Validator<string>>;\n",
        ));
        let file = FileId::new(202_625);
        for corruption in 0..3 {
            let mut context = source_conditional_context(&parsed, file);
            let arrays = Some(CanonicalArrayTargets::from_global_types(
                context.global_types(),
            ));
            let validator = source_conditional_symbol(&context, "validator");
            let annotation = source_conditional_annotation(&context, validator);
            let reference = context.get_type_from_type_node(annotation).unwrap();
            prepare_source_conditional_callable_template(&mut context, reference);
            let cold = context
                .store()
                .type_payload(reference)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .clone();
            assert!(cold.signatures.is_none());
            let before = conditional_callable_counts(context.store());
            assert_eq!(
                validate_conditional_operand(
                    context.store(),
                    reference,
                    &mut HashSet::new(),
                    arrays
                ),
                Ok(())
            );
            assert_eq!(
                validate_conditional_operand(context.store(), reference, &mut HashSet::new(), None),
                Err(ConditionalTypeError::Relation(
                    RelationUnavailable::MalformedFunctionType(reference)
                )),
            );
            assert_eq!(conditional_callable_counts(context.store()), before);
            assert_eq!(
                context
                    .store()
                    .type_payload(reference)
                    .unwrap()
                    .data()
                    .structured(),
                Some(&cold)
            );

            context.check_source_file(file).unwrap();
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let verified = source_conditional_symbol(&context, "Verified");
            let query = source_conditional_annotation(&context, verified);
            assert_eq!(context.get_declared_type_of_symbol(verified), Ok(number));
            let forwarded = source_conditional_symbol(&context, "Forwarded");
            let forwarded_query = source_conditional_annotation(&context, forwarded);
            assert_eq!(context.get_declared_type_of_symbol(forwarded), Ok(string));
            let Some(StoredCallableSetValidation::Valid { projection, .. }) =
                super::super::instantiated_members::validate_generic_interface_callable(
                    context.store(),
                    reference,
                    arrays,
                )
            else {
                panic!("the real call must retain an authenticated copied signature")
            };
            let signature = projection.call_signatures[0].signature;
            let store = context.store_mut_for_test();
            assert_eq!(store.callable_signature_parameter_types(signature), None);
            assert_eq!(
                validate_conditional_operand(store, reference, &mut HashSet::new(), arrays),
                Ok(())
            );
            assert_eq!(
                validate_conditional_reference_result_with_array_targets(
                    store, query, number, arrays
                ),
                Ok(true)
            );
            assert_eq!(
                validate_conditional_reference_result_with_array_targets(
                    store,
                    forwarded_query,
                    string,
                    arrays,
                ),
                Ok(true),
            );
            let forwarded_proof = store
                .conditional_query_production(ConditionalQueryKey::AliasReference(forwarded_query))
                .unwrap();
            assert_eq!(forwarded_proof.type_arguments.len(), 1);
            assert!(!forwarded_proof.type_arguments.contains(&reference));
            assert_eq!(forwarded_proof.alias.as_ref().unwrap().1[0], reference);
            let source = store.signature(signature).unwrap().target().unwrap();
            let parameter = store.signature(signature).unwrap().parameters()[0];
            match corruption {
                0 => {
                    assert!(store.set_signature_resolved_return_type(signature, Some(number)));
                }
                1 => {
                    let mut links = store.value_symbol_links(parameter).unwrap().clone();
                    links.resolved_type = Some(number);
                    assert!(store.set_value_symbol_links(parameter, links));
                }
                _ => {
                    let source_parameter = store.signature(source).unwrap().parameters()[0];
                    let template = store
                        .value_symbol_links(source_parameter)
                        .unwrap()
                        .resolved_type
                        .unwrap();
                    let mapper = store.new_type_mapper(vec![template], vec![number]).unwrap();
                    assert!(store.set_signature_target_and_mapper(
                        signature,
                        Some(source),
                        Some(mapper)
                    ));
                }
            }
            let before = conditional_callable_counts(store);
            for _ in 0..2 {
                assert_eq!(
                    validate_conditional_operand(store, reference, &mut HashSet::new(), arrays),
                    Err(ConditionalTypeError::Relation(
                        RelationUnavailable::MalformedFunctionType(reference)
                    )),
                );
                assert_eq!(
                    validate_conditional_reference_result_with_array_targets(
                        store, query, number, arrays
                    ),
                    Err(ConditionalTypeError::Relation(
                        RelationUnavailable::MalformedFunctionType(reference)
                    )),
                );
                assert_eq!(
                    validate_conditional_reference_result_with_array_targets(
                        store,
                        forwarded_query,
                        string,
                        arrays,
                    ),
                    Err(ConditionalTypeError::Relation(
                        RelationUnavailable::MalformedFunctionType(reference)
                    )),
                );
                assert_eq!(conditional_callable_counts(store), before);
            }
        }
    }

    #[test]
    fn conditional_callable_inference_rejects_pending_structural_members() {
        let parsed = parse_source_file(concat!(
            "interface Callable<T> { (value: T): T; }\n",
            "type Result<C> = C extends (value: string) => infer R ? R : never;\n",
            "declare const callable: Callable<string>;\n",
            "type Text = Result<Callable<string>>;\n",
        ));
        let file = FileId::new(202_626);
        let mut context = source_conditional_context(&parsed, file);
        let callable = source_conditional_symbol(&context, "callable");
        let annotation = source_conditional_annotation(&context, callable);
        let reference = context.get_type_from_type_node(annotation).unwrap();
        prepare_source_conditional_callable_template(&mut context, reference);
        let result = source_conditional_symbol(&context, "Result");
        let conditional = context.get_declared_type_of_symbol(result).unwrap();
        let store = context.store_mut_for_test();
        let data = conditional_snapshot(store, conditional, None).unwrap();
        let root = store.conditional_root(data.root).unwrap();
        let branches = ConditionalTypeBranches {
            true_type: root.infer_type_parameters().unwrap()[0],
            false_type: store.intrinsic_bootstrap().unwrap().never_type,
        };
        let cache = root.instantiations().clone();
        let before = conditional_callable_counts(store);
        assert!(matches!(
            structured_inference_shape(store, reference, None, None),
            Err(ConditionalTypeError::Relation(RelationUnavailable::UnresolvedStructuredMembers(type_))) if type_ == reference
        ));
        assert_eq!(conditional_callable_counts(store), before);
        assert_eq!(
            get_conditional_type_instantiation(
                store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[reference],
                    branches,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Err(ConditionalTypeError::Relation(
                RelationUnavailable::UnresolvedStructuredMembers(reference)
            )),
        );
        assert_eq!(
            store.conditional_root(data.root).unwrap().instantiations(),
            &cache
        );
        let record = store.type_payload(reference).unwrap();
        assert!(
            !record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        assert!(record.data().structured().unwrap().signatures.is_none());
    }

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl Fixture {
        fn new(source: &str) -> Self {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(17);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/conditional.ts\""),
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
            let mut store = SemanticStore::<TypeRecord, TypeMapper>::from_symbol_store(symbols);
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
            store
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            let locals = bound.locals(bound.source_file()).unwrap();
            let mut symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
                .collect::<Vec<_>>();
            symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            for (_, symbol) in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn conditional(&self) -> NodeRef {
            self.parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ConditionalType).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        node,
                    ))
                })
                .unwrap()
        }

        fn type_parameter(&mut self, expected: &str) -> TypeId {
            let declaration = self
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeParameterDeclaration(parameter) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &self.parsed.arena.get(parameter.name)?.data
                    else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        node,
                    ))
                })
                .unwrap_or_else(|| panic!("missing type parameter {expected}"));
            let symbol = self
                .bound
                .symbol(declaration)
                .unwrap_or_else(|| panic!("missing type-parameter symbol {expected}"));
            execute_type_parameter(&mut self.store, symbol)
        }

        fn alias_declaration(&self, expected: &str) -> NodeRef {
            self.parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &self.parsed.arena.get(alias.name)?.data
                    else {
                        return None;
                    };
                    (name.text == expected).then_some(NodeRef::new(
                        self.parsed.arena.id(),
                        self.file,
                        node,
                    ))
                })
                .unwrap_or_else(|| panic!("missing type alias {expected}"))
        }

        fn alias_symbol(&self, expected: &str) -> SemanticSymbolId {
            self.bound
                .symbol(self.alias_declaration(expected))
                .unwrap_or_else(|| panic!("missing type-alias symbol {expected}"))
        }

        fn declared_alias(&mut self, expected: &str) -> TypeId {
            self.try_declared_alias(expected)
                .unwrap_or_else(|error| panic!("type alias {expected} failed: {error:?}"))
        }

        fn try_declared_alias(&mut self, expected: &str) -> Result<TypeId, DeclaredTypeError> {
            let symbol = self.alias_symbol(expected);
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let result = CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(symbol);
            assert!(diagnostics.is_empty());
            result
        }
    }

    fn branches(true_type: TypeId, false_type: TypeId) -> ConditionalTypeBranches {
        ConditionalTypeBranches {
            true_type,
            false_type,
        }
    }

    fn callable_object(
        store: &mut CanonicalTypeMapperStore,
        return_type: TypeId,
        construct: bool,
    ) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let signature = store
            .alloc_signature(
                if construct {
                    SignatureFlags::CONSTRUCT
                } else {
                    SignatureFlags::NONE
                },
                None,
                Vec::new(),
                None,
                Vec::new(),
                Some(return_type),
                None,
                0,
            )
            .unwrap();
        let call = (!construct).then(|| vec![signature]);
        let constructor = construct.then(|| vec![signature]);
        assert!(store.set_structured_type_members(object, None, None, call, constructor, None));
        object
    }

    fn property_object(store: &mut CanonicalTypeMapperStore, name: &str, value: TypeId) -> TypeId {
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let property = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source(name),
            ))
            .unwrap();
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(value),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            object,
            None,
            Some(vec![property]),
            None,
            None,
            None,
        ));
        object
    }

    #[test]
    fn concrete_conditionals_choose_the_correct_branch_and_reuse_node_identity() {
        let mut fixture = Fixture::new("type Result = string extends string ? number : boolean;");
        let node = fixture.conditional();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let request = ConditionalTypeRequest {
            node,
            check_type: string,
            extends_type: string,
            branches: branches(number, boolean),
            infer_type_parameters: &[],
            outer_type_parameters: None,
            alias: None,
        };

        assert_eq!(
            get_type_from_conditional_type(&mut fixture.store, request, None),
            Ok(number)
        );
        assert_eq!(fixture.store.conditional_root_len(), 1);
        assert_eq!(
            fixture
                .store
                .type_node_links(node)
                .and_then(|links| links.resolved_type),
            Some(number)
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_type_from_conditional_type(&mut fixture.store, request, None),
            Ok(number)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            warm
        );
    }

    #[test]
    fn distributive_conditionals_filter_unions_and_preserve_never() {
        let mut fixture = Fixture::new("type Exclude<T, U> = T extends U ? never : T;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let excluded = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let branch_types = branches(never, parameter);
        let declared = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: excluded,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: Some(&[parameter, excluded]),
                alias: None,
            },
            None,
        )
        .unwrap();
        let TypeData::Conditional(conditional) =
            fixture.store.type_payload(declared).unwrap().data()
        else {
            panic!("a generic conditional must retain its deferred type identity")
        };
        let root = conditional.root;
        let root_record = fixture.store.conditional_root(root).unwrap();
        assert_eq!(root_record.node(), node);
        assert!(root_record.is_distributive());
        assert_eq!(
            root_record.outer_type_parameters(),
            Some([parameter, excluded].as_slice())
        );
        let TypeCacheState::Allocated(cache) = root_record.instantiations() else {
            panic!("a generic conditional root owns its instantiation cache")
        };
        assert_eq!(cache.len(), 1);

        let union = canonical_anonymous_union(&mut fixture.store, &[string, number]).unwrap();
        let filtered = get_conditional_type_instantiation(
            &mut fixture.store,
            ConditionalTypeInstantiation {
                conditional_type: declared,
                type_arguments: &[union, string],
                branches: branch_types,
                alias: None,
                for_constraint: false,
            },
            None,
            None,
        )
        .unwrap();
        assert_eq!(filtered, number);
        let warm = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[union, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(number)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            warm
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[never, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(never)
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // All trivial bounds share one root and cache identity proof.
    fn trivial_distributive_instantiations_preserve_checked_parameter_identity() {
        #[derive(Clone, Copy)]
        enum Bound {
            Never,
            Checked,
            Any,
            Unknown,
        }

        for (keep_true, bound) in [
            (false, Bound::Never),
            (true, Bound::Checked),
            (true, Bound::Any),
            (true, Bound::Unknown),
        ] {
            let source = if keep_true {
                "type Select<T, U> = T extends U ? T : never; type Caller<Value> = Value;"
            } else {
                "type Select<T, U> = T extends U ? never : T; type Caller<Value> = Value;"
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound_parameter = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let never = bootstrap.never_type;
            let actual_bound = match bound {
                Bound::Never => never,
                Bound::Checked => checked,
                Bound::Any => bootstrap.any_type,
                Bound::Unknown => bootstrap.unknown_type,
            };
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound_parameter,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter, bound_parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            let root = match fixture.store.type_payload(conditional).unwrap().data() {
                TypeData::Conditional(data) => data.root,
                _ => panic!("the generic declaration must retain its conditional root"),
            };
            let mapper_count = fixture.store.mapper_len();
            let arguments = [checked, actual_bound];

            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(checked),
            );
            assert_eq!(fixture.store.mapper_len(), mapper_count);
            let TypeCacheState::Allocated(cache) = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
            else {
                panic!("the generic conditional root retains its instantiation cache")
            };
            assert_eq!(cache.len(), 2);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(checked),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations()
                        .clone(),
                ),
                warm,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Impossible bounds share one root and warm-cache matrix.
    fn trivial_distributive_instantiations_reduce_impossible_branches_to_never() {
        #[derive(Clone, Copy)]
        enum Bound {
            Never,
            Checked,
            Any,
            Unknown,
        }

        for (keep_true, bound) in [
            (true, Bound::Never),
            (false, Bound::Checked),
            (false, Bound::Any),
            (false, Bound::Unknown),
        ] {
            let source = if keep_true {
                "type Select<T, U> = T extends U ? T : never; type Caller<Value> = Value;"
            } else {
                "type Select<T, U> = T extends U ? never : T; type Caller<Value> = Value;"
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound_parameter = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let never = bootstrap.never_type;
            let actual_bound = match bound {
                Bound::Never => never,
                Bound::Checked => checked,
                Bound::Any => bootstrap.any_type,
                Bound::Unknown => bootstrap.unknown_type,
            };
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound_parameter,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter, bound_parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            let mapper_count = fixture.store.mapper_len();

            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, actual_bound],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(never),
            );
            assert_eq!(fixture.store.mapper_len(), mapper_count);
            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, actual_bound],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(never),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn trivial_conditional_never_reductions_preserve_any_semantics() {
        for (keep_true, use_any_bound, expected_any) in [
            (true, false, true),
            (true, true, true),
            (false, false, true),
            (false, true, false),
        ] {
            let source = if keep_true {
                "type Select<T, U> = T extends U ? T : never;"
            } else {
                "type Select<T, U> = T extends U ? never : T;"
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound = fixture.type_parameter("U");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (any, never) = (bootstrap.any_type, bootstrap.never_type);
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter, bound]),
                    alias: None,
                },
                None,
            )
            .unwrap();

            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[any, if use_any_bound { any } else { never }],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(if expected_any { any } else { never }),
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Literal and primitive constraints share one safety matrix.
    fn constrained_primitive_conditionals_reduce_only_when_domains_are_disjoint() {
        for (keep_true, use_literals) in [(true, false), (false, false), (true, true)] {
            let source = if keep_true {
                concat!(
                    "type Select<T, U> = T extends U ? T : never; ",
                    "type Caller<Value> = Value;",
                )
            } else {
                concat!(
                    "type Select<T, U> = T extends U ? never : T; ",
                    "type Caller<Value> = Value;",
                )
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, never) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
            );
            let (constraint, disjoint_bound, compatible_bound) = if use_literals {
                (
                    fixture
                        .store
                        .regular_string_literal_type("left".to_owned())
                        .unwrap(),
                    fixture
                        .store
                        .regular_string_literal_type("right".to_owned())
                        .unwrap(),
                    string,
                )
            } else {
                (string, number, string)
            };
            assert!(fixture.store.set_type_parameter_resolution(
                checked,
                Some(constraint),
                None,
                None,
                None,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                disjoint_bound,
            ));
            assert!(!conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                compatible_bound,
            ));
            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter, bound]),
                    alias: None,
                },
                None,
            )
            .unwrap();

            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, disjoint_bound],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(if keep_true { never } else { checked }),
            );
            let unresolved = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, compatible_bound],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            assert!(matches!(
                fixture.store.type_payload(unresolved).map(TypeRecord::data),
                Some(TypeData::Conditional(_))
            ));
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Primitive and literal unions share one bounded proof matrix.
    fn bounded_primitive_union_constraints_reduce_only_disjoint_members() {
        for (keep_true, use_literals) in
            [(true, false), (false, false), (true, true), (false, true)]
        {
            let source = if keep_true {
                concat!(
                    "type Select<T, U> = T extends U ? T : never; ",
                    "type Caller<Value, Other> = Value;",
                )
            } else {
                concat!(
                    "type Select<T, U> = T extends U ? never : T; ",
                    "type Caller<Value, Other> = Value;",
                )
            };
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bound = fixture.type_parameter("U");
            let checked = fixture.type_parameter("Value");
            let other = fixture.type_parameter("Other");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, bigint, symbol, never) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.es_symbol_type,
                bootstrap.never_type,
            );
            let (constraint_members, disjoint_members, overlapping_members) = if use_literals {
                let left = fixture
                    .store
                    .regular_string_literal_type("left".to_owned())
                    .unwrap();
                let center = fixture
                    .store
                    .regular_string_literal_type("center".to_owned())
                    .unwrap();
                let right = fixture
                    .store
                    .regular_string_literal_type("right".to_owned())
                    .unwrap();
                let other = fixture
                    .store
                    .regular_string_literal_type("other".to_owned())
                    .unwrap();
                ([left, center], [right, other], [center, right])
            } else {
                ([string, bigint], [number, symbol], [string, number])
            };
            let constraint =
                canonical_anonymous_union(&mut fixture.store, &constraint_members).unwrap();
            let disjoint =
                canonical_anonymous_union(&mut fixture.store, &disjoint_members).unwrap();
            let overlapping =
                canonical_anonymous_union(&mut fixture.store, &overlapping_members).unwrap();
            assert!(fixture.store.set_type_parameter_resolution(
                checked,
                Some(constraint),
                None,
                None,
                None,
            ));
            assert!(fixture.store.set_type_parameter_resolution(
                other,
                Some(disjoint),
                None,
                None,
                None,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                disjoint,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                other,
            ));
            assert!(conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                constraint,
                disjoint,
            ));
            assert!(!conditional_operands_have_disjoint_primitive_domains(
                &fixture.store,
                checked,
                overlapping,
            ));

            let branch_types = if keep_true {
                branches(parameter, never)
            } else {
                branches(never, parameter)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: bound,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter, bound]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            for actual_bound in [disjoint, other] {
                assert_eq!(
                    get_conditional_type_instantiation(
                        &mut fixture.store,
                        ConditionalTypeInstantiation {
                            conditional_type: conditional,
                            type_arguments: &[checked, actual_bound],
                            branches: branch_types,
                            alias: None,
                            for_constraint: false,
                        },
                        None,
                        None,
                    ),
                    Ok(if keep_true { never } else { checked }),
                );
            }

            let unresolved = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, overlapping],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            assert!(matches!(
                fixture.store.type_payload(unresolved).map(TypeRecord::data),
                Some(TypeData::Conditional(_))
            ));

            let warm = (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.conditional_root_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[checked, disjoint],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(if keep_true { never } else { checked }),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.mapper_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn primitive_union_disjointness_enforces_constituent_and_comparison_limits() {
        let mut fixture = Fixture::new("type Caller<Value> = Value;");
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let mut strings = Vec::new();
        for index in 0..=MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS {
            strings.push(
                fixture
                    .store
                    .regular_string_literal_type(format!("value-{index}"))
                    .unwrap(),
            );
        }
        let bounded = canonical_anonymous_union(
            &mut fixture.store,
            &strings[..MAX_CONDITIONAL_PRIMITIVE_UNION_CONSTITUENTS],
        )
        .unwrap();
        let oversized = canonical_anonymous_union(&mut fixture.store, &strings).unwrap();
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            bounded,
            number,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            oversized,
            number,
        ));

        let bounded_comparisons =
            canonical_anonymous_union(&mut fixture.store, &strings[..8]).unwrap();
        let excessive_comparisons =
            canonical_anonymous_union(&mut fixture.store, &strings[..9]).unwrap();
        let mut numbers = Vec::new();
        for value in 0..8 {
            numbers.push(
                fixture
                    .store
                    .regular_number_literal_type(ts_jsnum::Number::new(f64::from(value)))
                    .unwrap(),
            );
        }
        let right = canonical_anonymous_union(&mut fixture.store, &numbers).unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            bounded_comparisons,
            right,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            excessive_comparisons,
            right,
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn primitive_union_disjointness_rejects_forged_union_identities() {
        let mut fixture = Fixture::new("type Caller<Value> = Value;");
        let checked = fixture.type_parameter("Value");
        let left = fixture
            .store
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let right = fixture
            .store
            .regular_string_literal_type("right".to_owned())
            .unwrap();
        let canonical = canonical_anonymous_union(&mut fixture.store, &[left, right]).unwrap();
        let members = match fixture.store.type_payload(canonical).unwrap().data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => panic!("two distinct string literals must retain a canonical union"),
        };
        let forged = fixture
            .store
            .alloc_union_type(ObjectFlags::NONE, members)
            .unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(canonical),
            None,
            None,
            None,
        ));
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            number,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            forged,
            number,
        ));
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(forged),
            None,
            None,
            None,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            number,
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One proof covers forged literals, owners, and cycles.
    fn disjoint_primitive_conditional_proofs_reject_forged_caches() {
        let mut fixture = Fixture::new("type Caller<Value, Other> = Value;");
        let checked = fixture.type_parameter("Value");
        let other = fixture.type_parameter("Other");
        let left = fixture
            .store
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let right = fixture
            .store
            .regular_string_literal_type("right".to_owned())
            .unwrap();
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(checked, Some(left), None, None, None,)
        );
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));

        let forged = fixture
            .store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                LiteralValue::String("left".to_owned()),
                RegularLiteralLink::SelfType,
            )
            .unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(forged),
            None,
            None,
            None,
        ));
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(checked, Some(left), None, None, None,)
        );

        let owner = cached_ordinary_type_parameter_owner(&fixture.store, checked).unwrap();
        let links = fixture.store.declared_type_links(owner).unwrap().clone();
        assert!(
            fixture
                .store
                .set_declared_type_links(owner, DeclaredTypeLinks::default())
        );
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));
        assert!(fixture.store.set_declared_type_links(owner, links));
        assert!(conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));

        assert!(fixture.store.set_type_parameter_resolution(
            other,
            Some(checked),
            None,
            None,
            None,
        ));
        assert!(fixture.store.set_type_parameter_resolution(
            checked,
            Some(other),
            None,
            None,
            None,
        ));
        let cyclic = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(!conditional_operands_have_disjoint_primitive_domains(
            &fixture.store,
            checked,
            right,
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            cyclic,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One root covers identity, keyof, and deferred cases.
    fn templated_conditional_identity_simplifies_only_proven_branches() {
        let mut fixture = Fixture::new(concat!(
            "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
            "Check extends Bound ? WhenTrue : WhenFalse; ",
            "type Caller<Value> = Value;",
        ));
        let node = fixture.conditional();
        let check = fixture.type_parameter("Check");
        let bound = fixture.type_parameter("Bound");
        let when_true = fixture.type_parameter("WhenTrue");
        let when_false = fixture.type_parameter("WhenFalse");
        let checked = fixture.type_parameter("Value");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (never, string, number) = (
            bootstrap.never_type,
            bootstrap.string_type,
            bootstrap.number_type,
        );
        let keys = fixture
            .store
            .alloc_index_type(checked, IndexFlags::NONE)
            .unwrap();
        let branch_types = branches(when_true, when_false);
        let parameters = [check, bound, when_true, when_false];
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: check,
                extends_type: bound,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: Some(&parameters),
                alias: None,
            },
            None,
        )
        .unwrap();
        let root = match fixture.store.type_payload(conditional).unwrap().data() {
            TypeData::Conditional(data) => data.root,
            _ => panic!("the generic declaration must retain its conditional root"),
        };

        for (arguments, expected) in [
            ([checked, never, never, checked], checked),
            ([checked, checked, checked, never], checked),
            ([checked, string, checked, checked], checked),
            ([keys, never, never, keys], keys),
            ([keys, keys, keys, never], keys),
        ] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &arguments,
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected),
            );
        }

        for arguments in [
            [checked, string, checked, never],
            [checked, never, number, number],
        ] {
            let deferred = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &arguments,
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            let TypeData::Conditional(data) = fixture.store.type_payload(deferred).unwrap().data()
            else {
                panic!("an unproven distributive conditional must remain deferred")
            };
            assert_eq!(data.root, root);
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
        }

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[never, string, number, number],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(never),
            "equal non-identity branches must not erase distributive never",
        );
    }

    #[test]
    fn extract_against_any_preserves_the_original_concrete_union() {
        let mut fixture = Fixture::new("type Extract<T, U> = T extends U ? T : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bound = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, any, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.any_type,
            bootstrap.never_type,
        );
        let branch_types = branches(parameter, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: bound,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: Some(&[parameter, bound]),
                alias: None,
            },
            None,
        )
        .unwrap();
        let union = canonical_anonymous_union(&mut fixture.store, &[number, string]).unwrap();

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[union, any],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(union),
        );
    }

    #[test]
    fn trivial_conditional_alias_type_nodes_resolve_to_the_checked_identity() {
        for (source, alias) in [
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value> = Exclude<Value, never>;",
                ),
                "Exclude",
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value> = Extract<Value, Value>;",
                ),
                "Extract",
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value> = Extract<Value, any>;",
                ),
                "Extract",
            ),
            (
                concat!(
                    "type ExcludeWithDefault<T, U, D = never> = T extends U ? D : T; ",
                    "type Result<Value> = ExcludeWithDefault<Value, never>;",
                ),
                "ExcludeWithDefault",
            ),
            (
                concat!(
                    "type ExtractWithDefault<T, U, D = never> = T extends U ? T : D; ",
                    "type Result<Value> = ExtractWithDefault<Value, Value>;",
                ),
                "ExtractWithDefault",
            ),
            (
                concat!(
                    "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                    "Check extends Bound ? WhenTrue : WhenFalse; ",
                    "type Result<Value> = Select<Value, never, never, Value>;",
                ),
                "Select",
            ),
            (
                concat!(
                    "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                    "Check extends Bound ? WhenTrue : WhenFalse; ",
                    "type Result<Value> = Select<Value, Value, Value, never>;",
                ),
                "Select",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            assert_eq!(fixture.declared_alias("Result"), checked, "{alias}");
            let conditional = fixture.declared_alias(alias);
            let TypeData::Conditional(data) =
                fixture.store.type_payload(conditional).unwrap().data()
            else {
                panic!("{alias} must retain its original deferred declaration")
            };
            assert!(data.resolved_true_type.is_none());
            assert!(data.resolved_false_type.is_none());
            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), checked, "{alias}");
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn impossible_conditional_alias_type_nodes_reduce_to_never() {
        for source in [
            concat!(
                "type Extract<T, U> = T extends U ? T : never; ",
                "type Result<Value> = Extract<Value, never>;",
            ),
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<Value, Value>;",
            ),
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<Value, any>;",
            ),
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<Value, unknown>;",
            ),
            concat!(
                "type ExtractWithDefault<T, U, D = never> = T extends U ? T : D; ",
                "type Result<Value> = ExtractWithDefault<Value, never>;",
            ),
            concat!(
                "type ExcludeWithDefault<T, U, D = never> = T extends U ? D : T; ",
                "type Result<Value> = ExcludeWithDefault<Value, Value>;",
            ),
            concat!(
                "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                "Check extends Bound ? WhenTrue : WhenFalse; ",
                "type Result<Value> = Select<Value, never, Value, never>;",
            ),
            concat!(
                "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                "Check extends Bound ? WhenTrue : WhenFalse; ",
                "type Result<Value> = Select<Value, Value, never, Value>;",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
            assert_eq!(fixture.declared_alias("Result"), never);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), never);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn constrained_conditional_alias_type_nodes_use_only_disjoint_primitive_proofs() {
        for (source, preserves_parameter) in [
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string> = Extract<Value, number>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends string> = Exclude<Value, number>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string, Bound extends number> = ",
                    "Extract<Value, Bound>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends string, Bound extends number> = ",
                    "Exclude<Value, Bound>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends 'left'> = Extract<Value, 'right'>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends 'left'> = Exclude<Value, 'right'>;",
                ),
                true,
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            let expected = if preserves_parameter {
                checked
            } else {
                fixture.store.intrinsic_bootstrap().unwrap().never_type
            };
            assert_eq!(fixture.declared_alias("Result"), expected);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), expected);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }

        let mut uncertain = Fixture::new(concat!(
            "type Extract<T, U> = T extends U ? T : never; ",
            "type Result<Value extends string> = Extract<Value, string>;",
        ));
        let unresolved = uncertain.declared_alias("Result");
        assert!(matches!(
            uncertain
                .store
                .type_payload(unresolved)
                .map(TypeRecord::data),
            Some(TypeData::Conditional(_))
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Alias resolution covers primitive and literal union proofs.
    fn constrained_conditional_alias_type_nodes_reduce_bounded_disjoint_primitive_unions() {
        for (source, preserves_parameter) in [
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string | bigint> = ",
                    "Extract<Value, number | symbol>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends string | bigint> = ",
                    "Exclude<Value, number | symbol>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends 'a' | 'b'> = ",
                    "Extract<Value, 'c' | 'd'>;",
                ),
                false,
            ),
            (
                concat!(
                    "type Exclude<T, U> = T extends U ? never : T; ",
                    "type Result<Value extends 'a' | 'b'> = ",
                    "Exclude<Value, 'c' | 'd'>;",
                ),
                true,
            ),
            (
                concat!(
                    "type Extract<T, U> = T extends U ? T : never; ",
                    "type Result<Value extends string | bigint, ",
                    "Bound extends number | symbol> = Extract<Value, Bound>;",
                ),
                false,
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            let expected = if preserves_parameter {
                checked
            } else {
                fixture.store.intrinsic_bootstrap().unwrap().never_type
            };
            assert_eq!(fixture.declared_alias("Result"), expected);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), expected);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }

        let mut uncertain = Fixture::new(concat!(
            "type Extract<T, U> = T extends U ? T : never; ",
            "type Result<Value extends string | number> = ",
            "Extract<Value, number | symbol>;",
        ));
        let checked = uncertain.type_parameter("Value");
        let unresolved = uncertain.declared_alias("Result");
        let TypeData::Conditional(data) = uncertain.store.type_payload(unresolved).unwrap().data()
        else {
            panic!("overlapping primitive unions must retain a deferred conditional")
        };
        assert_eq!(data.check_type, checked);
        assert!(data.resolved_true_type.is_none());
        assert!(data.resolved_false_type.is_none());

        let warm = (
            uncertain.store.type_len(),
            uncertain.store.conditional_root_len(),
            uncertain.store.mapper_len(),
            uncertain.store.checker_link_allocated_lengths(),
        );
        assert_eq!(uncertain.declared_alias("Result"), unresolved);
        assert_eq!(
            (
                uncertain.store.type_len(),
                uncertain.store.conditional_root_len(),
                uncertain.store.mapper_len(),
                uncertain.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn nontrivial_conditional_reference_branches_remain_deferred() {
        let mut fixture = Fixture::new(concat!(
            "type OnlyText<Input extends string> = Input; ",
            "type Select<T, U> = T extends U ? OnlyText<number> : T; ",
            "type Result<Value> = Select<Value, never>;",
        ));
        let checked = fixture.type_parameter("Value");
        let result = fixture.declared_alias("Result");
        let TypeData::Conditional(data) = fixture.store.type_payload(result).unwrap().data() else {
            panic!("an unproven conditional branch must remain deferred")
        };
        assert_eq!(data.check_type, checked);
        assert!(data.resolved_true_type.is_none());
        assert!(data.resolved_false_type.is_none());
    }

    #[test]
    fn trivial_conditional_keyof_instantiations_preserve_index_identity() {
        for source in [
            concat!(
                "type Exclude<T, U> = T extends U ? never : T; ",
                "type Result<Value> = Exclude<keyof Value, never>;",
            ),
            concat!(
                "type Extract<T, U> = T extends U ? T : never; ",
                "type Result<Value> = Extract<keyof Value, keyof Value>;",
            ),
            concat!(
                "type Select<Check, Bound, WhenTrue, WhenFalse> = ",
                "Check extends Bound ? WhenTrue : WhenFalse; ",
                "type Result<Value> = Select<keyof Value, never, never, keyof Value>;",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let checked = fixture.type_parameter("Value");
            let result = fixture.declared_alias("Result");
            let TypeData::Index(index) = fixture.store.type_payload(result).unwrap().data() else {
                panic!("the conditional must preserve the generic keyof identity")
            };
            assert_eq!(index.target, checked);

            let warm = (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(fixture.declared_alias("Result"), result);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn trivial_conditional_instantiation_rejects_invalid_root_cache_state() {
        let mut fixture = Fixture::new(concat!(
            "type Exclude<T, U> = T extends U ? never : T; ",
            "type Caller<Value> = Value;",
        ));
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bound = fixture.type_parameter("U");
        let checked = fixture.type_parameter("Value");
        let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
        let branch_types = branches(never, parameter);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: bound,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: Some(&[parameter, bound]),
                alias: None,
            },
            None,
        )
        .unwrap();
        let root = match fixture.store.type_payload(conditional).unwrap().data() {
            TypeData::Conditional(data) => data.root,
            _ => panic!("the generic declaration must retain its conditional root"),
        };
        let valid_cache = fixture
            .store
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone();
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, TypeCacheState::Unallocated,)
        );
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, never],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Err(ConditionalTypeError::InvalidInstantiationCache(root)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            before,
        );
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, valid_cache)
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[checked, never],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(checked),
        );
    }

    #[test]
    fn any_joins_both_branches_except_against_any_or_unknown() {
        let mut fixture = Fixture::new("type Result = any extends string ? number : boolean;");
        let node = fixture.conditional();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (any, string, number, boolean) = (
            bootstrap.any_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let result = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: any,
                extends_type: string,
                branches: branches(number, boolean),
                infer_type_parameters: &[],
                outer_type_parameters: None,
                alias: None,
            },
            None,
        )
        .unwrap();
        let expected = canonical_anonymous_union(&mut fixture.store, &[number, boolean]).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn naked_any_uses_both_branches_but_tuple_wrapped_any_uses_only_the_true_branch() {
        let mut naked = Fixture::new("type T = any extends number ? 1 : 0;");
        let naked_node = naked.conditional();
        let bootstrap = naked.store.intrinsic_bootstrap().unwrap();
        let (any, number) = (bootstrap.any_type, bootstrap.number_type);
        let one = naked
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let zero = naked
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let naked_result = get_type_from_conditional_type(
            &mut naked.store,
            ConditionalTypeRequest {
                node: naked_node,
                check_type: any,
                extends_type: number,
                branches: branches(one, zero),
                infer_type_parameters: &[],
                outer_type_parameters: None,
                alias: None,
            },
            None,
        )
        .unwrap();
        let TypeData::Union(union) = naked.store.type_payload(naked_result).unwrap().data() else {
            panic!("a naked any conditional must retain both numeric branches")
        };
        assert!(union.union.types.contains(&one));
        assert!(union.union.types.contains(&zero));

        let mut wrapped = Fixture::new("type U = [any] extends [number] ? 1 : 0;");
        let wrapped_node = wrapped.conditional();
        let bootstrap = wrapped.store.intrinsic_bootstrap().unwrap();
        let (any, number) = (bootstrap.any_type, bootstrap.number_type);
        let one = wrapped
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let zero = wrapped
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let required = wrapped
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let check = wrapped
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[any], &[required], false))
            .unwrap();
        let extends = wrapped
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number],
                &[required],
                false,
            ))
            .unwrap();
        assert_eq!(
            conditional_check_is_assignable(&mut wrapped.store, check, extends, None),
            Ok(true)
        );
        assert_eq!(
            get_type_from_conditional_type(
                &mut wrapped.store,
                ConditionalTypeRequest {
                    node: wrapped_node,
                    check_type: check,
                    extends_type: extends,
                    branches: branches(one, zero),
                    infer_type_parameters: &[],
                    outer_type_parameters: None,
                    alias: None,
                },
                None,
            ),
            Ok(one)
        );
    }

    #[test]
    fn naked_infer_parameters_retain_candidates_and_respect_constraints() {
        let mut fixture = Fixture::new("type Result<T> = T extends infer U ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        assert!(fixture.store.set_type_parameter_resolution(
            inferred,
            Some(string),
            None,
            None,
            None,
        ));
        let branch_types = branches(inferred, never);
        let declared = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: inferred,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();

        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(string)
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[number],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(never)
        );
    }

    #[test]
    fn conditional_keys_preserve_alias_and_constraint_dimensions() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let parameter = fixture.type_parameter("T");
        let ordinary = conditional_type_key(&mut fixture.store, &[parameter], None, false, None)
            .expect("ordinary cache key");
        let constraint = conditional_type_key(&mut fixture.store, &[parameter], None, true, None)
            .expect("constraint cache key");
        assert_ne!(ordinary, constraint);
    }

    fn conditional_allocation_counts(
        store: &CanonicalTypeMapperStore,
    ) -> (usize, usize, usize, usize, (usize, usize)) {
        (
            store.type_len(),
            store.conditional_root_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.conditional_production_lengths(),
        )
    }

    fn query_capture_node(
        fixture: &mut Fixture,
        node: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &fixture.bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let result = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_from_type_node(node);
        assert!(diagnostics.is_empty());
        result
    }

    #[test]
    fn conditional_source_captures_keep_absent_and_filtered_empty_root_caches_distinct() {
        for reverse in [false, true] {
            let mut fixture = Fixture::new(concat!(
                "type Empty<T> = { [K in keyof T]: string extends number ? 0 : 1 }; ",
                "type Plain = string extends number ? 0 : 1;",
            ));
            let mut nodes = fixture
                .parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    (record.kind == SyntaxKind::ConditionalType).then_some((
                        record.range.start,
                        NodeRef::new(fixture.parsed.arena.id(), fixture.file, id),
                    ))
                })
                .collect::<Vec<_>>();
            nodes.sort_unstable();
            let [(_, empty), (_, plain)] = nodes.as_slice() else {
                panic!("two source conditionals");
            };
            let (empty, plain) = (*empty, *plain);
            let order = if reverse {
                [plain, empty]
            } else {
                [empty, plain]
            };
            for node in order {
                query_capture_node(&mut fixture, node).unwrap();
            }
            let empty_proof = fixture
                .store
                .conditional_query_production(ConditionalQueryKey::Node(empty))
                .unwrap()
                .clone();
            let plain_proof = fixture
                .store
                .conditional_query_production(ConditionalQueryKey::Node(plain))
                .unwrap()
                .clone();
            assert_eq!(
                empty_proof.definition.outer_type_parameters,
                Some(Vec::new())
            );
            assert_eq!(plain_proof.definition.outer_type_parameters, None);
            let root = fixture.store.conditional_root(empty_proof.root()).unwrap();
            assert_eq!(root.outer_type_parameters(), Some([].as_slice()));
            let TypeCacheState::Allocated(cache) = root.instantiations() else {
                panic!("filtered captures keep the identity cache");
            };
            assert_eq!(cache.len(), 1);
            assert_eq!(
                cache.get(&conditional_type_key_parts(&[], None, false)),
                Some(&empty_proof.result)
            );
            assert_eq!(
                fixture
                    .store
                    .conditional_root(plain_proof.root())
                    .unwrap()
                    .instantiations(),
                &TypeCacheState::Unallocated
            );
            let warm = conditional_allocation_counts(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    query_capture_node(&mut fixture, empty),
                    Ok(empty_proof.result)
                );
                assert_eq!(
                    query_capture_node(&mut fixture, plain),
                    Ok(plain_proof.result)
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), warm);
                assert_eq!(
                    validate_conditional_source_captures(&fixture.store, empty, Some(&[]), &[]),
                    Ok(())
                );
                assert_eq!(
                    validate_conditional_source_captures(&fixture.store, plain, None, &[]),
                    Ok(())
                );
                assert_eq!(
                    validate_conditional_source_captures(&fixture.store, empty, None, &[]),
                    Err(ConditionalTypeError::InvalidTypeNodeCache(empty))
                );
                assert_eq!(
                    validate_conditional_source_captures(&fixture.store, plain, Some(&[]), &[]),
                    Err(ConditionalTypeError::InvalidTypeNodeCache(plain))
                );
            }
        }
    }

    #[test]
    fn conditional_source_captures_reject_outer_parameter_node_links_before_publication() {
        for warm in [false, true] {
            let mut fixture = Fixture::new(
                "type Empty<T> = { [K in keyof T]: string extends number ? boolean : string };",
            );
            let node = fixture.conditional();
            if warm {
                query_capture_node(&mut fixture, node).unwrap();
            }
            assert!(fixture.store.ensure_type_node_links(node));
            let original = fixture.store.type_node_links(node).unwrap().clone();
            let proof = fixture
                .store
                .conditional_query_production(ConditionalQueryKey::Node(node))
                .cloned();
            let mut poison = original.clone();
            poison.outer_type_parameters = Some(Vec::new());
            assert!(fixture.store.set_type_node_links(node, poison.clone()));
            let before = conditional_allocation_counts(&fixture.store);
            let links = fixture.store.checker_link_allocated_lengths();
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, boolean) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            );
            for _ in 0..2 {
                assert_eq!(
                    validate_conditional_source_captures(&fixture.store, node, Some(&[]), &[]),
                    Err(ConditionalTypeError::InvalidTypeNodeCache(node))
                );
                assert_eq!(
                    get_type_from_conditional_type(
                        &mut fixture.store,
                        ConditionalTypeRequest {
                            node,
                            check_type: string,
                            extends_type: number,
                            branches: branches(boolean, string),
                            infer_type_parameters: &[],
                            outer_type_parameters: Some(&[]),
                            alias: None,
                        },
                        None
                    ),
                    Err(ConditionalTypeError::InvalidTypeNodeCache(node))
                );
                assert_eq!(
                    query_capture_node(&mut fixture, node),
                    Err(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidTypeReference(node),
                    ))
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(fixture.store.checker_link_allocated_lengths(), links);
                assert_eq!(fixture.store.type_node_links(node), Some(&poison));
                assert_eq!(
                    fixture
                        .store
                        .conditional_query_production(ConditionalQueryKey::Node(node)),
                    proof.as_ref()
                );
            }
            assert!(fixture.store.set_type_node_links(node, original));
            assert_eq!(query_capture_node(&mut fixture, node), Ok(string));
            assert!(
                fixture
                    .store
                    .type_node_links(node)
                    .unwrap()
                    .outer_type_parameters
                    .is_none()
            );
            let restored = conditional_allocation_counts(&fixture.store);
            assert_eq!(query_capture_node(&mut fixture, node), Ok(string));
            assert_eq!(conditional_allocation_counts(&fixture.store), restored);
        }
    }

    #[test]
    fn conditional_source_captures_reject_and_restore_an_empty_root_cache() {
        let mut fixture =
            Fixture::new("type Empty<T> = { [K in keyof T]: string extends number ? 0 : 1 };");
        let node = fixture.conditional();
        let result = query_capture_node(&mut fixture, node).unwrap();
        let proof = fixture
            .store
            .conditional_query_production(ConditionalQueryKey::Node(node))
            .unwrap()
            .clone();
        let original = fixture
            .store
            .conditional_root(proof.root())
            .unwrap()
            .instantiations()
            .clone();
        assert!(matches!(original, TypeCacheState::Allocated(_)));
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(proof.root(), TypeCacheState::Unallocated)
        );
        let before = conditional_allocation_counts(&fixture.store);
        for _ in 0..2 {
            assert_eq!(
                validate_conditional_source_captures(&fixture.store, node, Some(&[]), &[]),
                Err(ConditionalTypeError::InvalidInstantiationCache(
                    proof.root()
                ))
            );
            assert_eq!(
                query_capture_node(&mut fixture, node),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::InvalidTypeReference(node),
                ))
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
            assert_eq!(
                fixture
                    .store
                    .conditional_query_production(ConditionalQueryKey::Node(node)),
                Some(&proof)
            );
            assert_eq!(
                fixture.store.type_node_links(node).unwrap().resolved_type,
                Some(result)
            );
        }
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(proof.root(), original)
        );
        assert_eq!(query_capture_node(&mut fixture, node), Ok(result));
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve both real parameter caches through failure and replay.
    fn conditional_source_captures_revalidate_enclosing_parameter_caches_and_order() {
        for corrupt_symbol in [false, true] {
            let mut fixture = Fixture::new(concat!(
                "function outer<Outer, Unused>() { ",
                "type Select<Own> = Own extends string ? Outer : boolean; }",
            ));
            let source = fixture.declared_alias("Select");
            let outer = fixture.type_parameter("Outer");
            let unused = fixture.type_parameter("Unused");
            let own = fixture.type_parameter("Own");
            let parameters = [outer, unused, own];
            let symbols = parameters.map(|parameter| {
                cached_ordinary_type_parameter_owner(&fixture.store, parameter).unwrap()
            });
            let proof = validated_conditional_production(&fixture.store, source, None)
                .unwrap()
                .clone();
            assert_eq!(
                proof.definition.outer_type_parameters.as_deref(),
                Some(parameters.as_slice())
            );
            assert_eq!(
                proof.definition.alias.as_ref().unwrap().type_arguments,
                [own]
            );
            let node = proof.definition.node;
            let declaration = fixture
                .store
                .symbol(symbols[0])
                .unwrap()
                .declarations()
                .unwrap()[0];
            assert!(fixture.store.ensure_type_node_links(declaration));
            assert!(fixture.store.ensure_symbol_node_links(declaration));
            let original_type = fixture.store.type_node_links(declaration).unwrap().clone();
            let original_symbol = fixture
                .store
                .symbol_node_links(declaration)
                .unwrap()
                .clone();
            let before = conditional_allocation_counts(&fixture.store);
            assert_eq!(
                validate_conditional_source_captures(&fixture.store, node, Some(&symbols), &[]),
                Ok(())
            );
            assert_eq!(
                validate_conditional_source_captures(
                    &fixture.store,
                    node,
                    Some(&[symbols[1], symbols[0], symbols[2]]),
                    &[]
                ),
                Err(ConditionalTypeError::InvalidTypeNodeCache(node))
            );
            if corrupt_symbol {
                let mut links = original_symbol.clone();
                links.resolved_symbol = Some(symbols[1]);
                assert!(fixture.store.set_symbol_node_links(declaration, links));
            } else {
                let mut links = original_type.clone();
                links.resolved_type = Some(unused);
                assert!(fixture.store.set_type_node_links(declaration, links));
            }
            let poisoned_type = fixture.store.type_node_links(declaration).unwrap().clone();
            let poisoned_symbol = fixture
                .store
                .symbol_node_links(declaration)
                .unwrap()
                .clone();
            for _ in 0..2 {
                assert_eq!(
                    fixture.try_declared_alias("Select"),
                    Err(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidTypeReference(declaration),
                    ))
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(
                    fixture.store.type_node_links(declaration),
                    Some(&poisoned_type)
                );
                assert_eq!(
                    fixture.store.symbol_node_links(declaration),
                    Some(&poisoned_symbol)
                );
                assert_eq!(
                    validated_conditional_production(&fixture.store, source, None),
                    Ok(&proof)
                );
            }
            assert!(
                fixture
                    .store
                    .set_type_node_links(declaration, original_type)
            );
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(declaration, original_symbol)
            );
            for _ in 0..2 {
                assert_eq!(fixture.declared_alias("Select"), source);
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
            }
        }
    }

    fn assert_uncaptured_conditional_remap_is_unsupported(
        fixture: &mut Fixture,
        source: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
    ) {
        let original = conditional_snapshot(&fixture.store, source, None).unwrap();
        assert!(original.resolved_true_type.is_none());
        assert!(original.resolved_false_type.is_none());
        assert!(original.resolved_inferred_true_type.is_none());
        let cache = fixture
            .store
            .conditional_root(original.root)
            .unwrap()
            .instantiations()
            .clone();
        let nodes = fixture
            .parsed
            .arena
            .iter()
            .map(|(node, _)| NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            .collect::<Vec<_>>();
        let links = |store: &CanonicalTypeMapperStore| {
            nodes
                .iter()
                .map(|node| {
                    (
                        store.type_node_links(*node).cloned(),
                        store.symbol_node_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = conditional_allocation_counts(&fixture.store);
        let original_links = links(&fixture.store);
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut session = InstantiationSession::new_recovering(
            &fixture.store,
            InstantiationLimits::default(),
            error_type,
        )
        .unwrap();
        for _ in 0..2 {
            assert_eq!(
                conditional_remap_projection(&fixture.store, source),
                Err(ConditionalTypeError::Instantiation(
                    InstantiationError::UnsupportedType(source)
                ))
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    parameters,
                    arguments,
                    None,
                    None,
                ),
                Err(InstantiationError::UnsupportedType(source))
            );
            assert_eq!(
                instantiate_type_with_vector_and_session(
                    &mut fixture.store,
                    source,
                    parameters,
                    arguments,
                    None,
                    &mut session,
                ),
                Err(InstantiationError::UnsupportedType(source))
            );
            assert_eq!(session.query_count(), 0);
            assert_eq!(session.limit_event_count(), 0);
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
            assert_eq!(
                conditional_snapshot(&fixture.store, source, None).unwrap(),
                original
            );
            assert_eq!(
                fixture
                    .store
                    .conditional_root(original.root)
                    .unwrap()
                    .instantiations(),
                &cache
            );
            assert_eq!(links(&fixture.store), original_links);
        }
    }

    #[test]
    fn deferred_conditional_remap_rejects_inline_roots_with_complete_mapped_captures() {
        let mut fixture = Fixture::new(concat!(
            "interface Validator<Value> {} ",
            "type IsOptional<Value> = Value extends undefined ? true : false; ",
            "type RequiredKeys<Value> = { ",
            "[Key in keyof Value]: Value[Key] extends Validator<infer Item> ",
            "? IsOptional<Item> extends true ? never : Key : never ",
            "}[keyof Value];",
        ));
        let declared = fixture.declared_alias("RequiredKeys");
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ConditionalTypeNode(conditional) = &record.data else {
                    return None;
                };
                (fixture.parsed.arena.get(conditional.check_type)?.kind
                    == SyntaxKind::IndexedAccessType)
                    .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .unwrap();
        let source = fixture
            .store
            .type_node_links(node)
            .unwrap()
            .resolved_type
            .unwrap();
        let proof = validated_conditional_production(&fixture.store, source, None).unwrap();
        assert_eq!(proof.definition.node, node);
        assert!(proof.definition.alias.is_none());
        let TypeData::IndexedAccess(indexed) = fixture
            .store
            .type_payload(proof.definition.check_type)
            .unwrap()
            .data()
        else {
            unreachable!()
        };
        let parameters = [indexed.object_type, indexed.index_type];
        assert_eq!(
            proof.definition.outer_type_parameters.as_deref(),
            Some(parameters.as_slice())
        );
        let target = fixture.type_parameter("Value");
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_ne!(parameters[0], target);
        assert_ne!(parameters[1], string);
        assert_uncaptured_conditional_remap_is_unsupported(
            &mut fixture,
            source,
            &parameters,
            &[target, string],
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("RequiredKeys"), declared);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn deferred_conditional_remap_rejects_local_aliases_with_complete_outer_captures() {
        let mut fixture = Fixture::new(concat!(
            "function outer<Outer>() { ",
            "type Select<Own> = Own extends string ? Outer : boolean; ",
            "}",
        ));
        let source = fixture.declared_alias("Select");
        let own = fixture.type_parameter("Own");
        let outer = fixture.type_parameter("Outer");
        let proof = validated_conditional_production(&fixture.store, source, None).unwrap();
        assert_eq!(
            proof.definition.outer_type_parameters.as_deref(),
            Some([outer, own].as_slice())
        );
        assert_eq!(
            proof.definition.alias.as_ref().unwrap().type_arguments,
            [own]
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_uncaptured_conditional_remap_is_unsupported(
            &mut fixture,
            source,
            &[outer],
            &[number],
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Select"), source);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check both formal-node caches against one real warm remap and restore it.
    fn deferred_conditional_remap_keeps_parameter_node_cache_errors_typed() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for corrupt_symbol in [false, true] {
            let mut fixture = Fixture::new(concat!(
                "type Select<Value> = Value extends string ? number : boolean; ",
                "type Next<Other> = Other;",
            ));
            let source = fixture.declared_alias("Select");
            let owner = fixture.alias_symbol("Select");
            let other_owner = fixture.alias_symbol("Next");
            let parameter = fixture.type_parameter("Value");
            let argument = fixture.type_parameter("Other");
            let parameter_owner =
                cached_ordinary_type_parameter_owner(&fixture.store, parameter).unwrap();
            let parameter_node = fixture
                .store
                .symbol(parameter_owner)
                .unwrap()
                .declarations()
                .unwrap()[0];
            assert!(fixture.store.ensure_type_node_links(parameter_node));
            assert!(fixture.store.ensure_symbol_node_links(parameter_node));
            let original_types = fixture
                .store
                .type_node_links(parameter_node)
                .unwrap()
                .clone();
            let original_symbols = fixture
                .store
                .symbol_node_links(parameter_node)
                .unwrap()
                .clone();
            let result =
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument])
                    .unwrap();
            let original = conditional_snapshot(&fixture.store, source, None).unwrap();
            let mapped = conditional_snapshot(&fixture.store, result, None).unwrap();
            let cache = fixture
                .store
                .conditional_root(original.root)
                .unwrap()
                .instantiations()
                .clone();
            let mut types = original_types.clone();
            let mut symbols = original_symbols.clone();
            if corrupt_symbol {
                symbols.resolved_symbol = Some(other_owner);
            } else {
                types.resolved_type =
                    Some(fixture.store.intrinsic_bootstrap().unwrap().number_type);
            }
            assert!(
                fixture
                    .store
                    .set_type_node_links(parameter_node, types.clone())
            );
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(parameter_node, symbols.clone())
            );
            let before = conditional_allocation_counts(&fixture.store);
            let mut session = InstantiationSession::new(InstantiationLimits::default());
            for _ in 0..2 {
                assert_eq!(
                    conditional_remap_projection(&fixture.store, source),
                    Err(ConditionalTypeError::InvalidAliasSymbol(owner))
                );
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        None,
                    ),
                    Err(InstantiationError::InvalidType(source))
                );
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        &mut fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        &mut session,
                    ),
                    Err(InstantiationError::InvalidType(source))
                );
                assert_eq!(session.query_count(), 0);
                assert_eq!(session.limit_event_count(), 0);
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(fixture.store.type_node_links(parameter_node), Some(&types));
                assert_eq!(
                    fixture.store.symbol_node_links(parameter_node),
                    Some(&symbols)
                );
                assert_eq!(
                    conditional_snapshot(&fixture.store, source, None).unwrap(),
                    original
                );
                assert_eq!(
                    conditional_snapshot(&fixture.store, result, None).unwrap(),
                    mapped
                );
                assert_eq!(
                    fixture
                        .store
                        .conditional_root(original.root)
                        .unwrap()
                        .instantiations(),
                    &cache
                );
            }
            assert!(
                fixture
                    .store
                    .set_type_node_links(parameter_node, original_types)
            );
            assert!(
                fixture
                    .store
                    .set_symbol_node_links(parameter_node, original_symbols)
            );
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    &[parameter],
                    &[argument],
                    None,
                    None,
                ),
                Ok(Some(result))
            );
            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument]),
                Ok(result)
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep source order, mapper order, and later branch demand together.
    fn deferred_conditional_remap_keeps_source_order_and_lazy_branch_caches() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for declaration_first in [false, true] {
            let mut fixture = Fixture::new(concat!(
                "type Select<Check, Value> = Check extends string ? Value : boolean; ",
                "type Forward<Left, Right> = Select<Right, Left>; ",
                "type Next<NewLeft, NewRight> = NewLeft;",
            ));
            if declaration_first {
                fixture.declared_alias("Select");
            }
            let source = fixture.declared_alias("Forward");
            let left = fixture.type_parameter("Left");
            let right = fixture.type_parameter("Right");
            let new_left = fixture.type_parameter("NewLeft");
            let new_right = fixture.type_parameter("NewRight");
            let value = fixture.type_parameter("Value");
            let owner = fixture.alias_symbol("Forward");
            let projection = conditional_remap_projection(&fixture.store, source).unwrap();
            assert_eq!(projection.arguments(), &[right, left]);
            assert_eq!(
                projection.alias(),
                Some(ConditionalAliasIdentity {
                    symbol: owner,
                    type_arguments: &[left, right],
                })
            );
            let source_data = conditional_snapshot(&fixture.store, source, None).unwrap();
            let source_alias = fixture.store.type_alias_links(owner).cloned();
            let nodes = fixture
                .parsed
                .arena
                .iter()
                .map(|(node, _)| NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
                .collect::<Vec<_>>();
            let node_links = |store: &CanonicalTypeMapperStore| {
                nodes
                    .iter()
                    .map(|node| store.type_node_links(*node).cloned())
                    .collect::<Vec<_>>()
            };
            let original_links = node_links(&fixture.store);
            assert_eq!(
                cached_instantiation_with_vector(
                    &fixture.store,
                    source,
                    &[left, right],
                    &[new_left, new_right],
                    None,
                    None,
                ),
                Ok(None)
            );
            let result = instantiate_type_with_vector(
                &mut fixture.store,
                source,
                &[left, right],
                &[new_left, new_right],
            )
            .unwrap();
            let mapped = conditional_remap_projection(&fixture.store, result).unwrap();
            assert_eq!(mapped.arguments(), &[new_right, new_left]);
            assert_eq!(mapped.parameters(), projection.parameters());
            assert_eq!(
                mapped.production.alias_reference,
                projection.production.alias_reference
            );
            assert_eq!(
                mapped.alias(),
                Some(ConditionalAliasIdentity {
                    symbol: owner,
                    type_arguments: &[new_left, new_right],
                })
            );
            let result_data = conditional_snapshot(&fixture.store, result, None).unwrap();
            assert_eq!(result_data.root, source_data.root);
            assert_eq!(result_data.check_type, new_right);
            assert_eq!(result_data.extends_type, source_data.extends_type);
            assert!(result_data.resolved_true_type.is_none());
            assert!(result_data.resolved_false_type.is_none());
            assert!(result_data.resolved_inferred_true_type.is_none());
            assert_eq!(
                conditional_snapshot(&fixture.store, source, None).unwrap(),
                source_data
            );
            assert_eq!(node_links(&fixture.store), original_links);
            assert_eq!(fixture.store.type_alias_links(owner).cloned(), source_alias);
            let warm = conditional_allocation_counts(&fixture.store);
            for _ in 0..2 {
                assert_eq!(fixture.declared_alias("Forward"), source);
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[left, right],
                        &[new_left, new_right],
                        None,
                        None,
                    ),
                    Ok(Some(result))
                );
                assert_eq!(
                    instantiate_type_with_vector(
                        &mut fixture.store,
                        source,
                        &[left, right],
                        &[new_left, new_right],
                    ),
                    Ok(result)
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), warm);
                assert_eq!(node_links(&fixture.store), original_links);
            }

            // A later legitimate source branch demand must not invalidate the
            // remap proof. The raw branch is Value, not a cached mapped result.
            let boolean = fixture.store.intrinsic_bootstrap().unwrap().boolean_type;
            assert_eq!(
                get_true_type_from_conditional_type(
                    &mut fixture.store,
                    result,
                    branches(value, boolean),
                    None,
                    None,
                ),
                Ok(new_left)
            );
            assert_eq!(
                get_false_type_from_conditional_type(
                    &mut fixture.store,
                    result,
                    branches(value, boolean),
                    None,
                    None,
                ),
                Ok(boolean)
            );
            let warm = conditional_allocation_counts(&fixture.store);
            assert_eq!(
                instantiate_type_with_vector(
                    &mut fixture.store,
                    source,
                    &[left, right],
                    &[new_left, new_right],
                ),
                Ok(result)
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), warm);
            assert_eq!(
                conditional_snapshot(&fixture.store, source, None).unwrap(),
                source_data
            );
        }
    }

    #[test]
    fn deferred_conditional_remap_does_not_use_a_warm_concrete_result() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for concrete_first in [false, true] {
            let mut fixture =
                Fixture::new("type Select<Value> = Value extends string ? number : boolean;");
            let source = fixture.declared_alias("Select");
            let parameter = fixture.type_parameter("Value");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, boolean) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            );
            if concrete_first {
                assert_eq!(
                    get_conditional_type_instantiation(
                        &mut fixture.store,
                        ConditionalTypeInstantiation {
                            conditional_type: source,
                            type_arguments: &[string],
                            branches: branches(number, boolean),
                            alias: None,
                            for_constraint: false,
                        },
                        None,
                        None,
                    ),
                    Ok(number)
                );
            }
            let root = conditional_snapshot(&fixture.store, source, None)
                .unwrap()
                .root;
            let root_cache = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            let before = conditional_allocation_counts(&fixture.store);
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[parameter],
                        &[string],
                        None,
                        None,
                    ),
                    Err(InstantiationError::UnsupportedType(source))
                );
                assert_eq!(
                    instantiate_type_with_vector(
                        &mut fixture.store,
                        source,
                        &[parameter],
                        &[string]
                    ),
                    Err(InstantiationError::UnsupportedType(source))
                );
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations(),
                    &root_cache
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each corruption is restored before replaying the same source request.
    fn deferred_conditional_remap_rejects_and_restores_source_and_result_caches() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        for corruption in 0..10 {
            let mut fixture = Fixture::new(concat!(
                "type Select<Value> = Value extends string ? number : boolean; ",
                "type Forward<Other> = Select<Other>; type Next<After> = After;",
            ));
            let source = fixture.declared_alias("Forward");
            let parameter = fixture.type_parameter("Other");
            let argument = fixture.type_parameter("After");
            let result =
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument])
                    .unwrap();
            let projection = conditional_remap_projection(&fixture.store, source).unwrap();
            let root = projection.production.definition.root;
            let source_owner = projection.alias().unwrap().symbol;
            let root_owner = projection
                .production
                .definition
                .alias
                .as_ref()
                .unwrap()
                .symbol;
            let original_source_alias_links = fixture
                .store
                .type_alias_links(source_owner)
                .unwrap()
                .clone();
            let original_root_alias_links =
                fixture.store.type_alias_links(root_owner).unwrap().clone();
            let key = remap_cache_key(
                &fixture.store,
                &projection,
                &[argument],
                Some(ConditionalAliasIdentity {
                    symbol: projection.alias().unwrap().symbol,
                    type_arguments: &[argument],
                }),
            )
            .unwrap();
            let original_cache = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            let original_root_alias = fixture.store.conditional_root(root).unwrap().alias();
            let result_data = conditional_snapshot(&fixture.store, result, None).unwrap();
            let alias = fixture.store.type_payload(result).unwrap().alias().unwrap();
            let original_alias_arguments = fixture
                .store
                .type_alias(alias)
                .unwrap()
                .type_arguments()
                .map(<[TypeId]>::to_vec);
            let reference = projection.production.alias_reference.unwrap();
            let original_reference_links =
                fixture.store.type_node_links(reference).unwrap().clone();
            let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
            match corruption {
                0 | 1 => {
                    let TypeCacheState::Allocated(mut cache) = original_cache.clone() else {
                        unreachable!()
                    };
                    assert_eq!(cache.remove(&key), Some(result));
                    if corruption == 1 {
                        cache.insert(key, source);
                    }
                    assert!(fixture.store.set_conditional_root_instantiations(
                        root,
                        TypeCacheState::Allocated(cache)
                    ));
                }
                2 => {
                    assert!(fixture.store.set_conditional_resolution(
                        result, None, None, None, None, None, None, None,
                    ));
                }
                3 => assert!(
                    fixture
                        .store
                        .set_type_alias_arguments(alias, Some(vec![number]))
                ),
                4 => assert!(fixture.store.set_conditional_root_alias(root, None)),
                5 => {
                    let mut links = original_reference_links.clone();
                    links.resolved_type = Some(number);
                    assert!(fixture.store.set_type_node_links(reference, links));
                }
                6..=8 => {
                    let mut links = original_source_alias_links.clone();
                    match corruption {
                        6 => links.declared_type = Some(number),
                        7 => links.type_parameters = Some(vec![argument]),
                        8 => {
                            let key = super::super::declared::type_list_key(&[parameter]);
                            assert_eq!(
                                links.instantiations.as_mut().unwrap().insert(key, number),
                                Some(source)
                            );
                        }
                        _ => unreachable!(),
                    }
                    assert!(fixture.store.set_type_alias_links(source_owner, links));
                }
                9 => {
                    let mut links = original_root_alias_links.clone();
                    links.declared_type = Some(number);
                    assert!(fixture.store.set_type_alias_links(root_owner, links));
                }
                _ => unreachable!(),
            }
            let before = conditional_allocation_counts(&fixture.store);
            let link_counts = fixture.store.checker_link_allocated_lengths();
            let poisoned_source_alias_links = fixture.store.type_alias_links(source_owner).cloned();
            let poisoned_root_alias_links = fixture.store.type_alias_links(root_owner).cloned();
            let poisoned_cache = fixture
                .store
                .conditional_root(root)
                .unwrap()
                .instantiations()
                .clone();
            for _ in 0..2 {
                assert_eq!(
                    cached_instantiation_with_vector(
                        &fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        None,
                    ),
                    Err(InstantiationError::InvalidType(source)),
                    "corruption {corruption}"
                );
                let mut session = InstantiationSession::new(InstantiationLimits::default());
                let mark = session.limit_event_mark();
                assert_eq!(
                    instantiate_type_with_vector_and_session(
                        &mut fixture.store,
                        source,
                        &[parameter],
                        &[argument],
                        None,
                        &mut session,
                    ),
                    Err(InstantiationError::InvalidType(source)),
                    "corruption {corruption}"
                );
                assert_eq!(session.limit_event_mark(), mark);
                assert_eq!(conditional_allocation_counts(&fixture.store), before);
                assert_eq!(fixture.store.checker_link_allocated_lengths(), link_counts);
                assert_eq!(
                    fixture.store.type_alias_links(source_owner).cloned(),
                    poisoned_source_alias_links
                );
                assert_eq!(
                    fixture.store.type_alias_links(root_owner).cloned(),
                    poisoned_root_alias_links
                );
                assert_eq!(
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations(),
                    &poisoned_cache
                );
            }
            assert!(
                fixture
                    .store
                    .set_conditional_root_instantiations(root, original_cache)
            );
            assert!(
                fixture
                    .store
                    .set_conditional_root_alias(root, original_root_alias)
            );
            assert!(
                fixture
                    .store
                    .set_type_alias_arguments(alias, original_alias_arguments)
            );
            assert!(
                fixture
                    .store
                    .set_type_node_links(reference, original_reference_links)
            );
            assert!(
                fixture
                    .store
                    .set_type_alias_links(source_owner, original_source_alias_links)
            );
            assert!(
                fixture
                    .store
                    .set_type_alias_links(root_owner, original_root_alias_links)
            );
            assert!(fixture.store.set_conditional_resolution(
                result,
                result_data.resolved_true_type,
                result_data.resolved_false_type,
                result_data.resolved_inferred_true_type,
                result_data.resolved_default_constraint,
                result_data.resolved_constraint_of_distributive,
                result_data.mapper,
                result_data.combined_mapper,
            ));
            let warm = conditional_allocation_counts(&fixture.store);
            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument]),
                Ok(result)
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), warm);
        }
    }

    #[test]
    fn deferred_conditional_remap_checks_later_alias_publication() {
        use crate::semantic::instantiate::instantiate_type_with_vector;

        let mut fixture = Fixture::new(concat!(
            "type Select<Value> = Value extends string ? number : boolean; ",
            "type Next<Other> = Other;",
        ));
        let node = fixture.conditional();
        let owner = fixture.alias_symbol("Select");
        let parameter = fixture.type_parameter("Value");
        let argument = fixture.type_parameter("Other");
        let source = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&fixture.parsed.arena, &fixture.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let source = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(node)
            .unwrap();
            assert!(diagnostics.is_empty());
            source
        };
        assert!(
            fixture
                .store
                .conditional_query_production(ConditionalQueryKey::AliasDeclaration(owner))
                .is_none()
        );
        assert!(
            fixture
                .store
                .type_alias_links(owner)
                .is_none_or(|links| links.declared_type.is_none())
        );
        let result =
            instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument])
                .unwrap();
        assert_eq!(fixture.declared_alias("Select"), source);
        let links = fixture.store.type_alias_links(owner).unwrap().clone();
        assert_eq!(links.declared_type, Some(source));
        let warm = conditional_allocation_counts(&fixture.store);
        for _ in 0..2 {
            assert_eq!(
                instantiate_type_with_vector(&mut fixture.store, source, &[parameter], &[argument]),
                Ok(result)
            );
            assert_eq!(fixture.store.type_alias_links(owner), Some(&links));
            assert_eq!(conditional_allocation_counts(&fixture.store), warm);
        }
    }

    #[test]
    fn conditional_alias_roots_keep_parentheses_and_unused_local_parameters() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T, Unused> = ((T extends string ? number : boolean)); ",
            "type Reduced = Select<string, never>;",
        ));
        let declared = fixture.declared_alias("Select");
        let parameters = [
            fixture.type_parameter("T"),
            fixture.type_parameter("Unused"),
        ];
        let symbol = fixture.alias_symbol("Select");
        assert_eq!(
            conditional_alias_projection(&fixture.store, declared),
            Ok(Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &parameters
            })),
        );
        let data = conditional_snapshot(&fixture.store, declared, None).unwrap();
        let root = fixture.store.conditional_root(data.root).unwrap();
        assert_eq!(root.outer_type_parameters(), Some(parameters.as_slice()));
        assert_eq!(
            root.alias(),
            fixture.store.type_payload(declared).unwrap().alias()
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Select"), declared);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);

        let aliases = fixture.store.type_alias_len();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(fixture.declared_alias("Reduced"), number);
        assert!(
            fixture
                .store
                .type_payload(number)
                .unwrap()
                .alias()
                .is_none()
        );
        assert_eq!(fixture.store.type_alias_len(), aliases);
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Reduced"), number);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_references_keep_the_requested_owner_and_compose_root_arguments() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T, Unused> = ((T extends string ? number : boolean)); ",
            "type Forward<Value> = Select<Value, never>; ",
            "type Reduced = Forward<string>;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let parameter = fixture.type_parameter("Value");
        let symbol = fixture.alias_symbol("Forward");
        assert_eq!(
            conditional_alias_projection(&fixture.store, forwarded),
            Ok(Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &[parameter]
            })),
        );
        let data = conditional_snapshot(&fixture.store, forwarded, None).unwrap();
        let root = fixture.store.conditional_root(data.root).unwrap();
        let root_alias = stored_alias_identity(&fixture.store, root.alias().unwrap()).unwrap();
        assert_eq!(root_alias.symbol, fixture.alias_symbol("Select"));
        assert_eq!(root_alias.type_arguments.len(), 2);
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(fixture.declared_alias("Reduced"), number);
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Forward"), forwarded);
        assert_eq!(fixture.declared_alias("Reduced"), number);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_reduced_outer_keeps_inner_identity_on_warm_queries() {
        let mut fixture = Fixture::new(concat!(
            "type Inner<T> = T extends string ? number : boolean; ",
            "type Outer<U> = string extends string ? Inner<U> : never; ",
            "type Result = Outer<string>;",
        ));
        let outer = fixture.declared_alias("Outer");
        let parameter = fixture.type_parameter("U");
        assert_eq!(
            conditional_alias_projection(&fixture.store, outer),
            Ok(Some(ConditionalAliasIdentity {
                symbol: fixture.alias_symbol("Inner"),
                type_arguments: &[parameter],
            }))
        );
        let declaration = fixture.alias_declaration("Outer");
        let NodeData::TypeAliasDeclaration(source) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let node = NodeRef::new(declaration.arena, declaration.file, source.type_);
        let alias = conditional_query_alias(&fixture.store, node)
            .unwrap()
            .unwrap();
        assert_eq!(
            fixture.store.type_alias(alias).unwrap().symbol(),
            Some(fixture.alias_symbol("Outer"))
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(fixture.declared_alias("Result"), number);
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Outer"), outer);
        assert_eq!(fixture.declared_alias("Result"), number);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_distribution_retains_the_requested_union_alias() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? 1 : 2; ",
            "type Result = Select<string | number>; type Other = boolean;",
        ));
        let result = fixture.declared_alias("Result");
        let record = fixture.store.type_payload(result).unwrap();
        let TypeData::Union(union) = record.data() else {
            panic!("distribution must preserve both literal results");
        };
        assert_eq!(union.union.types.len(), 2);
        let alias = fixture.store.type_alias(record.alias().unwrap()).unwrap();
        assert_eq!(alias.symbol(), Some(fixture.alias_symbol("Result")));
        assert!(alias.type_arguments().unwrap_or_default().is_empty());
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Result"), result);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);

        let declaration = fixture.alias_declaration("Result");
        let NodeData::TypeAliasDeclaration(source) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let reference = NodeRef::new(declaration.arena, declaration.file, source.type_);
        let other = fixture.alias_symbol("Other");
        let alias = fixture.store.alloc_type_alias(Some(other)).unwrap();
        assert!(fixture.store.set_type_alias(result, Some(alias)));
        let before = conditional_allocation_counts(&fixture.store);
        assert!(validate_conditional_reference_result(&fixture.store, reference, result).is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_projection_rejects_uncached_clones_with_matching_aliases() {
        let mut fixture = Fixture::new("type Select<T> = T extends string ? number : boolean;");
        let original = fixture.declared_alias("Select");
        let data = conditional_snapshot(&fixture.store, original, None).unwrap();
        let original_alias = fixture.store.type_payload(original).unwrap().alias();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        for check in [data.check_type, number] {
            let clone = fixture
                .store
                .alloc_conditional_type(data.root, check, data.extends_type, None, None)
                .unwrap();
            assert!(fixture.store.set_type_alias(clone, original_alias));
            let before = conditional_allocation_counts(&fixture.store);
            assert!(conditional_alias_projection(&fixture.store, clone).is_err());
            assert!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: clone,
                        type_arguments: &[number],
                        branches: branches(number, number),
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None
                )
                .is_err()
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
        }
        let proof = fixture
            .store
            .conditional_type_production(original)
            .unwrap()
            .clone();
        let before = conditional_allocation_counts(&fixture.store);
        assert!(!fixture.store.publish_conditional_type_production(proof));
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_rejects_unexpected_combined_mapper_without_writes() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? T : never; ",
            "type Forward<U> = Select<U>;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let parameter = fixture.type_parameter("U");
        let original = conditional_snapshot(&fixture.store, forwarded, None).unwrap();
        assert!(original.combined_mapper.is_none());
        let root = original.root;
        let checked = fixture.store.conditional_root(root).unwrap().check_type();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (number, never) = (bootstrap.number_type, bootstrap.never_type);
        let unexpected = fixture
            .store
            .new_simple_type_mapper(checked, number)
            .unwrap();
        assert!(fixture.store.set_conditional_resolution(
            forwarded,
            original.resolved_true_type,
            original.resolved_false_type,
            original.resolved_inferred_true_type,
            original.resolved_default_constraint,
            original.resolved_constraint_of_distributive,
            original.mapper,
            Some(unexpected),
        ));
        let forward_symbol = fixture.alias_symbol("Forward");
        let select_symbol = fixture.alias_symbol("Select");
        let snapshot = |store: &CanonicalTypeMapperStore| {
            let TypeData::Conditional(data) = store.type_payload(forwarded).unwrap().data() else {
                panic!("the forwarded type must retain its conditional payload");
            };
            (
                conditional_allocation_counts(store),
                store.checker_link_allocated_lengths(),
                store.type_resolution_len(),
                store.type_resolution_start(),
                data.clone(),
                store
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone(),
                store.type_alias_links(forward_symbol).cloned(),
                store.type_alias_links(select_symbol).cloned(),
            )
        };
        let before = snapshot(&fixture.store);
        assert_eq!(
            conditional_alias_projection(&fixture.store, forwarded),
            Err(ConditionalTypeError::InvalidConditional(forwarded))
        );
        assert_eq!(snapshot(&fixture.store), before);
        assert!(fixture.try_declared_alias("Forward").is_err());
        assert_eq!(snapshot(&fixture.store), before);
        assert_eq!(
            get_inferred_true_type_from_conditional_type(
                &mut fixture.store,
                forwarded,
                branches(checked, never),
                None,
                None,
            ),
            Err(ConditionalTypeError::InvalidConditional(forwarded))
        );
        assert_eq!(snapshot(&fixture.store), before);

        assert!(fixture.store.set_conditional_resolution(
            forwarded,
            original.resolved_true_type,
            original.resolved_false_type,
            original.resolved_inferred_true_type,
            original.resolved_default_constraint,
            original.resolved_constraint_of_distributive,
            original.mapper,
            original.combined_mapper,
        ));
        assert_eq!(fixture.declared_alias("Forward"), forwarded);
        assert_eq!(
            get_inferred_true_type_from_conditional_type(
                &mut fixture.store,
                forwarded,
                branches(checked, never),
                None,
                None,
            ),
            Ok(parameter)
        );
    }

    #[test]
    fn conditional_alias_source_rejects_an_unrelated_owner_and_matching_cache_entry() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Forward<U> = Select<U>; type Other<V> = V;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let parameter = fixture.type_parameter("U");
        let root = conditional_snapshot(&fixture.store, forwarded, None)
            .unwrap()
            .root;
        let other = fixture.alias_symbol("Other");
        let alias = fixture.store.alloc_type_alias(Some(other)).unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![parameter]))
        );
        assert!(fixture.store.set_type_alias(forwarded, Some(alias)));
        let key = conditional_type_key(
            &mut fixture.store,
            &[parameter],
            Some(ConditionalAliasIdentity {
                symbol: other,
                type_arguments: &[parameter],
            }),
            false,
            None,
        )
        .unwrap();
        let TypeCacheState::Allocated(mut cache) = fixture
            .store
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone()
        else {
            unreachable!();
        };
        cache.insert(key, forwarded);
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(conditional_alias_projection(&fixture.store, forwarded).is_err());
        assert!(fixture.try_declared_alias("Forward").is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_source_rejects_swapped_arguments_and_matching_cache_entry() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T, U> = T extends string ? U : boolean; ",
            "type Forward<Left, Right> = Select<Right, Left>;",
        ));
        let forwarded = fixture.declared_alias("Forward");
        let left = fixture.type_parameter("Left");
        let right = fixture.type_parameter("Right");
        let symbol = fixture.alias_symbol("Forward");
        assert_eq!(
            conditional_alias_projection(&fixture.store, forwarded),
            Ok(Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &[left, right],
            }))
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(fixture.declared_alias("Forward"), forwarded);
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
        let root = conditional_snapshot(&fixture.store, forwarded, None)
            .unwrap()
            .root;
        let alias = fixture
            .store
            .type_payload(forwarded)
            .unwrap()
            .alias()
            .unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![right, left]))
        );
        let key = conditional_type_key(
            &mut fixture.store,
            &[right, left],
            Some(ConditionalAliasIdentity {
                symbol,
                type_arguments: &[right, left],
            }),
            false,
            None,
        )
        .unwrap();
        let TypeCacheState::Allocated(mut cache) = fixture
            .store
            .conditional_root(root)
            .unwrap()
            .instantiations()
            .clone()
        else {
            unreachable!();
        };
        cache.insert(key, forwarded);
        assert!(
            fixture
                .store
                .set_conditional_root_instantiations(root, TypeCacheState::Allocated(cache))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(conditional_alias_projection(&fixture.store, forwarded).is_err());
        assert!(fixture.try_declared_alias("Forward").is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_instantiations_map_default_arguments_and_keep_warm_identity() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Other<U> = U;",
        ));
        let declared = fixture.declared_alias("Select");
        let parameter = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (number, boolean) = (bootstrap.number_type, bootstrap.boolean_type);
        let arguments = [parameter];
        let request = ConditionalTypeInstantiation {
            conditional_type: declared,
            type_arguments: &arguments,
            branches: branches(number, boolean),
            alias: None,
            for_constraint: false,
        };
        let mapped =
            get_conditional_type_instantiation(&mut fixture.store, request, None, None).unwrap();
        assert_eq!(
            conditional_alias_projection(&fixture.store, mapped),
            Ok(Some(ConditionalAliasIdentity {
                symbol: fixture.alias_symbol("Select"),
                type_arguments: &arguments,
            })),
        );
        let warm = conditional_allocation_counts(&fixture.store);
        assert_eq!(
            get_conditional_type_instantiation(&mut fixture.store, request, None, None),
            Ok(mapped)
        );
        assert_eq!(conditional_allocation_counts(&fixture.store), warm);
    }

    #[test]
    fn conditional_alias_cache_validation_rejects_changed_arguments_without_allocating() {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Other<U> = U;",
        ));
        let declared = fixture.declared_alias("Select");
        let parameter = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (number, boolean) = (bootstrap.number_type, bootstrap.boolean_type);
        let arguments = [parameter];
        let request = ConditionalTypeInstantiation {
            conditional_type: declared,
            type_arguments: &arguments,
            branches: branches(number, boolean),
            alias: None,
            for_constraint: false,
        };
        let mapped =
            get_conditional_type_instantiation(&mut fixture.store, request, None, None).unwrap();
        let alias = fixture.store.type_payload(mapped).unwrap().alias().unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![number]))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(
            get_conditional_type_instantiation(&mut fixture.store, request, None, None).is_err()
        );
        assert!(conditional_alias_projection(&fixture.store, mapped).is_err());
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![parameter]))
        );
        assert_eq!(
            get_conditional_type_instantiation(&mut fixture.store, request, None, None),
            Ok(mapped)
        );
        assert_eq!(conditional_allocation_counts(&fixture.store), before);
    }

    #[test]
    fn conditional_alias_requests_reject_foreign_arguments_and_wrong_root_owners_before_allocation()
    {
        let mut fixture = Fixture::new(concat!(
            "type Select<T> = T extends string ? number : boolean; ",
            "type Other<U> = U;",
        ));
        let foreign = Fixture::new("type Foreign = number;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let wrong_owner = fixture.alias_symbol("Other");
        let alias = fixture.store.alloc_type_alias(Some(wrong_owner)).unwrap();
        assert!(
            fixture
                .store
                .set_type_alias_arguments(alias, Some(vec![parameter]))
        );
        let before = conditional_allocation_counts(&fixture.store);
        assert!(
            get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: string,
                    branches: branches(number, boolean),
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter]),
                    alias: Some(alias),
                },
                None
            )
            .is_err()
        );
        assert_eq!(conditional_allocation_counts(&fixture.store), before);

        let declared = fixture.declared_alias("Select");
        let foreign_argument = foreign.store.intrinsic_bootstrap().unwrap().number_type;
        for (conditional_type, argument) in
            [(declared, foreign_argument), (foreign_argument, parameter)]
        {
            let before = conditional_allocation_counts(&fixture.store);
            assert!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type,
                        type_arguments: &[argument],
                        branches: branches(number, boolean),
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None
                )
                .is_err()
            );
            assert_eq!(conditional_allocation_counts(&fixture.store), before);
        }
    }

    #[test]
    fn source_owned_conditional_self_recursion_reaches_the_pinned_limit() {
        let mut fixture = Fixture::new("type Loop<T> = T extends string ? string : Loop<T>;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let declared = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: string,
                branches: branches(string, never),
                infer_type_parameters: &[],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();
        let TypeData::Conditional(data) = fixture.store.type_payload(declared).unwrap().data()
        else {
            panic!("the recursive source alias must retain its conditional root")
        };
        let root = fixture.store.conditional_root(data.root).unwrap();
        assert!(root.alias().is_none());
        assert!(conditional_node_has_alias_owner(
            &fixture.store,
            root.node()
        ));
        let branch_types = branches(string, declared);
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
            fixture.store.mapper_len(),
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: declared,
                    type_arguments: &[number],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Err(ConditionalTypeError::TailRecursionLimit {
                count: CONDITIONAL_TAIL_RECURSION_LIMIT,
                limit: CONDITIONAL_TAIL_RECURSION_LIMIT,
            })
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.conditional_root_len(),
                fixture.store.mapper_len(),
            ),
            before
        );
    }

    #[test]
    fn foreign_inputs_and_duplicate_parameters_fail_before_root_allocation() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let foreign = Fixture::new("type Foreign = string extends string ? number : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let foreign_string = foreign.store.intrinsic_bootstrap().unwrap().string_type;
        let before = fixture.store.conditional_root_len();

        assert_eq!(
            get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: foreign_string,
                    extends_type: string,
                    branches: branches(parameter, never),
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            ),
            Err(ConditionalTypeError::InvalidType(foreign_string))
        );
        assert_eq!(
            get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: string,
                    branches: branches(parameter, never),
                    infer_type_parameters: &[parameter],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            ),
            Err(ConditionalTypeError::DuplicateTypeParameter(parameter))
        );
        assert_eq!(fixture.store.conditional_root_len(), before);
    }

    #[test]
    fn indexed_conditional_operands_preserve_nested_type_parameter_dependencies() {
        let mut fixture =
            Fixture::new("type Result<Object, Key> = Object extends Key ? Object : never;");
        let object = fixture.type_parameter("Object");
        let key = fixture.type_parameter("Key");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let keyof_object = fixture
            .store
            .alloc_index_type(object, IndexFlags::NONE)
            .unwrap();
        let object_access = fixture
            .store
            .alloc_indexed_access_type(object, string, AccessFlags::NONE)
            .unwrap();
        let key_access = fixture
            .store
            .alloc_indexed_access_type(string, key, AccessFlags::NONE)
            .unwrap();
        let nested_access = fixture
            .store
            .alloc_indexed_access_type(keyof_object, key, AccessFlags::NONE)
            .unwrap();

        for (type_, contains_object, contains_key) in [
            (keyof_object, true, false),
            (object_access, true, false),
            (key_access, false, true),
            (nested_access, true, true),
        ] {
            assert_eq!(
                contains_mapped_type_parameter(
                    &fixture.store,
                    type_,
                    &[object],
                    &mut HashSet::new(),
                ),
                Ok(contains_object),
            );
            assert_eq!(
                contains_mapped_type_parameter(&fixture.store, type_, &[key], &mut HashSet::new()),
                Ok(contains_key),
            );
            assert_eq!(
                contains_type_parameter(&fixture.store, type_, &HashSet::from([object])),
                Ok(contains_key),
            );
            assert_eq!(
                contains_type_parameter(&fixture.store, type_, &HashSet::from([key])),
                Ok(contains_object),
            );
            assert_eq!(
                contains_type_parameter(&fixture.store, type_, &HashSet::from([object, key])),
                Ok(false),
            );
            assert_eq!(
                validate_conditional_operand(&fixture.store, type_, &mut HashSet::new(), None),
                Ok(()),
            );
        }

        let node = fixture.conditional();
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: nested_access,
                extends_type: string,
                branches: branches(string, never),
                infer_type_parameters: &[],
                outer_type_parameters: Some(&[object, key]),
                alias: None,
            },
            None,
        )
        .unwrap();
        assert!(matches!(
            fixture.store.type_payload(conditional).map(TypeRecord::data),
            Some(TypeData::Conditional(data)) if data.check_type == nested_access
        ));
    }

    #[test]
    fn indexed_conditional_operands_reject_malformed_nested_signatures() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let parameter = fixture.type_parameter("T");
        let malformed = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_structured_type_members(
            malformed,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));

        let keyof_malformed = fixture
            .store
            .alloc_index_type(malformed, IndexFlags::NONE)
            .unwrap();
        let malformed_object = fixture
            .store
            .alloc_indexed_access_type(malformed, parameter, AccessFlags::NONE)
            .unwrap();
        let malformed_index = fixture
            .store
            .alloc_indexed_access_type(parameter, malformed, AccessFlags::NONE)
            .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.conditional_root_len(),
        );

        for type_ in [keyof_malformed, malformed_object, malformed_index] {
            assert_eq!(
                validate_conditional_operand(&fixture.store, type_, &mut HashSet::new(), None),
                Err(ConditionalTypeError::InvalidSignature(signature)),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.conditional_root_len()
                ),
                before,
            );
        }
    }

    #[test]
    fn default_constraints_cache_branches_and_exclude_any() {
        for true_branch_is_any in [true, false] {
            let mut fixture = Fixture::new("type Result<T> = T extends string ? any : number;");
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, any) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.any_type,
            );
            let branch_types = if true_branch_is_any {
                branches(any, number)
            } else {
                branches(number, any)
            };
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: string,
                    branches: branch_types,
                    infer_type_parameters: &[],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            let cold = conditional_snapshot(&fixture.store, conditional, None).unwrap();
            assert_eq!(cold.resolved_true_type, None);
            assert_eq!(cold.resolved_false_type, None);
            assert_eq!(cold.resolved_default_constraint, None);

            assert_eq!(
                get_default_constraint_of_conditional_type(
                    &mut fixture.store,
                    conditional,
                    branch_types,
                    None,
                    None,
                ),
                Ok(number)
            );
            let resolved = conditional_snapshot(&fixture.store, conditional, None).unwrap();
            assert_eq!(resolved.resolved_true_type, Some(branch_types.true_type));
            assert_eq!(resolved.resolved_false_type, Some(branch_types.false_type));
            assert_eq!(resolved.resolved_default_constraint, Some(number));

            let warm = (fixture.store.type_len(), fixture.store.mapper_len());
            assert_eq!(
                get_default_constraint_of_conditional_type(
                    &mut fixture.store,
                    conditional,
                    branch_types,
                    None,
                    None,
                ),
                Ok(number)
            );
            assert_eq!((fixture.store.type_len(), fixture.store.mapper_len()), warm);
        }
    }

    #[test]
    fn distributive_constraints_filter_a_constrained_parameter() {
        let mut fixture = Fixture::new("type Result<T> = T extends string ? T : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let constraint = canonical_anonymous_union(&mut fixture.store, &[string, number]).unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            parameter,
            Some(constraint),
            None,
            None,
            None,
        ));
        let branch_types = branches(parameter, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: string,
                branches: branch_types,
                infer_type_parameters: &[],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();

        assert_eq!(
            get_constraint_of_distributive_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(Some(string))
        );
        let resolved = conditional_snapshot(&fixture.store, conditional, None).unwrap();
        assert_eq!(resolved.resolved_constraint_of_distributive, Some(string));
        assert_eq!(
            get_constraint_from_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(string)
        );

        assert_eq!(
            get_true_type_from_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(parameter)
        );
        assert_eq!(
            get_false_type_from_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(never)
        );
        assert_eq!(
            constraints::get_constraint_of_type(&mut fixture.store, conditional),
            Ok(Some(string))
        );
    }

    #[test]
    fn template_inference_consumes_complete_unicode_code_points() {
        let surrogate = encode_js_string(&JsString::from_units(vec![0xd800]));
        let surrogate_source = format!("{surrogate}abc");
        for (source, input, expected, selected) in [
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "ABC",
                "A",
                "H",
            ),
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "\u{3042}\u{3044}\u{3046}",
                "\u{3042}",
                "H",
            ),
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                "\u{1F600}abc",
                "\u{1F600}",
                "H",
            ),
            (
                "type Head<T> = T extends `${infer H}${infer R}` ? H : never;",
                surrogate_source.as_str(),
                surrogate.as_str(),
                "H",
            ),
            (
                "type Rest<T> = T extends `${infer H}${infer R}` ? R : never;",
                "\u{1F600}abc",
                "abc",
                "R",
            ),
            (
                "type Rest<T> = T extends `${infer H}${infer R}` ? R : never;",
                surrogate_source.as_str(),
                "abc",
                "R",
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let head = fixture.type_parameter("H");
            let rest = fixture.type_parameter("R");
            let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
            let template = fixture
                .store
                .get_template_literal_type(
                    &[String::new(), String::new(), String::new()],
                    &[head, rest],
                )
                .unwrap();
            let selected = if selected == "H" { head } else { rest };
            let branch_types = branches(selected, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: template,
                    branches: branch_types,
                    infer_type_parameters: &[head, rest],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            let value = fixture
                .store
                .regular_string_literal_type(input.to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            let Some(TypeData::Literal(literal)) =
                fixture.store.type_payload(result).map(TypeRecord::data)
            else {
                panic!("template inference must produce a string literal")
            };
            assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
        }
    }

    #[test]
    fn conditional_template_assignability_matches_patterns_and_unions() {
        let mut fixture = Fixture::new("type Pattern = `start-${string}`;");
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let target = fixture
            .store
            .get_template_literal_type(&["start-".to_owned(), String::new()], &[string])
            .unwrap();
        let matching = fixture
            .store
            .regular_string_literal_type("start-value".to_owned())
            .unwrap();
        let japanese = fixture
            .store
            .regular_string_literal_type("start-\u{3042}".to_owned())
            .unwrap();
        let mismatch = fixture
            .store
            .regular_string_literal_type("other-value".to_owned())
            .unwrap();
        let matching_union =
            canonical_anonymous_union(&mut fixture.store, &[matching, japanese]).unwrap();
        let mixed_union =
            canonical_anonymous_union(&mut fixture.store, &[matching, mismatch]).unwrap();

        for (source, expected) in [
            (matching, true),
            (japanese, true),
            (mismatch, false),
            (matching_union, true),
            (mixed_union, false),
        ] {
            assert_eq!(
                conditional_check_is_assignable(&mut fixture.store, source, target, None),
                Ok(expected),
                "source={source:?}"
            );
        }
    }

    #[test]
    fn template_inference_preserves_unconstrained_string_placeholders() {
        for (source, input, expected, first) in [
            (
                "type Head<T> = T extends `${infer H}${string}` ? H : never;",
                "ABC",
                "A",
                true,
            ),
            (
                "type Head<T> = T extends `${infer H}${string}` ? H : never;",
                "\u{3042}\u{3044}\u{3046}",
                "\u{3042}",
                true,
            ),
            (
                "type Rest<T> = T extends `${string}${infer R}` ? R : never;",
                "ABC",
                "BC",
                false,
            ),
            (
                "type Rest<T> = T extends `${string}${infer R}` ? R : never;",
                "\u{3042}\u{3044}\u{3046}",
                "\u{3044}\u{3046}",
                false,
            ),
        ] {
            let mut fixture = Fixture::new(source);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let inferred = fixture.type_parameter(if first { "H" } else { "R" });
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, never) = (bootstrap.string_type, bootstrap.never_type);
            let placeholders = if first {
                [inferred, string]
            } else {
                [string, inferred]
            };
            let template = fixture
                .store
                .get_template_literal_type(
                    &[String::new(), String::new(), String::new()],
                    &placeholders,
                )
                .unwrap();
            let branch_types = branches(inferred, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: template,
                    branches: branch_types,
                    infer_type_parameters: &[inferred],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            let value = fixture
                .store
                .regular_string_literal_type(input.to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            let Some(TypeData::Literal(literal)) =
                fixture.store.type_payload(result).map(TypeRecord::data)
            else {
                panic!("template inference must produce a string literal")
            };
            assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
        }
    }

    #[test]
    fn template_inference_matches_delimiters_and_rejects_missing_segments() {
        let mut fixture =
            Fixture::new("type Left<T> = T extends `start-${infer A}:${infer B}-end` ? A : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let left = fixture.type_parameter("A");
        let right = fixture.type_parameter("B");
        let never = fixture.store.intrinsic_bootstrap().unwrap().never_type;
        let template = fixture
            .store
            .get_template_literal_type(
                &["start-".to_owned(), ":".to_owned(), "-end".to_owned()],
                &[left, right],
            )
            .unwrap();
        let branch_types = branches(left, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: template,
                branches: branch_types,
                infer_type_parameters: &[left, right],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();
        for (source, expected) in [("start-first:second-end", Some("first")), ("bad", None)] {
            let value = fixture
                .store
                .regular_string_literal_type(source.to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            if let Some(expected) = expected {
                let Some(TypeData::Literal(literal)) =
                    fixture.store.type_payload(result).map(TypeRecord::data)
                else {
                    panic!("a matching template must infer its first segment")
                };
                assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
            } else {
                assert_eq!(result, never);
            }
        }
    }

    #[test]
    fn constrained_template_inference_preserves_numeric_bigint_and_boolean_literals() {
        for (source, constraint_kind, expected) in [
            (
                "42",
                "number",
                Some(LiteralValue::Number(ts_jsnum::Number::new(42.0))),
            ),
            (
                "-7",
                "bigint",
                Some(LiteralValue::BigInt(ts_jsnum::PseudoBigInt::parse_valid(
                    "-7",
                ))),
            ),
            ("true", "boolean", Some(LiteralValue::Boolean(true))),
            ("01", "number", None),
        ] {
            let mut fixture = Fixture::new("type Parse<T> = T extends `${infer U}` ? U : never;");
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let inferred = fixture.type_parameter("U");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let never = bootstrap.never_type;
            let constraint = match constraint_kind {
                "number" => bootstrap.number_type,
                "bigint" => bootstrap.bigint_type,
                "boolean" => bootstrap.boolean_type,
                _ => unreachable!(),
            };
            assert!(fixture.store.set_type_parameter_resolution(
                inferred,
                Some(constraint),
                None,
                None,
                None,
            ));
            let template = fixture
                .store
                .get_template_literal_type(&[String::new(), String::new()], &[inferred])
                .unwrap();
            let branch_types = branches(inferred, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: template,
                    branches: branch_types,
                    infer_type_parameters: &[inferred],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            let value = fixture
                .store
                .regular_string_literal_type(source.to_owned())
                .unwrap();
            let result = get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            )
            .unwrap();
            if let Some(expected) = expected {
                let Some(TypeData::Literal(literal)) =
                    fixture.store.type_payload(result).map(TypeRecord::data)
                else {
                    panic!("{source:?} must infer a {constraint_kind} literal")
                };
                assert_eq!(literal.value, expected);
            } else {
                assert_eq!(result, never);
            }
        }
    }

    #[test]
    fn constrained_template_inference_keeps_strings_when_the_constraint_allows_them() {
        let mut fixture = Fixture::new("type Parse<T> = T extends `${infer U}` ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let constraint = canonical_anonymous_union(&mut fixture.store, &[string, number]).unwrap();
        assert!(fixture.store.set_type_parameter_resolution(
            inferred,
            Some(constraint),
            None,
            None,
            None,
        ));
        let template = fixture
            .store
            .get_template_literal_type(&[String::new(), String::new()], &[inferred])
            .unwrap();
        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: template,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();
        let value = fixture
            .store
            .regular_string_literal_type("42".to_owned())
            .unwrap();
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[value],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(value)
        );
    }

    #[test]
    fn conditional_inference_reads_call_and_construct_return_types() {
        for construct in [false, true] {
            let mut fixture = Fixture::new("type Result<T> = T extends infer U ? U : never;");
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let inferred = fixture.type_parameter("U");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, never) = (bootstrap.string_type, bootstrap.never_type);
            let target = callable_object(&mut fixture.store, inferred, construct);
            let source = callable_object(&mut fixture.store, string, construct);
            let branch_types = branches(inferred, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: target,
                    branches: branch_types,
                    infer_type_parameters: &[inferred],
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(string),
                "construct={construct}"
            );
        }
    }

    #[test]
    fn conditional_inference_uses_bound_generic_signature_constraints() {
        let mut fixture =
            Fixture::new("type H<X> = (<O extends X>() => O) extends (() => infer R) ? R : never;");
        let node = fixture.conditional();
        let outer = fixture.type_parameter("X");
        let local = fixture.type_parameter("O");
        let inferred = fixture.type_parameter("R");
        assert!(
            fixture
                .store
                .set_type_parameter_resolution(local, Some(outer), None, None, None)
        );

        let source = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        let signature = fixture
            .store
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                vec![local],
                None,
                Vec::new(),
                Some(local),
                None,
                0,
            )
            .unwrap();
        assert!(fixture.store.set_structured_type_members(
            source,
            None,
            None,
            Some(vec![signature]),
            None,
            None,
        ));
        let target = callable_object(&mut fixture.store, inferred, false);
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        assert_eq!(
            contains_type_parameter(&fixture.store, source, &HashSet::new()),
            Ok(true),
        );
        assert_eq!(
            contains_type_parameter(&fixture.store, source, &HashSet::from([outer])),
            Ok(false),
        );

        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: source,
                extends_type: target,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: Some(&[outer]),
                alias: None,
            },
            None,
        )
        .unwrap();
        for argument in [string, number] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[argument],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(argument),
            );
        }

        let original = fixture.store.signature(signature).unwrap();
        assert_eq!(original.type_parameters(), &[local]);
        assert_eq!(original.resolved_return_type(), Some(local));
        let Some(TypeData::TypeParameter(parameter)) =
            fixture.store.type_payload(local).map(TypeRecord::data)
        else {
            panic!("a signature-local generic parameter must remain intact")
        };
        assert_eq!(parameter.constraint, Some(outer));
    }

    #[test]
    fn declared_constructor_inference_maps_alias_arguments_and_checks_signatures() {
        let mut fixture = Fixture::new(concat!(
            "type Strings = { new(value: string): number }; ",
            "type Numbers = { new(value: number): string }; ",
            "type Extra = { new(value: string, extra: number): boolean }; ",
            "type Overloaded = { new(value: number): string; new(value: string): boolean }; ",
            "type Callable = { (value: string): boolean }; ",
            "type Extract<T, Value> = T extends { new(value: Value): infer Result } ",
            "? Result : never;",
        ));
        let strings = fixture.declared_alias("Strings");
        let numbers = fixture.declared_alias("Numbers");
        let extra = fixture.declared_alias("Extra");
        let overloaded = fixture.declared_alias("Overloaded");
        let callable = fixture.declared_alias("Callable");
        let conditional = fixture.declared_alias("Extract");
        let inferred = fixture.type_parameter("Result");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, boolean, any, unknown, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
            bootstrap.any_type,
            bootstrap.unknown_type,
            bootstrap.never_type,
        );
        let branch_types = branches(inferred, never);
        let cases = [
            (strings, string, number),
            (strings, number, never),
            (numbers, number, string),
            (extra, string, never),
            (overloaded, string, boolean),
            (callable, string, never),
            (any, string, unknown),
        ];

        for (source, argument, expected) in cases {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source, argument],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected),
                "source={source:?}, argument={argument:?}",
            );
        }

        let union =
            canonical_anonymous_union(&mut fixture.store, &[strings, numbers, boolean]).unwrap();
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[union, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(number),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_conditional_type_instantiation(
                &mut fixture.store,
                ConditionalTypeInstantiation {
                    conditional_type: conditional,
                    type_arguments: &[union, string],
                    branches: branch_types,
                    alias: None,
                    for_constraint: false,
                },
                None,
                None,
            ),
            Ok(number),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn constructor_inference_rejects_poisoned_provenance_before_cached_results() {
        for corruption in 0..3 {
            let mut fixture = Fixture::new(concat!(
                "type Source = { new(): string }; ",
                "type Extract<T> = T extends { new(): infer Result } ? Result : never;",
            ));
            let source = fixture.declared_alias("Source");
            let conditional = fixture.declared_alias("Extract");
            let inferred = fixture.type_parameter("Result");
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (string, number, never) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.never_type,
            );
            let branch_types = branches(inferred, never);
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(string),
            );

            let root = conditional_snapshot(&fixture.store, conditional, None)
                .unwrap()
                .root;
            let target = fixture.store.conditional_root(root).unwrap().extends_type();
            let poisoned = match corruption {
                0 | 1 => {
                    let owner = if corruption == 0 { source } else { target };
                    let signature = fixture
                        .store
                        .type_payload(owner)
                        .and_then(|record| record.data().structured())
                        .and_then(|structured| structured.signatures.as_deref())
                        .and_then(|signatures| signatures.first())
                        .copied()
                        .unwrap();
                    assert!(
                        fixture
                            .store
                            .set_signature_resolved_return_type(signature, Some(number))
                    );
                    owner
                }
                2 => {
                    let signature = fixture
                        .store
                        .type_payload(source)
                        .and_then(|record| record.data().structured())
                        .and_then(|structured| structured.signatures.as_deref())
                        .and_then(|signatures| signatures.first())
                        .copied()
                        .unwrap();
                    let forged = fixture
                        .store
                        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
                        .unwrap();
                    assert!(fixture.store.set_structured_type_members(
                        forged,
                        None,
                        None,
                        None,
                        Some(vec![signature]),
                        None,
                    ));
                    forged
                }
                _ => unreachable!(),
            };
            let argument = if corruption == 2 { poisoned } else { source };
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .conditional_root(root)
                    .unwrap()
                    .instantiations()
                    .clone(),
            );
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[argument],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Err(ConditionalTypeError::Relation(
                    RelationUnavailable::MalformedFunctionType(poisoned),
                )),
                "corruption case {corruption}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.mapper_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture
                        .store
                        .conditional_root(root)
                        .unwrap()
                        .instantiations()
                        .clone(),
                ),
                before,
                "corruption case {corruption}",
            );
        }
    }

    #[test]
    fn cached_distributive_constructor_constraints_revalidate_their_target() {
        let mut fixture =
            Fixture::new("type Extract<T> = T extends { new(): infer Result } ? Result : never;");
        let conditional = fixture.declared_alias("Extract");
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("Result");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        assert!(fixture.store.set_type_parameter_resolution(
            parameter,
            Some(string),
            None,
            None,
            None,
        ));
        let branch_types = branches(inferred, never);
        assert_eq!(
            get_constraint_of_distributive_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Ok(None),
        );
        let target = conditional_snapshot(&fixture.store, conditional, None)
            .map(|data| data.extends_type)
            .unwrap();
        let signature = fixture
            .store
            .type_payload(target)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first())
            .copied()
            .unwrap();
        assert!(
            fixture
                .store
                .set_signature_resolved_return_type(signature, Some(number))
        );
        let before = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            get_constraint_of_distributive_conditional_type(
                &mut fixture.store,
                conditional,
                branch_types,
                None,
                None,
            ),
            Err(ConditionalTypeError::Relation(
                RelationUnavailable::MalformedFunctionType(target),
            )),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn conditional_inference_reads_named_object_properties() {
        let mut fixture = Fixture::new("type Result<T> = T extends infer U ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, never) = (bootstrap.string_type, bootstrap.never_type);
        let target = property_object(&mut fixture.store, "value", inferred);
        let matching = property_object(&mut fixture.store, "value", string);
        let missing = property_object(&mut fixture.store, "other", string);
        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: target,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();

        for (source, expected) in [(matching, string), (missing, never)] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected)
            );
        }
    }

    #[test]
    fn tuple_inference_preserves_elements_and_rejects_short_inputs() {
        let mut fixture = Fixture::new("type Result<T> = T extends [infer U, number] ? U : never;");
        let node = fixture.conditional();
        let parameter = fixture.type_parameter("T");
        let inferred = fixture.type_parameter("U");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number, never) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.never_type,
        );
        let required = fixture
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let target_infos = [required, required];
        let target = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[inferred, number],
                &target_infos,
                false,
            ))
            .unwrap();
        let matching = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number],
                &target_infos,
                false,
            ))
            .unwrap();
        let missing = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string],
                &[required],
                false,
            ))
            .unwrap();
        let branch_types = branches(inferred, never);
        let conditional = get_type_from_conditional_type(
            &mut fixture.store,
            ConditionalTypeRequest {
                node,
                check_type: parameter,
                extends_type: target,
                branches: branch_types,
                infer_type_parameters: &[inferred],
                outer_type_parameters: Some(&[parameter]),
                alias: None,
            },
            None,
        )
        .unwrap();

        for (source, expected) in [(matching, string), (missing, never)] {
            assert_eq!(
                get_conditional_type_instantiation(
                    &mut fixture.store,
                    ConditionalTypeInstantiation {
                        conditional_type: conditional,
                        type_arguments: &[source],
                        branches: branch_types,
                        alias: None,
                        for_constraint: false,
                    },
                    None,
                    None,
                ),
                Ok(expected)
            );
        }
    }

    #[test]
    fn tuple_inference_uses_fixed_constraints_for_adjacent_rest_and_variadic_elements() {
        for (declaration, rest_first) in [
            (
                "type Result<T> = T extends [...(infer C)[], ...infer B extends [any, any]] ? B : never;",
                true,
            ),
            (
                "type Result<T> = T extends [...infer A extends [any, any], ...(infer D)[]] ? A : never;",
                false,
            ),
        ] {
            let mut fixture = Fixture::new(declaration);
            let node = fixture.conditional();
            let parameter = fixture.type_parameter("T");
            let rest_parameter = fixture.type_parameter(if rest_first { "C" } else { "D" });
            let variadic_parameter = fixture.type_parameter(if rest_first { "B" } else { "A" });
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let (any, never) = (bootstrap.any_type, bootstrap.never_type);
            let required = fixture
                .store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap();
            let rest = fixture
                .store
                .create_tuple_element_info(ElementFlags::REST, None)
                .unwrap();
            let variadic = fixture
                .store
                .create_tuple_element_info(ElementFlags::VARIADIC, None)
                .unwrap();
            let constraint = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &[any, any],
                    &[required, required],
                    false,
                ))
                .unwrap();
            assert!(fixture.store.set_type_parameter_resolution(
                variadic_parameter,
                Some(constraint),
                None,
                None,
                None,
            ));
            let (target_types, target_infos, inferred_parameters) = if rest_first {
                (
                    [rest_parameter, variadic_parameter],
                    [rest, variadic],
                    [rest_parameter, variadic_parameter],
                )
            } else {
                (
                    [variadic_parameter, rest_parameter],
                    [variadic, rest],
                    [variadic_parameter, rest_parameter],
                )
            };
            let target = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &target_types,
                    &target_infos,
                    false,
                ))
                .unwrap();
            let branch_types = branches(variadic_parameter, never);
            let conditional = get_type_from_conditional_type(
                &mut fixture.store,
                ConditionalTypeRequest {
                    node,
                    check_type: parameter,
                    extends_type: target,
                    branches: branch_types,
                    infer_type_parameters: &inferred_parameters,
                    outer_type_parameters: Some(&[parameter]),
                    alias: None,
                },
                None,
            )
            .unwrap();

            let mut values = Vec::new();
            for value in [1.0, 2.0, 3.0, 4.0] {
                values.push(
                    fixture
                        .store
                        .regular_number_literal_type(ts_jsnum::Number::new(value))
                        .unwrap(),
                );
            }
            let expected_long = if rest_first {
                &values[2..]
            } else {
                &values[..2]
            };
            let cases: &[(&[TypeId], Option<&[TypeId]>)] = &[
                (&values[..2], Some(&values[..2])),
                (&values[..], Some(expected_long)),
                (&values[..1], None),
            ];
            for (elements, expected) in cases {
                let infos = vec![required; elements.len()];
                let source = fixture
                    .store
                    .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                        elements, &infos, false,
                    ))
                    .unwrap();
                let expected = if let Some(elements) = expected {
                    let infos = vec![required; elements.len()];
                    fixture
                        .store
                        .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                            elements, &infos, false,
                        ))
                        .unwrap()
                } else {
                    never
                };
                assert_eq!(
                    get_conditional_type_instantiation(
                        &mut fixture.store,
                        ConditionalTypeInstantiation {
                            conditional_type: conditional,
                            type_arguments: &[source],
                            branches: branch_types,
                            alias: None,
                            for_constraint: false,
                        },
                        None,
                        None,
                    ),
                    Ok(expected),
                    "rest_first={rest_first}, elements={elements:?}",
                );
            }
        }
    }

    #[test]
    fn tuple_assignability_aligns_rest_elements_with_required_suffixes() {
        let mut fixture = Fixture::new("type Target = [...number[], string];");
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let required = fixture
            .store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let rest = fixture
            .store
            .create_tuple_element_info(ElementFlags::REST, None)
            .unwrap();
        let target = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, string],
                &[rest, required],
                false,
            ))
            .unwrap();

        let cases: &[(&[TypeId], bool)] = &[
            (&[number, number, string], true),
            (&[string], true),
            (&[number, number, number], false),
            (&[string, string], false),
        ];
        for (elements, expected) in cases {
            let infos = vec![required; elements.len()];
            let source = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    elements, &infos, false,
                ))
                .unwrap();
            assert_eq!(
                conditional_check_is_assignable(&mut fixture.store, source, target, None),
                Ok(*expected),
                "elements={elements:?}"
            );
        }

        let prefixed_target = fixture
            .store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number, string],
                &[required, rest, required],
                false,
            ))
            .unwrap();
        for elements in [&[string, number, number, string][..], &[string, string][..]] {
            let infos = vec![required; elements.len()];
            let source = fixture
                .store
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    elements, &infos, false,
                ))
                .unwrap();
            assert_eq!(
                conditional_check_is_assignable(&mut fixture.store, source, prefixed_target, None),
                Ok(true),
                "elements={elements:?}"
            );
        }
    }
}
