//! Source operation receipts share one transport list. Each variant retains
//! its own request, result, dependency closure, and replay operation.

use super::*;
use crate::semantic::IndexInfoId;
use crate::semantic::relater::{
    MappedValueRecoveryAdapterScope, observe_mapped_value_adapter_outcome,
    observe_mapped_value_adapter_path, observe_mapped_value_predicate,
};
use crate::semantic::mapped_types::{
    MappedMembersReplayIdentity, SourceMappedMembersOutcome, capture_source_mapped_members_identity,
    validate_source_mapped_recovered_index_identity, validate_source_mapped_recovered_value_identity,
    validate_source_mapped_value_identity,
};

#[derive(Clone, Debug)]
pub(super) enum SourceQueryRead {
    Conditional(ConditionalSourceResultProof),
    Operation(SourceOperationProof),
}

impl SourceQueryRead {
    pub(super) fn conditional(&self) -> Option<ConditionalSourceResultProof> {
        match self { Self::Conditional(proof) => Some(proof.clone()), Self::Operation(_) => None }
    }

    pub(super) fn operation(&self) -> Option<SourceOperationProof> {
        match self { Self::Operation(proof) => Some(proof.clone()), Self::Conditional(_) => None }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(in crate::semantic) enum SourceMappedReadRequest {
    Members { receiver: TypeId },
    Value { receiver: TypeId, member: SemanticSymbolId },
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(in crate::semantic) enum SourceQueryDemand {
    Mapped(SourceMappedReadRequest),
    IndexedDiagnostic { node: NodeRef, object: TypeId, index: TypeId },
}

impl SourceQueryDemand {
    pub(in crate::semantic) fn from_error(error: &DeclaredTypeError) -> Option<Self> {
        if let Some(request) = SourceMappedReadRequest::from_error(error) {
            return Some(Self::Mapped(request));
        }
        match error {
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::SourceIndexedDiagnosticDemand { node, object, index }) => {
                Some(Self::IndexedDiagnostic { node: *node, object: *object, index: *index })
            }
            _ => None,
        }
    }

    #[track_caller]
    fn unavailable(self) -> DeclaredTypeError {
        match self {
            Self::Mapped(request) => request.missing_proof(),
            Self::IndexedDiagnostic { node, object, index } => {
                type_node_unavailable(TypeNodeUnavailable::SourceIndexedDiagnosticDemand { node, object, index })
            }
        }
    }
}

impl SourceMappedReadRequest {
    pub(in crate::semantic) fn from_error(error: &DeclaredTypeError) -> Option<Self> {
        match error {
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::SourceMappedMembersDemand { receiver }) => {
                Some(Self::Members { receiver: *receiver })
            }
            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::SourceMappedValueDemand { receiver, member }) => {
                Some(Self::Value { receiver: *receiver, member: *member })
            }
            _ => None,
        }
    }

    #[track_caller]
    pub(in crate::semantic) fn missing_proof(self) -> DeclaredTypeError {
        if matches!(self, Self::Members { .. }) {
            super::super::production::observe_mixed_recheck_members(
                self,
                std::panic::Location::caller(),
            );
        }
        type_node_unavailable(match self {
            Self::Members { receiver } => TypeNodeUnavailable::SourceMappedMembersDemand { receiver },
            Self::Value { receiver, member } => TypeNodeUnavailable::SourceMappedValueDemand { receiver, member },
        })
    }

    pub(in crate::semantic) const fn receiver(self) -> TypeId {
        match self {
            Self::Members { receiver } | Self::Value { receiver, .. } => receiver,
        }
    }
}

pub(in crate::semantic) enum SourceMappedReadOutcome {
    Complete(SourceMappedReadProof),
    LimitRecovery(TypeId),
    RecoveredValue(SourceMappedRecoveredValue),
    RecoveredMembers(SourceMappedRecoveredMembers),
}

/// A completed Members proof with one separate, fresh native index episode.
#[derive(Debug)]
pub(in crate::semantic) struct SourceMappedRecoveredMembers {
    proof: SourceMappedReadProof,
    index: IndexInfoId,
    recovery: TypeId,
    episode: (InstantiationLimitEventMark, InstantiationLimitEventMark),
}

impl SourceMappedRecoveredMembers {
    pub(in crate::semantic) const fn recovery_type(&self) -> TypeId {
        self.recovery
    }

    pub(in crate::semantic) fn into_parts(self) -> (
        SourceMappedReadProof, IndexInfoId, TypeId,
        (InstantiationLimitEventMark, InstantiationLimitEventMark),
    ) {
        (self.proof, self.index, self.recovery, self.episode)
    }
}

/// A real cached selected value, separate from the scalar limit recovery leaf.
#[derive(Debug)]
pub(in crate::semantic) struct SourceMappedRecoveredValue {
    proof: SourceMappedReadProof,
    episode: Option<(InstantiationLimitEventMark, InstantiationLimitEventMark)>,
}

impl SourceMappedRecoveredValue {
    pub(in crate::semantic) fn recovery_type(&self) -> TypeId {
        self.proof.recovery_error.expect("a recovered value retains its canonical recovery type")
    }

    pub(in crate::semantic) fn into_parts(
        self,
    ) -> (SourceMappedReadProof, Option<(InstantiationLimitEventMark, InstantiationLimitEventMark)>) {
        (self.proof, self.episode)
    }
}

#[derive(Clone, Debug)]
pub(in crate::semantic) struct SourceMappedReadProof {
    request: SourceMappedReadRequest,
    members: MappedMembersReplayIdentity,
    value: Option<TypeId>,
    recovery_error: Option<TypeId>,
    globals: CanonicalGlobalTypes,
    options: CanonicalTypeQueryOptions,
    aliases: HashMap<NodeRef, CanonicalTypeReferenceAliasTarget>,
    jsdoc: Option<CanonicalJsDocImportTypeTarget>,
    conditionals: Vec<ConditionalSourceResultProof>,
    values: Vec<GlobalThisMemberValueProof>,
    returns: Vec<SourceSignatureReturnProof>,
    operations: Vec<SourceOperationProof>,
}

impl SourceMappedReadProof {
    pub(in crate::semantic) const fn request(&self) -> SourceMappedReadRequest {
        self.request
    }

    pub(in crate::semantic) fn matches_context(
        &self,
        globals: &CanonicalGlobalTypes,
        options: CanonicalTypeQueryOptions,
    ) -> bool {
        &self.globals == globals && self.options == options
    }

    pub(in crate::semantic) fn same_result(&self, other: &Self) -> bool {
        self.request == other.request && self.members == other.members && self.value == other.value
            && self.recovery_error == other.recovery_error
    }

    pub(in crate::semantic) const fn is_recovered_value(&self) -> bool {
        self.recovery_error.is_some()
    }

    pub(in crate::semantic) fn members(&self) -> &crate::semantic::mapped_types::ResolvedMappedTypeMembers {
        self.members.members()
    }

    pub(in crate::semantic) const fn value(&self) -> Option<TypeId> {
        self.value
    }

    pub(in crate::semantic) fn recovered_members_index_is_current(
        &self, store: &CanonicalTypeMapperStore, index: IndexInfoId, globals: &CanonicalGlobalTypes,
    ) -> bool {
        matches!(self.request, SourceMappedReadRequest::Members { .. })
            && self.value.is_none() && self.recovery_error.is_none()
            && self.members.recovered_index_is_current(store, index, globals)
    }

    pub(in crate::semantic) fn recovered_members_index_with_source(
        &self, store: &CanonicalTypeMapperStore, globals: &CanonicalGlobalTypes,
        source: &dyn ConditionalBranchSource,
    ) -> Result<Option<IndexInfoId>, MappedTypeError> {
        if !matches!(self.request, SourceMappedReadRequest::Members { .. })
            || self.value.is_some() || self.recovery_error.is_some()
        {
            return Err(MappedTypeError::InvalidCachedMembers(self.request.receiver()));
        }
        validate_source_mapped_recovered_index_identity(store, &self.members, globals, source)
    }
}

impl SourceTypeQueryAdapter<'_, '_, '_> {
    #[track_caller]
    fn mapped_read_recovery_since(
        &self,
        session: &InstantiationSession,
        mark: crate::semantic::instantiate::InstantiationLimitEventMark,
        recoveries: (usize, usize),
        receiver: TypeId,
    ) -> Result<Option<SourceMappedReadOutcome>, MappedTypeError> {
        if observe_mapped_value_predicate("adapter_limit_checkpoint", session.limit_event_occurred_since(mark)) {
            return session.recovery_error_type()
                .map(|type_| Some(SourceMappedReadOutcome::LimitRecovery(type_)))
                .ok_or(MappedTypeError::InvalidMappedType(receiver));
        }
        if recoveries != (self.context.recoveries.len(), self.context.semantic_results.len()) {
            return Err(MappedTypeError::UnsupportedSource(receiver));
        }
        Ok(None)
    }

    pub(super) fn resolve_mapped_read(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        request: SourceMappedReadRequest,
        session: &mut InstantiationSession,
    ) -> Result<SourceMappedReadOutcome, MappedTypeError> {
        let receiver = request.receiver();
        if !matches!(store.type_payload(receiver).map(TypeRecord::data), Some(TypeData::Mapped(_))) {
            return Err(MappedTypeError::InvalidMappedType(receiver));
        }
        if !self.context.active_mapped_reads.insert(request) {
            return Err(MappedTypeError::RecursiveMembers(receiver));
        }
        let globals = self.context.globals.clone();
        let arrays = Some(CanonicalArrayTargets::from_global_types(&globals));
        let values = self.context.values.len();
        let returns = self.context.returns.len();
        let recoveries = (self.context.recoveries.len(), self.context.semantic_results.len());
        let mark = session.limit_event_mark();
        let _mapped_value_observation = MappedValueRecoveryAdapterScope::enter(request, mark);
        let previous = self.context.signature_instantiation_conditionals.clone();
        let reads = previous.clone().unwrap_or_default();
        let conditionals = reads.borrow().len();
        self.context.signature_instantiation_conditionals = Some(reads.clone());
        let result = (|| {
            if let Some(proof) = self.context.instantiations.iter().rev().find_map(|operation| {
                match operation {
                    SourceOperationProof::MappedRead(proof) if proof.request == request => Some(proof.clone()),
                    _ => None,
                }
            }) {
                observe_mapped_value_adapter_path(true);
                self.context.validate_mapped_read(store, &proof, &globals, self.context.options.strict_function_types)?;
                if let Some(recovery) = proof.recovery_error {
                    if self.context.mapped_recovery_disposition != super::super::relater::SourceRelationRecoveryDisposition::Assignment
                        || session.recovery_error_type() != Some(recovery)
                        || session.limit_event_occurred_since(mark)
                    {
                        return Err(MappedTypeError::UnsupportedSource(receiver));
                    }
                    return Ok(SourceMappedReadOutcome::RecoveredValue(SourceMappedRecoveredValue {
                        proof, episode: None,
                    }));
                }
                return Ok(SourceMappedReadOutcome::Complete(proof));
            }
            observe_mapped_value_adapter_path(false);
            store.validate_source_mapped_read_request(receiver, &globals, &*self)?;
            if let Some(modifier) = crate::semantic::mapped_types::source_mapped_instance_modifier_input(
                store, receiver, arrays, Some((&globals, &*self)),
            )? {
                match store.type_payload(modifier).map(TypeRecord::data) {
                    Some(TypeData::Interface(_) | TypeData::TypeReference(_)) => {
                        self.context.query(store, session, self.diagnostics, |query| {
                            query.prepare_source_class_interface_members(modifier)
                        })?;
                        if let Some(recovery) = self.mapped_read_recovery_since(session, mark, recoveries, receiver)? {
                            return Ok(recovery);
                        }
                        // Preparation already validated this completed ordinary table.
                        let completed_ordinary_interface = store.source_declared_member_names(modifier).is_none()
                            && store.direct_interface_heritage_provenance(modifier).is_none()
                            && store.type_payload(modifier).is_some_and(|record| {
                                record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK == ObjectFlags::INTERFACE
                                    && record.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED)
                                    && matches!(record.data(), TypeData::Interface(interface)
                                        if interface.declared_members_resolved
                                            && interface.base_types_resolved
                                            && interface.all_type_parameters.is_none()
                                            && interface.reference.resolved_type_arguments.is_none())
                            });
                        if !completed_ordinary_interface {
                            crate::semantic::instantiated_members::resolve_members_with_array_targets_and_session(
                                store, modifier, arrays, session,
                            ).map_err(|error| match error {
                                crate::semantic::instantiated_members::GenericInterfaceMemberError::Capacity(_) => MappedTypeError::Capacity,
                                crate::semantic::instantiated_members::GenericInterfaceMemberError::UnsupportedTarget(_)
                                | crate::semantic::instantiated_members::GenericInterfaceMemberError::UnsupportedMember(_)
                                | crate::semantic::instantiated_members::GenericInterfaceMemberError::UnsupportedPropertyType(_) => MappedTypeError::UnsupportedSource(modifier),
                                _ => MappedTypeError::InvalidSource(modifier),
                            })?;
                        }
                    }
                    Some(TypeData::Mapped(_)) => {
                        match self.resolve_mapped_read(
                            store, SourceMappedReadRequest::Members { receiver: modifier }, session,
                        )? {
                            SourceMappedReadOutcome::Complete(_) => {}
                            SourceMappedReadOutcome::LimitRecovery(type_) => return Ok(SourceMappedReadOutcome::LimitRecovery(type_)),
                            SourceMappedReadOutcome::RecoveredValue(_) => return Err(MappedTypeError::UnsupportedSource(modifier)),
                            SourceMappedReadOutcome::RecoveredMembers(_) => return Err(MappedTypeError::Declared(
                                type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery),
                            )),
                        }
                    }
                    _ => {}
                }
                if let Some(recovery) = self.mapped_read_recovery_since(session, mark, recoveries, receiver)? {
                    return Ok(recovery);
                }
            }
            let members = match store.resolve_source_mapped_type_members(receiver, &globals, session, self)? {
                SourceMappedMembersOutcome::Complete(members) => members,
                SourceMappedMembersOutcome::LimitRecovery(type_) => return Ok(SourceMappedReadOutcome::LimitRecovery(type_)),
            };
            let members_episode = if matches!(request, SourceMappedReadRequest::Members { .. })
                && session.limit_event_occurred_since(mark)
                && self.context.mapped_recovery_disposition == super::super::relater::SourceRelationRecoveryDisposition::Assignment
            {
                let canonical = store.intrinsic_bootstrap().ok_or(MappedTypeError::BootstrapUninitialized)?.error_type;
                if session.recovery_error_type() != Some(canonical)
                    || recoveries != (self.context.recoveries.len(), self.context.semantic_results.len())
                {
                    return Err(MappedTypeError::UnsupportedSource(receiver));
                }
                Some((canonical, (mark, session.limit_event_mark())))
            } else {
                if let Some(recovery) = self.mapped_read_recovery_since(session, mark, recoveries, receiver)? {
                    return Ok(recovery);
                }
                None
            };
            let mut recovery_error = None;
            let mut episode = None;
            let value = match request {
                SourceMappedReadRequest::Members { .. } => None,
                SourceMappedReadRequest::Value { member, .. } => {
                    if !members.properties().contains(&member) {
                        return Err(MappedTypeError::InvalidCachedProperty(member));
                    }
                    let name = store.symbol(member).ok_or(MappedTypeError::InvalidCachedProperty(member))?.name().to_owned();
                    let episode_start = session.limit_event_mark();
                    let value = store.resolve_mapped_type_property_with_source(
                        receiver, name.as_ref(), crate::semantic::mapped_types::MappedTypeModifiers::NONE,
                        &globals, session, self,
                    )?;
                    let fresh = session.limit_event_occurred_since(episode_start);
                    let recovered = store.mapped_property_recovery(member).is_some();
                    if self.context.mapped_recovery_disposition == super::super::relater::SourceRelationRecoveryDisposition::Assignment
                        && (fresh || recovered)
                    {
                        let canonical = store.intrinsic_bootstrap().ok_or(MappedTypeError::BootstrapUninitialized)?.error_type;
                        if session.recovery_error_type() != Some(canonical)
                            || recoveries != (self.context.recoveries.len(), self.context.semantic_results.len())
                            || episode_start != mark
                            || !recovered
                        {
                            return Err(MappedTypeError::UnsupportedSource(receiver));
                        }
                        recovery_error = Some(canonical);
                        if fresh {
                            episode = Some((episode_start, session.limit_event_mark()));
                        }
                    } else if let Some(recovery) = self.mapped_read_recovery_since(session, mark, recoveries, receiver)? {
                        return Ok(recovery);
                    }
                    let value = value.ok_or(MappedTypeError::InvalidCachedProperty(member))?;
                    if value.symbol() != member {
                        return Err(MappedTypeError::InvalidCachedProperty(member));
                    }
                    Some(value.type_id())
                }
            };
            if recovery_error.is_none() && members_episode.is_none()
                && let Some(recovery) = self.mapped_read_recovery_since(session, mark, recoveries, receiver)?
            {
                return Ok(recovery);
            }
            let identity = capture_source_mapped_members_identity(store, receiver, &globals, &*self)?;
            if let (SourceMappedReadRequest::Value { member, .. }, Some(value)) = (request, value) {
                if recovery_error.is_some() {
                    validate_source_mapped_recovered_value_identity(store, &identity, member, value, &globals, &*self)?;
                } else {
                    validate_source_mapped_value_identity(store, &identity, member, value, &globals, &*self)?;
                }
            }
            let proof = SourceMappedReadProof {
                request, members: identity, value, recovery_error, globals: globals.clone(), options: self.context.options,
                aliases: self.context.aliases.clone(), jsdoc: self.context.jsdoc,
                conditionals: reads.borrow()[conditionals..].iter().filter_map(SourceQueryRead::conditional).collect(),
                values: self.context.values[values..].to_vec(), returns: self.context.returns[returns..].to_vec(),
                operations: reads.borrow()[conditionals..].iter().filter_map(SourceQueryRead::operation).collect(),
            };
            Ok(if let Some((recovery, episode)) = members_episode {
                let index = proof.recovered_members_index_with_source(store, &globals, &*self)?
                    .ok_or(MappedTypeError::UnsupportedSource(receiver))?;
                if recoveries != (self.context.recoveries.len(), self.context.semantic_results.len())
                    || episode.1 != session.limit_event_mark()
                {
                    return Err(MappedTypeError::UnsupportedSource(receiver));
                }
                SourceMappedReadOutcome::RecoveredMembers(SourceMappedRecoveredMembers {
                    proof, index, recovery, episode,
                })
            } else if recovery_error.is_some() {
                SourceMappedReadOutcome::RecoveredValue(SourceMappedRecoveredValue { proof, episode })
            } else {
                SourceMappedReadOutcome::Complete(proof)
            })
        })();
        self.context.signature_instantiation_conditionals = previous;
        self.context.active_mapped_reads.remove(&request);
        let result = result?;
        let retained = match &result {
            SourceMappedReadOutcome::Complete(proof) => Some(proof),
            SourceMappedReadOutcome::RecoveredValue(value) => Some(&value.proof),
            SourceMappedReadOutcome::RecoveredMembers(members) => Some(&members.proof),
            SourceMappedReadOutcome::LimitRecovery(_) => None,
        };
        if let Some(proof) = retained {
            self.context.validate_mapped_read(store, proof, &globals, self.context.options.strict_function_types)?;
            self.context.retain_mapped_read(proof.clone())?;
        }
        observe_mapped_value_adapter_outcome(&result);
        Ok(result)
    }
}

#[derive(Clone, Debug)]
pub(in crate::semantic) enum SourceOperationProof {
    SignatureInstantiation(SourceSignatureInstantiationProof),
    MappedRead(SourceMappedReadProof),
}

impl SourceOperationProof {
    pub(in crate::semantic) fn as_signature_instantiation(&self) -> Option<&SourceSignatureInstantiationProof> {
        match self {
            Self::SignatureInstantiation(proof) => Some(proof),
            Self::MappedRead(_) => None,
        }
    }

    pub(in crate::semantic) fn into_signature_instantiation(self) -> SourceSignatureInstantiationProof {
        match self {
            Self::SignatureInstantiation(proof) => proof,
            Self::MappedRead(_) => panic!("mapped read receipts require the complete operation handoff"),
        }
    }
}

impl SourceTypeQueryContext<'_, '_> {
    pub(super) fn retain_mapped_read(
        &mut self,
        proof: SourceMappedReadProof,
    ) -> Result<(), DeclaredTypeError> {
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery);
        if !proof.matches_context(&self.globals, self.options)
            || proof.aliases != self.aliases
            || proof.jsdoc != self.jsdoc
            || self.instantiations.iter().any(|operation| match operation {
                SourceOperationProof::MappedRead(old) => old.request == proof.request && !old.same_result(&proof),
                SourceOperationProof::SignatureInstantiation(_) => false,
            })
        {
            return Err(invalid());
        }
        if let Some(reads) = &self.signature_instantiation_conditionals {
            reads.borrow_mut().push(SourceQueryRead::Operation(SourceOperationProof::MappedRead(proof.clone())));
        }
        let retained = self.instantiations.iter_mut().rev().find_map(|operation| match operation {
            SourceOperationProof::MappedRead(old) if old.request == proof.request => Some(old),
            _ => None,
        });
        if let Some(old) = retained {
            *old = proof;
        } else {
            self.instantiations.push(SourceOperationProof::MappedRead(proof));
        }
        Ok(())
    }

    pub(super) fn validate_operation(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &SourceOperationProof,
        globals: &CanonicalGlobalTypes,
        strict: Option<bool>,
    ) -> Result<(), DeclaredTypeError> {
        match proof {
            SourceOperationProof::SignatureInstantiation(proof) => {
                self.validate_signature_instantiation(store, proof, globals, strict)
            }
            SourceOperationProof::MappedRead(proof) => self.validate_mapped_read(store, proof, globals, strict),
        }
    }

    pub(super) fn validate_mapped_read(
        &self,
        store: &CanonicalTypeMapperStore,
        proof: &SourceMappedReadProof,
        globals: &CanonicalGlobalTypes,
        strict: Option<bool>,
    ) -> Result<(), DeclaredTypeError> {
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery);
        if globals != &self.globals
            || !proof.matches_context(globals, self.options)
            || proof.aliases != self.aliases
            || proof.jsdoc != self.jsdoc
            || strict != self.options.strict_function_types
            || proof.members.members().type_id() != proof.request.receiver()
        {
            return Err(invalid());
        }
        let mut current = self.clone();
        if !current.validating_mapped_reads.insert(proof.request) {
            return Err(invalid());
        }
        current.signature_instantiation_conditionals = None;
        current.completed = proof.conditionals.clone();
        current.produced.clear();
        current.values = proof.values.clone();
        current.returns = proof.returns.clone();
        current.instantiations = proof.operations.clone();
        current.recoveries.clear();
        current.semantic_results.clear();
        for conditional in &proof.conditionals {
            current.validate_completed_conditional(store, conditional)?;
        }
        for value in &proof.values {
            current.validate_value(store, value, globals, strict)?;
        }
        for returned in &proof.returns {
            current.validate_signature_return(store, returned, globals, strict)?;
        }
        for operation in &proof.operations {
            current.validate_operation(store, operation, globals, strict)?;
        }
        let actual = capture_source_mapped_members_identity(store, proof.request.receiver(), globals, &current)
            .map_err(|error| match error {
                MappedTypeError::Declared(error) if SourceQueryDemand::from_error(&error).is_some() => error,
                _ => invalid(),
            })?;
        if actual != proof.members {
            return Err(invalid());
        }
        match (proof.request, proof.value) {
            (SourceMappedReadRequest::Members { .. }, None) if proof.recovery_error.is_none() => Ok(()),
            (SourceMappedReadRequest::Value { member, .. }, Some(value)) => {
                let result = if let Some(recovery) = proof.recovery_error {
                    if store.intrinsic_bootstrap().is_none_or(|bootstrap| bootstrap.error_type != recovery) {
                        return Err(invalid());
                    }
                    validate_source_mapped_recovered_value_identity(store, &actual, member, value, globals, &current)
                } else {
                    validate_source_mapped_value_identity(store, &actual, member, value, globals, &current)
                };
                result
                    .map_err(|error| match error {
                        MappedTypeError::Declared(error) if SourceQueryDemand::from_error(&error).is_some() => error,
                        _ => invalid(),
                    })
            }
            _ => Err(invalid()),
        }
    }
}

impl CanonicalTypeQuery<'_, '_, '_, '_> {
    pub(super) fn resolve_mapped_query_demand(
        &mut self,
        request: SourceMappedReadRequest,
        node: NodeRef,
    ) -> Result<Option<TypeId>, DeclaredTypeError> {
        self.resolve_source_query_demand(SourceQueryDemand::Mapped(request), node)
    }

    pub(super) fn resolve_source_query_demand(
        &mut self,
        request: SourceQueryDemand,
        node: NodeRef,
    ) -> Result<Option<TypeId>, DeclaredTypeError> {
        let mark = self.instantiation_session.as_deref()
            .ok_or_else(|| type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery))?
            .limit_event_mark();
        let recoveries = (self.source_branch_recoveries.len(), self.source_conditional_recoveries.len());
        if !self.active_source_query_demands.insert(request) {
            return Err(request.unavailable());
        }
        let mut pending = vec![request];
        let mut completed = HashSet::new();
        let result = (|| {
        while let Some(request) = pending.last().copied() {
            let result = match request {
                SourceQueryDemand::Mapped(request) => self.resolve_mapped_query_demand_once(request, node),
                SourceQueryDemand::IndexedDiagnostic { node, object, index } => {
                    self.resolve_source_indexed_diagnostic_demand(node, object, index)
                }
            };
            match result {
                Ok(Some(recovery)) => return Ok(Some(recovery)),
                Ok(None) => {
                    pending.pop();
                    completed.insert(request);
                    self.active_source_query_demands.remove(&request);
                }
                Err(error) => {
                    if self.instantiation_session.as_deref()
                        .is_none_or(|session| session.limit_event_occurred_since(mark))
                        || self.source_branch_recoveries.len() != recoveries.0
                        || self.source_conditional_recoveries.len() != recoveries.1
                    {
                        return Err(error);
                    }
                    let Some(next) = SourceQueryDemand::from_error(&error) else {
                        return Err(error);
                    };
                    if completed.contains(&next) || !self.active_source_query_demands.insert(next) {
                        return Err(error);
                    }
                    pending.push(next);
                }
            }
        }
        Ok(None)
        })();
        for request in pending {
            self.active_source_query_demands.remove(&request);
        }
        result
    }

    fn resolve_mapped_query_demand_once(
        &mut self,
        request: SourceMappedReadRequest,
        node: NodeRef,
    ) -> Result<Option<TypeId>, DeclaredTypeError> {
        let context = self.source_query_context()?;
        let session = self.instantiation_session.as_deref_mut()
            .ok_or_else(|| type_node_unavailable(TypeNodeUnavailable::InvalidPreparedTypeQuery))?;
        let mut adapter = SourceTypeQueryAdapter { context, diagnostics: self.diagnostics };
        let result = adapter.resolve_mapped_read(self.store, request, session);
        self.global_this_members = adapter.context.members;
        self.completed_source_conditionals = adapter.context.completed;
        self.new_source_conditionals.extend(adapter.context.produced);
        self.completed_global_values = adapter.context.values;
        self.source_branch_recoveries = adapter.context.recoveries;
        self.source_conditional_recoveries = adapter.context.semantic_results;
        self.completed_source_returns = adapter.context.returns;
        self.completed_signature_instantiations = adapter.context.instantiations;
        match result.map_err(|error| mapped_type_error(error, node))? {
            SourceMappedReadOutcome::Complete(proof) if proof.request() == request => Ok(None),
            SourceMappedReadOutcome::Complete(_) => Err(request.missing_proof()),
            SourceMappedReadOutcome::LimitRecovery(type_) => Ok(Some(type_)),
            SourceMappedReadOutcome::RecoveredValue(value) => Ok(Some(value.recovery_type())),
            SourceMappedReadOutcome::RecoveredMembers(_) => Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidPreparedTypeQuery,
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic::production::{
        CanonicalCheckerContext, CanonicalCheckerOptions, GlobalMergeCompletion,
    };
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    };
    use ts_parser::parse_source_file;

    #[test]
    #[allow(clippy::too_many_lines)] // Keep retained cache, capture events and corruption checks together.
    fn mapped_read_retention_keeps_latest_proof_and_each_capture_event() {
        let library = parse_source_file("type Partial<T> = { [P in keyof T]?: T[P] };");
        let source = parse_source_file("interface Shape { value: string; other: number } type Weak = Partial<Shape>;");
        let library_file = FileId::new(30_000);
        let file = FileId::new(30_001);
        let mut binder = CanonicalBinder::new();
        for (parsed, id, path, default_library) in [
            (&library, library_file, "\"/retained-mapped-lib.d.ts\"", true),
            (&source, file, "\"/retained-mapped-source.d.ts\"", false),
        ] {
            assert!(parsed.diagnostics.is_empty());
            binder.bind_source_file_with_facts(
                &parsed.arena, parsed.source_file, id,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path), CanonicalSourceLanguage::TypeScript,
                    true, default_library, CanonicalModuleState::Script,
                ),
            ).unwrap();
            binder.bind_typescript_declaration_slice(&parsed.arena, id).unwrap();
        }
        let mut checker = CanonicalCheckerContext::new(
            binder.finish(), vec![(library_file, &library.arena), (file, &source.arena)],
            CanonicalCheckerOptions::default(),
        ).unwrap();
        let library_bound = checker.file(library_file).unwrap().1.clone();
        let source_bound = checker.file(file).unwrap().1.clone();
        let alias = source.arena.iter().find_map(|(node, record)| {
            (record.kind == SyntaxKind::TypeAliasDeclaration).then(|| {
                source_bound.symbol(NodeRef::new(source.arena.id(), file, node)).unwrap()
            })
        }).unwrap();
        let globals = checker.global_types().clone();
        let options = checker.options();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&library.arena, &library_bound), (&source.arena, &source_bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        ).unwrap();
        let mut diagnostics = checker.diagnostics().clone();
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut query = CanonicalTypeQuery::new_with_global_types_and_session(
            checker.store_mut_for_test(), &host, &globals, options, &mut session, &mut diagnostics,
        ).unwrap();
        let mapped = query.get_declared_type_of_symbol(alias).unwrap();
        let name = EscapedName::source("value");
        let property = query.get_property_of_source_object(mapped, name.as_ref()).unwrap().unwrap();
        let string = query.store.intrinsic_bootstrap().unwrap().string_type;
        let number = query.store.intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(property.type_, string);
        let mut context = query.source_query_context().unwrap();
        let members = context.instantiations.iter().find_map(|operation| match operation {
            SourceOperationProof::MappedRead(proof)
                if proof.request == (SourceMappedReadRequest::Members { receiver: mapped }) => Some(proof.clone()),
            _ => None,
        }).unwrap();
        let value = context.instantiations.iter().find_map(|operation| match operation {
            SourceOperationProof::MappedRead(proof)
                if proof.request == (SourceMappedReadRequest::Value { receiver: mapped, member: property.symbol }) => Some(proof.clone()),
            _ => None,
        }).unwrap();
        assert_eq!(context.instantiations.len(), 2);
        let reads = context.signature_instantiation_conditionals.as_ref().unwrap().clone();
        let event_start = reads.borrow().len();
        let mut latest = value.clone();
        latest.operations.push(SourceOperationProof::MappedRead(members.clone()));
        assert_eq!(context.validate_mapped_read(query.store, &latest, &globals, context.options.strict_function_types), Ok(()));
        for _ in 0..2 {
            context.retain_mapped_read(latest.clone()).unwrap();
            assert_eq!(context.instantiations.len(), 2);
            let retained = context.completed_source_mapped_read(latest.request).unwrap();
            assert!(retained.same_result(&latest));
            assert_eq!(retained.operations.len(), latest.operations.len());
            assert_eq!(context.validate_mapped_read(query.store, &retained, &globals, context.options.strict_function_types), Ok(()));
        }
        let events = reads.borrow()[event_start..].iter().filter_map(SourceQueryRead::operation).collect::<Vec<_>>();
        assert_eq!(events.len(), 2);
        for event in events {
            let SourceOperationProof::MappedRead(proof) = event else { unreachable!(); };
            assert!(proof.same_result(&latest));
            assert_eq!(proof.operations.len(), latest.operations.len());
        }
        let rejected_start = reads.borrow().len();
        let mut conflict = latest.clone();
        conflict.value = Some(number);
        assert!(context.retain_mapped_read(conflict).is_err());
        let mut wrong_context = latest.clone();
        wrong_context.options.strict_builtin_iterator_return = !context.options.strict_builtin_iterator_return;
        assert!(context.retain_mapped_read(wrong_context).is_err());
        assert_eq!(reads.borrow().len(), rejected_start);
        assert_eq!(context.instantiations.len(), 2);
        let original = query.store.value_symbol_links(property.symbol).unwrap().clone();
        let mut damaged = original.clone();
        damaged.resolved_type = Some(number);
        assert!(query.store.set_value_symbol_links(property.symbol, damaged.clone()));
        for _ in 0..2 {
            assert!(context.validate_mapped_read(query.store, &latest, &globals, context.options.strict_function_types).is_err());
            assert!(query.get_property_of_source_object(mapped, name.as_ref()).is_err());
            assert_eq!(query.store.value_symbol_links(property.symbol), Some(&damaged));
            assert_eq!(query.completed_signature_instantiations.len(), 2);
        }
        assert!(query.store.set_value_symbol_links(property.symbol, original));
        assert_eq!(context.validate_mapped_read(query.store, &latest, &globals, context.options.strict_function_types), Ok(()));
        let restored = query.get_property_of_source_object(mapped, name.as_ref()).unwrap().unwrap();
        assert_eq!(restored.symbol, property.symbol);
        assert_eq!(restored.type_, string);
        assert_eq!(query.completed_signature_instantiations.len(), 2);
        assert!(query.diagnostics.is_empty());
    }
}
