//! Each cached comparison keeps only the mapped operations it consumed.

use super::*;
use std::collections::BTreeSet;

enum ReadEvent {
    Proof(usize),
    Child(CacheHashKey),
}

#[derive(Default)]
pub(super) struct MappedRelationReads {
    nodes: HashMap<CacheHashKey, Vec<ReadEvent>>,
    active: Vec<CacheHashKey>,
    proofs: Vec<SourceMappedReadProof>,
}

impl MappedRelationReads {
    pub(super) fn enter(&mut self, key: CacheHashKey) {
        if let Some(parent) = self.active.last().copied() {
            self.nodes.entry(parent).or_default().push(ReadEvent::Child(key));
        }
        self.nodes.entry(key).or_default();
        self.active.push(key);
    }

    pub(super) fn leave(&mut self, key: CacheHashKey) {
        assert_eq!(self.active.pop(), Some(key));
    }

    pub(super) fn use_child(&mut self, child: CacheHashKey) {
        if let Some(key) = self.active.last().copied() {
            self.nodes.entry(key).or_default().push(ReadEvent::Child(child));
        }
    }

    pub(super) fn consumed(&self) -> &[SourceMappedReadProof] {
        &self.proofs
    }

    pub(super) fn consume(&mut self, proof: &SourceMappedReadProof) -> Result<(), RelationUnavailable> {
        let Some(key) = self.active.last().copied() else {
            return Ok(());
        };
        if self.proofs.iter().any(|previous| previous.request() == proof.request() && crate::semantic::relater::original_failure_proof_same!(concat!("mapped_proof.consume.same_result@", "mapped_cache.rs", ":", line!()), previous, proof, previous, proof)) {
            return crate::semantic::relater::original_failure_phase_relation_result!(concat!("mapped_cache.rs", ":", line!()), "mapped-proof-consume", Err(RelationUnavailable::InvalidStructuredMembers(proof.request().receiver())));
        }
        let index = self.proofs.len();
        self.proofs.push(proof.clone());
        self.nodes.entry(key).or_default().push(ReadEvent::Proof(index));
        Ok(())
    }

    pub(super) fn closure(&self, key: CacheHashKey) -> Vec<SourceMappedReadProof> {
        let mut pending = vec![key];
        let mut visited = HashSet::new();
        let mut uses = BTreeSet::new();
        while let Some(key) = pending.pop() {
            if !visited.insert(key) {
                continue;
            }
            for event in self.nodes.get(&key).into_iter().flatten() {
                match event {
                    ReadEvent::Proof(index) => { uses.insert(*index); }
                    ReadEvent::Child(child) => pending.push(*child),
                }
            }
        }
        // Sequence numbers keep the actual demand order through Maybe cycles.
        let mut requests = HashSet::new();
        uses.into_iter().filter_map(|index| {
            let proof = &self.proofs[index];
            requests.insert(proof.request()).then(|| proof.clone())
        }).collect()
    }
}

fn mapped_request_unavailable(request: SourceMappedReadRequest) -> RelationUnavailable {
    match request {
        SourceMappedReadRequest::Members { receiver } => RelationUnavailable::SourceMappedMembersDemand { receiver },
        SourceMappedReadRequest::Value { receiver, member } => RelationUnavailable::SourceMappedValueDemand { receiver, member },
    }
}

pub(super) fn admitted_mapped_proof<'a>(
    context: Option<GlobalThisRelationContext<'a>>,
    request: SourceMappedReadRequest,
) -> Result<&'a SourceMappedReadProof, RelationUnavailable> {
    context.and_then(|context| context.signature_instantiations.iter().find_map(|operation| {
        match operation {
            SourceOperationProof::MappedRead(proof) if proof.request() == request
                && (!proof.is_recovered_value()
                    || context.recovery_disposition == SourceRelationRecoveryDisposition::Assignment
                        && context.recovery_receiver == Some(request.receiver())) => Some(proof),
            _ => None,
        }
    })).ok_or_else(|| mapped_request_unavailable(request))
}

pub(super) fn replay_cached_mapped_proofs(
    proofs: &[SourceMappedReadProof],
    context: Option<GlobalThisRelationContext<'_>>,
) -> Result<Vec<SourceMappedReadProof>, RelationUnavailable> {
    proofs.iter().map(|expected| {
        let actual = admitted_mapped_proof(context, expected.request())?;
        if crate::semantic::relater::original_failure_proof_same!(concat!("mapped_proof.replay.same_result@", "mapped_cache.rs", ":", line!()), actual, expected, expected, actual) {
            return crate::semantic::relater::original_failure_phase_relation_result!(concat!("mapped_cache.rs", ":", line!()), "physical-proof-replay", Err(RelationUnavailable::InvalidStructuredMembers(expected.request().receiver())));
        }
        Ok(actual.clone())
    }).collect()
}

pub(super) fn source_mapped_endpoint_before_session(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    context: Option<GlobalThisRelationContext<'_>>,
) -> Result<Option<bool>, RelationUnavailable> {
    if context.is_none() || !matches!(store.type_payload(receiver).map(TypeRecord::data), Some(TypeData::Mapped(_))) {
        return Ok(None);
    }
    let proof = admitted_mapped_proof(context, SourceMappedReadRequest::Members { receiver })?;
    let structured = store.type_payload(receiver).and_then(|record| record.data().structured())
        .ok_or(RelationUnavailable::InvalidStructuredMembers(receiver))?;
    let properties = (!proof.members().properties().is_empty()).then_some(proof.members().properties());
    if structured.members != Some(proof.members().members())
        || structured.properties.as_deref() != properties
    {
        return Err(RelationUnavailable::InvalidStructuredMembers(receiver));
    }
    Ok(Some(true))
}
