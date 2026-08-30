//! Exact semantic kernel for direct calls and authenticated tagged templates.
//!
//! This is the dependency-closed fixed-signature branch of pinned
//! typescript-go `checkCallExpression`, `resolveCallExpression`, `resolveCall`,
//! `chooseOverload`, and `hasCorrectArity`. Syntax planning and expression
//! typing remain with the source checker. This module accepts an already-typed
//! callee and arguments, proves an ordered set of stored non-generic call
//! signatures, selects the first applicable fixed-arity candidate, and
//! projects its resolved return type. It never substitutes `any` for an
//! unsupported or malformed call.

use std::collections::HashSet;

use ts_ast::NodeRef;
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, MinArgumentCountFlags, RelationUnavailable,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    callable_sets::{
        StoredCallableSetValidation, validate_stored_callable_set,
        validate_stored_callable_set_with_array_targets,
    },
    callables::ValidatedSingleCallable,
    classes::{
        ClassBodyCallable, ClassHeritageMembersValidation, optional_constructor_parameter_type,
        validate_class_heritage_members,
    },
    instantiate::{InstantiationLimits, InstantiationSession},
    intersection_types::{IntersectionTypeError, intersect_property_types},
    links::ValueSymbolLinks,
    relation::RelationKind,
    signatures::{ElementFlags, Signature, SignatureFlags, SignatureKind, TupleElementInfo},
    tuple_types::{CanonicalTupleTypeRequest, TupleTypeError},
    type_records::{ObjectTypeData, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// Call-like syntax presented to the direct-call semantic kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallForm {
    Call,
    /// Admitted only through an authenticated class-body target.
    New,
    #[allow(dead_code)] // Source syntax integration is staged separately.
    TaggedTemplate,
}

/// Syntax-neutral input after the source checker has typed the callee and every
/// argument expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectCallRequest<'a> {
    pub(super) form: DirectCallForm,
    pub(super) optional_chain: bool,
    pub(super) type_argument_count: usize,
    pub(super) has_spread_argument: bool,
    pub(super) callee: TypeId,
    pub(super) arguments: &'a [TypeId],
}

/// Valid TypeScript semantics outside the first direct-call slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallUnsupported {
    Form(DirectCallForm),
    OptionalChain,
    TypeArguments { count: usize },
    SpreadArgument,
    NotExactSingleCallable(TypeId),
    PendingCallable(TypeId),
    GenericSignature(SignatureId),
    ExplicitThisParameter(SignatureId),
    RestSignature(SignatureId),
    UnresolvedReturnType(SignatureId),
    OverloadFailureRecovery(TypeId),
}

/// Malformed callable storage or foreign semantic identities.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallInvariant {
    InvalidCalleeType(TypeId),
    MalformedCallable(TypeId),
    InvalidArgumentType {
        index: usize,
        type_: TypeId,
    },
    CallableOwnerMismatch {
        callee: TypeId,
        owner: TypeId,
    },
    InvalidSignature(SignatureId),
    SignatureParameterCountMismatch {
        signature: SignatureId,
        stored: usize,
        projected: usize,
    },
    SignatureMinimumMismatch {
        signature: SignatureId,
        stored: i32,
        projected: usize,
    },
    InvalidMinimumArgumentCount {
        signature: SignatureId,
        minimum: usize,
        maximum: usize,
    },
    InvalidResolvedMinimumArgumentCount {
        signature: SignatureId,
        cached: i32,
        expected: usize,
    },
    InvalidParameterType {
        signature: SignatureId,
        index: usize,
        type_: TypeId,
    },
    InvalidRestParameterType {
        signature: SignatureId,
        type_: TypeId,
    },
    MalformedParameterUnion {
        signature: SignatureId,
        index: usize,
        type_: TypeId,
    },
    SignatureReturnMismatch(SignatureId),
    InvalidReturnType {
        signature: SignatureId,
        type_: TypeId,
    },
    ParameterProjectionCapacity(SignatureId),
    InvalidParameterProjection(SignatureId),
    InvalidOverloadFailureSignature(SignatureId),
}

/// A capability, provenance, or relation failure. Ordinary call diagnostics
/// are represented by [`DirectCallApplicability`] instead.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallError {
    Unsupported(DirectCallUnsupported),
    Invariant(DirectCallInvariant),
    Relation(RelationUnavailable),
}

impl From<DirectCallUnsupported> for DirectCallError {
    fn from(error: DirectCallUnsupported) -> Self {
        Self::Unsupported(error)
    }
}

impl From<DirectCallInvariant> for DirectCallError {
    fn from(error: DirectCallInvariant) -> Self {
        Self::Invariant(error)
    }
}

impl From<RelationUnavailable> for DirectCallError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

/// Whether the selected signature's resolved return is exactly void-like for
/// `checkCallExpression`'s direct `TypeFlags::VOID` branch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallReturnKind {
    Void,
    Value,
}

/// The contextual target paired with one already-typed argument.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectCallArgumentTarget {
    pub(super) index: usize,
    pub(super) argument_type: TypeId,
    pub(super) parameter_type: TypeId,
}

/// Signature and return projection retained for both valid and erroneous calls.
/// A failed overload group has a separate marked recovery signature. Its
/// diagnostic still names the real overload that failed applicability.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectCallProjection {
    pub(super) callee: TypeId,
    pub(super) signature: SignatureId,
    pub(super) minimum_argument_count: usize,
    pub(super) maximum_argument_count: usize,
    pub(super) has_effective_rest: bool,
    pub(super) argument_targets: Vec<DirectCallArgumentTarget>,
    pub(super) rest_argument_target: Option<DirectCallArgumentTarget>,
    pub(super) return_type: TypeId,
    pub(super) return_kind: DirectCallReturnKind,
}

/// Ordinary applicability outcome for the one selected candidate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallApplicability {
    Applicable,
    TooFewArguments {
        expected_at_least: usize,
        actual: usize,
    },
    TooManyArguments {
        expected_at_most: usize,
        actual: usize,
    },
    ArgumentNotAssignable {
        index: usize,
        argument_type: TypeId,
        parameter_type: TypeId,
    },
    RestArgumentsNotAssignable {
        index: usize,
        argument_type: TypeId,
        parameter_type: TypeId,
    },
}

#[derive(Clone, Debug)]
enum RestParameterShape {
    Array {
        type_: TypeId,
        element: TypeId,
    },
    MissingGlobalArray {
        type_: TypeId,
        indexed_type: TypeId,
    },
    Tuple {
        type_: TypeId,
        elements: Vec<TypeId>,
        infos: Vec<TupleElementInfo>,
        fixed_length: usize,
        combined_flags: ElementFlags,
    },
    Union {
        type_: TypeId,
        members: Vec<Self>,
    },
    Intrinsic(TypeId),
}

impl RestParameterShape {
    fn type_id(&self) -> TypeId {
        match self {
            Self::Array { type_, .. }
            | Self::MissingGlobalArray { type_, .. }
            | Self::Tuple { type_, .. }
            | Self::Union { type_, .. }
            | Self::Intrinsic(type_) => *type_,
        }
    }

    fn has_effective_rest(&self) -> bool {
        match self {
            Self::Tuple { combined_flags, .. } => combined_flags.intersects(ElementFlags::VARIABLE),
            _ => true,
        }
    }

    fn parameter_count(&self) -> usize {
        match self {
            Self::Tuple { fixed_length, .. } => {
                *fixed_length + usize::from(self.has_effective_rest())
            }
            _ => 1,
        }
    }
}

/// Complete result of the first direct-call semantic cut.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectCallResolution {
    pub(super) projection: DirectCallProjection,
    pub(super) applicability: DirectCallApplicability,
    pub(super) overload_failure: Option<DirectCallOverloadFailure>,
}

/// Error selection is separate from the signature used to type a failed call.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DirectCallOverloadFailure {
    Argument {
        signature: SignatureId,
        failed_candidates: usize,
    },
    Arity {
        closest_signature: SignatureId,
        minimum_argument_count: usize,
        maximum_argument_count: usize,
        gap: Option<(usize, usize)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OverloadFailureParameter {
    symbol: SemanticSymbolId,
    source: SemanticSymbolId,
    type_: TypeId,
}

/// Immutable inputs and outputs of one fixed overload-failure signature.
/// This receipt does not add the recovery signature to the callable's overloads.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct OverloadFailureSignature {
    signature: SignatureId,
    callables: Vec<ValidatedSingleCallable>,
    parameters: Vec<OverloadFailureParameter>,
    return_type: TypeId,
    flags: SignatureFlags,
    declaration: Option<NodeRef>,
    minimum_argument_count: i32,
    array_targets: CanonicalArrayTargets,
}

/// A checked argument list that does not claim a signature return type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectCallArgumentResolution {
    callee: TypeId,
    signature: SignatureId,
    minimum_argument_count: usize,
    maximum_argument_count: usize,
    has_effective_rest: bool,
    argument_targets: Vec<DirectCallArgumentTarget>,
    rest_argument_target: Option<DirectCallArgumentTarget>,
    applicability: DirectCallApplicability,
}

impl DirectCallArgumentResolution {
    pub(super) const fn signature(&self) -> SignatureId {
        self.signature
    }

    fn with_return_type(
        self,
        return_type: TypeId,
        return_kind: DirectCallReturnKind,
    ) -> DirectCallResolution {
        DirectCallResolution {
            projection: DirectCallProjection {
                callee: self.callee,
                signature: self.signature,
                minimum_argument_count: self.minimum_argument_count,
                maximum_argument_count: self.maximum_argument_count,
                has_effective_rest: self.has_effective_rest,
                argument_targets: self.argument_targets,
                rest_argument_target: self.rest_argument_target,
                return_type,
                return_kind,
            },
            applicability: self.applicability,
            overload_failure: None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ClassBodyInvocationResolution {
    Resolved(DirectCallResolution),
    PendingReturn(DirectCallArgumentResolution),
}

/// Resolves the dependency-closed non-generic direct-call branch.
///
/// The source caller supplies immutable options and authoritative globals.
/// Projection can create canonical position unions and rest-argument tuples.
pub(super) fn resolve_direct_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
) -> Result<DirectCallResolution, DirectCallError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_direct_call_with_session(
        store,
        global_types,
        strict_function_types,
        request,
        None,
        &mut session,
    )
}

/// Uses the caller's session for overload relations and recovery type construction.
pub(super) fn resolve_direct_call_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    existing_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<DirectCallResolution, DirectCallError> {
    validate_direct_call_form(request)?;
    if store.type_payload(request.callee).is_none() {
        return Err(DirectCallInvariant::InvalidCalleeType(request.callee).into());
    }
    validate_argument_types(store, request.arguments)?;
    validate_tagged_template_argument(store, request)?;

    let projection = match validate_stored_callable_set_with_array_targets(
        store,
        request.callee,
        Some(CanonicalArrayTargets::from_global_types(global_types)),
    ) {
        StoredCallableSetValidation::NotCallable => {
            return Err(DirectCallUnsupported::NotExactSingleCallable(request.callee).into());
        }
        StoredCallableSetValidation::Pending { .. } => {
            return Err(DirectCallUnsupported::PendingCallable(request.callee).into());
        }
        StoredCallableSetValidation::Malformed { .. } => {
            return Err(DirectCallInvariant::MalformedCallable(request.callee).into());
        }
        StoredCallableSetValidation::Valid { projection, .. } => projection,
    };
    if projection.owner != request.callee
        || !projection.construct_signatures.is_empty()
        || projection.call_signatures.is_empty()
    {
        return Err(DirectCallUnsupported::NotExactSingleCallable(request.callee).into());
    }
    resolve_direct_call_candidates_with_session(
        store,
        global_types,
        strict_function_types,
        request,
        &projection.call_signatures,
        existing_signature,
        session,
    )
}

pub(super) fn resolve_direct_call_candidates_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    callables: &[ValidatedSingleCallable],
    existing_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<DirectCallResolution, DirectCallError> {
    validate_direct_invocation_options(request)?;
    validate_argument_types(store, request.arguments)?;
    if let Some(existing) = existing_signature
        && !callables
            .iter()
            .any(|callable| callable.signature == existing)
        && (request.form != DirectCallForm::Call
            || !overload_failure_signature_matches(store, request.callee, existing, callables)
            || overload_failure_signature_return_type(
                store,
                existing,
                Some(CanonicalArrayTargets::from_global_types(global_types)),
            )
            .is_err())
    {
        return Err(DirectCallInvariant::InvalidOverloadFailureSignature(existing).into());
    }
    let resolution = (|| {
        let original_callables = callables;
        let callables = reorder_direct_call_candidates(store, request.callee, callables)?;
        let candidate_count = callables.len();
        let mut candidates = Vec::with_capacity(candidate_count);
        for callable in &callables {
            match project_validated_direct_call(store, Some(global_types), request, callable) {
                Ok(candidate) => candidates.push(candidate),
                Err(DirectCallError::Unsupported(DirectCallUnsupported::Form(
                    DirectCallForm::TaggedTemplate,
                ))) if candidate_count > 1 => {}
                Err(error) => return Err(error),
            }
        }
        if candidates.is_empty() {
            return Err(DirectCallUnsupported::Form(request.form).into());
        }
        if candidate_count == 1 {
            let mut resolution = candidates
                .into_iter()
                .next()
                .expect("the exact-single candidate count was checked");
            if resolution.applicability != DirectCallApplicability::Applicable {
                return Ok(resolution);
            }
            resolution.applicability =
                check_argument_applicability(&resolution.projection, |source, target| {
                    store.is_type_assignable_to_with_session(
                        source,
                        target,
                        Some(global_types),
                        Some(strict_function_types),
                        session,
                    )
                })?;
            return Ok(resolution);
        }

        let mut argument_failures = Vec::with_capacity(candidates.len());
        if let Some(candidate) =
            choose_applicable_overload(&candidates, &mut argument_failures, |source, target| {
                store.is_type_related_to_with_session(
                    source,
                    target,
                    RelationKind::Subtype,
                    Some(global_types),
                    Some(strict_function_types),
                    session,
                )
            })?
        {
            return Ok(candidate);
        }
        if let Some(candidate) =
            choose_applicable_overload(&candidates, &mut argument_failures, |source, target| {
                store.is_type_assignable_to_with_session(
                    source,
                    target,
                    Some(global_types),
                    Some(strict_function_types),
                    session,
                )
            })?
        {
            return Ok(candidate);
        }

        if request.form == DirectCallForm::Call
            && callables
                .iter()
                .all(|callable| callable.rest_parameter.is_none())
        {
            return recover_fixed_call_overload(
                store,
                global_types,
                strict_function_types,
                request,
                &callables,
                original_callables,
                &candidates,
                &argument_failures,
                existing_signature,
                session,
            );
        }
        if let Some(candidate) = recover_direct_call_overload(
            store,
            global_types,
            strict_function_types,
            request,
            &candidates,
            session,
        )? {
            return Ok(candidate);
        }
        Err(DirectCallUnsupported::OverloadFailureRecovery(request.callee).into())
    })()?;
    if let Some(existing) = existing_signature
        && existing != resolution.projection.signature
    {
        return Err(DirectCallInvariant::InvalidOverloadFailureSignature(existing).into());
    }
    Ok(resolution)
}

/// Applies the ordinary fixed-signature engine to an authenticated class-body target.
#[cfg(test)]
pub(super) fn resolve_class_body_invocation(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    target: &ClassBodyCallable,
) -> Result<ClassBodyInvocationResolution, DirectCallError> {
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    resolve_class_body_invocation_with_session(
        store,
        global_types,
        strict_function_types,
        request,
        target,
        None,
        &mut session,
    )
}

pub(super) fn resolve_class_body_invocation_with_session(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    target: &ClassBodyCallable,
    existing_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<ClassBodyInvocationResolution, DirectCallError> {
    if !matches!(
        (request.form, target.kind()),
        (DirectCallForm::Call, SignatureKind::Call)
            | (DirectCallForm::New, SignatureKind::Construct)
    ) {
        return Err(DirectCallUnsupported::Form(request.form).into());
    }
    validate_direct_invocation_options(request)?;
    validate_argument_types(store, request.arguments)?;
    if let Some(overloads) = target.overloads() {
        if target.kind() != SignatureKind::Call
            || request.callee != target.callable().owner
            || target.pending_return_body().is_some()
            || super::classes::source_class_method_overloads(store, request.callee)
                .ok()
                .flatten()
                .as_ref()
                != Some(overloads)
        {
            return Err(DirectCallInvariant::MalformedCallable(request.callee).into());
        }
        return resolve_direct_call_candidates_with_session(
            store,
            global_types,
            strict_function_types,
            request,
            &overloads.signatures,
            existing_signature,
            session,
        )
        .map(ClassBodyInvocationResolution::Resolved);
    }
    let callable = target.callable();
    if let Some(existing) = existing_signature
        && existing != callable.signature
    {
        return Err(DirectCallInvariant::InvalidOverloadFailureSignature(existing).into());
    }
    let invalid = || DirectCallInvariant::MalformedCallable(callable.owner);
    let owner = store.type_payload(callable.owner).ok_or_else(invalid)?;
    let structured = owner.data().structured().ok_or_else(invalid)?;
    let signatures = structured.signatures.as_deref().ok_or_else(invalid)?;
    if structured.call_signature_count > signatures.len() {
        return Err(invalid().into());
    }
    let (calls, constructs) = signatures.split_at(structured.call_signature_count);
    let (selected, other) = match target.kind() {
        SignatureKind::Call => (calls, constructs),
        SignatureKind::Construct => (constructs, calls),
    };
    let signature = validate_signature_parameters(store, callable)?;
    if selected != [callable.signature]
        || !other.is_empty()
        || signature.flags().contains(SignatureFlags::CONSTRUCT)
            != (target.kind() == SignatureKind::Construct)
        || signature.declaration() != target.declaration()
        || signature.resolved_return_type() != callable.return_type
        || target.pending_return_body().is_some()
            && (target.kind() != SignatureKind::Call || callable.return_type.is_some())
    {
        return Err(invalid().into());
    }
    if target.kind() == SignatureKind::Construct {
        let instance = callable.return_type.ok_or_else(invalid)?;
        if store.type_payload(instance).and_then(TypeRecord::symbol) != Some(target.class_symbol())
            || validate_class_heritage_members(store, instance)
                != ClassHeritageMembersValidation::Valid
        {
            return Err(invalid().into());
        }
    }
    validate_class_call_parameter_types(store, target, signature)?;
    if target.pending_return_body().is_some() {
        let arguments = check_validated_class_call_arguments(
            store,
            global_types,
            strict_function_types,
            request,
            callable,
            session,
        )?;
        return Ok(ClassBodyInvocationResolution::PendingReturn(arguments));
    }
    let mut resolution =
        project_validated_direct_call(store, Some(global_types), request, callable)?;
    if resolution.applicability == DirectCallApplicability::Applicable {
        resolution.applicability =
            check_argument_applicability(&resolution.projection, |source, target| {
                store.is_type_assignable_to_with_session(
                    source,
                    target,
                    Some(global_types),
                    Some(strict_function_types),
                    session,
                )
            })?;
    }
    Ok(ClassBodyInvocationResolution::Resolved(resolution))
}

fn validate_class_call_parameter_types(
    store: &CanonicalTypeMapperStore,
    target: &ClassBodyCallable,
    signature: &Signature,
) -> Result<(), DirectCallError> {
    let callable = target.callable();
    let invalid = || DirectCallInvariant::MalformedCallable(callable.owner);
    for (symbol, projected) in signature.parameters().iter().zip(
        callable
            .parameters
            .iter()
            .chain(callable.rest_parameter.iter()),
    ) {
        let local = store
            .value_symbol_links(*symbol)
            .and_then(|links| links.resolved_type)
            .ok_or_else(invalid)?;
        if local == *projected {
            continue;
        }
        if target.kind() != SignatureKind::Construct {
            return Err(invalid().into());
        }
        let declaration = store
            .symbol(*symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or_else(invalid)?;
        // A's sealed constructor projection owns default/optional admission.
        // Its call type may add undefined without widening the body-local type.
        let expected = optional_constructor_parameter_type(store, local, true, declaration)
            .map_err(|_| invalid())?;
        if expected != Some(*projected) {
            return Err(invalid().into());
        }
    }
    Ok(())
}

/// Keeps specialized overloads first and reverses merged declaration groups.
pub(super) fn reorder_direct_call_candidates<'a>(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    callables: &'a [ValidatedSingleCallable],
) -> Result<Vec<&'a ValidatedSingleCallable>, DirectCallError> {
    let shared_declaration_owner = store
        .type_payload(callee)
        .and_then(TypeRecord::symbol)
        .and_then(|owner| store.symbol(owner))
        .and_then(|owner| owner.declarations())
        .is_some_and(|declarations| {
            callables.iter().all(|callable| {
                store
                    .signature(callable.signature)
                    .and_then(Signature::declaration)
                    .is_some_and(|declaration| declarations.contains(&declaration))
            })
        });
    let mut ordered = Vec::with_capacity(callables.len());
    let mut previous_parent = None;
    let mut declaration_index = 0;
    let mut cutoff_index = 0;
    let mut specialized_count = 0;

    for callable in callables {
        let signature = store
            .signature(callable.signature)
            .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?;
        if shared_declaration_owner {
            let parent = signature
                .declaration()
                .and_then(|declaration| store.source_node_parent(declaration));
            if previous_parent.is_some() && previous_parent == parent {
                declaration_index += 1;
            } else {
                previous_parent = parent;
                declaration_index = cutoff_index;
            }
        } else {
            declaration_index = ordered.len();
        }

        let insertion_index = if signature
            .flags()
            .contains(SignatureFlags::HAS_LITERAL_TYPES)
        {
            let index = specialized_count;
            specialized_count += 1;
            cutoff_index += 1;
            index
        } else {
            declaration_index
        };
        ordered.insert(insertion_index, callable);
    }

    Ok(ordered)
}

fn choose_applicable_overload(
    candidates: &[DirectCallResolution],
    argument_failures: &mut Vec<(SignatureId, DirectCallApplicability)>,
    mut is_related: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<Option<DirectCallResolution>, DirectCallError> {
    argument_failures.clear();
    for candidate in candidates {
        if candidate.applicability != DirectCallApplicability::Applicable {
            continue;
        }
        let applicability = check_argument_applicability(&candidate.projection, &mut is_related)?;
        if applicability == DirectCallApplicability::Applicable {
            let mut selected = candidate.clone();
            selected.applicability = applicability;
            return Ok(Some(selected));
        }
        argument_failures.push((candidate.projection.signature, applicability));
    }
    Ok(None)
}

/// Mirrors the fixed, non-generic part of `getCandidateForOverloadFailure`.
#[allow(clippy::too_many_arguments)]
fn recover_fixed_call_overload(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    callables: &[&ValidatedSingleCallable],
    original_callables: &[ValidatedSingleCallable],
    candidates: &[DirectCallResolution],
    argument_failures: &[(SignatureId, DirectCallApplicability)],
    existing_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<DirectCallResolution, DirectCallError> {
    if let Err(established) = store.claim_strict_function_types(strict_function_types) {
        return Err(RelationUnavailable::StrictFunctionTypesOptionMismatch {
            established,
            requested: strict_function_types,
        }
        .into());
    }
    let class_method = store
        .type_payload(request.callee)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|method| {
            method.flags().contains(SymbolFlags::METHOD)
                && method
                    .parent()
                    .and_then(|owner| store.symbol(owner))
                    .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
        });
    if class_method
        && super::classes::source_class_method_overloads(store, request.callee)
            .ok()
            .flatten()
            .is_none()
    {
        return Err(DirectCallUnsupported::OverloadFailureRecovery(request.callee).into());
    }
    let first = candidates
        .first()
        .ok_or(DirectCallInvariant::MalformedCallable(request.callee))?;
    let (failure, applicability) =
        if let Some(&(signature, applicability)) = argument_failures.last() {
            (
                DirectCallOverloadFailure::Argument {
                    signature,
                    failed_candidates: argument_failures.len(),
                },
                applicability,
            )
        } else {
            // Arity diagnostics use the original visible order, before literal
            // overloads move to the front of the applicability search.
            let arity_candidates = original_callables
                .iter()
                .map(|callable| {
                    candidates
                        .iter()
                        .find(|candidate| candidate.projection.signature == callable.signature)
                        .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let closest_candidate = arity_candidates
                .first()
                .ok_or(DirectCallInvariant::MalformedCallable(request.callee))?;
            let mut minimum = closest_candidate.projection.minimum_argument_count;
            let mut maximum = closest_candidate.projection.maximum_argument_count;
            let mut closest = closest_candidate.projection.signature;
            let mut below = None;
            let mut above = None;
            for candidate in arity_candidates {
                let min = candidate.projection.minimum_argument_count;
                let max = candidate.projection.maximum_argument_count;
                if min < minimum {
                    minimum = min;
                    closest = candidate.projection.signature;
                }
                maximum = maximum.max(max);
                if min < request.arguments.len() {
                    below = Some(below.map_or(min, |previous: usize| previous.max(min)));
                }
                if request.arguments.len() < max {
                    above = Some(above.map_or(max, |previous: usize| previous.min(max)));
                }
            }
            let gap = if minimum < request.arguments.len() && request.arguments.len() < maximum {
                Some(
                    below
                        .zip(above)
                        .ok_or(DirectCallInvariant::MalformedCallable(request.callee))?,
                )
            } else {
                None
            };
            (
                DirectCallOverloadFailure::Arity {
                    closest_signature: closest,
                    minimum_argument_count: minimum,
                    maximum_argument_count: maximum,
                    gap,
                },
                first.applicability,
            )
        };
    let callable = get_fixed_overload_failure_signature(
        store,
        global_types,
        request.callee,
        callables,
        existing_signature,
        session,
    )?;
    let mut resolution =
        project_validated_direct_call(store, Some(global_types), request, &callable)?;
    // A union of parameter types can accept the arguments. That does not turn
    // this failed call into a successful overload selection.
    resolution.applicability = applicability;
    resolution.overload_failure = Some(failure);
    Ok(resolution)
}

fn overload_failure_type_error(
    callee: TypeId,
    signature: SignatureId,
    error: LiteralTypeCacheError,
) -> DirectCallError {
    match error {
        LiteralTypeCacheError::UnsupportedUnionConstituent(_) => {
            DirectCallUnsupported::OverloadFailureRecovery(callee).into()
        }
        LiteralTypeCacheError::Capacity => {
            DirectCallInvariant::ParameterProjectionCapacity(signature).into()
        }
        _ => DirectCallInvariant::InvalidOverloadFailureSignature(signature).into(),
    }
}

fn overload_failure_return_type(
    store: &mut CanonicalTypeMapperStore,
    callee: TypeId,
    signature: SignatureId,
    returns: &[TypeId],
    array_targets: CanonicalArrayTargets,
) -> Result<TypeId, DirectCallError> {
    match intersect_property_types(store, returns) {
        Ok(type_) => Ok(type_),
        Err(IntersectionTypeError::UnsupportedPropertyType(_)) => store
            .canonical_intersection_type_with_array_targets(returns, None, Some(array_targets))
            .map_err(|error| match error {
                IntersectionTypeError::UnsupportedConstituent(_)
                | IntersectionTypeError::UnsupportedPropertyType(_) => {
                    DirectCallUnsupported::OverloadFailureRecovery(callee).into()
                }
                IntersectionTypeError::Capacity => {
                    DirectCallInvariant::ParameterProjectionCapacity(signature).into()
                }
                _ => DirectCallInvariant::InvalidOverloadFailureSignature(signature).into(),
            }),
        Err(_) => Err(DirectCallInvariant::InvalidOverloadFailureSignature(signature).into()),
    }
}

fn get_fixed_overload_failure_signature(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    callee: TypeId,
    callables: &[&ValidatedSingleCallable],
    existing_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<ValidatedSingleCallable, DirectCallError> {
    let first = callables
        .first()
        .ok_or(DirectCallInvariant::MalformedCallable(callee))?;
    let key = (
        callee,
        callables
            .iter()
            .map(|callable| callable.signature)
            .collect::<Vec<_>>(),
    );
    let array_targets = CanonicalArrayTargets::from_global_types(global_types);
    if let Some(cached) = store.overload_failure_signatures.get(&key) {
        if existing_signature.is_some_and(|existing| existing != cached.signature)
            || store.overload_failure_signature_keys.get(&cached.signature) != Some(&key)
            || cached.array_targets != array_targets
            || !cached.callables.iter().eq(callables.iter().copied())
            || !overload_failure_signature_is_exact(store, cached)
        {
            return Err(
                DirectCallInvariant::InvalidOverloadFailureSignature(cached.signature).into(),
            );
        }
        return Ok(cached.callable(callee));
    }
    if let Some(existing) = existing_signature {
        return Err(DirectCallInvariant::InvalidOverloadFailureSignature(existing).into());
    }
    let mut flags = SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE;
    let mut minimum = usize::MAX;
    let mut maximum = 0;
    let mut returns = Vec::with_capacity(callables.len());
    for callable in callables {
        let signature = validate_signature_parameters(store, callable)?;
        if callable.owner != callee
            || callable.rest_parameter.is_some()
            || !signature.type_parameters().is_empty()
            || signature.this_parameter().is_some()
            || signature.flags().intersects(
                SignatureFlags::CONSTRUCT
                    | SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE,
            )
        {
            return Err(DirectCallUnsupported::OverloadFailureRecovery(callee).into());
        }
        flags |= signature.flags() & SignatureFlags::HAS_LITERAL_TYPES;
        minimum = minimum.min(signature.parameters().len());
        maximum = maximum.max(signature.parameters().len());
        let return_type =
            callable
                .return_type
                .ok_or(DirectCallUnsupported::UnresolvedReturnType(
                    callable.signature,
                ))?;
        store
            .validate_union_constituent_with_array_targets(array_targets, return_type)
            .map_err(|error| overload_failure_type_error(callee, callable.signature, error))?;
        returns.push(return_type);
    }
    let return_type =
        overload_failure_return_type(store, callee, first.signature, &returns, array_targets)?;
    let declaration = store
        .signature(first.signature)
        .ok_or(DirectCallInvariant::InvalidSignature(first.signature))?
        .declaration();
    let minimum_argument_count = i32::try_from(minimum)
        .map_err(|_| DirectCallInvariant::ParameterProjectionCapacity(first.signature))?;
    let mut parameter_types = Vec::with_capacity(maximum);
    for index in 0..maximum {
        let mut types = Vec::new();
        let mut source = None;
        for callable in callables {
            if let Some(&type_) = callable.parameters.get(index) {
                types.push(type_);
                let symbol = store
                    .signature(callable.signature)
                    .and_then(|signature| signature.parameters().get(index))
                    .copied()
                    .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?;
                source.get_or_insert(symbol);
            }
        }
        let source = source.ok_or(DirectCallInvariant::InvalidSignature(first.signature))?;
        let type_ = store
            .expression_union_type_with_global_types_and_session(
                global_types,
                &types,
                UnionReduction::Subtype,
                session,
            )
            .map_err(|error| overload_failure_type_error(callee, first.signature, error))?;
        parameter_types.push((source, type_));
    }
    if !store.try_reserve_signatures(1)
        || !store.try_reserve_checker_symbol_allocations(maximum, 0)
        || !store.try_reserve_value_symbol_links(maximum)
        || store.overload_failure_signatures.try_reserve(1).is_err()
        || store
            .overload_failure_signature_keys
            .try_reserve(1)
            .is_err()
    {
        return Err(DirectCallInvariant::ParameterProjectionCapacity(first.signature).into());
    }
    let mut parameters = Vec::with_capacity(maximum);
    for (source, type_) in parameter_types {
        let original = store
            .symbol(source)
            .expect("the overload provider validated its parameter");
        let flags = original.flags();
        let name = original.name().to_owned();
        let check_flags = original.check_flags() & CheckFlags::READONLY;
        let declarations = original.declarations().map(<[_]>::to_vec);
        let value_declaration = original.value_declaration();
        let parent = original.parent();
        let name_type = store
            .value_symbol_links(source)
            .and_then(|links| links.name_type);
        let symbol = store.alloc_transient_symbol(flags, name, check_flags);
        assert!(store.set_symbol_declarations(symbol, declarations, value_declaration));
        assert!(store.set_symbol_relationships(symbol, None, None, parent, None));
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                target: Some(source),
                name_type,
                ..ValueSymbolLinks::default()
            }
        ));
        parameters.push(OverloadFailureParameter {
            symbol,
            source,
            type_,
        });
    }
    let signature = store
        .alloc_signature(
            flags,
            declaration,
            Vec::new(),
            None,
            parameters
                .iter()
                .map(|parameter| parameter.symbol)
                .collect(),
            Some(return_type),
            None,
            minimum_argument_count,
        )
        .expect("overload failure signature inputs were validated and reserved");
    let receipt = OverloadFailureSignature {
        signature,
        callables: callables
            .iter()
            .map(|callable| (**callable).clone())
            .collect(),
        parameters,
        return_type,
        flags,
        declaration,
        minimum_argument_count,
        array_targets,
    };
    let result = receipt.callable(callee);
    assert!(
        store
            .overload_failure_signature_keys
            .insert(signature, key.clone())
            .is_none()
    );
    assert!(
        store
            .overload_failure_signatures
            .insert(key, receipt)
            .is_none()
    );
    Ok(result)
}

impl OverloadFailureSignature {
    fn callable(&self, owner: TypeId) -> ValidatedSingleCallable {
        ValidatedSingleCallable {
            owner,
            signature: self.signature,
            parameters: self
                .parameters
                .iter()
                .map(|parameter| parameter.type_)
                .collect(),
            rest_parameter: None,
            min_argument_count: usize::try_from(self.minimum_argument_count)
                .expect("the recovery minimum was checked before publication"),
            return_type: Some(self.return_type),
            strict_variance_exempt: self.callables[0].strict_variance_exempt,
        }
    }
}

fn overload_failure_signature_is_exact(
    store: &CanonicalTypeMapperStore,
    receipt: &OverloadFailureSignature,
) -> bool {
    let Some(signature) = store.signature(receipt.signature) else {
        return false;
    };
    if signature.flags() != receipt.flags
        || signature.declaration() != receipt.declaration
        || signature.min_argument_count() != receipt.minimum_argument_count
        || signature.resolved_return_type() != Some(receipt.return_type)
        || signature.parameters().len() != receipt.parameters.len()
        || !signature.type_parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.target().is_some()
        || signature.mapper().is_some()
        || signature.composite().is_some()
        || signature.isolated_signature_type().is_some()
        || signature.resolved_type_predicate().is_some()
        || receipt
            .callables
            .iter()
            .any(|callable| callable.signature == receipt.signature)
    {
        return false;
    }
    for (symbol, parameter) in signature.parameters().iter().zip(&receipt.parameters) {
        let Some(original) = store.symbol(parameter.source) else {
            return false;
        };
        let Some(combined) = store.symbol(*symbol) else {
            return false;
        };
        if *symbol != parameter.symbol
            || store.get_merged_symbol(*symbol) != Some(*symbol)
            || combined.flags() != original.flags() | SymbolFlags::TRANSIENT
            || combined.check_flags() != original.check_flags() & CheckFlags::READONLY
            || combined.name() != original.name()
            || combined.declarations() != original.declarations()
            || combined.value_declaration() != original.value_declaration()
            || combined.parent() != original.parent()
            || combined.members().is_some()
            || combined.exports().is_some()
            || combined.export_symbol().is_some()
            || store.value_symbol_links(*symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(parameter.type_),
                    target: Some(parameter.source),
                    name_type: store
                        .value_symbol_links(parameter.source)
                        .and_then(|links| links.name_type),
                    ..ValueSymbolLinks::default()
                })
            || store
                .validate_union_constituent_with_array_targets(
                    receipt.array_targets,
                    parameter.type_,
                )
                .is_err()
        {
            return false;
        }
    }
    store
        .validate_union_constituent_with_array_targets(receipt.array_targets, receipt.return_type)
        .is_ok()
        && receipt.callables.first().is_some_and(|first| {
            get_min_argument_count_with_array_targets(
                store,
                Some(receipt.array_targets),
                &receipt.callable(first.owner),
                MinArgumentCountFlags::NONE,
            )
            .is_ok()
        })
}

/// A call cache can retain only a failure signature from this exact group.
pub(super) fn overload_failure_signature_matches(
    store: &CanonicalTypeMapperStore,
    callee: TypeId,
    signature: SignatureId,
    callables: &[ValidatedSingleCallable],
) -> bool {
    let Ok(ordered) = reorder_direct_call_candidates(store, callee, callables) else {
        return false;
    };
    let key = (
        callee,
        ordered
            .iter()
            .map(|callable| callable.signature)
            .collect::<Vec<_>>(),
    );
    store
        .overload_failure_signatures
        .get(&key)
        .is_some_and(|receipt| {
            receipt.signature == signature
                && store.overload_failure_signature_keys.get(&signature) == Some(&key)
                && receipt.callables.iter().eq(ordered.iter().copied())
                && overload_failure_signature_is_exact(store, receipt)
        })
}

/// Raw return queries use the recovery's reverse-owned receipt and real overload provider.
pub(super) fn overload_failure_signature_return_type(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<Option<TypeId>, DirectCallError> {
    let invalid = || DirectCallInvariant::InvalidOverloadFailureSignature(signature);
    let Some(key) = store.overload_failure_signature_keys.get(&signature) else {
        return if store.signature(signature).is_some_and(|record| {
            record
                .flags()
                .contains(SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE)
        }) {
            Err(invalid().into())
        } else {
            Ok(None)
        };
    };
    let receipt = store
        .overload_failure_signatures
        .get(key)
        .ok_or_else(invalid)?;
    if array_targets != Some(receipt.array_targets) {
        return Err(invalid().into());
    }
    let callables = if let Some(group) =
        super::classes::source_class_method_overloads(store, key.0).map_err(|_| invalid())?
    {
        group.signatures
    } else {
        match validate_stored_callable_set_with_array_targets(store, key.0, array_targets) {
            StoredCallableSetValidation::Valid { projection, .. }
                if projection.construct_signatures.is_empty()
                    && !projection.call_signatures.is_empty() =>
            {
                projection.call_signatures
            }
            _ => return Err(invalid().into()),
        }
    };
    if !overload_failure_signature_matches(store, key.0, signature, &callables) {
        return Err(invalid().into());
    }
    Ok(Some(receipt.return_type))
}

/// Source classes retain the implementation needed for exact recovery notes.
fn recover_direct_call_overload(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    candidates: &[DirectCallResolution],
    session: &mut InstantiationSession,
) -> Result<Option<DirectCallResolution>, DirectCallError> {
    let class_method = store
        .type_payload(request.callee)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|method| {
            method.flags().contains(SymbolFlags::METHOD)
                && method
                    .parent()
                    .and_then(|owner| store.symbol(owner))
                    .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
        });
    if request.form != DirectCallForm::Call
        || class_method
            && super::classes::source_class_method_overloads(store, request.callee)
                .ok()
                .flatten()
                .is_none()
    {
        return Ok(None);
    }
    if let Some(candidate) = recover_uniform_overload_arity_error(candidates) {
        return Ok(Some(candidate));
    }
    recover_single_overload_argument_error(candidates, |source, target| {
        store.is_type_assignable_to_with_session(
            source,
            target,
            Some(global_types),
            Some(strict_function_types),
            session,
        )
    })
}

/// Keeps TS2554 exact when every fixed overload has the same bounds and return.
fn recover_uniform_overload_arity_error(
    candidates: &[DirectCallResolution],
) -> Option<DirectCallResolution> {
    let first = candidates.first()?;
    if first.projection.has_effective_rest
        || !matches!(
            first.applicability,
            DirectCallApplicability::TooFewArguments { .. }
                | DirectCallApplicability::TooManyArguments { .. }
        )
        || candidates.iter().skip(1).any(|candidate| {
            candidate.applicability != first.applicability
                || candidate.projection.has_effective_rest
                || candidate.projection.minimum_argument_count
                    != first.projection.minimum_argument_count
                || candidate.projection.maximum_argument_count
                    != first.projection.maximum_argument_count
                || candidate.projection.return_type != first.projection.return_type
        })
    {
        return None;
    }
    Some(first.clone())
}

/// Recovers TS2345 only when overload synthesis cannot change the return type.
fn recover_single_overload_argument_error(
    candidates: &[DirectCallResolution],
    mut is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<Option<DirectCallResolution>, DirectCallError> {
    let mut eligible = candidates
        .iter()
        .filter(|candidate| candidate.applicability == DirectCallApplicability::Applicable);
    let Some(candidate) = eligible.next() else {
        return Ok(None);
    };
    if eligible.next().is_some()
        || candidates
            .iter()
            .any(|other| other.projection.return_type != candidate.projection.return_type)
    {
        return Ok(None);
    }

    let applicability = check_argument_applicability(&candidate.projection, &mut is_assignable)?;
    if !matches!(
        applicability,
        DirectCallApplicability::ArgumentNotAssignable { .. }
            | DirectCallApplicability::RestArgumentsNotAssignable { .. }
    ) {
        return Ok(None);
    }
    let mut selected = candidate.clone();
    selected.applicability = applicability;
    Ok(Some(selected))
}

fn validate_direct_call_form(request: DirectCallRequest<'_>) -> Result<(), DirectCallError> {
    if !matches!(
        request.form,
        DirectCallForm::Call | DirectCallForm::TaggedTemplate
    ) || request.form == DirectCallForm::TaggedTemplate && request.arguments.is_empty()
    {
        return Err(DirectCallUnsupported::Form(request.form).into());
    }
    validate_direct_invocation_options(request)
}

fn validate_direct_invocation_options(
    request: DirectCallRequest<'_>,
) -> Result<(), DirectCallError> {
    if request.optional_chain {
        return Err(DirectCallUnsupported::OptionalChain.into());
    }
    if request.type_argument_count != 0 {
        return Err(DirectCallUnsupported::TypeArguments {
            count: request.type_argument_count,
        }
        .into());
    }
    if request.has_spread_argument {
        return Err(DirectCallUnsupported::SpreadArgument.into());
    }
    Ok(())
}

fn validate_tagged_template_argument(
    store: &CanonicalTypeMapperStore,
    request: DirectCallRequest<'_>,
) -> Result<(), DirectCallError> {
    if request.form != DirectCallForm::TaggedTemplate {
        return Ok(());
    }

    let expected = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("TemplateStringsArray"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .filter(|symbol| {
            store
                .symbol(*symbol)
                .is_some_and(|record| record.flags().contains(SymbolFlags::INTERFACE))
        })
        .and_then(|symbol| {
            let type_ = store.declared_type_links(symbol)?.declared_type?;
            let record = store.type_payload(type_)?;
            (matches!(record.data(), TypeData::Interface(_))
                && record
                    .symbol()
                    .and_then(|owner| store.get_merged_symbol(owner))
                    == Some(symbol))
            .then_some(type_)
        });

    if expected.is_none() || request.arguments.first().copied() != expected {
        return Err(DirectCallUnsupported::Form(DirectCallForm::TaggedTemplate).into());
    }
    Ok(())
}

fn validate_argument_types(
    store: &CanonicalTypeMapperStore,
    arguments: &[TypeId],
) -> Result<(), DirectCallError> {
    for (index, type_) in arguments.iter().copied().enumerate() {
        if store.type_payload(type_).is_none() {
            return Err(DirectCallInvariant::InvalidArgumentType { index, type_ }.into());
        }
    }
    Ok(())
}

fn validate_signature_parameters<'store>(
    store: &'store CanonicalTypeMapperStore,
    callable: &ValidatedSingleCallable,
) -> Result<&'store Signature, DirectCallError> {
    let signature = store
        .signature(callable.signature)
        .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?;
    let parameter_count =
        callable.parameters.len() + usize::from(callable.rest_parameter.is_some());
    if signature.has_rest_parameter() != callable.rest_parameter.is_some()
        || signature.parameters().len() != parameter_count
    {
        return Err(DirectCallInvariant::SignatureParameterCountMismatch {
            signature: callable.signature,
            stored: signature.parameters().len(),
            projected: parameter_count,
        }
        .into());
    }
    if usize::try_from(signature.min_argument_count()).ok() != Some(callable.min_argument_count) {
        return Err(DirectCallInvariant::SignatureMinimumMismatch {
            signature: callable.signature,
            stored: signature.min_argument_count(),
            projected: callable.min_argument_count,
        }
        .into());
    }
    if callable.min_argument_count > callable.parameters.len() {
        return Err(DirectCallInvariant::InvalidMinimumArgumentCount {
            signature: callable.signature,
            minimum: callable.min_argument_count,
            maximum: callable.parameters.len(),
        }
        .into());
    }
    for (index, &type_) in callable.parameters.iter().enumerate() {
        if store.type_payload(type_).is_none() {
            return Err(DirectCallInvariant::InvalidParameterType {
                signature: callable.signature,
                index,
                type_,
            }
            .into());
        }
    }
    Ok(signature)
}

fn rest_parameter_shape(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    type_: TypeId,
    active: &mut HashSet<TypeId>,
) -> Result<RestParameterShape, DirectCallError> {
    let invalid = || {
        DirectCallError::Invariant(DirectCallInvariant::InvalidRestParameterType {
            signature,
            type_,
        })
    };
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    if !active.insert(type_) {
        return Err(invalid());
    }
    let result = (|| {
        if let TypeData::Union(union) = record.data() {
            let valid = match array_targets {
                Some(targets) => {
                    store.validate_cached_union_result_with_array_targets(targets, type_, None)
                }
                None => store.validate_cached_union_result(type_, None),
            };
            if !record.flags().intersects(TypeFlags::UNION) {
                return Err(invalid());
            }
            if let Err(error) = valid {
                return Err(match error {
                    LiteralTypeCacheError::UnsupportedUnionConstituent(_) => {
                        DirectCallUnsupported::RestSignature(signature).into()
                    }
                    LiteralTypeCacheError::ArrayType { .. } if array_targets.is_none() => {
                        DirectCallUnsupported::RestSignature(signature).into()
                    }
                    LiteralTypeCacheError::Capacity => {
                        DirectCallInvariant::ParameterProjectionCapacity(signature).into()
                    }
                    _ => invalid(),
                });
            }
            let members = union
                .union
                .types
                .iter()
                .map(|&member| {
                    rest_parameter_shape(store, array_targets, signature, member, active)
                })
                .collect::<Result<Vec<_>, _>>()?;
            return Ok(RestParameterShape::Union { type_, members });
        }
        if record.flags().intersects(TypeFlags::UNION) {
            return Err(invalid());
        }
        if let Some(tuple) = store.canonical_tuple_shape(type_).map_err(|_| invalid())? {
            return Ok(RestParameterShape::Tuple {
                type_,
                elements: tuple.element_types().to_vec(),
                infos: tuple.element_infos().to_vec(),
                fixed_length: tuple.fixed_length(),
                combined_flags: tuple.combined_flags(),
            });
        }
        if let Some(targets) = array_targets
            && let Some(array) = store
                .canonical_array_reference_with_targets(targets, type_)
                .map_err(|_| invalid())?
        {
            return Ok(RestParameterShape::Array {
                type_,
                element: array.element_type,
            });
        }
        if let Some(bootstrap) = store.intrinsic_bootstrap()
            && array_targets
                .is_some_and(|targets| targets.array_type() == bootstrap.empty_generic_type)
            && type_ == bootstrap.empty_object_type
        {
            if record.flags() != TypeFlags::OBJECT
                || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
                || record.symbol().is_some()
                || record.alias().is_some()
                || !matches!(record.data(), TypeData::Object(object) if object == &ObjectTypeData::default())
            {
                return Err(invalid());
            }
            store
                .validate_union_constituent(bootstrap.unknown_type)
                .map_err(|_| invalid())?;
            // Missing Array declarations produce emptyObjectType upstream. Keep
            // that non-array rest identity and its unknown indexed read type.
            return Ok(RestParameterShape::MissingGlobalArray {
                type_,
                indexed_type: bootstrap.unknown_type,
            });
        }
        if record.flags().intersects(TypeFlags::ANY | TypeFlags::NEVER) {
            store
                .validate_union_constituent(type_)
                .map_err(|_| invalid())?;
            return Ok(RestParameterShape::Intrinsic(type_));
        }
        Err(DirectCallUnsupported::RestSignature(signature).into())
    })();
    active.remove(&type_);
    result
}

fn callable_rest_shape(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    callable: &ValidatedSingleCallable,
) -> Result<Option<RestParameterShape>, DirectCallError> {
    callable
        .rest_parameter
        .map(|rest| {
            rest_parameter_shape(
                store,
                array_targets,
                callable.signature,
                rest,
                &mut HashSet::new(),
            )
        })
        .transpose()
}

/// Counts fixed tuple positions and one effective rest position, as in pinned `getParameterCount`.
pub(super) fn get_parameter_count(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    callable: &ValidatedSingleCallable,
) -> Result<usize, DirectCallError> {
    get_parameter_count_with_array_targets(
        store,
        global_types.map(CanonicalArrayTargets::from_global_types),
        callable,
    )
}

/// Counts parameter positions using the supplied global array targets.
pub(super) fn get_parameter_count_with_array_targets(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    callable: &ValidatedSingleCallable,
) -> Result<usize, DirectCallError> {
    validate_signature_parameters(store, callable)?;
    Ok(callable.parameters.len()
        + callable_rest_shape(store, array_targets, callable)?
            .as_ref()
            .map_or(0, RestParameterShape::parameter_count))
}

/// Reads every effective call arity without selecting a call or resolving a return.
pub(super) fn call_signature_parameter_counts(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    callee: TypeId,
) -> Result<Option<Vec<usize>>, DirectCallError> {
    store
        .type_payload(callee)
        .ok_or(DirectCallInvariant::InvalidCalleeType(callee))?;
    match validate_stored_callable_set(store, callee) {
        StoredCallableSetValidation::NotCallable => Ok(None),
        StoredCallableSetValidation::Pending { .. } => {
            Err(DirectCallUnsupported::PendingCallable(callee).into())
        }
        StoredCallableSetValidation::Malformed { .. } => {
            Err(DirectCallInvariant::MalformedCallable(callee).into())
        }
        StoredCallableSetValidation::Valid { projection, .. } => {
            if projection.owner != callee {
                return Err(DirectCallInvariant::CallableOwnerMismatch {
                    callee,
                    owner: projection.owner,
                }
                .into());
            }
            projection
                .call_signatures
                .iter()
                .map(|callable| get_parameter_count(store, Some(global_types), callable))
                .collect::<Result<Vec<_>, _>>()
                .map(Some)
        }
    }
}

/// Fixed rest tuples have no effective rest. Tuple unions retain their rest semantics.
pub(super) fn has_effective_rest_parameter(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    callable: &ValidatedSingleCallable,
) -> Result<bool, DirectCallError> {
    has_effective_rest_parameter_with_array_targets(
        store,
        global_types.map(CanonicalArrayTargets::from_global_types),
        callable,
    )
}

/// Tests for an effective rest parameter using the supplied global array targets.
pub(super) fn has_effective_rest_parameter_with_array_targets(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    callable: &ValidatedSingleCallable,
) -> Result<bool, DirectCallError> {
    validate_signature_parameters(store, callable)?;
    Ok(callable_rest_shape(store, array_targets, callable)?
        .as_ref()
        .is_some_and(RestParameterShape::has_effective_rest))
}

fn collect_rest_position_types(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    rest: &RestParameterShape,
    position: Option<usize>,
    result: &mut Vec<TypeId>,
    active: &mut HashSet<TypeId>,
) -> Result<(), DirectCallError> {
    let bootstrap =
        store
            .intrinsic_bootstrap()
            .ok_or(DirectCallInvariant::InvalidRestParameterType {
                signature,
                type_: rest.type_id(),
            })?;
    if !active.insert(rest.type_id()) {
        return Err(DirectCallInvariant::InvalidRestParameterType {
            signature,
            type_: rest.type_id(),
        }
        .into());
    }
    match rest {
        RestParameterShape::Array { element, .. } => result.push(*element),
        RestParameterShape::MissingGlobalArray { indexed_type, .. } => result.push(*indexed_type),
        RestParameterShape::Intrinsic(type_) => result.push(*type_),
        RestParameterShape::Union { members, .. } => {
            for member in members {
                let before = result.len();
                collect_rest_position_types(
                    store,
                    array_targets,
                    signature,
                    member,
                    position,
                    result,
                    active,
                )?;
                if before == result.len() && position.is_some() {
                    result.push(bootstrap.undefined_type);
                }
            }
        }
        RestParameterShape::Tuple {
            elements,
            infos,
            fixed_length,
            combined_flags,
            ..
        } => {
            let range = match position {
                Some(position) if position < *fixed_length => position..position + 1,
                Some(_) if !combined_flags.intersects(ElementFlags::VARIABLE) => 0..0,
                Some(_) => *fixed_length..elements.len(),
                None => 0..elements.len(),
            };
            for index in range {
                let element = elements[index];
                let flags = infos[index].flags();
                if flags.contains(ElementFlags::VARIADIC) {
                    let nested = rest_parameter_shape(
                        store,
                        array_targets,
                        signature,
                        element,
                        &mut HashSet::new(),
                    )?;
                    collect_rest_position_types(
                        store,
                        array_targets,
                        signature,
                        &nested,
                        None,
                        result,
                        active,
                    )?;
                } else {
                    result.push(element);
                }
                if flags.contains(ElementFlags::OPTIONAL) && bootstrap.options.strict_null_checks {
                    result.push(bootstrap.undefined_type);
                }
            }
        }
    }
    active.remove(&rest.type_id());
    Ok(())
}

fn position_types(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    callable: &ValidatedSingleCallable,
    rest: Option<&RestParameterShape>,
    position: usize,
) -> Result<Vec<TypeId>, DirectCallError> {
    if let Some(&type_) = callable.parameters.get(position) {
        return Ok(vec![type_]);
    }
    let mut result = Vec::new();
    if let Some(rest) = rest {
        collect_rest_position_types(
            store,
            array_targets,
            callable.signature,
            rest,
            Some(position - callable.parameters.len()),
            &mut result,
            &mut HashSet::new(),
        )?;
    }
    Ok(result)
}

/// Reads a provider-validated signature without publishing a resolved-minimum cache.
/// Arity alone does not establish compatibility with a rest tuple union.
pub(super) fn get_min_argument_count(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    callable: &ValidatedSingleCallable,
    flags: MinArgumentCountFlags,
) -> Result<usize, DirectCallError> {
    get_min_argument_count_with_array_targets(
        store,
        global_types.map(CanonicalArrayTargets::from_global_types),
        callable,
        flags,
    )
}

/// Reads the minimum argument count using the supplied global array targets.
pub(super) fn get_min_argument_count_with_array_targets(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    callable: &ValidatedSingleCallable,
    flags: MinArgumentCountFlags,
) -> Result<usize, DirectCallError> {
    let signature = validate_signature_parameters(store, callable)?;
    let rest = callable_rest_shape(store, array_targets, callable)?;
    let required_rest = match rest.as_ref() {
        Some(RestParameterShape::Tuple {
            infos,
            fixed_length,
            ..
        }) => {
            let required = infos
                .iter()
                .position(|info| !info.flags().contains(ElementFlags::REQUIRED))
                .unwrap_or(*fixed_length);
            (required > 0).then_some(callable.parameters.len() + required)
        }
        _ => None,
    };
    let mut minimum = if let Some(minimum) = required_rest {
        minimum
    } else if !flags.intersects(MinArgumentCountFlags::STRONG_ARITY_FOR_UNTYPED_JS)
        && signature
            .flags()
            .contains(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE)
    {
        0
    } else {
        callable.min_argument_count
    };
    if flags.intersects(MinArgumentCountFlags::VOID_IS_NON_OPTIONAL) {
        return Ok(minimum);
    }
    while minimum > 0 {
        let types = position_types(store, array_targets, callable, rest.as_ref(), minimum - 1)?;
        let mut accepts_void = false;
        for type_ in types {
            accepts_void |= type_contains_void(store, callable.signature, minimum - 1, type_)?;
        }
        if !accepts_void {
            break;
        }
        minimum -= 1;
    }
    let cached = signature.resolved_min_argument_count();
    if cached != -1 && usize::try_from(cached).ok() != Some(minimum) {
        return Err(DirectCallInvariant::InvalidResolvedMinimumArgumentCount {
            signature: callable.signature,
            cached,
            expected: minimum,
        }
        .into());
    }
    Ok(minimum)
}

/// Reads one parameter position. Union and optional positions use canonical unions.
/// This indexed type does not replace a complete rest-argument compatibility check.
#[allow(dead_code)] // Shared with the iterator protocol adapter.
pub(super) fn try_get_type_at_position(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    callable: &ValidatedSingleCallable,
    position: usize,
) -> Result<Option<TypeId>, DirectCallError> {
    try_get_type_at_position_with_array_targets(
        store,
        global_types.map(CanonicalArrayTargets::from_global_types),
        callable,
        position,
    )
}

/// Reads a parameter position and validates unions with the supplied array targets.
pub(super) fn try_get_type_at_position_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    callable: &ValidatedSingleCallable,
    position: usize,
) -> Result<Option<TypeId>, DirectCallError> {
    validate_signature_parameters(store, callable)?;
    let rest = callable_rest_shape(store, array_targets, callable)?;
    let types = position_types(store, array_targets, callable, rest.as_ref(), position)?;
    parameter_position_union(store, array_targets, callable.signature, &types)
}

fn parameter_position_union(
    store: &mut CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    types: &[TypeId],
) -> Result<Option<TypeId>, DirectCallError> {
    match types {
        [] => Ok(None),
        [single] => Ok(Some(*single)),
        _ => {
            let result =
                store.literal_union_type_with_alias_and_array_targets(types, None, array_targets);
            result.map(Some).map_err(|error| match error {
                LiteralTypeCacheError::Capacity => {
                    DirectCallInvariant::ParameterProjectionCapacity(signature).into()
                }
                LiteralTypeCacheError::UnsupportedUnionConstituent(_) => {
                    DirectCallUnsupported::RestSignature(signature).into()
                }
                _ => DirectCallInvariant::InvalidParameterProjection(signature).into(),
            })
        }
    }
}

struct PreparedDirectCallParameters {
    rest: Option<RestParameterShape>,
    has_effective_rest: bool,
    maximum_argument_count: usize,
}

fn prepare_direct_call_parameters(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    request: DirectCallRequest<'_>,
    callable: &ValidatedSingleCallable,
) -> Result<PreparedDirectCallParameters, DirectCallError> {
    if callable.owner != request.callee {
        return Err(DirectCallInvariant::CallableOwnerMismatch {
            callee: request.callee,
            owner: callable.owner,
        }
        .into());
    }
    let signature = validate_signature_parameters(store, callable)?;
    if !signature.type_parameters().is_empty() {
        return Err(DirectCallUnsupported::GenericSignature(callable.signature).into());
    }
    if signature.this_parameter().is_some() {
        return Err(DirectCallUnsupported::ExplicitThisParameter(callable.signature).into());
    }
    let rest = callable_rest_shape(
        store,
        global_types.map(CanonicalArrayTargets::from_global_types),
        callable,
    )?;
    let has_effective_rest = has_effective_rest_parameter(store, global_types, callable)?;
    let parameter_count = get_parameter_count(store, global_types, callable)?;
    let maximum_argument_count = parameter_count - usize::from(has_effective_rest);
    if request.form == DirectCallForm::TaggedTemplate {
        let first_parameter = callable.parameters.first().copied();
        let has_required_template_parameter = callable.min_argument_count != 0
            && (first_parameter == request.arguments.first().copied()
                || store
                    .intrinsic_bootstrap()
                    .is_some_and(|bootstrap| first_parameter == Some(bootstrap.any_type)));
        let has_canonical_any_rest = callable.parameters.is_empty()
            && callable.min_argument_count == 0
            && global_types.is_some_and(|global_types| {
                callable.rest_parameter == Some(global_types.any_array_type)
                    && store
                        .intrinsic_bootstrap()
                        .is_some_and(|bootstrap| matches!(rest.as_ref(), Some(RestParameterShape::Array { element, .. }) if *element == bootstrap.any_type))
            });
        if !has_required_template_parameter && !has_canonical_any_rest {
            return Err(DirectCallUnsupported::Form(DirectCallForm::TaggedTemplate).into());
        }
    }
    Ok(PreparedDirectCallParameters {
        rest,
        has_effective_rest,
        maximum_argument_count,
    })
}

pub(super) fn project_validated_direct_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    request: DirectCallRequest<'_>,
    callable: &ValidatedSingleCallable,
) -> Result<DirectCallResolution, DirectCallError> {
    let parameters = prepare_direct_call_parameters(store, global_types, request, callable)?;
    let signature = store
        .signature(callable.signature)
        .ok_or(DirectCallInvariant::InvalidSignature(callable.signature))?;
    let Some(return_type) = callable.return_type else {
        return Err(DirectCallUnsupported::UnresolvedReturnType(callable.signature).into());
    };
    if signature.resolved_return_type() != Some(return_type) {
        return Err(DirectCallInvariant::SignatureReturnMismatch(callable.signature).into());
    }
    let return_record =
        store
            .type_payload(return_type)
            .ok_or(DirectCallInvariant::InvalidReturnType {
                signature: callable.signature,
                type_: return_type,
            })?;
    let return_kind = if return_record.flags().intersects(TypeFlags::VOID) {
        DirectCallReturnKind::Void
    } else {
        DirectCallReturnKind::Value
    };
    let arguments =
        project_direct_call_arguments(store, global_types, request, callable, parameters)?;
    Ok(arguments.with_return_type(return_type, return_kind))
}

fn project_direct_call_arguments(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    request: DirectCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    parameters: PreparedDirectCallParameters,
) -> Result<DirectCallArgumentResolution, DirectCallError> {
    let PreparedDirectCallParameters {
        rest,
        has_effective_rest,
        maximum_argument_count,
    } = parameters;
    let minimum_argument_count =
        get_min_argument_count(store, global_types, callable, MinArgumentCountFlags::NONE)?;
    if has_effective_rest {
        validate_argument_literal_identities(
            store,
            global_types,
            callable.signature,
            request.arguments,
        )?;
    }
    let non_array_rest = non_array_rest_target(store, global_types, callable, rest.as_ref())?;
    let fixed_arguments = non_array_rest
        .as_ref()
        .map_or(request.arguments.len(), |(index, _)| {
            (*index).min(request.arguments.len())
        });
    let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
    let positions = (0..fixed_arguments)
        .map(|index| position_types(store, array_targets, callable, rest.as_ref(), index))
        .collect::<Result<Vec<_>, _>>()?;
    let mut argument_targets = Vec::with_capacity(positions.len());
    for (index, types) in positions.into_iter().enumerate() {
        if let Some(parameter_type) =
            parameter_position_union(store, array_targets, callable.signature, &types)?
        {
            argument_targets.push(DirectCallArgumentTarget {
                index,
                argument_type: request.arguments[index],
                parameter_type,
            });
        }
    }
    let rest_argument_target = non_array_rest
        .map(|(_, parameter_type)| {
            let argument_type = argument_tuple_type(
                store,
                global_types,
                callable.signature,
                parameter_type,
                &request.arguments[fixed_arguments..],
            )?;
            Ok::<_, DirectCallError>(DirectCallArgumentTarget {
                index: fixed_arguments,
                argument_type,
                parameter_type,
            })
        })
        .transpose()?;
    let applicability = match request.arguments.len() {
        actual if actual < minimum_argument_count => DirectCallApplicability::TooFewArguments {
            expected_at_least: minimum_argument_count,
            actual,
        },
        actual if !has_effective_rest && actual > maximum_argument_count => {
            DirectCallApplicability::TooManyArguments {
                expected_at_most: maximum_argument_count,
                actual,
            }
        }
        _ => DirectCallApplicability::Applicable,
    };
    Ok(DirectCallArgumentResolution {
        callee: request.callee,
        signature: callable.signature,
        minimum_argument_count,
        maximum_argument_count,
        has_effective_rest,
        argument_targets,
        rest_argument_target,
        applicability,
    })
}

fn check_validated_class_call_arguments(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    callable: &ValidatedSingleCallable,
    session: &mut InstantiationSession,
) -> Result<DirectCallArgumentResolution, DirectCallError> {
    validate_argument_types(store, request.arguments)?;
    let parameters = prepare_direct_call_parameters(store, Some(globals), request, callable)?;
    let mut arguments =
        project_direct_call_arguments(store, Some(globals), request, callable, parameters)?;
    if arguments.applicability == DirectCallApplicability::Applicable {
        arguments.applicability = check_argument_target_applicability(
            &arguments.argument_targets,
            arguments.rest_argument_target,
            |source, target| {
                store.is_type_assignable_to_with_session(
                    source,
                    target,
                    Some(globals),
                    Some(strict_function_types),
                    session,
                )
            },
        )?;
    }
    Ok(arguments)
}

/// Checks the real implementation only to explain an overload argument error.
pub(super) fn class_overload_implementation_accepts_arguments(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: DirectCallRequest<'_>,
    implementation: &ValidatedSingleCallable,
    session: &mut InstantiationSession,
) -> Result<bool, DirectCallError> {
    Ok(check_validated_class_call_arguments(
        store,
        globals,
        strict_function_types,
        request,
        implementation,
        session,
    )?
    .applicability
        == DirectCallApplicability::Applicable)
}

fn non_array_rest_target(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    callable: &ValidatedSingleCallable,
    rest: Option<&RestParameterShape>,
) -> Result<Option<(usize, TypeId)>, DirectCallError> {
    let Some(rest) = rest else {
        return Ok(None);
    };
    let prefix = callable.parameters.len();
    match rest {
        RestParameterShape::Array { .. } => Ok(None),
        RestParameterShape::Intrinsic(type_)
            if store
                .type_payload(*type_)
                .is_some_and(|record| record.flags().intersects(TypeFlags::ANY)) =>
        {
            Ok(None)
        }
        RestParameterShape::Intrinsic(type_)
        | RestParameterShape::Union { type_, .. }
        | RestParameterShape::MissingGlobalArray { type_, .. } => Ok(Some((prefix, *type_))),
        RestParameterShape::Tuple {
            elements,
            infos,
            fixed_length,
            combined_flags,
            ..
        } => {
            if !combined_flags.intersects(ElementFlags::VARIABLE) {
                return Ok(None);
            }
            if infos[*fixed_length..]
                .iter()
                .any(|info| info.flags().contains(ElementFlags::VARIADIC))
            {
                return Err(DirectCallUnsupported::RestSignature(callable.signature).into());
            }
            if infos[*fixed_length..].len() == 1
                && infos[*fixed_length].flags() == ElementFlags::REST
            {
                return Ok(None);
            }
            let request = CanonicalTupleTypeRequest::new(
                &elements[*fixed_length..],
                &infos[*fixed_length..],
                false,
            );
            let request = global_types.map_or(request, |globals| {
                request.with_array_targets(CanonicalArrayTargets::from_global_types(globals))
            });
            let tail = store
                .create_canonical_tuple_type(request)
                .map_err(|error| tuple_projection_error(callable.signature, error))?;
            Ok(Some((prefix + *fixed_length, tail)))
        }
    }
}

fn argument_tuple_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    signature: SignatureId,
    rest_type: TypeId,
    arguments: &[TypeId],
) -> Result<TypeId, DirectCallError> {
    let required = store
        .create_tuple_element_info(ElementFlags::REQUIRED, None)
        .ok_or(DirectCallInvariant::ParameterProjectionCapacity(signature))?;
    let types = rest_argument_types(store, global_types, signature, rest_type, arguments)?;
    let infos = vec![required; types.len()];
    let request = CanonicalTupleTypeRequest::new(&types, &infos, false);
    let request = global_types.map_or(request, |globals| {
        request.with_array_targets(CanonicalArrayTargets::from_global_types(globals))
    });
    store
        .create_canonical_tuple_type(request)
        .map_err(|error| tuple_projection_error(signature, error))
}

fn validate_argument_literal_identities(
    store: &CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    signature: SignatureId,
    arguments: &[TypeId],
) -> Result<(), DirectCallError> {
    for &argument in arguments {
        let record = store
            .type_payload(argument)
            .ok_or(DirectCallInvariant::InvalidParameterProjection(signature))?;
        if matches!(record.data(), TypeData::Literal(_) | TypeData::Union(_)) {
            let valid = match global_types {
                Some(globals) => store.validate_union_constituent_with_array_targets(
                    CanonicalArrayTargets::from_global_types(globals),
                    argument,
                ),
                None => store.validate_union_constituent(argument),
            };
            valid.map_err(|error| match error {
                LiteralTypeCacheError::UnsupportedUnionConstituent(_) => {
                    DirectCallUnsupported::RestSignature(signature).into()
                }
                LiteralTypeCacheError::Capacity => {
                    DirectCallInvariant::ParameterProjectionCapacity(signature).into()
                }
                _ => DirectCallError::Invariant(DirectCallInvariant::InvalidParameterProjection(
                    signature,
                )),
            })?;
        }
    }
    Ok(())
}

/// Uses the rest parameter's contextual element type to preserve or widen literals.
pub(super) fn rest_argument_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    signature: SignatureId,
    rest_type: TypeId,
    arguments: &[TypeId],
) -> Result<Vec<TypeId>, DirectCallError> {
    let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
    let rest = rest_parameter_shape(
        store,
        array_targets,
        signature,
        rest_type,
        &mut HashSet::new(),
    )?;
    validate_argument_literal_identities(store, global_types, signature, arguments)?;
    let contexts = (0..arguments.len())
        .map(|position| {
            let mut types = Vec::new();
            contextual_rest_position_types(
                store,
                array_targets,
                signature,
                &rest,
                position,
                arguments.len(),
                false,
                &mut types,
            )?;
            let absorbs = types.iter().any(|type_| {
                store
                    .type_payload(*type_)
                    .is_some_and(|record| record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN))
            });
            let mut primitive = false;
            for type_ in types {
                primitive |=
                    primitive_contextual_type(store, signature, type_, &mut HashSet::new())?;
            }
            Ok::<_, DirectCallError>(primitive && !absorbs)
        })
        .collect::<Result<Vec<_>, _>>()?;
    arguments
        .iter()
        .zip(contexts)
        .map(|(&argument, preserve)| {
            contextual_literal_argument_type(store, global_types, signature, argument, preserve)
        })
        .collect()
}

#[allow(clippy::too_many_arguments)] // Indexed union contexts and length-aware tuple contexts follow separate upstream paths.
fn contextual_rest_position_types(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    signature: SignatureId,
    rest: &RestParameterShape,
    position: usize,
    length: usize,
    indexed: bool,
    result: &mut Vec<TypeId>,
) -> Result<(), DirectCallError> {
    match rest {
        RestParameterShape::Array { element, .. } => result.push(*element),
        RestParameterShape::MissingGlobalArray { indexed_type, .. } => result.push(*indexed_type),
        RestParameterShape::Intrinsic(type_) => result.push(*type_),
        RestParameterShape::Union { members, .. } => {
            for member in members {
                contextual_rest_position_types(
                    store,
                    array_targets,
                    signature,
                    member,
                    position,
                    length,
                    true,
                    result,
                )?;
            }
        }
        RestParameterShape::Tuple {
            elements,
            infos,
            fixed_length,
            combined_flags,
            ..
        } => {
            if position < *fixed_length {
                result.push(elements[position]);
            } else if indexed {
                collect_rest_position_types(
                    store,
                    array_targets,
                    signature,
                    rest,
                    None,
                    result,
                    &mut HashSet::new(),
                )?;
            } else {
                let fixed_end = if combined_flags.intersects(ElementFlags::VARIABLE) {
                    infos
                        .iter()
                        .rev()
                        .take_while(|info| info.flags().intersects(ElementFlags::FIXED))
                        .count()
                } else {
                    0
                };
                let offset = length - position;
                if offset <= fixed_end {
                    result.push(elements[elements.len() - offset]);
                } else {
                    for index in *fixed_length..elements.len() - fixed_end {
                        if infos[index].flags().contains(ElementFlags::VARIADIC) {
                            let nested = rest_parameter_shape(
                                store,
                                array_targets,
                                signature,
                                elements[index],
                                &mut HashSet::new(),
                            )?;
                            collect_rest_position_types(
                                store,
                                array_targets,
                                signature,
                                &nested,
                                None,
                                result,
                                &mut HashSet::new(),
                            )?;
                        } else {
                            result.push(elements[index]);
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn primitive_contextual_type(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    type_: TypeId,
    active: &mut HashSet<TypeId>,
) -> Result<bool, DirectCallError> {
    let record = store
        .type_payload(type_)
        .ok_or(DirectCallInvariant::InvalidParameterProjection(signature))?;
    if record.flags().intersects(
        TypeFlags::PRIMITIVE
            | TypeFlags::INDEX
            | TypeFlags::TEMPLATE_LITERAL
            | TypeFlags::STRING_MAPPING,
    ) {
        return Ok(true);
    }
    let constituents = match record.data() {
        TypeData::Union(union) => &union.union.types,
        TypeData::Intersection(intersection) => &intersection.intersection.types,
        _ => return Ok(false),
    };
    if !active.insert(type_) {
        return Err(DirectCallInvariant::InvalidParameterProjection(signature).into());
    }
    let mut primitive = false;
    for &constituent in constituents {
        primitive |= primitive_contextual_type(store, signature, constituent, active)?;
    }
    active.remove(&type_);
    Ok(primitive)
}

fn contextual_literal_argument_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    signature: SignatureId,
    type_: TypeId,
    preserve: bool,
) -> Result<TypeId, DirectCallError> {
    let record = store
        .type_payload(type_)
        .ok_or(DirectCallInvariant::InvalidParameterProjection(signature))?;
    match record.data() {
        TypeData::Literal(literal) => {
            if preserve {
                return Ok(literal.regular_type);
            }
            if literal.fresh_type != Some(type_) || literal.regular_type == type_ {
                return Ok(type_);
            }
            if record.flags().intersects(TypeFlags::ENUM_LIKE) {
                let owner = super::enums::canonical_enum_type_owner(store, type_)
                    .ok_or(DirectCallInvariant::InvalidParameterProjection(signature))?;
                return store
                    .declared_type_links(owner)
                    .and_then(|links| links.declared_type)
                    .filter(|declared| {
                        super::enums::canonical_enum_type_owner(store, *declared) == Some(owner)
                    })
                    .ok_or_else(|| {
                        DirectCallInvariant::InvalidParameterProjection(signature).into()
                    });
            }
            let bootstrap = store
                .intrinsic_bootstrap()
                .ok_or(DirectCallInvariant::InvalidParameterProjection(signature))?;
            Ok(match &literal.value {
                super::type_records::LiteralValue::String(_) => bootstrap.string_type,
                super::type_records::LiteralValue::Number(_) => bootstrap.number_type,
                super::type_records::LiteralValue::BigInt(_) => bootstrap.bigint_type,
                super::type_records::LiteralValue::Boolean(_) => bootstrap.boolean_type,
                super::type_records::LiteralValue::ComputedEnum => {
                    return Err(DirectCallInvariant::InvalidParameterProjection(signature).into());
                }
            })
        }
        TypeData::Union(union) => {
            let original = union.union.types.clone();
            let mapped = original
                .iter()
                .map(|&member| {
                    contextual_literal_argument_type(
                        store,
                        global_types,
                        signature,
                        member,
                        preserve,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if mapped == original {
                Ok(type_)
            } else {
                parameter_position_union(
                    store,
                    global_types.map(CanonicalArrayTargets::from_global_types),
                    signature,
                    &mapped,
                )?
                .ok_or_else(|| DirectCallInvariant::InvalidParameterProjection(signature).into())
            }
        }
        _ => Ok(type_),
    }
}

fn tuple_projection_error(signature: SignatureId, error: TupleTypeError) -> DirectCallError {
    match error {
        TupleTypeError::Capacity => {
            DirectCallInvariant::ParameterProjectionCapacity(signature).into()
        }
        TupleTypeError::UnsupportedElementFlags { .. }
        | TupleTypeError::UnsupportedElementOrder { .. }
        | TupleTypeError::UnsupportedCreationFlags(_)
        | TupleTypeError::ArrayRestCollapseUnavailable => {
            DirectCallUnsupported::RestSignature(signature).into()
        }
        _ => DirectCallInvariant::InvalidParameterProjection(signature).into(),
    }
}

fn type_contains_void(
    store: &CanonicalTypeMapperStore,
    signature: SignatureId,
    index: usize,
    type_: TypeId,
) -> Result<bool, DirectCallError> {
    let record = store
        .type_payload(type_)
        .ok_or(DirectCallInvariant::InvalidParameterType {
            signature,
            index,
            type_,
        })?;
    if record.flags().intersects(TypeFlags::VOID) {
        return Ok(true);
    }
    let data_is_union = matches!(record.data(), TypeData::Union(_));
    if !record.flags().intersects(TypeFlags::UNION) {
        return if data_is_union {
            Err(DirectCallInvariant::MalformedParameterUnion {
                signature,
                index,
                type_,
            }
            .into())
        } else {
            Ok(false)
        };
    }
    let TypeData::Union(union) = record.data() else {
        return Err(DirectCallInvariant::MalformedParameterUnion {
            signature,
            index,
            type_,
        }
        .into());
    };
    if union.union.types.is_empty() {
        return Err(DirectCallInvariant::MalformedParameterUnion {
            signature,
            index,
            type_,
        }
        .into());
    }
    for constituent in &union.union.types {
        let Some(constituent_record) = store.type_payload(*constituent) else {
            return Err(DirectCallInvariant::MalformedParameterUnion {
                signature,
                index,
                type_,
            }
            .into());
        };
        if constituent_record.flags().intersects(TypeFlags::VOID) {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn check_argument_applicability(
    projection: &DirectCallProjection,
    is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<DirectCallApplicability, RelationUnavailable> {
    check_argument_target_applicability(
        &projection.argument_targets,
        projection.rest_argument_target,
        is_assignable,
    )
}

fn check_argument_target_applicability(
    targets: &[DirectCallArgumentTarget],
    rest_target: Option<DirectCallArgumentTarget>,
    mut is_assignable: impl FnMut(TypeId, TypeId) -> Result<bool, RelationUnavailable>,
) -> Result<DirectCallApplicability, RelationUnavailable> {
    for target in targets {
        if !is_assignable(target.argument_type, target.parameter_type)? {
            return Ok(DirectCallApplicability::ArgumentNotAssignable {
                index: target.index,
                argument_type: target.argument_type,
                parameter_type: target.parameter_type,
            });
        }
    }
    if let Some(target) = rest_target
        && !is_assignable(target.argument_type, target.parameter_type)?
    {
        return Ok(DirectCallApplicability::RestArgumentsNotAssignable {
            index: target.index,
            argument_type: target.argument_type,
            parameter_type: target.parameter_type,
        });
    }
    Ok(DirectCallApplicability::Applicable)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeHost, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, SemanticStore, TypeRecord, ValueSymbolLinks,
        bootstrap::UnionReduction, mapper::TypeMapper, production::GlobalMergeCompletion,
        types::ObjectFlags,
    };

    fn initialized_store() -> CanonicalTypeMapperStore {
        let mut store = SemanticStore::<TypeRecord, TypeMapper>::new();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        store
    }

    fn array_context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
        array_context_with_options(parsed, CanonicalCheckerOptions::default())
    }

    fn array_context_with_options(
        parsed: &ParseResult,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'_> {
        let file = FileId::new(9_411);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/tagged-template-calls.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
    }

    fn context_template_strings_array(context: &mut CanonicalCheckerContext<'_>) -> TypeId {
        let symbol = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("TemplateStringsArray"))
            .unwrap();
        context.get_declared_type_of_symbol(symbol).unwrap()
    }

    fn parameter(store: &mut CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                EscapedName::source(name),
            ))
            .unwrap()
    }

    fn template_strings_array(store: &mut CanonicalTypeMapperStore) -> TypeId {
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::INTERFACE,
                EscapedName::source("TemplateStringsArray"),
            ))
            .unwrap();
        let type_ = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        assert_eq!(
            store.insert_symbol(globals, EscapedName::source("TemplateStringsArray"), symbol),
            Some(None)
        );
        assert!(store.set_declared_type_links(
            symbol,
            DeclaredTypeLinks {
                declared_type: Some(type_),
                ..DeclaredTypeLinks::default()
            },
        ));
        type_
    }

    fn callable(
        store: &mut CanonicalTypeMapperStore,
        flags: SignatureFlags,
        parameters: &[TypeId],
        minimum: i32,
        return_type: Option<TypeId>,
    ) -> ValidatedSingleCallable {
        let mut projected_parameters = parameters.to_vec();
        let rest_parameter = if flags.contains(SignatureFlags::HAS_REST_PARAMETER) {
            projected_parameters.pop()
        } else {
            None
        };
        let symbols = parameters
            .iter()
            .enumerate()
            .map(|(index, _)| parameter(store, &format!("p{index}")))
            .collect();
        let signature = store
            .alloc_signature(
                flags,
                None,
                Vec::new(),
                None,
                symbols,
                return_type,
                None,
                minimum,
            )
            .unwrap();
        let owner = store.intrinsic_bootstrap().unwrap().any_function_type;
        ValidatedSingleCallable {
            owner,
            signature,
            parameters: projected_parameters,
            rest_parameter,
            min_argument_count: usize::try_from(minimum).unwrap(),
            return_type,
            strict_variance_exempt: false,
        }
    }

    fn request(callee: TypeId, arguments: &[TypeId]) -> DirectCallRequest<'_> {
        DirectCallRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            type_argument_count: 0,
            has_spread_argument: false,
            callee,
            arguments,
        }
    }

    fn tuple(store: &mut CanonicalTypeMapperStore, elements: &[(TypeId, ElementFlags)]) -> TypeId {
        let types = elements.iter().map(|(type_, _)| *type_).collect::<Vec<_>>();
        let infos = elements
            .iter()
            .map(|(_, flags)| store.create_tuple_element_info(*flags, None).unwrap())
            .collect::<Vec<_>>();
        store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&types, &infos, false))
            .unwrap()
    }

    #[test]
    fn signature_positions_preserve_void_and_untyped_minimum_rules() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (void, number, undefined) = (
            bootstrap.void_type,
            bootstrap.number_type,
            bootstrap.undefined_type,
        );
        let required_void = callable(&mut store, SignatureFlags::NONE, &[void], 1, Some(number));
        let undefined_parameter = callable(
            &mut store,
            SignatureFlags::NONE,
            &[undefined],
            1,
            Some(number),
        );
        let leading_void = callable(
            &mut store,
            SignatureFlags::NONE,
            &[void, number],
            2,
            Some(number),
        );
        let untyped = callable(
            &mut store,
            SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            &[number],
            1,
            Some(number),
        );
        let before = (store.type_len(), store.signature_len(), store.mapper_len());

        for _ in 0..2 {
            assert_eq!(
                get_min_argument_count(&store, None, &required_void, MinArgumentCountFlags::NONE),
                Ok(0)
            );
            assert_eq!(
                get_min_argument_count(
                    &store,
                    None,
                    &required_void,
                    MinArgumentCountFlags::VOID_IS_NON_OPTIONAL
                ),
                Ok(1)
            );
            assert_eq!(
                get_min_argument_count(
                    &store,
                    None,
                    &undefined_parameter,
                    MinArgumentCountFlags::NONE
                ),
                Ok(1)
            );
            assert_eq!(
                get_min_argument_count(&store, None, &leading_void, MinArgumentCountFlags::NONE),
                Ok(2)
            );
            assert_eq!(
                get_min_argument_count(&store, None, &untyped, MinArgumentCountFlags::NONE),
                Ok(0)
            );
            assert_eq!(
                get_min_argument_count(
                    &store,
                    None,
                    &untyped,
                    MinArgumentCountFlags::STRONG_ARITY_FOR_UNTYPED_JS
                ),
                Ok(1)
            );
        }
        assert_eq!(
            (store.type_len(), store.signature_len(), store.mapper_len()),
            before
        );
        assert_eq!(
            store
                .signature(required_void.signature)
                .unwrap()
                .resolved_min_argument_count(),
            -1
        );

        assert!(store.set_signature_resolved_min_argument_count(required_void.signature, 1));
        assert_eq!(
            get_min_argument_count(&store, None, &required_void, MinArgumentCountFlags::NONE),
            Err(DirectCallError::Invariant(
                DirectCallInvariant::InvalidResolvedMinimumArgumentCount {
                    signature: required_void.signature,
                    cached: 1,
                    expected: 0
                }
            ))
        );
    }

    #[test]
    fn signature_positions_expand_fixed_rest_tuples_without_losing_required_elements() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (number, string, void) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.void_type,
        );
        let empty = tuple(&mut store, &[]);
        let required = tuple(&mut store, &[(number, ElementFlags::REQUIRED)]);
        let trailing_void = tuple(
            &mut store,
            &[
                (number, ElementFlags::REQUIRED),
                (void, ElementFlags::REQUIRED),
            ],
        );
        let optional = tuple(
            &mut store,
            &[
                (number, ElementFlags::REQUIRED),
                (string, ElementFlags::OPTIONAL),
            ],
        );
        for (rest, expected_minimum, expected_count) in [
            (empty, 0, 0),
            (required, 1, 1),
            (trailing_void, 1, 2),
            (optional, 1, 2),
        ] {
            let callable = callable(
                &mut store,
                SignatureFlags::HAS_REST_PARAMETER,
                &[rest],
                0,
                Some(void),
            );
            assert_eq!(
                get_parameter_count(&store, None, &callable),
                Ok(expected_count)
            );
            assert_eq!(
                get_min_argument_count(&store, None, &callable, MinArgumentCountFlags::NONE),
                Ok(expected_minimum)
            );
            assert_eq!(
                has_effective_rest_parameter(&store, None, &callable),
                Ok(false)
            );
            assert_eq!(
                try_get_type_at_position(&mut store, None, &callable, expected_count),
                Ok(None)
            );
            let result = project_validated_direct_call(
                &mut store,
                None,
                request(callable.owner, &[]),
                &callable,
            )
            .unwrap();
            assert_eq!(result.projection.minimum_argument_count, expected_minimum);
            assert_eq!(result.projection.maximum_argument_count, expected_count);
            assert_eq!(
                result.applicability,
                if expected_minimum == 0 {
                    DirectCallApplicability::Applicable
                } else {
                    DirectCallApplicability::TooFewArguments {
                        expected_at_least: expected_minimum,
                        actual: 0,
                    }
                }
            );
        }
        let required_rest = callable(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            &[required],
            0,
            Some(void),
        );
        assert_eq!(
            get_min_argument_count(&store, None, &required_rest, MinArgumentCountFlags::NONE),
            Ok(1)
        );
    }

    #[test]
    fn missing_global_array_rest_parameters_keep_fallback_identity() {
        for (source, missing_array) in [
            ("interface Empty {}", true),
            ("interface Array<T> {} interface ReadonlyArray<T> {}", false),
        ] {
            let parsed = parse_source_file(source);
            let mut context = array_context(&parsed);
            let globals = context.global_types().clone();
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let fallback = bootstrap.empty_object_type;
            let unknown = bootstrap.unknown_type;
            let void = bootstrap.void_type;
            assert_eq!(globals.any_array_type == fallback, missing_array);
            let store = context.store_mut_for_test();
            let fallback_callable = callable(
                store,
                SignatureFlags::HAS_REST_PARAMETER,
                &[fallback],
                0,
                Some(void),
            );
            let before = (store.type_len(), store.signature_len(), store.mapper_len());
            let unsupported = Err(DirectCallError::Unsupported(
                DirectCallUnsupported::RestSignature(fallback_callable.signature),
            ));

            assert_eq!(
                get_parameter_count(store, None, &fallback_callable),
                unsupported
            );
            if !missing_array {
                assert_eq!(
                    get_parameter_count(store, Some(&globals), &fallback_callable),
                    unsupported
                );
                assert_eq!(
                    (store.type_len(), store.signature_len(), store.mapper_len()),
                    before
                );
                continue;
            }
            assert_eq!(
                get_parameter_count(store, Some(&globals), &fallback_callable),
                Ok(1)
            );
            assert_eq!(
                has_effective_rest_parameter(store, Some(&globals), &fallback_callable),
                Ok(true)
            );
            assert_eq!(
                get_min_argument_count(
                    store,
                    Some(&globals),
                    &fallback_callable,
                    MinArgumentCountFlags::NONE,
                ),
                Ok(0)
            );
            for index in [0, 4] {
                assert_eq!(
                    try_get_type_at_position(store, Some(&globals), &fallback_callable, index),
                    Ok(Some(unknown))
                );
            }
            let shape = callable_rest_shape(
                store,
                Some(CanonicalArrayTargets::from_global_types(&globals)),
                &fallback_callable,
            )
            .unwrap();
            assert_eq!(
                non_array_rest_target(store, Some(&globals), &fallback_callable, shape.as_ref()),
                Ok(Some((0, fallback)))
            );
            assert_eq!(fallback_callable.rest_parameter, Some(fallback));
            assert_eq!(
                (store.type_len(), store.signature_len(), store.mapper_len()),
                before
            );

            let ordinary = store
                .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
                .unwrap();
            assert!(store.set_structured_type_members(ordinary, None, None, None, None, None));
            let ordinary = callable(
                store,
                SignatureFlags::HAS_REST_PARAMETER,
                &[ordinary],
                0,
                Some(void),
            );
            let before = (store.type_len(), store.signature_len(), store.mapper_len());
            assert_eq!(
                get_parameter_count(store, Some(&globals), &ordinary),
                Err(DirectCallError::Unsupported(
                    DirectCallUnsupported::RestSignature(ordinary.signature),
                ))
            );
            assert_eq!(
                (store.type_len(), store.signature_len(), store.mapper_len()),
                before
            );

            assert!(store.set_object_target_and_mapper(fallback, Some(fallback), None));
            let before = (store.type_len(), store.signature_len(), store.mapper_len());
            assert_eq!(
                get_parameter_count(store, Some(&globals), &fallback_callable),
                Err(DirectCallError::Invariant(
                    DirectCallInvariant::InvalidRestParameterType {
                        signature: fallback_callable.signature,
                        type_: fallback,
                    },
                ))
            );
            assert_eq!(
                (store.type_len(), store.signature_len(), store.mapper_len()),
                before
            );
        }
    }

    #[test]
    fn signature_positions_preserve_optional_and_variable_tuple_positions() {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let mut context = array_context_with_options(
            &parsed,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let globals = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string, boolean, undefined) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.boolean_type,
            bootstrap.undefined_type,
        );
        let store = context.store_mut_for_test();
        let optional = tuple(store, &[(number, ElementFlags::OPTIONAL)]);
        let variable = tuple(
            store,
            &[
                (number, ElementFlags::REQUIRED),
                (string, ElementFlags::REST),
                (boolean, ElementFlags::REQUIRED),
            ],
        );
        let optional_callable = callable(
            store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[optional],
            0,
            Some(number),
        );
        let variable_callable = callable(
            store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[variable],
            0,
            Some(number),
        );
        let expected_optional = store
            .expression_union_type(&[number, undefined], UnionReduction::Literal)
            .unwrap();
        let expected_tail = store
            .expression_union_type(&[string, boolean], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &optional_callable, 0),
            Ok(Some(expected_optional))
        );
        assert_eq!(
            get_parameter_count(store, Some(&globals), &variable_callable),
            Ok(2)
        );
        assert_eq!(
            get_min_argument_count(
                store,
                Some(&globals),
                &variable_callable,
                MinArgumentCountFlags::NONE
            ),
            Ok(1)
        );
        assert_eq!(
            has_effective_rest_parameter(store, Some(&globals), &variable_callable),
            Ok(true)
        );
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &variable_callable, 0),
            Ok(Some(number))
        );
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &variable_callable, 1),
            Ok(Some(expected_tail))
        );
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &variable_callable, 100),
            Ok(Some(expected_tail))
        );
        let before = (store.type_len(), store.signature_len(), store.mapper_len());
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &optional_callable, 0),
            Ok(Some(expected_optional))
        );
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &variable_callable, 100),
            Ok(Some(expected_tail))
        );
        assert_eq!(
            (store.type_len(), store.signature_len(), store.mapper_len()),
            before
        );
    }

    #[test]
    fn signature_positions_tuple_union_calls_check_the_whole_argument_tuple() {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let mut context = array_context_with_options(
            &parsed,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let globals = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, undefined, number) = (
            bootstrap.string_type,
            bootstrap.undefined_type,
            bootstrap.number_type,
        );
        let store = context.store_mut_for_test();
        let empty = tuple(store, &[]);
        let one = tuple(store, &[(string, ElementFlags::REQUIRED)]);
        let rest = store
            .expression_union_type_with_global_types(
                &globals,
                &[empty, one],
                UnionReduction::Literal,
            )
            .unwrap();
        let signature = callable(
            store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[rest],
            0,
            Some(number),
        );
        let optional_string = store
            .expression_union_type(&[string, undefined], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            get_min_argument_count(
                store,
                Some(&globals),
                &signature,
                MinArgumentCountFlags::NONE
            ),
            Ok(0)
        );
        assert_eq!(
            get_parameter_count(store, Some(&globals), &signature),
            Ok(1)
        );
        assert_eq!(
            has_effective_rest_parameter(store, Some(&globals), &signature),
            Ok(true)
        );
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &signature, 0),
            Ok(Some(optional_string))
        );
        assert_eq!(
            try_get_type_at_position(store, Some(&globals), &signature, 1),
            Ok(Some(undefined))
        );
        for (arguments, applicable) in [
            (&[][..], true),
            (&[string][..], true),
            (&[undefined][..], false),
            (&[string, string][..], false),
        ] {
            let mut warm = None;
            for _ in 0..2 {
                let result = project_validated_direct_call(
                    store,
                    Some(&globals),
                    request(signature.owner, arguments),
                    &signature,
                )
                .unwrap();
                assert_eq!(result.applicability, DirectCallApplicability::Applicable);
                let checked = check_argument_applicability(&result.projection, |source, target| {
                    store.is_type_assignable_to_with_global_types_and_strict_function_types(
                        source, target, &globals, false,
                    )
                })
                .unwrap();
                if applicable {
                    assert_eq!(checked, DirectCallApplicability::Applicable);
                } else {
                    assert!(
                        matches!(checked, DirectCallApplicability::RestArgumentsNotAssignable { index: 0, parameter_type, .. } if parameter_type == rest)
                    );
                }
                let state = (store.type_len(), store.signature_len(), store.mapper_len());
                if let Some(previous) = warm.replace(state) {
                    assert_eq!(state, previous);
                }
            }
        }
    }

    #[test]
    fn signature_positions_rest_literal_treatment_uses_primitive_contexts() {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let mut context = array_context(&parsed);
        let globals = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (object, string, number, any) = (
            bootstrap.non_primitive_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.any_type,
        );
        let store = context.store_mut_for_test();
        let empty = tuple(store, &[]);
        let object_one = tuple(store, &[(object, ElementFlags::REQUIRED)]);
        let object_two = tuple(
            store,
            &[
                (object, ElementFlags::REQUIRED),
                (object, ElementFlags::REQUIRED),
            ],
        );
        let string_one = tuple(store, &[(string, ElementFlags::REQUIRED)]);
        let any_one = tuple(store, &[(any, ElementFlags::REQUIRED)]);
        let object_rest = store
            .expression_union_type_with_global_types(
                &globals,
                &[object_one, object_two],
                UnionReduction::Literal,
            )
            .unwrap();
        let primitive_rest = store
            .expression_union_type_with_global_types(
                &globals,
                &[empty, string_one],
                UnionReduction::Literal,
            )
            .unwrap();
        let mixed_rest = store
            .expression_union_type_with_global_types(
                &globals,
                &[object_one, string_one],
                UnionReduction::Literal,
            )
            .unwrap();
        let any_rest = store
            .expression_union_type_with_global_types(
                &globals,
                &[any_one, string_one],
                UnionReduction::Literal,
            )
            .unwrap();
        let regular = store.regular_string_literal_type("bad".to_owned()).unwrap();
        let fresh = store.fresh_type_of_literal_type(regular).unwrap();
        let signature = callable(
            store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[object_rest],
            0,
            Some(number),
        );
        let before = (store.type_len(), store.signature_len(), store.mapper_len());

        for _ in 0..2 {
            assert_eq!(
                rest_argument_types(
                    store,
                    Some(&globals),
                    signature.signature,
                    object_rest,
                    &[fresh]
                ),
                Ok(vec![string])
            );
            assert_eq!(
                rest_argument_types(
                    store,
                    Some(&globals),
                    signature.signature,
                    object_rest,
                    &[regular]
                ),
                Ok(vec![regular])
            );
            assert_eq!(
                rest_argument_types(
                    store,
                    Some(&globals),
                    signature.signature,
                    primitive_rest,
                    &[fresh]
                ),
                Ok(vec![regular])
            );
            assert_eq!(
                rest_argument_types(
                    store,
                    Some(&globals),
                    signature.signature,
                    mixed_rest,
                    &[fresh]
                ),
                Ok(vec![regular])
            );
            assert_eq!(
                rest_argument_types(
                    store,
                    Some(&globals),
                    signature.signature,
                    any_rest,
                    &[fresh]
                ),
                Ok(vec![string])
            );
        }
        assert_eq!(
            (store.type_len(), store.signature_len(), store.mapper_len()),
            before
        );
    }

    #[test]
    fn signature_positions_reject_unregistered_fresh_literals_before_tuple_writes() {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let mut context = array_context(&parsed);
        let globals = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();
        let regular = store.regular_string_literal_type("x".to_owned()).unwrap();
        let canonical_fresh = store.fresh_type_of_literal_type(regular).unwrap();
        let empty = tuple(store, &[]);
        let one = tuple(store, &[(regular, ElementFlags::REQUIRED)]);
        let rest = store
            .expression_union_type_with_global_types(
                &globals,
                &[empty, one],
                UnionReduction::Literal,
            )
            .unwrap();
        let signature = callable(
            store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[rest],
            0,
            Some(number),
        );
        let forged = store
            .alloc_literal_type(
                TypeFlags::STRING_LITERAL,
                crate::semantic::type_records::LiteralValue::String("x".into()),
                crate::semantic::type_records::RegularLiteralLink::Type(regular),
            )
            .unwrap();
        assert!(store.set_literal_links(forged, Some(forged), regular));
        let before = (
            store.type_len(),
            store.signature_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
        );

        for _ in 0..2 {
            assert!(matches!(
                project_validated_direct_call(
                    store,
                    Some(&globals),
                    request(signature.owner, &[forged]),
                    &signature
                ),
                Err(DirectCallError::Invariant(
                    DirectCallInvariant::InvalidParameterProjection(_)
                ))
            ));
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.checker_link_allocated_lengths()
                ),
                before
            );
        }
        assert_eq!(store.validate_union_constituent(regular), Ok(()));
        assert_eq!(store.validate_union_constituent(canonical_fresh), Ok(()));
    }

    #[test]
    fn signature_positions_reject_foreign_and_poisoned_rest_types_without_writes() {
        let mut store = initialized_store();
        let mut other = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let foreign = tuple(&mut other, &[]);
        let foreign_signature = callable(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[foreign],
            0,
            Some(number),
        );
        let before = (store.type_len(), store.signature_len(), store.mapper_len());
        assert_eq!(
            get_min_argument_count(
                &store,
                None,
                &foreign_signature,
                MinArgumentCountFlags::NONE
            ),
            Err(DirectCallError::Invariant(
                DirectCallInvariant::InvalidRestParameterType {
                    signature: foreign_signature.signature,
                    type_: foreign
                }
            ))
        );
        assert_eq!(
            (store.type_len(), store.signature_len(), store.mapper_len()),
            before
        );

        let rest = tuple(&mut store, &[(number, ElementFlags::REQUIRED)]);
        let empty = tuple(&mut store, &[]);
        let forged_union = store
            .alloc_union_type(ObjectFlags::NONE, vec![empty, rest])
            .unwrap();
        let forged_signature = callable(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[forged_union],
            0,
            Some(number),
        );
        let before = (store.type_len(), store.signature_len(), store.mapper_len());
        assert!(matches!(
            get_min_argument_count(&store, None, &forged_signature, MinArgumentCountFlags::NONE),
            Err(DirectCallError::Invariant(
                DirectCallInvariant::InvalidRestParameterType { .. }
            ))
        ));
        assert_eq!(
            (store.type_len(), store.signature_len(), store.mapper_len()),
            before
        );
        let signature = callable(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[rest],
            0,
            Some(number),
        );
        let target = store.canonical_tuple_shape(rest).unwrap().unwrap().target();
        let Some(TypeData::Tuple(tuple)) = store.type_payload(target).map(TypeRecord::data) else {
            panic!("expected a canonical tuple target")
        };
        let this_type = tuple.interface.this_type.unwrap();
        assert!(store.set_resolved_base_constraint(this_type, Some(number)));
        let before = (store.type_len(), store.signature_len(), store.mapper_len());
        assert!(matches!(
            get_min_argument_count(&store, None, &signature, MinArgumentCountFlags::NONE),
            Err(DirectCallError::Invariant(
                DirectCallInvariant::InvalidRestParameterType { .. }
            ))
        ));
        assert!(matches!(
            try_get_type_at_position(&mut store, None, &signature, 0),
            Err(DirectCallError::Invariant(
                DirectCallInvariant::InvalidRestParameterType { .. }
            ))
        ));
        assert_eq!(
            (store.type_len(), store.signature_len(), store.mapper_len()),
            before
        );
    }

    #[test]
    fn syntax_capability_boundaries_are_explicit() {
        let store = initialized_store();
        let callee = store.intrinsic_bootstrap().unwrap().any_function_type;
        for (request, expected) in [
            (
                DirectCallRequest {
                    form: DirectCallForm::New,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::Form(DirectCallForm::New),
            ),
            (
                DirectCallRequest {
                    optional_chain: true,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::OptionalChain,
            ),
            (
                DirectCallRequest {
                    type_argument_count: 1,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::TypeArguments { count: 1 },
            ),
            (
                DirectCallRequest {
                    has_spread_argument: true,
                    ..request(callee, &[])
                },
                DirectCallUnsupported::SpreadArgument,
            ),
        ] {
            assert_eq!(
                validate_direct_call_form(request),
                Err(DirectCallError::Unsupported(expected))
            );
        }
    }

    #[test]
    fn literal_overloads_stay_first_without_changing_their_relative_order() {
        let mut store = initialized_store();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let broad_first = callable(&mut store, SignatureFlags::NONE, &[number], 1, Some(number));
        let literal_first = callable(
            &mut store,
            SignatureFlags::HAS_LITERAL_TYPES,
            &[number],
            1,
            Some(number),
        );
        let broad_second = callable(&mut store, SignatureFlags::NONE, &[number], 1, Some(number));
        let literal_second = callable(
            &mut store,
            SignatureFlags::HAS_LITERAL_TYPES,
            &[number],
            1,
            Some(number),
        );
        let expected = [
            literal_first.signature,
            literal_second.signature,
            broad_first.signature,
            broad_second.signature,
        ];
        let callee = broad_first.owner;
        let callables = [broad_first, literal_first, broad_second, literal_second];

        let actual = reorder_direct_call_candidates(&store, callee, &callables)
            .unwrap()
            .into_iter()
            .map(|callable| callable.signature)
            .collect::<Vec<_>>();

        assert_eq!(actual, expected);
    }

    #[test]
    fn merged_interface_method_overloads_prefer_later_declaration_groups() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface API { ",
            "run(value: string): number; ",
            "run(value: number): number; ",
            "} ",
            "interface API { ",
            "run(value: string): string; ",
            "run(value: number): string; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(9_411);
        let mut context = array_context(&parsed);
        let owner = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("API"))
            .unwrap();
        context.get_declared_type_of_symbol(owner).unwrap();
        let mut declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::MethodSignature).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        let [first, second, third, fourth] = declarations.as_slice() else {
            panic!("expected two overloads in each merged declaration")
        };
        let signatures = [third.1, fourth.1, first.1, second.1].map(|declaration| {
            context
                .store()
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        });
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("run"))
            .unwrap();
        let callee = context
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(context.store(), callee)
        else {
            panic!("expected an authenticated merged interface method")
        };
        let ordered =
            reorder_direct_call_candidates(context.store(), callee, &projection.call_signatures)
                .unwrap()
                .into_iter()
                .map(|callable| callable.signature)
                .collect::<Vec<_>>();
        assert_eq!(ordered, signatures);

        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let arguments = [string];
        let globals = context.global_types().clone();
        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );

        for _ in 0..2 {
            let resolution = resolve_direct_call(
                context.store_mut_for_test(),
                &globals,
                false,
                request(callee, &arguments),
            )
            .unwrap();
            assert_eq!(resolution.projection.signature, signatures[0]);
            assert_eq!(resolution.projection.return_type, string);
        }

        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            warm,
        );
    }

    #[test]
    fn tagged_templates_skip_overloads_with_incompatible_first_parameters() {
        for declarations in [
            "(template: string): number; (template: TemplateStringsArray): string;",
            "(template: TemplateStringsArray): string; (template: string): number;",
        ] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} \
                 interface ReadonlyArray<T> {{}} \
                 interface TemplateStringsArray {{}} \
                 interface Tag {{ {declarations} }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut context = array_context(&parsed);
            let template = context_template_strings_array(&mut context);
            let owner = context
                .store()
                .symbol_table(context.globals())
                .and_then(|globals| globals.get_source("Tag"))
                .unwrap();
            let callee = context.get_declared_type_of_symbol(owner).unwrap();
            let globals = context.global_types().clone();
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let expected = match validate_stored_callable_set(context.store(), callee) {
                StoredCallableSetValidation::Valid { projection, .. } => {
                    projection
                        .call_signatures
                        .iter()
                        .find(|callable| callable.return_type == Some(string))
                        .unwrap()
                        .signature
                }
                _ => panic!("expected two authenticated tag overloads"),
            };
            let arguments = [template];
            let tagged = DirectCallRequest {
                form: DirectCallForm::TaggedTemplate,
                ..request(callee, &arguments)
            };
            let before = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            );

            for _ in 0..2 {
                let resolution =
                    resolve_direct_call(context.store_mut_for_test(), &globals, false, tagged)
                        .unwrap();
                assert_eq!(resolution.projection.signature, expected);
                assert_eq!(resolution.projection.return_type, string);
                assert_eq!(
                    resolution.applicability,
                    DirectCallApplicability::Applicable
                );
            }

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                ),
                before,
            );
        }
    }

    #[test]
    fn incompatible_tagged_template_overloads_keep_their_unsupported_boundary() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {} ",
            "interface Tag { ",
            "(template: string): number; ",
            "(template: number): string; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let owner = context
            .store()
            .symbol_table(context.globals())
            .and_then(|globals| globals.get_source("Tag"))
            .unwrap();
        let callee = context.get_declared_type_of_symbol(owner).unwrap();
        let globals = context.global_types().clone();
        let arguments = [template];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callee, &arguments)
        };

        assert_eq!(
            resolve_direct_call(context.store_mut_for_test(), &globals, false, tagged),
            Err(DirectCallError::Unsupported(DirectCallUnsupported::Form(
                DirectCallForm::TaggedTemplate,
            ))),
        );
    }

    #[test]
    fn tagged_templates_authenticate_the_global_first_argument_and_signature() {
        let mut store = initialized_store();
        let template = template_strings_array(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[template, number],
            1,
            Some(string),
        );
        let arguments = [template, number];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &arguments)
        };

        assert_eq!(validate_direct_call_form(tagged), Ok(()));
        assert_eq!(validate_tagged_template_argument(&store, tagged), Ok(()));

        let resolution =
            project_validated_direct_call(&mut store, None, tagged, &callable).unwrap();
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
        assert_eq!(resolution.projection.signature, callable.signature);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            resolution.projection.argument_targets,
            vec![
                DirectCallArgumentTarget {
                    index: 0,
                    argument_type: template,
                    parameter_type: template,
                },
                DirectCallArgumentTarget {
                    index: 1,
                    argument_type: number,
                    parameter_type: number,
                },
            ]
        );
    }

    #[test]
    fn tagged_templates_reject_missing_or_forged_template_arguments() {
        let mut store = initialized_store();
        let callee = store.intrinsic_bootstrap().unwrap().any_function_type;
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let any = bootstrap.any_type;
        let unknown = bootstrap.unknown_type;
        let unsupported = DirectCallError::Unsupported(DirectCallUnsupported::Form(
            DirectCallForm::TaggedTemplate,
        ));
        let missing = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callee, &[])
        };
        assert_eq!(validate_direct_call_form(missing), Err(unsupported));

        let arguments = [number];
        let forged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callee, &arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(&store, forged),
            Err(unsupported)
        );

        let template = template_strings_array(&mut store);
        assert_eq!(
            validate_tagged_template_argument(&store, forged),
            Err(unsupported)
        );

        let wrong_signature =
            callable(&mut store, SignatureFlags::NONE, &[number], 1, Some(number));
        let arguments = [template];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(wrong_signature.owner, &arguments)
        };
        assert_eq!(validate_tagged_template_argument(&store, tagged), Ok(()));
        assert_eq!(
            project_validated_direct_call(&mut store, None, tagged, &wrong_signature),
            Err(unsupported)
        );

        let optional_template = callable(
            &mut store,
            SignatureFlags::NONE,
            &[template],
            0,
            Some(number),
        );
        assert_eq!(
            project_validated_direct_call(&mut store, None, tagged, &optional_template),
            Err(unsupported)
        );

        let optional_any = callable(&mut store, SignatureFlags::NONE, &[any], 0, Some(number));
        assert_eq!(
            project_validated_direct_call(&mut store, None, tagged, &optional_any),
            Err(unsupported)
        );

        let unknown_signature = callable(
            &mut store,
            SignatureFlags::NONE,
            &[unknown],
            1,
            Some(number),
        );
        assert_eq!(
            project_validated_direct_call(&mut store, None, tagged, &unknown_signature),
            Err(unsupported)
        );
    }

    #[test]
    fn tagged_templates_accept_required_intrinsic_any_first_parameters() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;

        let fixed = callable(
            context.store_mut_for_test(),
            SignatureFlags::NONE,
            &[any],
            1,
            Some(string),
        );
        let fixed_arguments = [template];
        let fixed_tag = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(fixed.owner, &fixed_arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(context.store(), fixed_tag),
            Ok(())
        );
        let fixed_resolution =
            project_validated_direct_call(context.store_mut_for_test(), None, fixed_tag, &fixed)
                .unwrap();
        assert_eq!(
            fixed_resolution.projection.argument_targets,
            vec![DirectCallArgumentTarget {
                index: 0,
                argument_type: template,
                parameter_type: any,
            }],
        );
        assert_eq!(fixed_resolution.projection.minimum_argument_count, 1);
        assert_eq!(fixed_resolution.projection.maximum_argument_count, 1);
        assert!(!fixed_resolution.projection.has_effective_rest);

        let with_rest = callable(
            context.store_mut_for_test(),
            SignatureFlags::HAS_REST_PARAMETER,
            &[any, global_types.any_array_type],
            1,
            Some(string),
        );
        let arguments = [template, number];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(with_rest.owner, &arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(context.store(), tagged),
            Ok(())
        );
        let resolution = project_validated_direct_call(
            context.store_mut_for_test(),
            Some(&global_types),
            tagged,
            &with_rest,
        )
        .unwrap();
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
        assert_eq!(resolution.projection.minimum_argument_count, 1);
        assert_eq!(resolution.projection.maximum_argument_count, 1);
        assert!(resolution.projection.has_effective_rest);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            resolution.projection.argument_targets,
            vec![
                DirectCallArgumentTarget {
                    index: 0,
                    argument_type: template,
                    parameter_type: any,
                },
                DirectCallArgumentTarget {
                    index: 1,
                    argument_type: number,
                    parameter_type: any,
                },
            ],
        );
    }

    #[test]
    fn tagged_templates_keep_substitution_argument_diagnostics() {
        let mut store = initialized_store();
        let template = template_strings_array(&mut store);
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[template, number],
            2,
            Some(string),
        );
        let arguments = [template, string];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &arguments)
        };
        let resolution =
            project_validated_direct_call(&mut store, None, tagged, &callable).unwrap();
        let applicability =
            check_argument_applicability(&resolution.projection, |source, target| {
                Ok(source == target)
            })
            .unwrap();

        assert_eq!(
            applicability,
            DirectCallApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: string,
                parameter_type: number,
            }
        );
        assert_eq!(resolution.projection.return_type, string);
    }

    #[test]
    fn tagged_templates_accept_canonical_any_rest_signatures() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            context.store_mut_for_test(),
            SignatureFlags::HAS_REST_PARAMETER,
            &[global_types.any_array_type],
            0,
            Some(string),
        );

        for arguments in [&[template][..], &[template, number, string][..]] {
            let tagged = DirectCallRequest {
                form: DirectCallForm::TaggedTemplate,
                ..request(callable.owner, arguments)
            };
            assert_eq!(
                validate_tagged_template_argument(context.store(), tagged),
                Ok(())
            );
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let resolution = project_validated_direct_call(
                context.store_mut_for_test(),
                Some(&global_types),
                tagged,
                &callable,
            )
            .unwrap();

            assert_eq!(
                resolution.applicability,
                DirectCallApplicability::Applicable
            );
            assert_eq!(resolution.projection.minimum_argument_count, 0);
            assert_eq!(resolution.projection.maximum_argument_count, 0);
            assert!(resolution.projection.has_effective_rest);
            assert_eq!(resolution.projection.return_type, string);
            assert_eq!(
                resolution.projection.argument_targets.len(),
                arguments.len()
            );
            assert!(
                resolution
                    .projection
                    .argument_targets
                    .iter()
                    .enumerate()
                    .all(|(index, target)| {
                        target.index == index
                            && target.argument_type == arguments[index]
                            && target.parameter_type == any
                    })
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn tagged_templates_reject_noncanonical_rest_only_signatures() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = array_context(&parsed);
        let template = context_template_strings_array(&mut context);
        let global_types = context.global_types().clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let number_array = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let unsupported = DirectCallError::Unsupported(DirectCallUnsupported::Form(
            DirectCallForm::TaggedTemplate,
        ));

        for rest in [number_array, global_types.any_readonly_array_type] {
            let callable = callable(
                context.store_mut_for_test(),
                SignatureFlags::HAS_REST_PARAMETER,
                &[rest],
                0,
                Some(string),
            );
            let arguments = [template];
            let tagged = DirectCallRequest {
                form: DirectCallForm::TaggedTemplate,
                ..request(callable.owner, &arguments)
            };
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                project_validated_direct_call(
                    context.store_mut_for_test(),
                    Some(&global_types),
                    tagged,
                    &callable,
                ),
                Err(unsupported),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }

        let callable = callable(
            context.store_mut_for_test(),
            SignatureFlags::HAS_REST_PARAMETER,
            &[global_types.any_array_type],
            0,
            Some(string),
        );
        let forged_arguments = [number];
        let forged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &forged_arguments)
        };
        assert_eq!(
            validate_tagged_template_argument(context.store(), forged),
            Err(unsupported),
        );

        let arguments = [template];
        let tagged = DirectCallRequest {
            form: DirectCallForm::TaggedTemplate,
            ..request(callable.owner, &arguments)
        };
        assert_eq!(
            project_validated_direct_call(context.store_mut_for_test(), None, tagged, &callable),
            Err(DirectCallError::Unsupported(
                DirectCallUnsupported::RestSignature(callable.signature),
            )),
        );
    }

    #[test]
    fn fixed_signature_projects_exact_targets_and_value_return() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, string],
            1,
            Some(string),
        );
        let arguments = [number];
        let resolution = project_validated_direct_call(
            &mut store,
            None,
            request(callable.owner, &arguments),
            &callable,
        )
        .unwrap();

        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
        assert_eq!(resolution.projection.signature, callable.signature);
        assert_eq!(resolution.projection.minimum_argument_count, 1);
        assert_eq!(resolution.projection.maximum_argument_count, 2);
        assert_eq!(resolution.projection.return_type, string);
        assert_eq!(
            resolution.projection.return_kind,
            DirectCallReturnKind::Value
        );
        assert_eq!(
            resolution.projection.argument_targets,
            vec![DirectCallArgumentTarget {
                index: 0,
                argument_type: number,
                parameter_type: number,
            }]
        );
    }

    #[test]
    fn class_body_constructor_projection_keeps_locals_and_rejects_stale_types() {
        for corrupt_projection in [false, true] {
            let parsed = parse_source_file(concat!(
                "class Base { constructor(public value: number = 1, label: string) {} } ",
                "class Derived extends Base { constructor() { super(undefined, 'label'); } }",
            ));
            let file = FileId::new(9_411);
            let mut context = array_context_with_options(
                &parsed,
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks: true,
                        ..IntrinsicBootstrapOptions::default()
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );
            context.check_source_file(file).unwrap();
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let derived = context
                .store()
                .symbol_table(context.globals())
                .unwrap()
                .get_source("Derived")
                .unwrap();
            let plan = crate::semantic::classes::plan_source_class_members(
                context.store(),
                &host,
                derived,
            )
            .unwrap();
            let prepared = crate::semantic::classes::prepare_source_class_members(
                context.store_mut_for_test(),
                &host,
                &plan,
            )
            .unwrap();
            let token = prepared
                .body_access(context.store(), &host, &plan.bodies()[0])
                .unwrap();
            let target = crate::semantic::classes::class_body_super_constructor_callable(
                context.store(),
                &host,
                &token,
            )
            .unwrap();
            let callable = target.callable();
            let parameter = context
                .store()
                .signature(callable.signature)
                .unwrap()
                .parameters()[0];
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let (number, string, undefined) = (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.undefined_type,
            );
            let projected = callable.parameters[0];
            assert_ne!(projected, number);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .unwrap()
                    .resolved_type,
                Some(number)
            );
            let globals = context.global_types().clone();
            let arguments = [undefined, string];
            let request = DirectCallRequest {
                form: DirectCallForm::New,
                optional_chain: false,
                type_argument_count: 0,
                has_spread_argument: false,
                callee: callable.owner,
                arguments: &arguments,
            };
            let result = resolve_class_body_invocation(
                context.store_mut_for_test(),
                &globals,
                false,
                request,
                &target,
            )
            .unwrap();
            assert!(
                matches!(result, ClassBodyInvocationResolution::Resolved(result)
                if result.applicability == DirectCallApplicability::Applicable)
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .unwrap()
                    .resolved_type,
                Some(number)
            );

            if corrupt_projection {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_symbol(projected, Some(target.class_symbol()))
                );
            } else {
                assert!(context.store_mut_for_test().set_value_symbol_links(
                    parameter,
                    ValueSymbolLinks {
                        resolved_type: Some(string),
                        ..ValueSymbolLinks::default()
                    }
                ));
            }
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(
                resolve_class_body_invocation(
                    context.store_mut_for_test(),
                    &globals,
                    false,
                    request,
                    &target
                )
                .is_err()
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
    }

    #[test]
    fn pending_class_call_arguments_check_arity_and_relations_without_a_return_type() {
        let parsed = parse_source_file("");
        let mut context = array_context(&parsed);
        let globals = context.global_types().clone();
        let strict = context.options().strict_function_types;
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(store, SignatureFlags::NONE, &[number], 1, None);
        let before = (store.type_len(), store.signature_len());

        for (arguments, expected) in [
            (
                vec![],
                DirectCallApplicability::TooFewArguments {
                    expected_at_least: 1,
                    actual: 0,
                },
            ),
            (vec![number], DirectCallApplicability::Applicable),
            (
                vec![string],
                DirectCallApplicability::ArgumentNotAssignable {
                    index: 0,
                    argument_type: string,
                    parameter_type: number,
                },
            ),
            (
                vec![number, number],
                DirectCallApplicability::TooManyArguments {
                    expected_at_most: 1,
                    actual: 2,
                },
            ),
        ] {
            let checked = check_validated_class_call_arguments(
                store,
                &globals,
                strict,
                request(callable.owner, &arguments),
                &callable,
            )
            .unwrap();
            assert_eq!(checked.signature(), callable.signature);
            assert_eq!(checked.applicability, expected);
            assert_eq!(
                store
                    .signature(callable.signature)
                    .unwrap()
                    .resolved_return_type(),
                None
            );
            assert_eq!((store.type_len(), store.signature_len()), before);
        }
    }

    #[test]
    fn pending_class_call_arguments_reject_foreign_types_before_a_body_demand() {
        let parsed = parse_source_file("");
        let mut context = array_context(&parsed);
        let globals = context.global_types().clone();
        let strict = context.options().strict_function_types;
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let callable = callable(store, SignatureFlags::NONE, &[number], 1, None);
        let foreign = initialized_store();
        let foreign_type = foreign.intrinsic_bootstrap().unwrap().number_type;
        let before = (store.type_len(), store.signature_len());
        assert_eq!(
            check_validated_class_call_arguments(
                store,
                &globals,
                strict,
                request(callable.owner, &[foreign_type]),
                &callable,
            ),
            Err(DirectCallError::Invariant(
                DirectCallInvariant::InvalidArgumentType {
                    index: 0,
                    type_: foreign_type,
                }
            )),
        );
        assert_eq!(
            store
                .signature(callable.signature)
                .unwrap()
                .resolved_return_type(),
            None
        );
        assert_eq!((store.type_len(), store.signature_len()), before);
    }

    #[test]
    fn arity_is_checked_before_argument_applicability() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, string],
            2,
            Some(string),
        );

        let too_few = project_validated_direct_call(
            &mut store,
            None,
            request(callable.owner, &[number]),
            &callable,
        )
        .unwrap();
        assert_eq!(
            too_few.applicability,
            DirectCallApplicability::TooFewArguments {
                expected_at_least: 2,
                actual: 1,
            }
        );

        let too_many = project_validated_direct_call(
            &mut store,
            None,
            request(callable.owner, &[number, string, number]),
            &callable,
        )
        .unwrap();
        assert_eq!(
            too_many.applicability,
            DirectCallApplicability::TooManyArguments {
                expected_at_most: 2,
                actual: 3,
            }
        );
        assert_eq!(too_many.projection.argument_targets.len(), 2);
    }

    #[test]
    fn trailing_void_parameters_reduce_the_effective_minimum() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, void],
            2,
            Some(void),
        );
        let resolution = project_validated_direct_call(
            &mut store,
            None,
            request(callable.owner, &[number]),
            &callable,
        )
        .unwrap();

        assert_eq!(resolution.projection.minimum_argument_count, 1);
        assert_eq!(
            resolution.projection.return_kind,
            DirectCallReturnKind::Void
        );
        assert_eq!(
            resolution.applicability,
            DirectCallApplicability::Applicable
        );
    }

    #[test]
    fn untyped_javascript_signatures_use_zero_effective_minimum_without_changing_metadata() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let javascript = callable(
            &mut store,
            SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE,
            &[any],
            1,
            Some(void),
        );

        let missing = project_validated_direct_call(
            &mut store,
            None,
            request(javascript.owner, &[]),
            &javascript,
        )
        .unwrap();
        assert_eq!(missing.projection.minimum_argument_count, 0);
        assert_eq!(missing.projection.maximum_argument_count, 1);
        assert_eq!(missing.applicability, DirectCallApplicability::Applicable);

        let extra = project_validated_direct_call(
            &mut store,
            None,
            request(javascript.owner, &[number, number, number]),
            &javascript,
        )
        .unwrap();
        assert_eq!(extra.projection.minimum_argument_count, 0);
        assert_eq!(extra.projection.maximum_argument_count, 1);
        assert_eq!(
            extra.applicability,
            DirectCallApplicability::TooManyArguments {
                expected_at_most: 1,
                actual: 3,
            },
        );

        let stored = store.signature(javascript.signature).unwrap();
        assert_eq!(stored.min_argument_count(), 1);
        assert_eq!(stored.resolved_min_argument_count(), -1);

        let typescript = callable(&mut store, SignatureFlags::NONE, &[any], 1, Some(void));
        let missing = project_validated_direct_call(
            &mut store,
            None,
            request(typescript.owner, &[]),
            &typescript,
        )
        .unwrap();
        assert_eq!(missing.projection.minimum_argument_count, 1);
        assert_eq!(missing.projection.maximum_argument_count, 1);
        assert_eq!(
            missing.applicability,
            DirectCallApplicability::TooFewArguments {
                expected_at_least: 1,
                actual: 0,
            },
        );
    }

    #[test]
    fn first_argument_relation_failure_is_retained_without_any_fallback() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let callable = callable(
            &mut store,
            SignatureFlags::NONE,
            &[number, number],
            2,
            Some(string),
        );
        let resolution = project_validated_direct_call(
            &mut store,
            None,
            request(callable.owner, &[number, string]),
            &callable,
        )
        .unwrap();
        let applicability =
            check_argument_applicability(&resolution.projection, |source, target| {
                Ok(source == target)
            })
            .unwrap();

        assert_eq!(
            applicability,
            DirectCallApplicability::ArgumentNotAssignable {
                index: 1,
                argument_type: string,
                parameter_type: number,
            }
        );
        assert_eq!(resolution.projection.return_type, string);
    }

    #[test]
    fn unresolved_return_and_rest_signature_stop_at_typed_seams() {
        let mut store = initialized_store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let unresolved = callable(&mut store, SignatureFlags::NONE, &[number], 1, None);
        assert_eq!(
            project_validated_direct_call(
                &mut store,
                None,
                request(unresolved.owner, &[number]),
                &unresolved,
            ),
            Err(DirectCallError::Unsupported(
                DirectCallUnsupported::UnresolvedReturnType(unresolved.signature)
            ))
        );

        let rest = callable(
            &mut store,
            SignatureFlags::HAS_REST_PARAMETER,
            &[number],
            0,
            Some(number),
        );
        assert_eq!(
            project_validated_direct_call(&mut store, None, request(rest.owner, &[number]), &rest,),
            Err(DirectCallError::Unsupported(
                DirectCallUnsupported::RestSignature(rest.signature)
            ))
        );
    }
}
