//! Overload selection for published method signatures and their receiver copies.
//!
//! The ordinary and generic call engines check each real candidate. This module
//! owns declaration-group order, the two relation passes, and failure selection.
//! A diagnostic candidate can differ from the signature used for recovery.

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, MinArgumentCountFlags, RelationUnavailable,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    callables::ValidatedSingleCallable,
    calls::{
        DirectCallApplicability, DirectCallError, DirectCallForm, DirectCallRequest,
        DirectCallResolution, DirectCallUnsupported, check_argument_applicability,
        get_min_argument_count, get_parameter_count, has_effective_rest_parameter,
        project_validated_direct_call, reorder_direct_call_candidates,
    },
    generic_calls::{
        GenericCallArgumentRelation, GenericCallVectorApplicability, GenericCallVectorCandidate,
        GenericCallVectorError, GenericCallVectorRequest, GenericCallVectorResolution,
        check_generic_call_candidate_with_session, finish_generic_call_candidate_with_session,
        generic_method_signature_callee, generic_method_type_argument_bounds,
        validate_generic_call_vector_request,
    },
    instantiate::InstantiationSession,
    relation::RelationKind,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum GenericMethodCallSelection {
    Fixed {
        signature: SignatureId,
        return_type: TypeId,
    },
    Generic(GenericCallVectorResolution),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum GenericMethodCallDiagnostic {
    Fixed(DirectCallResolution),
    Generic {
        signature: SignatureId,
        applicability: GenericCallVectorApplicability,
    },
    TypeArgumentArity {
        expected: usize,
        actual: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GenericMethodCallResolution {
    pub(super) selected: GenericMethodCallSelection,
    pub(super) diagnostic: Option<GenericMethodCallDiagnostic>,
}

#[derive(Debug, PartialEq)]
pub(super) enum GenericMethodCallError {
    Direct(DirectCallError),
    Generic(GenericCallVectorError),
    Relation(RelationUnavailable),
    Unsupported(TypeId),
    Invalid(TypeId),
}

impl From<DirectCallError> for GenericMethodCallError {
    fn from(error: DirectCallError) -> Self {
        Self::Direct(error)
    }
}

impl From<GenericCallVectorError> for GenericMethodCallError {
    fn from(error: GenericCallVectorError) -> Self {
        Self::Generic(error)
    }
}

impl From<RelationUnavailable> for GenericMethodCallError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

enum CheckedMethodCandidate {
    Fixed(DirectCallResolution),
    Generic(GenericCallVectorCandidate),
}

impl CheckedMethodCandidate {
    fn applicable(&self) -> bool {
        match self {
            Self::Fixed(candidate) => {
                candidate.applicability == DirectCallApplicability::Applicable
            }
            Self::Generic(candidate) => {
                candidate.applicability() == GenericCallVectorApplicability::Applicable
            }
        }
    }

    fn diagnostic(&self) -> GenericMethodCallDiagnostic {
        match self {
            Self::Fixed(candidate) => GenericMethodCallDiagnostic::Fixed(candidate.clone()),
            Self::Generic(candidate) => GenericMethodCallDiagnostic::Generic {
                signature: candidate.signature(),
                applicability: candidate.applicability(),
            },
        }
    }

    fn argument_error(&self) -> bool {
        match self {
            Self::Fixed(candidate) => matches!(
                candidate.applicability,
                DirectCallApplicability::ArgumentNotAssignable { .. }
                    | DirectCallApplicability::RestArgumentsNotAssignable { .. }
            ),
            Self::Generic(candidate) => matches!(
                candidate.applicability(),
                GenericCallVectorApplicability::ArgumentNotAssignable { .. }
            ),
        }
    }

    fn constraint_error(&self) -> bool {
        matches!(self, Self::Generic(candidate) if matches!(candidate.applicability(),
            GenericCallVectorApplicability::ExplicitTypeArgumentConstraint { .. }))
    }
}

fn has_type_argument_arity(bounds: (usize, usize), explicit: Option<&[TypeId]>) -> bool {
    explicit.is_none_or(|arguments| {
        arguments.is_empty() || (bounds.0..=bounds.1).contains(&arguments.len())
    })
}

#[allow(clippy::too_many_arguments)]
fn check_candidate(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    callable: &ValidatedSingleCallable,
    relation: GenericCallArgumentRelation,
    session: &mut InstantiationSession,
) -> Result<CheckedMethodCandidate, GenericMethodCallError> {
    if !store
        .signature(callable.signature)
        .ok_or(GenericMethodCallError::Invalid(request.callee))?
        .type_parameters()
        .is_empty()
    {
        return check_generic_call_candidate_with_session(
            store,
            globals,
            strict_function_types,
            request,
            callable,
            relation,
            session,
        )
        .map(CheckedMethodCandidate::Generic)
        .map_err(Into::into);
    }
    let mut candidate = project_validated_direct_call(
        store,
        Some(globals),
        DirectCallRequest {
            form: request.form,
            optional_chain: request.optional_chain,
            type_argument_count: 0,
            has_spread_argument: request.has_spread_argument,
            callee: request.callee,
            arguments: request.arguments,
        },
        callable,
    )?;
    if candidate.applicability == DirectCallApplicability::Applicable {
        let (relation, strict_function_types) = match relation {
            GenericCallArgumentRelation::Assignable => {
                (RelationKind::Assignable, strict_function_types)
            }
            GenericCallArgumentRelation::Subtype {
                strict_function_types,
            } => (RelationKind::Subtype, strict_function_types),
        };
        candidate.applicability =
            check_argument_applicability(&candidate.projection, |source, target| {
                store.is_type_related_to_with_session(
                    source,
                    target,
                    relation,
                    Some(globals),
                    Some(strict_function_types),
                    session,
                )
            })?;
    }
    Ok(CheckedMethodCandidate::Fixed(candidate))
}

#[allow(clippy::too_many_arguments)]
fn finish_candidate(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    candidate: CheckedMethodCandidate,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<GenericMethodCallSelection, GenericMethodCallError> {
    match candidate {
        CheckedMethodCandidate::Fixed(candidate) => fixed_selection(
            request.callee,
            candidate.projection.signature,
            candidate.projection.return_type,
            existing_call_signature,
        ),
        CheckedMethodCandidate::Generic(candidate) => finish_generic_call_candidate_with_session(
            store,
            globals,
            strict_function_types,
            request,
            candidate,
            existing_call_signature,
            session,
        )
        .map(GenericMethodCallSelection::Generic)
        .map_err(Into::into),
    }
}

fn fixed_selection(
    callee: TypeId,
    signature: SignatureId,
    return_type: TypeId,
    existing: Option<SignatureId>,
) -> Result<GenericMethodCallSelection, GenericMethodCallError> {
    if existing.is_some_and(|existing| existing != signature) {
        return Err(GenericMethodCallError::Invalid(callee));
    }
    Ok(GenericMethodCallSelection::Fixed {
        signature,
        return_type,
    })
}

/// Uses Go's first signature with enough parameters, or the longest signature.
fn recovery_candidate<'a>(
    store: &CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    callee: TypeId,
    candidates: &[&'a ValidatedSingleCallable],
    argument_count: usize,
) -> Result<&'a ValidatedSingleCallable, GenericMethodCallError> {
    let mut longest = None;
    let mut maximum = 0;
    for &candidate in candidates {
        let count = get_parameter_count(store, Some(globals), candidate)?;
        if has_effective_rest_parameter(store, Some(globals), candidate)? || count >= argument_count
        {
            return Ok(candidate);
        }
        if longest.is_none() || count > maximum {
            longest = Some(candidate);
            maximum = count;
        }
    }
    longest.ok_or(GenericMethodCallError::Invalid(callee))
}

/// Call syntax and contextual arguments remain owned by the source caller.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub(super) fn resolve_generic_method_call(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    strict_function_types: bool,
    request: GenericCallVectorRequest<'_>,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
) -> Result<Option<GenericMethodCallResolution>, GenericMethodCallError> {
    if request.form != DirectCallForm::Call || request.optional_chain || request.has_spread_argument
    {
        return Ok(None);
    }
    let Some(structured) = store
        .type_payload(request.callee)
        .and_then(|record| record.data().structured())
    else {
        return Ok(None);
    };
    let Some(signatures) = structured.signatures.as_deref() else {
        return Ok(None);
    };
    if signatures.is_empty()
        || !signatures.iter().any(|signature| {
            store
                .signature(*signature)
                .is_some_and(|signature| !signature.type_parameters().is_empty())
        })
    {
        return Ok(None);
    }
    let array_targets = Some(CanonicalArrayTargets::from_global_types(globals));
    for &signature in signatures {
        if generic_method_signature_callee(store, signature, array_targets)? != Some(request.callee)
        {
            return Ok(None);
        }
    }
    validate_generic_call_vector_request(store, request)?;
    let projection =
        match validate_stored_callable_set_with_array_targets(store, request.callee, array_targets)
        {
            StoredCallableSetValidation::Valid { projection, .. }
                if projection.construct_signatures.is_empty()
                    && !projection.call_signatures.is_empty() =>
            {
                projection
            }
            StoredCallableSetValidation::Malformed { .. } => {
                return Err(GenericMethodCallError::Invalid(request.callee));
            }
            _ => return Err(GenericMethodCallError::Unsupported(request.callee)),
        };
    let ordered =
        reorder_direct_call_candidates(store, request.callee, &projection.call_signatures)?;
    let bounds = ordered
        .iter()
        .map(|candidate| generic_method_type_argument_bounds(store, candidate, array_targets))
        .collect::<Result<Vec<_>, _>>()?;
    let passes = [
        GenericCallArgumentRelation::Subtype {
            strict_function_types,
        },
        GenericCallArgumentRelation::Assignable,
    ];
    let mut argument_errors = Vec::new();
    let mut constraint_error = None;
    for relation in passes.into_iter().skip(usize::from(ordered.len() == 1)) {
        argument_errors.clear();
        constraint_error = None;
        for (&callable, &bounds) in ordered.iter().zip(&bounds) {
            if !has_type_argument_arity(bounds, request.explicit_type_arguments) {
                continue;
            }
            // Reuse the fixed, optional, and omitted-void bounds from ordinary calls.
            if bounds.1 != 0
                && (request.arguments.len()
                    < get_min_argument_count(
                        store,
                        Some(globals),
                        callable,
                        MinArgumentCountFlags::NONE,
                    )?
                    || callable.rest_parameter.is_none()
                        && request.arguments.len() > callable.parameters.len())
            {
                continue;
            }
            let candidate = check_candidate(
                store,
                globals,
                strict_function_types,
                request,
                callable,
                relation,
                session,
            )?;
            if candidate.applicable() {
                return finish_candidate(
                    store,
                    globals,
                    strict_function_types,
                    request,
                    candidate,
                    existing_call_signature,
                    session,
                )
                .map(|selected| {
                    Some(GenericMethodCallResolution {
                        selected,
                        diagnostic: None,
                    })
                });
            }
            if candidate.argument_error() {
                argument_errors.push(candidate.diagnostic());
            } else if candidate.constraint_error() {
                constraint_error = Some(candidate.diagnostic());
            }
        }
    }
    let diagnostic = if argument_errors.len() == 1 {
        argument_errors
            .pop()
            .expect("the sole argument error is present")
    } else if !argument_errors.is_empty() {
        // TS2769 chains and overload implementation notes remain a separate boundary.
        return Err(GenericMethodCallError::Unsupported(request.callee));
    } else if let Some(diagnostic) = constraint_error {
        diagnostic
    } else {
        // Arity notes use the original declaration order, not overload search order.
        let mut eligible = Vec::new();
        for candidate in &projection.call_signatures {
            if has_type_argument_arity(
                generic_method_type_argument_bounds(store, candidate, array_targets)?,
                request.explicit_type_arguments,
            ) {
                eligible.push(candidate);
            }
        }
        if eligible.is_empty() && ordered.len() == 1 {
            check_candidate(
                store,
                globals,
                strict_function_types,
                request,
                ordered[0],
                GenericCallArgumentRelation::Assignable,
                session,
            )?
            .diagnostic()
        } else if eligible.is_empty() {
            let actual = request
                .explicit_type_arguments
                .ok_or(GenericMethodCallError::Invalid(request.callee))?
                .len();
            let below = bounds
                .iter()
                .filter_map(|&(_, maximum)| (maximum < actual).then_some(maximum))
                .max();
            let above = bounds
                .iter()
                .filter_map(|&(minimum, _)| (minimum > actual).then_some(minimum))
                .min();
            let ((Some(expected), None) | (None, Some(expected))) = (below, above) else {
                return Err(GenericMethodCallError::Unsupported(request.callee));
            };
            GenericMethodCallDiagnostic::TypeArgumentArity { expected, actual }
        } else {
            let first = eligible[0];
            let minimum =
                get_min_argument_count(store, Some(globals), first, MinArgumentCountFlags::NONE)?;
            let maximum = get_parameter_count(store, Some(globals), first)?;
            let rest = has_effective_rest_parameter(store, Some(globals), first)?;
            for candidate in &eligible {
                if get_min_argument_count(
                    store,
                    Some(globals),
                    candidate,
                    MinArgumentCountFlags::NONE,
                )? != minimum
                    || get_parameter_count(store, Some(globals), candidate)? != maximum
                    || has_effective_rest_parameter(store, Some(globals), candidate)? != rest
                {
                    return Err(GenericMethodCallError::Unsupported(request.callee));
                }
            }
            let candidate = check_candidate(
                store,
                globals,
                strict_function_types,
                request,
                first,
                GenericCallArgumentRelation::Assignable,
                session,
            )?;
            if candidate.applicable() {
                return Err(GenericMethodCallError::Invalid(request.callee));
            }
            candidate.diagnostic()
        }
    };
    let recovery = recovery_candidate(
        store,
        globals,
        request.callee,
        &ordered,
        request.arguments.len(),
    )?;
    let selected = if store
        .signature(recovery.signature)
        .ok_or(GenericMethodCallError::Invalid(request.callee))?
        .type_parameters()
        .is_empty()
    {
        // Go returns this signature without checking its argument relation again.
        let return_type = recovery.return_type.ok_or(GenericMethodCallError::Direct(
            DirectCallError::Unsupported(DirectCallUnsupported::UnresolvedReturnType(
                recovery.signature,
            )),
        ))?;
        fixed_selection(
            request.callee,
            recovery.signature,
            return_type,
            existing_call_signature,
        )?
    } else {
        let candidate = check_candidate(
            store,
            globals,
            strict_function_types,
            request,
            recovery,
            GenericCallArgumentRelation::Assignable,
            session,
        )?;
        finish_candidate(
            store,
            globals,
            strict_function_types,
            request,
            candidate,
            existing_call_signature,
            session,
        )?
    };
    Ok(Some(GenericMethodCallResolution {
        selected,
        diagnostic: Some(diagnostic),
    }))
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, ValueSymbolLinks,
        bootstrap::{LiteralTypeCacheError, UnionReduction},
        callables::{StoredSingleCallableValidation, validate_stored_single_callable},
        declared::type_list_key,
        derived_types::DerivedTypeError,
        generic_calls::demand_generic_call_vector_selected_return,
        inference::NakedTypeCandidateError,
        instantiate::{InstantiationError, InstantiationLimits, instantiate_type_with_session},
        instantiated_members::validate_generic_interface_members,
        store::CachedSignatureLookup,
        structured_members::{
            InterfaceHeritageMembersValidation, validate_interface_heritage_members,
        },
        type_records::TypeData,
        types::ObjectFlags,
    };

    const LIBRARY: FileId = FileId::new(163_100);
    const SOURCE: FileId = FileId::new(163_101);

    fn relation_context<'arena>(
        library: &'arena ParseResult,
        source: &'arena ParseResult,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (file, parsed, declaration, path) in [
            (LIBRARY, library, true, "\"/method-relation-library.d.ts\""),
            (SOURCE, source, false, "\"/method-relation.ts\""),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
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
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            [(LIBRARY, &library.arena), (SOURCE, &source.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn global_interface(store: &CanonicalTypeMapperStore, name: &str) -> TypeId {
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

    fn inherited_value(store: &CanonicalTypeMapperStore) -> SemanticSymbolId {
        let derived = global_interface(store, "Derived");
        let TypeData::Interface(data) = store.type_payload(derived).unwrap().data() else {
            panic!("Derived must retain its interface identity")
        };
        store
            .symbol_table(data.reference.object.structured.members.unwrap())
            .and_then(|members| members.get_source("value"))
            .unwrap()
    }

    fn source_function(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
        name: &str,
    ) -> ValidatedSingleCallable {
        let name = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let node = function.name?;
                let NodeData::Identifier(identifier) = &parsed.arena.get(node)?.data else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), SOURCE, node))
            })
            .unwrap();
        let type_ = context.get_type_at_location(name).unwrap();
        match validate_stored_single_callable(context.store(), type_) {
            StoredSingleCallableValidation::Valid { callable, .. } => callable,
            other => panic!("expected the real source function: {other:?}"),
        }
    }

    fn source_method(
        context: &mut CanonicalCheckerContext<'_>,
        parsed: &ParseResult,
    ) -> (TypeId, SignatureId) {
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
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set_with_array_targets(context.store(), callee, Some(targets))
        else {
            panic!("the source method overload group must be published")
        };
        assert_eq!(projection.call_signatures.len(), 2);
        let original = projection.call_signatures[0].signature;
        assert_eq!(
            context.store().signature(original).unwrap().declaration(),
            Some(declaration)
        );
        (callee, original)
    }

    fn spent_inherited_budget(
        store: &mut CanonicalTypeMapperStore,
        targets: CanonicalArrayTargets,
        proxy: SemanticSymbolId,
    ) -> InstantiationSession {
        let links = store.value_symbol_links(proxy).unwrap();
        assert_eq!(links.resolved_type, None);
        let mapper = links.mapper.unwrap();
        let template = store
            .value_symbol_links(links.target.unwrap())
            .unwrap()
            .resolved_type
            .unwrap();
        assert!(matches!(
            store.type_payload(template).unwrap().data(),
            TypeData::TypeParameter(_)
        ));
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut limited = InstantiationSession::new(InstantiationLimits {
            max_count: 1,
            ..InstantiationLimits::default()
        });
        // Spend the caller's budget on the real inherited mapper, without publishing its value.
        assert_eq!(
            instantiate_type_with_session(store, template, mapper, Some(targets), &mut limited),
            Ok(number)
        );
        assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
        assert_eq!(limited.limit_event_count(), 0);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        limited
    }

    fn cache_counts(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize, usize) {
        (
            store.type_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.cached_signature_len(),
        )
    }

    #[derive(Clone, Copy)]
    enum MethodRelationInput {
        FixedProperty,
        GenericProperty,
        GenericCallback,
    }

    #[allow(clippy::too_many_lines)] // One source graph checks spent limits, retry, and warm reuse.
    fn assert_spent_method_relation_budget(input: MethodRelationInput, assignable_pass: bool) {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; } ",
            "interface Box<T> { value: T; }",
        ));
        let declarations = match input {
            MethodRelationInput::FixedProperty => concat!(
                "interface Methods { m(tag: string, value: Plain): number; ",
                "m<T>(a: T, b: T, c: T): T; }",
            ),
            MethodRelationInput::GenericProperty => concat!(
                "interface Methods { m<U>(tag: string, value: Box<U>): number; ",
                "m(tag: string, value: number, extra: number): number; } ",
                "function warm(value: Box<number>): number { return value.value; }",
            ),
            MethodRelationInput::GenericCallback => concat!(
                "interface Callback { (...values: string[]): string; } ",
                "declare function choose<First, Second>(first?: First, second?: Second): Second; ",
                "interface Methods { m(tag: string, callback: Callback): number; ",
                "m<T>(a: T, b: T, c: T): T; }",
            ),
        };
        let parsed = parse_source_file(&format!(
            "interface Derived extends Base<number> {{}} \
             interface Plain {{ value: number; }} {declarations} \
             function keep(methods: Methods, derived: Derived): number {{ return 1; }}",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let derived = global_interface(context.store(), "Derived");
        let proxy = inherited_value(context.store());
        let (argument, parameter) = match input {
            MethodRelationInput::FixedProperty => {
                (derived, global_interface(context.store(), "Plain"))
            }
            MethodRelationInput::GenericProperty => (
                derived,
                source_function(&mut context, &parsed, "warm").parameters[0],
            ),
            MethodRelationInput::GenericCallback => (
                source_function(&mut context, &parsed, "choose").owner,
                global_interface(context.store(), "Callback"),
            ),
        };
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (string, number, any) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.any_type,
        );
        let explicit = [number];
        let arguments = [if assignable_pass { any } else { string }, argument];
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: matches!(input, MethodRelationInput::GenericProperty)
                .then_some(explicit.as_slice()),
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let prewarmed = if matches!(input, MethodRelationInput::GenericProperty) {
            // This resolves the checked parameter mapper without reading Derived.value.
            let warm_arguments = [string, parameter];
            let mut setup = InstantiationSession::new(InstantiationLimits::default());
            let selected = resolve_generic_method_call(
                store,
                &globals,
                false,
                GenericCallVectorRequest {
                    arguments: &warm_arguments,
                    ..request
                },
                None,
                &mut setup,
            )
            .unwrap()
            .unwrap();
            let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
                panic!("the explicit call must select its generic method")
            };
            assert_eq!(generic.projection().generic_signature, original);
            assert_eq!(generic.projection().instantiation.type_arguments, [number]);
            assert_eq!(
                store
                    .signature(generic.projection().instantiation.signature)
                    .unwrap()
                    .parameters()
                    .iter()
                    .map(|parameter| store.value_symbol_links(*parameter).unwrap().resolved_type)
                    .collect::<Vec<_>>(),
                [Some(string), Some(parameter)]
            );
            Some(selected)
        } else {
            None
        };
        let mut limited = spent_inherited_budget(store, targets, proxy);
        let expected = match input {
            MethodRelationInput::FixedProperty => {
                GenericMethodCallError::Relation(RelationUnavailable::UnsupportedProperty(proxy))
            }
            MethodRelationInput::GenericProperty => GenericMethodCallError::Generic(
                GenericCallVectorError::Relation(RelationUnavailable::UnsupportedProperty(proxy)),
            ),
            MethodRelationInput::GenericCallback => {
                GenericMethodCallError::Relation(RelationUnavailable::StructuralRelation {
                    source: argument,
                    target: parameter,
                    relation: if assignable_pass {
                        RelationKind::Assignable
                    } else {
                        RelationKind::Subtype
                    },
                })
            }
        };
        let mut failed_counts = None;
        for events in 1..=2 {
            let mark = limited.limit_event_mark();
            assert_eq!(
                resolve_generic_method_call(store, &globals, false, request, None, &mut limited)
                    .unwrap_err(),
                expected
            );
            assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
            assert!(limited.limit_event_occurred_since(mark));
            assert_eq!(limited.limit_event_count(), events);
            assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
            if let Some(failed_counts) = failed_counts {
                assert_eq!(cache_counts(store), failed_counts);
            } else {
                failed_counts = Some(cache_counts(store));
            }
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        assert!(prewarmed.as_ref().is_none_or(|warm| *warm == selected));
        let signature = match &selected.selected {
            GenericMethodCallSelection::Fixed {
                signature,
                return_type,
            } => {
                assert_eq!(*signature, original);
                assert_eq!(*return_type, number);
                *signature
            }
            GenericMethodCallSelection::Generic(generic) => {
                assert_eq!(generic.projection().generic_signature, original);
                assert_eq!(
                    demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                        .unwrap()
                        .0,
                    number
                );
                generic.projection().instantiation.signature
            }
        };
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            (!matches!(input, MethodRelationInput::GenericCallback)).then_some(number)
        );
        let warm = cache_counts(store);
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
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn fixed_method_candidates_preserve_the_callers_spent_relation_budget() {
        for assignable_pass in [false, true] {
            assert_spent_method_relation_budget(
                MethodRelationInput::FixedProperty,
                assignable_pass,
            );
        }
    }

    #[test]
    fn generic_method_candidates_preserve_the_callers_spent_relation_budget() {
        for assignable_pass in [false, true] {
            assert_spent_method_relation_budget(
                MethodRelationInput::GenericProperty,
                assignable_pass,
            );
        }
    }

    #[test]
    fn method_callback_inference_preserves_the_callers_spent_relation_budget() {
        for assignable_pass in [false, true] {
            assert_spent_method_relation_budget(
                MethodRelationInput::GenericCallback,
                assignable_pass,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The cold literal union must fail before parameter mapping.
    fn method_literal_candidate_unions_preserve_the_callers_spent_relation_budget() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; }",
        ));
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Methods { m<T>(first: T, second: T): T; ",
            "m(first: number, second: number, third: number): number; } ",
            "declare const derived: Derived; declare const plain: Plain; ",
            "const left = { child: derived }; const right = { child: plain };",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let literals = ["left", "right"].map(|name| {
            let node = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then(|| {
                        NodeRef::new(parsed.arena.id(), SOURCE, variable.initializer.unwrap())
                    })
                })
                .unwrap();
            let type_ = context.get_type_at_location(node).unwrap();
            assert!(
                context
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .intersects(ObjectFlags::OBJECT_LITERAL)
            );
            type_
        });
        assert_ne!(literals[0], literals[1]);
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let proxy = inherited_value(context.store());
        let store = context.store_mut_for_test();
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: None,
            has_spread_argument: false,
            callee,
            arguments: &literals,
        };
        let warm_arguments = [literals[1]; 2];
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let prewarmed = resolve_generic_method_call(
            store,
            &globals,
            false,
            GenericCallVectorRequest {
                arguments: &warm_arguments,
                ..request
            },
            None,
            &mut setup,
        )
        .unwrap()
        .unwrap();
        let GenericMethodCallSelection::Generic(generic) = &prewarmed.selected else {
            panic!("the two-argument call must select its generic method")
        };
        let signature = generic.projection().instantiation.signature;
        assert_eq!(generic.projection().generic_signature, original);
        let inferred = generic.projection().instantiation.type_arguments[0];
        assert_eq!(
            store.get_widened_type_with_global_types(literals[1], &globals),
            Ok(inferred)
        );
        assert!(
            store
                .signature(signature)
                .unwrap()
                .parameters()
                .iter()
                .all(|parameter| {
                    store.value_symbol_links(*parameter).unwrap().resolved_type == Some(inferred)
                })
        );
        let mut limited = spent_inherited_budget(store, targets, proxy);
        let before = cache_counts(store);
        // Subtype reduction visits the canonical type order in reverse.
        let failed_constituent = literals[0].max(literals[1]);
        for events in 1..=2 {
            assert_eq!(
                resolve_generic_method_call(store, &globals, false, request, None, &mut limited),
                Err(GenericMethodCallError::Generic(
                    GenericCallVectorError::Inference(NakedTypeCandidateError::Union(
                        LiteralTypeCacheError::UnsupportedUnionConstituent(failed_constituent)
                    ))
                ))
            );
            assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
            assert_eq!(limited.limit_event_count(), events);
            assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
            assert_eq!(cache_counts(store), before);
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected, prewarmed);
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("literal inference must retain the selected generic signature")
        };
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                .unwrap()
                .0,
            inferred
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().number_type)
        );
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let warm = cache_counts(store);
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
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
    }

    #[allow(clippy::too_many_lines)] // Restoring one lazy link forces the real cached union scan.
    fn assert_dirty_method_inference_budget(widening: bool) {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; }",
        ));
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Methods { m<T>(first: T, second: T): T; m(value: number): number; } ",
            "declare const first: 'one'; declare const second: 'two'; ",
            "const left = { one: 1 }; const right = { two: 'two' };",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let arguments = ["first", "second"].map(|name| {
            let node = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name)
                        .then(|| NodeRef::new(parsed.arena.id(), SOURCE, variable.type_.unwrap()))
                })
                .unwrap();
            context.get_type_at_location(node).unwrap()
        });
        let object_literals = widening.then(|| {
            ["left", "right"].map(|name| {
                let node = parsed
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::VariableDeclaration(variable) = &record.data else {
                            return None;
                        };
                        let NodeData::Identifier(identifier) =
                            &parsed.arena.get(variable.name)?.data
                        else {
                            return None;
                        };
                        (identifier.text == name).then(|| {
                            NodeRef::new(parsed.arena.id(), SOURCE, variable.initializer.unwrap())
                        })
                    })
                    .unwrap();
                context.get_type_at_location(node).unwrap()
            })
        });
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let derived = global_interface(context.store(), "Derived");
        let plain = global_interface(context.store(), "Plain");
        let proxy = inherited_value(context.store());
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let arguments = if let Some(object_literals) = object_literals {
            let union = store
                .expression_union_type_with_global_types_and_session(
                    &globals,
                    &object_literals,
                    UnionReduction::Literal,
                    &mut setup,
                )
                .unwrap();
            assert!(
                store
                    .type_payload(union)
                    .unwrap()
                    .object_flags()
                    .intersects(ObjectFlags::REQUIRES_WIDENING)
            );
            [union; 2]
        } else {
            arguments
        };
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
        store
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
        // Keep the source target and mapper. Only restore their supported lazy value state.
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: None,
                ..original_links
            }
        ));
        store.mark_union_cache_validation_dirty();
        let mut limited = spent_inherited_budget(store, targets, proxy);
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: None,
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let before = cache_counts(store);
        let scans = store.union_cache_validation_scan_count();
        let expected_error =
            GenericMethodCallError::Generic(GenericCallVectorError::Inference(if widening {
                NakedTypeCandidateError::Widening(DerivedTypeError::UnsupportedWideningType(
                    derived.max(plain),
                ))
            } else {
                NakedTypeCandidateError::Union(LiteralTypeCacheError::UnsupportedUnionConstituent(
                    derived.max(plain),
                ))
            }));
        for events in 1..=2 {
            assert_eq!(
                resolve_generic_method_call(store, &globals, false, request, None, &mut limited)
                    .unwrap_err(),
                expected_error
            );
            assert_eq!((limited.query_count(), limited.total_count()), (1, 1));
            assert_eq!(limited.limit_event_count(), events);
            assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
            assert_eq!(cache_counts(store), before);
            assert_eq!(
                store.union_cache_validation_scan_count(),
                scans + usize::try_from(events).unwrap()
            );
        }

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("the two literal arguments must select their generic method")
        };
        assert_eq!(generic.projection().generic_signature, original);
        let expected = if widening {
            store
                .get_widened_type_with_global_types_and_session(
                    arguments[0],
                    &globals,
                    &mut adequate,
                )
                .unwrap()
        } else {
            store
                .expression_union_type_with_global_types_and_session(
                    &globals,
                    &arguments,
                    UnionReduction::Literal,
                    &mut adequate,
                )
                .unwrap()
        };
        assert_eq!(
            generic.projection().instantiation.type_arguments,
            [expected]
        );
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                .unwrap()
                .0,
            expected
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(number)
        );
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let signature = generic.projection().instantiation.signature;
        let warm = cache_counts(store);
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
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
    }

    #[test]
    fn method_literal_inference_revalidates_dirty_unions_with_the_callers_spent_budget() {
        assert_dirty_method_inference_budget(false);
    }

    #[test]
    fn method_inference_widening_revalidates_dirty_unions_with_the_callers_spent_budget() {
        assert_dirty_method_inference_budget(true);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Mapping and cache validation must share one count limit.
    fn method_union_parameter_mapping_revalidates_dirty_unions_with_the_caller() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: number; }",
        ));
        let parsed = parse_source_file(concat!(
            "interface Derived extends Base<number> {} ",
            "interface Plain { value: number; } ",
            "interface Methods { m<T>(value: T | string): T; m(a: number, b: number): number; }",
        ));
        let mut context = relation_context(&library, &parsed);
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty());
        let (callee, original) = source_method(&mut context, &parsed);
        let globals = context.global_types().clone();
        let derived = global_interface(context.store(), "Derived");
        let plain = global_interface(context.store(), "Plain");
        let proxy = inherited_value(context.store());
        let TypeData::Interface(data) = context.store().type_payload(derived).unwrap().data()
        else {
            panic!("Derived must retain its source interface")
        };
        let base = data.resolved_base_types.as_ref().unwrap()[0];
        let store = context.store_mut_for_test();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mut setup = InstantiationSession::new(InstantiationLimits::default());
        let source_union = store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[number, derived],
                UnionReduction::Literal,
                &mut setup,
            )
            .unwrap();
        store
            .expression_union_type_with_global_types_and_session(
                &globals,
                &[source_union, plain],
                UnionReduction::Subtype,
                &mut setup,
            )
            .unwrap();
        let original_links = store.value_symbol_links(proxy).unwrap().clone();
        assert_eq!(original_links.resolved_type, Some(number));
        assert!(store.set_value_symbol_links(
            proxy,
            ValueSymbolLinks {
                resolved_type: None,
                ..original_links
            }
        ));
        store.mark_union_cache_validation_dirty();
        assert_eq!(
            validate_interface_heritage_members(store, derived),
            InterfaceHeritageMembersValidation::Valid
        );
        assert!(
            validate_generic_interface_members(store, base, None)
                .unwrap()
                .is_some()
        );
        let arguments = [number];
        let request = GenericCallVectorRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            explicit_type_arguments: Some(&arguments),
            has_spread_argument: false,
            callee,
            arguments: &arguments,
        };
        let mut limited = InstantiationSession::new(InstantiationLimits {
            max_count: 2,
            ..InstantiationLimits::default()
        });
        let before = cache_counts(store);
        // The real union frame and T substitution spend both available instantiations.
        assert_eq!(
            resolve_generic_method_call(store, &globals, false, request, None, &mut limited),
            Err(GenericMethodCallError::Generic(
                GenericCallVectorError::Instantiation(InstantiationError::Union(
                    LiteralTypeCacheError::UnsupportedUnionConstituent(derived.max(plain))
                ))
            ))
        );
        assert_eq!((limited.query_count(), limited.total_count()), (2, 2));
        assert_eq!(limited.limit_event_count(), 1);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        let CachedSignatureLookup::Hit(signature) =
            store.cached_signature(original, type_list_key(&arguments), &arguments)
        else {
            panic!("the failed parameter demand must retain its checked shell")
        };
        assert_eq!(store.signature(signature).unwrap().target(), Some(original));
        let parameter = store.signature(signature).unwrap().parameters()[0];
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            None
        );
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().target,
            Some(store.signature(original).unwrap().parameters()[0])
        );
        let failed = cache_counts(store);
        assert_eq!(failed.3, before.3 + 1);
        assert_eq!(failed.4, before.4 + 1);
        let scans = store.union_cache_validation_scan_count();
        // A second request in the same query stops before mapping. The resolver cannot reset it.
        assert_eq!(
            resolve_generic_method_call(store, &globals, false, request, None, &mut limited),
            Err(GenericMethodCallError::Generic(
                GenericCallVectorError::Instantiation(InstantiationError::CountLimit {
                    count: 2,
                    limit: 2
                })
            ))
        );
        assert_eq!((limited.query_count(), limited.total_count()), (2, 2));
        assert_eq!(limited.limit_event_count(), 2);
        assert_eq!(store.value_symbol_links(proxy).unwrap().resolved_type, None);
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            None
        );
        assert_eq!(store.union_cache_validation_scan_count(), scans);
        assert_eq!(cache_counts(store), failed);

        let mut adequate = InstantiationSession::new(InstantiationLimits::default());
        let selected =
            resolve_generic_method_call(store, &globals, false, request, None, &mut adequate)
                .unwrap()
                .unwrap();
        assert_eq!(selected.diagnostic, None);
        let GenericMethodCallSelection::Generic(generic) = &selected.selected else {
            panic!("the explicit call must select its generic method")
        };
        assert_eq!(generic.projection().generic_signature, original);
        assert_eq!(generic.projection().instantiation.signature, signature);
        assert_eq!(generic.projection().instantiation.type_arguments, arguments);
        assert_eq!(
            store.value_symbol_links(parameter).unwrap().resolved_type,
            Some(store.intrinsic_bootstrap().unwrap().string_or_number_type)
        );
        assert_eq!(
            demand_generic_call_vector_selected_return(store, generic, &mut adequate)
                .unwrap()
                .0,
            number
        );
        assert_eq!(
            store.value_symbol_links(proxy).unwrap().resolved_type,
            Some(number)
        );
        assert!(adequate.total_count() > 0);
        assert_eq!(adequate.limit_event_count(), 0);
        let warm = cache_counts(store);
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
            assert_eq!(adequate.total_count(), count);
            assert_eq!(adequate.limit_event_count(), 0);
            assert_eq!(cache_counts(store), warm);
        }
    }
}
