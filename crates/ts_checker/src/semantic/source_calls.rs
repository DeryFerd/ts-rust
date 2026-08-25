//! Exact source integration for identifier, nested, immediate, or property calls.
//!
//! This admits `identifier(arguments)`, authenticated public or private
//! property calls and tagged templates, proven nested call callees, and
//! immediately invoked anonymous or async callables.
//! Arguments may contain scalar
//! values, interpolated templates, identifier and property reads, object and
//! array literals, arrow or anonymous functions, type assertions, nested direct
//! calls, or recursively proven primitive expressions, optionally parenthesized.
//! The semantic kernel remains in `calls`; this module owns the AST proof,
//! lazy-return/relation retries, call caches, and source diagnostics.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalCheckerRelatedInformation, CanonicalGlobalTypes,
    CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    ResolvedSignatureState, SignatureId, SignatureLinks, TypeId, TypeNodeLinks, ValueSymbolLinks,
    bootstrap::UnionReduction,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::{StoredSingleCallableValidation, validate_stored_single_callable},
    calls::{
        DirectCallApplicability, DirectCallError, DirectCallForm, DirectCallRequest,
        DirectCallUnsupported, resolve_direct_call,
    },
    declared::{cached_ordinary_type_parameter_owner, execute_type_parameter, type_list_key},
    formatter::{
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
        type_to_string_with_host_global_types_and_flags,
    },
    generic_calls::{
        GenericCallVectorApplicability, GenericCallVectorError, GenericCallVectorRequest,
        GenericCallVectorResolution, GenericCallVectorUnsupported, IdentityGenericCallError,
        IdentityGenericCallRequest, IdentityGenericCallResolution, IdentityGenericCallUnsupported,
        demand_generic_call_vector_return_with_session,
        demand_identity_generic_call_return_with_session, materialize_generic_call_vector_source,
        resolve_generic_call_vector_with_session,
        resolve_source_identity_generic_call_with_session,
        source_declared_inference_candidate_is_exported,
    },
    inference::{NakedTypeCandidateError, NakedTypeInferenceError},
    instantiate::{InstantiationLimits, InstantiationSession},
    object_diagnostics::{
        callable_assignability_details, exact_optional_property_mismatch_details,
        excess_object_argument_diagnostic, missing_mapped_index_signature_details,
    },
    signatures::{SignatureFlags, TypePredicateKind},
    source::{
        PlannedExpression, PlannedExpressionKind, PlannedIdentifierReadKind, SourceCheckError,
        UnsupportedSourceSyntax, logical_binary_operator_text, merge_retry_diagnostic,
        merge_retry_diagnostics, primitive_binary_operator_text,
        retry_source_generic_member_failure,
    },
    source_callables::{
        CallableTypePredicatePlan, StoredSourceCallableValidation, plan_callable_type_predicate,
        valid_fixed_generic_source_parameter_type, valid_planned_callable_type_predicate,
        valid_stored_callable_type_predicate, validate_stored_source_callable,
    },
    source_imports::synthetic_source_import_origin,
    source_new::promise_executor_missing_argument_is_exact,
    store::{CachedSignatureLookup, SourceNodeParent},
    tuple_types::CanonicalTupleTypeRequest,
    type_nodes::CanonicalTypeQuery,
    type_records::{TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// Fully proven syntax plus source-planned callee and arguments.
#[derive(Clone, Debug)]
pub(super) struct SourceCallPlan {
    pub(super) node: NodeRef,
    pub(super) callee: PlannedExpression,
    form: DirectCallForm,
    callee_diagnostic_node: NodeRef,
    type_arguments: Option<SourceTypeArgumentList>,
    pub(super) arguments: Vec<PlannedExpression>,
}

/// The exact callee family proven by call syntax.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallCalleeForm {
    /// An identifier or nested call planned through the ordinary expression path.
    Identifier,
    RequiredOwnProperty,
    /// One authenticated zero-argument parenthesized async arrow.
    ParenthesizedAsyncArrow,
}

/// Exact parser-owned type-argument list syntax retained for checker recovery.
///
/// The local parser stores the surrounding angle brackets in `NodeList.range`,
/// while pinned TypeScript-Go stores the list range after `<` and before `>`.
/// `syntax_range` retains the complete bracketed list for grammar TS1099.
/// `diagnostic_range` retains the first type token through the last type token
/// or trailing comma for TS2558, excluding outer trivia and angle brackets. An
/// empty list remains present because call resolution treats it as inference.
#[derive(Clone, Debug)]
struct SourceTypeArgumentList {
    nodes: Vec<NodeRef>,
    syntax_range: TextRange,
    diagnostic_range: Option<TextRange>,
    trailing_comma_range: Option<TextRange>,
}

#[derive(Clone, Debug)]
pub(super) struct DirectSourceCallSyntax {
    node: NodeRef,
    callee: NodeRef,
    form: DirectCallForm,
    callee_form: SourceCallCalleeForm,
    callee_diagnostic_node: NodeRef,
    type_arguments: Option<SourceTypeArgumentList>,
    arguments: Vec<NodeRef>,
    argument_arrow_nodes: Vec<Option<NodeRef>>,
    array_argument_arrow_nodes: Vec<Vec<NodeRef>>,
}

impl DirectSourceCallSyntax {
    pub(super) fn callee(&self) -> NodeRef {
        self.callee
    }

    pub(super) fn callee_form(&self) -> SourceCallCalleeForm {
        self.callee_form
    }

    pub(super) fn callee_diagnostic_node(&self) -> NodeRef {
        self.callee_diagnostic_node
    }

    pub(super) fn arguments(&self) -> &[NodeRef] {
        &self.arguments
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceCall {
    pub(super) return_type: TypeId,
}

#[derive(Clone, Copy, Debug)]
struct GlobalArrayFindIndexParameter {
    symbol: SemanticSymbolId,
    annotation: NodeRef,
}

#[derive(Clone, Copy, Debug)]
struct GlobalArrayFindIndexMethod {
    owner: SemanticSymbolId,
    target: TypeId,
    element: TypeId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    predicate: GlobalArrayFindIndexParameter,
    this_arg: GlobalArrayFindIndexParameter,
    return_annotation: NodeRef,
}

/// Recognizes only the source spelling of the ES2015 array search method.
pub(super) fn source_is_global_array_find_index_method(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> bool {
    let Some(NodeData::PropertyAccessExpression(access)) =
        host.node(node).map(|record| &record.data)
    else {
        return false;
    };
    let name = NodeRef::new(node.arena, node.file, access.name);
    matches!(
        host.node(name).map(|record| &record.data),
        Some(NodeData::Identifier(identifier)) if identifier.text == "findIndex"
    )
}

fn plan_global_array_find_index_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    method: NodeRef,
    declaration: NodeRef,
    expected_name: &str,
    optional: bool,
) -> Result<GlobalArrayFindIndexParameter, SourceCheckError> {
    let invalid = || SourceCheckError::Call(method);
    let record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter) = &record.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, parameter.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    let annotation = parameter
        .type_
        .map(|annotation| NodeRef::new(declaration.arena, declaration.file, annotation))
        .ok_or_else(invalid)?;
    let annotation_record = host.node(annotation).ok_or_else(invalid)?;
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let symbol = bound
        .symbol(declaration)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::Parameter
        || record.flags.0 != 0
        || record.parent != Some(method.node)
        || parameter.dot_dot_dot_token.is_some()
        || parameter.initializer.is_some()
        || parameter.symbol.is_some()
        || parameter.modifiers.is_some()
        || parameter.facts != 0
        || parameter.question_token.is_some() != optional
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text != expected_name
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(expected_name)
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(invalid());
    }
    Ok(GlobalArrayFindIndexParameter { symbol, annotation })
}

fn plan_global_array_find_index_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
    site: NodeRef,
) -> Result<Option<GlobalArrayFindIndexMethod>, SourceCheckError> {
    let invalid = || SourceCheckError::Call(site);
    let Some(array) = store
        .canonical_array_reference(global_types, receiver)
        .map_err(|_| invalid())?
    else {
        return Ok(None);
    };
    let (target, owner_name) = if array.readonly {
        (global_types.readonly_array_type, "ReadonlyArray")
    } else {
        (global_types.array_type, "Array")
    };
    let target_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(invalid());
    };
    let [element] = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .ok_or_else(invalid)?
    else {
        return Err(invalid());
    };
    let element = *element;
    let owner = target_record
        .symbol()
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let globals = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .ok_or_else(invalid)?;
    let allowed_owner_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if globals
        .get_source(owner_name)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        != Some(owner)
        || owner_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner_record.flags().without(allowed_owner_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some(owner_name)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(target)
    {
        return Err(invalid());
    }
    let Some(symbol) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source("findIndex"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let method = store.symbol(symbol).ok_or_else(invalid)?;
    let Some([declaration]) = method.declarations() else {
        return Ok(None);
    };
    let declaration = *declaration;
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::MethodSignatureDeclaration(syntax) = &record.data else {
        return Err(invalid());
    };
    let [predicate, this_arg] = syntax.parameters.nodes.as_slice() else {
        return Ok(None);
    };
    let name = NodeRef::new(declaration.arena, declaration.file, syntax.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    let return_annotation = syntax
        .type_
        .map(|annotation| NodeRef::new(declaration.arena, declaration.file, annotation))
        .ok_or_else(invalid)?;
    let return_record = host.node(return_annotation).ok_or_else(invalid)?;
    if method.flags() != SymbolFlags::METHOD
        || method.check_flags() != CheckFlags::NONE
        || method.name().as_utf8() != Some("findIndex")
        || method.value_declaration() != Some(declaration)
        || method.members().is_some()
        || method.exports().is_some()
        || method.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || !host.symbol_matches(store, declaration, symbol)
        || bound.source_facts().is_none_or(|facts| {
            !facts.is_default_library()
                || !facts.is_declaration_file()
                || facts.is_javascript_file()
                || facts.is_external_or_common_js_module()
        })
        || record.kind != SyntaxKind::MethodSignature
        || record.flags.0 != 0
        || syntax.full_signature.is_some()
        || syntax.next_container.is_some()
        || syntax.postfix_token.is_some()
        || syntax.symbol.is_some()
        || syntax.type_parameters.is_some()
        || syntax.modifiers.is_some()
        || syntax.parameters.has_trailing_comma
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text != "findIndex"
        || return_record.kind != SyntaxKind::NumberKeyword
        || return_record.flags.0 != 0
        || return_record.parent != Some(declaration.node)
    {
        return Err(invalid());
    }
    let predicate = plan_global_array_find_index_parameter(
        store,
        host,
        declaration,
        NodeRef::new(declaration.arena, declaration.file, *predicate),
        "predicate",
        false,
    )?;
    let this_arg = plan_global_array_find_index_parameter(
        store,
        host,
        declaration,
        NodeRef::new(declaration.arena, declaration.file, *this_arg),
        "thisArg",
        true,
    )?;
    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals))
        .ok_or_else(invalid)?;
    let callback_record = host.node(predicate.annotation).ok_or_else(invalid)?;
    let NodeData::FunctionTypeNode(callback) = &callback_record.data else {
        return Err(invalid());
    };
    let callback_return = callback
        .type_
        .map(|annotation| {
            NodeRef::new(
                predicate.annotation.arena,
                predicate.annotation.file,
                annotation,
            )
        })
        .ok_or_else(invalid)?;
    let callback_return_record = host.node(callback_return).ok_or_else(invalid)?;
    if callback_record.kind != SyntaxKind::FunctionType
        || callback_record.flags.0 != 0
        || callback_record.parent
            != store
                .symbol(predicate.symbol)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .map(|parameter| parameter.node)
        || callback.full_signature.is_some()
        || callback.next_container.is_some()
        || callback.symbol.is_some()
        || callback.type_parameters.is_some()
        || callback.modifiers.is_some()
        || callback.parameters.has_trailing_comma
        || callback.parameters.nodes.len() != 3
        || callback_return_record.kind != SyntaxKind::UnknownKeyword
        || callback_return_record.flags.0 != 0
        || callback_return_record.parent != Some(predicate.annotation.node)
        || store.source_node_kind(this_arg.annotation) != Some(SyntaxKind::AnyKeyword)
        || locals.len() != 2
        || locals.get_source("predicate") != Some(predicate.symbol)
        || locals.get_source("thisArg") != Some(this_arg.symbol)
    {
        return Err(invalid());
    }

    Ok(Some(GlobalArrayFindIndexMethod {
        owner,
        target,
        element,
        symbol,
        declaration,
        predicate,
        this_arg,
        return_annotation,
    }))
}

/// Publishes the exact default-library `findIndex` method without expanding Array.
#[allow(clippy::too_many_arguments)] // Method publication retains the caller's checker context.
pub(super) fn materialize_global_array_find_index_method(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    receiver: TypeId,
    site: NodeRef,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(plan) =
        plan_global_array_find_index_method(store, host, global_types, receiver, site)?
    else {
        return Ok(None);
    };
    let invalid = || SourceCheckError::Call(site);
    let (any, number, unknown) = {
        let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
        (
            bootstrap.any_type,
            bootstrap.number_type,
            bootstrap.unknown_type,
        )
    };
    if let Some(links) = store.value_symbol_links(plan.symbol)
        && links != &ValueSymbolLinks::default()
    {
        let type_ = links.resolved_type.ok_or_else(invalid)?;
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, type_)
        else {
            return Err(invalid());
        };
        let [signature] = projection.call_signatures.as_ref() else {
            return Err(invalid());
        };
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
            || !projection.construct_signatures.is_empty()
            || signature.parameters.len() != 2
            || signature.min_argument_count != 1
            || signature.return_type != Some(number)
            || store
                .signature(signature.signature)
                .and_then(super::signatures::Signature::declaration)
                != Some(plan.declaration)
        {
            return Err(invalid());
        }
        return Ok(Some(type_));
    }
    if [plan.predicate.symbol, plan.this_arg.symbol]
        .iter()
        .any(|symbol| {
            store
                .value_symbol_links(*symbol)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
        })
        || store
            .signature_links(plan.declaration)
            .is_some_and(|links| links != &SignatureLinks::default())
    {
        return Err(invalid());
    }

    let callback =
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
            .get_type_from_type_node(plan.predicate.annotation)?;
    let StoredSingleCallableValidation::Valid {
        callable: callback_signature,
        ..
    } = validate_stored_single_callable(store, callback)
    else {
        return Err(invalid());
    };
    let callback_return =
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
            .get_return_type_of_signature(callback_signature.signature)?;
    let StoredSingleCallableValidation::Valid {
        callable: callback_signature,
        ..
    } = validate_stored_single_callable(store, callback)
    else {
        return Err(invalid());
    };
    let [element, index, array] = callback_signature.parameters.as_slice() else {
        return Err(invalid());
    };
    if *element != plan.element
        || *index != number
        || callback_return != unknown
        || callback_signature.return_type != Some(unknown)
        || callback_signature.rest_parameter.is_some()
        || callback_signature.min_argument_count != 3
        || store
            .canonical_array_reference(global_types, *array)
            .map_err(|_| invalid())?
            .is_none_or(|array| {
                array.element_type != plan.element
                    || array.readonly != (plan.target == global_types.readonly_array_type)
            })
        || store
            .authenticated_interface_method_owner(plan.symbol)
            .is_none_or(|(owner, target)| owner != plan.owner || target != plan.target)
    {
        return Err(invalid());
    }

    if !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(usize::from(
            store.signature_links(plan.declaration).is_none(),
        ))
        || !store.try_reserve_value_symbol_links(
            usize::from(store.value_symbol_links(plan.symbol).is_none())
                + usize::from(store.value_symbol_links(plan.predicate.symbol).is_none())
                + usize::from(store.value_symbol_links(plan.this_arg.symbol).is_none()),
        )
        || !store.try_reserve_function_signature_return_annotations(1)
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(invalid());
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .ok_or_else(invalid)?;
    let signature = store
        .alloc_signature(
            SignatureFlags::NONE,
            Some(plan.declaration),
            Vec::new(),
            None,
            vec![plan.predicate.symbol, plan.this_arg.symbol],
            Some(number),
            None,
            1,
        )
        .ok_or_else(invalid)?;
    assert!(store.set_signature_links(
        plan.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    for (symbol, type_) in [
        (plan.predicate.symbol, callback),
        (plan.this_arg.symbol, any),
    ] {
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
    }
    assert!(store.set_value_symbol_links(
        plan.symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(
        type_,
        None,
        None,
        Some(vec![signature]),
        None,
        None
    ));
    assert!(store.set_function_signature_return_annotation(
        signature,
        plan.return_annotation,
        false,
    ));
    assert!(
        store.set_callable_signature_parameter_types_batch(vec![(signature, vec![callback, any])])
    );
    if !matches!(
        validate_stored_callable_set(store, type_),
        StoredCallableSetValidation::Valid { .. }
    ) {
        return Err(invalid());
    }
    Ok(Some(type_))
}

fn check_authenticated_array_find_index_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_types: &[TypeId],
) -> Result<Option<CheckedSourceCall>, SourceCheckError> {
    if plan.form != DirectCallForm::Call
        || plan.type_arguments.is_some()
        || !(1..=2).contains(&argument_types.len())
    {
        return Ok(None);
    }
    let PlannedExpressionKind::Property(property) = &plan.callee.unparenthesized().kind else {
        return Ok(None);
    };
    let Some(method) = store.type_payload(callee_type).and_then(TypeRecord::symbol) else {
        return Ok(None);
    };
    let Some(method_record) = store.symbol(method) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    if method_record.flags() != SymbolFlags::METHOD
        || method_record.name().as_utf8() != Some("findIndex")
        || store
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            != Some(callee_type)
    {
        return Ok(None);
    }
    let receiver = store
        .type_node_links(property.receiver.node)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let Some(array) = store
        .canonical_array_reference(global_types, receiver)
        .map_err(|_| SourceCheckError::Call(plan.node))?
    else {
        return Ok(None);
    };
    let target = if array.readonly {
        global_types.readonly_array_type
    } else {
        global_types.array_type
    };
    if store
        .authenticated_interface_method_owner(method)
        .is_none_or(|(_, owner)| owner != target)
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    let StoredCallableSetValidation::Valid {
        projection: method_projection,
        ..
    } = validate_stored_callable_set(store, callee_type)
    else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let [method_signature] = method_projection.call_signatures.as_ref() else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let number = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.number_type)
        .ok_or(SourceCheckError::Call(plan.node))?;
    if !method_projection.construct_signatures.is_empty()
        || method_signature.parameters.len() != 2
        || method_signature.min_argument_count != 1
        || method_signature.return_type != Some(number)
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    let callback = argument_types[0];
    let StoredCallableSetValidation::Valid {
        projection: callback_projection,
        ..
    } = validate_stored_callable_set(store, callback)
    else {
        return Ok(None);
    };
    let Some(callback_signature) = callback_projection.call_signatures.first() else {
        return Ok(None);
    };
    if callback_signature.rest_parameter.is_some()
        || callback_signature.parameters.len() > 3
        || callback_signature.min_argument_count > 3
    {
        return Ok(None);
    }
    for (provided, expected) in [array.element_type, number, receiver]
        .into_iter()
        .zip(&callback_signature.parameters)
    {
        if !store
            .is_type_assignable_to_with_global_types(provided, *expected, global_types)
            .map_err(SourceCheckError::RelationUnavailable)?
        {
            return Ok(None);
        }
    }
    if preflight_call_publication(store, plan.node, number)?
        .is_some_and(|existing| existing != method_signature.signature)
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    publish_call_links(store, plan.node, method_signature.signature, number)?;
    Ok(Some(CheckedSourceCall {
        return_type: number,
    }))
}

#[derive(Clone, Debug)]
struct GlobalArrayCallbackParameter {
    symbol: SemanticSymbolId,
    annotation: NodeRef,
    optional: bool,
}

#[derive(Clone, Copy, Debug)]
struct GlobalArrayCallbackTypeParameter {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    constraint: Option<NodeRef>,
}

#[derive(Clone, Debug)]
struct GlobalArrayCallbackOverload {
    declaration: NodeRef,
    callback_annotation: NodeRef,
    callback_predicate: Option<CallableTypePredicatePlan>,
    return_annotation: NodeRef,
    parameters: Vec<GlobalArrayCallbackParameter>,
    type_parameters: Vec<GlobalArrayCallbackTypeParameter>,
}

#[derive(Clone, Debug)]
struct GlobalArrayCallbackMethod {
    owner: SemanticSymbolId,
    target: TypeId,
    symbol: SemanticSymbolId,
    overloads: Vec<GlobalArrayCallbackOverload>,
}

#[derive(Clone, Debug)]
struct ResolvedGlobalArrayCallbackOverload {
    type_parameters: Vec<TypeId>,
    parameter_types: Vec<TypeId>,
    return_type: TypeId,
}

/// Returns an exact `Array` callback method name from a property access.
pub(super) fn source_global_array_callback_method_name(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Option<String> {
    let NodeData::PropertyAccessExpression(property) = &host.node(node)?.data else {
        return None;
    };
    let name = NodeRef::new(node.arena, node.file, property.name);
    let NodeData::Identifier(identifier) = &host.node(name)?.data else {
        return None;
    };
    matches!(
        identifier.text.as_str(),
        "map" | "filter" | "find" | "forEach" | "reduce"
    )
    .then(|| identifier.text.clone())
}

#[allow(clippy::too_many_lines)] // Authenticate every declaration before exposing the method.
fn plan_global_array_callback_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
    name: &str,
    site: NodeRef,
) -> Result<Option<GlobalArrayCallbackMethod>, SourceCheckError> {
    if !matches!(name, "map" | "filter" | "find" | "forEach") {
        return Ok(None);
    }
    let Some(array) = store
        .canonical_array_reference(global_types, receiver)
        .map_err(|_| SourceCheckError::Call(site))?
    else {
        return Ok(None);
    };
    let (target, owner_name) = if array.readonly {
        (global_types.readonly_array_type, "ReadonlyArray")
    } else {
        (global_types.array_type, "Array")
    };
    let owner = store
        .type_payload(target)
        .and_then(TypeRecord::symbol)
        .and_then(|owner| store.get_merged_symbol(owner))
        .ok_or(SourceCheckError::Call(site))?;
    let owner_record = store.symbol(owner).ok_or(SourceCheckError::Call(site))?;
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source(owner_name))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let Some(symbol) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get_source(name))
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let method = store.symbol(symbol).ok_or(SourceCheckError::Call(site))?;
    let Some(declarations) = method
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Ok(None);
    };
    let allowed_owner_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if global != Some(owner)
        || owner_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner_record.flags().without(allowed_owner_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some(owner_name)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || method.flags() != SymbolFlags::METHOD
        || method.check_flags() != CheckFlags::NONE
        || method.name().as_utf8() != Some(name)
        || method.value_declaration() != declarations.first().copied()
        || method.members().is_some()
        || method.exports().is_some()
        || method.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store.get_merged_symbol(symbol) != Some(symbol)
    {
        return Err(SourceCheckError::Call(site));
    }

    let mut overloads = Vec::with_capacity(declarations.len());
    let mut seen_declarations = HashSet::with_capacity(declarations.len());
    for declaration in declarations {
        if !seen_declarations.insert(*declaration) {
            return Err(SourceCheckError::Call(site));
        }
        let Some(SourceNodeParent::Parent(interface)) = store.source_node_parent(*declaration)
        else {
            return Err(SourceCheckError::Call(site));
        };
        if !owner_record
            .declarations()
            .is_some_and(|declarations| declarations.contains(&interface))
            || store.source_node_kind(interface) != Some(SyntaxKind::InterfaceDeclaration)
        {
            return Err(SourceCheckError::Call(site));
        }
        overloads.push(plan_global_array_callback_overload(
            store,
            host,
            symbol,
            *declaration,
            site,
        )?);
    }

    let supported = match (name, overloads.as_slice()) {
        ("forEach", [overload]) => {
            overload.type_parameters.is_empty() && overload.callback_predicate.is_none()
        }
        ("map", [overload]) => {
            overload.type_parameters.len() == 1
                && overload.type_parameters[0].constraint.is_none()
                && overload.callback_predicate.is_none()
        }
        ("filter" | "find", [predicate, ordinary]) => {
            predicate.type_parameters.len() == 1
                && predicate.type_parameters[0].constraint.is_some()
                && predicate.callback_predicate.is_some()
                && ordinary.type_parameters.is_empty()
                && ordinary.callback_predicate.is_none()
        }
        _ => false,
    };
    if !supported {
        return Ok(None);
    }

    Ok(Some(GlobalArrayCallbackMethod {
        owner,
        target,
        symbol,
        overloads,
    }))
}

#[allow(clippy::too_many_lines)] // One overload retains all binder-owned parameter identities.
fn plan_global_array_callback_overload(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    method: SemanticSymbolId,
    declaration: NodeRef,
    site: NodeRef,
) -> Result<GlobalArrayCallbackOverload, SourceCheckError> {
    let Some(bound) = host.bound_file(declaration) else {
        return Err(SourceCheckError::Call(site));
    };
    let Some(record) = host.node(declaration) else {
        return Err(SourceCheckError::Call(site));
    };
    let NodeData::MethodSignatureDeclaration(syntax) = &record.data else {
        return Err(SourceCheckError::Call(site));
    };
    if record.kind != SyntaxKind::MethodSignature
        || record.flags.0 != 0
        || syntax.full_signature.is_some()
        || syntax.next_container.is_some()
        || syntax.postfix_token.is_some()
        || syntax.symbol.is_some()
        || syntax.modifiers.is_some()
        || syntax.parameters.has_trailing_comma
        || syntax.parameters.nodes.is_empty()
        || bound
            .source_facts()
            .is_none_or(|facts| !facts.is_default_library() || !facts.is_declaration_file())
        || !host.symbol_matches(store, declaration, method)
    {
        return Err(SourceCheckError::Call(site));
    }

    let mut type_parameters = Vec::new();
    if let Some(parameters) = syntax.type_parameters.as_ref() {
        if parameters.nodes.len() != 1 || parameters.has_trailing_comma {
            return Err(SourceCheckError::Call(site));
        }
        let parameter = NodeRef::new(declaration.arena, declaration.file, parameters.nodes[0]);
        let Some(parameter_record) = host.node(parameter) else {
            return Err(SourceCheckError::Call(site));
        };
        let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
            return Err(SourceCheckError::Call(site));
        };
        let name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
        let Some(name_record) = host.node(name) else {
            return Err(SourceCheckError::Call(site));
        };
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(SourceCheckError::Call(site));
        };
        let symbol = bound
            .symbol(parameter)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or(SourceCheckError::Call(site))?;
        let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Call(site))?;
        let constraint = parameter_data
            .constraint
            .map(|node| NodeRef::new(parameter.arena, parameter.file, node));
        if parameter_record.kind != SyntaxKind::TypeParameter
            || parameter_record.flags.0 != 0
            || parameter_record.parent != Some(declaration.node)
            || parameter_data.default_type.is_some()
            || parameter_data.expression.is_some()
            || parameter_data.symbol.is_some()
            || parameter_data.modifiers.is_some()
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(parameter.node)
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
            || symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || bound
                .locals(declaration)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get(symbol_record.name()))
                != Some(symbol)
            || constraint.is_some_and(|constraint| {
                host.node(constraint).is_none_or(|record| {
                    record.flags.0 != 0 || record.parent != Some(parameter.node)
                })
            })
        {
            return Err(SourceCheckError::Call(site));
        }
        type_parameters.push(GlobalArrayCallbackTypeParameter {
            declaration: parameter,
            symbol,
            constraint,
        });
    }

    let return_annotation = syntax
        .type_
        .map(|annotation| NodeRef::new(declaration.arena, declaration.file, annotation))
        .ok_or(SourceCheckError::Call(site))?;
    let mut parameters = Vec::with_capacity(syntax.parameters.nodes.len());
    for parameter in &syntax.parameters.nodes {
        let parameter_declaration = NodeRef::new(declaration.arena, declaration.file, *parameter);
        let Some(record) = host.node(parameter_declaration) else {
            return Err(SourceCheckError::Call(site));
        };
        let NodeData::ParameterDeclaration(parameter) = &record.data else {
            return Err(SourceCheckError::Call(site));
        };
        let symbol = bound
            .symbol(parameter_declaration)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or(SourceCheckError::Call(site))?;
        let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Call(site))?;
        let annotation = parameter
            .type_
            .map(|annotation| {
                NodeRef::new(
                    parameter_declaration.arena,
                    parameter_declaration.file,
                    annotation,
                )
            })
            .ok_or(SourceCheckError::Call(site))?;
        if record.kind != SyntaxKind::Parameter
            || record.parent != Some(declaration.node)
            || record.flags.0 != 0
            || parameter.dot_dot_dot_token.is_some()
            || parameter.initializer.is_some()
            || parameter.symbol.is_some()
            || parameter.modifiers.is_some()
            || parameter.facts != 0
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.declarations() != Some(&[parameter_declaration])
            || symbol_record.value_declaration() != Some(parameter_declaration)
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
        {
            return Err(SourceCheckError::Call(site));
        }
        parameters.push(GlobalArrayCallbackParameter {
            symbol,
            annotation,
            optional: parameter.question_token.is_some(),
        });
    }
    let callback_annotation = parameters[0].annotation;
    if store.source_node_kind(callback_annotation) != Some(SyntaxKind::FunctionType)
        || parameters[0].optional
        || parameters
            .iter()
            .skip(1)
            .any(|parameter| !parameter.optional)
    {
        return Err(SourceCheckError::Call(site));
    }

    let Some(callback_record) = host.node(callback_annotation) else {
        return Err(SourceCheckError::Call(site));
    };
    let NodeData::FunctionTypeNode(callback) = &callback_record.data else {
        return Err(SourceCheckError::Call(site));
    };
    let callback_return = callback
        .type_
        .map(|node| NodeRef::new(callback_annotation.arena, callback_annotation.file, node))
        .ok_or(SourceCheckError::Call(site))?;
    let callback_predicate =
        if store.source_node_kind(callback_return) == Some(SyntaxKind::TypePredicate) {
            let predicate = plan_callable_type_predicate(store, host, callback_return)
                .map_err(|_| SourceCheckError::Call(site))?;
            if predicate.owner != callback_annotation
                || predicate.kind != TypePredicateKind::Identifier
                || predicate.parameter_index != 0
                || predicate.narrowed_type.is_none()
            {
                return Err(SourceCheckError::Call(site));
            }
            Some(predicate)
        } else {
            None
        };

    Ok(GlobalArrayCallbackOverload {
        declaration,
        callback_annotation,
        callback_predicate,
        return_annotation,
        parameters,
        type_parameters,
    })
}

/// Publishes every authenticated `Array` callback overload in declaration order.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Keep source and publication proofs together.
pub(super) fn materialize_global_array_callback_method(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    receiver: TypeId,
    name: &str,
    site: NodeRef,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(plan) =
        plan_global_array_callback_method(store, host, global_types, receiver, name, site)?
    else {
        return Ok(None);
    };
    if let Some(links) = store.value_symbol_links(plan.symbol)
        && links != &ValueSymbolLinks::default()
    {
        let type_ = links.resolved_type.ok_or(SourceCheckError::Call(site))?;
        return match validate_stored_callable_set(store, type_) {
            StoredCallableSetValidation::Valid { projection, .. }
                if projection.call_signatures.len() == plan.overloads.len()
                    && projection.call_signatures.iter().zip(&plan.overloads).all(
                        |(signature, overload)| {
                            store.signature(signature.signature).is_some_and(|record| {
                                record.declaration() == Some(overload.declaration)
                                    && record.type_parameters().len()
                                        == overload.type_parameters.len()
                                    && record
                                        .type_parameters()
                                        .iter()
                                        .zip(&overload.type_parameters)
                                        .all(|(type_, parameter)| {
                                            cached_ordinary_type_parameter_owner(store, *type_)
                                                == Some(parameter.symbol)
                                        })
                            }) && signature.parameters.first().copied()
                                == store
                                    .type_node_links(overload.callback_annotation)
                                    .and_then(|links| links.resolved_type)
                                && valid_global_array_callback_predicate(
                                    store,
                                    overload,
                                    signature.parameters.first().copied(),
                                )
                        },
                    ) =>
            {
                Ok(Some(type_))
            }
            _ => Err(SourceCheckError::Call(site)),
        };
    }
    if plan.overloads.iter().any(|overload| {
        store
            .signature_links(overload.declaration)
            .is_some_and(|links| links != &SignatureLinks::default())
            || overload.parameters.iter().any(|parameter| {
                store
                    .value_symbol_links(parameter.symbol)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
            })
            || overload.type_parameters.iter().any(|parameter| {
                store
                    .declared_type_links(parameter.symbol)
                    .is_some_and(|links| {
                        links.declared_type.is_some_and(|type_| {
                            cached_ordinary_type_parameter_owner(store, type_)
                                != Some(parameter.symbol)
                        })
                    })
            })
    }) {
        return Err(SourceCheckError::Call(site));
    }

    let cold_type_parameters = plan
        .overloads
        .iter()
        .flat_map(|overload| &overload.type_parameters)
        .filter(|parameter| {
            store
                .declared_type_links(parameter.symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        })
        .count();
    let missing_declared_links = plan
        .overloads
        .iter()
        .flat_map(|overload| &overload.type_parameters)
        .filter(|parameter| store.declared_type_links(parameter.symbol).is_none())
        .count();
    if !store.try_reserve_types(cold_type_parameters)
        || !store.try_reserve_declared_type_links(missing_declared_links)
    {
        return Err(SourceCheckError::Call(site));
    }

    let mut annotation_diagnostics = CanonicalCheckerDiagnostics::default();
    let resolved = resolve_global_array_callback_overloads(
        store,
        host,
        global_types,
        options,
        &mut annotation_diagnostics,
        &plan,
        site,
    );
    merge_retry_diagnostics(diagnostics, annotation_diagnostics);
    let resolved = resolved?;

    if !store.try_reserve_types(1)
        || !store.try_reserve_signatures(plan.overloads.len())
        || !store.try_reserve_signature_links(
            plan.overloads
                .iter()
                .filter(|overload| store.signature_links(overload.declaration).is_none())
                .count(),
        )
        || !store.try_reserve_value_symbol_links(
            usize::from(store.value_symbol_links(plan.symbol).is_none())
                + plan
                    .overloads
                    .iter()
                    .flat_map(|overload| &overload.parameters)
                    .filter(|parameter| store.value_symbol_links(parameter.symbol).is_none())
                    .count(),
        )
        || !store.try_reserve_function_signature_return_annotations(plan.overloads.len())
        || !store.try_reserve_callable_signature_parameter_types(plan.overloads.len())
    {
        return Err(SourceCheckError::Call(site));
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .ok_or(SourceCheckError::Call(site))?;
    let mut signatures = Vec::with_capacity(plan.overloads.len());
    let mut parameter_batches = Vec::with_capacity(plan.overloads.len());
    for (overload, resolved) in plan.overloads.iter().zip(resolved) {
        let signature = store
            .alloc_signature(
                SignatureFlags::NONE,
                Some(overload.declaration),
                resolved.type_parameters,
                None,
                overload
                    .parameters
                    .iter()
                    .map(|parameter| parameter.symbol)
                    .collect(),
                Some(resolved.return_type),
                None,
                1,
            )
            .ok_or(SourceCheckError::Call(site))?;
        assert!(store.set_signature_links(
            overload.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        for (parameter, type_) in overload.parameters.iter().zip(&resolved.parameter_types) {
            assert!(store.set_value_symbol_links(
                parameter.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        signatures.push(signature);
        parameter_batches.push((signature, resolved.parameter_types));
    }
    assert!(store.set_value_symbol_links(
        plan.symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(type_, None, None, Some(signatures), None, None,));
    assert!(store.set_callable_signature_parameter_types_batch(parameter_batches));
    for overload in &plan.overloads {
        let signature = store
            .signature_links(overload.declaration)
            .and_then(|links| links.resolved_signature.signature())
            .ok_or(SourceCheckError::Call(site))?;
        assert!(store.set_function_signature_return_annotation(
            signature,
            overload.return_annotation,
            false,
        ));
    }
    if !matches!(
        validate_stored_callable_set(store, type_),
        StoredCallableSetValidation::Valid { .. }
    ) {
        return Err(SourceCheckError::Call(site));
    }
    Ok(Some(type_))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Resolve real generic dependencies before publication.
fn resolve_global_array_callback_overloads(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &GlobalArrayCallbackMethod,
    site: NodeRef,
) -> Result<Vec<ResolvedGlobalArrayCallbackOverload>, SourceCheckError> {
    let [element] = store
        .type_payload(plan.target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => {
                interface.reference.resolved_type_arguments.as_deref()
            }
            _ => None,
        })
        .ok_or(SourceCheckError::Call(site))?
    else {
        return Err(SourceCheckError::Call(site));
    };
    let element = *element;
    if store
        .type_payload(plan.target)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        != Some(plan.owner)
    {
        return Err(SourceCheckError::Call(site));
    }

    let mut resolved = Vec::with_capacity(plan.overloads.len());
    for overload in &plan.overloads {
        let mut type_parameters = Vec::with_capacity(overload.type_parameters.len());
        for parameter in &overload.type_parameters {
            if store.source_node_parent(parameter.declaration)
                != Some(SourceNodeParent::Parent(overload.declaration))
            {
                return Err(SourceCheckError::Call(site));
            }
            let type_ = execute_type_parameter(store, parameter.symbol);
            let constraint = parameter
                .constraint
                .map(|constraint| {
                    CanonicalTypeQuery::new_with_global_types(
                        store,
                        host,
                        global_types,
                        options,
                        diagnostics,
                    )?
                    .get_type_from_type_node(constraint)
                })
                .transpose()?;
            let Some(TypeData::TypeParameter(data)) =
                store.type_payload(type_).map(TypeRecord::data)
            else {
                return Err(SourceCheckError::Call(site));
            };
            if data.is_this_type
                || data.target.is_some()
                || data.mapper.is_some()
                || data.resolved_default_type.is_some()
                || data
                    .constraint
                    .is_some_and(|existing| Some(existing) != constraint)
                || constraint.is_some_and(|constraint| constraint != element)
            {
                return Err(SourceCheckError::Call(site));
            }
            if data.constraint != constraint
                && !store.set_type_parameter_resolution(type_, constraint, None, None, None)
            {
                return Err(SourceCheckError::Call(site));
            }
            type_parameters.push(type_);
        }

        let mut parameter_types = Vec::with_capacity(overload.parameters.len());
        for parameter in &overload.parameters {
            let type_ = CanonicalTypeQuery::new_with_global_types(
                store,
                host,
                global_types,
                options,
                diagnostics,
            )?
            .get_type_from_type_node(parameter.annotation)?;
            parameter_types.push(type_);
        }
        let return_type = resolve_global_array_callback_return_annotation(
            store,
            host,
            global_types,
            options,
            diagnostics,
            overload.return_annotation,
            site,
        )?;
        let callback = parameter_types[0];
        let StoredSingleCallableValidation::Valid {
            callable: callback_signature,
            ..
        } = validate_stored_single_callable(store, callback)
        else {
            return Err(SourceCheckError::Call(site));
        };
        CanonicalTypeQuery::new_with_global_types(store, host, global_types, options, diagnostics)?
            .get_return_type_of_signature(callback_signature.signature)?;
        let StoredSingleCallableValidation::Valid {
            callable: callback_signature,
            ..
        } = validate_stored_single_callable(store, callback)
        else {
            return Err(SourceCheckError::Call(site));
        };
        if callback_signature.parameters.first().copied() != Some(element)
            || callback_signature.rest_parameter.is_some()
            || !valid_global_array_callback_predicate(store, overload, Some(callback))
        {
            return Err(SourceCheckError::Call(site));
        }
        if let Some(predicate) = overload.callback_predicate {
            let callback_record = store
                .signature(callback_signature.signature)
                .ok_or(SourceCheckError::Call(site))?;
            let narrowed = callback_record
                .resolved_type_predicate()
                .and_then(|predicate| store.type_predicate(predicate))
                .and_then(super::signatures::TypePredicate::type_id);
            if type_parameters.as_slice() != narrowed.as_slice()
                || predicate.narrowed_type.is_none()
            {
                return Err(SourceCheckError::Call(site));
            }
        }
        resolved.push(ResolvedGlobalArrayCallbackOverload {
            type_parameters,
            parameter_types,
            return_type,
        });
    }
    Ok(resolved)
}

#[allow(clippy::too_many_arguments)] // Method roots must not materialize every Array member.
fn resolve_global_array_callback_return_annotation(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    annotation: NodeRef,
    site: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let record = host.node(annotation).ok_or(SourceCheckError::Call(site))?;
    let type_ = match &record.data {
        NodeData::ArrayTypeNode(array) if record.kind == SyntaxKind::ArrayType => {
            let element = NodeRef::new(annotation.arena, annotation.file, array.element_type);
            if store.source_node_parent(element) != Some(SourceNodeParent::Parent(annotation)) {
                return Err(SourceCheckError::Call(site));
            }
            let element = CanonicalTypeQuery::new_with_global_types(
                store,
                host,
                global_types,
                options,
                diagnostics,
            )?
            .get_type_from_type_node(element)?;
            store
                .create_canonical_array_type(global_types, element, false)
                .map_err(|_| SourceCheckError::Call(site))?
        }
        NodeData::UnionTypeNode(union) if record.kind == SyntaxKind::UnionType => {
            if union.types.nodes.len() != 2 || union.types.has_trailing_comma {
                return Err(SourceCheckError::Call(site));
            }
            let mut types = Vec::with_capacity(union.types.nodes.len());
            for member in &union.types.nodes {
                let member = NodeRef::new(annotation.arena, annotation.file, *member);
                if store.source_node_parent(member) != Some(SourceNodeParent::Parent(annotation)) {
                    return Err(SourceCheckError::Call(site));
                }
                types.push(
                    CanonicalTypeQuery::new_with_global_types(
                        store,
                        host,
                        global_types,
                        options,
                        diagnostics,
                    )?
                    .get_type_from_type_node(member)?,
                );
            }
            store
                .expression_union_type_with_global_types(
                    global_types,
                    &types,
                    UnionReduction::Literal,
                )
                .map_err(|_| SourceCheckError::Call(site))?
        }
        NodeData::KeywordTypeNode(_) if record.kind == SyntaxKind::VoidKeyword => store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.void_type)
            .ok_or(SourceCheckError::Call(site))?,
        _ => return Err(SourceCheckError::Call(site)),
    };
    let expected = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    match store.type_node_links(annotation) {
        Some(existing) if existing == &expected => {}
        Some(existing) if existing != &TypeNodeLinks::default() => {
            return Err(SourceCheckError::Call(site));
        }
        _ => {
            if !store.try_reserve_type_node_links(usize::from(
                store.type_node_links(annotation).is_none(),
            )) || !store.set_type_node_links(annotation, expected)
            {
                return Err(SourceCheckError::Call(site));
            }
        }
    }
    Ok(type_)
}

fn valid_global_array_callback_predicate(
    store: &CanonicalTypeMapperStore,
    overload: &GlobalArrayCallbackOverload,
    callback: Option<TypeId>,
) -> bool {
    let Some(callback) = callback else {
        return false;
    };
    let StoredSingleCallableValidation::Valid { callable, .. } =
        validate_stored_single_callable(store, callback)
    else {
        return false;
    };
    let Some(signature) = store.signature(callable.signature) else {
        return false;
    };
    let annotation = store
        .function_signature_return_annotation(callable.signature)
        .map(|(annotation, _)| annotation);
    valid_planned_callable_type_predicate(store, signature, annotation, overload.callback_predicate)
}

/// Maps a real `Array` callback's first generic parameter to its typed receiver.
pub(super) fn array_callback_contextual_parameter_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    arrow: NodeRef,
    contextual_type: TypeId,
    parameter_type: TypeId,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(SourceNodeParent::Parent(call)) = store.source_node_parent(arrow) else {
        return Ok(None);
    };
    let Some(NodeData::CallExpression(call_data)) = host.node(call).map(|record| &record.data)
    else {
        return Ok(None);
    };
    let property = NodeRef::new(call.arena, call.file, call_data.expression);
    let Some(NodeData::PropertyAccessExpression(access)) =
        host.node(property).map(|record| &record.data)
    else {
        return Ok(None);
    };
    if source_global_array_callback_method_name(host, property).is_none()
        || call_data.arguments.nodes.first().copied() != Some(arrow.node)
    {
        return Ok(None);
    }
    let receiver = NodeRef::new(property.arena, property.file, access.expression);
    let receiver_type = store
        .type_node_links(receiver)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(call))?;
    let Some(array) = store
        .canonical_array_reference(global_types, receiver_type)
        .map_err(|_| SourceCheckError::Call(call))?
    else {
        return Ok(None);
    };
    let target = if array.readonly {
        global_types.readonly_array_type
    } else {
        global_types.array_type
    };
    let [source_parameter] = store
        .type_payload(target)
        .and_then(|record| match record.data() {
            TypeData::Interface(interface) => {
                interface.reference.resolved_type_arguments.as_deref()
            }
            _ => None,
        })
        .ok_or(SourceCheckError::Call(call))?
    else {
        return Err(SourceCheckError::Call(call));
    };
    let method = store
        .symbol_node_links(property)
        .and_then(|links| links.resolved_symbol)
        .ok_or(SourceCheckError::Call(call))?;
    if store
        .authenticated_interface_method_owner(method)
        .is_none_or(|(_, owner)| owner != target)
        || store
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .and_then(|type_| store.type_payload(type_))
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .is_none_or(|signatures| {
                signatures.iter().all(|signature| {
                    store
                        .callable_signature_parameter_types(*signature)
                        .and_then(|parameters| parameters.first())
                        .copied()
                        != Some(contextual_type)
                })
            })
        || parameter_type != *source_parameter
    {
        return Err(SourceCheckError::Call(call));
    }
    Ok(Some(array.element_type))
}

/// Authenticates a context whose first parameter comes from an `Array` element.
pub(super) fn authenticated_array_callback_contextual_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    source_parameter: TypeId,
    actual_parameter: TypeId,
) -> bool {
    let Some(parameter_symbol) =
        super::declared::cached_ordinary_type_parameter_owner(store, source_parameter)
    else {
        return false;
    };
    let Some(owner) = store.get_parent_of_symbol(parameter_symbol) else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some(owner_name) = owner_record.name().as_utf8() else {
        return false;
    };
    if !matches!(owner_name, "Array" | "ReadonlyArray")
        || store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source(owner_name))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(owner)
        || store.type_payload(actual_parameter).is_none()
    {
        return false;
    }
    let Some(callback_symbol) = store.type_payload(target).and_then(TypeRecord::symbol) else {
        return false;
    };
    let Some(callback) = store.symbol(callback_symbol) else {
        return false;
    };
    let Some([callback_declaration]) = callback.declarations() else {
        return false;
    };
    let Some(SourceNodeParent::Parent(parameter_declaration)) =
        store.source_node_parent(*callback_declaration)
    else {
        return false;
    };
    let Some(SourceNodeParent::Parent(method_declaration)) =
        store.source_node_parent(parameter_declaration)
    else {
        return false;
    };
    let Some(members) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    callback.flags() == SymbolFlags::TYPE_LITERAL
        && store.source_node_kind(*callback_declaration) == Some(SyntaxKind::FunctionType)
        && store.source_direct_type_annotation(parameter_declaration) == Some(*callback_declaration)
        && store
            .type_node_links(*callback_declaration)
            .and_then(|links| links.resolved_type)
            == Some(target)
        && members.iter().any(|(_, member)| {
            store.get_merged_symbol(member).is_some_and(|method| {
                store.symbol(method).is_some_and(|record| {
                    record.flags() == SymbolFlags::METHOD
                        && record.name().as_utf8().is_some_and(|name| {
                            matches!(name, "map" | "filter" | "find" | "forEach" | "reduce")
                        })
                        && record
                            .declarations()
                            .is_some_and(|declarations| declarations.contains(&method_declaration))
                        && store.get_parent_of_symbol(method) == Some(owner)
                })
            })
        })
}

#[allow(clippy::too_many_lines)] // Select and validate every supported array callback overload.
fn check_authenticated_array_callback_call(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_types: &[TypeId],
) -> Result<Option<CheckedSourceCall>, SourceCheckError> {
    if plan.form != DirectCallForm::Call
        || plan.type_arguments.is_some()
        || !(1..=2).contains(&argument_types.len())
    {
        return Ok(None);
    }
    let PlannedExpressionKind::Property(property) = &plan.callee.unparenthesized().kind else {
        return Ok(None);
    };
    let Some(method) = store.type_payload(callee_type).and_then(TypeRecord::symbol) else {
        return Ok(None);
    };
    let Some(method_record) = store.symbol(method) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let Some(method_name) = method_record.name().as_utf8() else {
        return Ok(None);
    };
    if method_record.flags() != SymbolFlags::METHOD
        || !matches!(method_name, "map" | "filter" | "find" | "forEach")
        || store
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            != Some(callee_type)
    {
        return Ok(None);
    }
    let method_name = method_name.to_owned();
    let receiver = store
        .type_node_links(property.receiver.node)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let Some(array) = store
        .canonical_array_reference(global_types, receiver)
        .map_err(|_| SourceCheckError::Call(plan.node))?
    else {
        return Ok(None);
    };
    let target = if array.readonly {
        global_types.readonly_array_type
    } else {
        global_types.array_type
    };
    if store
        .authenticated_interface_method_owner(method)
        .is_none_or(|(_, owner)| owner != target)
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, callee_type)
    else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let callback = *argument_types
        .first()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let StoredCallableSetValidation::Valid {
        projection: callback_projection,
        ..
    } = validate_stored_callable_set(store, callback)
    else {
        return Ok(None);
    };
    let Some(callback_callable) = callback_projection.call_signatures.first() else {
        return Ok(None);
    };
    let Some(callback_signature) = store.signature(callback_callable.signature) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let annotation = store
        .function_signature_return_annotation(callback_callable.signature)
        .map(|(annotation, _)| annotation);
    if !valid_stored_callable_type_predicate(store, callback_signature, annotation) {
        return Err(SourceCheckError::Call(plan.node));
    }
    let callback_predicate = callback_signature
        .resolved_type_predicate()
        .map(|predicate| {
            let predicate = store
                .type_predicate(predicate)
                .ok_or(SourceCheckError::Call(plan.node))?;
            if predicate.kind() != TypePredicateKind::Identifier || predicate.parameter_index() != 0
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            predicate.type_id().ok_or(SourceCheckError::Call(plan.node))
        })
        .transpose()?;
    let callback_parameter = callback_callable.parameters.first().copied();
    let callback_return = callback_callable.return_type;
    let callback_context = store
        .source_callable_provenance(callback)
        .and_then(|provenance| provenance.contextual_target);
    if callback_context.is_some_and(|context| {
        projection
            .call_signatures
            .iter()
            .all(|signature| signature.parameters.first().copied() != Some(context))
    }) {
        return Err(SourceCheckError::Call(plan.node));
    }
    if let Some(callback_parameter) = callback_parameter
        && !store
            .is_type_assignable_to_with_global_types(
                array.element_type,
                callback_parameter,
                global_types,
            )
            .map_err(SourceCheckError::RelationUnavailable)?
    {
        return Ok(None);
    }
    if let Some(narrowed) = callback_predicate
        && !store
            .is_type_assignable_to_with_global_types(narrowed, array.element_type, global_types)
            .map_err(SourceCheckError::RelationUnavailable)?
    {
        return Ok(None);
    }

    let mut selected = None;
    for candidate in &projection.call_signatures {
        if argument_types.len() > candidate.parameters.len() {
            continue;
        }
        let Some(context) = candidate.parameters.first().copied() else {
            return Err(SourceCheckError::Call(plan.node));
        };
        let StoredSingleCallableValidation::Valid {
            callable: target, ..
        } = validate_stored_single_callable(store, context)
        else {
            return Err(SourceCheckError::Call(plan.node));
        };
        let target_signature = store
            .signature(target.signature)
            .ok_or(SourceCheckError::Call(plan.node))?;
        if target_signature.resolved_type_predicate().is_some() == callback_predicate.is_some() {
            selected = Some((candidate, target));
            break;
        }
    }
    let Some((signature, callback_target)) = selected else {
        return Ok(None);
    };
    let declaration_signature = store
        .signature(signature.signature)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let source_element = callback_target
        .parameters
        .first()
        .copied()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let generic_parameter = declaration_signature.type_parameters().first().copied();
    let template_return = signature
        .return_type
        .ok_or(SourceCheckError::Call(plan.node))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let (undefined, void) = (bootstrap.undefined_type, bootstrap.void_type);
    let expected_element = callback_predicate.map_or(source_element, |_| {
        generic_parameter.unwrap_or(source_element)
    });

    let return_type = match method_name.as_str() {
        "forEach" if generic_parameter.is_none() && template_return == void => void,
        "map" => {
            let mapped = callback_return.ok_or(SourceCheckError::Call(plan.node))?;
            let Some(parameter) = generic_parameter else {
                return Err(SourceCheckError::Call(plan.node));
            };
            if callback_target.return_type != Some(parameter)
                || store
                    .canonical_array_reference(global_types, template_return)
                    .map_err(|_| SourceCheckError::Call(plan.node))?
                    .is_none_or(|array| array.readonly || array.element_type != parameter)
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            store
                .create_canonical_array_type(global_types, mapped, false)
                .map_err(|_| SourceCheckError::Call(plan.node))?
        }
        "filter" => {
            if store
                .canonical_array_reference(global_types, template_return)
                .map_err(|_| SourceCheckError::Call(plan.node))?
                .is_none_or(|array| array.readonly || array.element_type != expected_element)
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            store
                .create_canonical_array_type(
                    global_types,
                    callback_predicate.unwrap_or(array.element_type),
                    false,
                )
                .map_err(|_| SourceCheckError::Call(plan.node))?
        }
        "find" => {
            let valid_return = template_return == expected_element
                || matches!(
                    store.type_payload(template_return).map(TypeRecord::data),
                    Some(TypeData::Union(union))
                        if union.union.types.len() == 2
                            && union.union.types.contains(&expected_element)
                            && union.union.types.contains(&undefined)
                );
            if !valid_return {
                return Err(SourceCheckError::Call(plan.node));
            }
            store
                .expression_union_type_with_global_types(
                    global_types,
                    &[callback_predicate.unwrap_or(array.element_type), undefined],
                    UnionReduction::Literal,
                )
                .map_err(|_| SourceCheckError::Call(plan.node))?
        }
        _ => return Err(SourceCheckError::Call(plan.node)),
    };
    let existing_signature = preflight_call_publication(store, plan.node, return_type)?;
    let call_signature = if template_return == return_type {
        if existing_signature.is_some_and(|existing| existing != signature.signature) {
            return Err(SourceCheckError::Call(plan.node));
        }
        signature.signature
    } else {
        let mut mapper_sources = vec![source_element];
        let mut mapper_targets = vec![array.element_type];
        if let Some(parameter) = generic_parameter {
            let inferred = if method_name == "map" {
                callback_return
            } else {
                callback_predicate
            }
            .ok_or(SourceCheckError::Call(plan.node))?;
            mapper_sources.push(parameter);
            mapper_targets.push(inferred);
        }

        if let Some(existing) = existing_signature {
            let instantiated = store
                .signature(existing)
                .ok_or(SourceCheckError::Call(plan.node))?;
            let original = store
                .signature(signature.signature)
                .ok_or(SourceCheckError::Call(plan.node))?;
            let mapper = instantiated
                .mapper()
                .ok_or(SourceCheckError::Call(plan.node))?;
            if instantiated.target() != Some(signature.signature)
                || instantiated.resolved_return_type() != Some(return_type)
                || !instantiated.type_parameters().is_empty()
                || instantiated.flags() != original.flags() & SignatureFlags::PROPAGATING_FLAGS
                || instantiated.declaration() != original.declaration()
                || instantiated.min_argument_count() != original.min_argument_count()
                || instantiated.parameters().len() != original.parameters().len()
                || store.type_mapper_has_exact_endpoints(mapper, &mapper_sources, &mapper_targets)
                    != Some(true)
                || instantiated
                    .parameters()
                    .iter()
                    .copied()
                    .zip(original.parameters().iter().copied())
                    .any(|(parameter, target)| {
                        parameter != target
                            && store.value_symbol_links(parameter).is_none_or(|links| {
                                links.target != Some(target) || links.mapper != Some(mapper)
                            })
                    })
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            existing
        } else {
            if !store.try_reserve_mappers(1) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let mapper = store
                .new_type_mapper(mapper_sources, mapper_targets)
                .ok_or(SourceCheckError::Call(plan.node))?;
            let instantiated = store
                .instantiate_signature_ex(signature.signature, mapper, true)
                .map_err(|_| SourceCheckError::Call(plan.node))?;
            if !store.set_signature_resolved_return_type(instantiated, Some(return_type)) {
                return Err(SourceCheckError::Call(plan.node));
            }
            instantiated
        }
    };
    publish_call_links(store, plan.node, call_signature, return_type)?;
    Ok(Some(CheckedSourceCall { return_type }))
}

#[allow(clippy::too_many_arguments)] // Factory calls retain their source and diagnostic context.
fn check_authenticated_generic_object_factory_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_types: &[TypeId],
    explicit_type_arguments: &[TypeId],
) -> Result<Option<CheckedSourceCall>, SourceCheckError> {
    let ([type_argument], [argument_type]) = (explicit_type_arguments, argument_types) else {
        return Ok(None);
    };
    let PlannedExpressionKind::Property(property) = &plan.callee.unparenthesized().kind else {
        return Ok(None);
    };
    let PlannedExpressionKind::Identifier(receiver) = &property.receiver.unparenthesized().kind
    else {
        return Ok(None);
    };
    let Some(method) = store.type_payload(callee_type).and_then(TypeRecord::symbol) else {
        return Ok(None);
    };
    let method_record = store
        .symbol(method)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let Some(name @ ("entries" | "values")) = method_record.name().as_utf8() else {
        return Ok(None);
    };
    let name = name.to_owned();
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let globals = store
        .symbol_table(bootstrap.globals)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let Some(object) = globals
        .get_source("Object")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    if receiver.value_symbol != object {
        return Ok(None);
    }
    let constructor = globals
        .get_source("ObjectConstructor")
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceCheckError::Call(plan.node))?;
    let receiver_type = store
        .type_node_links(property.receiver.node)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let string = bootstrap.string_type;
    if method_record.flags() != SymbolFlags::METHOD
        || store.authenticated_interface_method_owner(method) != Some((constructor, receiver_type))
        || store.value_symbol_links(method)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(callee_type),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(SourceCheckError::Call(plan.node));
    }

    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, callee_type)
    else {
        return Err(SourceCheckError::Call(plan.node));
    };
    if !projection.construct_signatures.is_empty() {
        return Err(SourceCheckError::Call(plan.node));
    }
    let Some(generic) = projection.call_signatures.iter().find(|candidate| {
        store
            .signature(candidate.signature)
            .is_some_and(|signature| !signature.type_parameters().is_empty())
    }) else {
        return Ok(None);
    };
    let signature = store
        .signature(generic.signature)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let ([type_parameter], [parameter]) = (signature.type_parameters(), signature.parameters())
    else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let (type_parameter, parameter) = (*type_parameter, *parameter);
    if generic.parameters.as_slice() != [type_parameter]
        || generic.min_argument_count != 1
        || generic.rest_parameter.is_some()
        || signature.flags() != SignatureFlags::NONE
        || signature.this_parameter().is_some()
        || signature.min_argument_count() != 1
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    let return_template = generic
        .return_type
        .ok_or(SourceCheckError::Call(plan.node))?;
    let template_array = store
        .canonical_array_reference(global_types, return_template)
        .map_err(|_| SourceCheckError::Call(plan.node))?
        .ok_or(SourceCheckError::Call(plan.node))?;
    if template_array.readonly || template_array.array_literal {
        return Err(SourceCheckError::Call(plan.node));
    }
    let tuple_infos = if name == "entries" {
        let tuple = store
            .canonical_tuple_shape(template_array.element_type)
            .map_err(|_| SourceCheckError::Call(plan.node))?
            .ok_or(SourceCheckError::Call(plan.node))?;
        if tuple.element_types() != [string, type_parameter]
            || tuple.min_length() != 2
            || tuple.fixed_length() != 2
            || tuple.is_readonly()
        {
            return Err(SourceCheckError::Call(plan.node));
        }
        Some(tuple.element_infos().to_vec())
    } else {
        if template_array.element_type != type_parameter {
            return Err(SourceCheckError::Call(plan.node));
        }
        None
    };

    let type_arguments = [*type_argument];
    let cache_key = type_list_key(&type_arguments);
    let cached = match store.cached_signature(generic.signature, cache_key, &type_arguments) {
        CachedSignatureLookup::Missing => None,
        CachedSignatureLookup::Hit(signature) => Some(signature),
        CachedSignatureLookup::Invalid | CachedSignatureLookup::HashCollision(_) => {
            return Err(SourceCheckError::Call(plan.node));
        }
    };
    let element_type = if let Some(infos) = tuple_infos {
        store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, *type_argument],
                &infos,
                false,
            ))
            .map_err(|_| SourceCheckError::Call(plan.node))?
    } else {
        *type_argument
    };
    let return_type = store
        .create_canonical_array_type(global_types, element_type, false)
        .map_err(|_| SourceCheckError::Call(plan.node))?;

    let instantiated = if let Some(instantiated) = cached {
        let record = store
            .signature(instantiated)
            .ok_or(SourceCheckError::Call(plan.node))?;
        let mapper = record.mapper().ok_or(SourceCheckError::Call(plan.node))?;
        let [mapped_parameter] = record.parameters() else {
            return Err(SourceCheckError::Call(plan.node));
        };
        if record.target() != Some(generic.signature)
            || record.resolved_return_type() != Some(return_type)
            || !record.type_parameters().is_empty()
            || record.min_argument_count() != 1
            || store.type_mapper_has_exact_endpoints(mapper, &[type_parameter], &type_arguments)
                != Some(true)
            || store.value_symbol_links(*mapped_parameter)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(*type_argument),
                    target: Some(parameter),
                    mapper: Some(mapper),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(SourceCheckError::Call(plan.node));
        }
        instantiated
    } else {
        if !store.try_reserve_mappers(1)
            || !store.try_reserve_checker_symbol_allocations(1, 0)
            || !store.try_reserve_value_symbol_links(1)
            || !store.try_reserve_signatures(1)
            || !store.try_reserve_cached_signatures(1)
        {
            return Err(SourceCheckError::Call(plan.node));
        }
        let mapper = store
            .new_simple_type_mapper(type_parameter, *type_argument)
            .ok_or(SourceCheckError::Call(plan.node))?;
        let instantiated = store
            .instantiate_signature_ex(generic.signature, mapper, true)
            .map_err(|_| SourceCheckError::Call(plan.node))?;
        let [mapped_parameter] = store
            .signature(instantiated)
            .ok_or(SourceCheckError::Call(plan.node))?
            .parameters()
        else {
            return Err(SourceCheckError::Call(plan.node));
        };
        let mapped_parameter = *mapped_parameter;
        if !store.set_value_symbol_links(
            mapped_parameter,
            ValueSymbolLinks {
                resolved_type: Some(*type_argument),
                target: Some(parameter),
                mapper: Some(mapper),
                ..ValueSymbolLinks::default()
            },
        ) || !store.set_signature_resolved_return_type(instantiated, Some(return_type))
            || !store.set_cached_signature(
                generic.signature,
                cache_key,
                Box::new(type_arguments),
                instantiated,
            )
        {
            return Err(SourceCheckError::Call(plan.node));
        }
        instantiated
    };

    if preflight_call_publication(store, plan.node, return_type)?
        .is_some_and(|existing| existing != instantiated)
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    if !store
        .is_type_assignable_to_with_global_types_and_strict_function_types(
            *argument_type,
            *type_argument,
            global_types,
            options.strict_function_types,
        )
        .map_err(SourceCheckError::RelationUnavailable)?
    {
        let argument = plan
            .arguments
            .first()
            .ok_or(SourceCheckError::Call(plan.node))?;
        for diagnostic in prepare_source_argument_mismatch_diagnostics(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            argument,
            *argument_type,
            *type_argument,
        )? {
            merge_retry_diagnostic(diagnostics, diagnostic);
        }
    }
    publish_call_links(store, plan.node, instantiated, return_type)?;
    Ok(Some(CheckedSourceCall { return_type }))
}

fn authenticated_array_callback_callee(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceCallPlan,
    callee_type: TypeId,
) -> Result<bool, SourceCheckError> {
    let PlannedExpressionKind::Property(property) = &plan.callee.unparenthesized().kind else {
        return Ok(false);
    };
    let Some(method) = store.type_payload(callee_type).and_then(TypeRecord::symbol) else {
        return Ok(false);
    };
    let Some(record) = store.symbol(method) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    if record.flags() != SymbolFlags::METHOD
        || !matches!(
            record.name().as_utf8(),
            Some("map" | "filter" | "find" | "forEach" | "reduce")
        )
    {
        return Ok(false);
    }
    let receiver = store
        .type_node_links(property.receiver.node)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let Some(array) = store
        .canonical_array_reference(global_types, receiver)
        .map_err(|_| SourceCheckError::Call(plan.node))?
    else {
        return Ok(false);
    };
    let target = if array.readonly {
        global_types.readonly_array_type
    } else {
        global_types.array_type
    };
    Ok(store
        .authenticated_interface_method_owner(method)
        .is_some_and(|(_, owner)| owner == target))
}

fn shared_array_callback_context(
    store: &CanonicalTypeMapperStore,
    contexts: &[TypeId],
) -> Option<TypeId> {
    let mut parameter = None;
    let mut selected = None;
    for context in contexts {
        let StoredSingleCallableValidation::Valid { callable, .. } =
            validate_stored_single_callable(store, *context)
        else {
            continue;
        };
        let signature = store.signature(callable.signature)?;
        let first = callable.parameters.first().copied()?;
        if !signature.type_parameters().is_empty()
            || signature.has_rest_parameter()
            || callable.rest_parameter.is_some()
            || parameter.is_some_and(|previous| previous != first)
        {
            return None;
        }
        parameter = Some(first);
        selected = Some(*context);
    }
    selected
}

/// Returns an authenticated parameter context for an object, array, arrow, or template.
///
/// Array and object arguments can retain a shared indexed context when
/// overload parameter identities differ. Generic signatures provide context
/// for authenticated fixed parameters, array callbacks, and constrained templates.
/// Unary overloaded callbacks retain a shared parameter and prefer informative returns.
pub(super) fn source_call_argument_contextual_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_index: usize,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(argument) = plan.arguments.get(argument_index) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let argument = argument.unparenthesized();
    if !matches!(
        argument.kind,
        PlannedExpressionKind::Object { .. }
            | PlannedExpressionKind::Array(_)
            | PlannedExpressionKind::Arrow(_)
            | PlannedExpressionKind::Template(_)
    ) {
        return Ok(None);
    }
    let callee_type =
        specialize_readonly_array_concat_callee(store, global_types, plan, callee_type)?;
    let array_callback = matches!(argument.kind, PlannedExpressionKind::Arrow(_))
        && authenticated_array_callback_callee(store, global_types, plan, callee_type)?;

    let parameter_index = argument_index + usize::from(plan.form == DirectCallForm::TaggedTemplate);

    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, callee_type)
    else {
        return Ok(None);
    };
    if !projection.construct_signatures.is_empty() || projection.call_signatures.is_empty() {
        return Ok(None);
    }

    let mut parameter_types = Vec::with_capacity(projection.call_signatures.len());
    for callable in &projection.call_signatures {
        let Some(signature) = store.signature(callable.signature) else {
            return Err(SourceCheckError::Call(plan.node));
        };
        if !signature.type_parameters().is_empty()
            && projection.call_signatures.len() == 1
            && matches!(argument.kind, PlannedExpressionKind::Template(_))
            && let Some(parameter) = callable.parameters.get(parameter_index).copied()
            && signature.type_parameters().contains(&parameter)
            && let Some(TypeData::TypeParameter(data)) =
                store.type_payload(parameter).map(TypeRecord::data)
            && data.constraint.is_some_and(|constraint| {
                store.type_payload(constraint).is_some_and(|record| {
                    record.flags().intersects(
                        TypeFlags::STRING_LIKE | TypeFlags::UNION | TypeFlags::INTERSECTION,
                    )
                })
            })
        {
            return Ok(Some(parameter));
        }
        let parameter_type = match callable.parameters.get(parameter_index).copied() {
            Some(parameter) => Some(parameter),
            None => callable
                .rest_parameter
                .map(|rest| store.canonical_array_element_type(global_types, rest))
                .transpose()?
                .flatten(),
        };
        let Some(parameter_type) = parameter_type else {
            return Ok(None);
        };
        if !signature.type_parameters().is_empty()
            && !array_callback
            && !valid_fixed_generic_source_parameter_type(store, parameter_type)
        {
            return Ok(None);
        }
        parameter_types.push(parameter_type);
    }

    let Some(first) = parameter_types.first().copied() else {
        return Ok(None);
    };
    if parameter_types.iter().all(|parameter| *parameter == first) {
        return Ok(Some(
            if matches!(argument.kind, PlannedExpressionKind::Arrow(_)) {
                nonnullable_contextual_callback_type(store, first)
            } else {
                first
            },
        ));
    }
    if array_callback {
        return Ok(shared_array_callback_context(store, &parameter_types));
    }
    if matches!(argument.kind, PlannedExpressionKind::Template(_)) {
        return Ok(None);
    }
    if matches!(argument.kind, PlannedExpressionKind::Arrow(_)) {
        return Ok(shared_overload_callback_context(store, &parameter_types));
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let index_key = match argument.kind {
        PlannedExpressionKind::Array(_) => bootstrap.number_type,
        PlannedExpressionKind::Object { .. } => bootstrap.string_type,
        PlannedExpressionKind::Arrow(_) => return Ok(None),
        _ => unreachable!("only contextual call arguments pass the syntax gate"),
    };
    let Some(element_type) =
        shared_overload_index_type(store, global_types, plan.node, &parameter_types, index_key)?
    else {
        return Ok(None);
    };

    if matches!(argument.kind, PlannedExpressionKind::Array(_)) {
        for parameter in &parameter_types {
            if let Some(array) = contextual_array_parameter_with_element(
                store,
                global_types,
                plan.node,
                *parameter,
                element_type,
            )? {
                return Ok(Some(array));
            }
        }
        return store
            .create_canonical_array_type(global_types, element_type, false)
            .map(Some)
            .map_err(Into::into);
    }

    for parameter in parameter_types {
        if let Some(object) = contextual_indexed_parameter_with_element(
            store,
            global_types,
            plan.node,
            parameter,
            index_key,
            element_type,
        )? {
            return Ok(Some(object));
        }
    }
    Ok(None)
}

/// Optional callback parameters contextualize against their callable member.
fn nonnullable_contextual_callback_type(
    store: &CanonicalTypeMapperStore,
    contextual_type: TypeId,
) -> TypeId {
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return contextual_type;
    };
    let Some(TypeData::Union(union)) = store.type_payload(contextual_type).map(TypeRecord::data)
    else {
        return contextual_type;
    };
    if union.union.types.len() != 2 || !union.union.types.contains(&undefined) {
        return contextual_type;
    }
    let Some(callable) = union
        .union
        .types
        .iter()
        .copied()
        .find(|candidate| *candidate != undefined)
    else {
        return contextual_type;
    };
    match validate_stored_callable_set(store, callable) {
        StoredCallableSetValidation::Valid { projection, .. }
            if !projection.call_signatures.is_empty()
                && projection.construct_signatures.is_empty() =>
        {
            callable
        }
        _ => contextual_type,
    }
}

/// Reuses a real unary callback whose input is shared by every overload.
fn shared_overload_callback_context(
    store: &CanonicalTypeMapperStore,
    contexts: &[TypeId],
) -> Option<TypeId> {
    let any = store.intrinsic_bootstrap()?.any_type;
    let mut parameter = None;
    let mut selected: Option<(TypeId, TypeId)> = None;

    for context in contexts {
        let StoredSingleCallableValidation::Valid { callable, .. } =
            validate_stored_single_callable(store, *context)
        else {
            return None;
        };
        let signature = store.signature(callable.signature)?;
        let [input] = callable.parameters.as_slice() else {
            return None;
        };
        if !signature.type_parameters().is_empty()
            || signature.has_rest_parameter()
            || callable.rest_parameter.is_some()
            || callable.min_argument_count != 1
            || parameter.is_some_and(|previous| previous != *input)
        {
            return None;
        }
        parameter = Some(*input);

        let return_type = callable.return_type?;
        match selected {
            None => selected = Some((*context, return_type)),
            Some((_, previous)) if previous == any && return_type != any => {
                selected = Some((*context, return_type));
            }
            Some((_, previous))
                if previous != any && return_type != any && previous != return_type =>
            {
                return None;
            }
            Some(_) => {}
        }
    }

    selected.map(|(context, _)| context)
}

/// Specializes readonly concat calls whose declaration returns mutable arrays.
fn specialize_readonly_array_concat_callee(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceCallPlan,
    callee_type: TypeId,
) -> Result<TypeId, SourceCheckError> {
    let PlannedExpressionKind::Property(property) = &plan.callee.unparenthesized().kind else {
        return Ok(callee_type);
    };
    let Some(method) = store.type_payload(callee_type).and_then(TypeRecord::symbol) else {
        return Ok(callee_type);
    };
    let Some(method_record) = store.symbol(method) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    if method_record.flags() != SymbolFlags::METHOD
        || method_record.name().as_utf8() != Some("concat")
        || store
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            != Some(callee_type)
    {
        return Ok(callee_type);
    }
    if store
        .authenticated_interface_method_owner(method)
        .is_none_or(|(_, target)| target != global_types.readonly_array_type)
    {
        return Ok(callee_type);
    }
    let receiver = store
        .type_node_links(property.receiver.node)
        .and_then(|links| links.resolved_type)
        .ok_or(SourceCheckError::Call(plan.node))?;
    if store
        .canonical_array_reference(global_types, receiver)?
        .is_none_or(|array| !array.readonly)
    {
        return Ok(callee_type);
    }

    super::instantiated_members::instantiate_published_generic_interface_method(
        store,
        global_types,
        receiver,
        method,
    )
    .map_err(|_| SourceCheckError::Call(plan.node))
}

fn shared_overload_index_type(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    call: NodeRef,
    parameters: &[TypeId],
    key_type: TypeId,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(first) = parameters.first().copied() else {
        return Ok(None);
    };
    let mut common = contextual_indexed_element_types(
        store,
        global_types,
        call,
        first,
        key_type,
        &mut HashSet::new(),
    )?;
    common.dedup();
    if common.is_empty() {
        return Ok(None);
    }
    for parameter in &parameters[1..] {
        let candidates = contextual_indexed_element_types(
            store,
            global_types,
            call,
            *parameter,
            key_type,
            &mut HashSet::new(),
        )?;
        common.retain(|candidate| candidates.contains(candidate));
        if common.is_empty() {
            return Ok(None);
        }
    }
    Ok((common.len() == 1).then_some(common[0]))
}

fn contextual_indexed_element_types(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    call: NodeRef,
    contextual_type: TypeId,
    key_type: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<Vec<TypeId>, SourceCheckError> {
    if !visiting.insert(contextual_type) {
        return Err(SourceCheckError::Call(call));
    }
    let result = contextual_indexed_element_types_inner(
        store,
        global_types,
        call,
        contextual_type,
        key_type,
        visiting,
    );
    visiting.remove(&contextual_type);
    result
}

fn contextual_indexed_element_types_inner(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    call: NodeRef,
    contextual_type: TypeId,
    key_type: TypeId,
    visiting: &mut HashSet<TypeId>,
) -> Result<Vec<TypeId>, SourceCheckError> {
    let record = store
        .type_payload(contextual_type)
        .ok_or(SourceCheckError::Call(call))?;
    if let TypeData::Union(union) = record.data() {
        if union.union.types.is_empty() {
            return Err(SourceCheckError::Call(call));
        }
        let mut elements = Vec::new();
        for constituent in &union.union.types {
            for element in contextual_indexed_element_types(
                store,
                global_types,
                call,
                *constituent,
                key_type,
                visiting,
            )? {
                if !elements.contains(&element) {
                    elements.push(element);
                }
            }
        }
        return Ok(elements);
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::Call(call))?;
    if key_type == bootstrap.number_type {
        if let Some(element) = store.canonical_array_element_type(global_types, contextual_type)? {
            return Ok(vec![element]);
        }
        if let Some(tuple) = store
            .canonical_tuple_shape(contextual_type)
            .map_err(|_| SourceCheckError::Call(call))?
        {
            let mut elements = Vec::new();
            for element in tuple.element_types() {
                if !elements.contains(element) {
                    elements.push(*element);
                }
            }
            return Ok(elements);
        }
    }

    let mut elements = Vec::new();
    if let Some(indexes) = record
        .data()
        .structured()
        .and_then(|structured| structured.index_infos.as_deref())
    {
        for index in indexes {
            let index = store
                .index_info(*index)
                .ok_or(SourceCheckError::Call(call))?;
            if store.type_payload(index.key_type()).is_none()
                || store.type_payload(index.value_type()).is_none()
            {
                return Err(SourceCheckError::Call(call));
            }
            if index.key_type() == key_type && !elements.contains(&index.value_type()) {
                elements.push(index.value_type());
            }
        }
    }
    if !elements.is_empty() || key_type != bootstrap.number_type {
        return Ok(elements);
    }

    let TypeData::TypeReference(reference) = record.data() else {
        return Ok(elements);
    };
    let Some(target) = reference.object.target else {
        return Ok(elements);
    };
    let Some([element]) = reference.resolved_type_arguments.as_deref() else {
        return Ok(elements);
    };
    let Some(owner) = store.type_payload(target).and_then(TypeRecord::symbol) else {
        return Ok(elements);
    };
    let Some(owner_record) = store.symbol(owner) else {
        return Err(SourceCheckError::Call(call));
    };
    let Some(index) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
    else {
        return Ok(elements);
    };
    let Some(index_record) = store.symbol(index) else {
        return Err(SourceCheckError::Call(call));
    };
    if owner_record.name().as_utf8() == Some("ConcatArray")
        && owner_record.flags().contains(SymbolFlags::INTERFACE)
        && store
            .symbol_table(bootstrap.globals)
            .and_then(|globals| globals.get_source("ConcatArray"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            == Some(owner)
        && index_record.flags() == SymbolFlags::SIGNATURE
        && index_record.parent() == Some(owner)
        && index_record.declarations().is_some_and(|declarations| {
            !declarations.is_empty()
                && declarations.iter().all(|declaration| {
                    store.source_node_kind(*declaration) == Some(SyntaxKind::IndexSignature)
                })
        })
        && store.type_payload(*element).is_some()
    {
        elements.push(*element);
    }
    Ok(elements)
}

fn contextual_array_parameter_with_element(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    call: NodeRef,
    parameter: TypeId,
    element: TypeId,
) -> Result<Option<TypeId>, SourceCheckError> {
    if store.canonical_array_element_type(global_types, parameter)? == Some(element) {
        return Ok(Some(parameter));
    }
    let record = store
        .type_payload(parameter)
        .ok_or(SourceCheckError::Call(call))?;
    let TypeData::Union(union) = record.data() else {
        return Ok(None);
    };
    for constituent in &union.union.types {
        if store.canonical_array_element_type(global_types, *constituent)? == Some(element) {
            return Ok(Some(*constituent));
        }
    }
    Ok(None)
}

fn contextual_indexed_parameter_with_element(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    call: NodeRef,
    parameter: TypeId,
    key_type: TypeId,
    element: TypeId,
) -> Result<Option<TypeId>, SourceCheckError> {
    let record = store
        .type_payload(parameter)
        .ok_or(SourceCheckError::Call(call))?;
    if let TypeData::Union(union) = record.data() {
        for constituent in &union.union.types {
            if let Some(candidate) = contextual_indexed_parameter_with_element(
                store,
                global_types,
                call,
                *constituent,
                key_type,
                element,
            )? {
                return Ok(Some(candidate));
            }
        }
        return Ok(None);
    }
    Ok(contextual_indexed_element_types(
        store,
        global_types,
        call,
        parameter,
        key_type,
        &mut HashSet::new(),
    )?
    .contains(&element)
    .then_some(parameter))
}

/// Proves the complete direct-call syntax and rejects poisoned cold/warm cache
/// shapes before source execution publishes value state.
pub(super) fn plan_direct_source_call_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourceCallSyntax, SourceCheckError> {
    let Some(record) = arena.get(node.node) else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    };
    if record.kind == SyntaxKind::TaggedTemplateExpression {
        return plan_tagged_template_source_call_syntax(arena, store, node);
    }
    let NodeData::CallExpression(call) = &record.data else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    };
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || call.question_dot_token.is_some()
        || call.symbol.is_some()
        || call.facts != 0
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }

    let actual_callee = NodeRef::new(node.arena, node.file, call.expression);
    let Some(callee_record) = arena.get(call.expression) else {
        return Err(SourceCheckError::Call(node));
    };
    if callee_record.parent != Some(node.node) {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }
    let (callee, callee_form, callee_diagnostic_node) =
        match (callee_record.kind, &callee_record.data) {
            (SyntaxKind::Identifier, NodeData::Identifier(_)) => (
                actual_callee,
                SourceCallCalleeForm::Identifier,
                actual_callee,
            ),
            (SyntaxKind::CallExpression, NodeData::CallExpression(_)) => {
                plan_direct_source_call_syntax(arena, store, actual_callee)?;
                (
                    actual_callee,
                    SourceCallCalleeForm::Identifier,
                    actual_callee,
                )
            }
            (
                SyntaxKind::ParenthesizedExpression | SyntaxKind::FunctionExpression,
                NodeData::ParenthesizedExpression(_) | NodeData::FunctionExpression(_),
            ) if is_immediately_invoked_source_callable(arena, node) => (
                actual_callee,
                SourceCallCalleeForm::Identifier,
                actual_callee,
            ),
            (
                SyntaxKind::PropertyAccessExpression,
                NodeData::PropertyAccessExpression(property),
            ) => {
                let name = NodeRef::new(node.arena, node.file, property.name);
                let Some(name_record) = arena.get(property.name) else {
                    return Err(SourceCheckError::Call(node));
                };
                if name_record.parent != Some(actual_callee.node)
                    || name_record.flags.0 != 0
                    || !matches!(
                        (&name_record.data, name_record.kind),
                        (NodeData::Identifier(identifier), SyntaxKind::Identifier)
                            if identifier.flow_node.is_none() && !identifier.text.is_empty()
                    ) && !matches!(
                        (&name_record.data, name_record.kind),
                        (NodeData::PrivateIdentifier(identifier), SyntaxKind::PrivateIdentifier)
                            if identifier.text.starts_with('#') && identifier.text.len() > 1
                    )
                {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                }
                (
                    actual_callee,
                    SourceCallCalleeForm::RequiredOwnProperty,
                    name,
                )
            }
            (
                SyntaxKind::ParenthesizedExpression,
                NodeData::ParenthesizedExpression(parenthesized),
            ) => {
                let arrow = NodeRef::new(node.arena, node.file, parenthesized.expression);
                let Some(arrow_record) = arena.get(arrow.node) else {
                    return Err(SourceCheckError::Call(node));
                };
                let NodeData::ArrowFunction(function) = &arrow_record.data else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                };
                let Some(modifiers) = function.modifiers.as_ref() else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                };
                let [modifier] = modifiers.list.nodes.as_slice() else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                };
                let Some(modifier_record) = arena.get(*modifier) else {
                    return Err(SourceCheckError::Call(node));
                };
                if callee_record.flags.0 != 0
                    || arrow_record.kind != SyntaxKind::ArrowFunction
                    || arrow_record.flags.0 != 0
                    || arrow_record.parent != Some(actual_callee.node)
                    || !function.parameters.nodes.is_empty()
                    || function.parameters.has_trailing_comma
                    || function.type_parameters.is_some()
                    || function.type_.is_some()
                    || modifiers.flags.0 != 0
                    || modifiers.list.has_trailing_comma
                    || modifier_record.kind != SyntaxKind::AsyncKeyword
                    || modifier_record.flags.0 != 0
                    || modifier_record.parent != Some(arrow.node)
                    || !matches!(modifier_record.data, NodeData::Token(_))
                    || !call.arguments.nodes.is_empty()
                    || call.arguments.has_trailing_comma
                    || call.type_arguments.is_some()
                {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                }
                (
                    actual_callee,
                    SourceCallCalleeForm::ParenthesizedAsyncArrow,
                    actual_callee,
                )
            }
            _ => {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
        };

    let type_arguments = call
        .type_arguments
        .as_ref()
        .map(|type_arguments| {
            let start = type_arguments.range.start.get();
            let end = type_arguments.range.end.get();
            if type_arguments.range.start < record.range.start
                || type_arguments.range.end > record.range.end
                || end < start.saturating_add(2)
                || arena.source_text().is_some_and(|source| {
                    let start = usize::try_from(start).ok();
                    let close = usize::try_from(end.saturating_sub(1)).ok();
                    start.is_none_or(|start| source.as_bytes().get(start) != Some(&b'<'))
                        || close.is_none_or(|close| source.as_bytes().get(close) != Some(&b'>'))
                })
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            let nodes = type_arguments
                .nodes
                .iter()
                .map(|type_argument| {
                    let type_argument = NodeRef::new(node.arena, node.file, *type_argument);
                    let Some(type_argument_record) = arena.get(type_argument.node) else {
                        return Err(SourceCheckError::Call(node));
                    };
                    if type_argument_record.parent != Some(node.node)
                        || type_argument_record.range.start < type_arguments.range.start
                        || type_argument_record.range.end > type_arguments.range.end
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Call(node),
                        ));
                    }
                    Ok(type_argument)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut trailing_comma_range = None;
            let diagnostic_range = if let (Some(first), Some(last)) = (nodes.first(), nodes.last())
            {
                let first_range = arena
                    .get(first.node)
                    .ok_or(SourceCheckError::Call(node))?
                    .range;
                let last_range = arena
                    .get(last.node)
                    .ok_or(SourceCheckError::Call(node))?
                    .range;
                if first_range.start < TextPos::new(start.saturating_add(1))
                    || last_range.end > TextPos::new(end.saturating_sub(1))
                {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                }
                let diagnostic_end = if type_arguments.has_trailing_comma {
                    trailing_comma_range = arena.source_text().and_then(|source| {
                        trailing_type_argument_comma_range(
                            source,
                            last_range.end,
                            TextPos::new(end.saturating_sub(1)),
                        )
                    });
                    trailing_comma_range.map(|range| range.end)
                } else {
                    Some(last_range.end)
                };
                diagnostic_end
                    .map(|diagnostic_end| TextRange::new(first_range.start, diagnostic_end))
            } else {
                None
            };
            if type_arguments.has_trailing_comma && trailing_comma_range.is_none() {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            Ok(SourceTypeArgumentList {
                nodes,
                syntax_range: type_arguments.range,
                diagnostic_range,
                trailing_comma_range,
            })
        })
        .transpose()?;

    let mut arguments = Vec::with_capacity(call.arguments.nodes.len());
    let mut argument_arrow_nodes = Vec::with_capacity(call.arguments.nodes.len());
    let mut array_argument_arrow_nodes = Vec::with_capacity(call.arguments.nodes.len());
    for argument_id in &call.arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument_id);
        let Some(argument_record) = arena.get(*argument_id) else {
            return Err(SourceCheckError::Call(node));
        };
        if argument_record.parent != Some(node.node)
            || !is_supported_call_argument_syntax(arena, argument)
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(node),
            ));
        }
        let mut array_arrows = Vec::new();
        if !collect_array_argument_arrow_syntax(arena, argument, &mut array_arrows) {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(node),
            ));
        }
        argument_arrow_nodes.push(unparenthesized_arrow_argument_node(arena, argument));
        array_argument_arrow_nodes.push(array_arrows);
        arguments.push(argument);
    }
    preflight_call_links(store, node)?;
    Ok(DirectSourceCallSyntax {
        node,
        callee,
        form: DirectCallForm::Call,
        callee_form,
        callee_diagnostic_node,
        type_arguments,
        arguments,
        argument_arrow_nodes,
        array_argument_arrow_nodes,
    })
}

/// Authenticates a zero-argument call of an anonymous function or arrow.
pub(super) fn is_immediately_invoked_source_callable(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::CallExpression(call) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || call.question_dot_token.is_some()
        || call.symbol.is_some()
        || call.type_arguments.is_some()
        || call.facts != 0
        || !call.arguments.nodes.is_empty()
        || call.arguments.has_trailing_comma
        || call.arguments.range.end != record.range.end
    {
        return false;
    }

    let mut current = NodeRef::new(node.arena, node.file, call.expression);
    let mut expected_parent = node.node;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(current.node) {
            return false;
        }
        let Some(expression) = arena.get(current.node) else {
            return false;
        };
        if expression.flags.0 != 0 || expression.parent != Some(expected_parent) {
            return false;
        }
        match (&expression.data, expression.kind) {
            (
                NodeData::ParenthesizedExpression(parenthesized),
                SyntaxKind::ParenthesizedExpression,
            ) => {
                expected_parent = current.node;
                current = NodeRef::new(current.arena, current.file, parenthesized.expression);
            }
            (NodeData::FunctionExpression(function), SyntaxKind::FunctionExpression) => {
                return function.name.is_none() && function.parameters.nodes.is_empty();
            }
            (NodeData::ArrowFunction(arrow), SyntaxKind::ArrowFunction) => {
                return arrow.parameters.nodes.is_empty() && arrow.modifiers.is_none();
            }
            _ => return false,
        }
    }
}

fn plan_tagged_template_source_call_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourceCallSyntax, SourceCheckError> {
    let record = arena.get(node.node).ok_or(SourceCheckError::Call(node))?;
    let NodeData::TaggedTemplateExpression(tagged) = &record.data else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    };
    if record.flags.0 != 0
        || tagged.question_dot_token.is_some()
        || tagged.type_arguments.is_some()
        || tagged.facts != 0
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }

    let callee = NodeRef::new(node.arena, node.file, tagged.tag);
    let callee_record = arena.get(tagged.tag).ok_or(SourceCheckError::Call(node))?;
    if callee_record.parent != Some(node.node) || callee_record.flags.0 != 0 {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }
    let (callee_form, callee_diagnostic_node) = match (&callee_record.data, callee_record.kind) {
        (NodeData::Identifier(identifier), SyntaxKind::Identifier)
            if identifier.flow_node.is_none() && !identifier.text.is_empty() =>
        {
            (SourceCallCalleeForm::Identifier, callee)
        }
        (NodeData::PropertyAccessExpression(property), SyntaxKind::PropertyAccessExpression)
            if property.flow_node.is_none()
                && property.question_dot_token.is_none()
                && property.facts == 0 =>
        {
            let name = NodeRef::new(node.arena, node.file, property.name);
            let Some(record) = arena.get(property.name) else {
                return Err(SourceCheckError::Call(node));
            };
            if record.parent != Some(callee.node)
                || record.flags.0 != 0
                || !matches!(
                    (&record.data, record.kind),
                    (NodeData::Identifier(identifier), SyntaxKind::Identifier)
                        if identifier.flow_node.is_none() && !identifier.text.is_empty()
                ) && !matches!(
                    (&record.data, record.kind),
                    (NodeData::PrivateIdentifier(identifier), SyntaxKind::PrivateIdentifier)
                        if identifier.text.starts_with('#') && identifier.text.len() > 1
                )
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            (SourceCallCalleeForm::RequiredOwnProperty, name)
        }
        _ => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(node),
            ));
        }
    };

    let template = NodeRef::new(node.arena, node.file, tagged.template);
    let template_record = arena
        .get(tagged.template)
        .ok_or(SourceCheckError::Call(node))?;
    if template_record.parent != Some(node.node)
        || template_record.flags.0 != 0
        || template_record.range.start < callee_record.range.end
        || template_record.range.end != record.range.end
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }

    let arguments = match (&template_record.data, template_record.kind) {
        (
            NodeData::NoSubstitutionTemplateLiteral(literal),
            SyntaxKind::NoSubstitutionTemplateLiteral,
        ) if literal.symbol.is_none() => Vec::new(),
        (NodeData::TemplateExpression(expression), SyntaxKind::TemplateExpression) => {
            if expression.facts != 0
                || expression.template_spans.has_trailing_comma
                || expression.template_spans.nodes.is_empty()
                || expression.template_spans.range.start < template_record.range.start
                || expression.template_spans.range.end > template_record.range.end
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            let head = arena
                .get(expression.head)
                .ok_or(SourceCheckError::Call(node))?;
            if head.kind != SyntaxKind::TemplateHead
                || !matches!(&head.data, NodeData::TemplateHead(_))
                || head.parent != Some(template.node)
                || head.flags.0 != 0
                || head.range.start != template_record.range.start
                || head.range.end != expression.template_spans.range.start
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }

            let mut arguments = Vec::with_capacity(expression.template_spans.nodes.len());
            let mut previous_end = head.range.end;
            for (index, span_id) in expression.template_spans.nodes.iter().copied().enumerate() {
                let span = arena.get(span_id).ok_or(SourceCheckError::Call(node))?;
                let NodeData::TemplateSpan(span_data) = &span.data else {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                };
                let argument = NodeRef::new(node.arena, node.file, span_data.expression);
                let argument_record = arena
                    .get(span_data.expression)
                    .ok_or(SourceCheckError::Call(node))?;
                let literal = arena
                    .get(span_data.literal)
                    .ok_or(SourceCheckError::Call(node))?;
                let expected_literal_kind = if index + 1 == expression.template_spans.nodes.len() {
                    SyntaxKind::TemplateTail
                } else {
                    SyntaxKind::TemplateMiddle
                };
                if span.kind != SyntaxKind::TemplateSpan
                    || span.parent != Some(template.node)
                    || span.flags.0 != 0
                    || span.range.start < previous_end
                    || span.range.end > template_record.range.end
                    || argument_record.parent != Some(span_id)
                    || argument_record.range.start != span.range.start
                    || literal.kind != expected_literal_kind
                    || !matches!(
                        &literal.data,
                        NodeData::TemplateMiddle(_) | NodeData::TemplateTail(_)
                    )
                    || literal.parent != Some(span_id)
                    || literal.flags.0 != 0
                    || literal.range.start < argument_record.range.end
                    || literal.range.end != span.range.end
                    || !is_supported_call_argument_syntax(arena, argument)
                {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                }
                previous_end = span.range.end;
                arguments.push(argument);
            }
            if previous_end != template_record.range.end {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            arguments
        }
        _ => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(node),
            ));
        }
    };
    let argument_arrow_nodes = arguments
        .iter()
        .copied()
        .map(|argument| unparenthesized_arrow_argument_node(arena, argument))
        .collect();
    let array_argument_arrow_nodes = arguments
        .iter()
        .copied()
        .map(|argument| {
            let mut arrows = Vec::new();
            collect_array_argument_arrow_syntax(arena, argument, &mut arrows).then_some(arrows)
        })
        .collect::<Option<Vec<_>>>()
        .ok_or(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ))?;
    preflight_call_links(store, node)?;
    Ok(DirectSourceCallSyntax {
        node,
        callee,
        form: DirectCallForm::TaggedTemplate,
        callee_form,
        callee_diagnostic_node,
        type_arguments: None,
        arguments,
        argument_arrow_nodes,
        array_argument_arrow_nodes,
    })
}

fn trailing_type_argument_comma_range(
    source: &str,
    start: TextPos,
    closing_bracket: TextPos,
) -> Option<TextRange> {
    let start = usize::try_from(start.get()).ok()?;
    let closing_bracket = usize::try_from(closing_bracket.get()).ok()?;
    let before_close = source.get(start..closing_bracket)?;
    let comma = skip_call_type_argument_trivia(before_close)?;
    if before_close.as_bytes().get(comma) != Some(&b',') {
        return None;
    }
    Some(TextRange::new(
        TextPos::new(u32::try_from(start + comma).ok()?),
        TextPos::new(u32::try_from(start + comma + 1).ok()?),
    ))
}

fn skip_call_type_argument_trivia(text: &str) -> Option<usize> {
    let mut offset = 0;
    loop {
        let remaining = text.get(offset..)?;
        if remaining.starts_with("//") {
            offset += remaining.find(['\r', '\n']).unwrap_or(remaining.len());
            continue;
        }
        if remaining.starts_with("/*") {
            offset += remaining.find("*/")?.checked_add(2)?;
            continue;
        }
        let Some(character) = remaining.chars().next() else {
            return Some(offset);
        };
        if character.is_whitespace() || character == '\u{feff}' {
            offset = offset.checked_add(character.len_utf8())?;
            continue;
        }
        return Some(offset);
    }
}

pub(super) fn finish_direct_source_call_plan(
    syntax: &DirectSourceCallSyntax,
    callee: PlannedExpression,
    arguments: Vec<PlannedExpression>,
) -> Result<SourceCallPlan, SourceCheckError> {
    let exact_callee = match (&callee.kind, syntax.callee_form) {
        (PlannedExpressionKind::Identifier(_), SourceCallCalleeForm::Identifier) => true,
        (PlannedExpressionKind::Call(call), SourceCallCalleeForm::Identifier) => {
            call.node == callee.node && syntax.callee_diagnostic_node == syntax.callee
        }
        (
            PlannedExpressionKind::Parenthesized(_) | PlannedExpressionKind::Arrow(_),
            SourceCallCalleeForm::Identifier,
        ) => {
            syntax.arguments.is_empty()
                && syntax.type_arguments.is_none()
                && syntax.callee_diagnostic_node == syntax.callee
                && matches!(
                    callee.unparenthesized().kind,
                    PlannedExpressionKind::Arrow(_)
                )
        }
        (PlannedExpressionKind::Property(property), SourceCallCalleeForm::RequiredOwnProperty) => {
            property.is_call_callee_for(syntax.node, syntax.callee_diagnostic_node)
        }
        (
            PlannedExpressionKind::Parenthesized(expression),
            SourceCallCalleeForm::ParenthesizedAsyncArrow,
        ) => matches!(&expression.kind, PlannedExpressionKind::Arrow(_)),
        _ => false,
    };
    if callee.node != syntax.callee
        || !exact_callee
        || arguments.len() != syntax.arguments.len()
        || syntax.argument_arrow_nodes.len() != syntax.arguments.len()
        || syntax.array_argument_arrow_nodes.len() != syntax.arguments.len()
        || !arguments
            .iter()
            .zip(&syntax.arguments)
            .zip(&syntax.argument_arrow_nodes)
            .zip(&syntax.array_argument_arrow_nodes)
            .all(|(((argument, syntax_node), syntax_arrow), array_arrows)| {
                let unparenthesized = argument.unparenthesized();
                let exact_arrow = match (&unparenthesized.kind, syntax_arrow) {
                    (PlannedExpressionKind::Arrow(_), Some(node)) => unparenthesized.node == *node,
                    (PlannedExpressionKind::Arrow(_), None) | (_, Some(_)) => false,
                    (_, None) => true,
                };
                let mut planned_array_arrows = Vec::new();
                collect_array_argument_arrow_plans(argument, &mut planned_array_arrows);
                argument.node == *syntax_node
                    && exact_arrow
                    && &planned_array_arrows == array_arrows
                    && is_supported_call_argument_plan(argument)
            })
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(syntax.node),
        ));
    }
    Ok(SourceCallPlan {
        node: syntax.node,
        callee,
        form: syntax.form,
        callee_diagnostic_node: syntax.callee_diagnostic_node,
        type_arguments: syntax.type_arguments.clone(),
        arguments,
    })
}

fn unparenthesized_arrow_argument_node(arena: &NodeArena, mut node: NodeRef) -> Option<NodeRef> {
    loop {
        let record = arena.get(node.node)?;
        match (&record.data, record.kind) {
            (
                NodeData::ParenthesizedExpression(parenthesized),
                SyntaxKind::ParenthesizedExpression,
            ) => {
                node = NodeRef::new(node.arena, node.file, parenthesized.expression);
            }
            (NodeData::ArrowFunction(_), SyntaxKind::ArrowFunction) => return Some(node),
            (NodeData::FunctionExpression(_), SyntaxKind::FunctionExpression)
                if is_supported_function_expression_argument_syntax(arena, node) =>
            {
                return Some(node);
            }
            _ => return None,
        }
    }
}

fn collect_array_argument_arrow_syntax(
    arena: &NodeArena,
    node: NodeRef,
    arrows: &mut Vec<NodeRef>,
) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    match (&record.data, record.kind) {
        (NodeData::ParenthesizedExpression(parenthesized), SyntaxKind::ParenthesizedExpression) => {
            let inner = NodeRef::new(node.arena, node.file, parenthesized.expression);
            arena.get(inner.node).is_some_and(|inner_record| {
                inner_record.parent == Some(node.node)
                    && collect_array_argument_arrow_syntax(arena, inner, arrows)
            })
        }
        (NodeData::ArrayLiteralExpression(array), SyntaxKind::ArrayLiteralExpression) => {
            if record.flags.0 != 0 || array.facts != 0 {
                return false;
            }
            for element_id in &array.elements.nodes {
                let element = NodeRef::new(node.arena, node.file, *element_id);
                let Some(element_record) = arena.get(*element_id) else {
                    return false;
                };
                if element_record.parent != Some(node.node)
                    || !collect_array_argument_arrow_syntax(arena, element, arrows)
                {
                    return false;
                }
            }
            true
        }
        (NodeData::ArrowFunction(_), SyntaxKind::ArrowFunction) => {
            if !is_supported_arrow_argument_syntax(arena, node) {
                return false;
            }
            arrows.push(node);
            true
        }
        (NodeData::FunctionExpression(_), SyntaxKind::FunctionExpression) => {
            if !is_supported_function_expression_argument_syntax(arena, node) {
                return false;
            }
            arrows.push(node);
            true
        }
        _ => true,
    }
}

fn collect_array_argument_arrow_plans(expression: &PlannedExpression, arrows: &mut Vec<NodeRef>) {
    match &expression.kind {
        PlannedExpressionKind::Parenthesized(inner) => {
            collect_array_argument_arrow_plans(inner, arrows);
        }
        PlannedExpressionKind::Array(elements) => {
            for element in elements {
                collect_array_argument_arrow_plans(element, arrows);
            }
        }
        PlannedExpressionKind::Arrow(_) => arrows.push(expression.node),
        _ => {}
    }
}

fn is_supported_call_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    match record.kind {
        SyntaxKind::Identifier
        | SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::StringLiteral
        | SyntaxKind::RegularExpressionLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral => true,
        SyntaxKind::ParenthesizedExpression => {
            let NodeData::ParenthesizedExpression(parenthesized) = &record.data else {
                return false;
            };
            let inner = NodeRef::new(node.arena, node.file, parenthesized.expression);
            arena
                .get(parenthesized.expression)
                .is_some_and(|inner_record| {
                    inner_record.parent == Some(node.node)
                        && is_supported_call_argument_syntax(arena, inner)
                })
        }
        SyntaxKind::PrefixUnaryExpression => {
            let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                return false;
            };
            arena.get(prefix.operand).is_some_and(|operand| {
                operand.parent == Some(node.node)
                    && matches!(
                        operand.kind,
                        SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
                    )
            })
        }
        SyntaxKind::PropertyAccessExpression => {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return false;
            };
            if record.flags.0 != 0
                || access.flow_node.is_some()
                || access.question_dot_token.is_some()
                || access.facts != 0
            {
                return false;
            }
            let Some(receiver) = arena.get(access.expression) else {
                return false;
            };
            let Some(name) = arena.get(access.name) else {
                return false;
            };
            receiver.parent == Some(node.node)
                && receiver.flags.0 == 0
                && (matches!(
                    (&receiver.data, receiver.kind),
                    (NodeData::Identifier(identifier), SyntaxKind::Identifier)
                        if identifier.flow_node.is_none()
                ) || matches!(
                    (&receiver.data, receiver.kind),
                    (NodeData::KeywordExpression(keyword), SyntaxKind::ThisKeyword)
                        if keyword.flow_node.is_none()
                ))
                && name.parent == Some(node.node)
                && name.flags.0 == 0
                && (matches!(
                    (&name.data, name.kind),
                    (NodeData::Identifier(identifier), SyntaxKind::Identifier)
                        if identifier.flow_node.is_none() && !identifier.text.is_empty()
                ) || matches!(
                    (&name.data, name.kind),
                    (NodeData::PrivateIdentifier(identifier), SyntaxKind::PrivateIdentifier)
                        if identifier.text.starts_with('#') && identifier.text.len() > 1
                ))
        }
        SyntaxKind::ElementAccessExpression => is_context_insensitive_element_syntax(arena, node),
        SyntaxKind::TemplateExpression => {
            let NodeData::TemplateExpression(template) = &record.data else {
                return false;
            };
            record.flags.0 == 0
                && template.facts == 0
                && !template.template_spans.nodes.is_empty()
                && template.template_spans.nodes.iter().all(|span| {
                    let Some(span_record) = arena.get(*span) else {
                        return false;
                    };
                    let NodeData::TemplateSpan(data) = &span_record.data else {
                        return false;
                    };
                    span_record.parent == Some(node.node)
                        && arena.get(data.expression).is_some_and(|expression| {
                            expression.parent == Some(*span)
                                && is_supported_call_argument_syntax(
                                    arena,
                                    NodeRef::new(node.arena, node.file, data.expression),
                                )
                        })
                })
        }
        SyntaxKind::CallExpression => matches!(&record.data, NodeData::CallExpression(_)),
        SyntaxKind::TaggedTemplateExpression => {
            matches!(&record.data, NodeData::TaggedTemplateExpression(_))
        }
        SyntaxKind::ArrowFunction => is_supported_arrow_argument_syntax(arena, node),
        SyntaxKind::FunctionExpression => {
            is_supported_function_expression_argument_syntax(arena, node)
        }
        SyntaxKind::ObjectLiteralExpression => {
            matches!(&record.data, NodeData::ObjectLiteralExpression(_))
        }
        SyntaxKind::ArrayLiteralExpression => {
            matches!(&record.data, NodeData::ArrayLiteralExpression(_))
        }
        SyntaxKind::TypeAssertionExpression | SyntaxKind::AsExpression => {
            is_supported_type_assertion_argument_syntax(arena, node)
        }
        SyntaxKind::BinaryExpression => {
            is_context_insensitive_primitive_binary_syntax(arena, node)
                || is_context_insensitive_logical_binary_syntax(arena, node)
                || is_supported_shorthand_assignment_argument_syntax(arena, node)
        }
        _ => false,
    }
}

/// Accepts authenticated anonymous, zero-parameter function arguments.
fn is_supported_function_expression_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::FunctionExpression(function) = &record.data else {
        return false;
    };
    let Some(body) = arena.get(function.body) else {
        return false;
    };

    record.kind == SyntaxKind::FunctionExpression
        && record.flags.0 == 0
        && function.name.is_none()
        && function.modifiers.is_none()
        && function.asterisk_token.is_none()
        && function.type_parameters.is_none()
        && function.type_.is_none()
        && function.parameters.nodes.is_empty()
        && !function.parameters.has_trailing_comma
        && function.parameters.range.start >= record.range.start
        && function.parameters.range.end <= record.range.end
        && function.full_signature.is_none()
        && function.next_container.is_none()
        && function.symbol.is_none()
        && function.flow_node.is_none()
        && function.end_flow_node.is_none()
        && function.return_flow_node.is_none()
        && function.facts == 0
        && body.kind == SyntaxKind::Block
        && matches!(&body.data, NodeData::Block(_))
        && body.flags.0 == 0
        && body.parent == Some(node.node)
        && body.range.start >= function.parameters.range.end
        && body.range.end <= record.range.end
}

fn is_supported_shorthand_assignment_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::BinaryExpression(binary) = &record.data else {
        return false;
    };
    let Some(object_record) = arena.get(binary.left) else {
        return false;
    };
    let NodeData::ObjectLiteralExpression(object) = &object_record.data else {
        return false;
    };
    let Some(operator) = arena.get(binary.operator_token) else {
        return false;
    };
    let Some(source) = arena.get(binary.right) else {
        return false;
    };
    let [property] = object.properties.nodes.as_slice() else {
        return false;
    };
    let Some(property_record) = arena.get(*property) else {
        return false;
    };
    let NodeData::ShorthandPropertyAssignment(shorthand) = &property_record.data else {
        return false;
    };
    let (Some(equals), Some(initializer)) = (
        shorthand.equals_token,
        shorthand.object_assignment_initializer,
    ) else {
        return false;
    };
    let Some(name_record) = arena.get(shorthand.name) else {
        return false;
    };
    let NodeData::Identifier(name) = &name_record.data else {
        return false;
    };
    let Some(equals_record) = arena.get(equals) else {
        return false;
    };
    let Some(initializer_record) = arena.get(initializer) else {
        return false;
    };

    record.kind == SyntaxKind::BinaryExpression
        && record.flags.0 == 0
        && binary.symbol.is_none()
        && binary.type_.is_none()
        && binary.facts == 0
        && binary.modifiers.is_none()
        && object_record.kind == SyntaxKind::ObjectLiteralExpression
        && object_record.flags.0 == 0
        && object_record.parent == Some(node.node)
        && object.symbol.is_none()
        && object.facts == 0
        && object.properties.range == object_record.range
        && !object.properties.has_trailing_comma
        && operator.kind == SyntaxKind::EqualsToken
        && operator.flags.0 == 0
        && operator.parent == Some(node.node)
        && matches!(operator.data, NodeData::Token(_))
        && source.parent == Some(node.node)
        && object_record.range.end <= operator.range.start
        && operator.range.end <= source.range.start
        && property_record.kind == SyntaxKind::ShorthandPropertyAssignment
        && property_record.flags.0 == 0
        && property_record.parent == Some(binary.left)
        && shorthand.postfix_token.is_none()
        && shorthand.modifiers.is_none()
        && shorthand.type_.is_none()
        && shorthand.symbol.is_none()
        && shorthand.facts == 0
        && name_record.kind == SyntaxKind::Identifier
        && name_record.flags.0 == 0
        && name_record.parent == Some(*property)
        && name.flow_node.is_none()
        && !name.text.is_empty()
        && equals_record.kind == SyntaxKind::EqualsToken
        && equals_record.flags.0 == 0
        && equals_record.parent == Some(*property)
        && matches!(equals_record.data, NodeData::Token(_))
        && initializer_record.parent == Some(*property)
        && name_record.range.end <= equals_record.range.start
        && equals_record.range.end <= initializer_record.range.start
        && initializer_record.range.end <= property_record.range.end
        && is_supported_call_argument_syntax(
            arena,
            NodeRef::new(node.arena, node.file, initializer),
        )
        && is_supported_call_argument_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.right),
        )
}

fn is_supported_arrow_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::ArrowFunction(arrow) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::ArrowFunction
        || record.flags.0 != 0
        || arrow.asterisk_token.is_some()
        || arrow.end_flow_node.is_some()
        || arrow.flow_node.is_some()
        || arrow.full_signature.is_some()
        || arrow.next_container.is_some()
        || arrow.symbol.is_some()
        || arrow.type_parameters.is_some()
        || arrow.facts != 0
        || arrow.modifiers.is_some()
        || arrow.parameters.range.start < record.range.start
        || arrow.parameters.range.end > record.range.end
    {
        return false;
    }

    let Some(token) = arena.get(arrow.equals_greater_than_token) else {
        return false;
    };
    let Some(body) = arena.get(arrow.body) else {
        return false;
    };
    if token.kind != SyntaxKind::EqualsGreaterThanToken
        || !matches!(token.data, NodeData::Token(_))
        || token.parent != Some(node.node)
        || token.flags.0 != 0
        || token.range.start < arrow.parameters.range.end
        || body.parent != Some(node.node)
        || body.range.start < token.range.end
        || body.range.end > record.range.end
    {
        return false;
    }
    if let Some(type_id) = arrow.type_ {
        let Some(annotation) = arena.get(type_id) else {
            return false;
        };
        if annotation.parent != Some(node.node)
            || annotation.range.start < arrow.parameters.range.end
            || annotation.range.end > token.range.start
        {
            return false;
        }
    }

    let tuple_sort_callback =
        arrow.parameters.nodes.len() == 2 && is_authenticated_sort_callback_syntax(arena, node);

    let mut previous_end = arrow.parameters.range.start;
    for parameter_id in &arrow.parameters.nodes {
        let Some(parameter) = arena.get(*parameter_id) else {
            return false;
        };
        let NodeData::ParameterDeclaration(data) = &parameter.data else {
            return false;
        };
        if parameter.kind != SyntaxKind::Parameter
            || parameter.parent != Some(node.node)
            || parameter.flags.0 != 0
            || parameter.range.start < previous_end
            || parameter.range.end > arrow.parameters.range.end
            || data.facts != 0
            || data.symbol.is_some()
            || data.modifiers.is_some()
        {
            return false;
        }
        let Some(name) = arena.get(data.name) else {
            return false;
        };
        if name.parent != Some(*parameter_id)
            || name.flags.0 != 0
            || name.range.start < parameter.range.start
            || name.range.end > parameter.range.end
            || !match (&name.data, name.kind) {
                (NodeData::Identifier(identifier), SyntaxKind::Identifier) => {
                    identifier.flow_node.is_none() && !identifier.text.is_empty()
                }
                (NodeData::BindingPattern(pattern), SyntaxKind::ArrayBindingPattern)
                    if tuple_sort_callback =>
                {
                    is_authenticated_sort_tuple_binding(arena, data.name, pattern)
                }
                _ => false,
            }
        {
            return false;
        }
        if let Some(type_id) = data.type_ {
            let Some(annotation) = arena.get(type_id) else {
                return false;
            };
            if annotation.parent != Some(*parameter_id)
                || annotation.range.start < name.range.end
                || annotation.range.end > parameter.range.end
            {
                return false;
            }
        }
        previous_end = parameter.range.end;
    }
    true
}

pub(super) fn is_authenticated_sort_callback_syntax(arena: &NodeArena, arrow: NodeRef) -> bool {
    let Some(call_id) = arena.get(arrow.node).and_then(|record| record.parent) else {
        return false;
    };
    let Some(call_record) = arena.get(call_id) else {
        return false;
    };
    let NodeData::CallExpression(call) = &call_record.data else {
        return false;
    };
    if call_record.kind != SyntaxKind::CallExpression
        || call_record.flags.0 != 0
        || call.question_dot_token.is_some()
        || call.symbol.is_some()
        || call.facts != 0
        || call.arguments.nodes.as_slice() != [arrow.node]
    {
        return false;
    }
    let Some(callee_record) = arena.get(call.expression) else {
        return false;
    };
    let NodeData::PropertyAccessExpression(callee) = &callee_record.data else {
        return false;
    };
    let Some(receiver) = arena.get(callee.expression) else {
        return false;
    };
    let Some(name_record) = arena.get(callee.name) else {
        return false;
    };
    matches!(
        &name_record.data,
        NodeData::Identifier(name)
            if callee_record.kind == SyntaxKind::PropertyAccessExpression
                && callee_record.flags.0 == 0
                && callee_record.parent == Some(call_id)
                && callee.flow_node.is_none()
                && callee.question_dot_token.is_none()
                && callee.facts == 0
                && receiver.parent == Some(call.expression)
                && name_record.kind == SyntaxKind::Identifier
                && name_record.flags.0 == 0
                && name_record.parent == Some(call.expression)
                && name.flow_node.is_none()
                && name.text == "sort"
    )
}

pub(super) fn is_authenticated_sort_tuple_binding(
    arena: &NodeArena,
    pattern_id: ts_ast::NodeId,
    pattern: &ts_ast::BindingPatternData,
) -> bool {
    if pattern.facts != 0
        || pattern.elements.has_trailing_comma
        || pattern.elements.nodes.len() != 2
    {
        return false;
    }
    pattern.elements.nodes.iter().all(|element_id| {
        let Some(element_record) = arena.get(*element_id) else {
            return false;
        };
        let NodeData::BindingElement(element) = &element_record.data else {
            return false;
        };
        let Some(name_id) = element.name else {
            return false;
        };
        let Some(name_record) = arena.get(name_id) else {
            return false;
        };
        matches!(
            &name_record.data,
            NodeData::Identifier(name)
                if element_record.kind == SyntaxKind::BindingElement
                    && element_record.flags.0 == 0
                    && element_record.parent == Some(pattern_id)
                    && element.dot_dot_dot_token.is_none()
                    && element.flow_node.is_none()
                    && element.initializer.is_none()
                    && element.local_symbol.is_none()
                    && element.property_name.is_none()
                    && element.symbol.is_none()
                    && element.facts == 0
                    && name_record.kind == SyntaxKind::Identifier
                    && name_record.flags.0 == 0
                    && name_record.parent == Some(*element_id)
                    && name.flow_node.is_none()
                    && !name.text.is_empty()
        )
    })
}

fn is_supported_type_assertion_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let (type_, operand) = match (&record.data, record.kind) {
        (NodeData::TypeAssertion(assertion), SyntaxKind::TypeAssertionExpression) => {
            (assertion.type_, assertion.expression)
        }
        (NodeData::AsExpression(assertion), SyntaxKind::AsExpression) => {
            (assertion.type_, assertion.expression)
        }
        _ => return false,
    };
    arena
        .get(type_)
        .is_some_and(|annotation| annotation.parent == Some(node.node))
        && arena
            .get(operand)
            .is_some_and(|expression| expression.parent == Some(node.node))
        && is_supported_call_argument_syntax(arena, NodeRef::new(node.arena, node.file, operand))
}

fn is_context_insensitive_element_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::ElementAccessExpression(access) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::ElementAccessExpression
        || record.flags.0 != 0
        || access.flow_node.is_some()
        || access.question_dot_token.is_some()
        || access.facts != 0
    {
        return false;
    }
    let Some(receiver) = arena.get(access.expression) else {
        return false;
    };
    let Some(index) = arena.get(access.argument_expression) else {
        return false;
    };
    receiver.parent == Some(node.node)
        && receiver.kind == SyntaxKind::Identifier
        && receiver.flags.0 == 0
        && matches!(
            &receiver.data,
            NodeData::Identifier(identifier) if identifier.flow_node.is_none()
        )
        && index.parent == Some(node.node)
        && receiver.range.end <= index.range.start
        && is_context_insensitive_element_index_syntax(arena, access.argument_expression)
}

fn is_context_insensitive_element_index_syntax(arena: &NodeArena, node: ts_ast::NodeId) -> bool {
    let Some(record) = arena.get(node) else {
        return false;
    };
    match record.kind {
        SyntaxKind::Identifier => {
            record.flags.0 == 0
                && matches!(
                    &record.data,
                    NodeData::Identifier(identifier) if identifier.flow_node.is_none()
                )
        }
        SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral => true,
        SyntaxKind::PrefixUnaryExpression => {
            let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                return false;
            };
            arena.get(prefix.operand).is_some_and(|operand| {
                operand.parent == Some(node)
                    && matches!(
                        operand.kind,
                        SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
                    )
            })
        }
        _ => false,
    }
}

fn is_context_insensitive_logical_binary_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::BinaryExpression(binary) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::BinaryExpression
        || record.flags.0 != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
    {
        return false;
    }
    let Some(left) = arena.get(binary.left) else {
        return false;
    };
    let Some(operator) = arena.get(binary.operator_token) else {
        return false;
    };
    let Some(right) = arena.get(binary.right) else {
        return false;
    };
    left.parent == Some(node.node)
        && operator.parent == Some(node.node)
        && right.parent == Some(node.node)
        && left.range.end <= operator.range.start
        && operator.range.end <= right.range.start
        && operator.flags.0 == 0
        && matches!(operator.data, NodeData::Token(_))
        && logical_binary_operator_text(operator.kind).is_some()
        && is_supported_call_argument_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.left),
        )
        && is_supported_call_argument_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.right),
        )
}

fn is_context_insensitive_primitive_binary_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    // This is the call owner's context-sensitivity proof. Source planning still
    // performs the exact operator-spelling, cache, and operand capability proof.
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::BinaryExpression(binary) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::BinaryExpression
        || record.flags.0 != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
    {
        return false;
    }
    let Some(left) = arena.get(binary.left) else {
        return false;
    };
    let Some(operator) = arena.get(binary.operator_token) else {
        return false;
    };
    let Some(right) = arena.get(binary.right) else {
        return false;
    };
    left.parent == Some(node.node)
        && operator.parent == Some(node.node)
        && right.parent == Some(node.node)
        && left.range.end <= operator.range.start
        && operator.range.end <= right.range.start
        && operator.flags.0 == 0
        && matches!(operator.data, NodeData::Token(_))
        && primitive_binary_operator_text(operator.kind).is_some()
        && is_context_insensitive_primitive_binary_operand_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.left),
        )
        && is_context_insensitive_primitive_binary_operand_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.right),
        )
}

fn is_context_insensitive_primitive_binary_operand_syntax(
    arena: &NodeArena,
    node: NodeRef,
) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    match record.kind {
        SyntaxKind::Identifier
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral => true,
        SyntaxKind::ParenthesizedExpression => {
            let NodeData::ParenthesizedExpression(parenthesized) = &record.data else {
                return false;
            };
            let inner = NodeRef::new(node.arena, node.file, parenthesized.expression);
            arena
                .get(parenthesized.expression)
                .is_some_and(|inner_record| {
                    inner_record.parent == Some(node.node)
                        && is_context_insensitive_primitive_binary_operand_syntax(arena, inner)
                })
        }
        SyntaxKind::PrefixUnaryExpression => {
            let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                return false;
            };
            arena.get(prefix.operand).is_some_and(|operand| {
                operand.parent == Some(node.node)
                    && matches!(
                        operand.kind,
                        SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
                    )
            })
        }
        SyntaxKind::ElementAccessExpression => is_context_insensitive_element_syntax(arena, node),
        SyntaxKind::BinaryExpression => is_context_insensitive_primitive_binary_syntax(arena, node),
        _ => false,
    }
}

fn is_supported_call_argument_plan(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::Null
        | PlannedExpressionKind::String(_)
        | PlannedExpressionKind::RegularExpression(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Element(_)
        | PlannedExpressionKind::Arrow(_) => true,
        PlannedExpressionKind::Call(call) => {
            call.node == expression.node
                && call.arguments.iter().all(is_supported_call_argument_plan)
        }
        PlannedExpressionKind::Object { properties, .. } => {
            properties.iter().all(is_supported_call_argument_plan)
        }
        PlannedExpressionKind::Array(elements) => {
            elements.iter().all(is_supported_call_argument_plan)
        }
        PlannedExpressionKind::Template(template) => template
            .substitutions
            .iter()
            .all(is_supported_call_argument_plan),
        PlannedExpressionKind::Assertion { operand, .. } => {
            is_supported_call_argument_plan(operand)
        }
        PlannedExpressionKind::Parenthesized(inner) => is_supported_call_argument_plan(inner),
        PlannedExpressionKind::Binary(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && binary.shorthand_assignment_initializer().map_or_else(
                    || {
                        primitive_binary_operator_text(binary.operator()).is_some()
                            && is_context_insensitive_primitive_binary_operand_plan(left)
                            && is_context_insensitive_primitive_binary_operand_plan(right)
                    },
                    |initializer| {
                        binary.operator() == SyntaxKind::EqualsToken
                            && is_supported_call_argument_plan(left)
                            && is_supported_call_argument_plan(right)
                            && is_supported_call_argument_plan(initializer)
                    },
                )
        }
        PlannedExpressionKind::Logical(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && logical_binary_operator_text(binary.operator()).is_some()
                && is_supported_call_argument_plan(left)
                && is_supported_call_argument_plan(right)
        }
        PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Conditional(_) => false,
    }
}

fn is_context_insensitive_primitive_binary_operand_plan(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::Element(_) => true,
        PlannedExpressionKind::Parenthesized(inner) => {
            is_context_insensitive_primitive_binary_operand_plan(inner)
        }
        PlannedExpressionKind::Binary(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && primitive_binary_operator_text(binary.operator()).is_some()
                && is_context_insensitive_primitive_binary_operand_plan(left)
                && is_context_insensitive_primitive_binary_operand_plan(right)
        }
        PlannedExpressionKind::Logical(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && logical_binary_operator_text(binary.operator()).is_some()
                && is_context_insensitive_primitive_binary_operand_plan(left)
                && is_context_insensitive_primitive_binary_operand_plan(right)
        }
        PlannedExpressionKind::Null
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::Template(_)
        | PlannedExpressionKind::RegularExpression(_)
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Call(_)
        | PlannedExpressionKind::Arrow(_)
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Conditional(_) => false,
    }
}

fn preflight_call_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
    let mut resolved_type = None;
    if let Some(links) = store.type_node_links(node) {
        let expected = TypeNodeLinks {
            resolved_type: links.resolved_type,
            ..TypeNodeLinks::default()
        };
        if links != &expected
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(SourceCheckError::Call(node));
        }
        resolved_type = links.resolved_type;
    }
    let mut resolved_signature = None;
    if let Some(links) = store.signature_links(node) {
        let expected = SignatureLinks {
            resolved_signature: links.resolved_signature,
            ..SignatureLinks::default()
        };
        if links != &expected
            || match links.resolved_signature {
                ResolvedSignatureState::Unresolved => false,
                ResolvedSignatureState::Resolving => true,
                ResolvedSignatureState::Resolved(signature) => store.signature(signature).is_none(),
            }
        {
            return Err(SourceCheckError::Call(node));
        }
        resolved_signature = links.resolved_signature.signature();
    }
    if resolved_type.is_some() != resolved_signature.is_some() {
        return Err(SourceCheckError::Call(node));
    }
    if let (Some(resolved_type), Some(resolved_signature)) = (resolved_type, resolved_signature)
        && store
            .signature(resolved_signature)
            .and_then(super::signatures::Signature::resolved_return_type)
            != Some(resolved_type)
    {
        return Err(SourceCheckError::Call(node));
    }
    Ok(())
}

/// Resolves one already-typed source call, retrying the two lazy semantic
/// boundaries before publishing its exact signature/return caches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedLegacySourceCall {
    signature: SignatureId,
    return_type: TypeId,
    minimum_argument_count: usize,
    maximum_argument_count: usize,
    has_effective_rest: bool,
    applicability: DirectCallApplicability,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ResolvedSourceCall {
    Legacy(ResolvedLegacySourceCall),
    NongenericTypeArguments(ResolvedLegacySourceCall),
    Vector(GenericCallVectorResolution),
    Identity(IdentityGenericCallResolution),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceCallResolutionError {
    Retry(SignatureId),
    Relation(RelationUnavailable),
    Unsupported,
    Invariant,
}

#[derive(Clone, Copy, Debug)]
struct SourceCallResolutionRequest<'a> {
    form: DirectCallForm,
    callee_type: TypeId,
    argument_types: &'a [TypeId],
    explicit_type_arguments: Option<&'a [TypeId]>,
}

fn resolve_source_call_once(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    request: SourceCallResolutionRequest<'_>,
) -> Result<ResolvedSourceCall, SourceCallResolutionError> {
    let SourceCallResolutionRequest {
        form,
        callee_type,
        argument_types,
        explicit_type_arguments,
    } = request;
    let nongeneric_type_arguments = if explicit_type_arguments.is_some() {
        match validate_stored_callable_set(store, callee_type) {
            StoredCallableSetValidation::Valid { projection, .. }
                if projection.construct_signatures.is_empty()
                    && projection.call_signatures.len() == 1 =>
            {
                store
                    .signature(projection.call_signatures[0].signature)
                    .ok_or(SourceCallResolutionError::Invariant)?
                    .type_parameters()
                    .is_empty()
            }
            StoredCallableSetValidation::Malformed { .. } => {
                return Err(SourceCallResolutionError::Invariant);
            }
            StoredCallableSetValidation::NotCallable
            | StoredCallableSetValidation::Pending { .. }
            | StoredCallableSetValidation::Valid { .. } => false,
        }
    } else {
        false
    };
    if explicit_type_arguments.is_none() || nongeneric_type_arguments {
        let request = DirectCallRequest {
            form,
            optional_chain: false,
            type_argument_count: 0,
            has_spread_argument: false,
            callee: callee_type,
            arguments: argument_types,
        };
        match resolve_direct_call(store, global_types, options.strict_function_types, request) {
            Ok(resolution) => {
                let resolved = ResolvedLegacySourceCall {
                    signature: resolution.projection.signature,
                    return_type: resolution.projection.return_type,
                    minimum_argument_count: resolution.projection.minimum_argument_count,
                    maximum_argument_count: resolution.projection.maximum_argument_count,
                    has_effective_rest: resolution.projection.has_effective_rest,
                    applicability: resolution.applicability,
                };
                return Ok(if nongeneric_type_arguments {
                    ResolvedSourceCall::NongenericTypeArguments(resolved)
                } else {
                    ResolvedSourceCall::Legacy(resolved)
                });
            }
            Err(DirectCallError::Unsupported(DirectCallUnsupported::GenericSignature(_)))
                if form == DirectCallForm::Call => {}
            Err(
                DirectCallError::Unsupported(DirectCallUnsupported::UnresolvedReturnType(
                    signature,
                ))
                | DirectCallError::Relation(RelationUnavailable::UnresolvedSignatureReturn(
                    signature,
                )),
            ) => return Err(SourceCallResolutionError::Retry(signature)),
            Err(DirectCallError::Relation(error)) => {
                return Err(SourceCallResolutionError::Relation(error));
            }
            Err(DirectCallError::Unsupported(_)) => {
                return Err(SourceCallResolutionError::Unsupported);
            }
            Err(DirectCallError::Invariant(_)) => return Err(SourceCallResolutionError::Invariant),
        }
    }

    match validate_stored_source_callable(store, callee_type) {
        StoredSourceCallableValidation::Valid(_) => {}
        StoredSourceCallableValidation::NotSourceCallable
        | StoredSourceCallableValidation::Pending => {
            return Err(SourceCallResolutionError::Unsupported);
        }
        StoredSourceCallableValidation::Malformed => {
            return Err(SourceCallResolutionError::Invariant);
        }
    }
    let vector_request = GenericCallVectorRequest {
        form,
        optional_chain: false,
        explicit_type_arguments,
        has_spread_argument: false,
        callee: callee_type,
        arguments: argument_types,
    };
    match resolve_generic_call_vector_with_session(
        store,
        global_types,
        options.strict_function_types,
        vector_request,
        existing_call_signature,
        session,
    ) {
        Ok(resolution) => return Ok(ResolvedSourceCall::Vector(resolution)),
        Err(
            GenericCallVectorError::Unsupported(
                GenericCallVectorUnsupported::UnresolvedReturnType(signature),
            )
            | GenericCallVectorError::Relation(RelationUnavailable::UnresolvedSignatureReturn(
                signature,
            )),
        ) => return Err(SourceCallResolutionError::Retry(signature)),
        Err(
            GenericCallVectorError::Relation(error)
            | GenericCallVectorError::Inference(NakedTypeCandidateError::Relation(error)),
        ) => {
            return Err(SourceCallResolutionError::Relation(error));
        }
        Err(error)
            if source_identity_fallback_is_exact(
                store,
                explicit_type_arguments,
                argument_types,
                &error,
            ) => {}
        Err(GenericCallVectorError::Invariant(_)) => {
            return Err(SourceCallResolutionError::Invariant);
        }
        Err(
            GenericCallVectorError::Unsupported(_)
            | GenericCallVectorError::Inference(_)
            | GenericCallVectorError::Instantiation(_),
        ) => return Err(SourceCallResolutionError::Unsupported),
    }

    let request = IdentityGenericCallRequest {
        form,
        optional_chain: false,
        explicit_type_arguments,
        has_spread_argument: false,
        callee: callee_type,
        arguments: argument_types,
    };
    match resolve_source_identity_generic_call_with_session(
        store,
        host,
        global_types,
        options.strict_function_types,
        request,
        existing_call_signature,
        session,
    ) {
        Ok(resolution) => Ok(ResolvedSourceCall::Identity(resolution)),
        Err(
            IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::UnresolvedReturnType(signature),
            )
            | IdentityGenericCallError::Relation(RelationUnavailable::UnresolvedSignatureReturn(
                signature,
            )),
        ) => Err(SourceCallResolutionError::Retry(signature)),
        Err(IdentityGenericCallError::Relation(error)) => {
            Err(SourceCallResolutionError::Relation(error))
        }
        Err(
            IdentityGenericCallError::Unsupported(_)
            | IdentityGenericCallError::Inference(_)
            | IdentityGenericCallError::Instantiation(_),
        ) => Err(SourceCallResolutionError::Unsupported),
        Err(IdentityGenericCallError::Invariant(_)) => Err(SourceCallResolutionError::Invariant),
    }
}

/// Reuses ordinary source-call inference for a JSX component's spread props.
#[allow(clippy::too_many_arguments)] // JSX retains its opening-node signature and source context.
pub(super) fn resolve_jsx_generic_component_signature(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    opening: NodeRef,
    component: TypeId,
    attributes: TypeId,
) -> Result<SignatureId, SourceCheckError> {
    let existing = store
        .signature_links(opening)
        .and_then(|links| links.resolved_signature.signature());
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut retried_signatures = HashSet::new();
    let arguments = [attributes];
    let resolution = loop {
        match resolve_source_call_once(
            store,
            host,
            global_types,
            options,
            existing,
            &mut session,
            SourceCallResolutionRequest {
                form: DirectCallForm::Call,
                callee_type: component,
                argument_types: &arguments,
                explicit_type_arguments: None,
            },
        ) {
            Ok(resolution) => break resolution,
            Err(SourceCallResolutionError::Retry(signature))
                if retried_signatures.insert(signature) =>
            {
                resolve_signature_return(
                    store,
                    host,
                    global_types,
                    options,
                    &mut session,
                    diagnostics,
                    signature,
                )?;
            }
            Err(SourceCallResolutionError::Relation(error)) => return Err(error.into()),
            Err(
                SourceCallResolutionError::Retry(_)
                | SourceCallResolutionError::Unsupported
                | SourceCallResolutionError::Invariant,
            ) => {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        node: opening,
                        kind: SyntaxKind::JsxOpeningElement,
                        role: super::SourceSyntaxRole::VariableInitializer,
                    },
                ));
            }
        }
    };

    match resolution {
        ResolvedSourceCall::Legacy(resolution)
        | ResolvedSourceCall::NongenericTypeArguments(resolution) => Ok(resolution.signature),
        ResolvedSourceCall::Identity(resolution) => {
            demand_identity_generic_call_return_with_session(store, &resolution, &mut session)
                .map_err(|_| SourceCheckError::Call(opening))?;
            Ok(resolution.projection.signature)
        }
        ResolvedSourceCall::Vector(resolution) => {
            if !matches!(
                resolution.applicability(),
                GenericCallVectorApplicability::Applicable
                    | GenericCallVectorApplicability::ArgumentNotAssignable { .. }
            ) {
                return Err(SourceCheckError::Call(opening));
            }
            let materialized = materialize_generic_call_vector_source(store, &resolution, existing)
                .map_err(|_| SourceCheckError::Call(opening))?;
            demand_generic_call_vector_return_with_session(store, &resolution, &mut session)
                .map_err(|_| SourceCheckError::Call(opening))?;
            Ok(materialized.call_signature)
        }
    }
}

fn source_identity_fallback_is_exact(
    store: &CanonicalTypeMapperStore,
    explicit_type_arguments: Option<&[TypeId]>,
    argument_types: &[TypeId],
    error: &GenericCallVectorError,
) -> bool {
    let [argument] = argument_types else {
        return false;
    };
    explicit_type_arguments.is_none()
        && matches!(
            error,
            GenericCallVectorError::Inference(NakedTypeCandidateError::Candidate(
                NakedTypeInferenceError::UnsupportedCandidate(candidate),
            )) if candidate == argument
        )
        && source_declared_inference_candidate_is_exported(store, *argument)
}

#[allow(clippy::too_many_arguments)]
fn resolve_explicit_source_type_arguments(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    type_arguments: Option<&[NodeRef]>,
) -> Result<Option<Vec<TypeId>>, SourceCheckError> {
    let Some(type_arguments) = type_arguments else {
        return Ok(None);
    };
    if type_arguments.is_empty() {
        return Ok(None);
    }
    let mut type_argument_diagnostics = CanonicalCheckerDiagnostics::default();
    let result = (|| {
        let mut query = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_argument_diagnostics,
        )?;
        type_arguments
            .iter()
            .map(|type_argument| query.get_type_from_type_node(*type_argument))
            .collect::<Result<Vec<_>, _>>()
    })();
    merge_retry_diagnostics(diagnostics, type_argument_diagnostics);
    Ok(Some(result?))
}

pub(super) fn emit_call_type_argument_grammar_diagnostics(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
) -> Result<(), SourceCheckError> {
    let Some(type_arguments) = &plan.type_arguments else {
        return Ok(());
    };
    if let Some(range) = type_arguments.trailing_comma_range {
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(CanonicalCheckerDiagnosticRange::new(plan.node, range)),
                diagnostic: Diagnostic::new(
                    message_by_code(1009).ok_or(SourceCheckError::MissingDiagnostic(1009))?,
                ),
                related_information: Vec::new(),
            },
        );
        return Ok(());
    }
    if type_arguments.nodes.is_empty() {
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(CanonicalCheckerDiagnosticRange::new(
                    plan.node,
                    type_arguments.syntax_range,
                )),
                diagnostic: Diagnostic::new(
                    message_by_code(1099).ok_or(SourceCheckError::MissingDiagnostic(1099))?,
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok(())
}

fn extra_argument_diagnostic_range(
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallPlan,
    first_extra: usize,
) -> Result<CanonicalCheckerDiagnosticRange, SourceCheckError> {
    let first = plan
        .arguments
        .get(first_extra)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let last = plan
        .arguments
        .last()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let first_range = host
        .node(first.node)
        .ok_or(SourceCheckError::Call(plan.node))?
        .range;
    let last_range = host
        .node(last.node)
        .ok_or(SourceCheckError::Call(plan.node))?
        .range;
    Ok(CanonicalCheckerDiagnosticRange::new(
        plan.node,
        TextRange::new(first_range.start, last_range.end),
    ))
}

fn arrow_argument_diagnostic_range(
    host: &DeclaredTypeHost<'_>,
    argument: &PlannedExpression,
) -> Result<Option<CanonicalCheckerDiagnosticRange>, SourceCheckError> {
    let argument = argument.unparenthesized();
    if !matches!(argument.kind, PlannedExpressionKind::Arrow(_)) {
        return Ok(None);
    }

    let record = host
        .node(argument.node)
        .ok_or(SourceCheckError::Call(argument.node))?;
    let arrow = match (&record.data, record.kind) {
        (NodeData::ArrowFunction(arrow), SyntaxKind::ArrowFunction) => arrow,
        (NodeData::FunctionExpression(_), SyntaxKind::FunctionExpression) => return Ok(None),
        _ => return Err(SourceCheckError::Call(argument.node)),
    };
    let body = NodeRef::new(argument.node.arena, argument.node.file, arrow.body);
    let body = host
        .node(body)
        .ok_or(SourceCheckError::Call(argument.node))?;
    if body.kind != SyntaxKind::Block {
        return Ok(None);
    }

    let token = NodeRef::new(
        argument.node.arena,
        argument.node.file,
        arrow.equals_greater_than_token,
    );
    let token = host
        .node(token)
        .ok_or(SourceCheckError::Call(argument.node))?;
    let Some(source) = host
        .source(argument.node)
        .and_then(|(arena, _)| arena.source_text())
    else {
        return Ok(None);
    };
    let start = usize::try_from(token.range.end.get())
        .map_err(|_| SourceCheckError::Call(argument.node))?;
    let end =
        usize::try_from(body.range.end.get()).map_err(|_| SourceCheckError::Call(argument.node))?;
    let text = source
        .get(start..end)
        .ok_or(SourceCheckError::Call(argument.node))?;
    let Some(line_break) = text.find(['\n', '\r', '\u{2028}', '\u{2029}']) else {
        return Ok(None);
    };
    let end = start
        .checked_add(line_break)
        .and_then(|end| u32::try_from(end).ok())
        .map(TextPos::new)
        .ok_or(SourceCheckError::Call(argument.node))?;

    Ok(Some(CanonicalCheckerDiagnosticRange::new(
        argument.node,
        TextRange::new(record.range.start, end),
    )))
}

fn missing_argument_related_information(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    call: NodeRef,
    signature: SignatureId,
    actual: usize,
) -> Result<CanonicalCheckerRelatedInformation, SourceCheckError> {
    let parameter = *store
        .signature(signature)
        .and_then(|signature| signature.parameters().get(actual))
        .ok_or(SourceCheckError::Call(call))?;
    let symbol = store
        .symbol(parameter)
        .ok_or(SourceCheckError::Call(call))?;
    let declaration = *symbol
        .declarations()
        .and_then(|declarations| declarations.first())
        .ok_or(SourceCheckError::Call(call))?;
    if host.node(declaration).is_none() {
        return Err(SourceCheckError::Call(call));
    }
    let name = symbol
        .name()
        .as_utf8()
        .ok_or(SourceCheckError::Call(call))?
        .to_owned();
    Ok(CanonicalCheckerRelatedInformation {
        node: Some(declaration),
        diagnostic: Diagnostic::with_arguments(
            message_by_code(6210).ok_or(SourceCheckError::MissingDiagnostic(6210))?,
            [name],
        ),
    })
}

fn source_call_display_flags(options: CanonicalCheckerOptions) -> CanonicalTypeFormatFlags {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    flags
}

fn expected_count_text(minimum: usize, maximum: usize) -> String {
    if minimum == maximum {
        minimum.to_string()
    } else {
        format!("{minimum}-{maximum}")
    }
}

fn exact_optional_argument_mismatch(
    store: &CanonicalTypeMapperStore,
    options: CanonicalCheckerOptions,
    source: TypeId,
    target: TypeId,
) -> bool {
    if !options.intrinsic.exact_optional_property_types {
        return false;
    }
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return false;
    };
    let Some(source_members) = store
        .type_payload(source)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.members)
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    let Some(target_properties) = store
        .type_payload(target)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.properties.as_deref())
    else {
        return false;
    };
    target_properties.iter().any(|property| {
        let Some(target_property) = store.symbol(*property) else {
            return false;
        };
        if !target_property.flags().contains(SymbolFlags::OPTIONAL) {
            return false;
        }
        let Some(source_property) = source_members.get(target_property.name()) else {
            return false;
        };
        let Some(source_type) = store
            .value_symbol_links(source_property)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        let Some(target_type) = store
            .value_symbol_links(*property)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        type_contains_undefined(store, source_type, undefined)
            && !type_contains_undefined(store, target_type, undefined)
    })
}

fn type_contains_undefined(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    undefined: TypeId,
) -> bool {
    type_ == undefined
        || store.type_payload(type_).is_some_and(|record| {
            matches!(record.data(), TypeData::Union(union) if union.union.types.contains(&undefined))
        })
}

fn array_argument_diagnostics(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    argument: &PlannedExpression,
    parameter_type: TypeId,
) -> Result<Option<Vec<CanonicalCheckerDiagnostic>>, SourceCheckError> {
    let mut diagnostics = Vec::new();
    if collect_array_argument_diagnostics(
        store,
        host,
        global_types,
        options,
        argument,
        parameter_type,
        &mut diagnostics,
    )? && !diagnostics.is_empty()
    {
        Ok(Some(diagnostics))
    } else {
        Ok(None)
    }
}

fn collect_array_argument_diagnostics(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    argument: &PlannedExpression,
    parameter_type: TypeId,
    diagnostics: &mut Vec<CanonicalCheckerDiagnostic>,
) -> Result<bool, SourceCheckError> {
    let argument = argument.unparenthesized();
    let PlannedExpressionKind::Array(elements) = &argument.kind else {
        return Ok(false);
    };
    let Some(argument_type) = store
        .type_node_links(argument.node)
        .and_then(|links| links.resolved_type)
    else {
        return Err(SourceCheckError::Call(argument.node));
    };
    if store
        .canonical_array_reference(global_types, argument_type)?
        .is_none()
    {
        return Ok(false);
    }
    let Some(target_element_type) =
        store.canonical_array_element_type(global_types, parameter_type)?
    else {
        return Ok(false);
    };

    for element in elements {
        let Some(element_type) = store
            .type_node_links(element.node)
            .and_then(|links| links.resolved_type)
        else {
            return Err(SourceCheckError::Call(element.node));
        };
        if store.is_type_assignable_to_with_global_types_and_strict_function_types(
            element_type,
            target_element_type,
            global_types,
            options.strict_function_types,
        )? {
            continue;
        }
        let previous_count = diagnostics.len();
        if collect_array_argument_diagnostics(
            store,
            host,
            global_types,
            options,
            element,
            target_element_type,
            diagnostics,
        )? && diagnostics.len() != previous_count
        {
            continue;
        }
        let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            element_type,
            target_element_type,
            source_call_display_flags(options),
        )?;
        diagnostics.push(CanonicalCheckerDiagnostic {
            node: Some(element.unparenthesized().node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2322).ok_or(SourceCheckError::MissingDiagnostic(2322))?,
                [display.source, display.target],
            ),
            related_information: Vec::new(),
        });
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn prepare_source_argument_mismatch_diagnostics(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    argument: &PlannedExpression,
    argument_type: TypeId,
    parameter_type: TypeId,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    if let Some(diagnostics) =
        array_argument_diagnostics(store, host, global_types, options, argument, parameter_type)?
    {
        return Ok(diagnostics);
    }

    let flags = source_call_display_flags(options);
    let exact_optional_mismatch =
        exact_optional_argument_mismatch(store, options, argument_type, parameter_type);
    if !exact_optional_mismatch
        && matches!(
            argument.unparenthesized().kind,
            PlannedExpressionKind::Object { .. }
        )
        && matches!(
            super::object_members::validate_resolved_declared_property_type_graph(
                store,
                parameter_type,
            ),
            super::object_members::DeclaredPropertyTypeGraphValidation::Traversable(_)
        )
        && let Some(diagnostic) = excess_object_argument_diagnostic(
            store,
            host,
            global_types,
            argument,
            argument_type,
            parameter_type,
            flags,
        )?
    {
        return Ok(vec![diagnostic]);
    }

    for type_ in [argument_type, parameter_type] {
        let StoredCallableSetValidation::Valid { projection, .. } =
            validate_stored_callable_set(store, type_)
        else {
            continue;
        };
        let [callable] = projection.call_signatures.as_ref() else {
            continue;
        };
        if projection.construct_signatures.is_empty() && callable.return_type.is_none() {
            resolve_signature_return(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                callable.signature,
            )?;
        }
    }

    let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
        store,
        host,
        global_types,
        argument_type,
        parameter_type,
        flags,
    )?;
    let code = if exact_optional_mismatch { 2379 } else { 2345 };
    let details = if exact_optional_mismatch {
        exact_optional_property_mismatch_details(
            store,
            host,
            global_types,
            argument_type,
            parameter_type,
            flags,
        )?
    } else {
        let details = callable_assignability_details(
            store,
            host,
            global_types,
            argument_type,
            parameter_type,
            flags,
            options,
        )?;
        if details.is_empty() {
            missing_mapped_index_signature_details(store, argument_type, parameter_type)?
        } else {
            details
        }
    };

    Ok(vec![CanonicalCheckerDiagnostic {
        node: Some(argument.unparenthesized().node),
        range_override: arrow_argument_diagnostic_range(host, argument)?,
        diagnostic: Diagnostic::with_arguments(
            message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?,
            [display.source, display.target],
        )
        .with_details(details),
        related_information: Vec::new(),
    }])
}

#[allow(clippy::too_many_arguments)]
fn prepare_legacy_source_call_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    argument_types: &[TypeId],
    resolution: ResolvedLegacySourceCall,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let implicit_arguments = usize::from(plan.form == DirectCallForm::TaggedTemplate);
    let diagnostic = match resolution.applicability {
        DirectCallApplicability::Applicable => return Ok(Vec::new()),
        DirectCallApplicability::TooFewArguments {
            expected_at_least,
            actual,
        } => {
            if expected_at_least != resolution.minimum_argument_count
                || actual != plan.arguments.len() + implicit_arguments
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            if expected_at_least == 1
                && actual == 0
                && !resolution.has_effective_rest
                && promise_executor_missing_argument_is_exact(
                    store,
                    host,
                    plan.node,
                    plan.callee_diagnostic_node,
                    resolution.signature,
                )
            {
                return Ok(vec![CanonicalCheckerDiagnostic {
                    node: Some(plan.callee_diagnostic_node),
                    range_override: None,
                    diagnostic: Diagnostic::new(
                        message_by_code(2810).ok_or(SourceCheckError::MissingDiagnostic(2810))?,
                    ),
                    related_information: Vec::new(),
                }]);
            }
            let (message, expected) = if resolution.has_effective_rest {
                (
                    message_by_code(2555).ok_or(SourceCheckError::MissingDiagnostic(2555))?,
                    resolution.minimum_argument_count.to_string(),
                )
            } else {
                (
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    expected_count_text(
                        resolution.minimum_argument_count,
                        resolution.maximum_argument_count,
                    ),
                )
            };
            CanonicalCheckerDiagnostic {
                node: Some(plan.callee_diagnostic_node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(message, [expected, actual.to_string()]),
                related_information: vec![missing_argument_related_information(
                    store,
                    host,
                    plan.node,
                    resolution.signature,
                    actual,
                )?],
            }
        }
        DirectCallApplicability::TooManyArguments {
            expected_at_most,
            actual,
        } => {
            if resolution.has_effective_rest
                || expected_at_most != resolution.maximum_argument_count
                || actual != plan.arguments.len() + implicit_arguments
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(extra_argument_diagnostic_range(
                    host,
                    plan,
                    expected_at_most
                        .checked_sub(implicit_arguments)
                        .ok_or(SourceCheckError::Call(plan.node))?,
                )?),
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    [
                        expected_count_text(
                            resolution.minimum_argument_count,
                            resolution.maximum_argument_count,
                        ),
                        actual.to_string(),
                    ],
                ),
                related_information: Vec::new(),
            }
        }
        DirectCallApplicability::ArgumentNotAssignable {
            index,
            argument_type,
            parameter_type,
        } => {
            if argument_types.get(index).copied() != Some(argument_type) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let argument = plan
                .arguments
                .get(
                    index
                        .checked_sub(implicit_arguments)
                        .ok_or(SourceCheckError::Call(plan.node))?,
                )
                .ok_or(SourceCheckError::Call(plan.node))?;
            return prepare_source_argument_mismatch_diagnostics(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                argument,
                argument_type,
                parameter_type,
            );
        }
    };
    Ok(vec![diagnostic])
}

fn prepare_source_type_argument_arity_diagnostic(
    plan: &SourceCallPlan,
    explicit_type_arguments: &[TypeId],
    minimum: usize,
    maximum: usize,
) -> Result<CanonicalCheckerDiagnostic, SourceCheckError> {
    let syntax = plan
        .type_arguments
        .as_ref()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let actual = explicit_type_arguments.len();
    if actual == 0
        || actual != syntax.nodes.len()
        || minimum > maximum
        || (minimum..=maximum).contains(&actual)
    {
        return Err(SourceCheckError::Call(plan.node));
    }
    let range = syntax
        .diagnostic_range
        .ok_or(SourceCheckError::Call(plan.node))?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(plan.node),
        range_override: Some(CanonicalCheckerDiagnosticRange::new(plan.node, range)),
        diagnostic: Diagnostic::with_arguments(
            message_by_code(2558).ok_or(SourceCheckError::MissingDiagnostic(2558))?,
            [expected_count_text(minimum, maximum), actual.to_string()],
        ),
        related_information: Vec::new(),
    })
}

#[allow(clippy::too_many_arguments)]
fn prepare_vector_source_call_diagnostic(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
    resolution: &GenericCallVectorResolution,
) -> Result<Vec<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let projection = resolution.projection();
    let (parameter_count, minimum_argument_count, has_effective_rest) = store
        .signature(projection.generic_signature)
        .and_then(|signature| {
            usize::try_from(signature.min_argument_count())
                .ok()
                .map(|minimum| {
                    (
                        signature.parameters().len(),
                        minimum,
                        signature.has_rest_parameter(),
                    )
                })
        })
        .ok_or(SourceCheckError::Call(plan.node))?;
    let diagnostic = match resolution.applicability() {
        GenericCallVectorApplicability::Applicable => return Ok(Vec::new()),
        GenericCallVectorApplicability::TypeArgumentArity {
            minimum,
            maximum,
            actual,
        } => {
            let resolved = explicit_type_arguments.ok_or(SourceCheckError::Call(plan.node))?;
            if actual != resolved.len() || maximum != projection.type_parameters.len() {
                return Err(SourceCheckError::Call(plan.node));
            }
            prepare_source_type_argument_arity_diagnostic(plan, resolved, minimum, maximum)?
        }
        GenericCallVectorApplicability::TooFewArguments { expected, actual } => {
            if expected != minimum_argument_count
                || actual != plan.arguments.len()
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            if expected == 1
                && actual == 0
                && !has_effective_rest
                && promise_executor_missing_argument_is_exact(
                    store,
                    host,
                    plan.node,
                    plan.callee_diagnostic_node,
                    projection.generic_signature,
                )
            {
                return Ok(vec![CanonicalCheckerDiagnostic {
                    node: Some(plan.callee_diagnostic_node),
                    range_override: None,
                    diagnostic: Diagnostic::new(
                        message_by_code(2810).ok_or(SourceCheckError::MissingDiagnostic(2810))?,
                    ),
                    related_information: Vec::new(),
                }]);
            }
            let (message, expected) = if has_effective_rest {
                (
                    message_by_code(2555).ok_or(SourceCheckError::MissingDiagnostic(2555))?,
                    minimum_argument_count.to_string(),
                )
            } else {
                (
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    expected_count_text(minimum_argument_count, parameter_count),
                )
            };
            CanonicalCheckerDiagnostic {
                node: Some(plan.callee_diagnostic_node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(message, [expected, actual.to_string()]),
                related_information: vec![missing_argument_related_information(
                    store,
                    host,
                    plan.node,
                    projection.generic_signature,
                    actual,
                )?],
            }
        }
        GenericCallVectorApplicability::TooManyArguments { expected, actual } => {
            if has_effective_rest
                || expected != parameter_count
                || actual != plan.arguments.len()
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(extra_argument_diagnostic_range(host, plan, expected)?),
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    [
                        expected_count_text(minimum_argument_count, parameter_count),
                        actual.to_string(),
                    ],
                ),
                related_information: Vec::new(),
            }
        }
        GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
            index,
            type_argument,
            constraint,
        } => {
            let syntax = plan
                .type_arguments
                .as_ref()
                .ok_or(SourceCheckError::Call(plan.node))?;
            let resolved = explicit_type_arguments.ok_or(SourceCheckError::Call(plan.node))?;
            let node = *syntax
                .nodes
                .get(index)
                .ok_or(SourceCheckError::Call(plan.node))?;
            if resolved.get(index).copied() != Some(type_argument) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                type_argument,
                constraint,
                source_call_display_flags(options),
            )?;
            CanonicalCheckerDiagnostic {
                node: Some(node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2344).ok_or(SourceCheckError::MissingDiagnostic(2344))?,
                    [display.source, display.target],
                ),
                related_information: Vec::new(),
            }
        }
        GenericCallVectorApplicability::ArgumentNotAssignable {
            index,
            argument_type,
            parameter_type,
        } => {
            if argument_types.get(index).copied() != Some(argument_type) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let argument = plan
                .arguments
                .get(index)
                .ok_or(SourceCheckError::Call(plan.node))?;
            return prepare_source_argument_mismatch_diagnostics(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                argument,
                argument_type,
                parameter_type,
            );
        }
    };
    Ok(vec![diagnostic])
}

fn preflight_call_publication(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    return_type: TypeId,
) -> Result<Option<SignatureId>, SourceCheckError> {
    preflight_call_links(store, node)?;
    let existing_type = store
        .type_node_links(node)
        .and_then(|links| links.resolved_type);
    if existing_type.is_some_and(|existing| existing != return_type) {
        return Err(SourceCheckError::Call(node));
    }
    Ok(store
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature()))
}

fn missing_semicolon_related_information(
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallPlan,
) -> Result<Option<CanonicalCheckerRelatedInformation>, SourceCheckError> {
    if plan.form != DirectCallForm::Call || plan.arguments.len() != 1 {
        return Ok(None);
    }

    let (arena, _) = host
        .source(plan.node)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let Some(source) = arena.source_text() else {
        return Ok(None);
    };
    let callee = host
        .node(plan.callee.node)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let call = host
        .node(plan.node)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let NodeData::CallExpression(call) = &call.data else {
        return Err(SourceCheckError::Call(plan.node));
    };
    let start =
        usize::try_from(callee.range.end.get()).map_err(|_| SourceCheckError::Call(plan.node))?;
    let end = usize::try_from(call.arguments.range.start.get())
        .map_err(|_| SourceCheckError::Call(plan.node))?;
    let trivia = source
        .get(start..end)
        .ok_or(SourceCheckError::Call(plan.node))?;
    if !call_trivia_has_line_break(trivia).ok_or(SourceCheckError::Call(plan.node))? {
        return Ok(None);
    }

    Ok(Some(CanonicalCheckerRelatedInformation {
        node: Some(plan.callee.node),
        diagnostic: Diagnostic::new(
            message_by_code(2734).ok_or(SourceCheckError::MissingDiagnostic(2734))?,
        ),
    }))
}

fn call_trivia_has_line_break(text: &str) -> Option<bool> {
    let mut offset = 0usize;
    while let Some(remaining) = text.get(offset..) {
        if remaining.is_empty() {
            return Some(false);
        }
        if matches!(remaining.as_bytes().first(), Some(b'\r' | b'\n')) {
            return Some(true);
        }
        if remaining.starts_with("//") {
            let Some(line_break) = remaining.find(['\r', '\n']) else {
                return Some(false);
            };
            offset = offset.checked_add(line_break)?;
            continue;
        }
        if remaining.starts_with("/*") {
            let comment_end = remaining.find("*/")?.checked_add(2)?;
            offset = offset.checked_add(comment_end)?;
            continue;
        }
        let character = remaining.chars().next()?;
        if character.is_whitespace() || matches!(character, '\u{200b}' | '\u{feff}') {
            offset = offset.checked_add(character.len_utf8())?;
            continue;
        }
        return Some(false);
    }
    None
}

fn recover_non_callable_source_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    callee_type: TypeId,
) -> Result<CheckedSourceCall, SourceCheckError> {
    let flags = store
        .type_payload(callee_type)
        .map(super::type_records::TypeRecord::flags)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let error_type = bootstrap.error_type;
    let (return_type, signature, report_diagnostic) = if flags.intersects(TypeFlags::ANY) {
        if callee_type == error_type {
            (error_type, bootstrap.unknown_signature, false)
        } else {
            (bootstrap.any_type, bootstrap.any_signature, false)
        }
    } else {
        (error_type, bootstrap.unknown_signature, true)
    };
    let existing = preflight_call_publication(store, plan.node, return_type)?;
    if existing.is_some_and(|existing| existing != signature) {
        return Err(SourceCheckError::Call(plan.node));
    }
    let diagnostic = if report_diagnostic {
        let namespace_import = match &plan.callee.unparenthesized().kind {
            PlannedExpressionKind::Identifier(read)
                if read.kind == PlannedIdentifierReadKind::Import =>
            {
                synthetic_source_import_origin(store, read.value_symbol, callee_type)
            }
            _ => None,
        };
        let apparent_type = if flags.intersects(TypeFlags::NUMBER_LIKE) {
            "Number".to_owned()
        } else if flags.intersects(TypeFlags::STRING_LIKE) {
            "String".to_owned()
        } else if flags.intersects(TypeFlags::BOOLEAN_LIKE) {
            "Boolean".to_owned()
        } else if flags.intersects(TypeFlags::BIG_INT_LIKE) {
            "BigInt".to_owned()
        } else if flags.intersects(TypeFlags::ES_SYMBOL | TypeFlags::UNIQUE_ES_SYMBOL) {
            "Symbol".to_owned()
        } else if namespace_import.is_some() {
            "{ default: () => void; }".to_owned()
        } else {
            type_to_string_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                callee_type,
                source_call_display_flags(options),
            )?
        };
        let detail = Diagnostic::with_arguments(
            message_by_code(2757).ok_or(SourceCheckError::MissingDiagnostic(2757))?,
            [apparent_type],
        )
        .render()
        .expect("TS2757 has one formatting argument");
        let mut related_information = missing_semicolon_related_information(host, plan)?
            .into_iter()
            .collect::<Vec<_>>();
        if let Some(import) = namespace_import {
            related_information.push(CanonicalCheckerRelatedInformation {
                node: Some(import),
                diagnostic: Diagnostic::new(
                    message_by_code(7038).ok_or(SourceCheckError::MissingDiagnostic(7038))?,
                ),
            });
        }
        Some(CanonicalCheckerDiagnostic {
            node: Some(plan.callee_diagnostic_node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(2349).ok_or(SourceCheckError::MissingDiagnostic(2349))?,
            )
            .with_details([format!("  {detail}")]),
            related_information,
        })
    } else if return_type != error_type
        && plan
            .type_arguments
            .as_ref()
            .is_some_and(|arguments| !arguments.nodes.is_empty())
    {
        Some(CanonicalCheckerDiagnostic {
            node: Some(plan.node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(2347).ok_or(SourceCheckError::MissingDiagnostic(2347))?,
            ),
            related_information: Vec::new(),
        })
    } else {
        None
    };
    publish_call_links(store, plan.node, signature, return_type)?;
    if let Some(diagnostic) = diagnostic {
        merge_retry_diagnostic(diagnostics, diagnostic);
    }
    Ok(CheckedSourceCall { return_type })
}

fn tagged_template_argument_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
) -> Result<TypeId, SourceCheckError> {
    let unsupported = || SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node));
    let symbol = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("TemplateStringsArray"))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .filter(|symbol| {
            store
                .symbol(*symbol)
                .is_some_and(|record| record.flags().contains(SymbolFlags::INTERFACE))
        })
        .ok_or_else(unsupported)?;
    let type_ = if let Some(type_) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    {
        type_
    } else {
        let record = store.symbol(symbol).ok_or_else(unsupported)?;
        let Some([declaration]) = record.declarations() else {
            return Err(unsupported());
        };
        let declaration = *declaration;
        let (_, bound) = host.source(declaration).ok_or_else(unsupported)?;
        let declaration_record = host.node(declaration).ok_or_else(unsupported)?;
        let NodeData::InterfaceDeclaration(interface) = &declaration_record.data else {
            return Err(unsupported());
        };
        let name = NodeRef::new(declaration.arena, declaration.file, interface.name);
        let name_record = host.node(name).ok_or_else(unsupported)?;
        if record.flags() != SymbolFlags::INTERFACE
            || record.parent().is_some()
            || record.value_declaration().is_some()
            || record.export_symbol().is_some()
            || bound
                .source_facts()
                .is_none_or(|facts| !facts.is_default_library() || !facts.is_declaration_file())
            || bound
                .symbol(declaration)
                .and_then(|owner| store.get_merged_symbol(owner))
                != Some(symbol)
            || declaration_record.kind != SyntaxKind::InterfaceDeclaration
            || declaration_record.parent != Some(bound.source_file().node)
            || interface.type_parameters.is_some()
            || name_record.parent != Some(declaration.node)
            || !matches!(
                &name_record.data,
                NodeData::Identifier(identifier)
                    if identifier.text == "TemplateStringsArray"
            )
        {
            return Err(unsupported());
        }
        let mut template_diagnostics = CanonicalCheckerDiagnostics::default();
        let result = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut template_diagnostics,
        )
        .and_then(|mut query| query.get_declared_type_of_symbol(symbol));
        merge_retry_diagnostics(diagnostics, template_diagnostics);
        result?
    };
    let record = store.type_payload(type_).ok_or_else(unsupported)?;
    if !matches!(record.data(), TypeData::Interface(_))
        || record
            .symbol()
            .and_then(|owner| store.get_merged_symbol(owner))
            != Some(symbol)
    {
        return Err(unsupported());
    }
    Ok(type_)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_types: &[TypeId],
) -> Result<CheckedSourceCall, SourceCheckError> {
    preflight_call_links(store, plan.node)?;
    if argument_types.len() != plan.arguments.len() {
        return Err(SourceCheckError::Call(plan.node));
    }
    if let Some(checked) = check_authenticated_array_find_index_call(
        store,
        global_types,
        plan,
        callee_type,
        argument_types,
    )? {
        return Ok(checked);
    }
    let callee_type =
        specialize_readonly_array_concat_callee(store, global_types, plan, callee_type)?;
    if let Some(checked) = check_authenticated_array_callback_call(
        store,
        global_types,
        plan,
        callee_type,
        argument_types,
    )? {
        return Ok(checked);
    }
    let tagged_argument_types = if plan.form == DirectCallForm::TaggedTemplate {
        let template = tagged_template_argument_type(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            plan.node,
        )?;
        let mut arguments = Vec::with_capacity(argument_types.len() + 1);
        arguments.push(template);
        arguments.extend_from_slice(argument_types);
        Some(arguments)
    } else {
        None
    };
    let argument_types = tagged_argument_types.as_deref().unwrap_or(argument_types);
    let existing_call_signature = store
        .signature_links(plan.node)
        .and_then(|links| links.resolved_signature.signature());
    let limit_mark = session.limit_event_mark();
    let explicit_type_arguments = resolve_explicit_source_type_arguments(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        plan.type_arguments
            .as_ref()
            .map(|type_arguments| type_arguments.nodes.as_slice()),
    )?;
    if let Some(type_arguments) = explicit_type_arguments.as_deref()
        && let Some(checked) = check_authenticated_generic_object_factory_call(
            store,
            host,
            global_types,
            options,
            session,
            diagnostics,
            plan,
            callee_type,
            argument_types,
            type_arguments,
        )?
    {
        return Ok(checked);
    }
    let mut retried_signatures = HashSet::new();
    let mut retried_members = HashSet::new();
    let mut retried_properties = HashSet::new();
    let mut relation_candidates = Vec::new();
    let resolution = loop {
        match resolve_source_call_once(
            store,
            host,
            global_types,
            options,
            existing_call_signature,
            session,
            SourceCallResolutionRequest {
                form: plan.form,
                callee_type,
                argument_types,
                explicit_type_arguments: explicit_type_arguments.as_deref(),
            },
        ) {
            Ok(resolution) => break resolution,
            Err(SourceCallResolutionError::Retry(signature))
                if retried_signatures.insert(signature) =>
            {
                resolve_signature_return(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    signature,
                )?;
            }
            Err(SourceCallResolutionError::Relation(
                error @ (RelationUnavailable::UnresolvedStructuredMembers(_)
                | RelationUnavailable::UnresolvedPropertyType(_)),
            )) => {
                if relation_candidates.is_empty() {
                    relation_candidates.extend_from_slice(argument_types);
                }
                if let RelationUnavailable::UnresolvedStructuredMembers(type_) = error
                    && !relation_candidates.contains(&type_)
                {
                    relation_candidates.push(type_);
                }
                retry_source_generic_member_failure(
                    store,
                    global_types,
                    session,
                    error,
                    &relation_candidates,
                    &mut retried_members,
                    &mut retried_properties,
                )?;
            }
            Err(SourceCallResolutionError::Relation(error)) => return Err(error.into()),
            Err(SourceCallResolutionError::Unsupported)
                if matches!(
                    validate_stored_callable_set(store, callee_type),
                    StoredCallableSetValidation::NotCallable
                ) =>
            {
                return recover_non_callable_source_call(
                    store,
                    host,
                    global_types,
                    options,
                    diagnostics,
                    plan,
                    callee_type,
                );
            }
            Err(SourceCallResolutionError::Unsupported) if plan.type_arguments.is_some() => {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(plan.node),
                ));
            }
            Err(
                SourceCallResolutionError::Retry(_)
                | SourceCallResolutionError::Unsupported
                | SourceCallResolutionError::Invariant,
            ) => {
                return Err(SourceCheckError::Call(plan.node));
            }
        }
    };

    let (signature, return_type, call_diagnostics) = match resolution {
        ResolvedSourceCall::Legacy(resolution) => {
            let existing = preflight_call_publication(store, plan.node, resolution.return_type)?;
            if existing.is_some_and(|existing| existing != resolution.signature) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let diagnostic = prepare_legacy_source_call_diagnostic(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                plan,
                argument_types,
                resolution,
            )?;
            (resolution.signature, resolution.return_type, diagnostic)
        }
        ResolvedSourceCall::NongenericTypeArguments(resolution) => {
            let existing = preflight_call_publication(store, plan.node, resolution.return_type)?;
            if existing.is_some_and(|existing| existing != resolution.signature) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let explicit = explicit_type_arguments
                .as_deref()
                .ok_or(SourceCheckError::Call(plan.node))?;
            let diagnostic = prepare_source_type_argument_arity_diagnostic(plan, explicit, 0, 0)?;
            (
                resolution.signature,
                resolution.return_type,
                vec![diagnostic],
            )
        }
        ResolvedSourceCall::Vector(resolution) => {
            let diagnostic = prepare_vector_source_call_diagnostic(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                plan,
                argument_types,
                explicit_type_arguments.as_deref(),
                &resolution,
            )?;
            let materialized =
                materialize_generic_call_vector_source(store, &resolution, existing_call_signature)
                    .map_err(|error| match error {
                        GenericCallVectorError::Relation(error)
                        | GenericCallVectorError::Inference(NakedTypeCandidateError::Relation(
                            error,
                        )) => SourceCheckError::from(error),
                        GenericCallVectorError::Unsupported(_)
                        | GenericCallVectorError::Invariant(_)
                        | GenericCallVectorError::Inference(_)
                        | GenericCallVectorError::Instantiation(_) => {
                            SourceCheckError::Call(plan.node)
                        }
                    })?;
            let return_type =
                demand_generic_call_vector_return_with_session(store, &resolution, session)
                    .map_err(|error| match error {
                        GenericCallVectorError::Relation(error)
                        | GenericCallVectorError::Inference(NakedTypeCandidateError::Relation(
                            error,
                        )) => SourceCheckError::from(error),
                        GenericCallVectorError::Unsupported(_)
                        | GenericCallVectorError::Invariant(_)
                        | GenericCallVectorError::Inference(_)
                        | GenericCallVectorError::Instantiation(_) => {
                            SourceCheckError::Call(plan.node)
                        }
                    })?;
            if preflight_call_publication(store, plan.node, return_type)? != existing_call_signature
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            (materialized.call_signature, return_type, diagnostic)
        }
        ResolvedSourceCall::Identity(resolution) => {
            let return_type =
                demand_identity_generic_call_return_with_session(store, &resolution, session)
                    .map_err(|error| match error {
                        IdentityGenericCallError::Relation(error) => SourceCheckError::from(error),
                        IdentityGenericCallError::Unsupported(_)
                        | IdentityGenericCallError::Invariant(_)
                        | IdentityGenericCallError::Inference(_)
                        | IdentityGenericCallError::Instantiation(_) => {
                            SourceCheckError::Call(plan.node)
                        }
                    })?;
            if preflight_call_publication(store, plan.node, return_type)? != existing_call_signature
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            let legacy = ResolvedLegacySourceCall {
                signature: resolution.projection.signature,
                return_type,
                minimum_argument_count: 1,
                maximum_argument_count: 1,
                has_effective_rest: false,
                applicability: resolution.applicability,
            };
            let diagnostic = prepare_legacy_source_call_diagnostic(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
                plan,
                argument_types,
                legacy,
            )?;
            (resolution.projection.signature, return_type, diagnostic)
        }
    };
    publish_call_links(store, plan.node, signature, return_type)?;
    for diagnostic in call_diagnostics {
        merge_retry_diagnostic(diagnostics, diagnostic);
    }
    if session.limit_event_occurred_since(limit_mark) {
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: None,
                diagnostic: Diagnostic::new(
                    message_by_code(2589).ok_or(SourceCheckError::MissingDiagnostic(2589))?,
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok(CheckedSourceCall { return_type })
}

#[allow(clippy::too_many_arguments)]
fn resolve_signature_return(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    signature: super::SignatureId,
) -> Result<(), SourceCheckError> {
    let mut resolution_diagnostics = CanonicalCheckerDiagnostics::default();
    let result = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        global_types,
        options,
        session,
        &mut resolution_diagnostics,
    )?
    .get_return_type_of_signature(signature);
    merge_retry_diagnostics(diagnostics, resolution_diagnostics);
    result?;
    Ok(())
}

fn publish_call_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    signature: super::SignatureId,
    return_type: TypeId,
) -> Result<(), SourceCheckError> {
    let expected_type = TypeNodeLinks {
        resolved_type: Some(return_type),
        ..TypeNodeLinks::default()
    };
    let expected_signature = SignatureLinks {
        resolved_signature: ResolvedSignatureState::Resolved(signature),
        ..SignatureLinks::default()
    };
    let type_links = store.type_node_links(node);
    let signature_links = store.signature_links(node);
    let exact = type_links == Some(&expected_type) && signature_links == Some(&expected_signature);
    if exact {
        return Ok(());
    }
    let type_is_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    let signature_is_cold = signature_links.is_none_or(|links| links == &SignatureLinks::default());
    if !type_is_cold || !signature_is_cold {
        return Err(SourceCheckError::Call(node));
    }
    if !store.set_signature_links(node, expected_signature)
        || !store.set_type_node_links(node, expected_type)
    {
        return Err(SourceCheckError::Call(node));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, IntrinsicBootstrapOptions, SourceFileLinks,
        bootstrap::UnionReduction,
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
        },
        object_members::{
            DeclaredPropertyTypeGraphValidation, validate_resolved_declared_property_type_graph,
        },
        reference_types::validate_direct_generic_reference,
        source::{PlannedIdentifierRead, PlannedIdentifierReadKind},
        type_records::{LiteralValue, TypeData},
    };

    fn parsed(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        context_with_options(parsed, file, CanonicalCheckerOptions::default())
    }

    fn context_with_options(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
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
            options,
        )
        .unwrap()
    }

    fn context_with_default_library<'arena>(
        library: &'arena ParseResult,
        library_file: FileId,
        source: &'arena ParseResult,
        source_file: FileId,
    ) -> CanonicalCheckerContext<'arena> {
        let files = [(library_file, library), (source_file, source)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            let is_default_library = file == library_file;
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        is_default_library,
                        is_default_library,
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
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn array_callback_default_library() -> ParseResult {
        parsed(concat!(
            "interface Array<T> { ",
            "map<U>(callbackfn: ",
            "(value: T, index: number, array: T[]) => U, thisArg?: any): U[]; ",
            "filter<S extends T>(predicate: ",
            "(value: T, index: number, array: T[]) => value is S, thisArg?: any): S[]; ",
            "filter(predicate: ",
            "(value: T, index: number, array: T[]) => unknown, thisArg?: any): T[]; ",
            "untouched(value: T): void; ",
            "} interface ReadonlyArray<T> { ",
            "map<U>(callbackfn: ",
            "(value: T, index: number, array: readonly T[]) => U, ",
            "thisArg?: any): U[]; ",
            "filter<S extends T>(predicate: ",
            "(value: T, index: number, array: readonly T[]) => value is S, ",
            "thisArg?: any): S[]; ",
            "filter(predicate: ",
            "(value: T, index: number, array: readonly T[]) => unknown, ",
            "thisArg?: any): T[]; ",
            "} interface Array<T> { ",
            "find<S extends T>(predicate: ",
            "(value: T, index: number, array: T[]) => value is S, ",
            "thisArg?: any): S | undefined; ",
            "find(predicate: ",
            "(value: T, index: number, array: T[]) => unknown, ",
            "thisArg?: any): T | undefined; ",
            "} interface ReadonlyArray<T> { ",
            "find<S extends T>(predicate: ",
            "(value: T, index: number, array: readonly T[]) => value is S, ",
            "thisArg?: any): S | undefined; ",
            "find(predicate: ",
            "(value: T, index: number, array: readonly T[]) => unknown, ",
            "thisArg?: any): T | undefined; ",
            "}",
        ))
    }

    fn imported_context<'arena>(
        importer: &'arena ParseResult,
        importer_file: FileId,
        target: &'arena ParseResult,
        target_file: FileId,
    ) -> CanonicalCheckerContext<'arena> {
        imported_context_with_target_facts(
            importer,
            importer_file,
            target,
            target_file,
            false,
            CanonicalModuleResolutionMode::Esm,
            CanonicalCheckerOptions::default(),
        )
    }

    fn imported_context_with_target_facts<'arena>(
        importer: &'arena ParseResult,
        importer_file: FileId,
        target: &'arena ParseResult,
        target_file: FileId,
        declaration_target: bool,
        resolution_mode: CanonicalModuleResolutionMode,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        let files = [(importer_file, importer), (target_file, target)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        declaration_target && file == target_file,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut module_specifiers = importer
            .arena
            .iter()
            .filter_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some((
                    record.range.start,
                    NodeRef::new(importer.arena.id(), importer_file, import.module_specifier),
                )),
                _ => None,
            })
            .collect::<Vec<_>>();
        module_specifiers.sort_by_key(|(start, _)| *start);
        assert!(
            !module_specifiers.is_empty(),
            "fixture contains an import declaration"
        );
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            options,
            CanonicalModuleResolutionManifestInput::new(module_specifiers.into_iter().map(
                |(_, module_specifier)| {
                    CanonicalModuleResolutionEntry::resolved(
                        module_specifier,
                        CanonicalResolvedModuleInput::new(
                            target_file,
                            resolution_mode,
                            resolution_mode,
                        ),
                    )
                },
            )),
        )
        .unwrap()
    }

    fn calls(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallExpression)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect()
    }

    fn property_accesses(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::PropertyAccessExpression)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect()
    }

    fn property_name(parsed: &ParseResult, file: FileId, access: NodeRef) -> NodeRef {
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            panic!("expected a property access")
        };
        NodeRef::new(parsed.arena.id(), file, property.name)
    }

    fn first_function_symbol(
        parsed: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("fixture must contain a function declaration");
        let (_, bound) = context.file(file).unwrap();
        bound.symbol(declaration).unwrap()
    }

    fn identifier_plan(node: NodeRef, symbol: SemanticSymbolId) -> PlannedExpression {
        PlannedExpression::new(
            node,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
                kind: PlannedIdentifierReadKind::Function,
            }),
        )
    }

    fn string_argument_plans(syntax: &DirectSourceCallSyntax) -> Vec<PlannedExpression> {
        syntax
            .arguments()
            .iter()
            .enumerate()
            .map(|(index, node)| {
                PlannedExpression::new(
                    *node,
                    PlannedExpressionKind::String(format!("argument{index}")),
                )
            })
            .collect()
    }

    #[derive(Debug, Eq, PartialEq)]
    struct CallPublicationState {
        type_count: usize,
        mapper_count: usize,
        signature_count: usize,
        cached_signature_count: usize,
        type_links: Option<TypeNodeLinks>,
        signature_links: Option<SignatureLinks>,
        diagnostics: Vec<CanonicalCheckerDiagnostic>,
    }

    fn call_publication_state(
        context: &CanonicalCheckerContext<'_>,
        call: NodeRef,
    ) -> CallPublicationState {
        CallPublicationState {
            type_count: context.store().type_len(),
            mapper_count: context.store().mapper_len(),
            signature_count: context.store().signature_len(),
            cached_signature_count: context.store().cached_signature_len(),
            type_links: context.store().type_node_links(call).cloned(),
            signature_links: context.store().signature_links(call).cloned(),
            diagnostics: context.diagnostics().as_slice().to_vec(),
        }
    }

    fn mark_source_unchecked(context: &mut CanonicalCheckerContext<'_>, file: FileId) {
        let source = context.source_file(file).unwrap();
        let mut links = context
            .store()
            .source_file_links(source)
            .cloned()
            .unwrap_or_else(SourceFileLinks::default);
        links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source, links)
        );
    }

    #[test]
    fn tagged_template_plans_keep_nested_substitutions_and_invalid_escapes() {
        let parsed = parsed(concat!(
            "declare function tag(template: TemplateStringsArray, ...values: any[]): string; ",
            r"const value = tag`ok ${tag`\u`} tail ${tag`\x`}`;",
        ));
        let file = FileId::new(491);
        let context = context(&parsed, file);
        let mut tags = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::TaggedTemplateExpression)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect::<Vec<_>>();
        tags.sort_by_key(|tag| parsed.arena.get(tag.node).unwrap().range.start);
        let [outer, first_inner, second_inner] = tags.as_slice() else {
            panic!("expected one outer and two inner tagged templates")
        };

        let outer_syntax =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *outer).unwrap();
        assert_eq!(outer_syntax.form, DirectCallForm::TaggedTemplate);
        assert_eq!(outer_syntax.arguments(), &[*first_inner, *second_inner]);

        let symbol = first_function_symbol(&parsed, &context, file);
        let arguments = [*first_inner, *second_inner]
            .into_iter()
            .map(|node| {
                let syntax =
                    plan_direct_source_call_syntax(&parsed.arena, context.store(), node).unwrap();
                assert!(syntax.arguments().is_empty());
                let plan = finish_direct_source_call_plan(
                    &syntax,
                    identifier_plan(syntax.callee(), symbol),
                    Vec::new(),
                )
                .unwrap();
                PlannedExpression::new(node, PlannedExpressionKind::Call(Box::new(plan)))
            })
            .collect::<Vec<_>>();
        let plan = finish_direct_source_call_plan(
            &outer_syntax,
            identifier_plan(outer_syntax.callee(), symbol),
            arguments,
        )
        .unwrap();
        assert_eq!(plan.form, DirectCallForm::TaggedTemplate);
        assert_eq!(plan.arguments.len(), 2);
    }

    #[test]
    fn private_property_tagged_templates_preserve_tag_and_private_substitution() {
        let parsed = parsed(concat!(
            "class Model { #tag = null as any; #value = 1; ",
            "run() { this.#tag`value ${this.#value}`; } }",
        ));
        let file = FileId::new(496);
        let context = context(&parsed, file);
        let tagged = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TaggedTemplateExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), tagged)
            .expect("a private property tag retains the existing tagged-call capability");

        assert_eq!(syntax.form, DirectCallForm::TaggedTemplate);
        assert_eq!(
            syntax.callee_form(),
            SourceCallCalleeForm::RequiredOwnProperty
        );
        let name = parsed
            .arena
            .get(syntax.callee_diagnostic_node().node)
            .unwrap();
        assert!(matches!(
            &name.data,
            NodeData::PrivateIdentifier(identifier) if identifier.text == "#tag"
        ));
        let [argument] = syntax.arguments() else {
            panic!("the private template retains exactly one private substitution")
        };
        let NodeData::PropertyAccessExpression(access) =
            &parsed.arena.get(argument.node).unwrap().data
        else {
            panic!("the substitution remains a private property access")
        };
        assert!(matches!(
            &parsed.arena.get(access.name).unwrap().data,
            NodeData::PrivateIdentifier(identifier) if identifier.text == "#value"
        ));
    }

    #[test]
    fn ordinary_private_method_calls_retain_the_private_name_diagnostic_node() {
        let parsed = parsed("class Model { #run() {} call() { this.#run(); } }");
        let file = FileId::new(497);
        let context = context(&parsed, file);
        let call = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
            .expect("a private method call retains its authenticated property callee");

        assert_eq!(
            syntax.callee_form(),
            SourceCallCalleeForm::RequiredOwnProperty
        );
        assert!(matches!(
            &parsed
                .arena
                .get(syntax.callee_diagnostic_node().node)
                .unwrap()
                .data,
            NodeData::PrivateIdentifier(identifier) if identifier.text == "#run"
        ));
    }

    #[test]
    fn tagged_template_substitution_plans_keep_the_substitution_node() {
        let text = concat!(
            "declare function tag(template: TemplateStringsArray, value: number): string; ",
            "const result: string = tag`value ${'wrong'}`;",
        );
        let source = parsed(text);
        let source_file = FileId::new(493);
        let context = context(&source, source_file);
        let wrong_start = text.find("'wrong'").unwrap();
        let wrong = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::StringLiteral
                    && record.range.start == TextPos::new(u32::try_from(wrong_start).unwrap()))
                .then(|| NodeRef::new(source.arena.id(), source_file, node))
            })
            .unwrap();
        let tag = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TaggedTemplateExpression)
                    .then(|| NodeRef::new(source.arena.id(), source_file, node))
            })
            .unwrap();
        let syntax = plan_direct_source_call_syntax(&source.arena, context.store(), tag).unwrap();
        assert_eq!(syntax.arguments(), &[wrong]);

        let symbol = first_function_symbol(&source, &context, source_file);
        let plan = finish_direct_source_call_plan(
            &syntax,
            identifier_plan(syntax.callee(), symbol),
            vec![PlannedExpression::new(
                wrong,
                PlannedExpressionKind::String("wrong".to_owned()),
            )],
        )
        .unwrap();
        assert_eq!(plan.arguments[0].unparenthesized().node, wrong);
    }

    #[test]
    fn rest_only_tagged_templates_initialize_the_global_template_type_once() {
        let library = parsed(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface TemplateStringsArray {}",
        ));
        let source = parsed(concat!(
            "declare function tag(...values: any[]): string; ",
            "const plain: string = tag`plain`; ",
            "const substitution: string = tag`value ${1}`;",
        ));
        let library_file = FileId::new(494);
        let source_file = FileId::new(495);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let symbol = context
            .store()
            .intrinsic_bootstrap()
            .and_then(|bootstrap| context.store().symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("TemplateStringsArray"))
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .expect("the default library must own TemplateStringsArray");
        assert!(context.store().declared_type_links(symbol).is_none());

        context.check_source_file(source_file).unwrap();

        assert!(context.diagnostics().is_empty());
        let template = context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .expect("the first tagged call must initialize the global interface");
        let TypeData::Interface(interface) = context.store().type_payload(template).unwrap().data()
        else {
            panic!("TemplateStringsArray must retain its declared interface identity")
        };
        assert!(!interface.declared_members_resolved);

        let tags = source
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::TaggedTemplateExpression)
            .map(|(node, _)| NodeRef::new(source.arena.id(), source_file, node))
            .collect::<Vec<_>>();
        assert_eq!(tags.len(), 2);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        for tag in &tags {
            assert_eq!(
                context
                    .store()
                    .type_node_links(*tag)
                    .and_then(|links| links.resolved_type),
                Some(string)
            );
            assert!(
                context
                    .store()
                    .signature_links(*tag)
                    .and_then(|links| links.resolved_signature.signature())
                    .is_some()
            );
        }

        let cold = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().declared_type_links(symbol).cloned(),
            tags.iter()
                .map(|tag| call_publication_state(&context, *tag))
                .collect::<Vec<_>>(),
        );
        mark_source_unchecked(&mut context, source_file);
        context.check_source_file(source_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().declared_type_links(symbol).cloned(),
                tags.iter()
                    .map(|tag| call_publication_state(&context, *tag))
                    .collect::<Vec<_>>(),
            ),
            cold,
        );
    }

    #[test]
    fn call_plan_retains_go_style_type_argument_list_interior() {
        let text = concat!(
            "function pair<T, U>(left: T, right: U): U { return right; } ",
            "const spaced = pair< string, number >(\"left\", 1); ",
            "const empty = pair<>(\"left\", 1); ",
            "const trailing = pair< string, number ,   >(\"left\", 1);",
        );
        let parsed = parsed(text);
        let file = FileId::new(435);
        let context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [spaced, empty, trailing] = call_nodes.as_slice() else {
            panic!("expected spaced, empty, and trailing-comma generic calls")
        };

        let spaced = plan_direct_source_call_syntax(&parsed.arena, context.store(), *spaced)
            .unwrap()
            .type_arguments
            .unwrap();
        let spaced_start = text.find("string, number").unwrap();
        let spaced_end = spaced_start + "string, number".len();
        assert_eq!(spaced.nodes.len(), 2);
        assert_eq!(spaced.trailing_comma_range, None);
        let spaced_syntax_start = text.find("< string, number >").unwrap();
        let spaced_syntax_end = spaced_syntax_start + "< string, number >".len();
        assert_eq!(
            spaced.syntax_range,
            TextRange::new(
                TextPos::new(u32::try_from(spaced_syntax_start).unwrap()),
                TextPos::new(u32::try_from(spaced_syntax_end).unwrap()),
            )
        );
        assert_eq!(
            spaced.diagnostic_range,
            Some(TextRange::new(
                TextPos::new(u32::try_from(spaced_start).unwrap()),
                TextPos::new(u32::try_from(spaced_end).unwrap()),
            ))
        );

        let empty = plan_direct_source_call_syntax(&parsed.arena, context.store(), *empty)
            .unwrap()
            .type_arguments
            .unwrap();
        assert!(empty.nodes.is_empty());
        assert_eq!(empty.trailing_comma_range, None);
        let empty_syntax_start = text.find("<>").unwrap();
        assert_eq!(
            empty.syntax_range,
            TextRange::new(
                TextPos::new(u32::try_from(empty_syntax_start).unwrap()),
                TextPos::new(u32::try_from(empty_syntax_start + 2).unwrap()),
            )
        );
        assert_eq!(empty.diagnostic_range, None);

        let trailing = plan_direct_source_call_syntax(&parsed.arena, context.store(), *trailing)
            .unwrap()
            .type_arguments
            .unwrap();
        let trailing_start = text.rfind("string, number ,").unwrap();
        let trailing_end = trailing_start + "string, number ,".len();
        assert_eq!(trailing.nodes.len(), 2);
        assert_eq!(
            trailing.trailing_comma_range,
            Some(TextRange::new(
                TextPos::new(u32::try_from(trailing_end - 1).unwrap()),
                TextPos::new(u32::try_from(trailing_end).unwrap()),
            ))
        );
        assert_eq!(
            trailing.diagnostic_range,
            Some(TextRange::new(
                TextPos::new(u32::try_from(trailing_start).unwrap()),
                TextPos::new(u32::try_from(trailing_end).unwrap()),
            ))
        );
    }

    #[test]
    fn immediate_async_arrow_calls_require_exact_parenthesized_zero_argument_syntax() {
        let accepted = parsed("function run() { (async () => {})(); }");
        let file = FileId::new(496);
        let accepted_context = context(&accepted, file);
        let accepted_calls = calls(&accepted, file);
        let [call] = accepted_calls.as_slice() else {
            panic!("expected one immediately invoked async arrow")
        };
        let syntax =
            plan_direct_source_call_syntax(&accepted.arena, accepted_context.store(), *call)
                .expect("an authenticated async arrow IIFE must retain its callee");
        assert_eq!(
            syntax.callee_form(),
            SourceCallCalleeForm::ParenthesizedAsyncArrow
        );
        assert!(syntax.arguments().is_empty());

        let synchronous = parsed("function run() { (() => {})(); }");
        let file = FileId::new(497);
        let synchronous_context = context(&synchronous, file);
        let synchronous_calls = calls(&synchronous, file);
        let [call] = synchronous_calls.as_slice() else {
            panic!("expected one immediately invoked synchronous arrow")
        };
        let syntax =
            plan_direct_source_call_syntax(&synchronous.arena, synchronous_context.store(), *call)
                .expect("an authenticated synchronous arrow IIFE must retain its callee");
        assert_eq!(syntax.callee_form(), SourceCallCalleeForm::Identifier);
        assert!(syntax.arguments().is_empty());

        for (index, source) in [
            "function run() { (async () => {})(1); }",
            "function run() { (async (value: number) => {})(1); }",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(498 + u32::try_from(index).unwrap());
            let context = context(&parsed, file);
            let rejected_calls = calls(&parsed, file);
            let [call] = rejected_calls.as_slice() else {
                panic!("expected one rejected immediate call: {source}")
            };
            assert!(
                matches!(
                    plan_direct_source_call_syntax(&parsed.arena, context.store(), *call),
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(_)
                    ))
                ),
                "{source}",
            );
        }
    }

    #[test]
    fn call_plan_accepts_authenticated_arrow_arguments_without_publication() {
        let parsed = parsed(concat!(
            "function take(value: any): void {} ",
            "take(() => 127); ",
            "take((() => 1)); ",
            "take((value: number): number => value);",
        ));
        let file = FileId::new(457);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let context = context(&parsed, file);

        for call in call_nodes {
            let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
                .expect("well-formed arrow arguments must pass call syntax validation");
            assert_eq!(syntax.arguments().len(), 1);
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
        }
    }

    #[test]
    fn call_plan_accepts_authenticated_anonymous_function_arguments_without_publication() {
        let parsed = parsed(concat!(
            "function take(value: any): void {} ",
            "take(function () { return 127; }); ",
            "take((function () { return 1; }));",
        ));
        let file = FileId::new(500);
        let context = context(&parsed, file);

        for call in calls(&parsed, file) {
            let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
                .expect("anonymous function arguments must pass call syntax validation");
            let [argument] = syntax.arguments() else {
                panic!("expected one anonymous function argument")
            };
            let function = match &parsed.arena.get(argument.node).unwrap().data {
                NodeData::FunctionExpression(_) => *argument,
                NodeData::ParenthesizedExpression(parenthesized) => {
                    NodeRef::new(argument.arena, argument.file, parenthesized.expression)
                }
                _ => panic!("expected a direct or parenthesized anonymous function"),
            };
            assert_eq!(syntax.argument_arrow_nodes, vec![Some(function)]);
            assert_eq!(syntax.array_argument_arrow_nodes, vec![vec![function]]);
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
        }
    }

    #[test]
    fn anonymous_function_argument_validation_rejects_unsupported_shapes() {
        for (index, source) in [
            "function take(value: any): void {} take(function named() { return 1; });",
            "function take(value: any): void {} take(function (value: number) { return value; });",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(501 + u32::try_from(index).unwrap());
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one rejected anonymous function argument")
            };
            let store = CanonicalTypeMapperStore::new();

            assert!(matches!(
                plan_direct_source_call_syntax(&parsed.arena, &store, *call),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == *call
            ));
            assert!(store.type_node_links(*call).is_none());
            assert!(store.signature_links(*call).is_none());
        }

        let mut parsed = parsed(concat!(
            "function take(value: any): void {} ",
            "take(function () { return 1; });",
        ));
        let file = FileId::new(503);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one anonymous function argument")
        };
        let function = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionExpression).then_some(node)
            })
            .expect("fixture must contain an anonymous function argument");
        let NodeData::FunctionExpression(function) = &parsed.arena.get(function).unwrap().data
        else {
            unreachable!("the selected node is a function expression")
        };
        parsed.arena.get_mut(function.body).unwrap().parent = Some(call.node);
        let store = CanonicalTypeMapperStore::new();

        assert!(matches!(
            plan_direct_source_call_syntax(&parsed.arena, &store, *call),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                if node == *call
        ));
        assert!(store.type_node_links(*call).is_none());
        assert!(store.signature_links(*call).is_none());
    }

    #[test]
    fn anonymous_function_arguments_preserve_type_mismatch_diagnostics() {
        let parsed = parsed(concat!(
            "declare function take(value: number): void; ",
            "take(function () { return 1; });",
        ));
        let file = FileId::new(504);
        let mut context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one anonymous function argument")
        };

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one function argument type mismatch")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(
            diagnostic
                .node
                .and_then(|node| parsed.arena.get(node.node))
                .map(|record| record.kind),
            Some(SyntaxKind::FunctionExpression),
        );

        let cold = call_publication_state(&context, *call);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(call_publication_state(&context, *call), cold);
    }

    #[test]
    fn array_sort_call_authenticates_two_tuple_binding_callback_parameters() {
        let parsed = parsed(concat!(
            "declare const values: [string, any][]; ",
            "values.sort(([firstKey, firstValue], [secondKey, secondValue]) ",
            "=> firstValue.name.localeCompare(secondValue.name));",
        ));
        let file = FileId::new(4_960);
        let context = context(&parsed, file);
        let sort = calls(&parsed, file)
            .into_iter()
            .find(|call| {
                let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data
                else {
                    return false;
                };
                let NodeData::PropertyAccessExpression(property) =
                    &parsed.arena.get(call.expression).unwrap().data
                else {
                    return false;
                };
                matches!(
                    &parsed.arena.get(property.name).unwrap().data,
                    NodeData::Identifier(name) if name.text == "sort"
                )
            })
            .unwrap();

        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), sort).unwrap();

        assert_eq!(syntax.arguments().len(), 1);
        assert!(context.store().type_node_links(sort).is_none());
        assert!(context.store().signature_links(sort).is_none());
    }

    #[test]
    fn tuple_binding_callbacks_stay_exclusive_to_authenticated_array_sort_calls() {
        for (index, source) in [
            "consume(([first, second], [third, fourth]) => first);",
            "values.map(([first, second], [third, fourth]) => first);",
            "values.sort(([first = 0, second], [third, fourth]) => first);",
            "values.sort(({ first, second }, [third, fourth]) => first);",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(source);
            let file = FileId::new(4_961 + u32::try_from(index).unwrap());
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("the fixture retains one callback call")
            };
            let store = CanonicalTypeMapperStore::new();

            assert!(matches!(
                plan_direct_source_call_syntax(&parsed.arena, &store, *call),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == *call
            ));
            assert!(store.type_node_links(*call).is_none());
            assert!(store.signature_links(*call).is_none());
        }
    }

    #[test]
    fn property_calls_keep_actual_callees_after_call_receivers() {
        let parsed = parsed(concat!(
            "declare function makeNumber(): number; ",
            "declare function makeString(): string; ",
            "const fixed = makeNumber().toFixed(); ",
            "const lower = makeString().toLowerCase(); ",
            "const ordinary = makeString().toString();",
        ));
        let file = FileId::new(465);
        let context = context(&parsed, file);
        let property_calls = calls(&parsed, file)
            .into_iter()
            .filter_map(|call| {
                let NodeData::CallExpression(data) = &parsed.arena.get(call.node)?.data else {
                    return None;
                };
                let property = parsed.arena.get(data.expression)?;
                let NodeData::PropertyAccessExpression(access) = &property.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                    return None;
                };
                Some((call, data.expression, name.text.as_str()))
            })
            .collect::<Vec<_>>();
        assert_eq!(property_calls.len(), 3);

        for (call, property, name) in property_calls {
            let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
                .unwrap_or_else(|error| panic!("property {name} must retain its callee: {error}"));
            assert_eq!(
                syntax.callee_form(),
                SourceCallCalleeForm::RequiredOwnProperty
            );
            assert_eq!(syntax.callee().node, property);
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
        }
    }

    #[test]
    fn authenticated_own_property_calls_accept_call_receivers_cold_and_warm() {
        let parsed = parsed(concat!(
            "type API = { run: () => string }; ",
            "declare function create(): API; ",
            "const result: string = create().run();",
        ));
        let file = FileId::new(471);
        let mut context = context(&parsed, file);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| {
            let range = parsed.arena.get(call.node).unwrap().range;
            (range.start, range.end)
        });
        let [inner, outer] = call_nodes.as_slice() else {
            panic!("fixture must contain one receiver call and one member call")
        };
        let access_nodes = property_accesses(&parsed, file);
        let [access] = access_nodes.as_slice() else {
            panic!("fixture must contain one member access")
        };

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert_eq!(
            context
                .store()
                .type_node_links(*outer)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().string_type)
        );
        assert!(
            context
                .store()
                .symbol_node_links(*access)
                .is_some_and(|links| links.resolved_symbol.is_some())
        );
        let cold = [*inner, *outer].map(|call| call_publication_state(&context, call));

        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            [*inner, *outer].map(|call| call_publication_state(&context, call)),
            cold,
        );
    }

    #[test]
    fn optional_property_calls_on_call_receivers_preserve_exact_arity() {
        let parsed = parsed(concat!(
            "type API = { run: (digits?: number) => string }; ",
            "declare function create(): API; ",
            "const omitted: string = create().run(); ",
            "const supplied: string = create().run(2); ",
            "const extra = create().run(1, 2);",
        ));
        let file = FileId::new(472);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("only the extra optional argument must produce a diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2554);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Expected 0-1 arguments, but got 2."
        );
        let calls = calls(&parsed, file);
        assert_eq!(calls.len(), 6);
        let cold = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();

        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn call_plan_authenticates_arrows_nested_in_array_arguments() {
        let parsed = parsed(concat!(
            "function take(values: any): void {} ",
            "take([() => 1, [((value: number) => value)]]);",
        ));
        let file = FileId::new(466);
        let context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("fixture must contain one call with nested array arrows")
        };
        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), *call)
            .expect("nested array arrows must pass call syntax validation");
        let mut expected = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::ArrowFunction)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect::<Vec<_>>();
        expected.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);

        assert_eq!(syntax.argument_arrow_nodes, vec![None]);
        assert_eq!(syntax.array_argument_arrow_nodes, vec![expected]);
        assert!(context.store().type_node_links(*call).is_none());
        assert!(context.store().signature_links(*call).is_none());
    }

    #[test]
    fn array_arrow_argument_validation_rejects_forged_arrow_and_array_ownership() {
        for poison in 0..3 {
            let mut parsed = parsed("function take(values: any): void {} take([() => 1]);");
            let file = FileId::new(467 + poison);
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("fixture must contain one direct call")
            };
            let call = *call;
            let (array, arrow, body) = {
                let NodeData::CallExpression(call_data) =
                    &parsed.arena.get(call.node).unwrap().data
                else {
                    unreachable!("the selected node is a call")
                };
                let [array] = call_data.arguments.nodes.as_slice() else {
                    panic!("fixture must contain one array argument")
                };
                let NodeData::ArrayLiteralExpression(array_data) =
                    &parsed.arena.get(*array).unwrap().data
                else {
                    unreachable!("the argument is an array")
                };
                let [arrow] = array_data.elements.nodes.as_slice() else {
                    panic!("fixture must contain one arrow element")
                };
                let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(*arrow).unwrap().data
                else {
                    unreachable!("the selected element is an arrow")
                };
                (*array, *arrow, arrow_data.body)
            };
            match poison {
                0 => {
                    let NodeData::ArrowFunction(arrow_data) =
                        &mut parsed.arena.get_mut(arrow).unwrap().data
                    else {
                        unreachable!("the selected element is an arrow")
                    };
                    arrow_data.facts = 1;
                }
                1 => parsed.arena.get_mut(body).unwrap().parent = Some(array),
                2 => parsed.arena.get_mut(arrow).unwrap().parent = Some(call.node),
                _ => unreachable!("only authenticated arrow fields and ownership are mutated"),
            }

            let store = CanonicalTypeMapperStore::new();
            assert!(matches!(
                plan_direct_source_call_syntax(&parsed.arena, &store, call),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == call
            ));
            assert!(store.type_node_links(call).is_none());
            assert!(store.signature_links(call).is_none());
        }
    }

    #[test]
    fn finished_call_plan_rejects_scalar_plans_for_nested_array_arrows() {
        let parsed = parsed("function take(values: any): void {} take([() => 1]);");
        let file = FileId::new(470);
        let context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("fixture must contain one direct call")
        };
        let call = *call;
        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
            .expect("the fixture contains an authenticated nested arrow");
        let [array] = syntax.arguments() else {
            panic!("the fixture call has one array argument")
        };
        let [arrow] = syntax.array_argument_arrow_nodes[0].as_slice() else {
            panic!("the array argument contains one authenticated arrow")
        };
        let forged = PlannedExpression::new(
            *array,
            PlannedExpressionKind::Array(vec![PlannedExpression::new(
                *arrow,
                PlannedExpressionKind::String("forged".into()),
            )]),
        );
        let symbol = first_function_symbol(&parsed, &context, file);

        assert!(matches!(
            finish_direct_source_call_plan(
                &syntax,
                identifier_plan(syntax.callee(), symbol),
                vec![forged],
            ),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                if node == call
        ));
        assert!(context.store().type_node_links(call).is_none());
        assert!(context.store().signature_links(call).is_none());
    }

    #[test]
    fn arrow_argument_validation_rejects_forged_facts_tokens_and_body_ownership() {
        for poison in 0..3 {
            let mut parsed = parsed("function take(value: any): void {} take(() => 127);");
            let file = FileId::new(458 + poison);
            let arrow = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .expect("fixture must contain one arrow argument");
            let (body, token) = {
                let NodeData::ArrowFunction(arrow) = &parsed.arena.get(arrow.node).unwrap().data
                else {
                    unreachable!("the selected node is an arrow")
                };
                (arrow.body, arrow.equals_greater_than_token)
            };
            match poison {
                0 => {
                    let NodeData::ArrowFunction(arrow) =
                        &mut parsed.arena.get_mut(arrow.node).unwrap().data
                    else {
                        unreachable!("the selected node is an arrow")
                    };
                    arrow.facts = 1;
                }
                1 => {
                    let NodeData::ArrowFunction(arrow) =
                        &mut parsed.arena.get_mut(arrow.node).unwrap().data
                    else {
                        unreachable!("the selected node is an arrow")
                    };
                    arrow.equals_greater_than_token = body;
                }
                2 => parsed.arena.get_mut(body).unwrap().parent = Some(token),
                _ => unreachable!("only the three authenticated arrow fields are mutated"),
            }

            assert!(!is_supported_arrow_argument_syntax(&parsed.arena, arrow));
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("fixture must contain one direct call")
            };
            let store = CanonicalTypeMapperStore::new();
            assert!(matches!(
                plan_direct_source_call_syntax(&parsed.arena, &store, *call),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == *call
            ));
            assert!(store.type_node_links(*call).is_none());
            assert!(store.signature_links(*call).is_none());
        }
    }

    #[test]
    fn anonymous_function_argument_validation_rejects_forged_facts_names_and_body_ownership() {
        for poison in 0..3 {
            let mut parsed = parsed(concat!(
                "function take(callback: () => void): void {} ",
                "take(function () {});",
            ));
            let file = FileId::new(4_910 + poison);
            let expression = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::FunctionExpression).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .expect("fixture must contain an anonymous function argument");
            let NodeData::FunctionExpression(function) =
                &parsed.arena.get(expression.node).unwrap().data
            else {
                panic!("expected an anonymous function argument")
            };
            let body = function.body;
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("fixture must contain one direct call")
            };
            let call = *call;

            match poison {
                0 => {
                    let NodeData::FunctionExpression(function) =
                        &mut parsed.arena.get_mut(expression.node).unwrap().data
                    else {
                        unreachable!("the selected node is a function expression")
                    };
                    function.facts = 1;
                }
                1 => {
                    let NodeData::FunctionExpression(function) =
                        &mut parsed.arena.get_mut(expression.node).unwrap().data
                    else {
                        unreachable!("the selected node is a function expression")
                    };
                    function.name = Some(body);
                }
                2 => parsed.arena.get_mut(body).unwrap().parent = Some(call.node),
                _ => unreachable!("only authenticated anonymous function fields are mutated"),
            }

            assert!(!is_supported_function_expression_argument_syntax(
                &parsed.arena,
                expression,
            ));
            let store = CanonicalTypeMapperStore::new();
            assert!(matches!(
                plan_direct_source_call_syntax(&parsed.arena, &store, call),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == call
            ));
            assert!(store.type_node_links(call).is_none());
            assert!(store.signature_links(call).is_none());
        }
    }

    #[test]
    fn arrow_argument_validation_rejects_forged_parameter_and_return_annotations() {
        for poison in 0..3 {
            let mut parsed = parsed(concat!(
                "function take(value: any): void {} ",
                "take((value: number): number => value);",
            ));
            let file = FileId::new(461 + poison);
            let arrow = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .expect("fixture must contain one arrow argument");
            let (parameter, name, parameter_type, return_type) = {
                let NodeData::ArrowFunction(arrow_data) =
                    &parsed.arena.get(arrow.node).unwrap().data
                else {
                    unreachable!("the selected node is an arrow")
                };
                let [parameter] = arrow_data.parameters.nodes.as_slice() else {
                    panic!("fixture must contain one arrow parameter")
                };
                let NodeData::ParameterDeclaration(parameter_data) =
                    &parsed.arena.get(*parameter).unwrap().data
                else {
                    unreachable!("the arrow child is a parameter")
                };
                (
                    *parameter,
                    parameter_data.name,
                    parameter_data.type_.expect("parameter has an annotation"),
                    arrow_data.type_.expect("arrow has a return annotation"),
                )
            };
            match poison {
                0 => parsed.arena.get_mut(name).unwrap().parent = Some(arrow.node),
                1 => parsed.arena.get_mut(parameter_type).unwrap().parent = Some(arrow.node),
                2 => parsed.arena.get_mut(return_type).unwrap().parent = Some(parameter),
                _ => unreachable!("only the three owned arrow children are mutated"),
            }

            assert!(!is_supported_arrow_argument_syntax(&parsed.arena, arrow));
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("fixture must contain one direct call")
            };
            let store = CanonicalTypeMapperStore::new();
            assert!(matches!(
                plan_direct_source_call_syntax(&parsed.arena, &store, *call),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == *call
            ));
            assert!(store.type_node_links(*call).is_none());
            assert!(store.signature_links(*call).is_none());
        }
    }

    #[test]
    fn finished_call_plan_rejects_scalar_plans_for_authenticated_arrow_arguments() {
        let parsed = parsed(concat!(
            "function take(value: any): void {} ",
            "const direct = take(() => 1); ",
            "const wrapped = take((() => 2));",
        ));
        let file = FileId::new(464);
        let context = context(&parsed, file);
        let symbol = first_function_symbol(&parsed, &context, file);

        for call in calls(&parsed, file) {
            let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
                .expect("the fixture contains authenticated arrow arguments");
            let [argument] = syntax.arguments() else {
                panic!("the fixture calls have one argument")
            };
            let forged_argument = match &parsed.arena.get(argument.node).unwrap().data {
                NodeData::ArrowFunction(_) => PlannedExpression::new(
                    *argument,
                    PlannedExpressionKind::String("forged".into()),
                ),
                NodeData::ParenthesizedExpression(parenthesized) => {
                    let inner =
                        NodeRef::new(argument.arena, argument.file, parenthesized.expression);
                    PlannedExpression::new(
                        *argument,
                        PlannedExpressionKind::Parenthesized(Box::new(PlannedExpression::new(
                            inner,
                            PlannedExpressionKind::String("forged".into()),
                        ))),
                    )
                }
                _ => unreachable!("the fixture contains only direct and wrapped arrows"),
            };

            assert!(matches!(
                finish_direct_source_call_plan(
                    &syntax,
                    identifier_plan(syntax.callee(), symbol),
                    vec![forged_argument],
                ),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                    if node == call
            ));
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
        }
    }

    #[test]
    fn generic_call_grammar_diagnostics_use_exact_bracket_and_comma_ranges() {
        let text = concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const empty = identity<>(1 + true); ",
            "const trailing = identity< string , /* trivia */ >(\"trailing\");",
        );
        let parsed = parsed(text);
        let file = FileId::new(436);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![1099, 2365, 1009]
        );
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [empty, trailing] = call_nodes.as_slice() else {
            panic!("expected empty and trailing-comma generic calls")
        };
        let empty_start = text.find("<>").unwrap();
        assert_eq!(diagnostics[0].node, Some(*empty));
        assert_eq!(
            diagnostics[0].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                *empty,
                TextRange::new(
                    TextPos::new(u32::try_from(empty_start).unwrap()),
                    TextPos::new(u32::try_from(empty_start + 2).unwrap()),
                ),
            ))
        );
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type argument list cannot be empty."
        );
        let trailing_start = text.find(", /* trivia */").unwrap();
        assert_eq!(diagnostics[2].node, Some(*trailing));
        assert_eq!(
            diagnostics[2].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                *trailing,
                TextRange::new(
                    TextPos::new(u32::try_from(trailing_start).unwrap()),
                    TextPos::new(u32::try_from(trailing_start + 1).unwrap()),
                ),
            ))
        );
        assert_eq!(
            diagnostics[2].diagnostic.render().unwrap(),
            "Trailing comma not allowed."
        );

        let cold_diagnostics = context.diagnostics().as_slice().to_vec();
        let cold_counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().cached_signature_len(),
        );
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(context.diagnostics().as_slice(), cold_diagnostics);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
            ),
            cold_counts
        );
    }

    #[test]
    fn generic_call_recovery_replays_warm_without_source_writes() {
        let parsed = parsed(concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const bad = identity<string>(1);",
        ));
        let file = FileId::new(439);
        let mut context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one generic call")
        };

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2345]
        );
        let cold = call_publication_state(&context, *call);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(call_publication_state(&context, *call), cold);
    }

    #[test]
    fn finished_call_plan_rejects_a_same_shaped_forged_callee_without_publication() {
        let parsed = parsed(concat!(
            "function first(left: string, right: string): void {} ",
            "function second(left: string, right: string): void {} ",
            "const one = first('left', 'right'); ",
            "const two = second('other', 'tail');",
        ));
        let file = FileId::new(433);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [first_call, second_call] = call_nodes.as_slice() else {
            panic!("expected two direct calls")
        };
        let context = context(&parsed, file);
        let first_syntax =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *first_call).unwrap();
        let second_syntax =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *second_call).unwrap();
        let symbol = first_function_symbol(&parsed, &context, file);
        let arguments = string_argument_plans(&first_syntax);
        assert!(
            finish_direct_source_call_plan(
                &first_syntax,
                identifier_plan(first_syntax.callee(), symbol),
                arguments.clone(),
            )
            .is_ok()
        );
        let before = call_publication_state(&context, *first_call);

        assert!(matches!(
            finish_direct_source_call_plan(
                &first_syntax,
                identifier_plan(second_syntax.callee(), symbol),
                arguments,
            ),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                if node == *first_call
        ));

        assert_eq!(call_publication_state(&context, *first_call), before);
    }

    #[test]
    fn nested_call_callee_rejects_poisoned_cache_without_publication() {
        let parsed = parsed("declare function make(): string; const result = make()(1);");
        let file = FileId::new(489);
        let mut context = context(&parsed, file);
        let outer = calls(&parsed, file)
            .into_iter()
            .find(|call| {
                matches!(
                    parsed.arena.get(call.node).map(|record| &record.data),
                    Some(NodeData::CallExpression(call))
                        if parsed
                            .arena
                            .get(call.expression)
                            .is_some_and(|callee| callee.kind == SyntaxKind::CallExpression)
                )
            })
            .expect("fixture must contain a call-expression callee");
        let NodeData::CallExpression(call) = &parsed.arena.get(outer.node).unwrap().data else {
            unreachable!("the selected node is a call")
        };
        let inner = NodeRef::new(parsed.arena.id(), file, call.expression);
        let signature = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_signature;
        assert!(context.store_mut_for_test().set_signature_links(
            inner,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        let before = call_publication_state(&context, outer);

        assert!(matches!(
            plan_direct_source_call_syntax(&parsed.arena, context.store(), outer),
            Err(SourceCheckError::Call(node)) if node == inner
        ));
        assert_eq!(call_publication_state(&context, outer), before);
        assert!(context.store().type_node_links(inner).is_none());
    }

    #[test]
    fn finished_call_plan_rejects_swapped_same_shaped_arguments_without_publication() {
        let parsed = parsed(concat!(
            "function take(left: string, right: string): void {} ",
            "const result = take('left', 'right');",
        ));
        let file = FileId::new(434);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one direct call")
        };
        let context = context(&parsed, file);
        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), *call).unwrap();
        let symbol = first_function_symbol(&parsed, &context, file);
        let callee = identifier_plan(syntax.callee(), symbol);
        let mut arguments = string_argument_plans(&syntax);
        assert_eq!(arguments.len(), 2);
        assert!(finish_direct_source_call_plan(&syntax, callee.clone(), arguments.clone()).is_ok());
        arguments.swap(0, 1);
        let before = call_publication_state(&context, *call);

        assert!(matches!(
            finish_direct_source_call_plan(&syntax, callee, arguments),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                if node == *call
        ));

        assert_eq!(call_publication_state(&context, *call), before);
    }

    #[test]
    fn required_own_property_calls_publish_function_and_source_callables_cold_and_warm() {
        let parsed = parsed(concat!(
            "type API = { fn: (value: number) => string }; ",
            "function fromType(api: API): string { return api.fn(1); } ",
            "function render(value: number): string { return 'ok'; } ",
            "const holder = { fn: render }; ",
            "const fromSource: string = holder.fn(1);",
        ));
        let file = FileId::new(440);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let mut accesses = property_accesses(&parsed, file);
        accesses.sort_by_key(|access| parsed.arena.get(access.node).unwrap().range.start);
        assert_eq!(calls.len(), 2);
        assert_eq!(accesses.len(), 2);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        for (call, access) in calls.iter().zip(&accesses) {
            assert_eq!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type),
                Some(string)
            );
            assert!(
                context
                    .store()
                    .signature_links(*call)
                    .is_some_and(|links| links.resolved_signature.signature().is_some())
            );
            assert!(
                context
                    .store()
                    .type_node_links(*access)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(*access)
                    .is_some_and(|links| links.resolved_symbol.is_some())
            );
        }

        let cold_calls = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        let cold_properties = accesses
            .iter()
            .map(|access| {
                (
                    context.store().type_node_links(*access).cloned(),
                    context.store().symbol_node_links(*access).cloned(),
                )
            })
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold_calls
        );
        assert_eq!(
            accesses
                .iter()
                .map(|access| {
                    (
                        context.store().type_node_links(*access).cloned(),
                        context.store().symbol_node_links(*access).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            cold_properties
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source graph proves direct and member callback identity.
    fn anonymous_function_arguments_preserve_comments_callable_identity_and_warm_caches() {
        let parsed = parsed(concat!(
            "function accept(callback: () => void): void {} ",
            "accept(// direct callback\n",
            "function () {}); ",
            "type API = { run: (callback: () => number) => string }; ",
            "function use(api: API): string { return api.run(// member callback\n",
            "function () { return 1; }); }",
        ));
        let file = FileId::new(4_913);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [direct_call, member_call] = call_nodes.as_slice() else {
            panic!("expected one direct call and one member call")
        };
        let mut callbacks = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionExpression).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        callbacks.sort_by_key(|(start, _)| *start);
        let [(_, direct_callback), (_, member_callback)] = callbacks.as_slice() else {
            panic!("expected one anonymous function argument for each call")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let void = bootstrap.void_type;
        let number = bootstrap.number_type;
        let (_, bound) = context.file(file).unwrap();
        for (call, callback, expected_return) in [
            (*direct_call, *direct_callback, void),
            (*member_call, *member_callback, number),
        ] {
            let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), call)
                .expect("both anonymous callbacks must retain authenticated call syntax");
            assert_eq!(syntax.argument_arrow_nodes, vec![Some(callback)]);
            assert_eq!(syntax.array_argument_arrow_nodes, vec![vec![callback]]);
            let owner = bound
                .symbol(callback)
                .expect("anonymous callbacks must retain binder-owned symbols");
            let callable = context
                .store()
                .source_callable_type_for_owner(owner)
                .expect("anonymous callbacks must publish authenticated callable types");
            let provenance = context
                .store()
                .source_callable_provenance(callable)
                .expect("anonymous callbacks must retain source callable provenance");
            assert_eq!(provenance.declaration, callback);
            assert_eq!(provenance.owner_symbol, owner);
            assert_eq!(
                context
                    .store()
                    .signature(provenance.signature)
                    .and_then(super::super::signatures::Signature::resolved_return_type),
                Some(expected_return),
            );
            assert!(matches!(
                validate_stored_source_callable(context.store(), callable),
                StoredSourceCallableValidation::Valid(_)
            ));
            assert_eq!(
                context
                    .store()
                    .type_node_links(callback)
                    .and_then(|links| links.resolved_type),
                Some(callable),
            );
            assert!(
                context
                    .store()
                    .signature_links(call)
                    .is_some_and(|links| links.resolved_signature.signature().is_some())
            );
        }
        let cold = (
            [*direct_call, *member_call].map(|call| call_publication_state(&context, call)),
            [*direct_callback, *member_callback]
                .map(|callback| context.store().type_node_links(callback).cloned()),
        );

        context.recheck_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert_eq!(
            (
                [*direct_call, *member_call].map(|call| call_publication_state(&context, call)),
                [*direct_callback, *member_callback]
                    .map(|callback| context.store().type_node_links(callback).cloned()),
            ),
            cold
        );
    }

    #[test]
    fn anonymous_function_arguments_preserve_exact_callback_return_diagnostics() {
        let parsed = parsed(concat!(
            "function accept(callback: () => string): void {} ",
            "accept(function () { return 1; });",
        ));
        let file = FileId::new(4_914);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("fixture must contain one direct call")
        };
        let call = *call;
        let callback = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("fixture must contain one anonymous function argument");
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the callback return mismatch must produce exactly one diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.node, Some(callback));
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type '() => number' is not assignable to parameter of type '() => string'."
        );
        assert!(context.store().type_node_links(callback).is_some());
        let cold = call_publication_state(&context, call);

        context.recheck_source_file(file).unwrap();

        assert_eq!(call_publication_state(&context, call), cold);
    }

    #[test]
    fn readonly_array_concat_calls_publish_mutable_specialized_returns_cold_and_warm() {
        let library = parsed(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "} ",
            "interface ConcatArray<T> {}",
        ));
        let source = parsed(concat!(
            "declare const values: ReadonlyArray<number>; ",
            "const result: number[] = values.concat();",
        ));
        let library_file = FileId::new(4_886);
        let source_file = FileId::new(4_887);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);

        context.check_source_file(source_file).unwrap();

        assert!(context.diagnostics().is_empty());
        let call_nodes = calls(&source, source_file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one readonly Array.concat call")
        };
        let call = *call;
        let return_type = context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let array = context
            .store()
            .canonical_array_reference(context.global_types(), return_type)
            .unwrap()
            .unwrap();
        assert!(!array.readonly);
        assert_eq!(
            array.element_type,
            context.store().intrinsic_bootstrap().unwrap().number_type,
        );
        let signature = context
            .store()
            .signature_links(call)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        assert!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .target()
                .is_some()
        );
        let cold = call_publication_state(&context, call);

        mark_source_unchecked(&mut context, source_file);
        context.check_source_file(source_file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert_eq!(call_publication_state(&context, call), cold);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Verify mutable and readonly declarations plus warm identity.
    fn array_for_each_contextualizes_real_callback_parameters_cold_and_warm() {
        let library = parsed(concat!(
            "interface Array<T> { ",
            "forEach(callbackfn: (value: T, index: number, array: T[]) => void, ",
            "thisArg?: any): void; ",
            "untouched(value: T): void; ",
            "} ",
            "interface ReadonlyArray<T> { ",
            "forEach(callbackfn: (value: T, index: number, array: readonly T[]) => void, ",
            "thisArg?: any): void; ",
            "}",
        ));
        for (index, declaration) in [
            "declare const values: number[]; values.forEach(value => value * 2);",
            concat!(
                "declare const values: ReadonlyArray<number>; ",
                "values.forEach(value => value * 2);",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(declaration);
            let library_file = FileId::new(4_910 + u32::try_from(index * 2).unwrap());
            let source_file = FileId::new(4_911 + u32::try_from(index * 2).unwrap());
            let mut context =
                context_with_default_library(&library, library_file, &source, source_file);

            context.check_source_file(source_file).unwrap();

            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let call_nodes = calls(&source, source_file);
            let [call] = call_nodes.as_slice() else {
                panic!("the callback fixture must contain one forEach call")
            };
            let call = *call;
            let arrow = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                        source.arena.id(),
                        source_file,
                        node,
                    ))
                })
                .unwrap();
            let NodeData::ArrowFunction(arrow_data) = &source.arena.get(arrow.node).unwrap().data
            else {
                panic!("the callback fixture must contain its source arrow")
            };
            let parameter = NodeRef::new(arrow.arena, arrow.file, arrow_data.parameters.nodes[0]);
            let parameter = context
                .file(source_file)
                .unwrap()
                .1
                .symbol(parameter)
                .unwrap();
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let (number, void) = (bootstrap.number_type, bootstrap.void_type);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type),
                Some(number),
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type),
                Some(void),
            );
            let owner = if index == 0 {
                context.global_types().array_type
            } else {
                context.global_types().readonly_array_type
            };
            let owner = context
                .store()
                .type_payload(owner)
                .and_then(TypeRecord::symbol)
                .unwrap();
            let members = context.store().symbol(owner).unwrap().members().unwrap();
            let method = context
                .store()
                .symbol_table(members)
                .and_then(|members| members.get_source("forEach"))
                .unwrap();
            let callable = context
                .store()
                .value_symbol_links(method)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let [signature] = context
                .store()
                .type_payload(callable)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .unwrap()
            else {
                panic!("forEach must retain its binder-owned source signature")
            };
            assert_eq!(
                context
                    .store()
                    .signature(*signature)
                    .unwrap()
                    .min_argument_count(),
                1,
            );
            if index == 0 {
                let untouched = context
                    .store()
                    .symbol_table(members)
                    .and_then(|members| members.get_source("untouched"))
                    .unwrap();
                assert!(context.store().value_symbol_links(untouched).is_none());
            }
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                call_publication_state(&context, call),
            );
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    call_publication_state(&context, call),
                ),
                warm,
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Verify both owners, real overload order, and warm identity.
    fn array_find_and_filter_narrow_named_predicates_cold_and_warm() {
        let library = array_callback_default_library();
        for (index, declaration) in [
            concat!(
                "function isNumber(value: any): value is number { ",
                "return typeof value === \"number\"; } ",
                "declare const values: (string | number)[]; ",
                "const found: number | undefined = values.find(isNumber); ",
                "const filtered: number[] = values.filter(isNumber);",
            ),
            concat!(
                "function isNumber(value: any): value is number { ",
                "return typeof value === \"number\"; } ",
                "declare const values: ReadonlyArray<string | number>; ",
                "const found: number | undefined = values.find(isNumber); ",
                "const filtered: number[] = values.filter(isNumber);",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(declaration);
            let library_file = FileId::new(4_920 + u32::try_from(index * 2).unwrap());
            let source_file = FileId::new(4_921 + u32::try_from(index * 2).unwrap());
            let mut context =
                context_with_default_library(&library, library_file, &source, source_file);

            context.check_source_file(source_file).unwrap();

            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let call_nodes = calls(&source, source_file);
            let [find, filter] = call_nodes.as_slice() else {
                panic!("the predicate fixture must retain both callback calls")
            };
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let (number, undefined) = (bootstrap.number_type, bootstrap.undefined_type);
            let found = context
                .store()
                .type_node_links(*find)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert!(
                found == number
                    || matches!(
                        context.store().type_payload(found).map(TypeRecord::data),
                        Some(TypeData::Union(union))
                            if union.union.types.contains(&number)
                                && union.union.types.contains(&undefined)
                    )
            );
            let filtered = context
                .store()
                .type_node_links(*filter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let array = context
                .store()
                .canonical_array_reference(context.global_types(), filtered)
                .unwrap()
                .unwrap();
            assert_eq!(array.element_type, number);
            assert!(!array.readonly);

            let owner = if index == 0 {
                context.global_types().array_type
            } else {
                context.global_types().readonly_array_type
            };
            let owner = context
                .store()
                .type_payload(owner)
                .and_then(TypeRecord::symbol)
                .unwrap();
            let members = context.store().symbol(owner).unwrap().members().unwrap();
            for name in ["find", "filter"] {
                let method = context
                    .store()
                    .symbol_table(members)
                    .and_then(|members| members.get_source(name))
                    .unwrap();
                let callable = context
                    .store()
                    .value_symbol_links(method)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let [predicate, ordinary] = context
                    .store()
                    .type_payload(callable)
                    .and_then(|record| record.data().structured())
                    .and_then(|structured| structured.signatures.as_deref())
                    .unwrap()
                else {
                    panic!("the callback method must retain both real overloads")
                };
                assert_eq!(
                    context
                        .store()
                        .signature(*predicate)
                        .unwrap()
                        .type_parameters()
                        .len(),
                    1,
                );
                assert!(
                    context
                        .store()
                        .signature(*ordinary)
                        .unwrap()
                        .type_parameters()
                        .is_empty()
                );
            }
            if index == 0 {
                let untouched = context
                    .store()
                    .symbol_table(members)
                    .and_then(|members| members.get_source("untouched"))
                    .unwrap();
                assert!(context.store().value_symbol_links(untouched).is_none());
            }

            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().type_predicate_len(),
                call_publication_state(&context, *find),
                call_publication_state(&context, *filter),
            );
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().type_predicate_len(),
                    call_publication_state(&context, *find),
                    call_publication_state(&context, *filter),
                ),
                warm,
            );
        }
    }

    #[test]
    fn array_map_infers_callback_returns_and_filter_keeps_truthy_elements() {
        let library = array_callback_default_library();
        for (index, declaration) in [
            concat!(
                "declare const values: number[]; ",
                "const mapped = values.map(value => \"mapped\"); ",
                "const filtered = values.filter(value => value, undefined);",
            ),
            concat!(
                "declare const values: ReadonlyArray<number>; ",
                "const mapped = values.map(value => \"mapped\"); ",
                "const filtered = values.filter(value => value, undefined);",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = parsed(declaration);
            let library_file = FileId::new(4_924 + u32::try_from(index * 2).unwrap());
            let source_file = FileId::new(4_925 + u32::try_from(index * 2).unwrap());
            let mut context =
                context_with_default_library(&library, library_file, &source, source_file);

            context.check_source_file(source_file).unwrap();

            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let call_nodes = calls(&source, source_file);
            let [mapped, filtered] = call_nodes.as_slice() else {
                panic!("the callback fixture must retain map and filter")
            };
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            for (call, expected) in [
                (*mapped, bootstrap.string_type),
                (*filtered, bootstrap.number_type),
            ] {
                let result = context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type)
                    .unwrap();
                let array = context
                    .store()
                    .canonical_array_reference(context.global_types(), result)
                    .unwrap()
                    .unwrap();
                assert_eq!(array.element_type, expected);
                assert!(!array.readonly);
            }

            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                call_publication_state(&context, *mapped),
                call_publication_state(&context, *filtered),
            );
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    call_publication_state(&context, *mapped),
                    call_publication_state(&context, *filtered),
                ),
                warm,
            );
        }
    }

    #[test]
    fn array_callback_materialization_rejects_forged_predicate_metadata() {
        let library = array_callback_default_library();
        let source = parsed(concat!(
            "function isNumber(value: any): value is number { ",
            "return typeof value === \"number\"; } ",
            "declare const values: (string | number)[]; ",
            "values.filter(isNumber);",
        ));
        let library_file = FileId::new(4_928);
        let source_file = FileId::new(4_929);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        context.check_source_file(source_file).unwrap();

        let owner = context
            .store()
            .type_payload(context.global_types().array_type)
            .and_then(TypeRecord::symbol)
            .unwrap();
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("filter"))
            .unwrap();
        let callable = context
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let method_signature = context
            .store()
            .type_payload(callable)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .and_then(|signatures| signatures.first())
            .copied()
            .unwrap();
        let callback = context
            .store()
            .callable_signature_parameter_types(method_signature)
            .and_then(|parameters| parameters.first())
            .copied()
            .unwrap();
        let StoredSingleCallableValidation::Valid {
            callable: callback, ..
        } = validate_stored_single_callable(context.store(), callback)
        else {
            panic!("the predicate overload must retain its callback signature")
        };
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let forged = context
            .store_mut_for_test()
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, "value", Some(string))
            .unwrap();
        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_type_predicate(callback.signature, Some(forged))
        );

        assert!(context.recheck_source_file(source_file).is_err());
    }

    #[test]
    fn array_callback_materialization_rejects_forged_method_ownership() {
        let library = parsed(concat!(
            "interface Array<T> { ",
            "forEach(callbackfn: (value: T, index: number, array: T[]) => void, ",
            "thisArg?: any): void; ",
            "} interface ReadonlyArray<T> {}",
        ));
        let source = parsed("declare const values: number[]; values.forEach(value => value);");
        let library_file = FileId::new(4_914);
        let source_file = FileId::new(4_915);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let owner = context
            .store()
            .type_payload(context.global_types().array_type)
            .and_then(TypeRecord::symbol)
            .unwrap();
        let method = context
            .store()
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .and_then(|members| members.get_source("forEach"))
            .unwrap();
        assert!(context.store_mut_for_test().set_symbol_flags(
            method,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert!(context.check_source_file(source_file).is_err());

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn array_callback_overloads_share_their_first_contextual_parameter() {
        let parsed = parsed(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "type First = (value: number, index: number) => unknown; ",
            "type Second = (value: number, array: number[]) => boolean; ",
            "type Different = (value: string) => boolean;",
        ));
        let file = FileId::new(4_916);
        let mut context = context(&parsed, file);
        let nodes = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        let [first, second, different] = nodes.as_slice() else {
            panic!("the callback fixture must contain three function types")
        };
        let first = context.get_type_from_type_node(*first).unwrap();
        let second = context.get_type_from_type_node(*second).unwrap();
        let different = context.get_type_from_type_node(*different).unwrap();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        );

        assert_eq!(
            shared_array_callback_context(context.store(), &[first, second]),
            Some(second),
        );
        assert_eq!(
            shared_array_callback_context(context.store(), &[first, different]),
            None,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
            ),
            before,
        );
    }

    #[test]
    fn direct_callbacks_accept_wider_authenticated_parameter_lists() {
        let parsed = parsed(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "declare function consume(callback: ",
            "(value: number, index: number, values: number[]) => void): void; ",
            "consume(value => value * 2);",
        ));
        let file = FileId::new(4_917);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let arrow = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ArrowFunction).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data
        else {
            panic!("the callback fixture must retain its arrow")
        };
        let parameter = NodeRef::new(arrow.arena, arrow.file, arrow_data.parameters.nodes[0]);
        let parameter = context.file(file).unwrap().1.symbol(parameter).unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().number_type),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve both real array owners, signatures, and warm caches.
    fn array_find_index_preserves_default_library_signatures_and_receiver_elements() {
        let library = parsed(concat!(
            "interface Array<T> { ",
            "findIndex(predicate: (value: T, index: number, obj: T[]) => unknown, ",
            "thisArg?: any): number; ",
            "untouched(value: T): void; ",
            "} interface ReadonlyArray<T> { ",
            "findIndex(predicate: (value: T, index: number, obj: readonly T[]) => unknown, ",
            "thisArg?: any): number; ",
            "}",
        ));

        for (index, receiver) in ["number[]", "ReadonlyArray<number>"]
            .into_iter()
            .enumerate()
        {
            let source = parsed(&format!(
                concat!(
                    "declare function match(value: number): boolean; ",
                    "declare const values: {receiver}; ",
                    "const first: number = values.findIndex(match); ",
                    "const second: number = values.findIndex(match, undefined);",
                ),
                receiver = receiver,
            ));
            let library_file = FileId::new(4_980 + u32::try_from(index * 2).unwrap());
            let source_file = FileId::new(4_981 + u32::try_from(index * 2).unwrap());
            let mut context =
                context_with_default_library(&library, library_file, &source, source_file);

            context.check_source_file(source_file).unwrap();

            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics(),
            );
            let call_nodes = calls(&source, source_file);
            assert_eq!(call_nodes.len(), 2);
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            for call in &call_nodes {
                assert_eq!(
                    context
                        .store()
                        .type_node_links(*call)
                        .and_then(|links| links.resolved_type),
                    Some(number),
                );
            }
            let target = if index == 0 {
                context.global_types().array_type
            } else {
                context.global_types().readonly_array_type
            };
            let owner = context
                .store()
                .type_payload(target)
                .and_then(TypeRecord::symbol)
                .unwrap();
            let members = context.store().symbol(owner).unwrap().members().unwrap();
            let method = context
                .store()
                .symbol_table(members)
                .and_then(|members| members.get_source("findIndex"))
                .unwrap();
            let callable = context
                .store()
                .value_symbol_links(method)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let [signature] = context
                .store()
                .type_payload(callable)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .unwrap()
            else {
                panic!("findIndex must retain its one default-library method signature")
            };
            let signature = context.store().signature(*signature).unwrap();
            assert_eq!(signature.parameters().len(), 2);
            assert_eq!(signature.min_argument_count(), 1);
            assert_eq!(signature.resolved_return_type(), Some(number));
            if index == 0 {
                let untouched = context
                    .store()
                    .symbol_table(members)
                    .and_then(|members| members.get_source("untouched"))
                    .unwrap();
                assert!(context.store().value_symbol_links(untouched).is_none());
            }

            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                call_nodes
                    .iter()
                    .map(|call| call_publication_state(&context, *call))
                    .collect::<Vec<_>>(),
            );
            context.recheck_source_file(source_file).unwrap();
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    call_nodes
                        .iter()
                        .map(|call| call_publication_state(&context, *call))
                        .collect::<Vec<_>>(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn array_find_index_rejects_forged_library_signatures_before_call_publication() {
        for (index, declaration) in [
            concat!(
                "findIndex(predicate: (value: T, index: number, obj: T[]) => unknown, ",
                "thisArg?: any): string;",
            ),
            concat!(
                "findIndex(callback: (value: T, index: number, obj: T[]) => unknown, ",
                "thisArg?: any): number;",
            ),
            concat!(
                "findIndex(predicate: (value: T, index: number, obj: T[]) => unknown, ",
                "thisArg: any): number;",
            ),
            concat!(
                "findIndex(predicate: (value: T, index: number, obj: T[]) => boolean, ",
                "thisArg?: any): number;",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let library = parsed(&format!(
                "interface Array<T> {{ {declaration} }} interface ReadonlyArray<T> {{}}",
            ));
            let source = parsed(concat!(
                "declare function match(value: number): boolean; ",
                "declare const values: number[]; values.findIndex(match);",
            ));
            let library_file = FileId::new(4_990 + u32::try_from(index * 2).unwrap());
            let source_file = FileId::new(4_991 + u32::try_from(index * 2).unwrap());
            let mut context =
                context_with_default_library(&library, library_file, &source, source_file);
            let call_nodes = calls(&source, source_file);
            let [call] = call_nodes.as_slice() else {
                panic!("the malformed library fixture must retain one findIndex call")
            };
            let call = *call;

            assert!(context.check_source_file(source_file).is_err());
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
        }
    }

    #[test]
    fn array_find_index_rejects_source_owned_global_augmentations() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed(concat!(
            "interface Array<T> { ",
            "findIndex(predicate: (value: T, index: number, obj: T[]) => unknown, ",
            "thisArg?: any): number; } ",
            "declare function match(value: number): boolean; ",
            "declare const values: number[]; values.findIndex(match);",
        ));
        let library_file = FileId::new(4_998);
        let source_file = FileId::new(4_999);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let call_nodes = calls(&source, source_file);
        let [call] = call_nodes.as_slice() else {
            panic!("the source-owned augmentation must retain one findIndex call")
        };
        let call = *call;

        assert!(context.check_source_file(source_file).is_err());
        assert!(context.store().type_node_links(call).is_none());
        assert!(context.store().signature_links(call).is_none());
    }

    #[test]
    fn declared_call_sets_match_the_pinned_oracle_and_preserve_overload_order() {
        // Pinned tsgo oracle: the first applicable overload wins. `ordered(1)`
        // therefore returns string even though the following overload has the
        // same parameter list, while `branching(1)` skips its string overload.
        let parsed = parsed(concat!(
            "interface Ordered { ",
            "(value: number): string; ",
            "(value: number): number; ",
            "} ",
            "type Branching = { ",
            "(value: string): number; ",
            "(value: number): string; ",
            "}; ",
            "type Unary = { (value: boolean): number; }; ",
            "function fromInterface(ordered: Ordered): string { return ordered(1); } ",
            "function fromTypeLiteral(branching: Branching): string { return branching(1); } ",
            "function exactSingle(unary: Unary): number { return unary(true); }",
        ));
        let file = FileId::new(480);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [ordered_call, branching_call, exact_call] = calls.as_slice() else {
            panic!("expected the ordered, branching, and exact-single calls")
        };
        let mut declarations = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
            .map(|(node, record)| {
                (
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                )
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        let [ordered_first, _, _, branching_second, exact_declaration] = declarations.as_slice()
        else {
            panic!("expected five declared call signatures")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            [*ordered_call, *branching_call, *exact_call].map(|call| {
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type)
            }),
            [
                Some(string),
                Some(string),
                Some(context.store().intrinsic_bootstrap().unwrap().number_type),
            ],
        );
        let declared_signature = |declaration: NodeRef| {
            context
                .store()
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
        };
        assert_eq!(
            context
                .store()
                .signature_links(*ordered_call)
                .and_then(|links| links.resolved_signature.signature()),
            declared_signature(ordered_first.1),
        );
        assert_eq!(
            context
                .store()
                .signature_links(*branching_call)
                .and_then(|links| links.resolved_signature.signature()),
            declared_signature(branching_second.1),
        );
        assert_eq!(
            context
                .store()
                .signature_links(*exact_call)
                .and_then(|links| links.resolved_signature.signature()),
            declared_signature(exact_declaration.1),
        );

        let cold_counts = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().callable_signature_parameter_types_len(),
        );
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().callable_signature_parameter_types_len(),
            ),
            cold_counts,
        );

        let ordered_callee =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *ordered_call)
                .unwrap()
                .callee();
        let callable = context
            .store()
            .type_node_links(ordered_callee)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let callable_union = context
            .store_mut_for_test()
            .expression_union_type(&[callable, undefined], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            context
                .store()
                .validate_cached_union_result(callable_union, None),
            Ok(())
        );
    }

    #[test]
    fn overload_callback_context_prefers_informative_returns_without_cache_writes() {
        let parsed = parsed(concat!(
            "type Broad = (value: 'edge') => any; ",
            "type Exact = (value: 'edge') => 'edge'; ",
            "type OtherReturn = (value: 'edge') => 'other'; ",
            "type OtherInput = (value: 'other') => 'edge'; ",
            "type Optional = (value?: 'edge') => 'edge'; ",
            "type Pair = (value: 'edge', other: 'edge') => 'edge';",
        ));
        let file = FileId::new(4_888);
        let mut context = context(&parsed, file);
        let mut nodes = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        nodes.sort_by_key(|(start, _)| *start);
        let [broad, exact, other_return, other_input, optional, pair] = nodes
            .iter()
            .map(|(_, node)| context.get_type_from_type_node(*node).unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .expect("the fixture must retain six callback types");
        let primitive = context.store().intrinsic_bootstrap().unwrap().string_type;
        let cache_state = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            )
        };
        let before = cache_state(context.store());

        assert_eq!(
            shared_overload_callback_context(context.store(), &[broad, exact]),
            Some(exact),
        );
        assert_eq!(
            shared_overload_callback_context(context.store(), &[exact, broad]),
            Some(exact),
        );
        for rejected in [other_return, other_input, optional, pair, primitive] {
            assert_eq!(
                shared_overload_callback_context(context.store(), &[exact, rejected]),
                None,
            );
        }
        assert_eq!(shared_overload_callback_context(context.store(), &[]), None);
        assert_eq!(cache_state(context.store()), before);

        let exact_node = nodes[1].1;
        let original = context.store().signature_links(exact_node).unwrap().clone();
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(exact_node, SignatureLinks::default())
        );
        let poisoned = cache_state(context.store());

        assert_eq!(
            shared_overload_callback_context(context.store(), &[broad, exact]),
            None,
        );
        assert_eq!(
            shared_overload_callback_context(context.store(), &[exact, broad]),
            None,
        );
        assert_eq!(cache_state(context.store()), poisoned);
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(exact_node, original)
        );
        assert_eq!(
            shared_overload_callback_context(context.store(), &[broad, exact]),
            Some(exact),
        );
    }

    #[test]
    fn overloaded_callbacks_preserve_literal_contexts_and_replay_warm() {
        let parsed = parsed(concat!(
            "declare function broadFirst(callback: (value: 'edge') => any): void; ",
            "declare function broadFirst(callback: (value: 'edge') => 'edge'): void; ",
            "broadFirst(value => value); ",
            "declare function exactFirst(callback: (value: 'edge') => 'edge'): void; ",
            "declare function exactFirst(callback: (value: 'edge') => any): void; ",
            "exactFirst(value => value);",
        ));
        let file = FileId::new(4_889);
        let mut context = context_with_options(
            &parsed,
            file,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                no_implicit_any: true,
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let literal = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .cached_string_literal_type("edge")
            .unwrap();
        let nodes_of_kind = |kind| {
            let mut nodes = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == kind).then_some((
                        record.range.start,
                        NodeRef::new(parsed.arena.id(), file, node),
                    ))
                })
                .collect::<Vec<_>>();
            nodes.sort_by_key(|(start, _)| *start);
            nodes.into_iter().map(|(_, node)| node).collect::<Vec<_>>()
        };
        let callback_targets = nodes_of_kind(SyntaxKind::FunctionType)
            .into_iter()
            .map(|node| {
                context
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let arrows = nodes_of_kind(SyntaxKind::ArrowFunction);
        assert_eq!(arrows.len(), 2);

        let (_, bound) = context.file(file).unwrap();
        for (arrow, expected_target) in arrows
            .iter()
            .zip([callback_targets[1], callback_targets[2]])
        {
            let NodeData::ArrowFunction(syntax) = &parsed.arena.get(arrow.node).unwrap().data
            else {
                panic!("each overloaded argument must retain its callback arrow")
            };
            let parameter = NodeRef::new(parsed.arena.id(), file, syntax.parameters.nodes[0]);
            let parameter = bound.symbol(parameter).unwrap();
            let owner = bound.symbol(*arrow).unwrap();
            let callable = context
                .store()
                .source_callable_type_for_owner(owner)
                .unwrap();
            let provenance = context
                .store()
                .source_callable_provenance(callable)
                .unwrap();

            assert_eq!(provenance.contextual_target, Some(expected_target));
            assert!(provenance.contextual_variable.is_none());
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type),
                Some(literal),
            );
            assert_eq!(
                context
                    .store()
                    .signature(provenance.signature)
                    .and_then(super::super::signatures::Signature::resolved_return_type),
                Some(literal),
            );
        }

        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let declarations = nodes_of_kind(SyntaxKind::FunctionDeclaration);
        for (call, declaration) in call_nodes.iter().zip([declarations[0], declarations[2]]) {
            assert_eq!(
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature()),
                context
                    .store()
                    .signature_links(declaration)
                    .and_then(|links| links.resolved_signature.signature()),
            );
        }
        let cold = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        let cold_links = context.store().checker_link_allocated_lengths();

        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
        assert_eq!(context.store().checker_link_allocated_lengths(), cold_links);
    }

    #[test]
    fn overload_array_arguments_retain_their_shared_element_context_and_signature() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed(concat!(
            "interface Choices { ",
            "(values: number[]): string; ",
            "(values: ReadonlyArray<number>): string; ",
            "} ",
            "declare const choose: Choices; ",
            "const result = choose([1, 2]);",
        ));
        let library_file = FileId::new(4_880);
        let source_file = FileId::new(4_881);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);

        context.check_source_file(source_file).unwrap();

        let call_nodes = calls(&source, source_file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one overloaded call")
        };
        let call = *call;
        let NodeData::CallExpression(call_data) = &source.arena.get(call.node).unwrap().data else {
            panic!("expected an overloaded call expression")
        };
        let argument = NodeRef::new(source.arena.id(), source_file, call_data.arguments.nodes[0]);
        let argument_type = context
            .store()
            .type_node_links(argument)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            context
                .store()
                .canonical_array_element_type(context.global_types(), argument_type)
                .unwrap(),
            Some(context.store().intrinsic_bootstrap().unwrap().number_type)
        );
        assert!(context.diagnostics().is_empty());

        let cold = call_publication_state(&context, call);
        mark_source_unchecked(&mut context, source_file);
        context.check_source_file(source_file).unwrap();
        assert_eq!(call_publication_state(&context, call), cold);
    }

    #[test]
    fn different_overload_array_elements_do_not_create_a_contextual_type() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed("declare const unused: number;");
        let library_file = FileId::new(4_882);
        let source_file = FileId::new(4_883);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let globals = context.global_types().clone();
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let store = context.store_mut_for_test();
        let numbers = store
            .create_canonical_array_type(&globals, number, false)
            .unwrap();
        let strings = store
            .create_canonical_array_type(&globals, string, false)
            .unwrap();
        let node = NodeRef::new(source.arena.id(), source_file, source.source_file);
        let before = (store.type_len(), store.mapper_len(), store.signature_len());

        assert_eq!(
            shared_overload_index_type(store, &globals, node, &[numbers, strings], number),
            Ok(None)
        );
        assert_eq!(
            (store.type_len(), store.mapper_len(), store.signature_len()),
            before
        );
    }

    #[test]
    fn concat_array_overloads_keep_the_shared_tuple_index_type() {
        let library = parsed(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface ConcatArray<T> { readonly [index: number]: T; }",
        ));
        let source = parsed("type Pair = [number, number];");
        let library_file = FileId::new(4_884);
        let source_file = FileId::new(4_885);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let pair_declaration =
            source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::TypeAliasDeclaration(_))
                        .then_some(NodeRef::new(source.arena.id(), source_file, node))
                })
                .unwrap();
        let pair_owner = context
            .file(source_file)
            .unwrap()
            .1
            .symbol(pair_declaration)
            .unwrap();
        let concat_owner = {
            let store = context.store();
            store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .and_then(|globals| globals.get_source("ConcatArray"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .unwrap()
        };
        let pair = context.get_declared_type_of_symbol(pair_owner).unwrap();
        let concat_target = context.get_declared_type_of_symbol(concat_owner).unwrap();
        let globals = context.global_types().clone();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let node = NodeRef::new(source.arena.id(), source_file, source.source_file);
        let store = context.store_mut_for_test();
        let values = store
            .create_direct_generic_reference_type(concat_target, &[pair])
            .unwrap();
        let either = store
            .expression_union_type_with_global_types(
                &globals,
                &[pair, values],
                UnionReduction::Literal,
            )
            .unwrap();

        assert_eq!(
            shared_overload_index_type(store, &globals, node, &[values, either], number,),
            Ok(Some(pair))
        );
    }

    #[test]
    fn declared_call_set_poison_fails_closed_without_republishing_the_call() {
        let parsed = parsed(concat!(
            "interface Callable { ",
            "(value: number): string; ",
            "(value: string): number; ",
            "} ",
            "function use(callable: Callable): string { return callable(1); }",
        ));
        let file = FileId::new(481);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one call")
        };
        let call = *call;
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallSignature)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        mark_source_unchecked(&mut context, file);
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(declaration, SignatureLinks::default())
        );
        let poisoned_call = call_publication_state(&context, call);

        assert!(context.check_source_file(file).is_err());
        assert_eq!(call_publication_state(&context, call), poisoned_call);
        assert!(
            context
                .store()
                .signature_links(declaration)
                .is_some_and(|links| links == &SignatureLinks::default())
        );
    }

    #[test]
    fn declared_call_set_failure_recovery_remains_an_atomic_boundary() {
        // Pinned tsgo synthesizes a recovery signature whose return type is
        // `never`. That constructor is outside this overload slice, so the
        // call must remain unpublished rather than reuse either declaration.
        let parsed = parsed(concat!(
            "interface Recovery { ",
            "(value: number, other: number): string; ",
            "(value: string): number; ",
            "} ",
            "function use(callable: Recovery): number { return callable(true); }",
        ));
        let file = FileId::new(487);
        let call = calls(&parsed, file)
            .into_iter()
            .next()
            .expect("fixture contains one direct call");
        let declarations = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect::<Vec<_>>();
        let mut context = context(&parsed, file);

        assert!(context.check_source_file(file).is_err());

        assert!(context.diagnostics().is_empty());
        assert!(context.store().type_node_links(call).is_none());
        assert!(context.store().signature_links(call).is_none());
        assert!(declarations.iter().all(|declaration| {
            context
                .store()
                .signature_links(*declaration)
                .is_some_and(|links| links.resolved_signature.signature().is_some())
        }));
    }

    #[test]
    fn unsupported_declared_call_members_reject_before_signature_publication() {
        // Generic and rest signatures have authenticated providers. Only
        // unsupported member shapes must reject before signature publication.
        for (index, member) in [
            "(value?: number): string;",
            "new (value: number): string; (value: number): string;",
            "value: number; (value: number): string;",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(&format!(
                "interface Callable {{ {member} }} function use(callable: Callable): string {{ return callable(1); }}"
            ));
            let file = FileId::new(482 + u32::try_from(index).unwrap());
            let call = calls(&parsed, file)
                .into_iter()
                .next()
                .expect("fixture contains one direct call");
            let declarations = parsed
                .arena
                .iter()
                .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
                .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
                .collect::<Vec<_>>();
            let mut context = context(&parsed, file);

            assert!(context.check_source_file(file).is_err());
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
            assert!(
                declarations
                    .iter()
                    .all(|declaration| context.store().signature_links(*declaration).is_none())
            );
        }

        let parsed = parsed(concat!(
            "interface Callable { (value: number): string; } ",
            "declare var Callable: number; ",
            "function use(callable: Callable): string { return callable(1); }",
        ));
        let file = FileId::new(488);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallSignature)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut context = context(&parsed, file);
        assert!(context.check_source_file(file).is_err());
        assert!(context.store().signature_links(declaration).is_none());
    }

    #[test]
    fn property_call_diagnostics_retain_the_name_argument_and_call_nodes() {
        let text = concat!(
            "type API = { fn: (value: number) => string }; ",
            "function tooFew(api: API): string { return api.fn(); } ",
            "function wrong(api: API): string { return api.fn('bad'); } ",
            "function tooMany(api: API): string { return api.fn(1, 2); }",
        );
        let parsed = parsed(text);
        let file = FileId::new(441);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let mut accesses = property_accesses(&parsed, file);
        accesses.sort_by_key(|access| parsed.arena.get(access.node).unwrap().range.start);
        let [too_few, _, too_many] = calls.as_slice() else {
            panic!("expected three property calls")
        };
        let [too_few_access, _, _] = accesses.as_slice() else {
            panic!("expected three property accesses")
        };
        let wrong_argument = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::StringLiteral(literal) if literal.text == "bad")
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2554, 2345, 2554]
        );
        assert_eq!(
            diagnostics[0].node,
            Some(property_name(&parsed, file, *too_few_access))
        );
        assert_eq!(diagnostics[0].range_override, None);
        assert_eq!(diagnostics[1].node, Some(wrong_argument));
        assert_eq!(diagnostics[1].range_override, None);
        assert_eq!(diagnostics[2].node, Some(*too_many));
        assert!(diagnostics[2].range_override.is_some());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(calls.iter().all(|call| {
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                == Some(string)
        }));
        assert_ne!(diagnostics[0].node, Some(*too_few));
    }

    #[test]
    fn property_call_poison_is_rejected_without_additional_publication() {
        for poison_property in [true, false] {
            let parsed = parsed(concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return api.fn(1); }",
            ));
            let file = FileId::new(if poison_property { 442 } else { 443 });
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one call")
            };
            let call = *call;
            let access_nodes = property_accesses(&parsed, file);
            let [access] = access_nodes.as_slice() else {
                panic!("expected one property access")
            };
            let access = *access;
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            mark_source_unchecked(&mut context, file);

            if poison_property {
                assert!(context.store_mut_for_test().set_type_node_links(
                    access,
                    TypeNodeLinks {
                        outer_type_parameters: Some(Vec::new()),
                        ..TypeNodeLinks::default()
                    },
                ));
            } else {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_links(call, SignatureLinks::default())
                );
            }
            let poisoned_call = call_publication_state(&context, call);
            let poisoned_property_type = context.store().type_node_links(access).cloned();
            let poisoned_property_symbol = context.store().symbol_node_links(access).cloned();
            let result = context.check_source_file(file);

            if poison_property {
                assert_eq!(result, Err(SourceCheckError::Property(access)));
            } else {
                assert_eq!(result, Err(SourceCheckError::Call(call)));
            }
            assert_eq!(call_publication_state(&context, call), poisoned_call);
            assert_eq!(
                context.store().type_node_links(access),
                poisoned_property_type.as_ref()
            );
            assert_eq!(
                context.store().symbol_node_links(access),
                poisoned_property_symbol.as_ref()
            );
            let source = context.source_file(file).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
        }
    }

    #[test]
    fn hoisted_direct_call_publishes_exact_return_and_replays_warm() {
        let parsed = parsed(concat!(
            "const result = id(1); ",
            "function id(value: number): string { return 'ok'; }",
        ));
        let file = FileId::new(401);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one direct call")
        };
        let call = *call;
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        let signature = context
            .store()
            .signature_links(call)
            .and_then(|links| links.resolved_signature.signature())
            .expect("call signature must be cached");
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(string)
        );
        assert!(context.diagnostics().is_empty());

        let type_count = context.store().type_len();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(context.store().type_len(), type_count);
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(signature)
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn inferred_and_explicit_identity_calls_reuse_instantiated_signatures_warm() {
        let parsed = parsed(concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const inferred: 'x' = identity('x'); ",
            "const explicit = identity<string>('x');",
        ));
        let file = FileId::new(404);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [inferred, explicit] = call_nodes.as_slice() else {
            panic!("expected inferred and explicit calls")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let inferred_type = context
            .store()
            .type_node_links(*inferred)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_ne!(inferred_type, string);
        assert_eq!(
            context
                .store()
                .type_node_links(*explicit)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        let signatures = [inferred, explicit].map(|call| {
            context
                .store()
                .signature_links(*call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        });
        assert_ne!(signatures[0], signatures[1]);
        let counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        assert!(context.diagnostics().is_empty());

        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            counts
        );
        assert_eq!(
            [inferred, explicit].map(|call| {
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap()
            }),
            signatures
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn imported_identity_calls_match_oracle_and_replay_importer_first_warm() {
        let target = parsed("export function identity<T>(value: T): T { return value; }");
        let importer = parsed(concat!(
            "import { identity } from './a'; ",
            "export const inferred = identity('inferred'); ",
            "export const explicit = identity<number>(42); ",
            "export const bad: string = identity<number>(42);",
        ));
        let importer_file = FileId::new(410);
        let target_file = FileId::new(411);
        let mut call_nodes = calls(&importer, importer_file);
        call_nodes.sort_by_key(|call| importer.arena.get(call.node).unwrap().range.start);
        let [inferred, explicit, bad] = call_nodes.as_slice() else {
            panic!("expected inferred, explicit, and bad calls")
        };
        let calls = [*inferred, *explicit, *bad];
        let mut context = imported_context(&importer, importer_file, &target, target_file);
        let target_source = context.source_file(target_file).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(target_source)
                .is_some_and(|links| links.type_checked)
        );

        context.check_source_file(importer_file).unwrap();

        assert!(
            !context
                .store()
                .source_file_links(target_source)
                .is_some_and(|links| links.type_checked),
            "importer-first checking must lazily query, not recursively check, the target source"
        );
        let result_types = calls.map(|call| {
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type)
                .expect("every imported call caches its result type")
        });
        let TypeData::Literal(inferred_literal) = context
            .store()
            .type_payload(result_types[0])
            .unwrap()
            .data()
        else {
            panic!("inferred identity result must preserve its string literal")
        };
        assert_eq!(
            inferred_literal.value,
            LiteralValue::String("inferred".to_owned())
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(result_types[1..], [number, number]);

        let signatures = calls.map(|call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .expect("every imported call caches its instantiated signature")
        });
        assert_ne!(signatures[0], signatures[1]);
        assert_eq!(signatures[1], signatures[2]);
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2322]
        );
        assert_eq!(
            context.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        let counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().cached_signature_len(),
        );

        mark_source_unchecked(&mut context, importer_file);
        context.check_source_file(importer_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
            ),
            counts
        );
        assert_eq!(
            calls.map(|call| {
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap()
            }),
            signatures
        );
        assert_eq!(context.diagnostics().as_slice().len(), 1);
    }

    #[test]
    fn synthetic_default_module_property_calls_preserve_ambient_return_diagnostics() {
        let target = parsed("export function foo();\nexport function bar();");
        let importer = parsed("import { default as Foo } from './b'; Foo.bar(); Foo.foo();");

        for (index, no_implicit_any) in [false, true].into_iter().enumerate() {
            let offset = u32::try_from(index).unwrap() * 2;
            let importer_file = FileId::new(452 + offset);
            let target_file = FileId::new(453 + offset);
            let mut context = imported_context_with_target_facts(
                &importer,
                importer_file,
                &target,
                target_file,
                true,
                CanonicalModuleResolutionMode::CommonJs,
                CanonicalCheckerOptions {
                    no_implicit_any,
                    ..CanonicalCheckerOptions::default()
                },
            );

            context.check_source_file(target_file).unwrap();
            context.check_source_file(importer_file).unwrap();

            let expected_diagnostics = if no_implicit_any {
                vec![7010, 7010]
            } else {
                Vec::new()
            };
            assert_eq!(
                context
                    .diagnostics()
                    .as_slice()
                    .iter()
                    .map(|diagnostic| diagnostic.diagnostic.code())
                    .collect::<Vec<_>>(),
                expected_diagnostics
            );
            let call_nodes = calls(&importer, importer_file);
            assert_eq!(call_nodes.len(), 2);
            let any = context.store().intrinsic_bootstrap().unwrap().any_type;
            let signatures = call_nodes
                .iter()
                .map(|call| {
                    assert_eq!(
                        context
                            .store()
                            .type_node_links(*call)
                            .and_then(|links| links.resolved_type),
                        Some(any)
                    );
                    context
                        .store()
                        .signature_links(*call)
                        .and_then(|links| links.resolved_signature.signature())
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert_ne!(signatures[0], signatures[1]);

            let cold_calls = call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>();
            mark_source_unchecked(&mut context, importer_file);
            context.check_source_file(importer_file).unwrap();
            assert_eq!(
                call_nodes
                    .iter()
                    .map(|call| call_publication_state(&context, *call))
                    .collect::<Vec<_>>(),
                cold_calls
            );
        }
    }

    #[test]
    fn imported_declared_object_identity_calls_force_warm_replay_for_aliases_and_interfaces() {
        for (index, declaration) in [
            "export type User = { id: number }; ",
            "export interface User { id: number } ",
        ]
        .into_iter()
        .enumerate()
        {
            let target = parsed(&format!(
                "{declaration}export function identity<T>(value: T): T {{ return value; }}"
            ));
            let importer = parsed(concat!(
                "import type { User } from './a'; ",
                "import { identity } from './a'; ",
                "const user: User = { id: 1 }; ",
                "const inferred: User = identity(user); ",
                "const explicit = identity<string>('x');",
            ));
            let offset = u32::try_from(index).unwrap() * 2;
            let importer_file = FileId::new(420 + offset);
            let target_file = FileId::new(421 + offset);
            let mut call_nodes = calls(&importer, importer_file);
            call_nodes.sort_by_key(|call| importer.arena.get(call.node).unwrap().range.start);
            let [inferred, explicit] = call_nodes.as_slice() else {
                panic!("expected inferred declared-object and explicit primitive calls")
            };
            let mut context = imported_context(&importer, importer_file, &target, target_file);
            let target_source = context.source_file(target_file).unwrap();

            context.check_source_file(importer_file).unwrap();

            assert!(context.diagnostics().is_empty());
            assert!(
                !context
                    .store()
                    .source_file_links(target_source)
                    .is_some_and(|links| links.type_checked)
            );
            let result_types = [*inferred, *explicit].map(|call| {
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type)
                    .unwrap()
            });
            assert_eq!(context.type_to_string(result_types[0]).unwrap(), "User");
            assert_eq!(
                result_types[1],
                context.store().intrinsic_bootstrap().unwrap().string_type
            );
            let signatures = [*inferred, *explicit].map(|call| {
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap()
            });
            let counts = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
            );

            mark_source_unchecked(&mut context, importer_file);
            context.check_source_file(importer_file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().cached_signature_len(),
                ),
                counts
            );
            assert_eq!(
                [*inferred, *explicit].map(|call| {
                    context
                        .store()
                        .signature_links(call)
                        .and_then(|links| links.resolved_signature.signature())
                        .unwrap()
                }),
                signatures
            );
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn exported_alias_owner_poison_rejects_warm_replay_without_new_call_publication() {
        let target = parsed(concat!(
            "export type User = { id: number }; ",
            "export function identity<T>(value: T): T { return value; }",
        ));
        let importer = parsed(concat!(
            "import type { User } from './a'; ",
            "import { identity } from './a'; ",
            "const user: User = { id: 1 }; ",
            "const inferred: User = identity(user);",
        ));
        let importer_file = FileId::new(430);
        let target_file = FileId::new(431);
        let call_nodes = calls(&importer, importer_file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one imported identity call")
        };
        let call = *call;
        let mut context = imported_context(&importer, importer_file, &target, target_file);
        context.check_source_file(importer_file).unwrap();
        assert!(context.diagnostics().is_empty());
        let call_type = context.store().type_node_links(call).cloned();
        let call_signature = context.store().signature_links(call).cloned();
        let (module, user, identity) = {
            let (_, bound) = context.file(target_file).unwrap();
            let module = bound.symbol(bound.source_file()).unwrap();
            let exports = context
                .store()
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| context.store().symbol_table(exports))
                .unwrap();
            (
                module,
                exports.get_source("User").unwrap(),
                exports.get_source("identity").unwrap(),
            )
        };
        let exports = context.store().symbol(module).unwrap().exports().unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source("User"),
                identity,
            ),
            Some(Some(user))
        );
        mark_source_unchecked(&mut context, importer_file);
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().cached_signature_len(),
            context.store().relation_state_snapshot(),
        );

        let result = context.check_source_file(importer_file);

        assert!(matches!(
            result,
            Err(SourceCheckError::Import(node)) if node.file == importer_file
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
        assert_eq!(context.store().type_node_links(call), call_type.as_ref());
        assert_eq!(
            context.store().signature_links(call),
            call_signature.as_ref()
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nested_declared_objects_cannot_cross_the_source_inference_export_boundary() {
        let source = parsed(concat!(
            "function outer() { ",
            "type HiddenAlias = { id: number }; ",
            "interface HiddenInterface { id: number } ",
            "return 0; ",
            "}",
        ));
        let file = FileId::new(432);
        let mut context = context(&source, file);
        let symbols = {
            let (_, bound) = context.file(file).unwrap();
            source
                .arena
                .iter()
                .filter(|(_, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::TypeAliasDeclaration | SyntaxKind::InterfaceDeclaration
                    )
                })
                .map(|(node, _)| {
                    let declaration = NodeRef::new(source.arena.id(), file, node);
                    let raw = bound.symbol(declaration).unwrap();
                    context.store().get_merged_symbol(raw).unwrap()
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(symbols.len(), 2);

        for symbol in symbols {
            let type_ = context.get_declared_type_of_symbol(symbol).unwrap();
            assert!(matches!(
                validate_resolved_declared_property_type_graph(context.store(), type_),
                DeclaredPropertyTypeGraphValidation::Traversable(_)
            ));
            assert_eq!(
                super::super::inference::validate_inference_leaf(context.store(), type_),
                Err(super::super::inference::NakedTypeInferenceError::UnsupportedCandidate(type_)),
                "a nested declaration reaches the source-only override boundary"
            );
            assert!(
                !super::super::generic_calls::source_declared_inference_candidate_is_exported(
                    context.store(),
                    type_,
                ),
                "a nested modifier-free declaration must not mint export capability"
            );
        }
    }

    #[test]
    fn object_argument_excess_properties_use_the_property_span_for_both_call_paths() {
        let text = concat!(
            "function accept(value: { known: number }): void {} ",
            "function identity<T>(value: T): T { return value; } ",
            "accept({ extra: 1 }); ",
            "identity<{ known: number }>({ extra: 2 });",
        );
        let parsed = parsed(text);
        let file = FileId::new(474);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.diagnostic.code(), 2353);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Object literal may only specify known properties, and 'extra' does not exist in type '{ known: number; }'."
            );
            let node = diagnostic.node.expect("TS2353 must retain its property");
            let range = parsed.arena.get(node.node).unwrap().range;
            assert_eq!(
                &text[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                "extra"
            );
        }

        let calls = calls(&parsed, file);
        let cold = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn callable_argument_diagnostics_keep_parameter_and_return_details() {
        let parsed = parsed(concat!(
            "function accept(callback: (target: number) => number): void {} ",
            "function identity<T>(value: T): T { return value; } ",
            "accept((source: string) => {}); ",
            "accept((target: number) => {}); ",
            "identity<(target: number) => number>((source: string) => {}); ",
            "identity<(target: number) => number>((target: number) => {});",
        ));
        let file = FileId::new(475);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let actual = context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.diagnostic.code(),
                    diagnostic.diagnostic.render().unwrap(),
                )
            })
            .collect::<Vec<_>>();
        let parameter = concat!(
            "Argument of type '(source: string) => void' is not assignable to parameter of type ",
            "'(target: number) => number'.\n",
            "  Types of parameters 'source' and 'target' are incompatible.\n",
            "    Type 'number' is not assignable to type 'string'.",
        );
        let return_type = concat!(
            "Argument of type '(target: number) => void' is not assignable to parameter of type ",
            "'(target: number) => number'.\n",
            "  Type 'void' is not assignable to type 'number'.",
        );
        assert_eq!(
            actual,
            [
                (2345, parameter.to_owned()),
                (2345, return_type.to_owned()),
                (2345, parameter.to_owned()),
                (2345, return_type.to_owned()),
            ],
        );

        let calls = calls(&parsed, file);
        let cold = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn multiline_block_arrow_argument_diagnostics_stop_at_the_first_body_line() {
        let text = concat!(
            "function accept(callback: (value: number) => number): void {}\n",
            "function identity<T>(value: T): T { return value; }\n",
            "accept((value: number) => {});\n",
            "accept((value: number) => {\n});\n",
            "accept((value: number) =>\n// body comment\n{\n});\n",
            "identity<(value: number) => number>((value: number) => {\r\n});\n",
            "accept((value: number) =>\n'wrong');",
        );
        let parsed = parsed(text);
        let file = FileId::new(477);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 5, "{diagnostics:?}");
        let expected = [
            ("(value: number) => {}", false),
            ("(value: number) => {", true),
            ("(value: number) =>", true),
            ("(value: number) => {", true),
            ("(value: number) =>\n'wrong'", false),
        ];
        for (diagnostic, (expected_text, overridden)) in diagnostics.iter().zip(expected) {
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.range_override.is_some(), overridden);
            let node = diagnostic.node.expect("TS2345 must retain its arrow");
            let range = diagnostic.range_override.map_or_else(
                || parsed.arena.get(node.node).unwrap().range,
                CanonicalCheckerDiagnosticRange::range,
            );
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert_eq!(&text[start..end], expected_text);
        }

        let calls = calls(&parsed, file);
        let cold = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn mapped_record_argument_diagnostics_explain_the_missing_string_index() {
        let parsed = parsed(concat!(
            "type Record<K extends keyof any, T> = { [P in K]: T }; ",
            "declare const value: unknown; ",
            "function accept(record: Record<string, string>): void {} ",
            "function identity<T>(input: T): T { return input; } ",
            "accept(value || {}); ",
            "identity<Record<string, string>>(value || {});",
        ));
        let file = FileId::new(476);
        let mut context = context_with_options(
            &parsed,
            file,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        );

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                concat!(
                    "Argument of type '{}' is not assignable to parameter of type ",
                    "'Record<string, string>'.\n",
                    "  Index signature for type 'string' is missing in type '{}'.",
                ),
            );
        }

        let calls = calls(&parsed, file);
        let cold = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn direct_calls_issue_exact_arity_and_argument_diagnostics_but_keep_return_type() {
        let text = concat!(
            "function take(value: number): string { return 'ok'; } ",
            "const tooFew = take(); ",
            "const wrong = take((('x'))); ",
            "const tooMany = take(1, ('extra'), true);",
        );
        let parsed = parsed(text);
        let file = FileId::new(402);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [too_few, _, _] = calls.as_slice() else {
            panic!("expected too-few, wrong-type, and too-many calls")
        };
        let mut context = context(&parsed, file);
        let too_few_callee =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *too_few)
                .unwrap()
                .callee();
        let parameter = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::Parameter)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let wrong_start = text.find("'x'").unwrap();
        let wrong_argument = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::StringLiteral
                    && record.range.start == TextPos::new(u32::try_from(wrong_start).unwrap()))
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2554, 2345, 2554]
        );
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics[0].node, Some(too_few_callee));
        assert_eq!(diagnostics[0].range_override, None);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Expected 1 arguments, but got 0."
        );
        assert_eq!(diagnostics[0].related_information.len(), 1);
        assert_eq!(diagnostics[0].related_information[0].node, Some(parameter));
        assert_eq!(
            diagnostics[0].related_information[0]
                .diagnostic
                .render()
                .unwrap(),
            "An argument for 'value' was not provided."
        );
        assert_eq!(diagnostics[1].node, Some(wrong_argument));
        assert_eq!(diagnostics[1].range_override, None);
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        let too_many_start = text.find("('extra'), true").unwrap();
        let too_many_end = too_many_start + "('extra'), true".len();
        assert_eq!(diagnostics[2].node, Some(calls[2]));
        assert_eq!(
            diagnostics[2].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                calls[2],
                TextRange::new(
                    TextPos::new(u32::try_from(too_many_start).unwrap()),
                    TextPos::new(u32::try_from(too_many_end).unwrap()),
                ),
            ))
        );
        assert_eq!(
            diagnostics[2].diagnostic.render().unwrap(),
            "Expected 1 arguments, but got 3."
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(calls.iter().all(|call| {
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                == Some(string)
        }));
    }

    #[test]
    fn array_rest_calls_project_every_extra_argument_and_use_minimum_arity_diagnostic() {
        let library = parsed("interface Array<T> {}");
        let text = concat!(
            "function take(head: string, ...values: number[]): string { return head; } ",
            "const tooFew = take(); ",
            "const good = take('ok', 1, 2); ",
            "const wrong = take('ok', 1, 'bad');",
        );
        let parsed = parsed(text);
        let library_file = FileId::new(402);
        let file = FileId::new(403);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [too_few, good, wrong] = calls.as_slice() else {
            panic!("expected too-few, applicable, and wrong-rest calls")
        };
        let mut context = context_with_default_library(&library, library_file, &parsed, file);

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2555, 2345]
        );
        assert_eq!(
            context.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Expected at least 1 arguments, but got 0."
        );
        assert_eq!(
            context.diagnostics().as_slice()[1]
                .diagnostic
                .render()
                .unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        for call in [too_few, good, wrong] {
            let return_type = context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                return_type,
                context.store().intrinsic_bootstrap().unwrap().string_type
            );
        }
    }

    #[test]
    fn initialized_parameter_is_omittable_but_keeps_its_body_value_type() {
        let parsed = parsed(concat!(
            "function defaulted(value: number = 1): number { return value; } ",
            "const omitted: number = defaulted(); ",
            "const explicitUndefined: number = defaulted(undefined); ",
            "const wrong: number = defaulted('bad');",
        ));
        let file = FileId::new(404);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(diagnostics[0].diagnostic.code(), 2345);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        let owner = first_function_symbol(&parsed, &context, file);
        let callable = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        let signature = context.store().signature(provenance.signature).unwrap();
        assert_eq!(signature.min_argument_count(), 0);
        let parameter = signature.parameters()[0];
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().number_type)
        );
    }

    #[test]
    fn direct_call_cache_poison_is_rejected_before_call_publication() {
        for poison_signature in [false, true] {
            let parsed = parsed(concat!(
                "function id(value: number): string { return 'ok'; } ",
                "const result = id(1);",
            ));
            let file = FileId::new(if poison_signature { 404 } else { 403 });
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one direct call")
            };
            let call = *call;
            let mut context = context(&parsed, file);
            if poison_signature {
                assert!(context.store_mut_for_test().set_signature_links(
                    call,
                    SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolving,
                        ..SignatureLinks::default()
                    },
                ));
            } else {
                assert!(context.store_mut_for_test().set_type_node_links(
                    call,
                    TypeNodeLinks {
                        outer_type_parameters: Some(Vec::new()),
                        ..TypeNodeLinks::default()
                    },
                ));
            }

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Call(call))
            );
            assert!(context.diagnostics().is_empty());
            let source = context.source_file(file).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
            if poison_signature {
                assert_eq!(
                    context
                        .store()
                        .signature_links(call)
                        .unwrap()
                        .resolved_signature,
                    ResolvedSignatureState::Resolving
                );
                assert!(context.store().type_node_links(call).is_none());
            } else {
                assert!(context.store().signature_links(call).is_none());
                assert_eq!(
                    context
                        .store()
                        .type_node_links(call)
                        .unwrap()
                        .outer_type_parameters,
                    Some(Vec::new())
                );
            }
        }
    }

    #[test]
    fn direct_call_partial_warm_cache_is_rejected_without_writes() {
        for retain_type in [false, true] {
            let parsed = parsed(concat!(
                "function id(value: number): string { return 'ok'; } ",
                "const result = id(1);",
            ));
            let file = FileId::new(if retain_type { 438 } else { 437 });
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one direct call")
            };
            let call = *call;
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            mark_source_unchecked(&mut context, file);
            if retain_type {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_links(call, SignatureLinks::default())
                );
            } else {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(call, TypeNodeLinks::default())
                );
            }
            let poisoned = call_publication_state(&context, call);

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Call(call))
            );
            assert_eq!(call_publication_state(&context, call), poisoned);
            let source = context.source_file(file).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
        }
    }

    #[test]
    fn nested_identifier_calls_publish_each_signature_and_return_type() {
        let parsed = parsed(concat!(
            "function number(value: number): number { return value; } ",
            "function text(value: number): string { return 'ok'; } ",
            "const result: string = text(number(number(1)));",
        ));
        let file = FileId::new(405);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let calls = calls(&parsed, file);
        assert_eq!(calls.len(), 3);
        for call in &calls {
            assert!(
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature())
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }

        let warm_counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            warm_counts
        );
    }

    #[test]
    fn nongeneric_explicit_type_arguments_report_ts2558_and_reuse_the_original_signature() {
        let text = concat!(
            "function f(value: number): number { return value; } ",
            "const api = { fn: f }; ",
            "const direct = f<  /* leading */ string, number >(1); ",
            "const member = api.fn< /* member */ string >(1); ",
            "const missing = f< /* missing */ number >();",
        );
        let parsed = parsed(text);
        let file = FileId::new(406);
        let mut context = context(&parsed, file);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [direct, member, missing] = call_nodes.as_slice() else {
            panic!("expected three nongeneric calls with explicit type arguments")
        };

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
        let expected = [
            (*direct, "string, number", 2),
            (*member, "string", 1),
            (*missing, "number", 1),
        ];
        for (diagnostic, (call, expected_text, actual)) in diagnostics.iter().zip(expected) {
            assert_eq!(diagnostic.diagnostic.code(), 2558);
            assert_eq!(diagnostic.node, Some(call));
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!("Expected 0 type arguments, but got {actual}.")
            );
            let range = diagnostic
                .range_override
                .expect("TS2558 must retain the exact type argument range")
                .range();
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            assert_eq!(&text[start..end], expected_text);
            assert!(diagnostic.related_information.is_empty());
        }

        let owner = first_function_symbol(&parsed, &context, file);
        let callable = context
            .store()
            .source_callable_type_for_owner(owner)
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for call in call_nodes.iter().copied() {
            assert_eq!(
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature()),
                Some(signature)
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type),
                Some(number)
            );
        }

        let cold_calls = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold_calls
        );
    }

    #[test]
    fn noncallable_identifier_reports_ts2349_and_publishes_error_recovery() {
        let parsed = parsed("const value = 1; const result = value();");
        let file = FileId::new(446);
        let mut context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("fixture must contain one invalid call")
        };
        let call = *call;

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].diagnostic.code(), 2349);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "This expression is not callable.\n  Type 'Number' has no call signatures."
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(bootstrap.unknown_signature)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.error_type)
        );

        let counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.diagnostics().len(), 1);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            counts
        );
    }

    #[test]
    fn namespace_import_of_merged_ambient_callable_reports_exact_ts2349_and_ts7038() {
        let importer = parsed("import * as foo from \"./foo\";\nfoo()\n");
        let declaration = parsed(concat!(
            "declare function foo(): void;\n",
            "declare namespace foo {}\n",
            "export = foo;\n",
        ));
        let importer_file = FileId::new(4_470);
        let declaration_file = FileId::new(4_471);
        let mut context = imported_context_with_target_facts(
            &importer,
            importer_file,
            &declaration,
            declaration_file,
            true,
            CanonicalModuleResolutionMode::Esm,
            CanonicalCheckerOptions::default(),
        );
        let call = calls(&importer, importer_file)[0];
        let NodeData::CallExpression(call_data) = &importer.arena.get(call.node).unwrap().data
        else {
            panic!("expected the namespace import call")
        };
        let callee = NodeRef::new(importer.arena.id(), importer_file, call_data.expression);
        let import = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration).then_some(NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    node,
                ))
            })
            .unwrap();
        let function = first_function_symbol(&declaration, &context, declaration_file);

        context.check_source_file(declaration_file).unwrap();
        context.check_source_file(importer_file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one namespace import call diagnostic")
        };
        assert_eq!(diagnostic.node, Some(callee));
        assert_eq!(diagnostic.diagnostic.code(), 2349);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This expression is not callable.\n  Type '{ default: () => void; }' has no call signatures."
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("expected the namespace import related diagnostic")
        };
        assert_eq!(related.node, Some(import));
        assert_eq!(related.diagnostic.code(), 7038);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "Type originates at this import. A namespace-style import cannot be called or constructed, and will cause a failure at runtime. Consider using a default import or import require here instead."
        );
        let callable = context
            .store()
            .source_callable_type_for_owner(function)
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(callable)
            .map(|provenance| provenance.signature)
            .and_then(|signature| context.store().signature(signature))
            .unwrap();
        assert!(signature.parameters().is_empty());
        assert_eq!(
            signature.resolved_return_type(),
            Some(context.store().intrinsic_bootstrap().unwrap().void_type)
        );
        let (_, bound) = context.file(importer_file).unwrap();
        let binding = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::NamespaceImport).then_some(NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    node,
                ))
            })
            .unwrap();
        let alias = bound.symbol(binding).unwrap();
        let namespace = context
            .store()
            .value_symbol_links(alias)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let structured = context
            .store()
            .type_payload(namespace)
            .and_then(|record| record.data().structured())
            .unwrap();
        assert_eq!(structured.call_signature_count, 0);
        assert!(structured.signatures.is_none());
        let warm = (
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().as_slice().to_vec(),
        );

        context.recheck_source_file(importer_file).unwrap();

        assert_eq!(
            (
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().type_len(),
                context.store().signature_len(),
                context.diagnostics().as_slice().to_vec(),
            ),
            warm
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(function)
                .and_then(|links| links.resolved_type),
            Some(callable)
        );
    }

    #[test]
    fn namespace_import_of_merged_ambient_callable_supports_commonjs_resolution() {
        let importer = parsed("import * as foo from \"./foo\";\nfoo()\n");
        let declaration = parsed(concat!(
            "declare function foo(): void;\n",
            "declare namespace foo {}\n",
            "export = foo;\n",
        ));
        let importer_file = FileId::new(4_472);
        let declaration_file = FileId::new(4_473);
        let mut context = imported_context_with_target_facts(
            &importer,
            importer_file,
            &declaration,
            declaration_file,
            true,
            CanonicalModuleResolutionMode::CommonJs,
            CanonicalCheckerOptions::default(),
        );

        context.check_source_file(declaration_file).unwrap();
        context.check_source_file(importer_file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one CommonJS namespace import call diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2349);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This expression is not callable.\n  Type '{ default: () => void; }' has no call signatures."
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the namespace import must retain its originating import")
        };
        assert_eq!(related.diagnostic.code(), 7038);
    }

    #[test]
    fn nested_noncallable_calls_report_exact_missing_semicolon_information() {
        let text = concat!(
            "declare function foo(): string;\n",
            "foo()(1 as number).toString();\n",
            "foo()   (1 as number).toString();\n",
            "foo()\n",
            "(1 as number).toString();\n",
            "foo()\n",
            "    (1 + 2).toString();\n",
            "foo()\n",
            "    (<number>1).toString();\n",
        );
        let parsed = parsed(text);
        let file = FileId::new(490);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 5, "{diagnostics:?}");
        for (diagnostic, missing_semicolon) in
            diagnostics.iter().zip([false, false, true, true, true])
        {
            assert_eq!(diagnostic.diagnostic.code(), 2349);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "This expression is not callable.\n  Type 'String' has no call signatures."
            );
            let node = diagnostic.node.expect("TS2349 must retain its callee");
            let range = parsed.arena.get(node.node).unwrap().range;
            assert_eq!(
                &text[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                "foo()"
            );
            if missing_semicolon {
                let [related] = diagnostic.related_information.as_slice() else {
                    panic!("a newline-separated call requires one missing-semicolon diagnostic")
                };
                assert_eq!(related.node, Some(node));
                assert_eq!(related.diagnostic.code(), 2734);
                assert_eq!(
                    related.diagnostic.render().unwrap(),
                    "Are you missing a semicolon?"
                );
            } else {
                assert!(diagnostic.related_information.is_empty());
            }
        }

        let invalid_calls = calls(&parsed, file)
            .into_iter()
            .filter(|node| {
                matches!(
                    parsed.arena.get(node.node).map(|record| &record.data),
                    Some(NodeData::CallExpression(call))
                        if parsed
                            .arena
                            .get(call.expression)
                            .is_some_and(|callee| callee.kind == SyntaxKind::CallExpression)
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(invalid_calls.len(), 5);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        for call in &invalid_calls {
            assert_eq!(
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature()),
                Some(bootstrap.unknown_signature)
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type),
                Some(bootstrap.error_type)
            );
        }

        let cold = invalid_calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            invalid_calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold
        );
    }

    #[test]
    fn missing_semicolon_trivia_ignores_line_breaks_inside_block_comments() {
        for (trivia, expected) in [
            ("", false),
            (" \t", false),
            ("\n", true),
            ("\r\n", true),
            (" // comment\n", true),
            (" /* comment */\n", true),
            (" /* inside\ncomment */ ", false),
            ("\u{feff}\n", true),
            ("<string>\n", false),
        ] {
            assert_eq!(
                call_trivia_has_line_break(trivia),
                Some(expected),
                "{trivia:?}"
            );
        }
        assert_eq!(call_trivia_has_line_break("/* unterminated"), None);
    }

    #[test]
    fn any_identifier_calls_publish_the_any_signature_without_diagnostics() {
        let parsed = parsed("function use(value: any): any { return value(); }");
        let file = FileId::new(447);
        let mut context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("fixture must contain one any call")
        };
        let call = *call;

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(bootstrap.any_signature)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.any_type)
        );
    }

    #[test]
    fn any_calls_with_explicit_type_arguments_report_ts2347_and_keep_any_recovery() {
        let parsed = parsed(concat!(
            "function direct(value: any): any { return value<number>(1); } ",
            "type API = { fn: any }; ",
            "function member(api: API): any { return api.fn<string>('value'); }",
        ));
        let file = FileId::new(456);
        let mut context = context(&parsed, file);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        assert_eq!(call_nodes.len(), 2);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        for (diagnostic, call) in diagnostics.iter().zip(&call_nodes) {
            assert_eq!(diagnostic.diagnostic.code(), 2347);
            assert_eq!(diagnostic.node, Some(*call));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Untyped function calls may not accept type arguments."
            );
            assert!(diagnostic.related_information.is_empty());
            assert_eq!(
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature()),
                Some(bootstrap.any_signature)
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type),
                Some(bootstrap.any_type)
            );
        }

        let cold_calls = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold_calls
        );
    }

    #[test]
    fn generic_source_property_calls_infer_and_accept_explicit_type_arguments() {
        let parsed = parsed(concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const api = { fn: identity }; ",
            "const inferred: string = api.fn('value'); ",
            "const explicit: number = api.fn<number>(1);",
        ));
        let file = FileId::new(448);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [inferred, explicit] = call_nodes.as_slice() else {
            panic!("expected inferred and explicit generic property calls")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let inferred_type = context
            .store()
            .type_node_links(*inferred)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let TypeData::Literal(inferred_literal) =
            context.store().type_payload(inferred_type).unwrap().data()
        else {
            panic!("the inferred source property call must preserve its literal")
        };
        assert_eq!(
            inferred_literal.value,
            LiteralValue::String("value".to_owned())
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*explicit)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().number_type)
        );
        let signatures = [*inferred, *explicit].map(|call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        });
        assert_ne!(signatures[0], signatures[1]);

        let cold_calls = [*inferred, *explicit].map(|call| call_publication_state(&context, call));
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            [*inferred, *explicit].map(|call| call_publication_state(&context, call)),
            cold_calls
        );
    }

    #[test]
    fn generic_source_interface_calls_preserve_nested_references_and_warm_signatures() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed(concat!(
            "interface Box<T> { value: T } ",
            "interface Validator<T> { value: T } ",
            "interface Requireable<T> { value: T } ",
            "declare function wrap<T>(value: Box<T>): Box<T>; ",
            "declare function nested<T>(value: Box<Box<T>>): Box<Box<T>>; ",
            "declare function mixed<T>(value: Box<T[]>): Box<T>; ",
            "declare function validate<T>(value: Validator<T>): Requireable<T>; ",
            "declare const numberBox: Box<number>; ",
            "declare const nestedBox: Box<Box<number>>; ",
            "declare const arrayBox: Box<number[]>; ",
            "declare const numberValidator: Validator<number>; ",
            "const inferred = wrap(numberBox); ",
            "const explicit = wrap<number>(numberBox); ",
            "const nestedResult = nested(nestedBox); ",
            "const mixedResult = mixed(arrayBox); ",
            "const required = validate(numberValidator); ",
            "const wrong = wrap<string>(numberBox);",
        ));
        let library_file = FileId::new(4_886);
        let source_file = FileId::new(4_887);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let mut call_nodes = calls(&source, source_file);
        call_nodes.sort_by_key(|call| source.arena.get(call.node).unwrap().range.start);
        let [inferred, explicit, nested, mixed, required, wrong] = call_nodes.as_slice() else {
            panic!("expected inferred, explicit, nested, mixed, cross-interface, and invalid calls")
        };

        context.check_source_file(source_file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2345],
        );
        let resolved_type = |node| {
            context
                .store()
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
                .unwrap()
        };
        let inferred_type = resolved_type(*inferred);
        let explicit_type = resolved_type(*explicit);
        let nested_type = resolved_type(*nested);
        let mixed_type = resolved_type(*mixed);
        let required_type = resolved_type(*required);
        let wrong_type = resolved_type(*wrong);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;

        assert_eq!(inferred_type, explicit_type);
        let inferred_reference =
            validate_direct_generic_reference(context.store(), inferred_type).unwrap();
        assert_eq!(inferred_reference.type_arguments, [number]);
        let nested_reference =
            validate_direct_generic_reference(context.store(), nested_type).unwrap();
        assert_eq!(nested_reference.target, inferred_reference.target);
        assert_eq!(nested_reference.type_arguments, [inferred_type]);
        let mixed_reference =
            validate_direct_generic_reference(context.store(), mixed_type).unwrap();
        assert_eq!(mixed_reference.target, inferred_reference.target);
        assert_eq!(mixed_reference.type_arguments, [number]);
        let NodeData::CallExpression(mixed_call) = &source.arena.get(mixed.node).unwrap().data
        else {
            panic!("the mixed call must retain its interface-wrapped array argument")
        };
        let mixed_argument = NodeRef::new(
            source.arena.id(),
            source_file,
            mixed_call.arguments.nodes[0],
        );
        let mixed_argument_reference =
            validate_direct_generic_reference(context.store(), resolved_type(mixed_argument))
                .unwrap();
        assert_eq!(
            context
                .store()
                .canonical_array_element_type(
                    context.global_types(),
                    mixed_argument_reference.type_arguments[0],
                )
                .unwrap(),
            Some(number),
        );
        let required_reference =
            validate_direct_generic_reference(context.store(), required_type).unwrap();
        assert_ne!(required_reference.target, inferred_reference.target);
        assert_eq!(required_reference.type_arguments, [number]);
        let wrong_reference =
            validate_direct_generic_reference(context.store(), wrong_type).unwrap();
        assert_eq!(wrong_reference.target, inferred_reference.target);
        assert_eq!(wrong_reference.type_arguments, [string]);

        let signatures = [*inferred, *explicit].map(|call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        });
        assert_eq!(signatures[0], signatures[1]);

        let cold_calls = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, source_file);
        context.check_source_file(source_file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold_calls,
        );
    }

    #[test]
    fn strict_optional_generic_calls_infer_defaults_and_report_exact_arity_ranges() {
        let parsed = parsed(concat!(
            "declare function optional<T>(value?: T): T; ",
            "declare function fallback<T = string>(value?: T): T; ",
            "declare function dependent<T, U = T>(first: T, second?: U): U; ",
            "const omitted = optional(); ",
            "const inferred: number = optional(1); ",
            "const explicit: string = optional<string>(); ",
            "const defaulted: string = fallback(); ",
            "const related: string = dependent('value'); ",
            "const extra = optional(1, 2); ",
            "const missing = dependent();",
        ));
        let file = FileId::new(451);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [omitted, inferred, explicit, defaulted, dependent, _, _] = call_nodes.as_slice()
        else {
            panic!("expected seven optional generic calls")
        };
        let mut context = context_with_options(
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

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context
                .store()
                .type_node_links(*omitted)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.unknown_type)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*explicit)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.string_type)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*defaulted)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.string_type)
        );
        assert!(
            context
                .store()
                .type_node_links(*inferred)
                .and_then(|links| links.resolved_type)
                .and_then(|type_| context.store().type_payload(type_))
                .is_some_and(|record| record.flags().intersects(TypeFlags::NUMBER_LITERAL))
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*dependent)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.string_type)
        );
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| {
                    (
                        diagnostic.diagnostic.code(),
                        diagnostic.diagnostic.render().unwrap(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![
                (2554, "Expected 0-1 arguments, but got 2.".to_owned()),
                (2554, "Expected 1-2 arguments, but got 0.".to_owned()),
            ]
        );

        let cold_calls = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold_calls
        );
    }

    #[test]
    fn generic_fixed_callbacks_contextualize_parameters_and_reuse_checked_signatures() {
        let text = concat!(
            "declare function apply<T>(callback: (value: number) => number, input: T): T;\n",
            "apply(value => value, 'same');\n",
            "apply(value => 'wrong', 'other');\n",
            "apply(value => value, 'same');",
        );
        let source = parsed(text);
        let file = FileId::new(4_918);
        let mut context = context_with_options(
            &source,
            file,
            CanonicalCheckerOptions {
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let mut call_nodes = calls(&source, file);
        call_nodes.sort_by_key(|call| source.arena.get(call.node).unwrap().range.start);
        let [first, wrong, repeated] = call_nodes.as_slice() else {
            panic!("expected three generic calls with fixed callbacks")
        };

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one fixed callback return-type diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Argument of type '(value: number) => string' is not assignable to parameter ",
                "of type '(value: number) => number'.\n",
                "  Type 'string' is not assignable to type 'number'.",
            ),
        );
        let range = source
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap()
            .range;
        assert_eq!(
            &text[usize::try_from(range.start.get()).unwrap()
                ..usize::try_from(range.end.get()).unwrap()],
            "value => 'wrong'",
        );

        let callback_target = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionType).then_some(NodeRef::new(
                    source.arena.id(),
                    file,
                    node,
                ))
            })
            .and_then(|node| context.store().type_node_links(node))
            .and_then(|links| links.resolved_type)
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let (_, bound) = context.file(file).unwrap();
        for (node, record) in source.arena.iter() {
            if record.kind != SyntaxKind::ArrowFunction {
                continue;
            }
            let arrow = NodeRef::new(source.arena.id(), file, node);
            let NodeData::ArrowFunction(syntax) = &record.data else {
                unreachable!("the syntax kind identifies an arrow")
            };
            let parameter = NodeRef::new(source.arena.id(), file, syntax.parameters.nodes[0]);
            let parameter = bound.symbol(parameter).unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .and_then(|links| links.resolved_type),
                Some(number),
            );
            let owner = bound.symbol(arrow).unwrap();
            let callable = context
                .store()
                .source_callable_type_for_owner(owner)
                .unwrap();
            let provenance = context
                .store()
                .source_callable_provenance(callable)
                .unwrap();
            assert_eq!(provenance.contextual_target, Some(callback_target));
            assert!(provenance.contextual_variable.is_none());
        }

        let signature = |call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        };
        assert_eq!(signature(*first), signature(*repeated));
        assert_ne!(signature(*wrong), signature(*first));

        let cold = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn generic_fixed_prefixes_preserve_rest_inference_and_exact_argument_diagnostics() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let text = concat!(
            "declare function collect<T>(label: string, ...values: T[]): T[];\n",
            "declare function choose<T>(value: T, radix?: number): T;\n",
            "const first = collect('left', 1, 2);\n",
            "const repeated = collect('right', 3);\n",
            "const wrongLabel = collect(1, 2);\n",
            "const mixed = collect('left', 1, 'wrong');\n",
            "const explicit = collect<number>('left', 1, 'wrong');\n",
            "const missing = collect();\n",
            "const selected = choose('value', 2);\n",
            "const wrongOptional = choose('value', 'wrong');",
        );
        let source = parsed(text);
        let library_file = FileId::new(4_922);
        let source_file = FileId::new(4_923);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let mut call_nodes = calls(&source, source_file);
        call_nodes.sort_by_key(|call| source.arena.get(call.node).unwrap().range.start);
        let [
            first,
            repeated,
            wrong_label,
            mixed,
            explicit,
            missing,
            selected,
            wrong_optional,
        ] = call_nodes.as_slice()
        else {
            panic!("expected eight generic fixed-prefix calls")
        };

        context.check_source_file(source_file).unwrap();

        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for call in [*first, *repeated] {
            let result = context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(context.global_types(), result)
                    .unwrap(),
                Some(number),
            );
        }
        let signature = |call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        };
        assert_eq!(signature(*first), signature(*repeated));
        assert_ne!(signature(*wrong_label), signature(*first));
        assert_ne!(signature(*mixed), signature(*first));
        assert_ne!(signature(*explicit), signature(*first));
        assert!(context.store().signature(signature(*missing)).is_some());
        assert!(
            context
                .store()
                .type_node_links(*selected)
                .and_then(|links| links.resolved_type)
                .and_then(|type_| context.store().type_payload(type_))
                .is_some_and(|record| record.flags().intersects(TypeFlags::STRING_LITERAL))
        );
        assert_ne!(signature(*wrong_optional), signature(*selected));

        let expected = [
            (
                2345,
                "1",
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
            ),
            (
                2345,
                "'wrong'",
                "Argument of type 'string' is not assignable to parameter of type 'number'.",
            ),
            (
                2345,
                "'wrong'",
                "Argument of type 'string' is not assignable to parameter of type 'number'.",
            ),
            (2555, "collect", "Expected at least 1 arguments, but got 0."),
            (
                2345,
                "'wrong'",
                "Argument of type 'string' is not assignable to parameter of type 'number'.",
            ),
        ];
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
        for (diagnostic, (code, expected_text, expected_message)) in
            diagnostics.iter().zip(expected)
        {
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), expected_message);
            let range = source
                .arena
                .get(diagnostic.node.unwrap().node)
                .unwrap()
                .range;
            assert_eq!(
                &text[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                expected_text,
            );
        }

        let cold = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, source_file);
        context.check_source_file(source_file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn strict_optional_fixed_generic_parameters_retain_their_canonical_union() {
        let source = parsed(concat!(
            "declare function choose<T>(value: T, radix?: number): T; ",
            "const omitted = choose('same'); ",
            "const supplied = choose('same', 2); ",
            "const invalid = choose('same', 'wrong');",
        ));
        let file = FileId::new(4_924);
        let mut context = context_with_options(
            &source,
            file,
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let mut call_nodes = calls(&source, file);
        call_nodes.sort_by_key(|call| source.arena.get(call.node).unwrap().range.start);
        let [omitted, supplied, invalid] = call_nodes.as_slice() else {
            panic!("expected three strict optional fixed-parameter calls")
        };

        context.check_source_file(file).unwrap();

        let signature = |call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        };
        assert_eq!(signature(*omitted), signature(*supplied));
        assert_ne!(signature(*invalid), signature(*omitted));
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one strict optional fixed-parameter mismatch")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);

        let declaration = first_function_symbol(&source, &context, file);
        let callable = context
            .store()
            .source_callable_type_for_owner(declaration)
            .unwrap();
        let original = context
            .store()
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let optional = context
            .store()
            .callable_signature_parameter_types(original)
            .unwrap()[1];
        let TypeData::Union(union) = context.store().type_payload(optional).unwrap().data() else {
            panic!("strict optional fixed parameters must retain number | undefined")
        };
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert!(union.union.types.contains(&bootstrap.number_type));
        assert!(union.union.types.contains(&bootstrap.undefined_type));

        let cold = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn generic_array_rest_calls_infer_prefixes_defaults_and_reuse_checked_signatures() {
        let library = parsed("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parsed(concat!(
            "declare function collect<T>(...values: T[]): T[]; ",
            "declare function first<T>(head: T, ...values: T[]): T; ",
            "declare function fallback<T extends string = string>(...values: T[]): T; ",
            "const inferred = collect(1, 2, 3); ",
            "const repeated = collect(4, 5); ",
            "const explicit = collect<string>('first', 'second'); ",
            "const selected = first('first', 'second'); ",
            "const defaulted = fallback(); ",
            "const invalidConstraint = fallback<number>(1); ",
            "const wrong = collect<string>('first', 1); ",
            "const missing = first();",
        ));
        let library_file = FileId::new(4_920);
        let source_file = FileId::new(4_921);
        let mut context =
            context_with_default_library(&library, library_file, &source, source_file);
        let mut call_nodes = calls(&source, source_file);
        call_nodes.sort_by_key(|call| source.arena.get(call.node).unwrap().range.start);
        let [
            inferred,
            repeated,
            explicit,
            selected,
            defaulted,
            invalid_constraint,
            wrong,
            missing,
        ] = call_nodes.as_slice()
        else {
            panic!("expected eight generic array-rest calls")
        };

        context.check_source_file(source_file).unwrap();

        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        for call in [*inferred, *repeated] {
            let result = context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .canonical_array_element_type(context.global_types(), result)
                    .unwrap(),
                Some(number),
            );
        }
        let signature = |call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        };
        assert_eq!(signature(*inferred), signature(*repeated));
        assert!(
            context
                .store()
                .signature(signature(*inferred))
                .unwrap()
                .has_rest_parameter()
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*explicit)
                .and_then(|links| links.resolved_type)
                .and_then(|array| {
                    context
                        .store()
                        .canonical_array_element_type(context.global_types(), array)
                        .unwrap()
                }),
            Some(string),
        );
        let selected_result = context
            .store()
            .type_node_links(*selected)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let TypeData::Union(selected_union) = context
            .store()
            .type_payload(selected_result)
            .unwrap()
            .data()
        else {
            panic!("a naked returned type parameter must preserve its string literals")
        };
        assert_eq!(selected_union.union.types.len(), 2);
        assert_eq!(
            context
                .store()
                .type_node_links(*defaulted)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*invalid_constraint)
                .and_then(|links| links.resolved_type),
            Some(number),
        );
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2344, 2345, 2555],
        );
        assert_ne!(signature(*wrong), signature(*explicit));
        assert!(context.store().signature(signature(*missing)).is_some());

        let cold = call_nodes
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, source_file);
        context.check_source_file(source_file).unwrap();
        assert_eq!(
            call_nodes
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold,
        );
    }

    #[test]
    fn any_property_calls_publish_the_any_signature_without_diagnostics() {
        let parsed = parsed(concat!(
            "type API = { fn: any }; ",
            "function use(api: API): any { return api.fn(1); }",
        ));
        let file = FileId::new(449);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one any property call")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context
                .store()
                .signature_links(*call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(bootstrap.any_signature)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.any_type)
        );
    }

    #[test]
    fn noncallable_property_reports_ts2349_at_its_name() {
        let parsed = parsed("const api = { fn: 1 }; const result = api.fn();");
        let file = FileId::new(450);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one noncallable property call")
        };
        let access_nodes = property_accesses(&parsed, file);
        let [access] = access_nodes.as_slice() else {
            panic!("expected one noncallable property access")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one TS2349 property diagnostic")
        };
        assert_eq!(diagnostic.node, Some(property_name(&parsed, file, *access)));
        assert_eq!(diagnostic.diagnostic.code(), 2349);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This expression is not callable.\n  Type 'Number' has no call signatures."
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context
                .store()
                .signature_links(*call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(bootstrap.unknown_signature)
        );
        assert_eq!(
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.error_type)
        );

        let cold = call_publication_state(&context, *call);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(call_publication_state(&context, *call), cold);
    }
}
