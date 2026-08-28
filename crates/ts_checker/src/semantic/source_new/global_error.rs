use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ErrorConstructorPlan {
    annotation: NodeRef,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    return_annotation: NodeRef,
    parameters: Vec<(NodeRef, SemanticSymbolId, NodeRef)>,
}

fn invalid(node: NodeRef) -> SourceNewError {
    invariant(SourceNewInvariant::InvalidConstructorCache(node))
}

fn reference_names(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> bool {
    let Some(record) = host.node(node) else {
        return false;
    };
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return false;
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    record.kind == SyntaxKind::TypeReference
        && record.flags.0 == 0
        && reference.type_arguments.is_none()
        && host
            .name_resolver_host(store)
            .ok()
            .and_then(|mut resolver| {
                resolver
                    .resolve_entity_name(name, SymbolFlags::TYPE)
                    .ok()
                    .flatten()
            })
            .and_then(|raw| store.get_merged_symbol(raw))
            == Some(symbol)
}

// Select a real Error overload that accepts no arguments.
pub(super) fn plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<ErrorConstructorPlan, SourceNewError> {
    let reject = || {
        unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        })
    };
    let globals = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .ok_or_else(reject)?;
    let error = store.symbol(symbol).ok_or_else(reject)?;
    let declaration = error.value_declaration().ok_or_else(reject)?;
    let owner = globals
        .get_source("ErrorConstructor")
        .and_then(|raw| store.get_merged_symbol(raw))
        .ok_or_else(reject)?;
    let owner_record = store.symbol(owner).ok_or_else(reject)?;
    let declarations = owner_record.declarations().ok_or_else(reject)?;
    if globals.get_source("Error").and_then(|raw| store.get_merged_symbol(raw)) != Some(symbol)
        || !super::super::instantiated_members::valid_generic_interface_value_merge(store, symbol)
        || !store.source_is_default_library_declaration(declaration)
        || error.parent().is_some()
        || owner_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.parent().is_some()
        || owner_record.value_declaration().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || !store.source_merged_symbol_declarations_match(owner)
        || declarations.is_empty()
        || declarations.iter().any(|node| {
            !store.source_is_default_library_declaration(*node)
                || !matches!(host.node(*node).map(|node| &node.data), Some(NodeData::InterfaceDeclaration(interface)) if interface.type_parameters.is_none() && interface.heritage_clauses.is_none())
        })
    {
        return Err(reject());
    }
    let NodeData::VariableDeclaration(variable) = &host.node(declaration).ok_or_else(reject)?.data
    else {
        return Err(reject());
    };
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(reject)?;
    if variable.initializer.is_some() || !reference_names(store, host, annotation, owner) {
        return Err(reject());
    }
    for provider in [symbol, owner] {
        let flags = store.symbol(provider).ok_or_else(reject)?.flags();
        if preflight_class_or_interface_reference(store, host, provider, flags)? != 0 {
            return Err(reject());
        }
    }
    let signature_symbol = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .and_then(|members| members.get(InternalSymbolName::New.as_ref()))
        .and_then(|raw| store.get_merged_symbol(raw))
        .ok_or_else(reject)?;
    let signature = store.symbol(signature_symbol).ok_or_else(reject)?;
    if signature.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::SIGNATURE
        || signature.check_flags() != CheckFlags::NONE
        || signature.value_declaration().is_some()
        || signature.members().is_some()
        || signature.exports().is_some()
        || signature.export_symbol().is_some()
        || store.get_parent_of_symbol(signature_symbol) != Some(owner)
        || !store.source_merged_symbol_declarations_match(signature_symbol)
    {
        return Err(reject());
    }
    let mut groups: Vec<(NodeRef, Vec<ErrorConstructorPlan>)> = Vec::new();
    for &node in signature.declarations().ok_or_else(reject)? {
        let record = host.node(node).ok_or_else(reject)?;
        let NodeData::ConstructSignatureDeclaration(data) = &record.data else {
            return Err(reject());
        };
        let parent = record
            .parent
            .map(|parent| NodeRef::new(node.arena, node.file, parent))
            .ok_or_else(reject)?;
        let return_annotation = data
            .type_
            .map(|node_id| NodeRef::new(node.arena, node.file, node_id))
            .ok_or_else(reject)?;
        if record.kind != SyntaxKind::ConstructSignature
            || record.flags.0 != 0
            || !declarations.contains(&parent)
            || data.type_parameters.is_some()
            || data.full_signature.is_some()
            || data.next_container.is_some()
            || data.symbol.is_some()
            || data.parameters.has_trailing_comma
            || data.parameters.nodes.len() > 2
            || !reference_names(store, host, return_annotation, symbol)
            || host
                .node(return_annotation)
                .is_none_or(|record| record.parent != Some(node.node))
            || !host.symbol_matches(store, node, signature_symbol)
        {
            return Err(reject());
        }
        let bound = host.bound_file(node).ok_or_else(reject)?;
        let locals = bound
            .locals(node)
            .and_then(|locals| store.symbol_table(locals))
            .ok_or_else(reject)?;
        let mut parameters = Vec::new();
        for &parameter_id in &data.parameters.nodes {
            let parameter = NodeRef::new(node.arena, node.file, parameter_id);
            let record = host.node(parameter).ok_or_else(reject)?;
            let NodeData::ParameterDeclaration(data) = &record.data else {
                return Err(reject());
            };
            let symbol = bound.symbol(parameter).ok_or_else(reject)?;
            let parameter_symbol = store.symbol(symbol).ok_or_else(reject)?;
            let annotation = data
                .type_
                .map(|id| NodeRef::new(node.arena, node.file, id))
                .ok_or_else(reject)?;
            let question = data
                .question_token
                .map(|id| NodeRef::new(node.arena, node.file, id))
                .ok_or_else(reject)?;
            let name = NodeRef::new(node.arena, node.file, data.name);
            let Some(NodeData::Identifier(name)) = host.node(name).map(|node| &node.data) else {
                return Err(reject());
            };
            if record.kind != SyntaxKind::Parameter
                || record.flags.0 != 0
                || record.parent != Some(node.node)
                || data.initializer.is_some()
                || data.dot_dot_dot_token.is_some()
                || data.modifiers.is_some()
                || data.symbol.is_some()
                || data.facts != 0
                || name.text == "this"
                || host.node(question).is_none_or(|token| {
                    token.kind != SyntaxKind::QuestionToken || token.parent != Some(parameter.node)
                })
                || host
                    .node(annotation)
                    .is_none_or(|node| node.parent != Some(parameter.node))
                || parameter_symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || parameter_symbol.check_flags() != CheckFlags::NONE
                || parameter_symbol.name().as_utf8() != Some(name.text.as_str())
                || parameter_symbol.declarations() != Some(&[parameter])
                || parameter_symbol.value_declaration() != Some(parameter)
                || parameter_symbol.parent().is_some()
                || parameter_symbol.members().is_some()
                || parameter_symbol.exports().is_some()
                || parameter_symbol.export_symbol().is_some()
                || locals.get_source(&name.text) != Some(symbol)
                || store.get_merged_symbol(symbol) != Some(symbol)
            {
                return Err(reject());
            }
            parameters.push((parameter, symbol, annotation));
        }
        if locals.len() != parameters.len() {
            return Err(reject());
        }
        let candidate = ErrorConstructorPlan {
            annotation,
            owner,
            declaration: node,
            return_annotation,
            parameters,
        };
        if let Some((last, candidates)) = groups.last_mut()
            && *last == parent
        {
            candidates.push(candidate);
        } else {
            groups.push((parent, vec![candidate]));
        }
    }
    groups
        .into_iter()
        .rev()
        .flat_map(|(_, candidates)| candidates)
        .next()
        .ok_or_else(reject)
}

pub(super) fn resolve(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    global: &ErrorConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    let invalid = || invalid(plan.constructor);
    let value = store
        .declared_type_links(global.owner)
        .and_then(|links| links.declared_type);
    let instance = store
        .declared_type_links(plan.resolved_symbol)
        .and_then(|links| links.declared_type);
    let annotation = exact_type_cache(store, global.annotation).map_err(|_| invalid())?;
    let return_type = exact_type_cache(store, global.return_annotation).map_err(|_| invalid())?;
    let value_links = exact_class_value_type(store, plan.resolved_symbol)?;
    let annotation_symbol = exact_symbol_cache(store, global.annotation).map_err(|_| invalid())?;
    let return_symbol =
        exact_symbol_cache(store, global.return_annotation).map_err(|_| invalid())?;
    if annotation.is_some_and(|type_| Some(type_) != value)
        || return_type.is_some_and(|type_| Some(type_) != instance)
        || value_links.is_some_and(|type_| Some(type_) != value)
        || annotation_symbol.is_some_and(|symbol| symbol != global.owner)
        || return_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol)
    {
        return Err(invalid());
    }
    let Some(signature) =
        exact_signature_cache(store, global.declaration).map_err(|_| invalid())?
    else {
        return Ok(None);
    };
    let (Some(value_type), Some(instance_type)) = (value, instance) else {
        return Err(invalid());
    };
    for (type_, symbol) in [
        (value_type, global.owner),
        (instance_type, plan.resolved_symbol),
    ] {
        let record = store.type_payload(type_).ok_or_else(invalid)?;
        if record.flags() != TypeFlags::OBJECT
            || !record.object_flags().contains(ObjectFlags::INTERFACE)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
        {
            return Err(invalid());
        }
    }
    let record = store.signature(signature).ok_or_else(invalid)?;
    let parameters = global
        .parameters
        .iter()
        .map(|(_, symbol, _)| *symbol)
        .collect::<Vec<_>>();
    let parameter_types = parameters
        .iter()
        .map(|symbol| {
            store
                .value_symbol_links(*symbol)
                .and_then(|links| links.resolved_type)
                .ok_or_else(invalid)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if annotation != value
        || return_type != instance
        || value_links != value
        || annotation_symbol != Some(global.owner)
        || return_symbol != Some(plan.resolved_symbol)
        || record.flags() != SignatureFlags::CONSTRUCT
        || record.declaration() != Some(global.declaration)
        || record.parameters() != parameters
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.min_argument_count() != 0
        || record.resolved_min_argument_count() != -1
        || record.resolved_return_type() != instance
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.composite().is_some()
        || record.isolated_signature_type().is_some()
        || store
            .callable_signature_parameter_types(signature)
            .is_some_and(|cached| cached != parameter_types)
        || store.function_signature_return_annotation(signature)
            != Some((global.return_annotation, false))
    {
        return Err(invalid());
    }
    for ((declaration, symbol, annotation), &type_) in
        global.parameters.iter().zip(&parameter_types)
    {
        let base = exact_type_cache(store, *annotation)
            .map_err(|_| invalid())?
            .ok_or_else(invalid)?;
        if optional_constructor_parameter_type(store, base, true, *declaration)? != Some(type_)
            || store.value_symbol_links(*symbol)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(invalid());
        }
    }
    Ok(Some(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    }))
}

// The selected signature is published while the constructor interface stays lazy.
pub(super) fn prepare(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceDefaultNewPlan,
    global: &ErrorConstructorPlan,
) -> Result<(), SourceNewError> {
    if resolve(store, plan, global)?.is_some() {
        return Ok(());
    }
    let invalid = || invalid(plan.constructor);
    let instance_type = store.get_declared_type_of_symbol(host, plan.resolved_symbol)?;
    let value_type = store.get_declared_type_of_symbol(host, global.owner)?;
    if !store.try_reserve_type_node_links(global.parameters.len()) {
        return Err(invariant(SourceNewInvariant::Capacity(plan.constructor)));
    }
    let mut parameter_types = Vec::new();
    for &(declaration, symbol, annotation) in &global.parameters {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let base = CanonicalTypeQuery::new_with_global_types(
            store,
            host,
            globals,
            options,
            &mut diagnostics,
        )?
        .get_type_from_type_node(annotation)?;
        if !diagnostics.is_empty() {
            return Err(invalid());
        }
        if exact_type_cache(store, annotation)
            .map_err(|_| invalid())?
            .is_some_and(|cached| cached != base)
            || !store.set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(base),
                    ..TypeNodeLinks::default()
                },
            )
        {
            return Err(invalid());
        }
        let type_ = match optional_constructor_parameter_type(store, base, true, declaration)? {
            Some(type_) => type_,
            None => {
                let undefined = store
                    .intrinsic_bootstrap()
                    .ok_or_else(invalid)?
                    .undefined_type;
                super::super::instantiate::canonical_anonymous_union(store, &[base, undefined])
                    .map_err(|_| invalid())?
            }
        };
        let expected = ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        };
        if store
            .value_symbol_links(symbol)
            .is_some_and(|links| links != &ValueSymbolLinks::default() && links != &expected)
        {
            return Err(invalid());
        }
        parameter_types.push(type_);
    }
    if !store.try_reserve_signatures(1)
        || !store.try_reserve_signature_links(1)
        || !store.try_reserve_type_node_links(2)
        || !store.try_reserve_symbol_node_links(2)
        || !store.try_reserve_value_symbol_links(global.parameters.len() + 1)
        || !store.try_reserve_function_signature_return_annotations(1)
    {
        return Err(invariant(SourceNewInvariant::Capacity(plan.constructor)));
    }
    let signature = store
        .alloc_signature(
            SignatureFlags::CONSTRUCT,
            Some(global.declaration),
            Vec::new(),
            None,
            global
                .parameters
                .iter()
                .map(|(_, symbol, _)| *symbol)
                .collect(),
            Some(instance_type),
            None,
            0,
        )
        .ok_or_else(invalid)?;
    for ((_, symbol, _), &type_) in global.parameters.iter().zip(&parameter_types) {
        if !store.set_value_symbol_links(
            *symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ) {
            return Err(invalid());
        }
    }
    for (node, type_, symbol) in [
        (global.annotation, value_type, global.owner),
        (
            global.return_annotation,
            instance_type,
            plan.resolved_symbol,
        ),
    ] {
        if !store.set_type_node_links(
            node,
            TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            },
        ) || !store.set_symbol_node_links(
            node,
            SymbolNodeLinks {
                resolved_symbol: Some(symbol),
            },
        ) {
            return Err(invalid());
        }
    }
    if !store.set_value_symbol_links(
        plan.resolved_symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        },
    ) || !store.set_signature_links(
        global.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ) || !store.set_function_signature_return_annotation(
        signature,
        global.return_annotation,
        false,
    ) || resolve(store, plan, global)?.is_none()
    {
        return Err(invalid());
    }
    Ok(())
}
