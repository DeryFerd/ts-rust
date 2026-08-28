use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::InternalSymbolName;

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalModuleResolutionLookup, CanonicalModuleResolutionMode, CanonicalResolvedModule,
    CanonicalTypeMapperStore, DeclaredTypeHost, SymbolNodeLinks, TypeId, TypeNodeLinks,
    instantiate::InstantiationSession,
    reference_types::validate_direct_generic_reference,
    source::{SourceCheckError, UnsupportedSourceSyntax},
    source_imports::{prepare_source_file_namespace_identity, source_file_namespace_type},
    type_nodes::CanonicalTypeQuery,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedImportCall {
    pub(super) node: NodeRef,
    pub(super) specifier: NodeRef,
    pub(super) text: String,
    pub(super) deferred_name: Option<NodeRef>,
    pub(super) resolution: CanonicalResolvedModule,
}

pub(super) fn plan_import_call(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<PlannedImportCall>, SourceCheckError> {
    let invalid = || SourceCheckError::Import(node);
    let unsupported = || SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node));
    let record = arena.get(node.node).ok_or_else(invalid)?;
    if node.arena != arena.id() || !store.contains_node_ref(node) {
        return Err(invalid());
    }
    if !ts_ast::is_import_call(arena, record) {
        return Ok(None);
    }
    let NodeData::CallExpression(call) = &record.data else {
        return Err(invalid());
    };
    if record.flags.0 != 0 || call.symbol.is_some() || call.facts != 0 {
        return Err(invalid());
    }
    let [specifier] = call.arguments.nodes.as_slice() else {
        return Err(unsupported());
    };
    let specifier = NodeRef::new(node.arena, node.file, *specifier);
    let specifier_record = arena.get(specifier.node).ok_or_else(invalid)?;
    if !store.contains_node_ref(specifier)
        || !specifier_record
            .data
            .matches_syntax_kind(specifier_record.kind)
        || specifier_record.parent != Some(node.node)
    {
        return Err(invalid());
    }
    let NodeData::StringLiteral(literal) = &specifier_record.data else {
        return Err(unsupported());
    };
    let callee = NodeRef::new(node.arena, node.file, call.expression);
    let callee_record = arena.get(callee.node).ok_or_else(invalid)?;
    if callee_record.flags.0 != 0
        || callee_record.parent != Some(node.node)
        || callee_record.range.start != record.range.start
        || callee_record.range.end > record.range.end
        || specifier_record.kind != SyntaxKind::StringLiteral
        || specifier_record.flags.0 != 0
        || specifier_record.range.start < callee_record.range.end
        || specifier_record.range.end > record.range.end
    {
        return Err(invalid());
    }
    if call.type_arguments.is_some()
        || call.question_dot_token.is_some()
        || call.arguments.has_trailing_comma
        || literal.token_flags.0 != 0
        || literal.text.is_empty()
    {
        return Err(unsupported());
    }
    let deferred_name = match &callee_record.data {
        NodeData::MetaProperty(meta) => {
            let name = NodeRef::new(node.arena, node.file, meta.name);
            let name_record = arena.get(name.node).ok_or_else(invalid)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(invalid());
            };
            if meta.flow_node.is_some()
                || meta.facts != 0
                || name_record.flags.0 != 0
                || name_record.parent != Some(callee.node)
                || identifier.flow_node.is_some()
            {
                return Err(invalid());
            }
            Some(name)
        }
        NodeData::KeywordExpression(keyword) if keyword.flow_node.is_none() => None,
        NodeData::Token(_) => None,
        _ => return Err(invalid()),
    };
    let resolution = match host
        .module_resolutions()
        .ok_or_else(unsupported)?
        .lookup(specifier)
    {
        CanonicalModuleResolutionLookup::Resolved(resolution) => resolution,
        CanonicalModuleResolutionLookup::Unavailable
        | CanonicalModuleResolutionLookup::Unresolved => {
            return Err(unsupported());
        }
        CanonicalModuleResolutionLookup::EntryAbsent => return Err(invalid()),
    };
    if resolution.usage_mode() != CanonicalModuleResolutionMode::Esm {
        return Err(invalid());
    }
    if resolution.is_ambient_module() {
        return Err(unsupported());
    }
    if store
        .symbol(resolution.target_symbol())
        .and_then(|symbol| symbol.exports())
        .and_then(|exports| store.symbol_table(exports))
        .is_some_and(|exports| {
            exports
                .get(InternalSymbolName::ExportEquals.as_ref())
                .is_some()
        })
    {
        return Err(unsupported());
    }
    source_file_namespace_type(store, host, resolution.target_symbol()).map_err(|_| invalid())?;
    Ok(Some(PlannedImportCall {
        node,
        specifier,
        text: literal.text.clone(),
        deferred_name,
        resolution,
    }))
}

pub(super) fn check_import_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &PlannedImportCall,
) -> Result<TypeId, SourceCheckError> {
    let invalid = || SourceCheckError::Import(plan.node);
    let (arena, _) = host.source(plan.node).ok_or_else(invalid)?;
    if plan_import_call(arena, store, host, plan.node)?.as_ref() != Some(plan) {
        return Err(invalid());
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let any = bootstrap.any_type;
    let existing_string = bootstrap.cached_string_literal_type(&plan.text);
    if store.type_node_links(plan.specifier).is_some_and(|links| {
        links.outer_type_parameters.is_some()
            || links
                .resolved_type
                .is_some_and(|type_| Some(type_) != existing_string)
    }) || store
        .symbol_node_links(plan.specifier)
        .is_some_and(|links| {
            links
                .resolved_symbol
                .is_some_and(|symbol| symbol != plan.resolution.target_symbol())
        })
        || store
            .symbol_node_links(plan.node)
            .is_some_and(|links| links.resolved_symbol.is_some())
    {
        return Err(invalid());
    }
    if let Some(name) = plan.deferred_name {
        check_type_cache(store, name, any)?;
        if store
            .symbol_node_links(name)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return Err(invalid());
        }
    }
    if let Some(links) = store.type_node_links(plan.node) {
        if links.outer_type_parameters.is_some() {
            return Err(invalid());
        }
        if let Some(type_) = links.resolved_type {
            let reference =
                validate_direct_generic_reference(store, type_).map_err(|_| invalid())?;
            let namespace =
                source_file_namespace_type(store, host, plan.resolution.target_symbol())
                    .map_err(|_| invalid())?
                    .ok_or_else(invalid)?;
            let promise = store
                .symbol_table(bootstrap.globals)
                .and_then(|symbols| symbols.get_source("Promise"))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .ok_or_else(invalid)?;
            if reference.type_arguments != [namespace]
                || store
                    .type_payload(reference.target)
                    .and_then(|record| record.symbol())
                    != Some(promise)
            {
                return Err(invalid());
            }
        }
    }
    let namespace =
        prepare_source_file_namespace_identity(store, host, plan.resolution.target_symbol())
            .map_err(|_| invalid())?;
    let promise = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        globals,
        options,
        session,
        diagnostics,
    )?
    .get_global_promise_type(namespace)?;
    let string = store
        .regular_string_literal_type(plan.text.clone())
        .map_err(|_| invalid())?;
    check_type_cache(store, plan.node, promise)?;
    check_type_cache(store, plan.specifier, string)?;
    if !store.set_symbol_node_links(
        plan.specifier,
        SymbolNodeLinks {
            resolved_symbol: Some(plan.resolution.target_symbol()),
        },
    ) || !store.set_type_node_links(
        plan.specifier,
        TypeNodeLinks {
            resolved_type: Some(string),
            ..TypeNodeLinks::default()
        },
    ) || !store.set_type_node_links(
        plan.node,
        TypeNodeLinks {
            resolved_type: Some(promise),
            ..TypeNodeLinks::default()
        },
    ) {
        return Err(invalid());
    }
    // The phase-name token has no value symbol. Go location queries return any.
    if let Some(name) = plan.deferred_name
        && !store.set_type_node_links(
            name,
            TypeNodeLinks {
                resolved_type: Some(any),
                ..TypeNodeLinks::default()
            },
        )
    {
        return Err(invalid());
    }
    Ok(promise)
}

fn check_type_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    expected: TypeId,
) -> Result<(), SourceCheckError> {
    if store.type_node_links(node).is_some_and(|links| {
        links.outer_type_parameters.is_some()
            || links.resolved_type.is_some_and(|type_| type_ != expected)
    }) {
        return Err(SourceCheckError::Import(node));
    }
    Ok(())
}
