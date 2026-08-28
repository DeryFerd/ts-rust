use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

use super::*;
use crate::semantic::{
    CanonicalCheckerContext, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalResolvedModuleInput,
    reference_types::create_direct_generic_reference, types::ObjectFlags,
};

fn call_node(source: &ParseResult) -> NodeRef {
    let node = source
        .arena
        .iter()
        .find_map(|(node, record)| ts_ast::is_import_call(&source.arena, record).then_some(node))
        .unwrap();
    NodeRef::new(source.arena.id(), FileId::new(0), node)
}

fn context<'arena>(
    source: &'arena ParseResult,
    library: &'arena ParseResult,
    manifest: Option<CanonicalModuleResolutionManifestInput>,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    let files = [
        (FileId::new(0), source, false),
        (FileId::new(1), library, true),
    ];
    for (file, parsed, library) in files {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(if library {
                        "\"/lib.d.ts\""
                    } else {
                        "\"/main.ts\""
                    }),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let arenas = files
        .iter()
        .map(|(file, parsed, _)| (*file, &parsed.arena))
        .collect();
    if let Some(manifest) = manifest {
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            arenas,
            CanonicalCheckerOptions::default(),
            manifest,
        )
        .unwrap()
    } else {
        CanonicalCheckerContext::new(binder.finish(), arenas, CanonicalCheckerOptions::default())
            .unwrap()
    }
}

fn unresolved_manifest(source: &ParseResult) -> CanonicalModuleResolutionManifestInput {
    let call = call_node(source);
    let NodeData::CallExpression(data) = &source.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::unresolved(
        NodeRef::new(call.arena, call.file, data.arguments.nodes[0]),
    )])
}

#[test]
fn unresolved_import_calls_do_not_recover_missing_resolution_evidence() {
    let source = parse_source_file("import('./missing');");
    let library = parse_source_file("interface Promise<T> {}");
    let call = call_node(&source);
    for (manifest, expected) in [
        (
            None,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(call)),
        ),
        (
            Some(CanonicalModuleResolutionManifestInput::new([])),
            SourceCheckError::Import(call),
        ),
    ] {
        let context = context(&source, &library, manifest);
        let host = context
            .declared_type_host()
            .unwrap()
            .with_module_resolutions(context.module_resolutions());
        assert_eq!(
            plan_import_call(&source.arena, context.store(), &host, call),
            Err(expected)
        );
        assert!(context.store().type_node_links(call).is_none());
    }
    let context = context(&source, &library, Some(unresolved_manifest(&source)));
    let host = context
        .declared_type_host()
        .unwrap()
        .with_module_resolutions(context.module_resolutions());
    let plan = plan_import_call(&source.arena, context.store(), &host, call)
        .unwrap()
        .unwrap();
    assert_eq!(plan.resolution, None);
    assert_eq!(preflight_import_call(context.store(), &host, &plan), Ok(()));
    assert!(context.store().symbol_node_links(plan.specifier).is_none());
}

#[test]
fn unresolved_import_calls_reject_changed_plans_and_foreign_symbol_caches() {
    let source = parse_source_file("import('./missing');");
    let library = parse_source_file("interface Promise<T> {}");
    let call = call_node(&source);
    let mut context = context(&source, &library, Some(unresolved_manifest(&source)));
    let mut plan = {
        let host = context
            .declared_type_host()
            .unwrap()
            .with_module_resolutions(context.module_resolutions());
        plan_import_call(&source.arena, context.store(), &host, call)
            .unwrap()
            .unwrap()
    };
    let original = plan.clone();
    plan.text = Some("./different".to_owned());
    let host = context
        .declared_type_host()
        .unwrap()
        .with_module_resolutions(context.module_resolutions());
    assert_eq!(
        preflight_import_call(context.store(), &host, &plan),
        Err(SourceCheckError::Import(call))
    );
    let symbol = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_symbol;
    assert!(context.store_mut_for_test().set_symbol_node_links(
        original.specifier,
        SymbolNodeLinks {
            resolved_symbol: Some(symbol)
        },
    ));
    let before = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().checker_link_allocated_lengths(),
    );
    let host = context
        .declared_type_host()
        .unwrap()
        .with_module_resolutions(context.module_resolutions());
    assert_eq!(
        preflight_import_call(context.store(), &host, &original),
        Err(SourceCheckError::Import(call))
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths()
        ),
        before
    );
}

#[test]
fn unresolved_import_calls_require_a_real_promise_any_cache_on_replay() {
    let source = parse_source_file("import('./missing');");
    let library = parse_source_file("interface Promise<T> {}");
    let call = call_node(&source);
    let mut context = context(&source, &library, Some(unresolved_manifest(&source)));
    context.check_source_file(call.file).unwrap();
    let plan = {
        let host = context
            .declared_type_host()
            .unwrap()
            .with_module_resolutions(context.module_resolutions());
        plan_import_call(&source.arena, context.store(), &host, call)
            .unwrap()
            .unwrap()
    };
    let cached = context
        .store()
        .type_node_links(call)
        .unwrap()
        .resolved_type
        .unwrap();
    let any = context.store().intrinsic_bootstrap().unwrap().any_type;
    let reference = validate_direct_generic_reference(context.store(), cached).unwrap();
    assert_eq!(reference.type_arguments, [any]);
    context.recheck_source_file(call.file).unwrap();
    assert_eq!(
        context.store().type_node_links(call).unwrap().resolved_type,
        Some(cached)
    );
    assert!(context.store_mut_for_test().set_type_node_links(
        call,
        TypeNodeLinks {
            resolved_type: Some(any),
            ..TypeNodeLinks::default()
        }
    ));
    let host = context
        .declared_type_host()
        .unwrap()
        .with_module_resolutions(context.module_resolutions());
    assert_eq!(
        preflight_import_call(context.store(), &host, &plan),
        Err(SourceCheckError::Import(call))
    );
}

#[test]
fn resolved_import_calls_keep_the_namespace_argument_and_reject_promise_any() {
    let source = parse_source_file("export const value = 1; import('./main',);");
    let library = parse_source_file("interface Promise<T> {}");
    let call = call_node(&source);
    let NodeData::CallExpression(data) = &source.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let specifier = NodeRef::new(call.arena, call.file, data.arguments.nodes[0]);
    let manifest =
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                call.file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]);
    let mut context = context(&source, &library, Some(manifest));
    context.check_source_file(call.file).unwrap();
    let host = context
        .declared_type_host()
        .unwrap()
        .with_module_resolutions(context.module_resolutions());
    let plan = plan_import_call(&source.arena, context.store(), &host, call)
        .unwrap()
        .unwrap();
    let resolution = plan.resolution.unwrap();
    let namespace = source_file_namespace_type(context.store(), &host, resolution.target_symbol())
        .unwrap()
        .unwrap();
    let cached = context
        .store()
        .type_node_links(call)
        .unwrap()
        .resolved_type
        .unwrap();
    let reference = validate_direct_generic_reference(context.store(), cached).unwrap();
    let target = reference.target;
    let any = context.store().intrinsic_bootstrap().unwrap().any_type;
    assert_ne!(namespace, any);
    assert_eq!(reference.type_arguments, [namespace]);
    assert_eq!(
        context
            .store()
            .symbol_node_links(specifier)
            .unwrap()
            .resolved_symbol,
        Some(resolution.target_symbol()),
    );
    context.recheck_source_file(call.file).unwrap();
    assert_eq!(
        context.store().type_node_links(call).unwrap().resolved_type,
        Some(cached)
    );
    let recovery = create_direct_generic_reference(
        context.store_mut_for_test(),
        target,
        &[any],
        ObjectFlags::NONE,
    )
    .unwrap();
    assert!(context.store_mut_for_test().set_type_node_links(
        call,
        TypeNodeLinks {
            resolved_type: Some(recovery),
            ..TypeNodeLinks::default()
        }
    ));
    let host = context
        .declared_type_host()
        .unwrap()
        .with_module_resolutions(context.module_resolutions());
    assert_eq!(
        preflight_import_call(context.store(), &host, &plan),
        Err(SourceCheckError::Import(call))
    );
}
