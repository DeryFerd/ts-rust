use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

fn external_facts(name: &str) -> CanonicalSourceFileFacts {
    CanonicalSourceFileFacts::new(
        EscapedName::source(name),
        CanonicalSourceLanguage::TypeScript,
        false,
        CanonicalModuleState::External,
    )
}

fn importer_first_context<'arena>(
    importer: &'arena ParseResult,
    importer_file: FileId,
    target: &'arena ParseResult,
    target_file: FileId,
) -> CanonicalCheckerContext<'arena> {
    let specifier = importer
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::ImportDeclaration(import) => Some(NodeRef::new(
                importer.arena.id(),
                importer_file,
                import.module_specifier,
            )),
            _ => None,
        })
        .expect("fixture contains one import declaration");
    let files = [
        (importer_file, importer, external_facts("\"/project/b.ts\"")),
        (target_file, target, external_facts("\"/project/a.ts\"")),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, facts) in &files {
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, *file, facts.clone())
            .unwrap();
    }
    for (file, parsed, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, *file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                target_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

#[test]
fn imported_generic_identity_matches_oracle_and_replays_warm() {
    let target = parse_source_file("export function identity<T>(value: T): T { return value; }");
    let importer = parse_source_file(concat!(
        "import { identity } from './a'; ",
        "export const inferred = identity('inferred'); ",
        "export const explicit = identity<number>(42); ",
        "export const bad: string = identity<number>(42);",
    ));
    assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    let importer_file = FileId::new(0);
    let target_file = FileId::new(1);
    let mut calls = importer
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(importer.arena.id(), importer_file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    let [(_, inferred), (_, explicit), (_, bad)] = calls.as_slice() else {
        panic!("expected inferred, explicit, and bad calls")
    };
    let call_nodes = [*inferred, *explicit, *bad];
    let mut context = importer_first_context(&importer, importer_file, &target, target_file);

    context.check_source_file(importer_file).unwrap();

    let target_source = context.source_file(target_file).unwrap();
    assert!(
        !context
            .store()
            .source_file_links(target_source)
            .is_some_and(|links| links.type_checked),
        "importer-first checking must not recursively check the target source"
    );
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
    assert_eq!(
        context.diagnostics().as_slice()[0]
            .diagnostic
            .render()
            .unwrap(),
        "Type 'number' is not assignable to type 'string'."
    );
    let result_types = call_nodes.map(|call| {
        context
            .store()
            .type_node_links(call)
            .and_then(|links| links.resolved_type)
            .expect("every imported call caches its result type")
    });
    assert_eq!(
        context
            .store()
            .type_payload(result_types[0])
            .unwrap()
            .flags(),
        TypeFlags::STRING_LITERAL
    );
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(result_types[1..], [number, number]);
    let warm_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    context.check_source_file(importer_file).unwrap();

    assert_eq!(context.diagnostics().as_slice().len(), 1);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        warm_counts
    );
    assert_eq!(
        call_nodes.map(|call| {
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type)
                .unwrap()
        }),
        result_types
    );
}
