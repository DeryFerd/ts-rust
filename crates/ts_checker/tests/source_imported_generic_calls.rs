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
    let mut specifiers = importer
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
    specifiers.sort_by_key(|(start, _)| *start);
    assert!(
        !specifiers.is_empty(),
        "fixture contains an import declaration"
    );
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
        CanonicalModuleResolutionManifestInput::new(specifiers.into_iter().map(
            |(_, specifier)| {
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            },
        )),
    )
    .unwrap()
}

fn call_nodes(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    calls.into_iter().map(|(_, call)| call).collect()
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
    let calls = call_nodes(&importer, importer_file);
    let [inferred, explicit, bad] = calls.as_slice() else {
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

#[test]
fn imported_ordered_generics_share_checked_signatures_but_not_recoveries() {
    let target = parse_source_file(concat!(
        "export function pair<T, U>(left: T, right: U): U { return right; } ",
        "export const targetGood = pair<string, number>('target', 1);",
    ));
    let importer = parse_source_file(concat!(
        "import { pair } from './a'; ",
        "export const good = pair<string, number>('imported', 1); ",
        "export const badA = pair<string, number>('imported', 'bad'); ",
        "export const badB = pair<string, number>('imported', 'bad'); ",
        "export const tooFew = pair<string, number>('imported');",
    ));
    assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    let importer_file = FileId::new(30);
    let target_file = FileId::new(31);
    let importer_calls = call_nodes(&importer, importer_file);
    let [good, bad_a, bad_b, too_few] = importer_calls.as_slice() else {
        panic!("expected four imported ordered-generic calls")
    };
    let target_calls = call_nodes(&target, target_file);
    let [target_good] = target_calls.as_slice() else {
        panic!("expected one target-side ordered-generic call")
    };
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
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2345, 2345, 2554]
    );
    assert_eq!(diagnostics[2].node.map(|node| node.file), Some(importer_file));
    assert_eq!(diagnostics[2].related_information.len(), 1);
    assert_eq!(
        diagnostics[2].related_information[0]
            .node
            .map(|node| node.file),
        Some(target_file)
    );
    assert_eq!(diagnostics[2].related_information[0].diagnostic.code(), 6210);
    assert_eq!(
        diagnostics[2].related_information[0]
            .diagnostic
            .render()
            .unwrap(),
        "An argument for 'right' was not provided."
    );
    let signature = |context: &CanonicalCheckerContext<'_>, call: NodeRef| {
        context
            .store()
            .signature_links(call)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap()
    };
    let good_signature = signature(&context, *good);
    let first_recovery = signature(&context, *bad_a);
    let second_recovery = signature(&context, *bad_b);
    assert_ne!(first_recovery, second_recovery);
    assert_ne!(first_recovery, good_signature);
    assert_ne!(second_recovery, good_signature);
    assert_ne!(signature(&context, *too_few), good_signature);

    context.check_source_file(target_file).unwrap();

    assert_eq!(signature(&context, *target_good), good_signature);
    assert_eq!(context.diagnostics().len(), 3);
}

#[test]
#[allow(clippy::too_many_lines)]
fn imported_alias_objects_flow_through_inferred_and_explicit_identity_calls() {
    let target = parse_source_file(concat!(
        "export type User = { id: number }; ",
        "export function identity<T>(value: T): T { return value; }",
    ));
    let importer = parse_source_file(concat!(
        "import type { User } from './a'; ",
        "import { identity } from './a'; ",
        "export const user: User = { id: 1 }; ",
        "export const inferred: User = identity(user); ",
        "export const literal = identity('x'); ",
        "export const explicitString = identity<string>('x'); ",
        "export const bad: { id: string } = identity(user);",
    ));
    assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    let importer_file = FileId::new(20);
    let target_file = FileId::new(21);
    let calls = call_nodes(&importer, importer_file);
    let [inferred, literal, explicit_string, bad] = calls.as_slice() else {
        panic!("expected four identity calls")
    };
    let mut context = importer_first_context(&importer, importer_file, &target, target_file);
    let target_source = context.source_file(target_file).unwrap();

    context.check_source_file(importer_file).unwrap();

    assert!(
        !context
            .store()
            .source_file_links(target_source)
            .is_some_and(|links| links.type_checked),
        "imported declared-object calls must not recursively check their target source"
    );
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].diagnostic.code(), 2322);
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        concat!(
            "Type 'User' is not assignable to type '{ id: string; }'.\n",
            "  Types of property 'id' are incompatible.\n",
            "    Type 'number' is not assignable to type 'string'.",
        )
    );
    let result_types = calls
        .iter()
        .map(|call| {
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(result_types[0], result_types[3]);
    assert_eq!(context.type_to_string(result_types[0]).unwrap(), "User");
    assert_eq!(
        context
            .store()
            .type_payload(result_types[1])
            .unwrap()
            .flags(),
        TypeFlags::STRING_LITERAL
    );
    assert_eq!(
        result_types[2],
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    let signatures = [*inferred, *literal, *explicit_string, *bad].map(|call| {
        context
            .store()
            .signature_links(call)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap()
    });
    assert_eq!(signatures[0], signatures[3]);
    let counts = (
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
        counts
    );
}

#[test]
fn imported_interfaces_flow_through_inferred_identity_calls() {
    let target = parse_source_file(concat!(
        "export interface User { id: number } ",
        "export function identity<T>(value: T): T { return value; }",
    ));
    let importer = parse_source_file(concat!(
        "import type { User } from './a'; ",
        "import { identity } from './a'; ",
        "const user: User = { id: 1 }; ",
        "const inferred: User = identity(user); ",
        "const explicit = identity<string>('x');",
    ));
    let importer_file = FileId::new(22);
    let target_file = FileId::new(23);
    let calls = call_nodes(&importer, importer_file);
    let [inferred, explicit] = calls.as_slice() else {
        panic!("expected inferred interface and explicit primitive calls")
    };
    let mut context = importer_first_context(&importer, importer_file, &target, target_file);

    context.check_source_file(importer_file).unwrap();

    assert!(context.diagnostics().is_empty());
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

    context.check_source_file(importer_file).unwrap();
    assert!(context.diagnostics().is_empty());

    let mut target_first = importer_first_context(&importer, importer_file, &target, target_file);
    target_first.check_source_file(target_file).unwrap();
    target_first.check_source_file(importer_file).unwrap();
    assert!(target_first.diagnostics().is_empty());
}
