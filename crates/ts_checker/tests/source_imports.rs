use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, SourceCheckError,
    UnsupportedSourceSyntax,
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

fn import_nodes(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let clause = import.import_clause?;
            let clause = parsed.arena.get(clause)?;
            let NodeData::ImportClause(clause) = &clause.data else {
                return None;
            };
            let named = parsed.arena.get(clause.named_bindings?)?;
            let NodeData::NamedImports(named) = &named.data else {
                return None;
            };
            let binding = *named.elements.nodes.first()?;
            Some((declaration, NodeRef::new(parsed.arena.id(), file, binding)))
        })
        .expect("fixture has one named import")
}

fn import_specifier(parsed: &ParseResult, file: FileId, declaration: NodeRef) -> NodeRef {
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::ImportDeclaration(import) = &record.data else {
        panic!("fixture import declaration changed shape");
    };
    NodeRef::new(parsed.arena.id(), file, import.module_specifier)
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let name = parsed.arena.get(variable.name)?;
            let NodeData::Identifier(identifier) = &name.data else {
                return None;
            };
            (identifier.text == expected).then(|| {
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable
                        .initializer
                        .expect("fixture variable has an initializer"),
                )
            })
        })
        .unwrap_or_else(|| panic!("fixture has variable {expected}"))
}

fn make_context<'arena>(
    importer: &'arena ParseResult,
    target: &'arena ParseResult,
    importer_file: FileId,
    target_file: FileId,
) -> (CanonicalCheckerContext<'arena>, NodeRef) {
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
    let (declaration, binding) = import_nodes(importer, importer_file);
    let specifier = import_specifier(importer, importer_file, declaration);

    let mut binder = CanonicalBinder::new();
    for (file, parsed, name) in [
        (importer_file, importer, "\"/project/importer.ts\""),
        (target_file, target, "\"/project/target.ts\""),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                external_facts(name),
            )
            .unwrap();
    }
    for (file, parsed) in [(importer_file, importer), (target_file, target)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [
            (importer_file, &importer.arena),
            (target_file, &target.arena),
        ]
        .into_iter()
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
    .unwrap();
    (context, binding)
}

#[test]
fn importer_first_named_value_reads_are_exact_and_warm_stable() {
    let importer = parse_source_file(concat!(
        "import { value as renamed } from './target'; ",
        "const good: number = renamed; ",
        "const bad: string = renamed;",
    ));
    let target = parse_source_file("export const value: number = 1;");
    let importer_file = FileId::new(0);
    let target_file = FileId::new(1);
    let (mut context, _) = make_context(&importer, &target, importer_file, target_file);
    let target_source = context.source_file(target_file).unwrap();

    context.check_source_file(importer_file).unwrap();
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
    assert!(
        !context
            .store()
            .source_file_links(target_source)
            .is_some_and(|links| links.type_checked),
        "importer-first annotation lookup must not recursively check the target source"
    );

    context.check_source_file(importer_file).unwrap();
    assert_eq!(context.diagnostics().as_slice().len(), 1);
    context.check_source_file(target_file).unwrap();
    assert!(
        context
            .store()
            .source_file_links(target_source)
            .is_some_and(|links| links.type_checked)
    );
    assert_eq!(context.diagnostics().as_slice().len(), 1);

    let (mut target_first, _) = make_context(&importer, &target, importer_file, target_file);
    target_first.check_source_file(target_file).unwrap();
    target_first.check_source_file(importer_file).unwrap();
    assert_eq!(
        target_first
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
}

#[test]
fn importer_first_type_only_imports_check_annotations_and_reject_value_uses() {
    let importer = parse_source_file(concat!(
        "import type { User as LocalUser } from './target'; ",
        "const good: LocalUser = 1; ",
        "const bad: LocalUser = 'wrong'; ",
        "const invalid = LocalUser;",
    ));
    let target = parse_source_file("export type User = number;");
    let importer_file = FileId::new(10);
    let target_file = FileId::new(11);
    let (mut context, binding) = make_context(&importer, &target, importer_file, target_file);
    let alias = context
        .file(importer_file)
        .unwrap()
        .1
        .symbol(binding)
        .unwrap();
    let invalid_initializer = variable_initializer(&importer, importer_file, "invalid");
    let target_source = context.source_file(target_file).unwrap();

    context.check_source_file(importer_file).unwrap();

    let codes = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| diagnostic.diagnostic.code())
        .collect::<Vec<_>>();
    assert_eq!(codes, [2322, 1361]);
    let type_only_value_use = context
        .diagnostics()
        .as_slice()
        .iter()
        .find(|diagnostic| diagnostic.diagnostic.code() == 1361)
        .expect("type-only value use reports TS1361");
    assert_eq!(
        type_only_value_use.diagnostic.render().unwrap(),
        "'LocalUser' cannot be used as a value because it was imported using 'import type'."
    );
    let target_symbol = match context
        .store()
        .alias_symbol_links(alias)
        .expect("type import resolves its alias")
        .alias_target
    {
        AliasTargetState::Resolved(target) => target,
        state => panic!("type import alias is not resolved: {state:?}"),
    };
    assert!(context.store().value_symbol_links(alias).is_none());
    assert!(context.store().value_symbol_links(target_symbol).is_none());
    assert_eq!(
        context
            .store()
            .symbol_node_links(invalid_initializer)
            .and_then(|links| links.resolved_symbol),
        Some(alias)
    );
    let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
    assert_eq!(
        context
            .store()
            .type_node_links(invalid_initializer)
            .and_then(|links| links.resolved_type),
        Some(error_type)
    );
    assert!(
        !context
            .store()
            .source_file_links(target_source)
            .is_some_and(|links| links.type_checked),
        "importer-first type lookup must not recursively check the target source"
    );

    context.check_source_file(importer_file).unwrap();
    assert_eq!(context.diagnostics().as_slice().len(), 2);
}

#[test]
fn imported_values_feed_property_and_call_expression_verticals() {
    let importer = parse_source_file(concat!(
        "import { object, take } from './target'; ",
        "const copied: number = object.value; ",
        "const called: number = take(object.value);",
    ));
    let target = parse_source_file(concat!(
        "export const object: { value: number } = { value: 1 }; ",
        "export const take: (value: number) => number = value => value;",
    ));
    let importer_file = FileId::new(6);
    let target_file = FileId::new(7);
    let (mut context, _) = make_context(&importer, &target, importer_file, target_file);

    context.check_source_file(importer_file).unwrap();
    assert!(context.diagnostics().is_empty());
}

#[test]
fn unused_imports_resolve_without_eager_value_typing_or_partial_source_publication() {
    let importer = parse_source_file("import { value } from './target';");
    let target = parse_source_file("export const value = 1;");
    let importer_file = FileId::new(2);
    let target_file = FileId::new(3);
    let (mut context, binding) = make_context(&importer, &target, importer_file, target_file);
    let alias = context
        .file(importer_file)
        .unwrap()
        .1
        .symbol(binding)
        .unwrap();

    context.check_source_file(importer_file).unwrap();
    let alias_links = context.store().alias_symbol_links(alias).unwrap();
    assert!(matches!(
        alias_links.alias_target,
        AliasTargetState::Resolved(_)
    ));
    assert!(context.store().value_symbol_links(alias).is_none());
    assert!(context.diagnostics().is_empty());

    let rejected = parse_source_file(concat!(
        "import { value } from './target'; ",
        "class UnsupportedLater {}",
    ));
    let rejected_file = FileId::new(4);
    let rejected_target_file = FileId::new(5);
    let (mut rejected_context, rejected_binding) =
        make_context(&rejected, &target, rejected_file, rejected_target_file);
    let rejected_alias = rejected_context
        .file(rejected_file)
        .unwrap()
        .1
        .symbol(rejected_binding)
        .unwrap();
    assert!(matches!(
        rejected_context.check_source_file(rejected_file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Syntax { .. }
        ))
    ));
    assert!(
        rejected_context
            .store()
            .value_symbol_links(rejected_alias)
            .is_none()
    );
}

#[test]
fn merged_import_aliases_remain_a_typed_capability_boundary() {
    let importer = parse_source_file(concat!(
        "import { value } from './target'; ",
        "const value: number = 1;",
    ));
    let target = parse_source_file("export const value: number = 1;");
    let importer_file = FileId::new(8);
    let target_file = FileId::new(9);
    let (mut context, _) = make_context(&importer, &target, importer_file, target_file);

    assert!(matches!(
        context.check_source_file(importer_file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(_)
        ))
    ));
}
