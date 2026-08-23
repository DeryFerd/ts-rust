use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, SourceCheckError,
    UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

#[derive(Clone, Copy)]
struct Source<'arena> {
    parsed: &'arena ParseResult,
    file: FileId,
    path: &'static str,
}

#[derive(Clone, Copy)]
struct Route {
    source: usize,
    specifier: usize,
    target: usize,
}

fn external_facts(path: &str) -> CanonicalSourceFileFacts {
    CanonicalSourceFileFacts::new(
        EscapedName::source(path),
        CanonicalSourceLanguage::TypeScript,
        false,
        CanonicalModuleState::External,
    )
}

fn module_specifiers(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut specifiers = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let specifier = match &record.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                NodeData::ExportDeclaration(export) => export.module_specifier,
                _ => None,
            }?;
            Some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, specifier),
            ))
        })
        .collect::<Vec<_>>();
    specifiers.sort_by_key(|(start, _)| *start);
    specifiers
        .into_iter()
        .map(|(_, specifier)| specifier)
        .collect()
}

fn make_context<'arena>(
    sources: &[Source<'arena>],
    routes: &[Route],
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for source in sources {
        assert!(
            source.parsed.diagnostics.is_empty(),
            "{:?}",
            source.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &source.parsed.arena,
                source.parsed.source_file,
                source.file,
                external_facts(source.path),
            )
            .unwrap();
    }
    for source in sources {
        binder
            .bind_typescript_declaration_slice(&source.parsed.arena, source.file)
            .unwrap();
    }

    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        sources
            .iter()
            .map(|source| (source.file, &source.parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(routes.iter().map(|route| {
            let source = sources[route.source];
            let specifier = module_specifiers(source.parsed, source.file)[route.specifier];
            CanonicalModuleResolutionEntry::resolved(
                specifier,
                CanonicalResolvedModuleInput::new(
                    sources[route.target].file,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        })),
    )
    .unwrap()
}

fn named_import_binding(parsed: &ParseResult, file: FileId, local: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportSpecifier(specifier) = &record.data else {
                return None;
            };
            let name = parsed.arena.get(specifier.name)?;
            let NodeData::Identifier(identifier) = &name.data else {
                return None;
            };
            (identifier.text == local).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("fixture has named import binding {local}"))
}

fn default_import_binding(parsed: &ParseResult, file: FileId, local: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ImportClause(clause) = &record.data else {
                return None;
            };
            let name = parsed.arena.get(clause.name?)?;
            let NodeData::Identifier(identifier) = &name.data else {
                return None;
            };
            (identifier.text == local).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("fixture has default import binding {local}"))
}

fn named_reexport_binding(parsed: &ParseResult, file: FileId, exported: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ExportSpecifier(specifier) = &record.data else {
                return None;
            };
            let name = parsed.arena.get(specifier.name)?;
            let NodeData::Identifier(identifier) = &name.data else {
                return None;
            };
            (identifier.text == exported).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("fixture has named reexport binding {exported}"))
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .expect("fixture declaration has a bound symbol")
}

fn direct_export_symbol(
    context: &CanonicalCheckerContext<'_>,
    file: FileId,
    name: &str,
) -> SemanticSymbolId {
    let bound = context.file(file).unwrap().1;
    let module = bound
        .symbol(bound.source_file())
        .expect("external module has a source symbol");
    let exports = context
        .store()
        .symbol(module)
        .and_then(ts_binder::semantic::Symbol::exports)
        .expect("external module has an export table");
    context
        .store()
        .symbol_table(exports)
        .and_then(|exports| exports.get_source(name))
        .unwrap_or_else(|| panic!("fixture module exports {name}"))
}

fn assert_alias_chain(
    context: &CanonicalCheckerContext<'_>,
    alias: SemanticSymbolId,
    immediate: SemanticSymbolId,
    target: SemanticSymbolId,
    type_only_declaration: Option<NodeRef>,
) {
    let links = context
        .store()
        .alias_symbol_links(alias)
        .expect("resolved alias has links");
    assert_eq!(links.immediate_target, Some(immediate));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, type_only_declaration);
}

fn assert_lazy_alias_target(
    context: &CanonicalCheckerContext<'_>,
    alias: SemanticSymbolId,
    target: SemanticSymbolId,
    type_only_declaration: Option<NodeRef>,
) {
    let links = context
        .store()
        .alias_symbol_links(alias)
        .expect("transitively resolved alias has links");
    assert_eq!(
        links.immediate_target, None,
        "transitive resolution must not populate the distinct immediate-target cache"
    );
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, type_only_declaration);
}

fn source_is_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn repeated_namespace_imports_reuse_one_module_identity() {
    let consumer = parse_source_file(concat!(
        "import * as first from './module';\n",
        "import * as second from './module';\n",
        "const firstValue: number = first.value;\n",
        "const secondValue: number = second.value;\n",
    ));
    let module = parse_source_file("export const value: number = 1;\n");
    let files = [
        Source {
            parsed: &consumer,
            file: FileId::new(90),
            path: "\"/project/consumer.ts\"",
        },
        Source {
            parsed: &module,
            file: FileId::new(91),
            path: "\"/project/module.ts\"",
        },
    ];
    let mut context = make_context(
        &files,
        &[
            Route {
                source: 0,
                specifier: 0,
                target: 1,
            },
            Route {
                source: 0,
                specifier: 1,
                target: 1,
            },
        ],
    );

    context.check_source_file(files[0].file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(files[0].file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn local_enum_exports_follow_the_original_symbol_across_files() {
    let base = parse_source_file("const enum State { Ready }; export { State };");
    let barrel = parse_source_file("import { State } from './base'; export { State };");
    let base_file = FileId::new(92);
    let barrel_file = FileId::new(93);
    let sources = [
        Source {
            parsed: &base,
            file: base_file,
            path: "\"/project/base.ts\"",
        },
        Source {
            parsed: &barrel,
            file: barrel_file,
            path: "\"/project/barrel.ts\"",
        },
    ];
    let mut context = make_context(
        &sources,
        &[Route {
            source: 1,
            specifier: 0,
            target: 0,
        }],
    );
    let base_export = bound_symbol(&context, named_reexport_binding(&base, base_file, "State"));
    let import = bound_symbol(
        &context,
        named_import_binding(&barrel, barrel_file, "State"),
    );
    let barrel_export = bound_symbol(
        &context,
        named_reexport_binding(&barrel, barrel_file, "State"),
    );

    context.check_source_file(base_file).unwrap();
    context.check_source_file(barrel_file).unwrap();

    assert!(context.diagnostics().is_empty());
    assert!(source_is_checked(&context, base_file));
    assert!(source_is_checked(&context, barrel_file));
    let target = match context
        .store()
        .alias_symbol_links(base_export)
        .unwrap()
        .alias_target
    {
        AliasTargetState::Resolved(target) => target,
        other => panic!("expected an enum export alias, got {other:?}"),
    };
    assert_alias_chain(&context, base_export, target, target, None);
    assert_alias_chain(&context, import, base_export, target, None);
    assert_alias_chain(&context, barrel_export, import, target, None);

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(base_file).unwrap();
    context.recheck_source_file(barrel_file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn two_hop_renamed_value_and_function_reexports_are_exact_and_warm_stable() {
    let consumer = parse_source_file(concat!(
        "import { publicValue as value, publicTake as take } from './barrel-b'; ",
        "const good: number = take(value); ",
        "const bad: string = take(value);",
    ));
    let barrel_b = parse_source_file(concat!(
        "export { middleValue as publicValue, ",
        "middleTake as publicTake } from './barrel-a';",
    ));
    let barrel_a = parse_source_file(concat!(
        "export { originalValue as middleValue, ",
        "originalTake as middleTake } from './base';",
    ));
    let base = parse_source_file(concat!(
        "export const originalValue: number = 1; ",
        "export function originalTake(value: number): number { return value; }",
    ));
    let consumer_file = FileId::new(0);
    let public_barrel_file = FileId::new(1);
    let intermediate_barrel_file = FileId::new(2);
    let base_file = FileId::new(3);
    let sources = [
        Source {
            parsed: &consumer,
            file: consumer_file,
            path: "\"/project/consumer.ts\"",
        },
        Source {
            parsed: &barrel_b,
            file: public_barrel_file,
            path: "\"/project/barrel-b.ts\"",
        },
        Source {
            parsed: &barrel_a,
            file: intermediate_barrel_file,
            path: "\"/project/barrel-a.ts\"",
        },
        Source {
            parsed: &base,
            file: base_file,
            path: "\"/project/base.ts\"",
        },
    ];
    let mut context = make_context(
        &sources,
        &[
            Route {
                source: 0,
                specifier: 0,
                target: 1,
            },
            Route {
                source: 1,
                specifier: 0,
                target: 2,
            },
            Route {
                source: 2,
                specifier: 0,
                target: 3,
            },
        ],
    );

    let imported_value = bound_symbol(
        &context,
        named_import_binding(&consumer, consumer_file, "value"),
    );
    let imported_take = bound_symbol(
        &context,
        named_import_binding(&consumer, consumer_file, "take"),
    );
    let public_value = bound_symbol(
        &context,
        named_reexport_binding(&barrel_b, public_barrel_file, "publicValue"),
    );
    let public_take = bound_symbol(
        &context,
        named_reexport_binding(&barrel_b, public_barrel_file, "publicTake"),
    );
    let middle_value = bound_symbol(
        &context,
        named_reexport_binding(&barrel_a, intermediate_barrel_file, "middleValue"),
    );
    let middle_take = bound_symbol(
        &context,
        named_reexport_binding(&barrel_a, intermediate_barrel_file, "middleTake"),
    );
    let original_value = direct_export_symbol(&context, base_file, "originalValue");
    let original_take = direct_export_symbol(&context, base_file, "originalTake");

    context.check_source_file(consumer_file).unwrap();

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
    assert!(source_is_checked(&context, consumer_file));
    assert!(!source_is_checked(&context, public_barrel_file));
    assert!(!source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));

    assert_alias_chain(&context, imported_value, public_value, original_value, None);
    assert_alias_chain(&context, imported_take, public_take, original_take, None);
    assert_lazy_alias_target(&context, public_value, original_value, None);
    assert_lazy_alias_target(&context, public_take, original_take, None);
    assert_lazy_alias_target(&context, middle_value, original_value, None);
    assert_lazy_alias_target(&context, middle_take, original_take, None);

    context.check_source_file(public_barrel_file).unwrap();
    assert!(source_is_checked(&context, public_barrel_file));
    assert!(!source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));
    assert_alias_chain(&context, public_value, middle_value, original_value, None);
    assert_alias_chain(&context, public_take, middle_take, original_take, None);
    assert_lazy_alias_target(&context, middle_value, original_value, None);
    assert_lazy_alias_target(&context, middle_take, original_take, None);

    context.check_source_file(intermediate_barrel_file).unwrap();
    assert!(source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));
    assert_alias_chain(&context, middle_value, original_value, original_value, None);
    assert_alias_chain(&context, middle_take, original_take, original_take, None);

    context.check_source_file(base_file).unwrap();
    assert!(source_is_checked(&context, base_file));
    assert_eq!(context.diagnostics().as_slice().len(), 1);

    let warm_state = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    for file in [
        consumer_file,
        public_barrel_file,
        intermediate_barrel_file,
        base_file,
    ] {
        context.check_source_file(file).unwrap();
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        warm_state
    );
    assert_eq!(context.diagnostics().as_slice().len(), 1);
}

#[test]
#[allow(clippy::too_many_lines)]
fn transitive_type_only_reexport_markers_preserve_annotation_checking() {
    let consumer = parse_source_file(concat!(
        "import type { PublicModel as LocalModel } from './barrel-b'; ",
        "const good: LocalModel = { id: 1 }; ",
        "const bad: LocalModel = { id: 'wrong' };",
    ));
    let barrel_b =
        parse_source_file("export { IntermediateModel as PublicModel } from './barrel-a';");
    let barrel_a = parse_source_file("export type { Model as IntermediateModel } from './base';");
    let base = parse_source_file("export type Model = { id: number };");
    let consumer_file = FileId::new(10);
    let public_barrel_file = FileId::new(11);
    let intermediate_barrel_file = FileId::new(12);
    let base_file = FileId::new(13);
    let sources = [
        Source {
            parsed: &consumer,
            file: consumer_file,
            path: "\"/project/type-consumer.ts\"",
        },
        Source {
            parsed: &barrel_b,
            file: public_barrel_file,
            path: "\"/project/type-barrel-b.ts\"",
        },
        Source {
            parsed: &barrel_a,
            file: intermediate_barrel_file,
            path: "\"/project/type-barrel-a.ts\"",
        },
        Source {
            parsed: &base,
            file: base_file,
            path: "\"/project/type-base.ts\"",
        },
    ];
    let mut context = make_context(
        &sources,
        &[
            Route {
                source: 0,
                specifier: 0,
                target: 1,
            },
            Route {
                source: 1,
                specifier: 0,
                target: 2,
            },
            Route {
                source: 2,
                specifier: 0,
                target: 3,
            },
        ],
    );

    let consumer_binding = named_import_binding(&consumer, consumer_file, "LocalModel");
    let public_reexport_binding =
        named_reexport_binding(&barrel_b, public_barrel_file, "PublicModel");
    let intermediate_reexport_binding =
        named_reexport_binding(&barrel_a, intermediate_barrel_file, "IntermediateModel");
    let imported_model = bound_symbol(&context, consumer_binding);
    let public_model = bound_symbol(&context, public_reexport_binding);
    let intermediate_model = bound_symbol(&context, intermediate_reexport_binding);
    let model = direct_export_symbol(&context, base_file, "Model");

    context.check_source_file(consumer_file).unwrap();

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
    assert!(source_is_checked(&context, consumer_file));
    assert!(!source_is_checked(&context, public_barrel_file));
    assert!(!source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));
    assert_alias_chain(
        &context,
        imported_model,
        public_model,
        model,
        Some(consumer_binding),
    );
    assert_lazy_alias_target(
        &context,
        public_model,
        model,
        Some(intermediate_reexport_binding),
    );
    assert_lazy_alias_target(
        &context,
        intermediate_model,
        model,
        Some(intermediate_reexport_binding),
    );
    assert!(context.store().value_symbol_links(imported_model).is_none());
    assert!(context.store().value_symbol_links(public_model).is_none());
    assert!(
        context
            .store()
            .value_symbol_links(intermediate_model)
            .is_none()
    );

    context.check_source_file(public_barrel_file).unwrap();
    assert!(source_is_checked(&context, public_barrel_file));
    assert!(!source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));
    assert_alias_chain(
        &context,
        public_model,
        intermediate_model,
        model,
        Some(intermediate_reexport_binding),
    );
    assert_lazy_alias_target(
        &context,
        intermediate_model,
        model,
        Some(intermediate_reexport_binding),
    );

    context.check_source_file(intermediate_barrel_file).unwrap();
    assert!(source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));
    assert_alias_chain(
        &context,
        intermediate_model,
        model,
        model,
        Some(intermediate_reexport_binding),
    );

    context.check_source_file(base_file).unwrap();
    assert!(source_is_checked(&context, base_file));
    let warm_state = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    for file in [
        consumer_file,
        public_barrel_file,
        intermediate_barrel_file,
        base_file,
    ] {
        context.check_source_file(file).unwrap();
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        warm_state
    );
    assert_eq!(context.diagnostics().as_slice().len(), 1);
}

#[test]
#[allow(clippy::too_many_lines)]
fn mixed_default_and_named_imports_follow_renamed_default_reexports() {
    let consumer = parse_source_file(concat!(
        "import defaultLabel, { forwarded as value, default as namedLabel } from './barrel-b'; ",
        "const good: number = value; ",
        "const label: string = defaultLabel; ",
        "const repeated: string = namedLabel; ",
        "const bad: string = value;",
    ));
    let barrel_b =
        parse_source_file("export { default as forwarded, label as default } from './barrel-a';");
    let barrel_a = parse_source_file(concat!(
        "export { originalValue as default, ",
        "originalLabel as label } from './base';",
    ));
    let base = parse_source_file(concat!(
        "export const originalValue: number = 1; ",
        "export const originalLabel: string = 'ready';",
    ));
    let consumer_file = FileId::new(30);
    let public_barrel_file = FileId::new(31);
    let intermediate_barrel_file = FileId::new(32);
    let base_file = FileId::new(33);
    let sources = [
        Source {
            parsed: &consumer,
            file: consumer_file,
            path: "\"/project/default-consumer.ts\"",
        },
        Source {
            parsed: &barrel_b,
            file: public_barrel_file,
            path: "\"/project/default-barrel-b.ts\"",
        },
        Source {
            parsed: &barrel_a,
            file: intermediate_barrel_file,
            path: "\"/project/default-barrel-a.ts\"",
        },
        Source {
            parsed: &base,
            file: base_file,
            path: "\"/project/default-base.ts\"",
        },
    ];
    let mut context = make_context(
        &sources,
        &[
            Route {
                source: 0,
                specifier: 0,
                target: 1,
            },
            Route {
                source: 1,
                specifier: 0,
                target: 2,
            },
            Route {
                source: 2,
                specifier: 0,
                target: 3,
            },
        ],
    );
    let imported_default = bound_symbol(
        &context,
        default_import_binding(&consumer, consumer_file, "defaultLabel"),
    );
    let imported_named_default = bound_symbol(
        &context,
        named_import_binding(&consumer, consumer_file, "namedLabel"),
    );
    let imported_value = bound_symbol(
        &context,
        named_import_binding(&consumer, consumer_file, "value"),
    );
    let public_default = direct_export_symbol(&context, public_barrel_file, "default");
    let public_value = direct_export_symbol(&context, public_barrel_file, "forwarded");
    let middle_default = direct_export_symbol(&context, intermediate_barrel_file, "default");
    let middle_label = direct_export_symbol(&context, intermediate_barrel_file, "label");
    let original_value = direct_export_symbol(&context, base_file, "originalValue");
    let original_label = direct_export_symbol(&context, base_file, "originalLabel");

    context.check_source_file(consumer_file).unwrap();
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322]
    );
    assert!(!source_is_checked(&context, public_barrel_file));
    assert!(!source_is_checked(&context, intermediate_barrel_file));
    assert!(!source_is_checked(&context, base_file));
    assert_alias_chain(
        &context,
        imported_default,
        public_default,
        original_label,
        None,
    );
    assert_alias_chain(
        &context,
        imported_named_default,
        public_default,
        original_label,
        None,
    );
    assert_alias_chain(&context, imported_value, public_value, original_value, None);
    assert_lazy_alias_target(&context, public_default, original_label, None);
    assert_lazy_alias_target(&context, public_value, original_value, None);
    assert_lazy_alias_target(&context, middle_default, original_value, None);
    assert_lazy_alias_target(&context, middle_label, original_label, None);

    for file in [public_barrel_file, intermediate_barrel_file, base_file] {
        context.check_source_file(file).unwrap();
    }
    assert_alias_chain(&context, public_default, middle_label, original_label, None);
    assert_alias_chain(&context, public_value, middle_default, original_value, None);
    assert_alias_chain(
        &context,
        middle_default,
        original_value,
        original_value,
        None,
    );
    assert_alias_chain(&context, middle_label, original_label, original_label, None);

    let warm_state = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    for file in [
        consumer_file,
        public_barrel_file,
        intermediate_barrel_file,
        base_file,
    ] {
        context.check_source_file(file).unwrap();
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        warm_state
    );
    assert_eq!(context.diagnostics().as_slice().len(), 1);
}

#[test]
fn default_type_imports_keep_their_own_type_only_markers() {
    let consumer = parse_source_file(concat!(
        "import type DefaultModel from './barrel'; ",
        "import type { default as NamedModel } from './barrel'; ",
        "const good: DefaultModel = 1; ",
        "const bad: NamedModel = 'wrong'; ",
        "const invalid = DefaultModel;",
    ));
    let barrel = parse_source_file("export type { Model as default } from './base';");
    let base = parse_source_file("export type Model = number;");
    let consumer_file = FileId::new(40);
    let barrel_file = FileId::new(41);
    let base_file = FileId::new(42);
    let sources = [
        Source {
            parsed: &consumer,
            file: consumer_file,
            path: "\"/project/default-type-consumer.ts\"",
        },
        Source {
            parsed: &barrel,
            file: barrel_file,
            path: "\"/project/default-type-barrel.ts\"",
        },
        Source {
            parsed: &base,
            file: base_file,
            path: "\"/project/default-type-base.ts\"",
        },
    ];
    let mut context = make_context(
        &sources,
        &[
            Route {
                source: 0,
                specifier: 0,
                target: 1,
            },
            Route {
                source: 0,
                specifier: 1,
                target: 1,
            },
            Route {
                source: 1,
                specifier: 0,
                target: 2,
            },
        ],
    );
    let default_declaration = default_import_binding(&consumer, consumer_file, "DefaultModel");
    let named_declaration = named_import_binding(&consumer, consumer_file, "NamedModel");
    let export_declaration = named_reexport_binding(&barrel, barrel_file, "default");
    let imported_default = bound_symbol(&context, default_declaration);
    let imported_named = bound_symbol(&context, named_declaration);
    let exported_default = bound_symbol(&context, export_declaration);
    let model = direct_export_symbol(&context, base_file, "Model");

    context.check_source_file(consumer_file).unwrap();
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322, 1361]
    );
    assert_alias_chain(
        &context,
        imported_default,
        exported_default,
        model,
        Some(default_declaration),
    );
    assert_alias_chain(
        &context,
        imported_named,
        exported_default,
        model,
        Some(named_declaration),
    );
    assert_lazy_alias_target(&context, exported_default, model, Some(export_declaration));
    assert!(
        context
            .store()
            .value_symbol_links(imported_default)
            .is_none()
    );
    assert!(context.store().value_symbol_links(imported_named).is_none());

    context.check_source_file(barrel_file).unwrap();
    assert_alias_chain(
        &context,
        exported_default,
        model,
        model,
        Some(export_declaration),
    );
    context.check_source_file(base_file).unwrap();
    context.check_source_file(consumer_file).unwrap();
    assert_eq!(context.diagnostics().as_slice().len(), 2);
}

fn assert_module_reexport_shape_is_closed(source_text: &str) {
    let barrel = parse_source_file(source_text);
    let base = parse_source_file("export const value: number = 1;");
    let barrel_file = FileId::new(20);
    let base_file = FileId::new(21);
    let sources = [
        Source {
            parsed: &barrel,
            file: barrel_file,
            path: "\"/project/boundary.ts\"",
        },
        Source {
            parsed: &base,
            file: base_file,
            path: "\"/project/boundary-base.ts\"",
        },
    ];
    let mut context = make_context(
        &sources,
        &[Route {
            source: 0,
            specifier: 0,
            target: 1,
        }],
    );

    for _ in 0..2 {
        assert!(matches!(
            context.check_source_file(barrel_file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(_)
            ))
        ));
        assert!(!source_is_checked(&context, barrel_file));
        assert!(!source_is_checked(&context, base_file));
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn missing_default_star_and_namespace_reexports_remain_typed_boundaries() {
    assert_module_reexport_shape_is_closed("export { default as publicValue } from './base';");
    assert_module_reexport_shape_is_closed("export * from './base';");
    assert_module_reexport_shape_is_closed("export * as values from './base';");
}
