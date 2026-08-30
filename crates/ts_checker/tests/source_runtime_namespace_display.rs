use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, CanonicalTypeFormatFlags,
    SignatureId, TypeData, TypeId, signatures::SignatureFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.d.ts");
const LEGACY_DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts");

// These five files retain globalArrayAugmentationWithAmbientModuleReexportMerge1.ts.
const FOO: &str = concat!(
    "declare function foo(): void;\r\n",
    "declare namespace foo { export const items: string[]; }\r\n",
    "export = foo;\r\n\r\n",
);
const FIRST_MODULE: &str =
    "declare module 'mymod' { import * as foo from 'foo'; export { foo }; }\r\n\r\n";
const SECOND_MODULE: &str = "declare module 'mymod' { export const foo: number; }\r\n\r\n";
const AUGMENT: &str = concat!(
    "declare global {\r\n",
    "    interface Array<T> {\r\n",
    "        customMethod(): T;\r\n",
    "    }\r\n",
    "}\r\n",
    "export {};\r\n\r\n",
);
const INDEX: &str = concat!(
    "import * as foo from 'foo';\r\n",
    "const items = foo.items;\r\n",
    "const result: string = items.customMethod();\r\n\r\n",
    "const fresh: string[] = [];\r\n",
    "const result2: string = fresh.customMethod();\r\n",
);

struct TestSource<'arena> {
    parsed: &'arena ParseResult,
    file: FileId,
    path: &'static str,
    declaration: bool,
    library: bool,
    module_state: CanonicalModuleState,
}

fn context<'arena>(
    sources: &[TestSource<'arena>],
    entries: impl IntoIterator<Item = CanonicalModuleResolutionEntry>,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for source in sources {
        assert!(
            source.parsed.diagnostics.is_empty(),
            "{}: {:?}",
            source.path,
            source.parsed.diagnostics,
        );
        binder
            .bind_source_file_with_facts(
                &source.parsed.arena,
                source.parsed.source_file,
                source.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(source.path),
                    CanonicalSourceLanguage::TypeScript,
                    source.declaration,
                    source.library,
                    source.module_state,
                ),
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
        CanonicalCheckerOptions {
            no_emit: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("the source contains {kind:?}"))
}

fn declaration_name(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::FunctionDeclaration(data) => data.name.unwrap(),
        NodeData::ModuleDeclaration(data) => data.name,
        NodeData::NamespaceImport(data) => data.name,
        NodeData::VariableDeclaration(data) => data.name,
        NodeData::ExportSpecifier(data) => data.name,
        _ => panic!("the selected declaration has a name"),
    };
    NodeRef::new(declaration.arena, declaration.file, name)
}

fn function_body(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(function.name?)?.data else {
                return None;
            };
            (identifier.text == name)
                .then(|| NodeRef::new(parsed.arena.id(), file, function.body.unwrap()))
        })
        .unwrap_or_else(|| panic!("the source contains function {name}"))
}

fn owner(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(
            context
                .file(declaration.file)
                .unwrap()
                .1
                .symbol(declaration)
                .unwrap(),
        )
        .unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn import_route(
    parsed: &ParseResult,
    file: FileId,
    target: FileId,
) -> CanonicalModuleResolutionEntry {
    let import = node(parsed, file, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(data) = &parsed.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    CanonicalModuleResolutionEntry::resolved(
        NodeRef::new(import.arena, import.file, data.module_specifier),
        CanonicalResolvedModuleInput::new(
            target,
            CanonicalModuleResolutionMode::Esm,
            CanonicalModuleResolutionMode::Esm,
        ),
    )
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.global_types().clone(),
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
        context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect::<Vec<_>>(),
        context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let (arena, _) = context.file(file).unwrap();
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                        store.array_literal_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, record)| {
                (
                    symbol,
                    (
                        record.name().to_owned(),
                        record.flags(),
                        record.check_flags(),
                        record.parent(),
                        record.declarations().map(<[_]>::to_vec),
                        record.value_declaration(),
                        record.export_symbol(),
                    ),
                    [record.members(), record.exports()].map(|table| {
                        table.map(|table| {
                            (
                                table,
                                store
                                    .symbol_table(table)
                                    .unwrap()
                                    .iter()
                                    .map(|(name, member)| (name.to_owned(), member))
                                    .collect::<Vec<_>>(),
                            )
                        })
                    }),
                    (
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.alias_symbol_links(symbol).cloned(),
                        store.export_type_links(symbol).cloned(),
                        store.module_symbol_links(symbol).cloned(),
                        store.type_alias_links(symbol).cloned(),
                        store.symbol_reference_links(symbol).cloned(),
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn assert_callable(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    callable: TypeId,
    exported_name: &str,
) -> SignatureId {
    let declaration = node(parsed, file, SyntaxKind::FunctionDeclaration);
    let namespace = node(parsed, file, SyntaxKind::ModuleDeclaration);
    let symbol = owner(context, declaration);
    assert_eq!(owner(context, namespace), symbol);
    let record = context.store().symbol(symbol).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE
    );
    assert_eq!(
        record.declarations(),
        Some([declaration, namespace].as_slice())
    );
    assert_eq!(record.value_declaration(), Some(declaration));
    assert_eq!(value_type(context, symbol), callable);
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(symbol)
    );
    let exports = context
        .store()
        .symbol_table(record.exports().unwrap())
        .unwrap();
    let member = exports.get_source(exported_name).unwrap();
    assert_eq!(exports.len(), 1);
    assert_eq!(
        context.store().symbol(member).unwrap().parent(),
        Some(symbol)
    );
    let signature = context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("the original callable type remains an object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some([signature].as_slice())
    );
    let signature_record = context.store().signature(signature).unwrap();
    assert_eq!(signature_record.flags(), SignatureFlags::NONE);
    assert_eq!(signature_record.declaration(), Some(declaration));
    assert!(signature_record.parameters().is_empty());
    assert!(signature_record.type_parameters().is_empty());
    assert_eq!(signature_record.min_argument_count(), 0);
    assert_eq!(
        signature_record.resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().void_type),
    );
    signature
}

fn assert_display(
    context: &mut CanonicalCheckerContext<'_>,
    callable: TypeId,
    unqualified: &str,
    locations: &[(NodeRef, &str)],
) {
    let before = snapshot(context);
    for _ in 0..2 {
        assert_eq!(context.type_to_string(callable).unwrap(), unqualified);
        for &(location, expected) in locations {
            assert_eq!(
                context
                    .type_to_string_at_location_with_flags(
                        callable,
                        location,
                        CanonicalTypeFormatFlags::NO_TRUNCATION
                            | CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE,
                    )
                    .unwrap(),
                expected,
            );
        }
        assert_eq!(snapshot(context), before);
    }
}

#[allow(clippy::too_many_lines)] // Check the import owner, original callable, and both module properties together.
fn assert_import_namespace(
    context: &mut CanonicalCheckerContext<'_>,
    provider: (&ParseResult, FileId),
    importer: (&ParseResult, FileId),
    callable: TypeId,
) -> (SemanticSymbolId, TypeId) {
    let original = owner(
        context,
        node(provider.0, provider.1, SyntaxKind::FunctionDeclaration),
    );
    let import = node(importer.0, importer.1, SyntaxKind::ImportDeclaration);
    let binding = node(importer.0, importer.1, SyntaxKind::NamespaceImport);
    let name = declaration_name(importer.0, binding);
    let alias = owner(context, binding);
    let AliasTargetState::Resolved(module) = context.resolve_alias(alias).unwrap().target else {
        panic!("the namespace import resolves to its own module");
    };
    let module_type = context.get_type_at_location(name).unwrap();
    assert_eq!(context.get_symbol_at_location(name), Ok(Some(alias)));
    assert_ne!(alias, original);
    assert_ne!(module, original);
    assert_ne!(module, alias);
    assert_ne!(module_type, callable);
    assert_eq!(value_type(context, original), callable);
    assert_eq!(value_type(context, alias), module_type);
    assert_eq!(value_type(context, module), module_type);

    let item_declaration = node(provider.0, provider.1, SyntaxKind::VariableDeclaration);
    let item_name = declaration_name(provider.0, item_declaration);
    let item_symbol = owner(context, item_declaration);
    let item_type = context.get_type_at_location(item_name).unwrap();
    assert_eq!(
        context.get_symbol_at_location(item_name),
        Ok(Some(item_symbol))
    );
    let store = context.store();
    let alias_record = store.symbol(alias).unwrap();
    let NodeData::Identifier(identifier) = &importer.0.arena.get(name.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(alias_record.flags(), SymbolFlags::ALIAS);
    assert_eq!(
        alias_record.name().as_utf8(),
        Some(identifier.text.as_str())
    );
    assert_eq!(alias_record.declarations(), Some([binding].as_slice()));
    let alias_links = store.alias_symbol_links(alias).unwrap();
    assert_eq!(alias_links.immediate_target, Some(module));
    assert_eq!(alias_links.alias_target, AliasTargetState::Resolved(module));
    assert!(alias_links.type_only_declaration.is_none());
    let origin = store.export_type_links(module).unwrap();
    assert_eq!(origin.target, Some(original));
    assert_eq!(origin.originating_import, Some(import));

    let original_record = store.symbol(original).unwrap();
    let module_record = store.symbol(module).unwrap();
    assert_eq!(module_record.flags(), original_record.flags());
    assert_eq!(module_record.name(), original_record.name());
    assert_eq!(module_record.declarations(), original_record.declarations());
    assert_eq!(
        module_record.value_declaration(),
        original_record.value_declaration()
    );
    let exports = store
        .symbol_table(module_record.exports().unwrap())
        .unwrap();
    assert_eq!(exports.len(), 2);
    assert_eq!(exports.get_source("items"), Some(item_symbol));
    assert_eq!(
        store
            .symbol_table(original_record.exports().unwrap())
            .unwrap()
            .get_source("items"),
        Some(item_symbol),
    );
    let item_record = store.symbol(item_symbol).unwrap();
    assert_eq!(item_record.parent(), Some(original));
    assert_eq!(
        item_record.declarations(),
        Some([item_declaration].as_slice())
    );
    assert_eq!(item_record.value_declaration(), Some(item_declaration));
    let default_alias = exports.get(InternalSymbolName::Default.as_ref()).unwrap();
    let default_record = store.symbol(default_alias).unwrap();
    assert_eq!(default_record.flags(), SymbolFlags::ALIAS);
    assert_eq!(
        default_record.parent(),
        context
            .file(provider.1)
            .unwrap()
            .1
            .symbol(context.source_file(provider.1).unwrap().node_ref()),
    );
    let default_links = store.alias_symbol_links(default_alias).unwrap();
    assert_eq!(default_links.immediate_target, Some(original));
    assert_eq!(
        default_links.alias_target,
        AliasTargetState::Resolved(original)
    );
    assert!(default_links.type_only_declaration.is_none());

    let record = store.type_payload(module_type).unwrap();
    let TypeData::Object(object) = record.data() else {
        panic!("the namespace import retains its module object");
    };
    assert!(record.symbol().is_none());
    assert_eq!(object.structured.call_signature_count, 0);
    assert!(object.structured.signatures.is_none());
    let properties = object.structured.properties.as_deref().unwrap();
    let members = store
        .symbol_table(object.structured.members.unwrap())
        .unwrap();
    assert_eq!(properties.len(), 2);
    assert_eq!(members.len(), 2);
    for (key, expected) in [("default", callable), ("items", item_type)] {
        let property = members.get_source(key).unwrap();
        assert!(properties.contains(&property));
        assert_eq!(
            store.symbol(property).unwrap().flags(),
            SymbolFlags::PROPERTY
        );
        assert_eq!(value_type(context, property), expected);
    }
    let TypeData::TypeReference(reference) = store.type_payload(item_type).unwrap().data() else {
        panic!("the imported items retain their Array instance");
    };
    assert_eq!(
        reference.object.target,
        Some(context.global_types().array_type)
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some([store.intrinsic_bootstrap().unwrap().string_type].as_slice()),
    );
    (module, module_type)
}

#[test]
fn runtime_namespace_display_keeps_the_source_callable_and_export_table() {
    let parsed = parse_source_file(concat!(
        "declare function callable(): void; ",
        "declare namespace callable { export const value: string; }",
    ));
    let file = FileId::new(202_600);
    let declaration = node(&parsed, file, SyntaxKind::FunctionDeclaration);
    let namespace = node(&parsed, file, SyntaxKind::ModuleDeclaration);
    let names = [
        declaration_name(&parsed, declaration),
        declaration_name(&parsed, namespace),
    ];
    for query_first in [false, true] {
        let mut context = context(
            &[TestSource {
                parsed: &parsed,
                file,
                path: "\"/callable.ts\"",
                declaration: false,
                library: false,
                module_state: CanonicalModuleState::Script,
            }],
            [],
        );
        let symbol = owner(&context, declaration);
        assert!(context.store().value_symbol_links(symbol).is_none());
        assert!(context.store().signature_links(declaration).is_none());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        if !query_first {
            context.check_source_file(file).unwrap();
        }
        let callable = context.get_type_at_location(names[0]).unwrap();
        let signature = assert_callable(&context, &parsed, file, callable, "value");
        context.check_source_file(file).unwrap();
        for name in names {
            assert_eq!(context.get_type_at_location(name), Ok(callable));
            assert_eq!(context.get_symbol_at_location(name), Ok(Some(symbol)));
        }
        let warm = snapshot(&context);
        for _ in 0..2 {
            assert_display(
                &mut context,
                callable,
                "typeof callable",
                &[
                    (declaration, "typeof callable"),
                    (namespace, "typeof callable"),
                ],
            );
            context.recheck_source_file(file).unwrap();
            assert_eq!(
                assert_callable(&context, &parsed, file, callable, "value"),
                signature
            );
            for name in names {
                assert_eq!(context.get_type_at_location(name), Ok(callable));
                assert_eq!(context.get_symbol_at_location(name), Ok(Some(symbol)));
            }
            assert_eq!(snapshot(&context), warm);
        }
        assert!(context.diagnostics().is_empty());
    }
}

fn library_sources(parsed: &[ParseResult; 3]) -> [TestSource<'_>; 3] {
    let inputs = [
        ("\"/lib.es5.d.ts\"", 202_610),
        ("\"/lib.decorators.d.ts\"", 202_611),
        ("\"/lib.decorators.legacy.d.ts\"", 202_612),
    ];
    std::array::from_fn(|index| TestSource {
        parsed: &parsed[index],
        file: FileId::new(inputs[index].1),
        path: inputs[index].0,
        declaration: true,
        library: true,
        module_state: CanonicalModuleState::Script,
    })
}

#[test]
#[allow(clippy::too_many_lines)] // Compare both import scopes and both query orders in one checker.
fn runtime_namespace_display_uses_each_importers_value_scope() {
    let libraries = [ES5, DECORATORS, LEGACY_DECORATORS].map(parse_source_file);
    let provider = parse_source_file(FOO);
    let first = parse_source_file(concat!(
        "import * as renamed from 'foo'; const copied = renamed; ",
        "function typeOnly<renamed>(value: renamed): renamed { copied; return value; } ",
        "function hidden(renamed: number): number { copied; return renamed; }",
    ));
    let second = parse_source_file("import * as other from 'foo'; const copied = other;");
    let provider_file = FileId::new(202_613);
    let files = [FileId::new(202_614), FileId::new(202_615)];
    let importers = [&first, &second];
    let aliases = [
        node(&first, files[0], SyntaxKind::NamespaceImport),
        node(&second, files[1], SyntaxKind::NamespaceImport),
    ];
    let names = [
        declaration_name(&first, aliases[0]),
        declaration_name(&second, aliases[1]),
    ];
    let type_only_body = function_body(&first, files[0], "typeOnly");
    let hidden_body = function_body(&first, files[0], "hidden");
    for query_first in [false, true] {
        let mut sources = Vec::from(library_sources(&libraries));
        sources.push(TestSource {
            parsed: &provider,
            file: provider_file,
            path: "\"/node_modules/foo/index.d.ts\"",
            declaration: true,
            library: false,
            module_state: CanonicalModuleState::External,
        });
        for (index, parsed) in importers.into_iter().enumerate() {
            sources.push(TestSource {
                parsed,
                file: files[index],
                path: ["\"/first.ts\"", "\"/second.ts\""][index],
                declaration: false,
                library: false,
                module_state: CanonicalModuleState::External,
            });
        }
        let mut context = context(
            &sources,
            [
                import_route(&first, files[0], provider_file),
                import_route(&second, files[1], provider_file),
            ],
        );
        let declaration = node(&provider, provider_file, SyntaxKind::FunctionDeclaration);
        let original = owner(&context, declaration);
        assert!(context.store().value_symbol_links(original).is_none());
        let cold = query_first.then(|| context.get_type_at_location(names[0]).unwrap());
        for file in [provider_file, files[0], files[1]] {
            context.check_source_file(file).unwrap();
        }
        let callable = value_type(&context, original);
        let namespaces = [0, 1].map(|index| {
            assert_import_namespace(
                &mut context,
                (&provider, provider_file),
                (importers[index], files[index]),
                callable,
            )
        });
        assert_ne!(namespaces[0].0, namespaces[1].0);
        assert_ne!(namespaces[0].1, namespaces[1].1);
        if let Some(cold) = cold {
            assert_eq!(cold, namespaces[0].1);
        }
        assert_callable(&context, &provider, provider_file, callable, "items");
        let warm = snapshot(&context);
        for _ in 0..2 {
            assert_display(
                &mut context,
                callable,
                "typeof foo",
                &[
                    (aliases[0], "typeof renamed"),
                    (aliases[1], "typeof other"),
                    (type_only_body, "typeof renamed"),
                    (hidden_body, "typeof import(\"foo\")"),
                ],
            );
            for file in [files[1], provider_file, files[0]] {
                context.recheck_source_file(file).unwrap();
            }
            assert_callable(&context, &provider, provider_file, callable, "items");
            for index in [0, 1] {
                assert_eq!(
                    assert_import_namespace(
                        &mut context,
                        (&provider, provider_file),
                        (importers[index], files[index]),
                        callable,
                    ),
                    namespaces[index],
                );
            }
            assert_eq!(snapshot(&context), warm);
        }
        assert!(context.diagnostics().is_empty());
    }
}

fn assert_duplicate_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    first: (&ParseResult, FileId),
    second: (&ParseResult, FileId),
) {
    let first_name = declaration_name(first.0, node(first.0, first.1, SyntaxKind::ExportSpecifier));
    let second_name = declaration_name(
        second.0,
        node(second.0, second.1, SyntaxKind::VariableDeclaration),
    );
    assert_eq!(
        first
            .0
            .arena
            .get(first_name.node)
            .unwrap()
            .range
            .start
            .get(),
        62
    );
    assert_eq!(
        second
            .0
            .arena
            .get(second_name.node)
            .unwrap()
            .range
            .start
            .get(),
        38
    );
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, (name, related)) in diagnostics
        .iter()
        .zip([(first_name, second_name), (second_name, first_name)])
    {
        assert_eq!(diagnostic.node, Some(name));
        assert!(diagnostic.range_override.is_none());
        assert_eq!(diagnostic.diagnostic.code(), 2451);
        assert_eq!(diagnostic.diagnostic.arguments, ["foo"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Cannot redeclare block-scoped variable 'foo'."
        );
        let [other] = diagnostic.related_information.as_slice() else {
            panic!("each duplicate retains the other declaration");
        };
        assert_eq!(other.node, Some(related));
        assert_eq!(other.diagnostic.code(), 6203);
        assert_eq!(other.diagnostic.arguments, ["foo"]);
        assert_eq!(
            other.diagnostic.render().unwrap(),
            "'foo' was also declared here."
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the five original files, real libraries, diagnostics, and replay together.
fn original_array_augmentation_fixture_keeps_namespace_display_and_both_diagnostic_chains() {
    let libraries = [ES5, DECORATORS, LEGACY_DECORATORS].map(parse_source_file);
    let parsed = [FOO, FIRST_MODULE, SECOND_MODULE, AUGMENT, INDEX].map(parse_source_file);
    let files = [202_620, 202_621, 202_622, 202_623, 202_624].map(FileId::new);
    let paths = [
        "\"/node_modules/foo/index.d.ts\"",
        "\"/a.d.ts\"",
        "\"/b.d.ts\"",
        "\"/augment.ts\"",
        "\"/index.ts\"",
    ];
    let import = node(&parsed[4], files[4], SyntaxKind::NamespaceImport);
    let import_name = declaration_name(&parsed[4], import);
    for query_first in [false, true] {
        let mut sources = Vec::from(library_sources(&libraries));
        for (index, source) in parsed.iter().enumerate() {
            sources.push(TestSource {
                parsed: source,
                file: files[index],
                path: paths[index],
                declaration: index < 3,
                library: false,
                module_state: if index == 1 || index == 2 {
                    CanonicalModuleState::Script
                } else {
                    CanonicalModuleState::External
                },
            });
        }
        let mut context = context(
            &sources,
            [
                import_route(&parsed[1], files[1], files[0]),
                import_route(&parsed[4], files[4], files[0]),
            ],
        );
        assert!(context.global_type_diagnostics().next().is_none());
        let array_target = context.global_types().array_type;
        let globals = context.global_types().clone();
        let declaration = node(&parsed[0], files[0], SyntaxKind::FunctionDeclaration);
        let original = owner(&context, declaration);
        if query_first {
            // Prepare the real augmentation while keeping the callable and importer cold.
            context.check_source_file(files[3]).unwrap();
        }
        assert!(context.store().value_symbol_links(original).is_none());
        let cold = query_first.then(|| context.get_type_at_location(import_name).unwrap());
        for file in files {
            context.check_source_file(file).unwrap();
        }
        let callable = value_type(&context, original);
        let imported = assert_import_namespace(
            &mut context,
            (&parsed[0], files[0]),
            (&parsed[4], files[4]),
            callable,
        );
        if let Some(cold) = cold {
            assert_eq!(cold, imported.1);
        }
        assert_callable(&context, &parsed[0], files[0], callable, "items");
        assert_duplicate_diagnostics(&context, (&parsed[1], files[1]), (&parsed[2], files[2]));
        assert_eq!(context.global_types(), &globals);
        let namespace = node(&parsed[0], files[0], SyntaxKind::ModuleDeclaration);
        let NodeData::ExportAssignment(export) = &parsed[0]
            .arena
            .get(node(&parsed[0], files[0], SyntaxKind::ExportAssignment).node)
            .unwrap()
            .data
        else {
            unreachable!()
        };
        let exported = NodeRef::new(parsed[0].arena.id(), files[0], export.expression);
        let names = [
            declaration_name(&parsed[0], declaration),
            declaration_name(&parsed[0], namespace),
            exported,
        ];
        for name in names {
            assert_eq!(context.get_type_at_location(name), Ok(callable));
        }
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let mut checked_calls = 0;
        for (id, record) in parsed[4].arena.iter() {
            if record.kind == SyntaxKind::CallExpression {
                checked_calls += 1;
                assert_eq!(
                    context.get_type_at_location(NodeRef::new(parsed[4].arena.id(), files[4], id)),
                    Ok(string)
                );
            }
            let NodeData::VariableDeclaration(variable) = &record.data else {
                continue;
            };
            let NodeData::Identifier(name) = &parsed[4].arena.get(variable.name).unwrap().data
            else {
                continue;
            };
            if name.text == "items" || name.text == "fresh" {
                let type_ = value_type(
                    &context,
                    owner(&context, NodeRef::new(parsed[4].arena.id(), files[4], id)),
                );
                let TypeData::TypeReference(reference) =
                    context.store().type_payload(type_).unwrap().data()
                else {
                    panic!("the original Array instance is retained");
                };
                assert_eq!(reference.object.target, Some(array_target));
                assert_eq!(
                    reference.resolved_type_arguments.as_deref(),
                    Some([string].as_slice())
                );
                assert_eq!(context.type_to_string(type_).unwrap(), "string[]");
            }
        }
        assert_eq!(checked_calls, 2);
        let warm = snapshot(&context);
        for _ in 0..2 {
            assert_display(
                &mut context,
                callable,
                "typeof foo",
                &[
                    (declaration, "typeof foo"),
                    (namespace, "typeof foo"),
                    (import, "typeof foo"),
                ],
            );
            for file in files {
                context.recheck_source_file(file).unwrap();
            }
            assert_duplicate_diagnostics(&context, (&parsed[1], files[1]), (&parsed[2], files[2]));
            assert_callable(&context, &parsed[0], files[0], callable, "items");
            assert_eq!(
                assert_import_namespace(
                    &mut context,
                    (&parsed[0], files[0]),
                    (&parsed[4], files[4]),
                    callable,
                ),
                imported,
            );
            assert_eq!(snapshot(&context), warm);
        }
    }
}
