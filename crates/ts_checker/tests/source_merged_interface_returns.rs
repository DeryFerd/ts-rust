use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DOM: &str = include_str!("../../ts_bundled/libs/lib.dom.d.ts");
const ES5_FILE: FileId = FileId::new(200_210);
const DOM_FILE: FileId = FileId::new(200_211);
const ADDED_FILE: FileId = FileId::new(200_212);
const SOURCE_FILE: FileId = FileId::new(200_213);

fn context<'a>(
    es5: &'a ParseResult,
    dom: &'a ParseResult,
    added: &'a ParseResult,
    source: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (es5, ES5_FILE, "\"/lib/lib.es5.d.ts\"", true, true),
        (dom, DOM_FILE, "\"/lib/lib.dom.d.ts\"", true, true),
        (added, ADDED_FILE, "\"/project/added.d.ts\"", true, false),
        (source, SOURCE_FILE, "\"/project/main.ts\"", false, false),
    ];
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    library,
                    if declaration {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_implied_node_format(ModuleKind::EsNext),
            )
            .unwrap();
    }
    for (parsed, file, _, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(parsed, file, _, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            module_kind: ModuleKind::EsNext,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2025,
                ..CanonicalNameResolverOptions::default()
            },
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), SOURCE_FILE, node))
        })
        .unwrap()
}

fn merged_interface(
    checker: &CanonicalCheckerContext<'_>,
    name: &str,
    files: &[FileId],
) -> SemanticSymbolId {
    let store = checker.store();
    let raw = store
        .symbol_table(checker.globals())
        .unwrap()
        .get_source(name)
        .unwrap();
    let owner = store.get_merged_symbol(raw).unwrap();
    let record = store.symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
    );
    assert_eq!(
        record
            .declarations()
            .unwrap()
            .iter()
            .map(|node| node.file)
            .collect::<Vec<_>>(),
        files,
    );
    for &declaration in record.declarations().unwrap() {
        let bound = checker.file(declaration.file).unwrap().1;
        assert_eq!(
            store.get_merged_symbol(bound.symbol(declaration).unwrap()),
            Some(owner),
        );
        assert_eq!(
            bound.source_facts().unwrap().is_default_library(),
            declaration.file != ADDED_FILE,
        );
    }
    owner
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_source_checks(checker: &CanonicalCheckerContext<'_>, expected_checked: bool) {
    for file in [ES5_FILE, DOM_FILE, ADDED_FILE, SOURCE_FILE] {
        let source = checker.source_file(file).unwrap();
        let actual = checker
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked);
        assert_eq!(actual, expected_checked && file == SOURCE_FILE, "{file:?}");
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep identity, selected-member demand, and source replay together.
fn merged_import_meta_returns_keep_unread_library_and_user_members_cold() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let added = parse_source_file("interface ImportMeta { readonly marker: number; }");
    let source = parse_source_file(concat!(
        "function getMeta(): ImportMeta { return import.meta; }\n",
        "const path = getMeta().resolve('./entry.js');",
    ));
    for query_first in [false, true] {
        let mut checker = context(&es5, &dom, &added, &source);
        let owner = merged_interface(&checker, "ImportMeta", &[ES5_FILE, DOM_FILE, ADDED_FILE]);
        let members = checker.store().symbol(owner).unwrap().members().unwrap();
        let table = checker.store().symbol_table(members).unwrap();
        let selected = table.get_source("resolve").unwrap();
        let unread = [
            table.get_source("url").unwrap(),
            table.get_source("marker").unwrap(),
        ];
        for member in unread.into_iter().chain([selected]) {
            assert_eq!(checker.store().get_parent_of_symbol(member), Some(owner));
            assert!(
                checker
                    .store()
                    .value_symbol_links(member)
                    .and_then(|links| links.resolved_type)
                    .is_none(),
            );
        }
        let early = query_first.then(|| checker.get_declared_type_of_symbol(owner).unwrap());
        assert_source_checks(&checker, false);
        checker.check_source_file(SOURCE_FILE).unwrap();
        assert_source_checks(&checker, true);
        assert!(checker.diagnostics().is_empty());
        assert!(checker.global_type_diagnostics().next().is_none());

        let declaration = node(&source, SyntaxKind::FunctionDeclaration);
        let NodeData::FunctionDeclaration(function) =
            &source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let annotation = NodeRef::new(source.arena.id(), SOURCE_FILE, function.type_.unwrap());
        let function_name = NodeRef::new(source.arena.id(), SOURCE_FILE, function.name.unwrap());
        let function_owner = checker
            .file(SOURCE_FILE)
            .unwrap()
            .1
            .symbol(declaration)
            .unwrap();
        let function_owner = checker.store().get_merged_symbol(function_owner).unwrap();
        let callable = checker.get_type_at_location(function_name).unwrap();
        let signature = checker
            .store()
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let TypeData::Object(object) = checker.store().type_payload(callable).unwrap().data()
        else {
            panic!("getMeta must retain its callable type");
        };
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some(&[signature][..]),
        );
        assert_eq!(
            checker.store().type_payload(callable).unwrap().symbol(),
            Some(function_owner),
        );

        let meta = node(&source, SyntaxKind::MetaProperty);
        let access = node(&source, SyntaxKind::PropertyAccessExpression);
        let record = source.arena.get(access.node).unwrap();
        let NodeData::PropertyAccessExpression(property) = &record.data else {
            unreachable!();
        };
        let receiver = NodeRef::new(source.arena.id(), SOURCE_FILE, property.expression);
        let call = NodeRef::new(source.arena.id(), SOURCE_FILE, record.parent.unwrap());
        let instance = checker.get_type_at_location(meta).unwrap();
        assert!(early.is_none_or(|early| early == instance));
        assert_eq!(
            checker.store().type_payload(instance).unwrap().symbol(),
            Some(owner),
        );
        assert_eq!(checker.get_type_at_location(receiver), Ok(instance));
        assert_eq!(
            checker.get_return_type_of_signature(signature),
            Ok(instance)
        );
        assert_eq!(
            checker
                .store()
                .type_node_links(annotation)
                .unwrap()
                .resolved_type,
            Some(instance),
        );
        assert_eq!(checker.get_symbol_at_location(meta), Ok(Some(owner)));
        assert_eq!(checker.get_symbol_at_location(access), Ok(Some(selected)));
        assert!(
            checker
                .get_symbol_declarations(selected)
                .unwrap()
                .iter()
                .all(|node| node.file == DOM_FILE),
        );
        let method = checker.get_type_at_location(access).unwrap();
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(checker.get_type_at_location(call), Ok(string));

        let warm = counts(&checker);
        let signature_record = format!("{:?}", checker.store().signature(signature).unwrap());
        for _ in 0..3 {
            checker.recheck_source_file(SOURCE_FILE).unwrap();
            for member in unread {
                assert!(
                    checker
                        .store()
                        .value_symbol_links(member)
                        .and_then(|links| links.resolved_type)
                        .is_none(),
                );
            }
            let TypeData::Interface(interface) =
                checker.store().type_payload(instance).unwrap().data()
            else {
                panic!("ImportMeta must keep its interface identity");
            };
            assert!(!interface.declared_members_resolved);
            assert_eq!(
                checker.get_return_type_of_signature(signature),
                Ok(instance)
            );
            assert_eq!(checker.get_type_at_location(meta), Ok(instance));
            assert_eq!(checker.get_type_at_location(receiver), Ok(instance));
            assert_eq!(checker.get_type_at_location(access), Ok(method));
            assert_eq!(checker.get_type_at_location(call), Ok(string));
            assert_eq!(checker.get_symbol_at_location(access), Ok(Some(selected)));
            assert_eq!(
                format!("{:?}", checker.store().signature(signature).unwrap()),
                signature_record,
            );
            assert_eq!(counts(&checker), warm);
            assert_source_checks(&checker, true);
            assert!(checker.diagnostics().is_empty());
            assert!(checker.global_type_diagnostics().next().is_none());
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the exact return diagnostics and member state on each replay.
fn merged_library_interface_returns_check_real_scalar_and_object_bodies() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let added = parse_source_file("interface EventListenerOptions { marker: number; }");
    for (body, expected, location, needs_members) in [
        (
            "return 'bad';",
            Some("Type 'string' is not assignable to type 'EventListenerOptions'."),
            "return 'bad';",
            false,
        ),
        (
            "return { marker: 'bad' };",
            Some("Type 'string' is not assignable to type 'number'."),
            "marker",
            true,
        ),
        ("return { marker: 1 };", None, "", true),
    ] {
        let text =
            format!("export {{}}; function makeOptions(): EventListenerOptions {{ {body} }}");
        let source = parse_source_file(&text);
        let mut checker = context(&es5, &dom, &added, &source);
        let owner = merged_interface(&checker, "EventListenerOptions", &[DOM_FILE, ADDED_FILE]);
        let instance = checker.get_declared_type_of_symbol(owner).unwrap();
        let members = checker.store().symbol(owner).unwrap().members().unwrap();
        let table = checker.store().symbol_table(members).unwrap();
        let properties = [
            table.get_source("capture").unwrap(),
            table.get_source("marker").unwrap(),
        ];
        let raw_parents = properties.map(|property| {
            let parent = checker.store().symbol(property).unwrap().parent().unwrap();
            assert_ne!(parent, owner);
            assert_eq!(checker.store().get_merged_symbol(parent), Some(owner));
            parent
        });
        for property in properties {
            assert_eq!(checker.store().get_parent_of_symbol(property), Some(owner));
            assert!(
                checker
                    .store()
                    .value_symbol_links(property)
                    .and_then(|links| links.resolved_type)
                    .is_none(),
            );
        }
        assert_source_checks(&checker, false);
        checker
            .check_source_file(SOURCE_FILE)
            .unwrap_or_else(|error| panic!("{body}: {error:?}"));
        assert_source_checks(&checker, true);
        let declaration = node(&source, SyntaxKind::FunctionDeclaration);
        let signature = checker
            .store()
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(
            checker.get_return_type_of_signature(signature),
            Ok(instance)
        );
        let warm = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..3 {
            checker
                .recheck_source_file(SOURCE_FILE)
                .unwrap_or_else(|error| panic!("{body}: {error:?}"));
            if let Some(expected) = expected {
                let [diagnostic] = checker.diagnostics().as_slice() else {
                    panic!("{body}: expected one return diagnostic");
                };
                assert_eq!(diagnostic.diagnostic.code(), 2322, "{body}");
                assert_eq!(diagnostic.diagnostic.render().unwrap(), expected, "{body}");
                let node = diagnostic.node.unwrap();
                assert_eq!(node.file, SOURCE_FILE);
                let range = source.arena.get(node.node).unwrap().range;
                let start = usize::try_from(range.start.get()).unwrap();
                let end = usize::try_from(range.end.get()).unwrap();
                assert_eq!(text[start..end].trim(), location, "{body}",);
            } else {
                assert!(checker.diagnostics().is_empty(), "{body}");
            }
            if needs_members {
                let TypeData::Interface(interface) =
                    checker.store().type_payload(instance).unwrap().data()
                else {
                    panic!("EventListenerOptions must keep its interface identity");
                };
                assert!(interface.declared_members_resolved, "{body}");
                for property in properties {
                    assert!(
                        checker
                            .store()
                            .value_symbol_links(property)
                            .and_then(|links| links.resolved_type)
                            .is_some(),
                        "{body}",
                    );
                }
            }
            assert_eq!(
                checker.get_return_type_of_signature(signature),
                Ok(instance)
            );
            assert_eq!(
                checker
                    .store()
                    .signature_links(declaration)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(signature),
            );
            for (property, raw_parent) in properties.into_iter().zip(raw_parents) {
                assert_eq!(
                    checker.store().symbol(property).unwrap().parent(),
                    Some(raw_parent),
                );
                assert_eq!(checker.store().get_parent_of_symbol(property), Some(owner));
            }
            assert_eq!(checker.get_declared_type_of_symbol(owner), Ok(instance));
            assert_eq!(counts(&checker), warm, "{body}");
            assert_eq!(checker.diagnostics(), &diagnostics, "{body}");
            assert_source_checks(&checker, true);
            assert!(checker.global_type_diagnostics().next().is_none(), "{body}");
        }
    }
}
