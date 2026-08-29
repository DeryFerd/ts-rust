use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DOM: &str = include_str!("../../ts_bundled/libs/lib.dom.d.ts");
const SOURCE_FILE: FileId = FileId::new(2);

fn context<'arena>(
    es5: &'arena ParseResult,
    dom: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (es5, FileId::new(0), "\"/lib.es5.d.ts\"", true),
        (dom, FileId::new(1), "\"/lib.dom.d.ts\"", true),
        (source, SOURCE_FILE, "\"/main.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_implied_node_format(ModuleKind::EsNext),
            )
            .unwrap();
    }
    for (parsed, file, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(parsed, file, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            module_kind: ModuleKind::EsNext,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2025,
                ..CanonicalNameResolverOptions::default()
            },
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

#[test]
fn import_meta_method_demand_keeps_unread_dom_property_cold() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let source = parse_source_file("const path = import.meta.resolve('./entry.js');");
    let mut checker = context(&es5, &dom, &source);
    checker.check_source_file(SOURCE_FILE).unwrap();
    assert!(checker.diagnostics().as_slice().is_empty());
    assert!(checker.global_type_diagnostics().next().is_none());

    let meta = node(&source, SyntaxKind::MetaProperty);
    let call = node(&source, SyntaxKind::CallExpression);
    let access = node(&source, SyntaxKind::PropertyAccessExpression);
    let meta_type = checker.get_type_at_location(meta).unwrap();
    let global = checker.get_symbol_at_location(meta).unwrap().unwrap();
    let members = checker.store().symbol(global).unwrap().members().unwrap();
    let table = checker.store().symbol_table(members).unwrap();
    let url = table.get_source("url").unwrap();
    let method = table.get_source("resolve").unwrap();
    assert!(
        checker
            .store()
            .value_symbol_links(url)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    assert!(
        checker
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .is_some()
    );
    assert_eq!(checker.get_symbol_at_location(access), Ok(Some(method)));
    let declarations = checker.get_symbol_declarations(method).unwrap();
    assert!(!declarations.is_empty());
    assert!(
        declarations
            .iter()
            .all(|declaration| declaration.file == FileId::new(1))
    );
    let string = checker.get_type_at_location(call).unwrap();
    assert_eq!(checker.type_to_string(string).unwrap(), "string");

    let NodeData::MetaProperty(meta_data) = &source.arena.get(meta.node).unwrap().data else {
        unreachable!();
    };
    let name = NodeRef::new(source.arena.id(), SOURCE_FILE, meta_data.name);
    let wrapper_property = checker.get_symbol_at_location(name).unwrap().unwrap();
    checker.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(checker.get_type_at_location(call), Ok(string));
    assert_eq!(checker.get_type_at_location(meta), Ok(meta_type));
    assert_eq!(checker.get_symbol_at_location(access), Ok(Some(method)));
    assert_eq!(
        checker.get_symbol_at_location(name),
        Ok(Some(wrapper_property))
    );
    assert!(
        checker
            .store()
            .value_symbol_links(url)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    assert!(checker.diagnostics().as_slice().is_empty());
}

#[test]
fn import_meta_literal_element_reads_the_real_dom_property() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    let source = parse_source_file("const url = import.meta['url'];");
    let mut checker = context(&es5, &dom, &source);
    checker.check_source_file(SOURCE_FILE).unwrap();
    assert!(checker.diagnostics().as_slice().is_empty());
    assert!(checker.global_type_diagnostics().next().is_none());

    let meta = node(&source, SyntaxKind::MetaProperty);
    let element = node(&source, SyntaxKind::ElementAccessExpression);
    let global = checker.get_symbol_at_location(meta).unwrap().unwrap();
    let members = checker.store().symbol(global).unwrap().members().unwrap();
    let table = checker.store().symbol_table(members).unwrap();
    let url = table.get_source("url").unwrap();
    let method = table.get_source("resolve").unwrap();
    let string = checker.get_type_at_location(element).unwrap();
    assert_eq!(checker.type_to_string(string).unwrap(), "string");
    assert_eq!(checker.get_symbol_at_location(element), Ok(Some(url)));
    assert!(
        checker
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    checker.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(checker.get_type_at_location(element), Ok(string));
    assert_eq!(checker.get_symbol_at_location(element), Ok(Some(url)));
    assert!(
        checker
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    assert!(checker.diagnostics().as_slice().is_empty());
}

#[test]
#[allow(clippy::too_many_lines)] // Keep cold and replay checks on the same receiver variants.
fn import_meta_method_aliases_keep_selected_dom_member_identity_on_replay() {
    let es5 = parse_source_file(ES5);
    let dom = parse_source_file(DOM);
    for (case, text) in [
        (
            "plain alias",
            "const meta = import.meta; const path = meta.resolve('./entry.js');",
        ),
        (
            "parenthesized alias",
            "const meta = import.meta; const path = (meta).resolve('./entry.js');",
        ),
        (
            "returned receiver",
            concat!(
                "function getMeta(): ImportMeta { return import.meta; }\n",
                "const path = getMeta().resolve('./entry.js');",
            ),
        ),
        (
            "class local alias",
            concat!(
                "class Reader { read(): string {\n",
                "const meta = import.meta;\n",
                "return meta.resolve('./entry.js');\n",
                "} }",
            ),
        ),
        (
            "class captured alias",
            concat!(
                "const sourceMeta = import.meta;\n",
                "class Reader { read(): string {\n",
                "const meta = sourceMeta;\n",
                "return meta.resolve('./entry.js');\n",
                "} }",
            ),
        ),
    ] {
        let source = parse_source_file(text);
        let mut checker = context(&es5, &dom, &source);
        let global = checker
            .store()
            .symbol_table(checker.globals())
            .unwrap()
            .get_source("ImportMeta")
            .unwrap();
        let global = checker.store().get_merged_symbol(global).unwrap();
        let members = checker.store().symbol(global).unwrap().members().unwrap();
        let table = checker.store().symbol_table(members).unwrap();
        let url = table.get_source("url").unwrap();
        let method = table.get_source("resolve").unwrap();
        for member in [url, method] {
            assert!(
                checker
                    .store()
                    .value_symbol_links(member)
                    .and_then(|links| links.resolved_type)
                    .is_none(),
                "{case}: member must start cold",
            );
        }

        checker
            .check_source_file(SOURCE_FILE)
            .unwrap_or_else(|error| panic!("{case}: {error:?}"));
        assert!(checker.diagnostics().as_slice().is_empty(), "{case}");
        assert!(checker.global_type_diagnostics().next().is_none(), "{case}");
        assert!(
            checker
                .store()
                .value_symbol_links(url)
                .and_then(|links| links.resolved_type)
                .is_none(),
            "{case}: checking must leave unread url cold",
        );

        let meta = node(&source, SyntaxKind::MetaProperty);
        let access = node(&source, SyntaxKind::PropertyAccessExpression);
        let access_record = source.arena.get(access.node).unwrap();
        let NodeData::PropertyAccessExpression(access_data) = &access_record.data else {
            unreachable!();
        };
        let receiver = NodeRef::new(source.arena.id(), SOURCE_FILE, access_data.expression);
        let call = NodeRef::new(
            source.arena.id(),
            SOURCE_FILE,
            access_record.parent.unwrap(),
        );
        let NodeData::CallExpression(call_data) = &source.arena.get(call.node).unwrap().data else {
            panic!("{case}: selected property must be the method callee");
        };
        assert_eq!(call_data.expression, access.node, "{case}");
        let method_type = checker
            .store()
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap_or_else(|| panic!("{case}: checking must resolve the selected method"));
        let meta_type = checker.get_type_at_location(meta).unwrap();
        assert_eq!(
            checker.get_symbol_at_location(meta),
            Ok(Some(global)),
            "{case}"
        );
        assert_eq!(
            checker.get_type_at_location(receiver),
            Ok(meta_type),
            "{case}"
        );
        assert_eq!(
            checker.get_type_at_location(access),
            Ok(method_type),
            "{case}"
        );
        assert_eq!(
            checker.get_symbol_at_location(access),
            Ok(Some(method)),
            "{case}"
        );
        let declarations = checker.get_symbol_declarations(method).unwrap();
        assert!(!declarations.is_empty(), "{case}");
        assert!(
            declarations
                .iter()
                .all(|declaration| declaration.file == FileId::new(1)),
            "{case}",
        );
        let string = checker.get_type_at_location(call).unwrap();
        assert_eq!(checker.type_to_string(string).unwrap(), "string", "{case}");
        let NodeData::MetaProperty(meta_data) = &source.arena.get(meta.node).unwrap().data else {
            unreachable!();
        };
        let name = NodeRef::new(source.arena.id(), SOURCE_FILE, meta_data.name);
        let wrapper_property = checker.get_symbol_at_location(name).unwrap().unwrap();
        let warm_counts = (
            checker.store().type_len(),
            checker.store().symbol_len(),
            checker.store().signature_len(),
        );
        for replay in 0..3 {
            checker
                .recheck_source_file(SOURCE_FILE)
                .unwrap_or_else(|error| panic!("{case}, replay {replay}: {error:?}"));
            assert_eq!(checker.get_type_at_location(call), Ok(string), "{case}");
            assert_eq!(checker.get_type_at_location(meta), Ok(meta_type), "{case}");
            assert_eq!(
                checker.get_type_at_location(receiver),
                Ok(meta_type),
                "{case}"
            );
            assert_eq!(
                checker.get_type_at_location(access),
                Ok(method_type),
                "{case}"
            );
            assert_eq!(
                checker.get_symbol_at_location(access),
                Ok(Some(method)),
                "{case}"
            );
            assert_eq!(
                checker.get_symbol_at_location(name),
                Ok(Some(wrapper_property)),
                "{case}",
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(method)
                    .and_then(|links| links.resolved_type),
                Some(method_type),
                "{case}",
            );
            assert!(
                checker
                    .store()
                    .value_symbol_links(url)
                    .and_then(|links| links.resolved_type)
                    .is_none(),
                "{case}: unread url must stay cold",
            );
            assert_eq!(
                (
                    checker.store().type_len(),
                    checker.store().symbol_len(),
                    checker.store().signature_len(),
                ),
                warm_counts,
                "{case}, replay {replay}",
            );
            assert!(checker.diagnostics().as_slice().is_empty(), "{case}");
            assert!(checker.global_type_diagnostics().next().is_none(), "{case}");
        }
    }
}
