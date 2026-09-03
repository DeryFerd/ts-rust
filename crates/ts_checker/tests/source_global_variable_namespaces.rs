use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_parser::{ParseResult, parse_source_file};

const BASE: &str = "declare var Runtime: Runtime.Options;\ndeclare namespace Runtime { interface Options { port: number; } }\n";
const CONTRIBUTION: &str = "declare var Runtime: Runtime.Options;\ndeclare namespace Runtime { interface Options { label: string; } }\n";
const AUGMENTATION: &str = "export {};\ndeclare global {\nvar Runtime: Runtime.Options;\nnamespace Runtime { interface Options { label: string; } }\n}\n";
const CONSUMER: &str = "export {};\ntype Settings = Runtime.Options;\nclass Reader {\nread(): number { return Runtime.port; }\nlabel(): string { return Runtime.label; }\n}\nconst port: number = Runtime.port;\nconst label: string = Runtime.label;\nconst same: Settings = Runtime;\nconst wrong: string = Runtime.port;\n";
const SHADOW: &str = "export {};\nconst Runtime = { port: 'local' };\nclass Reader { read(): string { return Runtime.port; } }\nconst wrong: number = Runtime.port;\n";

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &[ParseResult],
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        parsed
            .iter()
            .enumerate()
            .flat_map(|(file, parsed)| {
                parsed.arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(parsed.arena.id(), FileId::new(file as u32), id);
                    (
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        checker.diagnostics().clone(),
    )
}

fn check(extra: &str, source: &str, shadow: bool) {
    let inputs = [
        (
            "/lib.es5.d.ts",
            include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
        ),
        (
            "/lib.decorators.d.ts",
            include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
        ),
        (
            "/lib.decorators.legacy.d.ts",
            include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
        ),
        ("/base.d.ts", BASE),
        ("/extra.d.ts", extra),
        ("/consumer.ts", source),
    ];
    let parsed = inputs
        .iter()
        .map(|(_, source)| parse_source_file(source))
        .collect::<Vec<_>>();
    let consumer = FileId::new(5);
    for query_first in [false, true] {
        let mut binder = CanonicalBinder::new();
        for (file, ((path, text), parsed)) in inputs.iter().zip(&parsed).enumerate() {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FileId::new(file as u32),
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        file != 5,
                        file < 3,
                        if text.starts_with("export") {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in parsed.iter().enumerate() {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FileId::new(file as u32))
                .unwrap();
        }
        let mut checker = CanonicalCheckerContext::new(
            binder.finish(),
            parsed
                .iter()
                .enumerate()
                .map(|(file, parsed)| (FileId::new(file as u32), &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                no_implicit_any: true,
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(checker.diagnostics().is_empty());
        let globals = checker.store().intrinsic_bootstrap().unwrap().globals;
        let raw = checker
            .store()
            .symbol_table(globals)
            .unwrap()
            .get_source("Runtime")
            .unwrap();
        let global = checker.store().get_merged_symbol(raw).unwrap();
        let record = checker.store().symbol(global).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
                | SymbolFlags::NAMESPACE_MODULE
                | SymbolFlags::TRANSIENT
        );
        let declarations = record.declarations().unwrap().to_vec();
        assert_eq!(declarations.len(), 4);
        assert_eq!(
            declarations
                .iter()
                .map(|node| node.file)
                .collect::<Vec<_>>(),
            [
                FileId::new(3),
                FileId::new(3),
                FileId::new(4),
                FileId::new(4)
            ]
        );
        let selected = record.value_declaration().unwrap();
        assert_eq!(selected, declarations[0]);
        let NodeData::VariableDeclaration(variable) =
            &parsed[3].arena.get(selected.node).unwrap().data
        else {
            panic!("selected variable")
        };
        let annotation = NodeRef::new(selected.arena, selected.file, variable.type_.unwrap());
        let exports = record.exports().unwrap();
        let table = checker.store().symbol_table(exports).unwrap();
        assert_eq!(table.len(), 1);
        let options = checker
            .store()
            .get_merged_symbol(table.get_source("Options").unwrap())
            .unwrap();
        let options_record = checker.store().symbol(options).unwrap();
        assert!(options_record.flags().contains(SymbolFlags::INTERFACE));
        assert_eq!(options_record.declarations().unwrap().len(), 2);
        assert_eq!(
            checker
                .store()
                .get_merged_symbol(options_record.parent().unwrap()),
            Some(global)
        );
        for &declaration in options_record.declarations().unwrap() {
            let (_, bound) = checker.file(declaration.file).unwrap();
            assert_eq!(
                checker
                    .store()
                    .get_merged_symbol(bound.symbol(declaration).unwrap()),
                Some(options)
            );
        }
        for declaration in &declarations {
            let (_, bound) = checker.file(declaration.file).unwrap();
            assert_eq!(
                checker
                    .store()
                    .get_merged_symbol(bound.symbol(*declaration).unwrap()),
                Some(global)
            );
        }

        let source_ast = &parsed[5];
        let mut reads = source_ast
            .arena
            .iter()
            .filter_map(|(id, node)| {
                let NodeData::PropertyAccessExpression(property) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(receiver) =
                    &source_ast.arena.get(property.expression)?.data
                else {
                    return None;
                };
                let NodeData::Identifier(name) = &source_ast.arena.get(property.name)?.data else {
                    return None;
                };
                (receiver.text == "Runtime").then_some((
                    NodeRef::new(source_ast.arena.id(), consumer, property.expression),
                    NodeRef::new(source_ast.arena.id(), consumer, id),
                    name.text.as_str(),
                ))
            })
            .collect::<Vec<_>>();
        reads.sort_by_key(|(_, node, _)| source_ast.arena.get(node.node).unwrap().range.start);
        assert_eq!(reads.len(), if shadow { 2 } else { 5 });
        if query_first {
            checker.get_type_at_location(reads[0].1).unwrap();
        }
        checker.check_source_file(consumer).unwrap();
        let owner = checker.get_symbol_at_location(reads[0].0).unwrap().unwrap();
        assert_eq!(owner == global, !shadow);
        for &(receiver, property, name) in &reads {
            assert_eq!(checker.get_symbol_at_location(receiver), Ok(Some(owner)));
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let expected = if shadow || name == "label" {
                bootstrap.string_type
            } else {
                bootstrap.number_type
            };
            assert_eq!(checker.get_type_at_location(property), Ok(expected));
        }
        let qualified = if !shadow {
            let value = checker.get_type_at_location(reads[0].0).unwrap();
            assert_eq!(checker.get_type_at_location(annotation), Ok(value));
            let qualified = source_ast
                .arena
                .iter()
                .find_map(|(_, node)| {
                    let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                        return None;
                    };
                    Some(NodeRef::new(source_ast.arena.id(), consumer, alias.type_))
                })
                .unwrap();
            assert_eq!(checker.get_type_at_location(qualified), Ok(value));
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(global)
                    .unwrap()
                    .resolved_type,
                Some(value)
            );
            Some((qualified, value))
        } else {
            None
        };
        let [error] = checker.diagnostics().as_slice() else {
            panic!("one assignment error: {:?}", checker.diagnostics())
        };
        assert_eq!(error.diagnostic.code(), 2322);
        assert_eq!(
            error.diagnostic.render().unwrap(),
            if shadow {
                "Type 'string' is not assignable to type 'number'."
            } else {
                "Type 'number' is not assignable to type 'string'."
            }
        );
        let error_node = error.node.unwrap();
        let location = source_ast.arena.get(error_node.node).unwrap();
        assert_eq!(error_node.file, consumer);
        assert_eq!(location.kind, SyntaxKind::Identifier);
        assert_eq!(
            location.range.start.get() as usize,
            source.find("wrong").unwrap()
        );
        assert_eq!(location.range.end.get() - location.range.start.get(), 5);
        assert!(error.range_override.is_none());
        assert!(error.related_information.is_empty());
        let global_record = checker.store().symbol(global).cloned();
        let options_record = checker.store().symbol(options).cloned();
        let exports = checker.store().symbol_table(exports).cloned();
        let value_links = checker.store().value_symbol_links(global).cloned();
        let warm = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.recheck_source_file(consumer).unwrap();
            for &(_, property, _) in &reads {
                checker.get_type_at_location(property).unwrap();
            }
            if let Some((qualified, value)) = qualified {
                assert_eq!(checker.get_type_at_location(reads[0].0), Ok(value));
                assert_eq!(checker.get_type_at_location(annotation), Ok(value));
                assert_eq!(checker.get_type_at_location(qualified), Ok(value));
            }
            assert_eq!(
                checker.store().value_symbol_links(global),
                value_links.as_ref()
            );
            assert_eq!(checker.store().symbol(global), global_record.as_ref());
            assert_eq!(checker.store().symbol(options), options_record.as_ref());
            assert_eq!(
                checker
                    .store()
                    .symbol_table(global_record.as_ref().unwrap().exports().unwrap()),
                exports.as_ref()
            );
            assert_eq!(snapshot(&checker, &parsed), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn variable_namespace_scripts_keep_value_types_exports_and_replay() {
    check(CONTRIBUTION, CONSUMER, false);
}

#[test]
fn variable_namespace_augmentations_keep_the_selected_value() {
    check(AUGMENTATION, CONSUMER, false);
}

#[test]
fn variable_namespace_globals_do_not_capture_local_shadows() {
    check(AUGMENTATION, SHADOW, true);
}
