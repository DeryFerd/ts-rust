use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_parser::parse_source_file;

const BASE: &str = concat!(
    "declare namespace Application { interface Options { port: number; } }\n",
    "declare var configuration: Application.Options;\n",
);
const CONSUMER: &str = concat!(
    "export {};\n",
    "class Reader { read(): number { return configuration.port; } }\n",
    "const wrong: string = configuration.port;\n",
);

fn check_global_values(extra: &str, source: &str, shadow: bool) {
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
        .map(|(_, text)| parse_source_file(text))
        .collect::<Vec<_>>();
    let consumer = FileId::new(5);
    for query_first in [false, true] {
        let mut binder = CanonicalBinder::new();
        for (index, ((path, text), parsed)) in inputs.iter().zip(&parsed).enumerate() {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FileId::new(index as u32),
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        index != 5,
                        index < 3,
                        if text.starts_with("export") {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
        }
        for (index, parsed) in parsed.iter().enumerate() {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FileId::new(index as u32))
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            parsed
                .iter()
                .enumerate()
                .map(|(index, parsed)| (FileId::new(index as u32), &parsed.arena))
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
        assert!(context.diagnostics().is_empty());
        let globals = context.store().intrinsic_bootstrap().unwrap().globals;
        let global = context
            .store()
            .symbol_table(globals)
            .unwrap()
            .get_source("configuration")
            .unwrap();
        let global = context.store().get_merged_symbol(global).unwrap();
        let record = context.store().symbol(global).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
        );
        let declarations = record.declarations().unwrap().to_vec();
        assert_eq!(declarations.len(), 2);
        assert_eq!(declarations[0].file, FileId::new(3));
        assert_eq!(declarations[1].file, FileId::new(4));
        let selected = record.value_declaration().unwrap();
        assert_eq!(selected, declarations[0]);

        let source_ast = &parsed[5];
        let mut reads = source_ast
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) =
                    &source_ast.arena.get(access.expression)?.data
                else {
                    return None;
                };
                (identifier.text == "configuration").then_some((
                    NodeRef::new(source_ast.arena.id(), consumer, access.expression),
                    NodeRef::new(source_ast.arena.id(), consumer, id),
                ))
            })
            .collect::<Vec<_>>();
        reads.sort_by_key(|(_, property)| source_ast.arena.get(property.node).unwrap().range.start);
        assert_eq!(reads.len(), 2);
        if query_first {
            context.get_type_at_location(reads[0].1).unwrap();
        }
        context.check_source_file(consumer).unwrap();
        let expected = if shadow {
            context.store().intrinsic_bootstrap().unwrap().string_type
        } else {
            context.store().intrinsic_bootstrap().unwrap().number_type
        };
        let owner = context.get_symbol_at_location(reads[0].0).unwrap().unwrap();
        assert_eq!(owner == global, !shadow);
        for &(receiver, property) in &reads {
            assert_eq!(context.get_symbol_at_location(receiver), Ok(Some(owner)));
            assert_eq!(context.get_type_at_location(property), Ok(expected));
        }
        let [error] = context.diagnostics().as_slice() else {
            panic!("expected one assignment error: {:?}", context.diagnostics());
        };
        assert_eq!(error.diagnostic.code(), 2322);
        let message = if shadow {
            "Type 'string' is not assignable to type 'number'."
        } else {
            "Type 'number' is not assignable to type 'string'."
        };
        assert_eq!(error.diagnostic.render().unwrap(), message);
        let error_node = error.node.unwrap();
        let error_record = source_ast.arena.get(error_node.node).unwrap();
        assert_eq!(error_node.file, consumer);
        assert_eq!(error_record.kind, SyntaxKind::Identifier);
        assert_eq!(
            error_record.range.start.get() as usize,
            source.find("wrong").unwrap()
        );
        assert_eq!(
            error_record.range.end.get() - error_record.range.start.get(),
            5
        );
        assert!(error.range_override.is_none());
        assert!(error.related_information.is_empty());
        let diagnostics = context.diagnostics().clone();
        let value_links = context.store().value_symbol_links(global).cloned();
        let query_results = reads
            .iter()
            .map(|&(receiver, property)| {
                (
                    context.store().symbol_node_links(receiver).cloned(),
                    context.store().type_node_links(receiver).cloned(),
                    context.store().type_node_links(property).cloned(),
                )
            })
            .collect::<Vec<_>>();
        for _ in 0..2 {
            context.check_source_file(consumer).unwrap();
            context.recheck_source_file(consumer).unwrap();
            for &(receiver, property) in &reads {
                assert_eq!(context.get_symbol_at_location(receiver), Ok(Some(owner)));
                assert_eq!(context.get_type_at_location(property), Ok(expected));
            }
            let record = context.store().symbol(global).unwrap();
            assert_eq!(record.declarations(), Some(declarations.as_slice()));
            assert_eq!(record.value_declaration(), Some(selected));
            assert_eq!(
                context.store().value_symbol_links(global).cloned(),
                value_links
            );
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(
                reads
                    .iter()
                    .map(|&(receiver, property)| (
                        context.store().symbol_node_links(receiver).cloned(),
                        context.store().type_node_links(receiver).cloned(),
                        context.store().type_node_links(property).cloned(),
                    ))
                    .collect::<Vec<_>>(),
                query_results
            );
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn merged_script_globals_keep_declared_values_and_replay() {
    check_global_values(
        "declare var configuration: Application.Options;\n",
        CONSUMER,
        false,
    );
}

#[test]
fn merged_augmented_globals_keep_class_reads_and_errors() {
    check_global_values(
        "export {};\ndeclare global { var configuration: Application.Options; }\n",
        CONSUMER,
        false,
    );
}

#[test]
fn local_shadow_keeps_its_own_value_type() {
    check_global_values(
        "declare var configuration: Application.Options;\n",
        concat!(
            "export {};\n",
            "const configuration = { port: 'local' };\n",
            "const correct: string = configuration.port;\n",
            "const wrong: number = configuration.port;\n",
        ),
        true,
    );
}
