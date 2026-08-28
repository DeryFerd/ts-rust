use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_parser::{ParseResult, parse_source_file};

use super::{CanonicalArtifactQueryError, CanonicalCheckerContext};
use crate::semantic::{
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ModuleSymbolLinks, SymbolNodeLinks, TypeAliasLinks,
    TypeNodeLinks,
};

#[path = "type_name_symbol_root_additional_tests.rs"]
mod additional;

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    bind(
        &mut binder,
        parsed,
        file,
        "/project/input.ts",
        false,
        CanonicalModuleState::Script,
    );
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn bind(
    binder: &mut CanonicalBinder,
    parsed: &ParseResult,
    file: FileId,
    path: &str,
    declaration: bool,
    module: CanonicalModuleState,
) {
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(format!("\"{path}\"")),
                CanonicalSourceLanguage::TypeScript,
                declaration,
                module,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
}

fn variable_annotation(parsed: &ParseResult, file: FileId, name: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::VariableDeclaration(variable) = &node.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            if identifier.text != name {
                return None;
            }
            let annotation = variable.type_?;
            let name = match &parsed.arena.get(annotation)?.data {
                NodeData::TypeReferenceNode(reference) => reference.type_name,
                NodeData::TypeQueryNode(query) => query.expr_name,
                _ => return None,
            };
            Some((
                NodeRef::new(parsed.arena.id(), file, annotation),
                NodeRef::new(parsed.arena.id(), file, name),
            ))
        })
        .unwrap()
}

fn state(context: &CanonicalCheckerContext<'_>) -> ([usize; 6], Vec<usize>) {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            context.diagnostics().len(),
        ],
        store.checker_link_allocated_lengths().to_vec(),
    )
}

fn assert_unresolved(
    context: &CanonicalCheckerContext<'_>,
    symbol: SemanticSymbolId,
    names: &[&str],
) {
    let names = names.iter().map(EscapedName::source).collect::<Vec<_>>();
    assert_eq!(
        context.store().unresolved_symbol_for_name_path(&names),
        Ok(Some(symbol))
    );
    let chain = context
        .store()
        .authenticated_unresolved_symbol_chain(symbol)
        .unwrap();
    assert_eq!(chain.len(), names.len());
    for symbol in chain {
        let record = context.store().symbol(symbol).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT
        );
        assert_eq!(record.check_flags(), CheckFlags::UNRESOLVED);
        assert!(context.get_symbol_declarations(symbol).unwrap().is_empty());
        assert_eq!(
            context
                .store()
                .type_alias_links(symbol)
                .unwrap()
                .declared_type,
            Some(
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .unresolved_type
            )
        );
    }
}

#[test]
fn root_type_name_symbols_keep_known_and_missing_arguments_cold() {
    let parsed = parse_source_file(concat!(
        "namespace Known { export interface Present<T> {} } ",
        "let known: Known.Present<Absent>; let item: Missing.Inner.Item<Absent>;",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(6_500);
    let mut context = context(&parsed, file);
    let (_, known) = variable_annotation(&parsed, file, "known");
    let (_, missing) = variable_annotation(&parsed, file, "item");
    let NodeData::QualifiedName(known_name) = &parsed.arena.get(known.node).unwrap().data else {
        unreachable!()
    };
    let root = NodeRef::new(known.arena, file, known_name.left);
    let before = state(&context).0;
    assert!(context.get_symbol_at_location(root).unwrap().is_some());
    assert!(context.get_symbol_at_location(known).unwrap().is_some());
    assert_eq!(state(&context).0, before);
    let symbol = context.get_symbol_at_location(missing).unwrap().unwrap();
    assert_unresolved(&context, symbol, &["Missing", "Inner", "Item"]);
    assert_eq!(context.symbol_to_string(symbol).unwrap(), "Item");
    let NodeData::QualifiedName(full) = &parsed.arena.get(missing.node).unwrap().data else {
        unreachable!()
    };
    let prefix = NodeRef::new(missing.arena, file, full.left);
    let NodeData::QualifiedName(inner) = &parsed.arena.get(prefix.node).unwrap().data else {
        unreachable!()
    };
    let member = NodeRef::new(missing.arena, file, full.right);
    let inner_name = NodeRef::new(missing.arena, file, inner.right);
    let chain = context
        .store()
        .authenticated_unresolved_symbol_chain(symbol)
        .unwrap();
    assert_eq!(
        context.get_symbol_at_location(prefix).unwrap(),
        Some(chain[1])
    );
    assert_eq!(
        context.get_symbol_at_location(inner_name).unwrap(),
        Some(chain[1])
    );
    assert_eq!(
        context.get_symbol_at_location(member).unwrap(),
        Some(symbol)
    );
    let after = state(&context).0;
    assert_eq!(
        [after[0], after[1], after[3], after[4], after[5]],
        [before[0], before[1], before[3], before[4], before[5]]
    );
    assert_eq!(after[2], before[2] + 3);
    for (id, _) in parsed.arena.iter() {
        let node = NodeRef::new(parsed.arena.id(), file, id);
        assert!(context.store().type_node_links(node).is_none());
        assert!(context.store().symbol_node_links(node).is_none());
    }
    assert!(
        context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source("Missing")
            .is_none()
    );
    let warm = state(&context);
    assert_eq!(
        context.get_symbol_at_location(missing).unwrap(),
        Some(symbol)
    );
    assert_eq!(state(&context), warm);
}

#[test]
fn root_type_name_symbols_preserve_existing_source_error_type_and_diagnostics() {
    let parsed =
        parse_source_file("let first: Missing.Item; let second: Missing.Item; let other: Other;");
    let file = FileId::new(6_501);
    let mut context = context(&parsed, file);
    let references =
        ["first", "second", "other"].map(|name| variable_annotation(&parsed, file, name));
    let first = context
        .get_symbol_at_location(references[0].1)
        .unwrap()
        .unwrap();
    let other = context
        .get_symbol_at_location(references[2].1)
        .unwrap()
        .unwrap();
    assert_ne!(first, other);
    let error = context.store().intrinsic_bootstrap().unwrap().error_type;
    for (reference, _) in references {
        assert_eq!(context.get_type_from_type_node(reference).unwrap(), error);
    }
    assert_eq!(
        context.get_type_at_location(references[0].1).unwrap(),
        error
    );
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2503, 2503, 2304]
    );
    let warm = state(&context);
    for _ in 0..2 {
        for ((reference, name), symbol) in references.into_iter().zip([first, first, other]) {
            assert_eq!(context.get_type_from_type_node(reference).unwrap(), error);
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            assert!(context.store().symbol_node_links(reference).is_none());
            assert!(context.store().symbol_node_links(name).is_none());
        }
    }
    assert_eq!(state(&context), warm);
}

#[test]
fn root_type_name_symbols_reject_mismatched_source_and_type_caches() {
    for warm in [false, true] {
        for corruption in 0..7 {
            let parsed = parse_source_file("namespace Real {} let item: Missing.Item;");
            let file = FileId::new(6_502);
            let mut context = context(&parsed, file);
            let (reference, name) = variable_annotation(&parsed, file, "item");
            let NodeData::QualifiedName(qualified) = &parsed.arena.get(name.node).unwrap().data
            else {
                unreachable!()
            };
            let root = NodeRef::new(name.arena, file, qualified.left);
            let member = NodeRef::new(name.arena, file, qualified.right);
            if warm {
                context.get_type_from_type_node(reference).unwrap();
            }
            if corruption < 4 {
                let real = context
                    .store()
                    .symbol_table(context.globals())
                    .unwrap()
                    .get_source("Real")
                    .unwrap();
                assert!(context.store_mut_for_test().set_symbol_node_links(
                    [reference, name, root, member][corruption],
                    SymbolNodeLinks {
                        resolved_symbol: Some(real)
                    }
                ));
            } else {
                let any = context.store().intrinsic_bootstrap().unwrap().any_type;
                let links = if corruption == 5 {
                    TypeNodeLinks {
                        outer_type_parameters: Some(Vec::new()),
                        ..TypeNodeLinks::default()
                    }
                } else {
                    TypeNodeLinks {
                        resolved_type: Some(any),
                        ..TypeNodeLinks::default()
                    }
                };
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(if corruption == 6 { name } else { reference }, links)
                );
            }
            let before = state(&context);
            for _ in 0..2 {
                assert!(
                    context.get_symbol_at_location(name).is_err(),
                    "case {corruption}"
                );
                assert_eq!(state(&context), before);
            }
        }
    }
}

#[test]
fn root_type_name_symbols_reject_damaged_producer_records_and_empty_inputs() {
    for corruption in 0..3 {
        let parsed = parse_source_file("let item: Missing.Item;");
        let file = FileId::new(6_503);
        let mut context = context(&parsed, file);
        let (_, name) = variable_annotation(&parsed, file, "item");
        let symbol = context.get_symbol_at_location(name).unwrap().unwrap();
        let any = context.store().intrinsic_bootstrap().unwrap().any_type;
        match corruption {
            0 => assert!(context.store_mut_for_test().set_symbol_flags(
                symbol,
                SymbolFlags::TYPE_ALIAS | SymbolFlags::TRANSIENT,
                CheckFlags::NONE
            )),
            1 => assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_relationships(symbol, None, None, None, None)
            ),
            2 => assert!(context.store_mut_for_test().set_type_alias_links(
                symbol,
                TypeAliasLinks {
                    declared_type: Some(any),
                    ..TypeAliasLinks::default()
                }
            )),
            _ => unreachable!(),
        }
        let before = state(&context);
        assert!(context.get_symbol_at_location(name).is_err());
        assert_eq!(state(&context), before);
    }
    let parsed = parse_source_file("let item: ;");
    let file = FileId::new(6_504);
    let mut context = context(&parsed, file);
    let (_, name) = variable_annotation(&parsed, file, "item");
    let before = state(&context);
    assert_eq!(context.get_symbol_at_location(name), Ok(None));
    assert!(
        context
            .store_mut_for_test()
            .get_or_create_unresolved_symbol(&[])
            .is_err()
    );
    assert_eq!(state(&context), before);
}

#[test]
fn root_type_name_symbols_reject_foreign_nodes() {
    let parsed = parse_source_file("let item: Missing;");
    let foreign = parse_source_file("let item: Missing;");
    let file = FileId::new(6_505);
    let mut context = context(&parsed, file);
    let (_, name) = variable_annotation(&foreign, file, "item");
    let before = state(&context);
    assert_eq!(
        context.get_symbol_at_location(name),
        Err(CanonicalArtifactQueryError::ForeignNode(name))
    );
    assert_eq!(state(&context), before);
}

fn import_context<'a>(
    importer: &'a ParseResult,
    target: &'a ParseResult,
) -> (CanonicalCheckerContext<'a>, FileId, FileId) {
    let importer_file = FileId::new(6_506);
    let target_file = FileId::new(6_507);
    let mut binder = CanonicalBinder::new();
    bind(
        &mut binder,
        importer,
        importer_file,
        "/project/importer.d.ts",
        true,
        CanonicalModuleState::External,
    );
    bind(
        &mut binder,
        target,
        target_file,
        "/project/target.d.ts",
        true,
        CanonicalModuleState::External,
    );
    let entries = importer
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(importer.arena.id(), importer_file, import.module_specifier),
                CanonicalResolvedModuleInput::new(
                    target_file,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ))
        })
        .collect::<Vec<_>>();
    let context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        vec![
            (importer_file, &importer.arena),
            (target_file, &target.arena),
        ],
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap();
    (context, importer_file, target_file)
}

#[test]
fn root_type_name_symbols_reject_value_aliases_in_type_positions() {
    let importer = parse_source_file(concat!(
        "import { Exposed as Local } from './target'; import * as Types from './target'; ",
        "declare const direct: Local; declare const qualified: Types.Exposed;",
    ));
    let target = parse_source_file("declare const value: number; export { value as Exposed };");
    let (mut context, file, _) = import_context(&importer, &target);
    let before = state(&context).0;
    for (variable, path) in [
        ("direct", vec!["Local"]),
        ("qualified", vec!["Types", "Exposed"]),
    ] {
        let (reference, name) = variable_annotation(&importer, file, variable);
        let symbol = context.get_symbol_at_location(name).unwrap().unwrap();
        assert_unresolved(&context, symbol, &path);
        assert!(context.store().symbol_node_links(reference).is_none());
        assert!(context.store().symbol_node_links(name).is_none());
        assert!(context.store().type_node_links(reference).is_none());
    }
    let after = state(&context).0;
    assert_eq!(
        [after[0], after[1], after[3], after[4], after[5]],
        [before[0], before[1], before[3], before[4], before[5]]
    );
}

#[test]
fn root_type_name_symbols_keep_original_value_export_as_type_negative_control() {
    let importer = parse_source_file(concat!(
        "import { forwarded as local } from './target';\n",
        "import * as Types from './target';\n",
        "declare const result: Types.Exposed;\n",
    ));
    let target = parse_source_file(concat!(
        "declare const value: number;\n",
        "export { value as forwarded };\n",
    ));
    let (mut context, file, target_file) = import_context(&importer, &target);
    let target_module = context
        .file(target_file)
        .unwrap()
        .1
        .symbol(context.file(target_file).unwrap().1.source_file())
        .unwrap();
    let value = target
        .arena
        .iter()
        .find_map(|(id, record)| {
            matches!(record.data, NodeData::VariableDeclaration(_)).then(|| {
                context
                    .file(target_file)
                    .unwrap()
                    .1
                    .symbol(NodeRef::new(target.arena.id(), target_file, id))
                    .unwrap()
            })
        })
        .unwrap();
    let exports = context.store_mut_for_test().alloc_symbol_table();
    assert_eq!(
        context
            .store_mut_for_test()
            .insert_symbol(exports, EscapedName::source("Exposed"), value),
        Some(None)
    );
    assert!(context.store_mut_for_test().set_module_symbol_links(
        target_module,
        ModuleSymbolLinks {
            resolved_exports: Some(exports),
            ..ModuleSymbolLinks::default()
        }
    ));
    let (_, name) = variable_annotation(&importer, file, "result");
    let symbol = context.get_symbol_at_location(name).unwrap().unwrap();
    assert_ne!(symbol, value);
    assert_unresolved(&context, symbol, &["Types", "Exposed"]);
    assert_eq!(context.symbol_to_string(symbol).unwrap(), "Exposed");
    assert!(context.diagnostics().is_empty());
}

#[test]
fn root_type_name_symbols_keep_const_assertions_cold_and_warm() {
    for source in [
        "const value = '\\u{D83D}\\u{DE00}' as const;",
        "const value = { new: 'new', delete: 'delete', continue: 'continue' } as const;",
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_508);
        let mut context = context(&parsed, file);
        let name = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::TypeReferenceNode(reference) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, reference.type_name))
            })
            .unwrap();
        let before = state(&context).0;
        let symbol = context.get_symbol_at_location(name).unwrap().unwrap();
        assert_unresolved(&context, symbol, &["const"]);
        assert_eq!(context.symbol_to_string(symbol).unwrap(), "const");
        let after = state(&context).0;
        assert_eq!(
            [after[0], after[1], after[3], after[4], after[5]],
            [before[0], before[1], before[3], before[4], before[5]]
        );
        context.check_source_file(file).unwrap();
        let warm = state(&context);
        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
        assert_eq!(state(&context), warm);
    }
}
