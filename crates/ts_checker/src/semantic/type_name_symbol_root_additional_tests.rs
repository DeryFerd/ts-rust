use super::*;
use ts_ast::SyntaxKind;
use ts_binder::CanonicalBindError;

#[test]
fn root_type_name_symbols_reject_cached_other_real_namespace_members() {
    for poison_root in [false, true] {
        let parsed = parse_source_file(
            "namespace First { export interface Item {} } namespace Second { export interface Item {} } let item: First.Item;",
        );
        let file = FileId::new(6_509);
        let mut context = context(&parsed, file);
        let (_, name) = variable_annotation(&parsed, file, "item");
        let NodeData::QualifiedName(qualified) = &parsed.arena.get(name.node).unwrap().data else {
            unreachable!()
        };
        let root = NodeRef::new(name.arena, file, qualified.left);
        let other = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source("Second")
            .unwrap();
        let cached_node = if poison_root { root } else { name };
        let cached = if poison_root {
            other
        } else {
            let exports = context.store().symbol(other).unwrap().exports().unwrap();
            context
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("Item")
                .unwrap()
        };
        assert!(context.store_mut_for_test().set_symbol_node_links(
            cached_node,
            SymbolNodeLinks {
                resolved_symbol: Some(cached)
            }
        ));
        let before = state(&context);
        assert_eq!(
            context.get_symbol_at_location(name),
            Err(CanonicalArtifactQueryError::InvalidSymbol {
                node: cached_node,
                symbol: cached
            })
        );
        assert_eq!(state(&context), before);
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_some_and(|links| links.type_checked)
        );
    }
}

#[test]
fn root_type_name_symbols_keep_the_written_path_and_requested_meaning() {
    for (source, path) in [
        ("let item: Missing;", vec!["Missing"]),
        ("namespace Shapes {} let item: Shapes;", vec!["Shapes"]),
        ("const ready = 1; let item: ready;", vec!["ready"]),
        (
            "interface Model {} let item: Model.Item;",
            vec!["Model", "Item"],
        ),
        (
            "namespace Known {} let item: Known.Missing;",
            vec!["Known", "Missing"],
        ),
        (
            "namespace Known { export const value = 1; } let item: Known.value;",
            vec!["Known", "value"],
        ),
        (
            "let item: Missing.Inner.Item;",
            vec!["Missing", "Inner", "Item"],
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_510);
        let mut context = context(&parsed, file);
        let (_, name) = variable_annotation(&parsed, file, "item");
        let before = state(&context).0;
        let symbol = context.get_symbol_at_location(name).unwrap().unwrap();
        assert_unresolved(&context, symbol, &path);
        assert_eq!(
            context.symbol_to_string(symbol).unwrap(),
            *path.last().unwrap()
        );
        let after = state(&context).0;
        assert_eq!(
            [after[0], after[1], after[3], after[4], after[5]],
            [before[0], before[1], before[3], before[4], before[5]]
        );
    }
}

#[test]
fn root_type_name_symbols_reject_malformed_records_at_binding() {
    for corrupt_reference in [false, true] {
        let mut parsed = parse_source_file("let item: Missing.Item;");
        let file = FileId::new(6_511);
        let (reference, name) = variable_annotation(&parsed, file, "item");
        let malformed = if corrupt_reference { reference } else { name };
        parsed.arena.get_mut(malformed.node).unwrap().kind = SyntaxKind::PropertyAccessExpression;
        let mut binder = CanonicalBinder::new();
        assert!(
            matches!(binder.bind_source_file(&parsed.arena, parsed.source_file, file),
            Err(CanonicalBindError::MismatchedNodeKind { node, kind: SyntaxKind::PropertyAccessExpression, .. }) if node == malformed)
        );
        assert_eq!(binder.symbol_store().symbol_len(), 0);
        assert_eq!(binder.symbol_store().symbol_table_len(), 0);
        assert!(binder.file(file).is_none());
    }
}

#[test]
fn root_type_name_symbols_do_not_recover_unavailable_alias_lookup() {
    let parsed =
        parse_source_file("import * as External from './missing'; let item: External.Missing;");
    let file = FileId::new(6_512);
    let mut binder = CanonicalBinder::new();
    bind(
        &mut binder,
        &parsed,
        file,
        "/project/unavailable.ts",
        false,
        CanonicalModuleState::External,
    );
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let (_, name) = variable_annotation(&parsed, file, "item");
    let before = state(&context).0;
    assert!(context.get_symbol_at_location(name).is_err());
    assert_eq!(
        context.store().unresolved_symbol_for_name_path(&[
            EscapedName::source("External"),
            EscapedName::source("Missing")
        ]),
        Ok(None)
    );
    assert_eq!(state(&context).0, before);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the bound identities and cold replay checks together.
fn root_type_name_symbols_keep_import_equals_namespace_exports_cold() {
    let importer = parse_source_file(concat!(
        "import api = require('./target');\n",
        "let first: api.Shape;\n",
        "let second: api.Names.Entry;\n",
    ));
    let target = parse_source_file(concat!(
        "export type Shape = { text: string };\n",
        "export namespace Names { export interface Entry { count: number } }\n",
        "export = { value: 1, label: 'ok' };\n",
    ));
    let file = FileId::new(6_513);
    let target_file = FileId::new(6_514);
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path) in [
        (&importer, file, "/project/importer.ts"),
        (&target, target_file, "/project/target.ts"),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        bind(
            &mut binder,
            parsed,
            file,
            path,
            false,
            CanonicalModuleState::External,
        );
    }
    let (alias, specifier) = importer
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ImportEqualsDeclaration(import) = &record.data else {
                return None;
            };
            let NodeData::ExternalModuleReference(reference) =
                &importer.arena.get(import.module_reference)?.data
            else {
                return None;
            };
            Some((
                binder
                    .file(file)
                    .unwrap()
                    .symbol(NodeRef::new(importer.arena.id(), file, id))
                    .unwrap(),
                NodeRef::new(importer.arena.id(), file, reference.expression),
            ))
        })
        .unwrap();
    let mut context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        vec![(file, &importer.arena), (target_file, &target.arena)],
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                target_file,
                CanonicalModuleResolutionMode::CommonJs,
                CanonicalModuleResolutionMode::CommonJs,
            ),
        )]),
    )
    .unwrap();
    let bound = context.file(target_file).unwrap().1;
    let module = bound.symbol(bound.source_file()).unwrap();
    let exports = context.store().symbol(module).unwrap().exports().unwrap();
    let exports = context.store().symbol_table(exports).unwrap();
    let shape = exports.get_source("Shape").unwrap();
    let names = exports.get_source("Names").unwrap();
    let exports = context.store().symbol(names).unwrap().exports().unwrap();
    let entry = context
        .store()
        .symbol_table(exports)
        .unwrap()
        .get_source("Entry")
        .unwrap();
    let (_, shape_name) = variable_annotation(&importer, file, "first");
    let NodeData::QualifiedName(qualified) = &importer.arena.get(shape_name.node).unwrap().data
    else {
        unreachable!()
    };
    let root = NodeRef::new(shape_name.arena, file, qualified.left);
    let (_, entry_name) = variable_annotation(&importer, file, "second");
    let NodeData::QualifiedName(qualified) = &importer.arena.get(entry_name.node).unwrap().data
    else {
        unreachable!()
    };
    let namespace = NodeRef::new(entry_name.arena, file, qualified.left);
    let queries = [
        (root, alias),
        (shape_name, shape),
        (namespace, names),
        (entry_name, entry),
    ];
    let before = state(&context).0;
    for (node, expected) in queries {
        assert_eq!(context.get_symbol_at_location(node), Ok(Some(expected)));
    }
    assert_eq!(state(&context).0, before);
    let warm = state(&context);
    for (node, expected) in queries {
        assert_eq!(context.get_symbol_at_location(node), Ok(Some(expected)));
    }
    assert_eq!(state(&context), warm);
    for file in [file, target_file] {
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
}
