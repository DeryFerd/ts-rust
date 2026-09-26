use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: &str = concat!(
    "interface IArguments {} interface Object {} interface Function {} ",
    "interface String {} interface Number {} interface Boolean {} interface RegExp {} ",
    "interface Array<T> { length: number; [index: number]: T; } ",
    "interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; } ",
    "interface ThisType<T> {}",
);

fn parsed(text: &str) -> ParseResult {
    let parsed = parse_source_file(text);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed
}

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
    file: FileId,
) -> CanonicalCheckerContext<'arena> {
    let files = [(FileId::new(32_100), library), (file, source)];
    let mut binder = CanonicalBinder::new();
    for (index, &(file, parsed)) in files.iter().enumerate() {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"/inherited-index-{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    index == 0,
                    index == 0,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for &(file, parsed) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn derived_node(source: &ParseResult, file: FileId) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                source.arena.id(),
                file,
                node,
            ))
        })
        .unwrap()
}

fn result_type(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    file: FileId,
) -> TypeId {
    let declaration = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &source.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "result").then_some(NodeRef::new(source.arena.id(), file, node))
        })
        .unwrap();
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let symbol = context.store().get_merged_symbol(symbol).unwrap();
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_inherited_index_identity(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    file: FileId,
) {
    let symbol = context
        .file(file)
        .unwrap()
        .1
        .symbol(derived_node(source, file))
        .unwrap();
    let symbol = context.store().get_merged_symbol(symbol).unwrap();
    let type_ = context
        .store()
        .declared_type_links(symbol)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(derived) = context.store().type_payload(type_).unwrap().data() else {
        panic!("Derived must retain its interface identity")
    };
    assert!(derived.declared_members_resolved);
    assert!(derived.declared_index_infos.is_none());
    let [base] = derived.resolved_base_types.as_deref().unwrap() else {
        panic!("Derived must retain one base")
    };
    let indexes = derived
        .reference
        .object
        .structured
        .index_infos
        .as_deref()
        .unwrap();
    assert_eq!(indexes.len(), 1);
    let base_members = match context.store().type_payload(*base).unwrap().data() {
        TypeData::TypeReference(base) => &base.object.structured,
        TypeData::Interface(base) => &base.reference.object.structured,
        _ => panic!("the array base must retain its reference payload"),
    };
    assert_eq!(base_members.index_infos.as_deref(), Some(indexes));
    let index = context.store().index_info(indexes[0]).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(index.key_type(), number);
    assert_eq!(index.value_type(), number);
    assert!(index.is_readonly());
}

#[test]
fn inherited_numeric_indexes_preserve_unconstrained_own_properties_on_source_replay() {
    let library = parsed(LIBRARY);
    for (property, access, expected) in [
        ("label: string", "values.label", "string"),
        ("readonly label: string", "values.label", "string"),
        ("label?: string", "values.label", "string | undefined"),
        ("\"01\": string", "values[\"01\"]", "string"),
        ("\"-0\": string", "values[\"-0\"]", "string"),
        ("\"1.0\": string", "values[\"1.0\"]", "string"),
        ("0: number", "values[0]", "number"),
        ("\"-1\": number", "values[-1]", "number"),
    ] {
        let source = parsed(&format!(
            "interface Derived extends ReadonlyArray<number> {{ {property}; }} \
             declare const values: Derived; const result = {access};",
        ));
        let file = FileId::new(32_101);
        let mut context = context(&library, &source, file);
        context.check_source_file(file).unwrap_or_else(|error| {
            let symbol = context
                .file(file)
                .unwrap()
                .1
                .symbol(derived_node(&source, file))
                .unwrap();
            let symbol = context.store().get_merged_symbol(symbol).unwrap();
            let derived = context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type);
            panic!("{property}: {error:?}; Derived type: {derived:?}");
        });
        assert!(
            context.diagnostics().is_empty(),
            "{property}: {:?}",
            context.diagnostics()
        );
        let result = result_type(&context, &source, file);
        assert_eq!(
            context.type_to_string(result).unwrap(),
            expected,
            "{property}"
        );
        assert_inherited_index_identity(&context, &source, file);
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().index_info_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                context.diagnostics().clone(),
                result_type(context, &source, file),
            )
        };
        let before = snapshot(&context);
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(&context), before, "{property}");
        assert_inherited_index_identity(&context, &source, file);
    }
}

#[test]
fn inherited_numeric_index_constraints_report_diagnostics_and_keep_members() {
    let library = parsed(LIBRARY);
    for property in [
        "0: string",
        "\"-1\": string",
        "\"1.5\": string",
        "\"NaN\": string",
        "\"Infinity\": string",
        "0?: number",
    ] {
        let source = parsed(&format!(
            "interface Derived extends ReadonlyArray<number> {{ {property}; }} \
             declare const values: Derived;",
        ));
        let file = FileId::new(32_102);
        let mut context = context(&library, &source, file);
        let (declaration, name, annotation) = source.arena.iter().find_map(|(node, record)| {
            let NodeData::PropertyDeclaration(data) = &record.data else { return None };
            Some((
                NodeRef::new(source.arena.id(), file, node),
                NodeRef::new(source.arena.id(), file, data.name),
                NodeRef::new(source.arena.id(), file, data.type_.unwrap()),
            ))
        }).unwrap();
        let own = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let own = context.store().get_merged_symbol(own).unwrap();
        context.check_source_file(file).unwrap_or_else(|error| panic!("{property}: {error:?}"));
        let optional = property == "0?: number";
        let name_text = property.split(':').next().unwrap().trim_end_matches('?');
        let type_text = if optional { "number | undefined" } else { "string" };
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("{property}: expected one TS2411, got {:?}", context.diagnostics())
        };
        assert_eq!(diagnostic.diagnostic.code(), 2411);
        assert_eq!(diagnostic.node, Some(name));
        assert_eq!(diagnostic.diagnostic.arguments, [name_text, type_text, "number", "number"]);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        let range = source.arena.get(name.node).unwrap().range;
        assert_eq!(range.start.get(), 50);
        assert_eq!(usize::try_from(range.end.get() - range.start.get()).unwrap(), name_text.len());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number, undefined) = (bootstrap.string_type, bootstrap.number_type, bootstrap.undefined_type);
        let annotation_type = if optional { number } else { string };
        assert_eq!(context.store().value_symbol_links(own).unwrap().resolved_type, Some(annotation_type));
        assert!(matches!(source.arena.get(annotation.node).unwrap().kind,
            SyntaxKind::StringKeyword | SyntaxKind::NumberKeyword));
        let expected_links = ts_checker::semantic::TypeNodeLinks {
            resolved_type: Some(annotation_type),
            ..Default::default()
        };
        let annotation_links = context.store().type_node_links(annotation).cloned();
        assert!(annotation_links.as_ref().is_none_or(|links| {
            links == &ts_checker::semantic::TypeNodeLinks::default() || links == &expected_links
        }));
        assert_eq!(context.get_type_from_type_node(annotation), Ok(annotation_type));
        assert_eq!(context.store().type_node_links(annotation), annotation_links.as_ref());
        assert_eq!(context.store().symbol(own).unwrap().value_declaration(), Some(declaration));
        assert_eq!(context.store().symbol(own).unwrap().flags().contains(ts_binder::SymbolFlags::OPTIONAL), optional);
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(own)));
        let read = context.get_type_at_location(name).unwrap();
        assert_eq!(context.type_to_string(read).unwrap(), type_text);
        if optional {
            let TypeData::Union(union) = context.store().type_payload(read).unwrap().data() else {
                panic!("optional number must keep a union")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&number));
            assert!(union.union.types.contains(&undefined));
        } else {
            assert_eq!(read, string);
        }
        let symbol = context
            .file(file)
            .unwrap()
            .1
            .symbol(derived_node(&source, file))
            .unwrap();
        let symbol = context.store().get_merged_symbol(symbol).unwrap();
        let type_ = context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(derived) = context.store().type_payload(type_).unwrap().data()
        else { panic!("Derived must retain its interface identity") };
        assert!(derived.declared_members_resolved);
        assert!(derived.base_types_resolved);
        let key = context.store().symbol(own).unwrap().name();
        for table in [derived.declared_members, derived.reference.object.structured.members] {
            assert_eq!(context.store().symbol_table(table.unwrap()).unwrap().get(key), Some(own));
        }
        assert!(derived.reference.object.structured.properties.as_ref().unwrap().contains(&own));
        let index = derived.reference.object.structured.index_infos.as_ref().unwrap()[0];
        assert_inherited_index_identity(&context, &source, file);
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            let TypeData::Interface(derived) = store.type_payload(type_).unwrap().data()
            else { unreachable!() };
            let info = store.index_info(index).unwrap();
            (
                [store.type_len(), store.symbol_len(), store.mapper_len(), store.signature_len(),
                    store.index_info_len(), store.symbol_store().symbol_table_len()],
                store.relation_state_snapshot(),
                context.diagnostics().clone(),
                store.value_symbol_links(own).cloned(),
                [declaration, name, annotation].map(|node| (
                    store.node_links(node).cloned(), store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )),
                (derived.declared_members, derived.resolved_base_types.clone(),
                    derived.reference.object.structured.members,
                    derived.reference.object.structured.properties.clone(),
                    derived.reference.object.structured.index_infos.clone()),
                (index, info.key_type(), info.value_type(), info.is_readonly(),
                    info.declaration(), info.index_symbol(), info.components().to_vec()),
                store.type_resolution_len(),
            )
        };
        let before = snapshot(&context);
        for _ in 0..2 {
            context.check_source_file(file).unwrap();
            context.recheck_source_file(file).unwrap();
            assert_eq!(context.get_type_from_type_node(annotation), Ok(annotation_type));
            assert_eq!(context.store().type_node_links(annotation), annotation_links.as_ref());
            assert_eq!(context.get_type_at_location(name), Ok(read));
            assert_eq!(context.get_symbol_at_location(name), Ok(Some(own)));
            assert_inherited_index_identity(&context, &source, file);
            assert!(context.store().type_resolution_is_empty());
            assert_eq!(snapshot(&context), before, "{property}");
        }
    }
}
