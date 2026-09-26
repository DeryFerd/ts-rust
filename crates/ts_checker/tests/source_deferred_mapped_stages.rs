use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolTableId,
    semantic::{Symbol, SymbolTable},
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    MappedSymbolLinks, TypeId, ValueSymbolLinks,
    relation::RelationKind,
    type_records::{MappedTypeData, TypeData},
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(0);
const SOURCE_FILE: FileId = FileId::new(1);
const LIBRARY: &str = "interface IArguments {} interface Object {} interface Function {} interface String {} interface Number {} interface Boolean {} interface RegExp {} interface Array<T> { length: number; [index: number]: T; } interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; } interface ThisType<T> {}\n";
const SOURCE: &str = concat!(
    "export type Shape<T> = { selected: T; unread: () => T };\n",
    "export type Copy<T> = { [K in keyof T]: T[K] };\n",
    "export type Applied = Copy<Shape<number>>;\n",
    "export type Selected = Applied[\"selected\"];\n",
);

fn checker<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, declaration, state, name) in [
        (LIBRARY_FILE, library, true, CanonicalModuleState::Script, "lib.d.ts"),
        (SOURCE_FILE, source, false, CanonicalModuleState::External, "consumer.ts"),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder.bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(name),
                CanonicalSourceLanguage::TypeScript,
                declaration,
                state,
            ),
        ).unwrap();
    }
    for (file, parsed) in [(LIBRARY_FILE, library), (SOURCE_FILE, source)] {
        binder.bind_typescript_declaration_slice(&parsed.arena, file).unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &source.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            strict_bind_call_apply: false,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    ).unwrap()
}

fn alias(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed.arena.iter().find_map(|(node, record)| {
        let NodeData::TypeAliasDeclaration(alias) = &record.data else { return None };
        let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
            return None;
        };
        (name.text == expected).then_some((
            NodeRef::new(parsed.arena.id(), SOURCE_FILE, node),
            NodeRef::new(parsed.arena.id(), SOURCE_FILE, alias.type_),
        ))
    }).unwrap_or_else(|| panic!("missing alias {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(SOURCE_FILE).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn mapped<'a>(checker: &'a CanonicalCheckerContext<'_>, id: TypeId) -> &'a MappedTypeData {
    let TypeData::Mapped(data) = checker.store().type_payload(id).unwrap().data() else {
        panic!("expected mapped instance");
    };
    data
}

fn identity(
    checker: &CanonicalCheckerContext<'_>,
    id: TypeId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    let record = store.type_payload(id).unwrap();
    let data = mapped(checker, id);
    let target = data.object.target.expect("original mapped target");
    let original = mapped(checker, target);
    let formal = data.type_parameter.expect("fresh mapped formal");
    let original_formal = original.type_parameter.unwrap();
    let TypeData::TypeParameter(parameter) = store.type_payload(formal).unwrap().data() else {
        panic!("expected mapped formal");
    };
    assert_ne!(id, target);
    assert_ne!(formal, original_formal);
    assert_eq!(parameter.target, Some(original_formal));
    assert!(parameter.mapper.is_some());
    assert_eq!(data.declaration, original.declaration);
    assert_eq!(record.symbol(), store.type_payload(target).unwrap().symbol());
    let alias = store.type_alias(record.alias().expect("instance alias identity")).unwrap();
    (
        id,
        record.symbol(),
        data.declaration,
        target,
        formal,
        data.object.mapper.expect("instance mapper"),
        parameter.target,
        parameter.mapper,
        alias.id(),
        alias.symbol(),
        alias.type_arguments().map(|arguments| arguments.to_vec()),
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Members {
    table: SymbolTableId,
    contents: SymbolTable,
    rows: Vec<(SemanticSymbolId, Symbol, MappedSymbolLinks, ValueSymbolLinks)>,
}

fn members(checker: &CanonicalCheckerContext<'_>, id: TypeId) -> Members {
    let store = checker.store();
    let structure = &mapped(checker, id).object.structured;
    let table = structure.members.expect("mapped names are complete");
    let contents = store.symbol_table(table).unwrap().clone();
    let selected = contents.get_source("selected").unwrap();
    let unread = contents.get_source("unread").unwrap();
    assert_eq!(contents.len(), 2);
    assert_eq!(structure.properties.as_deref(), Some([selected, unread].as_slice()));
    assert!(structure.index_infos.as_deref().unwrap_or_default().is_empty());
    let rows = [selected, unread].into_iter().map(|symbol| {
        let value = store.value_symbol_links(symbol).unwrap().clone();
        let mapped = store.mapped_symbol_links(symbol).unwrap().clone();
        assert_eq!(value.containing_type, Some(id));
        assert!(value.name_type.is_some());
        assert!(mapped.key_type.is_some());
        (symbol, store.symbol(symbol).unwrap().clone(), mapped, value)
    }).collect();
    Members { table, contents, rows }
}

fn assert_unread_cold(
    checker: &CanonicalCheckerContext<'_>,
    source_symbol: SemanticSymbolId,
    annotation: NodeRef,
    source_argument: TypeId,
) {
    let store = checker.store();
    assert_eq!(store.value_symbol_links(source_symbol).and_then(|links| links.resolved_type), None);
    assert_eq!(store.type_node_links(annotation).and_then(|links| links.resolved_type), None);
    let TypeData::Object(source) = store.type_payload(source_argument).unwrap().data() else {
        panic!("Shape<number> must be an ordinary source object");
    };
    if let Some(table) = source.structured.members {
        let unread = store.symbol_table(table).unwrap().get_source("unread").unwrap();
        assert_eq!(store.value_symbol_links(unread).and_then(|links| links.resolved_type), None);
    }
    assert!(!store.source_file_links(checker.source_file(SOURCE_FILE).unwrap())
        .is_some_and(|links| links.type_checked));
    assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    id: TypeId,
    source_unread: SemanticSymbolId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let nodes = parsed.arena.iter().map(|(node, _)| {
        let node = NodeRef::new(parsed.arena.id(), SOURCE_FILE, node);
        (
            node,
            store.node_links(node).cloned(),
            store.type_node_links(node).cloned(),
            store.symbol_node_links(node).cloned(),
            store.signature_links(node).cloned(),
        )
    }).collect::<Vec<_>>();
    let aliases = ["Shape", "Copy", "Applied", "Selected"].map(|name| {
        let owner = symbol(checker, alias(parsed, name).0);
        (owner, store.type_alias_links(owner).cloned())
    });
    let TypeData::TypeParameter(formal) = store.type_payload(mapped(checker, id).type_parameter.unwrap()).unwrap().data() else {
        panic!("expected mapped formal");
    };
    (
        [
            store.type_len(), store.type_alias_len(), store.symbol_len(),
            store.mapper_len(), store.signature_len(), store.index_info_len(),
            store.symbol_store().symbol_table_len(), store.properties_type_cache_len(),
            bootstrap.string_literal_cache_len(), bootstrap.union_cache_len(),
            store.relation_cache_size(RelationKind::Assignable),
        ],
        identity(checker, id),
        mapped(checker, id).clone(),
        formal.clone(),
        members(checker, id),
        nodes,
        aliases,
        store.value_symbol_links(source_unread).cloned(),
        checker.diagnostics().as_slice().to_vec(),
        store.relation_state_snapshot(),
    )
}

#[test]
fn mapped_queries_keep_unselected_named_values_cold() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(SOURCE);
    let mut checker = checker(&library, &parsed);
    let (_, shape) = alias(&parsed, "Shape");
    let (_, copy) = alias(&parsed, "Copy");
    let (_, applied) = alias(&parsed, "Applied");
    let (_, selected) = alias(&parsed, "Selected");
    let NodeData::TypeLiteralNode(shape) = &parsed.arena.get(shape.node).unwrap().data else {
        panic!("expected Shape body");
    };
    let (unread, annotation) = shape.members.nodes.iter().find_map(|&node| {
        let (name, annotation) = match &parsed.arena.get(node)?.data {
            NodeData::PropertySignatureDeclaration(property) => (property.name, property.type_),
            NodeData::PropertyDeclaration(property) => (property.name, property.type_?),
            _ => return None,
        };
        let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (name.text == "unread").then_some((
            NodeRef::new(parsed.arena.id(), SOURCE_FILE, node),
            NodeRef::new(parsed.arena.id(), SOURCE_FILE, annotation),
        ))
    }).unwrap();
    let unread = symbol(&checker, unread);
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(applied.node).unwrap().data else {
        panic!("expected Copy reference");
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one Copy argument");
    };
    let argument = NodeRef::new(parsed.arena.id(), SOURCE_FILE, *argument);

    let instance = checker.get_type_from_type_node(applied).expect("cold mapped instance");
    let source_argument = checker.store().type_node_links(argument).unwrap().resolved_type.unwrap();
    let cold_identity = identity(&checker, instance);
    let result_alias = checker.store().type_alias(
        checker.store().type_payload(instance).unwrap().alias().unwrap(),
    ).unwrap();
    assert_eq!(result_alias.symbol(), Some(symbol(&checker, alias(&parsed, "Copy").0)));
    assert_eq!(result_alias.type_arguments(), Some([source_argument].as_slice()));
    let data = mapped(&checker, instance);
    assert_eq!(data.declaration, Some(copy));
    assert!(data.object.structured.members.is_none());
    assert!(data.object.structured.properties.is_none());
    assert!(!checker.store().type_payload(instance).unwrap().object_flags().contains(ObjectFlags::MEMBERS_RESOLVED));
    assert_eq!((data.constraint_type, data.template_type, data.modifiers_type, data.name_type), (None, None, None, None));
    assert_unread_cold(&checker, unread, annotation, source_argument);

    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (empty, number) = (bootstrap.empty_object_type, bootstrap.number_type);
    assert_eq!(checker.is_type_assignable_to(empty, instance), Ok(false));
    assert_eq!(identity(&checker, instance), cold_identity);
    let names = members(&checker, instance);
    assert!(names.rows.iter().all(|row| row.3.resolved_type.is_none()));
    assert_unread_cold(&checker, unread, annotation, source_argument);

    assert_eq!(checker.get_type_from_type_node(selected), Ok(number));
    assert_eq!(identity(&checker, instance), cold_identity);
    let complete = members(&checker, instance);
    assert_eq!(complete.rows[0].3.resolved_type, Some(number));
    assert_eq!(complete.rows[1].3.resolved_type, None);
    // The selected value slot is the only named-row change allowed here.
    let mut names_after_value = complete.clone();
    names_after_value.rows[0].3.resolved_type = None;
    assert_eq!(names_after_value, names);
    assert_unread_cold(&checker, unread, annotation, source_argument);

    let warm = snapshot(&checker, &parsed, instance, unread);
    for _ in 0..2 {
        assert_eq!(checker.get_type_from_type_node(applied), Ok(instance));
        assert_eq!(checker.is_type_assignable_to(empty, instance), Ok(false));
        assert_eq!(checker.get_type_from_type_node(selected), Ok(number));
        assert_eq!(members(&checker, instance), complete);
        assert_unread_cold(&checker, unread, annotation, source_argument);
        assert_eq!(snapshot(&checker, &parsed, instance, unread), warm);
    }
}

#[test]
fn missing_mapped_index_reports_once_and_keeps_named_values_cold() {
    let library = parse_source_file(LIBRARY);
    let source = [SOURCE, "export type Missing = Applied[\"missing\"];\n"].concat();
    let parsed = parse_source_file(&source);
    let mut checker = checker(&library, &parsed);
    let (_, shape) = alias(&parsed, "Shape");
    let (_, applied) = alias(&parsed, "Applied");
    let (missing_owner, missing) = alias(&parsed, "Missing");
    let missing_symbol = symbol(&checker, missing_owner);
    let NodeData::IndexedAccessTypeNode(indexed) = &parsed.arena.get(missing.node).unwrap().data else {
        panic!("expected indexed type");
    };
    let index = NodeRef::new(parsed.arena.id(), SOURCE_FILE, indexed.index_type);
    let expected_start = u32::try_from(SOURCE.len() + "export type Missing = Applied[".len()).unwrap();
    let expected_end = expected_start + u32::try_from("\"missing\"".len()).unwrap();
    let NodeData::TypeLiteralNode(shape) = &parsed.arena.get(shape.node).unwrap().data else {
        panic!("expected Shape body");
    };
    let original_properties = shape.members.nodes.iter().map(|&node| {
        let annotation = match &parsed.arena.get(node).unwrap().data {
            NodeData::PropertySignatureDeclaration(property) => property.type_,
            NodeData::PropertyDeclaration(property) => property.type_.unwrap(),
            _ => panic!("expected source property"),
        };
        (
            symbol(&checker, NodeRef::new(parsed.arena.id(), SOURCE_FILE, node)),
            NodeRef::new(parsed.arena.id(), SOURCE_FILE, annotation),
        )
    }).collect::<Vec<_>>();
    assert_eq!(original_properties.len(), 2);
    let (unread, unread_annotation) = original_properties[1];
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(applied.node).unwrap().data else {
        panic!("expected Copy reference");
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one Copy argument");
    };
    let argument = NodeRef::new(parsed.arena.id(), SOURCE_FILE, *argument);

    let instance = checker.get_type_from_type_node(applied).expect("cold mapped instance");
    let source_argument = checker.store().type_node_links(argument).unwrap().resolved_type.unwrap();
    let cold_identity = identity(&checker, instance);
    let error = checker.store().intrinsic_bootstrap().unwrap().error_type;
    assert!(mapped(&checker, instance).object.structured.members.is_none());
    assert!(checker.diagnostics().is_empty());
    assert_eq!(checker.store().type_node_links(missing).and_then(|links| links.resolved_type), None);
    assert_eq!(checker.get_type_from_type_node(missing), Ok(error));
    assert_eq!(checker.store().type_node_links(missing).unwrap().resolved_type, Some(error));
    assert_eq!(identity(&checker, instance), cold_identity);
    let names = members(&checker, instance);
    assert_eq!(names.contents.get_source("missing"), None);
    assert!(names.rows.iter().all(|row| row.3.resolved_type.is_none()));
    let assert_values_cold = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        for (source_symbol, _) in &original_properties {
            assert_eq!(store.value_symbol_links(*source_symbol).and_then(|links| links.resolved_type), None);
        }
        assert_eq!(store.type_node_links(unread_annotation).and_then(|links| links.resolved_type), None);
        let TypeData::Object(source) = store.type_payload(source_argument).unwrap().data() else {
            panic!("expected Shape<number> object");
        };
        if let Some(table) = source.structured.members {
            for name in ["selected", "unread"] {
                let property = store.symbol_table(table).unwrap().get_source(name).unwrap();
                assert_eq!(store.value_symbol_links(property).and_then(|links| links.resolved_type), None);
            }
        }
        assert!(!store.source_file_links(checker.source_file(SOURCE_FILE).unwrap())
            .is_some_and(|links| links.type_checked));
    };
    assert_values_cold(&checker);
    let diagnostics = checker.diagnostics().as_slice().to_vec();
    let [diagnostic] = diagnostics.as_slice() else {
        panic!("expected exactly one diagnostic: {diagnostics:?}");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(diagnostic.node, Some(index));
    assert!(diagnostic.related_information.is_empty());
    let range = diagnostic.range_override.map(|range| {
        assert_eq!(range.anchor(), index);
        range.range()
    }).unwrap_or(parsed.arena.get(index.node).unwrap().range);
    assert_eq!((range.start.get(), range.end.get()), (expected_start, expected_end));

    let warm = (
        snapshot(&checker, &parsed, instance, unread),
        checker.store().type_alias_links(missing_symbol).cloned(),
    );
    for _ in 0..2 {
        assert_eq!(checker.get_type_from_type_node(missing), Ok(error));
        assert_eq!(members(&checker, instance), names);
        assert_values_cold(&checker);
        assert_eq!(checker.diagnostics().as_slice(), diagnostics.as_slice());
        assert_eq!((
            snapshot(&checker, &parsed, instance, unread),
            checker.store().type_alias_links(missing_symbol).cloned(),
        ), warm);
    }
}

#[test]
fn optional_mapped_index_replaces_missing_with_undefined_only_at_the_ast() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "export type Shape<T> = { selected?: T; unread: () => T };\n",
        "export type Copy<T> = { [K in keyof T]: T[K] };\n",
        "export type Applied = Copy<Shape<number>>;\n",
        "export type Selected = Applied[\"selected\"];\n",
    ));
    let mut binder = CanonicalBinder::new();
    for (file, parsed, declaration, state, name) in [
        (LIBRARY_FILE, &library, true, CanonicalModuleState::Script, "lib.d.ts"),
        (SOURCE_FILE, &parsed, false, CanonicalModuleState::External, "consumer.ts"),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder.bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(name),
                CanonicalSourceLanguage::TypeScript,
                declaration,
                state,
            ),
        ).unwrap();
    }
    for (file, parsed) in [(LIBRARY_FILE, &library), (SOURCE_FILE, &parsed)] {
        binder.bind_typescript_declaration_slice(&parsed.arena, file).unwrap();
    }
    let mut checker = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            strict_bind_call_apply: false,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    ).unwrap();
    let (_, shape) = alias(&parsed, "Shape");
    let (_, applied) = alias(&parsed, "Applied");
    let (_, selected) = alias(&parsed, "Selected");
    let NodeData::TypeLiteralNode(shape) = &parsed.arena.get(shape.node).unwrap().data else {
        panic!("expected Shape body");
    };
    let unread_node = shape.members.nodes[1];
    let annotation = match &parsed.arena.get(unread_node).unwrap().data {
        NodeData::PropertySignatureDeclaration(property) => property.type_,
        NodeData::PropertyDeclaration(property) => property.type_.expect("annotated unread property"),
        _ => panic!("expected unread property"),
    };
    let annotation = NodeRef::new(parsed.arena.id(), SOURCE_FILE, annotation);
    let unread = symbol(&checker, NodeRef::new(parsed.arena.id(), SOURCE_FILE, unread_node));
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(applied.node).unwrap().data else {
        panic!("expected Copy reference");
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one Copy argument");
    };
    let argument = NodeRef::new(parsed.arena.id(), SOURCE_FILE, *argument);

    assert_eq!(checker.store().type_node_links(selected).and_then(|links| links.resolved_type), None);
    let result = checker.get_type_from_type_node(selected).expect("optional indexed result");
    let instance = checker.store().type_node_links(applied).unwrap().resolved_type.unwrap();
    let source_argument = checker.store().type_node_links(argument).unwrap().resolved_type.unwrap();
    let names = members(&checker, instance);
    let raw = names.rows[0].3.resolved_type.expect("selected mapped value");
    assert_eq!(names.rows[1].3.resolved_type, None);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, undefined, missing) = (
        bootstrap.number_type, bootstrap.undefined_type, bootstrap.missing_type,
    );
    assert!(bootstrap.options.exact_optional_property_types);
    assert_eq!(bootstrap.undefined_or_missing_type, missing);
    assert_ne!(undefined, missing);
    assert_ne!(raw, result);
    for (type_, sentinel) in [(raw, missing), (result, undefined)] {
        let record = checker.store().type_payload(type_).unwrap();
        let TypeData::Union(union) = record.data() else {
            panic!("expected optional union");
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&number));
        assert!(union.union.types.contains(&sentinel));
        assert!(record.alias().is_none());
        assert_eq!(bootstrap.cached_union_type(&union.union.types), Some(type_));
    }
    assert_eq!(checker.store().type_node_links(selected).unwrap().resolved_type, Some(result));
    assert_unread_cold(&checker, unread, annotation, source_argument);

    let warm = snapshot(&checker, &parsed, instance, unread);
    for _ in 0..2 {
        assert_eq!(checker.get_type_from_type_node(selected), Ok(result));
        assert_eq!(members(&checker, instance), names);
        assert_unread_cold(&checker, unread, annotation, source_argument);
        assert_eq!(snapshot(&checker, &parsed, instance, unread), warm);
    }
}
