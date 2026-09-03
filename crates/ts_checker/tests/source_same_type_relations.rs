use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
    IntrinsicBootstrapOptions, RelationKind, RelationUnavailable, TypeData, TypeId,
    ValueSymbolLinks, type_records::StructuredTypeData, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(204_510);
const SOURCE_FILE: FileId = FileId::new(204_511);
const LIBRARY: &str = concat!(
    "interface Array<T> {}\n",
    "interface ReadonlyArray<T> {}\n",
    "declare var marker: number;\n",
);

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name_node = match &record.data {
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .unwrap_or_else(|| panic!("missing declaration {name}"))
}

fn annotation(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named(parsed, SOURCE_FILE, name);
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a type alias")
    };
    node(parsed, SOURCE_FILE, alias.type_)
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = context.file(declaration.file).unwrap().1;
    context
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap()
}

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, declaration, default_library) in [
        (
            LIBRARY_FILE,
            library,
            "\"/lib/lib.same-type-relations.d.ts\"",
            true,
            true,
        ),
        (
            SOURCE_FILE,
            source,
            "\"/project/same-type-relations.ts\"",
            false,
            false,
        ),
    ] {
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
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &source.arena)],
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
    .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct GlobalPublication {
    counts: [usize; 6],
    relations: [usize; 3],
    flags: ObjectFlags,
    members: StructuredTypeData,
    marker: Option<ValueSymbolLinks>,
}

fn global_publication(
    context: &CanonicalCheckerContext<'_>,
    marker: SemanticSymbolId,
) -> GlobalPublication {
    let store = context.store();
    let global = store
        .type_payload(context.global_types().global_this_value_type)
        .unwrap();
    let TypeData::Object(object) = global.data() else {
        panic!("globalThis must retain its canonical object")
    };
    GlobalPublication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relations: [
            RelationKind::Assignable,
            RelationKind::Identity,
            RelationKind::Comparable,
        ]
        .map(|relation| store.relation_cache_size(relation)),
        flags: global.object_flags(),
        members: object.structured.clone(),
        marker: store.value_symbol_links(marker).cloned(),
    }
}

fn assert_global_cold(context: &CanonicalCheckerContext<'_>, marker: SemanticSymbolId) {
    let publication = global_publication(context, marker);
    assert_eq!(publication.flags, ObjectFlags::ANONYMOUS);
    assert_eq!(publication.members, StructuredTypeData::default());
    assert!(
        publication
            .marker
            .is_none_or(|links| links == ValueSymbolLinks::default())
    );
}

fn demand_dependency(context: &mut CanonicalCheckerContext<'_>, source: &ParseResult) -> TypeId {
    let root = annotation(source, "Dependent");
    let type_ = context.get_type_from_type_node(root).unwrap();
    let world = context.global_types().global_this_value_type;
    assert_ne!(type_, world);
    assert_eq!(
        context.store().type_node_links(root).unwrap().resolved_type,
        Some(type_),
    );
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(symbol(context, root)),
    );
    let dependency = match &source.arena.get(root.node).unwrap().data {
        NodeData::TypeLiteralNode(literal) => {
            let [property] = literal.members.nodes.as_slice() else {
                panic!("expected exactly the scope property")
            };
            let declaration = node(source, SOURCE_FILE, *property);
            let (name, annotation) = match &source.arena.get(*property).unwrap().data {
                NodeData::PropertySignatureDeclaration(property) => (property.name, property.type_),
                NodeData::PropertyDeclaration(property) => (property.name, property.type_.unwrap()),
                _ => panic!("expected the source property"),
            };
            let NodeData::Identifier(name) = &source.arena.get(name).unwrap().data else {
                panic!("expected the scope name")
            };
            assert_eq!(name.text, "scope");
            let property_symbol = symbol(context, declaration);
            assert_eq!(
                context
                    .store()
                    .symbol(property_symbol)
                    .unwrap()
                    .declarations(),
                Some(&[declaration][..]),
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(property_symbol)
                    .unwrap()
                    .resolved_type,
                Some(world),
            );
            let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("expected the source object")
            };
            assert_eq!(
                object.structured.properties.as_deref(),
                Some(&[property_symbol][..])
            );
            node(source, SOURCE_FILE, annotation)
        }
        NodeData::FunctionTypeNode(function) => {
            let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("expected the source callable")
            };
            assert_eq!(object.structured.call_signature_count, 1);
            let [signature] = object.structured.signatures.as_deref().unwrap() else {
                panic!("expected one call signature")
            };
            let signature = *signature;
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                world
            );
            let signature = context.store().signature(signature).unwrap();
            assert_eq!(signature.declaration(), Some(root));
            assert_eq!(signature.resolved_return_type(), Some(world));
            assert!(signature.parameters().is_empty());
            assert!(signature.type_parameters().is_empty());
            assert_eq!(signature.min_argument_count(), 0);
            assert_eq!(signature.target(), None);
            assert_eq!(signature.mapper(), None);
            node(source, SOURCE_FILE, function.type_.unwrap())
        }
        _ => panic!("expected the parsed object or callable type"),
    };
    let NodeData::TypeQueryNode(query) = &source.arena.get(dependency.node).unwrap().data else {
        panic!("expected the written typeof globalThis dependency")
    };
    assert_eq!(
        context
            .store()
            .type_node_links(dependency)
            .unwrap()
            .resolved_type,
        Some(world),
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(node(source, SOURCE_FILE, query.expr_name))
            .unwrap()
            .resolved_symbol,
        Some(
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .global_this_symbol
        ),
    );
    type_
}

fn assert_same_type(context: &mut CanonicalCheckerContext<'_>, type_: TypeId) {
    assert_eq!(context.is_type_assignable_to(type_, type_), Ok(true));
    assert_eq!(context.is_type_identical_to(type_, type_), Ok(true));
    assert_eq!(context.is_type_comparable_to(type_, type_), Ok(true));
}

fn check_dependency(source: &str) {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(source);
    for source_first in [false, true] {
        let mut context = context(&library, &source);
        let marker = symbol(&context, named(&library, LIBRARY_FILE, "marker"));
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        }
        let type_ = demand_dependency(&mut context, &source);
        assert_global_cold(&context, marker);
        let cold = global_publication(&context, marker);
        assert_same_type(&mut context, type_);
        assert_eq!(global_publication(&context, marker), cold);
        assert_global_cold(&context, marker);

        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let warm = global_publication(&context, marker);
        for _ in 0..2 {
            assert_eq!(demand_dependency(&mut context, &source), type_);
            assert_same_type(&mut context, type_);
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert!(context.diagnostics().is_empty());
            assert_eq!(global_publication(&context, marker), warm);
        }
    }
}

#[test]
fn identical_source_objects_do_not_demand_global_this_members() {
    check_dependency("type Dependent = { scope: typeof globalThis };\n");
}

#[test]
fn identical_source_callables_do_not_demand_global_this_members() {
    check_dependency("type Dependent = () => typeof globalThis;\n");
}

#[test]
fn different_source_objects_keep_their_property_mismatch() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(concat!(
        "type Numeric = { value: number };\n",
        "type Textual = { value: string };\n",
    ));
    let mut context = context(&library, &source);
    let nodes = ["Numeric", "Textual"].map(|name| annotation(&source, name));
    let [numeric, textual] = nodes.map(|node| context.get_type_from_type_node(node).unwrap());
    assert_ne!(numeric, textual);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for (type_, expected) in [
        (numeric, bootstrap.number_type),
        (textual, bootstrap.string_type),
    ] {
        let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
            panic!("expected the parsed property object")
        };
        let [property] = object.structured.properties.as_deref().unwrap() else {
            panic!("expected one value property")
        };
        assert_eq!(
            context.store().symbol(*property).unwrap().name().as_utf8(),
            Some("value")
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(*property)
                .unwrap()
                .resolved_type,
            Some(expected),
        );
    }
    for _ in 0..2 {
        assert_eq!(context.is_type_assignable_to(numeric, textual), Ok(false));
        assert_eq!(context.is_type_assignable_to(textual, numeric), Ok(false));
        assert_eq!(context.is_type_identical_to(numeric, textual), Ok(false));
        assert_eq!(
            nodes.map(|node| context.get_type_from_type_node(node).unwrap()),
            [numeric, textual],
        );
        context.recheck_source_file(SOURCE_FILE).unwrap();
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn identical_direct_global_this_keeps_its_missing_context_error() {
    // This is a bootstrap guard control, not a parsed source query.
    let mut store = CanonicalTypeMapperStore::new();
    let owner = store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
        .unwrap()
        .global_this_symbol;
    let world = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
        .unwrap();
    assert!(store.set_value_symbol_links(
        owner,
        ValueSymbolLinks {
            resolved_type: Some(world),
            ..ValueSymbolLinks::default()
        },
    ));
    let before = store.relation_state_snapshot();
    for _ in 0..2 {
        assert_eq!(
            store.is_type_assignable_to(world, world),
            Err(RelationUnavailable::UnsupportedStructuredType(world)),
        );
        assert_eq!(store.relation_state_snapshot(), before);
    }
}

#[test]
fn identical_endpoints_keep_foreign_type_and_malformed_intersection_errors() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file("type Foreign = { value: number };\n");
    let mut foreign_context = context(&library, &source);
    let foreign = foreign_context
        .get_type_from_type_node(annotation(&source, "Foreign"))
        .unwrap();

    let mut store = CanonicalTypeMapperStore::new();
    let number = store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
        .unwrap()
        .number_type;
    assert!(foreign_context.store().type_payload(foreign).is_some());
    assert!(store.type_payload(foreign).is_none());
    // Raw allocation preserves the duplicate entries. It does not publish a valid intersection.
    let malformed = store
        .alloc_intersection_type(ObjectFlags::NONE, vec![number, number])
        .unwrap();
    let TypeData::Intersection(intersection) = store.type_payload(malformed).unwrap().data() else {
        panic!("expected the allocated intersection")
    };
    assert_eq!(intersection.intersection.types, [number, number]);
    let before = (
        store.type_len(),
        store.signature_len(),
        store.mapper_len(),
        store.relation_state_snapshot(),
    );
    for _ in 0..2 {
        for (source, target) in [(foreign, foreign), (foreign, number), (number, foreign)] {
            assert_eq!(
                store.is_type_assignable_to(source, target),
                Err(RelationUnavailable::Type(foreign)),
            );
        }
        assert_eq!(
            store.is_type_assignable_to(malformed, malformed),
            Err(RelationUnavailable::MalformedIntersection(malformed)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.relation_state_snapshot(),
            ),
            before,
        );
    }
}
