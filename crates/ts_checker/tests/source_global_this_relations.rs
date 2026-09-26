use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks, RelationKind, SignatureId,
    SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks, signatures::SignatureFlags, type_records::StructuredTypeData,
    types::ObjectFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FIRST_FILE: FileId = FileId::new(202_830);
const SECOND_FILE: FileId = FileId::new(202_810);
const CONSUMER_FILE: FileId = FileId::new(202_820);
const ARRAYS: &str = "interface Array<T> {}\ninterface ReadonlyArray<T> {}\n";

#[derive(Clone, Copy)]
struct Source<'a> {
    file: FileId,
    parsed: &'a ParseResult,
    path: &'static str,
    declaration: bool,
    library: bool,
}

impl Source<'_> {
    fn node(self, node: NodeId) -> NodeRef {
        NodeRef::new(self.parsed.arena.id(), self.file, node)
    }

    fn named(self, expected: &str) -> NodeRef {
        self.parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let name = match &record.data {
                    NodeData::VariableDeclaration(data) => data.name,
                    NodeData::FunctionDeclaration(data) => data.name?,
                    NodeData::InterfaceDeclaration(data) => data.name,
                    NodeData::TypeAliasDeclaration(data) => data.name,
                    _ => return None,
                };
                let NodeData::Identifier(name) = &self.parsed.arena.get(name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(self.node(id))
            })
            .unwrap_or_else(|| panic!("missing declaration {expected}"))
    }

    fn annotation(self, expected: &str) -> NodeRef {
        let declaration = self.named(expected);
        let annotation = match &self.parsed.arena.get(declaration.node).unwrap().data {
            NodeData::VariableDeclaration(data) => data.type_.unwrap(),
            NodeData::TypeAliasDeclaration(data) => data.type_,
            _ => panic!("missing annotation for {expected}"),
        };
        self.node(annotation)
    }
}

fn sources<'a>(
    first: &'a ParseResult,
    second: &'a ParseResult,
    consumer: &'a ParseResult,
) -> [Source<'a>; 3] {
    [
        Source {
            file: FIRST_FILE,
            parsed: first,
            path: "\"/lib/lib.global-relations.d.ts\"",
            declaration: true,
            library: true,
        },
        Source {
            file: SECOND_FILE,
            parsed: second,
            path: "\"/project/additional-globals.d.ts\"",
            declaration: true,
            library: false,
        },
        Source {
            file: CONSUMER_FILE,
            parsed: consumer,
            path: "\"/project/global-relations.ts\"",
            declaration: false,
            library: false,
        },
    ]
}

fn context<'a>(sources: &[Source<'a>], strict_function_types: bool) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    // Binder allocation order is also different from the Program's file order.
    for source in sources.iter().rev() {
        assert!(source.parsed.diagnostics.is_empty());
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
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.parsed.arena, source.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        sources
            .iter()
            .map(|source| (source.file, &source.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            strict_function_types,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn assert_global_declaration(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
    expected_flags: SymbolFlags,
) -> SemanticSymbolId {
    let owner = symbol(context, declaration);
    let record = context.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), expected_flags);
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));
    assert_eq!(record.parent(), None);
    assert_eq!(
        context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get(record.name()),
        Some(owner)
    );
    owner
}

fn assert_cold(context: &CanonicalCheckerContext<'_>, source: Source<'_>, name: &str) {
    let owner = symbol(context, source.named(name));
    assert!(
        context
            .store()
            .value_symbol_links(owner)
            .is_none_or(|links| links.resolved_type.is_none())
    );
    let annotation = source.annotation(name);
    let mut nodes = vec![annotation];
    if let NodeData::TypeQueryNode(query) = &source.parsed.arena.get(annotation.node).unwrap().data
    {
        nodes.push(source.node(query.expr_name));
    }
    for node in nodes {
        assert!(context.store().type_node_links(node).is_none());
        assert!(context.store().symbol_node_links(node).is_none());
    }
}

fn query_types<const N: usize>(
    context: &mut CanonicalCheckerContext<'_>,
    consumer: Source<'_>,
    names: [&str; N],
) -> [TypeId; N] {
    names.map(|name| {
        context
            .get_type_from_type_node(consumer.annotation(name))
            .unwrap()
    })
}

fn assert_world_query(context: &CanonicalCheckerContext<'_>, consumer: Source<'_>) {
    let annotation = consumer.annotation("World");
    let NodeData::TypeQueryNode(query) = &consumer.parsed.arena.get(annotation.node).unwrap().data
    else {
        panic!("World must query the real global value")
    };
    let store = context.store();
    assert_eq!(
        store.type_node_links(annotation).unwrap().resolved_type,
        Some(context.global_types().global_this_value_type)
    );
    assert_eq!(
        store
            .symbol_node_links(consumer.node(query.expr_name))
            .unwrap()
            .resolved_symbol,
        Some(store.intrinsic_bootstrap().unwrap().global_this_symbol)
    );
}

fn assert_global_members(
    context: &CanonicalCheckerContext<'_>,
    expected_names: &[&str],
    properties: &[SemanticSymbolId],
) {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let global_type = context.global_types().global_this_value_type;
    let owner = bootstrap.global_this_symbol;
    let symbol = store.symbol(owner).unwrap();
    assert_eq!(symbol.flags(), SymbolFlags::MODULE | SymbolFlags::TRANSIENT);
    assert_eq!(symbol.check_flags(), CheckFlags::READONLY);
    assert!(symbol.declarations().is_none());
    assert!(symbol.value_declaration().is_none());
    assert!(symbol.parent().is_none());
    assert_eq!(symbol.exports(), Some(context.globals()));
    assert_eq!(
        store.value_symbol_links(owner).unwrap(),
        &ValueSymbolLinks {
            resolved_type: Some(global_type),
            ..ValueSymbolLinks::default()
        }
    );
    let record = store.type_payload(global_type).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    assert!(record.alias().is_none());
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    );
    let TypeData::Object(object) = record.data() else {
        panic!("globalThis must keep its canonical object")
    };
    assert!(object.target.is_none());
    assert!(object.mapper.is_none());
    assert_eq!(object.structured.properties.as_deref(), Some(properties));
    assert!(object.structured.signatures.is_none());
    assert_eq!(object.structured.call_signature_count, 0);
    assert!(
        object
            .structured
            .index_infos
            .as_deref()
            .unwrap_or_default()
            .is_empty()
    );
    let globals = store.symbol_table(context.globals()).unwrap();
    let mut expected = expected_names
        .iter()
        .map(|name| (name.to_string(), globals.get_source(name).unwrap()))
        .collect::<Vec<_>>();
    expected.sort_by(|left, right| left.0.cmp(&right.0));
    let mut actual = store
        .symbol_table(object.structured.members.unwrap())
        .unwrap()
        .iter()
        .map(|(name, symbol)| (name.as_utf8().unwrap().to_owned(), symbol))
        .collect::<Vec<_>>();
    actual.sort_by(|left, right| left.0.cmp(&right.0));
    assert_eq!(actual, expected);
}

type NodePublication = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<TypeAliasLinks>,
);
type SignaturePublication = (
    SignatureId,
    Option<NodeRef>,
    SignatureFlags,
    Vec<SemanticSymbolId>,
    i32,
    Option<TypeId>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    relations: [usize; 5],
    global: StructuredTypeData,
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    signatures: Vec<SignaturePublication>,
    sources: Vec<(FileId, Option<SourceFileLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

#[allow(clippy::too_many_lines)] // Snapshot every source, symbol and signature link without a query.
fn publication(context: &CanonicalCheckerContext<'_>, sources: &[Source<'_>]) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.properties_type_cache_len(),
        ],
        relations: [
            RelationKind::Identity,
            RelationKind::Assignable,
            RelationKind::Comparable,
            RelationKind::Subtype,
            RelationKind::StrictSubtype,
        ]
        .map(|relation| store.relation_cache_size(relation)),
        global: match store
            .type_payload(context.global_types().global_this_value_type)
            .unwrap()
            .data()
        {
            TypeData::Object(object) => object.structured.clone(),
            _ => panic!("globalThis must keep its canonical object"),
        },
        nodes: sources
            .iter()
            .flat_map(|source| {
                source.parsed.arena.iter().map(move |(node, _)| {
                    let node = source.node(node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect(),
        signatures: sources
            .iter()
            .flat_map(|source| {
                source.parsed.arena.iter().filter_map(move |(node, _)| {
                    let signature = store
                        .signature_links(source.node(node))?
                        .resolved_signature
                        .signature()?;
                    let record = store.signature(signature)?;
                    Some((
                        signature,
                        record.declaration(),
                        record.flags(),
                        record.parameters().to_vec(),
                        record.min_argument_count(),
                        record.resolved_return_type(),
                    ))
                })
            })
            .collect(),
        sources: sources
            .iter()
            .map(|source| {
                (
                    source.file,
                    store
                        .source_file_links(context.source_file(source.file).unwrap())
                        .cloned(),
                )
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_relations(context: &mut CanonicalCheckerContext<'_>, types: [TypeId; 8], strict: bool) {
    let [
        world,
        matching,
        wrong,
        wide,
        outer,
        outer_target,
        factory,
        factory_target,
    ] = types;
    assert_eq!(context.is_type_assignable_to(world, matching), Ok(true));
    assert_eq!(context.is_type_assignable_to(world, wrong), Ok(false));
    assert_eq!(context.is_type_assignable_to(world, wide), Ok(!strict));
    assert_eq!(context.is_type_assignable_to(outer, outer_target), Ok(true));
    assert_eq!(
        context.is_type_assignable_to(factory, factory_target),
        Ok(true)
    );
    assert_eq!(context.is_type_assignable_to(matching, world), Ok(false));
    assert_eq!(context.is_type_identical_to(world, world), Ok(true));
    assert_eq!(context.is_type_comparable_to(world, matching), Ok(true));
}

#[test]
#[allow(clippy::too_many_lines)] // Keep source order, both options and exact replay in one real fixture.
fn global_this_relations_keep_real_members_arrays_options_and_replay() {
    let first = parse_source_file(&format!(
        "{ARRAYS}declare var sequence: number;\ndeclare function convert(value: number): string;\n"
    ));
    let second = parse_source_file(concat!(
        "declare var labels: string[];\n",
        "declare var unused: typeof unused;\n",
        "declare let lexical: number;\n",
        "interface TypeOnly { value: number; }\n",
    ));
    let consumer = parse_source_file(concat!(
        "type World = typeof globalThis;\n",
        "type Match = { sequence: number; convert: (value: number) => string; labels: string[] };\n",
        "type Mismatch = { sequence: string };\n",
        "type WiderCall = { convert: (value: unknown) => string };\n",
        "type Outer = { scope: typeof globalThis };\n",
        "type OuterMatch = { scope: { sequence: number } };\n",
        "type Factory = () => typeof globalThis;\n",
        "type FactoryMatch = () => { labels: string[] };\n",
    ));
    let sources = sources(&first, &second, &consumer);
    let [first, second, consumer] = sources;
    let names = [
        "World",
        "Match",
        "Mismatch",
        "WiderCall",
        "Outer",
        "OuterMatch",
        "Factory",
        "FactoryMatch",
    ];
    for strict in [false, true] {
        for source_first in [false, true] {
            let mut context = context(&sources, strict);
            assert_eq!(
                context.file_order(),
                &[FIRST_FILE, SECOND_FILE, CONSUMER_FILE]
            );
            let sequence = assert_global_declaration(
                &context,
                first.named("sequence"),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            );
            let convert =
                assert_global_declaration(&context, first.named("convert"), SymbolFlags::FUNCTION);
            let labels = assert_global_declaration(
                &context,
                second.named("labels"),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            );
            let unused = symbol(&context, second.named("unused"));
            let lexical = assert_global_declaration(
                &context,
                second.named("lexical"),
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
            );
            assert_cold(&context, first, "sequence");
            assert_cold(&context, second, "labels");
            assert_cold(&context, second, "unused");
            if source_first {
                context.check_source_file(CONSUMER_FILE).unwrap();
            }
            let types = query_types(&mut context, consumer, names);
            let world = context.global_types().global_this_value_type;
            assert_eq!(types[0], world);
            assert_world_query(&context, consumer);
            assert_relations(&mut context, types, strict);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let number = bootstrap.number_type;
            let string = bootstrap.string_type;
            let properties = [
                sequence,
                convert,
                labels,
                unused,
                bootstrap.global_this_symbol,
                bootstrap.undefined_symbol,
            ];
            let members = [
                "Array",
                "ReadonlyArray",
                "sequence",
                "convert",
                "labels",
                "unused",
                "TypeOnly",
                "World",
                "Match",
                "Mismatch",
                "WiderCall",
                "Outer",
                "OuterMatch",
                "Factory",
                "FactoryMatch",
                "globalThis",
                "undefined",
            ];
            assert_global_members(&context, &members, &properties);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(sequence)
                    .unwrap()
                    .resolved_type,
                Some(number)
            );
            let array = context
                .store()
                .value_symbol_links(labels)
                .unwrap()
                .resolved_type
                .unwrap();
            let TypeData::TypeReference(reference) =
                context.store().type_payload(array).unwrap().data()
            else {
                panic!("the global array value must use its real Array target")
            };
            assert_eq!(
                reference.object.target,
                Some(context.global_types().array_type)
            );
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[string][..])
            );
            assert_eq!(
                context
                    .store()
                    .type_payload(reference.object.target.unwrap())
                    .unwrap()
                    .symbol(),
                Some(symbol(&context, first.named("Array")))
            );
            let callable = context
                .store()
                .value_symbol_links(convert)
                .unwrap()
                .resolved_type
                .unwrap();
            let record = context.store().type_payload(callable).unwrap();
            assert_eq!(record.symbol(), Some(convert));
            let TypeData::Object(object) = record.data() else {
                panic!("the declared global function must keep its callable object")
            };
            let [signature] = object.structured.signatures.as_deref().unwrap() else {
                panic!("the declared global function must keep its one real signature")
            };
            let signature = *signature;
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(first.named("convert")));
            assert_eq!(record.flags(), SignatureFlags::NONE);
            assert_eq!(record.min_argument_count(), 1);
            assert_eq!(record.resolved_return_type(), Some(string));
            assert!(record.target().is_none());
            assert!(record.mapper().is_none());
            let NodeData::FunctionDeclaration(function) = &first
                .parsed
                .arena
                .get(first.named("convert").node)
                .unwrap()
                .data
            else {
                unreachable!()
            };
            let parameter = symbol(&context, first.node(function.parameters.nodes[0]));
            assert_eq!(record.parameters(), &[parameter]);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter)
                    .unwrap()
                    .resolved_type,
                Some(number)
            );
            assert_eq!(context.get_return_type_of_signature(signature), Ok(string));
            assert_eq!(
                context.get_type_from_type_node(second.annotation("labels")),
                Ok(array)
            );
            context.check_source_file(CONSUMER_FILE).unwrap();
            assert!(context.diagnostics().is_empty());
            assert_cold(&context, second, "unused");
            assert_cold(&context, second, "lexical");
            let stable = publication(&context, &sources);
            for _ in 0..2 {
                assert_eq!(query_types(&mut context, consumer, names), types);
                assert_world_query(&context, consumer);
                assert_relations(&mut context, types, strict);
                assert_eq!(context.get_return_type_of_signature(signature), Ok(string));
                context.check_source_file(CONSUMER_FILE).unwrap();
                context.recheck_source_file(CONSUMER_FILE).unwrap();
                assert_global_members(&context, &members, &properties);
                assert_cold(&context, second, "unused");
                assert_cold(&context, second, "lexical");
                assert_eq!(
                    assert_global_declaration(
                        &context,
                        first.named("sequence"),
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    ),
                    sequence
                );
                assert_eq!(
                    assert_global_declaration(
                        &context,
                        first.named("convert"),
                        SymbolFlags::FUNCTION
                    ),
                    convert
                );
                assert_eq!(
                    assert_global_declaration(
                        &context,
                        second.named("labels"),
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    ),
                    labels
                );
                assert_eq!(
                    assert_global_declaration(
                        &context,
                        second.named("lexical"),
                        SymbolFlags::BLOCK_SCOPED_VARIABLE
                    ),
                    lexical
                );
                assert_eq!(publication(&context, &sources), stable);
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the direct and nested missing-member paths with their replay.
fn global_this_relations_stop_before_a_later_cyclic_member() {
    let first = parse_source_file(&format!("{ARRAYS}declare var steady: number;\n"));
    let second = parse_source_file("declare var circular: typeof circular;\n");
    let consumer = parse_source_file(concat!(
        "type World = typeof globalThis;\n",
        "type Needs = { absent: number; circular: number };\n",
        "type NestedWorld = { globals: typeof globalThis };\n",
        "type NestedNeeds = { globals: { absent: number; circular: number } };\n",
        "type FactoryWorld = () => typeof globalThis;\n",
        "type FactoryNeeds = () => { absent: number; circular: number };\n",
    ));
    let sources = sources(&first, &second, &consumer);
    let [first, second, consumer] = sources;
    let names = [
        "World",
        "Needs",
        "NestedWorld",
        "NestedNeeds",
        "FactoryWorld",
        "FactoryNeeds",
    ];
    for source_first in [false, true] {
        let mut context = context(&sources, true);
        if source_first {
            context.check_source_file(CONSUMER_FILE).unwrap();
        }
        let types = query_types(&mut context, consumer, names);
        assert_eq!(types[0], context.global_types().global_this_value_type);
        assert_world_query(&context, consumer);
        let TypeData::Object(needs) = context.store().type_payload(types[1]).unwrap().data() else {
            panic!("the target must keep its declared object")
        };
        let property_names = needs
            .structured
            .properties
            .as_ref()
            .unwrap()
            .iter()
            .map(|property| {
                context
                    .store()
                    .symbol(*property)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(property_names, ["absent", "circular"]);
        for pair in types.chunks_exact(2) {
            assert_eq!(context.is_type_assignable_to(pair[0], pair[1]), Ok(false));
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let properties = [
            symbol(&context, first.named("steady")),
            symbol(&context, second.named("circular")),
            bootstrap.global_this_symbol,
            bootstrap.undefined_symbol,
        ];
        let members = [
            "Array",
            "ReadonlyArray",
            "steady",
            "circular",
            "World",
            "Needs",
            "NestedWorld",
            "NestedNeeds",
            "FactoryWorld",
            "FactoryNeeds",
            "globalThis",
            "undefined",
        ];
        assert_global_members(&context, &members, &properties);
        assert_cold(&context, first, "steady");
        assert_cold(&context, second, "circular");
        context.check_source_file(CONSUMER_FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let stable = publication(&context, &sources);
        for _ in 0..2 {
            assert_eq!(query_types(&mut context, consumer, names), types);
            assert_world_query(&context, consumer);
            for pair in types.chunks_exact(2) {
                assert_eq!(context.is_type_assignable_to(pair[0], pair[1]), Ok(false));
            }
            context.check_source_file(CONSUMER_FILE).unwrap();
            context.recheck_source_file(CONSUMER_FILE).unwrap();
            assert_global_members(&context, &members, &properties);
            assert_cold(&context, first, "steady");
            assert_cold(&context, second, "circular");
            assert_eq!(publication(&context, &sources), stable);
        }
    }
}
