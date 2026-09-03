use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks, type_records::InterfaceTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(202_810);
const FIRST_SOURCE: FileId = FileId::new(202_811);
const SECOND_SOURCE: FileId = FileId::new(202_812);
const CONSUMER: FileId = FileId::new(202_813);

type Input<'a> = (FileId, &'a ParseResult, &'static str, bool, bool);

fn context<'a>(files: &[Input<'a>]) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, declaration, library) in files {
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
        files
            .iter()
            .map(|(file, parsed, ..)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn interface(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing interface {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn interface_data<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a InterfaceTypeData {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the declared interface must keep its own type")
    };
    data
}

fn member(parsed: &ParseResult, owner: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("the member must belong to its original interface")
    };
    interface
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let name = match &parsed.arena.get(*node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((
                NodeRef::new(owner.arena, owner.file, *node),
                NodeRef::new(owner.arena, owner.file, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing property {expected}"))
}

fn heritage_names(parsed: &ParseResult, owner: NodeRef) -> Vec<NodeRef> {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("heritage must belong to its original interface")
    };
    let clauses = interface.heritage_clauses.as_ref().unwrap();
    let [clause] = clauses.nodes.as_slice() else {
        panic!("expected one extends clause")
    };
    let record = parsed.arena.get(*clause).unwrap();
    assert_eq!(record.parent, Some(owner.node));
    let NodeData::HeritageClause(heritage) = &record.data else {
        unreachable!()
    };
    heritage
        .types
        .nodes
        .iter()
        .map(|node| {
            let record = parsed.arena.get(*node).unwrap();
            assert_eq!(record.parent, Some(*clause));
            let NodeData::ExpressionWithTypeArguments(base) = &record.data else {
                unreachable!()
            };
            assert!(base.type_arguments.is_none());
            assert_eq!(
                parsed.arena.get(base.expression).unwrap().parent,
                Some(*node)
            );
            NodeRef::new(owner.arena, owner.file, base.expression)
        })
        .collect()
}

fn property_access(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), CONSUMER, node))
        })
        .unwrap_or_else(|| panic!("missing read of {expected}"))
}

fn assert_property(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
    derived: TypeId,
    name: &str,
    expected_type: TypeId,
    access: Option<NodeRef>,
) -> SemanticSymbolId {
    let (property, property_name) = member(parsed, declaration, name);
    let owner = symbol(checker, declaration);
    let property_symbol = symbol(checker, property);
    let record = checker.store().symbol(property_symbol).unwrap();
    assert_eq!(record.declarations(), Some([property].as_slice()));
    assert_eq!(record.value_declaration(), Some(property));
    assert_eq!(
        checker.store().get_parent_of_symbol(property_symbol),
        Some(owner)
    );
    let structured = &interface_data(checker, derived).reference.object.structured;
    assert_eq!(
        checker
            .store()
            .symbol_table(structured.members.unwrap())
            .unwrap()
            .get_source(name),
        Some(property_symbol),
    );
    assert_eq!(
        structured
            .properties
            .as_ref()
            .unwrap()
            .iter()
            .filter(|id| **id == property_symbol)
            .count(),
        1
    );
    assert_eq!(
        checker.get_symbol_at_location(property_name),
        Ok(Some(property_symbol))
    );
    assert_eq!(
        checker.get_type_at_location(property_name),
        Ok(expected_type)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(property_symbol)
            .unwrap()
            .resolved_type,
        Some(expected_type)
    );
    if let Some(access) = access {
        assert_eq!(
            checker.get_symbol_at_location(access),
            Ok(Some(property_symbol))
        );
        assert_eq!(checker.get_type_at_location(access), Ok(expected_type));
    }
    property_symbol
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    interfaces: Vec<InterfaceTypeData>,
    nodes: Vec<(Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    properties: Vec<Option<ValueSymbolLinks>>,
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    types: &[TypeId],
    nodes: &[NodeRef],
    properties: &[SemanticSymbolId],
) -> Snapshot {
    let store = checker.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        interfaces: types
            .iter()
            .map(|type_| interface_data(checker, *type_).clone())
            .collect(),
        nodes: nodes
            .iter()
            .map(|node| {
                (
                    store.type_node_links(*node).cloned(),
                    store.symbol_node_links(*node).cloned(),
                )
            })
            .collect(),
        properties: properties
            .iter()
            .map(|symbol| store.value_symbol_links(*symbol).cloned())
            .collect(),
    }
}

fn assert_checked(checker: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(file).unwrap())
            .unwrap()
            .type_checked
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Keep both query orders and their replay checks together.
fn ordinary_interface_preserves_three_ordered_bases_cold_and_warm() {
    let source = parse_source_file(concat!(
        "interface First { first: string; } interface Second { second: number; } ",
        "interface Third { third: boolean; } ",
        "interface Combined extends First, Second, Third { own: number; } ",
        "declare const packet: Combined;",
    ));
    let consumer = parse_source_file(concat!(
        "const first: string = packet.first; const second: number = packet.second; ",
        "const third: boolean = packet.third;",
    ));
    let declarations =
        ["First", "Second", "Third", "Combined"].map(|name| interface(&source, FIRST_SOURCE, name));
    let base_nodes = heritage_names(&source, declarations[3]);
    assert_eq!(base_nodes.len(), 3);
    let accesses = ["first", "second", "third"].map(|name| property_access(&consumer, name));
    for query_first in [false, true] {
        let mut checker = context(&[
            (
                FIRST_SOURCE,
                &source,
                "\"/project/three-bases.d.ts\"",
                true,
                false,
            ),
            (
                CONSUMER,
                &consumer,
                "\"/project/three-bases.ts\"",
                false,
                false,
            ),
        ]);
        let owners = declarations.map(|node| symbol(&checker, node));
        assert!(
            owners
                .iter()
                .all(|owner| checker.store().declared_type_links(*owner).is_none())
        );
        let early = query_first.then(|| {
            let type_ = checker.get_declared_type_of_symbol(owners[3]).unwrap();
            let data = interface_data(&checker, type_);
            assert!(!data.base_types_resolved);
            assert!(!data.declared_members_resolved);
            let string_type = checker.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(checker.get_type_at_location(accesses[0]), Ok(string_type));
            let data = interface_data(&checker, type_);
            assert!(data.base_types_resolved);
            assert!(data.declared_members_resolved);
            let bases = owners[..3]
                .iter()
                .map(|owner| {
                    checker
                        .store()
                        .declared_type_links(*owner)
                        .unwrap()
                        .declared_type
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert_eq!(data.resolved_base_types.as_deref(), Some(bases.as_slice()));
            let properties = [
                symbol(&checker, member(&source, declarations[3], "own").0),
                symbol(&checker, member(&source, declarations[0], "first").0),
                symbol(&checker, member(&source, declarations[1], "second").0),
                symbol(&checker, member(&source, declarations[2], "third").0),
            ];
            assert_eq!(
                data.reference.object.structured.properties.as_deref(),
                Some(properties.as_slice())
            );
            type_
        });
        for file in [FIRST_SOURCE, CONSUMER] {
            checker.check_source_file(file).unwrap();
            assert_checked(&checker, file);
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let types = owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        if let Some(early) = early {
            assert_eq!(early, types[3]);
        }
        let query = |checker: &mut CanonicalCheckerContext<'_>| {
            assert_eq!(
                interface_data(checker, types[3])
                    .resolved_base_types
                    .as_deref(),
                Some(&types[..3])
            );
            for ((declaration, owner), type_) in declarations.into_iter().zip(owners).zip(types) {
                assert_eq!(checker.get_type_at_location(declaration), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(declaration), Ok(Some(owner)));
                assert_eq!(
                    checker.store().type_payload(type_).unwrap().symbol(),
                    Some(owner)
                );
            }
            for ((node, owner), type_) in base_nodes.iter().zip(owners).zip(types) {
                assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(owner)));
                assert_eq!(checker.get_type_at_location(*node), Ok(type_));
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let expected = [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            ];
            let mut properties = vec![assert_property(
                checker,
                &source,
                declarations[3],
                types[3],
                "own",
                expected[1],
                None,
            )];
            for (index, name) in ["first", "second", "third"].into_iter().enumerate() {
                properties.push(assert_property(
                    checker,
                    &source,
                    declarations[index],
                    types[3],
                    name,
                    expected[index],
                    Some(accesses[index]),
                ));
            }
            assert_eq!(
                interface_data(checker, types[3])
                    .reference
                    .object
                    .structured
                    .properties
                    .as_deref(),
                Some(properties.as_slice())
            );
            properties
        };
        let properties = query(&mut checker);
        let nodes = declarations
            .into_iter()
            .chain(base_nodes.iter().copied())
            .chain(accesses)
            .collect::<Vec<_>>();
        let warm = snapshot(&checker, &types, &nodes, &properties);
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            for file in [FIRST_SOURCE, CONSUMER] {
                checker.recheck_source_file(file).unwrap();
            }
            assert_eq!(query(&mut checker), properties);
            assert_eq!(
                snapshot(&checker, &types, &nodes, &properties),
                warm,
                "query_first={query_first}"
            );
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the native declarations, ordered bases, and value separation together.
fn native_merged_interface_preserves_later_distinct_and_repeated_bases() {
    let library = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {} ",
        "interface First { first: string; } interface Second { second: number; } ",
        "interface Third { third: boolean; } interface Fourth { fourth: string; } ",
        "interface NativePacket extends First, Second, Third { own: number; } ",
        "declare var NativePacket: { prototype: NativePacket; new(): NativePacket; };",
    ));
    let added = parse_source_file("interface NativePacket extends Fourth { added: string; }");
    let repeated = parse_source_file("interface NativePacket extends Third {}");
    let consumer = parse_source_file(concat!(
        "declare const nativePacket: NativePacket; const third: boolean = nativePacket.third; ",
        "const fourth: string = nativePacket.fourth;",
    ));
    let base_declarations =
        ["First", "Second", "Third", "Fourth"].map(|name| interface(&library, LIBRARY, name));
    let declarations = [
        interface(&library, LIBRARY, "NativePacket"),
        interface(&added, FIRST_SOURCE, "NativePacket"),
        interface(&repeated, SECOND_SOURCE, "NativePacket"),
    ];
    let base_nodes = heritage_names(&library, declarations[0])
        .into_iter()
        .chain(heritage_names(&added, declarations[1]))
        .chain(heritage_names(&repeated, declarations[2]))
        .collect::<Vec<_>>();
    assert_eq!(base_nodes.len(), 5);
    let (value_declaration, value_annotation) = library
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "NativePacket").then(|| {
                (
                    NodeRef::new(library.arena.id(), LIBRARY, node),
                    NodeRef::new(library.arena.id(), LIBRARY, variable.type_.unwrap()),
                )
            })
        })
        .unwrap();
    let accesses = ["third", "fourth"].map(|name| property_access(&consumer, name));
    for query_first in [false, true] {
        let mut checker = context(&[
            (
                LIBRARY,
                &library,
                "\"/lib/lib.native-bases.d.ts\"",
                true,
                true,
            ),
            (
                FIRST_SOURCE,
                &added,
                "\"/project/later-base.d.ts\"",
                true,
                false,
            ),
            (
                SECOND_SOURCE,
                &repeated,
                "\"/project/repeated-base.d.ts\"",
                true,
                false,
            ),
            (
                CONSUMER,
                &consumer,
                "\"/project/native-bases.ts\"",
                false,
                false,
            ),
        ]);
        assert_eq!(
            checker.file_order(),
            [LIBRARY, FIRST_SOURCE, SECOND_SOURCE, CONSUMER]
        );
        let owner = symbol(&checker, declarations[0]);
        let base_owners = base_declarations.map(|node| symbol(&checker, node));
        let assert_value_cold = |checker: &CanonicalCheckerContext<'_>| {
            let record = checker.store().symbol(owner).unwrap();
            assert_eq!(
                record.flags(),
                SymbolFlags::INTERFACE
                    | SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    | SymbolFlags::TRANSIENT
            );
            assert_eq!(
                record.declarations(),
                Some(
                    [
                        declarations[0],
                        value_declaration,
                        declarations[1],
                        declarations[2]
                    ]
                    .as_slice()
                )
            );
            assert_eq!(record.value_declaration(), Some(value_declaration));
            assert_eq!(symbol(checker, value_declaration), owner);
            for declaration in declarations {
                assert_eq!(symbol(checker, declaration), owner);
            }
            assert!(
                checker
                    .store()
                    .value_symbol_links(owner)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            assert!(
                checker
                    .store()
                    .type_node_links(value_annotation)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(LIBRARY).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        };
        assert_value_cold(&checker);
        assert!(checker.store().declared_type_links(owner).is_none());
        let early = query_first.then(|| {
            let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
            let data = interface_data(&checker, type_);
            assert!(!data.base_types_resolved);
            assert!(!data.declared_members_resolved);
            assert!(data.resolved_base_types.is_none());
            type_
        });
        assert_value_cold(&checker);
        for file in [FIRST_SOURCE, SECOND_SOURCE, CONSUMER] {
            checker.check_source_file(file).unwrap();
            assert_checked(&checker, file);
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
        let bases = base_owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        if let Some(early) = early {
            assert_eq!(early, type_);
        }
        let query = |checker: &mut CanonicalCheckerContext<'_>| {
            assert_value_cold(checker);
            assert_eq!(
                checker.store().type_payload(type_).unwrap().symbol(),
                Some(owner)
            );
            for declaration in declarations {
                assert_eq!(checker.get_type_at_location(declaration), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(declaration), Ok(Some(owner)));
            }
            let ordered_bases = [bases[0], bases[1], bases[2], bases[3], bases[2]];
            assert_eq!(
                interface_data(checker, type_)
                    .resolved_base_types
                    .as_deref(),
                Some(ordered_bases.as_slice())
            );
            for (node, index) in base_nodes.iter().zip([0, 1, 2, 3, 2]) {
                assert_eq!(
                    checker.get_symbol_at_location(*node),
                    Ok(Some(base_owners[index]))
                );
                assert_eq!(checker.get_type_at_location(*node), Ok(bases[index]));
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let expected = [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
                bootstrap.string_type,
            ];
            let mut properties = vec![
                assert_property(
                    checker,
                    &library,
                    declarations[0],
                    type_,
                    "own",
                    expected[1],
                    None,
                ),
                assert_property(
                    checker,
                    &added,
                    declarations[1],
                    type_,
                    "added",
                    expected[0],
                    None,
                ),
            ];
            for (index, name) in ["first", "second", "third", "fourth"]
                .into_iter()
                .enumerate()
            {
                let access = match index {
                    2 => Some(accesses[0]),
                    3 => Some(accesses[1]),
                    _ => None,
                };
                properties.push(assert_property(
                    checker,
                    &library,
                    base_declarations[index],
                    type_,
                    name,
                    expected[index],
                    access,
                ));
            }
            assert_eq!(
                interface_data(checker, type_)
                    .reference
                    .object
                    .structured
                    .properties
                    .as_deref(),
                Some(properties.as_slice())
            );
            assert_value_cold(checker);
            properties
        };
        let properties = query(&mut checker);
        let snapshot_types = std::iter::once(type_).chain(bases).collect::<Vec<_>>();
        let nodes = declarations
            .into_iter()
            .chain(base_nodes.iter().copied())
            .chain(accesses)
            .chain([value_declaration, value_annotation])
            .collect::<Vec<_>>();
        let symbols = properties
            .iter()
            .copied()
            .chain([owner])
            .collect::<Vec<_>>();
        let warm = snapshot(&checker, &snapshot_types, &nodes, &symbols);
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            for file in [FIRST_SOURCE, SECOND_SOURCE, CONSUMER] {
                checker.recheck_source_file(file).unwrap();
            }
            assert_eq!(query(&mut checker), properties);
            assert_eq!(
                snapshot(&checker, &snapshot_types, &nodes, &symbols),
                warm,
                "query_first={query_first}"
            );
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the transitive owner checks and both query orders together.
fn leaf_interface_preserves_properties_from_a_three_base_interface() {
    let file = FileId::new(202_814);
    let source = parse_source_file(concat!(
        "interface First { first: string; } interface Second { second: number; } ",
        "interface Third { third: boolean; } ",
        "interface Wide extends First, Second, Third {}; ",
        "interface Leaf extends Wide { own:number } declare const leaf: Leaf;",
    ));
    let consumer = parse_source_file(concat!(
        "const first: string = leaf.first; const second: number = leaf.second; ",
        "const third: boolean = leaf.third; const own: number = leaf.own;",
    ));
    let declarations =
        ["First", "Second", "Third", "Wide", "Leaf"].map(|name| interface(&source, file, name));
    let wide_bases = heritage_names(&source, declarations[3]);
    let leaf_bases = heritage_names(&source, declarations[4]);
    assert_eq!(wide_bases.len(), 3);
    assert_eq!(leaf_bases.len(), 1);
    let accesses = ["first", "second", "third", "own"].map(|name| property_access(&consumer, name));
    for query_first in [false, true] {
        let mut checker = context(&[
            (
                file,
                &source,
                "\"/project/transitive-bases.d.ts\"",
                true,
                false,
            ),
            (
                CONSUMER,
                &consumer,
                "\"/project/transitive-bases.ts\"",
                false,
                false,
            ),
        ]);
        let owners = declarations.map(|node| symbol(&checker, node));
        assert!(
            owners
                .iter()
                .all(|owner| checker.store().declared_type_links(*owner).is_none())
        );
        let early = query_first.then(|| {
            let type_ = checker.get_declared_type_of_symbol(owners[4]).unwrap();
            let data = interface_data(&checker, type_);
            assert!(!data.base_types_resolved);
            assert!(!data.declared_members_resolved);
            let string_type = checker.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(checker.get_type_at_location(accesses[0]), Ok(string_type));
            let data = interface_data(&checker, type_);
            assert!(data.base_types_resolved);
            assert!(data.declared_members_resolved);
            let bases = owners[..4]
                .iter()
                .map(|owner| {
                    checker
                        .store()
                        .declared_type_links(*owner)
                        .unwrap()
                        .declared_type
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert_eq!(
                data.resolved_base_types.as_deref(),
                Some([bases[3]].as_slice())
            );
            let wide = interface_data(&checker, bases[3]);
            assert!(wide.base_types_resolved);
            assert!(wide.declared_members_resolved);
            assert_eq!(wide.resolved_base_types.as_deref(), Some(&bases[..3]));
            let inherited = [
                symbol(&checker, member(&source, declarations[0], "first").0),
                symbol(&checker, member(&source, declarations[1], "second").0),
                symbol(&checker, member(&source, declarations[2], "third").0),
            ];
            assert_eq!(
                wide.reference.object.structured.properties.as_deref(),
                Some(inherited.as_slice())
            );
            let properties =
                std::iter::once(symbol(&checker, member(&source, declarations[4], "own").0))
                    .chain(inherited)
                    .collect::<Vec<_>>();
            assert_eq!(
                data.reference.object.structured.properties.as_deref(),
                Some(properties.as_slice())
            );
            type_
        });
        for file in [file, CONSUMER] {
            checker.check_source_file(file).unwrap();
            assert_checked(&checker, file);
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let types = owners.map(|owner| checker.get_declared_type_of_symbol(owner).unwrap());
        if let Some(early) = early {
            assert_eq!(early, types[4]);
        }
        let query = |checker: &mut CanonicalCheckerContext<'_>| {
            assert_eq!(
                interface_data(checker, types[3])
                    .resolved_base_types
                    .as_deref(),
                Some(&types[..3])
            );
            assert_eq!(
                interface_data(checker, types[4])
                    .resolved_base_types
                    .as_deref(),
                Some([types[3]].as_slice())
            );
            for ((declaration, owner), type_) in declarations.into_iter().zip(owners).zip(types) {
                assert_eq!(checker.get_type_at_location(declaration), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(declaration), Ok(Some(owner)));
                assert_eq!(
                    checker.store().type_payload(type_).unwrap().symbol(),
                    Some(owner)
                );
            }
            for (node, index) in wide_bases.iter().chain(&leaf_bases).zip([0, 1, 2, 3]) {
                assert_eq!(
                    checker.get_symbol_at_location(*node),
                    Ok(Some(owners[index]))
                );
                assert_eq!(checker.get_type_at_location(*node), Ok(types[index]));
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let expected = [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            ];
            let own = assert_property(
                checker,
                &source,
                declarations[4],
                types[4],
                "own",
                expected[1],
                Some(accesses[3]),
            );
            let mut inherited = Vec::new();
            for (index, name) in ["first", "second", "third"].into_iter().enumerate() {
                let from_wide = assert_property(
                    checker,
                    &source,
                    declarations[index],
                    types[3],
                    name,
                    expected[index],
                    None,
                );
                let from_leaf = assert_property(
                    checker,
                    &source,
                    declarations[index],
                    types[4],
                    name,
                    expected[index],
                    Some(accesses[index]),
                );
                assert_eq!(from_leaf, from_wide);
                inherited.push(from_leaf);
            }
            assert_eq!(
                interface_data(checker, types[3])
                    .reference
                    .object
                    .structured
                    .properties
                    .as_deref(),
                Some(inherited.as_slice())
            );
            let properties = std::iter::once(own).chain(inherited).collect::<Vec<_>>();
            assert_eq!(
                interface_data(checker, types[4])
                    .reference
                    .object
                    .structured
                    .properties
                    .as_deref(),
                Some(properties.as_slice())
            );
            properties
        };
        let properties = query(&mut checker);
        let nodes = declarations
            .into_iter()
            .chain(wide_bases.iter().copied())
            .chain(leaf_bases.iter().copied())
            .chain(accesses)
            .collect::<Vec<_>>();
        let warm = snapshot(&checker, &types, &nodes, &properties);
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            for file in [file, CONSUMER] {
                checker.recheck_source_file(file).unwrap();
            }
            assert_eq!(query(&mut checker), properties);
            assert_eq!(
                snapshot(&checker, &types, &nodes, &properties),
                warm,
                "query_first={query_first}"
            );
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
}
