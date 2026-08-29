use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(98_810);
const EMPTY_FILE: FileId = FileId::new(98_811);
const ADDED_FILE: FileId = FileId::new(98_812);
const CONSUMER_FILE: FileId = FileId::new(98_813);

const LIBRARY: &str = concat!(
    "interface Array<T> {}\n",
    "interface ReadonlyArray<T> {}\n",
    "interface SignalPacket { original: string; readOriginal(): string; }\n",
    "declare var SignalPacket: {\n",
    "  readonly prototype: SignalPacket;\n",
    "  new (original: string): SignalPacket;\n",
    "  readonly kind: number;\n",
    "};\n",
);
const EMPTY: &str = "interface SignalPacket {}";
const ADDED: &str = "interface SignalPacket { added: number; readAdded(): number; }";

fn context<'a>(
    library: &'a ParseResult,
    empty: &'a ParseResult,
    added: &'a ParseResult,
    consumer: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    context_with_intrinsic(
        library,
        empty,
        added,
        consumer,
        IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
    )
}

fn context_with_intrinsic<'a>(
    library: &'a ParseResult,
    empty: &'a ParseResult,
    added: &'a ParseResult,
    consumer: &'a ParseResult,
    intrinsic: IntrinsicBootstrapOptions,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration, default_library) in [
        (library, LIBRARY_FILE, "\"/lib/lib.merge.d.ts\"", true, true),
        (empty, EMPTY_FILE, "\"/project/empty.d.ts\"", true, false),
        (added, ADDED_FILE, "\"/project/added.d.ts\"", true, false),
        (
            consumer,
            CONSUMER_FILE,
            "\"/project/consumer.ts\"",
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
        vec![
            (LIBRARY_FILE, &library.arena),
            (EMPTY_FILE, &empty.arena),
            (ADDED_FILE, &added.arena),
            (CONSUMER_FILE, &consumer.arena),
        ],
        CanonicalCheckerOptions {
            intrinsic,
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn interface(parsed: &ParseResult, file: FileId) -> NodeRef {
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
            (name.text == "SignalPacket").then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap()
}

fn variable(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, variable.name),
                    NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing annotated variable {expected}"))
}

fn member(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, name),
            ))
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn merged_symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn members(
    checker: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
) -> Vec<(String, SemanticSymbolId)> {
    let table = checker.store().symbol(owner).unwrap().members().unwrap();
    checker
        .store()
        .symbol_table(table)
        .unwrap()
        .iter()
        .map(|(name, symbol)| {
            (
                name.as_utf8().unwrap().to_owned(),
                checker.store().get_merged_symbol(symbol).unwrap(),
            )
        })
        .collect()
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
    ]
}

fn assert_value_annotation_cold(
    checker: &CanonicalCheckerContext<'_>,
    library: &ParseResult,
    owner: SemanticSymbolId,
) {
    let (declaration, _, annotation) = variable(library, LIBRARY_FILE, "SignalPacket");
    assert_eq!(
        checker.store().symbol(owner).unwrap().value_declaration(),
        Some(declaration),
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type),
        None,
    );
    assert_eq!(
        checker
            .store()
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type),
        None,
    );
    let NodeData::VariableDeclaration(value) = &library.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(value.type_, Some(annotation.node));
}

fn demand_members(
    checker: &mut CanonicalCheckerContext<'_>,
    library: &ParseResult,
    added: &ParseResult,
) -> [TypeId; 4] {
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    [
        (library, LIBRARY_FILE, "original", false, string),
        (library, LIBRARY_FILE, "readOriginal", true, string),
        (added, ADDED_FILE, "added", false, number),
        (added, ADDED_FILE, "readAdded", true, number),
    ]
    .map(|(parsed, file, name, method, expected)| {
        let (declaration, name_node) = member(parsed, file, name);
        let symbol = merged_symbol(checker, declaration);
        let owner = merged_symbol(checker, interface(parsed, file));
        assert_eq!(checker.store().get_parent_of_symbol(symbol), Some(owner));
        let type_ = checker.get_type_at_location(name_node).unwrap();
        assert_eq!(
            checker.get_symbol_at_location(name_node).unwrap(),
            Some(symbol)
        );
        if method {
            let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data()
            else {
                panic!("the selected method must be callable");
            };
            let [signature] = object.structured.signatures.as_deref().unwrap() else {
                panic!("the selected method must have one signature");
            };
            let signature = *signature;
            assert!(
                checker
                    .store()
                    .signature(signature)
                    .unwrap()
                    .parameters()
                    .is_empty()
            );
            assert_eq!(
                checker.get_return_type_of_signature(signature).unwrap(),
                expected
            );
        } else {
            assert_eq!(type_, expected);
        }
        type_
    })
}

#[test]
fn merged_global_interface_identity_keeps_constructor_annotation_cold() {
    for source_first in [false, true] {
        let library = parse_source_file(LIBRARY);
        let empty = parse_source_file(EMPTY);
        let added = parse_source_file("");
        let consumer = parse_source_file("declare const packet: SignalPacket;");
        let mut checker = context(&library, &empty, &added, &consumer);
        let library_interface = interface(&library, LIBRARY_FILE);
        let empty_interface = interface(&empty, EMPTY_FILE);
        let owner = merged_symbol(&checker, library_interface);
        assert_eq!(merged_symbol(&checker, empty_interface), owner);
        let declarations = checker
            .store()
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        let original_members = members(&checker, owner);
        let signatures = checker.store().signature_len();
        assert_eq!(
            checker.store().symbol(owner).unwrap().flags(),
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
        );
        assert_value_annotation_cold(&checker, &library, owner);
        if source_first {
            checker.check_source_file(EMPTY_FILE).unwrap();
        }
        let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
        let (_, _, annotation) = variable(&consumer, CONSUMER_FILE, "packet");
        assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), type_);
        if !source_first {
            checker.check_source_file(EMPTY_FILE).unwrap();
        }
        assert!(matches!(
            checker.store().type_payload(type_).unwrap().data(),
            TypeData::Interface(_)
        ));
        assert_eq!(
            checker.store().type_payload(type_).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(
            checker.get_type_at_location(empty_interface).unwrap(),
            type_
        );
        assert_value_annotation_cold(&checker, &library, owner);
        assert_eq!(checker.store().signature_len(), signatures);
        for (_, member) in &original_members {
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(*member)
                    .and_then(|links| links.resolved_type),
                None,
            );
        }
        assert_eq!(members(&checker, owner), original_members);
        assert_eq!(
            checker.store().symbol(owner).unwrap().declarations(),
            Some(declarations.as_slice())
        );
        assert!(checker.diagnostics().is_empty());

        let warm = counts(&checker);
        checker.recheck_source_file(EMPTY_FILE).unwrap();
        assert_eq!(checker.get_declared_type_of_symbol(owner).unwrap(), type_);
        assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), type_);
        assert_eq!(counts(&checker), warm);
        assert_value_annotation_cold(&checker, &library, owner);
        assert_eq!(members(&checker, owner), original_members);
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check source order, member demand order, and replay together.
fn merged_global_interface_members_survive_source_and_query_order() {
    for query_first in [false, true] {
        for added_first in [false, true] {
            let library = parse_source_file(LIBRARY);
            let empty = parse_source_file(EMPTY);
            let added = parse_source_file(ADDED);
            let consumer = parse_source_file(concat!(
                "declare const packet: SignalPacket;\n",
                "const original: string = packet.original;\n",
                "const added: number = packet.added;\n",
                "const wrong: string = packet.added;\n",
            ));
            let mut checker = context(&library, &empty, &added, &consumer);
            let owner = merged_symbol(&checker, interface(&library, LIBRARY_FILE));
            assert_eq!(
                merged_symbol(&checker, interface(&empty, EMPTY_FILE)),
                owner
            );
            assert_eq!(
                merged_symbol(&checker, interface(&added, ADDED_FILE)),
                owner
            );
            let original_members = members(&checker, owner);
            let mut names = original_members
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>();
            names.sort_unstable();
            assert_eq!(names, ["added", "original", "readAdded", "readOriginal"],);
            let early = query_first.then(|| demand_members(&mut checker, &library, &added));
            let order = if added_first {
                [ADDED_FILE, EMPTY_FILE]
            } else {
                [EMPTY_FILE, ADDED_FILE]
            };
            for file in order {
                checker.check_source_file(file).unwrap();
            }
            let member_types = demand_members(&mut checker, &library, &added);
            if let Some(early) = early {
                assert_eq!(member_types, early);
            }
            let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
            assert_value_annotation_cold(&checker, &library, owner);
            checker.check_source_file(CONSUMER_FILE).unwrap();
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("only the wrong added-property assignment must fail");
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            let (_, wrong, _) = variable(&consumer, CONSUMER_FILE, "wrong");
            assert_eq!(diagnostic.node, Some(wrong));
            assert_eq!(members(&checker, owner), original_members);
            let (_, _, annotation) = variable(&consumer, CONSUMER_FILE, "packet");
            assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), type_);
            assert_value_annotation_cold(&checker, &library, owner);

            let warm = counts(&checker);
            let diagnostics = checker.diagnostics().clone();
            for file in order.into_iter().chain([CONSUMER_FILE]) {
                checker.recheck_source_file(file).unwrap();
            }
            assert_eq!(demand_members(&mut checker, &library, &added), member_types);
            assert_eq!(checker.get_declared_type_of_symbol(owner).unwrap(), type_);
            assert_eq!(members(&checker, owner), original_members);
            assert_eq!(counts(&checker), warm);
            assert_eq!(checker.diagnostics(), &diagnostics);
            assert_value_annotation_cold(&checker, &library, owner);
        }
    }
}

#[test]
fn merged_global_interface_value_type_is_independent_of_its_instance_type() {
    for value_first in [false, true] {
        let library = parse_source_file(concat!(
            "interface SignalPacket { original: string; readOriginal(): string; }\n",
            "declare var SignalPacket: number;\n",
        ));
        let empty = parse_source_file(EMPTY);
        let added = parse_source_file(ADDED);
        let consumer = parse_source_file(concat!(
            "const current: number = SignalPacket;\n",
            "const wrong: string = SignalPacket;\n",
        ));
        let mut checker = context(&library, &empty, &added, &consumer);
        let owner = merged_symbol(&checker, interface(&library, LIBRARY_FILE));
        let (value_declaration, value_name, annotation) =
            variable(&library, LIBRARY_FILE, "SignalPacket");
        assert_eq!(merged_symbol(&checker, value_declaration), owner);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        if value_first {
            assert_eq!(checker.get_type_at_location(value_name).unwrap(), number);
        }
        let instance = checker.get_declared_type_of_symbol(owner).unwrap();
        assert!(matches!(
            checker.store().type_payload(instance).unwrap().data(),
            TypeData::Interface(_)
        ));
        assert_ne!(instance, number);
        assert_eq!(checker.get_type_at_location(value_name).unwrap(), number);
        assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), number);
        assert_eq!(
            checker.get_symbol_at_location(value_name).unwrap(),
            Some(owner)
        );
        assert_eq!(
            checker.store().symbol(owner).unwrap().value_declaration(),
            Some(value_declaration)
        );
        for file in [EMPTY_FILE, ADDED_FILE, CONSUMER_FILE] {
            checker.check_source_file(file).unwrap();
        }
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("only the wrong value assignment must fail");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        let (_, wrong, _) = variable(&consumer, CONSUMER_FILE, "wrong");
        assert_eq!(diagnostic.node, Some(wrong));
        assert_eq!(
            checker.get_declared_type_of_symbol(owner).unwrap(),
            instance
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type),
            Some(number),
        );

        let warm = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        for file in [ADDED_FILE, EMPTY_FILE, CONSUMER_FILE] {
            checker.recheck_source_file(file).unwrap();
        }
        assert_eq!(checker.get_type_at_location(value_name).unwrap(), number);
        assert_eq!(
            checker.get_declared_type_of_symbol(owner).unwrap(),
            instance
        );
        assert_eq!(counts(&checker), warm);
        assert_eq!(checker.diagnostics(), &diagnostics);
    }
}

const NULL_CHECK_MODES: [IntrinsicBootstrapOptions; 3] = [
    IntrinsicBootstrapOptions {
        strict_null_checks: false,
        exact_optional_property_types: false,
    },
    IntrinsicBootstrapOptions {
        strict_null_checks: true,
        exact_optional_property_types: false,
    },
    IntrinsicBootstrapOptions {
        strict_null_checks: true,
        exact_optional_property_types: true,
    },
];

fn check_duplicate_property(
    added_source: &str,
    intrinsic: IntrinsicBootstrapOptions,
    expected_type_error: Option<&str>,
    modifier_error: bool,
) {
    check_duplicate_property_in_library(
        LIBRARY,
        added_source,
        intrinsic,
        expected_type_error.map(|type_| ("string", type_)),
        modifier_error,
    );
}

fn check_duplicate_property_in_library(
    library_source: &str,
    added_source: &str,
    intrinsic: IntrinsicBootstrapOptions,
    expected_type_error: Option<(&str, &str)>,
    modifier_error: bool,
) {
    let library = parse_source_file(library_source);
    let empty = parse_source_file(EMPTY);
    let added = parse_source_file(added_source);
    let consumer = parse_source_file("");
    let mut checker = context_with_intrinsic(&library, &empty, &added, &consumer, intrinsic);
    let owner = merged_symbol(&checker, interface(&library, LIBRARY_FILE));
    assert_eq!(
        merged_symbol(&checker, interface(&added, ADDED_FILE)),
        owner
    );
    let original_members = members(&checker, owner);
    let (first_declaration, _) = member(&library, LIBRARY_FILE, "original");
    let (_, second_name) = member(&added, ADDED_FILE, "original");

    // Check only the ordinary contribution, not the default library declaration.
    checker.check_source_file(ADDED_FILE).unwrap();
    let diagnostics = checker.diagnostics().as_slice();
    let expected_codes = expected_type_error
        .map(|_| 2717)
        .into_iter()
        .chain(modifier_error.then_some(2687))
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        expected_codes,
        "source: {added_source}, options: {intrinsic:?}",
    );
    for diagnostic in diagnostics {
        assert_eq!(diagnostic.node, Some(second_name));
        assert_eq!(diagnostic.range_override, None);
    }
    if let Some((expected_first, expected_second)) = expected_type_error {
        let diagnostic = &diagnostics[0];
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["original", expected_first, expected_second],
        );
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the type conflict must refer to the first declaration");
        };
        assert_eq!(related.node, Some(first_declaration));
        assert_eq!(related.diagnostic.code(), 6203);
        assert_eq!(related.diagnostic.arguments, ["original"]);
    }
    if modifier_error {
        let diagnostic = diagnostics.last().unwrap();
        assert_eq!(diagnostic.diagnostic.arguments, ["original"]);
        assert!(diagnostic.related_information.is_empty());
    }
    assert_eq!(members(&checker, owner), original_members);
    assert_value_annotation_cold(&checker, &library, owner);

    let diagnostics = checker.diagnostics().clone();
    let warm = counts(&checker);
    checker.recheck_source_file(ADDED_FILE).unwrap();
    assert_eq!(checker.diagnostics(), &diagnostics);
    assert_eq!(counts(&checker), warm);
    assert_eq!(members(&checker, owner), original_members);
    assert_value_annotation_cold(&checker, &library, owner);
}

#[test]
fn merged_global_interface_duplicate_properties_accept_the_same_type() {
    for intrinsic in NULL_CHECK_MODES {
        check_duplicate_property(
            "interface SignalPacket { original: string; }",
            intrinsic,
            None,
            false,
        );
    }
}

#[test]
fn merged_global_interface_duplicate_property_types_report_the_secondary_name() {
    for intrinsic in NULL_CHECK_MODES {
        check_duplicate_property(
            "interface SignalPacket { original: number; }",
            intrinsic,
            Some("number"),
            false,
        );
    }
}

#[test]
fn merged_global_interface_duplicate_readonly_modifiers_report_the_secondary_name() {
    for intrinsic in NULL_CHECK_MODES {
        check_duplicate_property(
            "interface SignalPacket { readonly original: string; }",
            intrinsic,
            None,
            true,
        );
    }
}

#[test]
fn merged_global_interface_duplicate_optional_properties_keep_each_declaration_type() {
    for intrinsic in NULL_CHECK_MODES {
        check_duplicate_property(
            "interface SignalPacket { original?: string; }",
            intrinsic,
            intrinsic.strict_null_checks.then_some("string | undefined"),
            true,
        );
    }
}

#[test]
fn merged_global_interface_duplicate_literal_type_is_not_widened_in_diagnostics() {
    let library = concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "interface SignalPacket { original: \"literal\"; readOriginal(): string; }\n",
        "declare var SignalPacket: {\n",
        "  readonly prototype: SignalPacket;\n",
        "  new (original: string): SignalPacket;\n",
        "  readonly kind: number;\n",
        "};\n",
    );
    for intrinsic in NULL_CHECK_MODES {
        check_duplicate_property_in_library(
            library,
            "interface SignalPacket { original: string; }",
            intrinsic,
            Some(("\"literal\"", "string")),
            false,
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check inherited queries, source order, and replay together.
fn merged_global_interface_inherited_members_survive_source_and_query_order() {
    for query_first in [false, true] {
        for added_first in [false, true] {
            let library = parse_source_file(concat!(
                "interface Array<T> {}\n",
                "interface ReadonlyArray<T> {}\n",
                "interface SignalPacket extends SharedBase { original: string; }\n",
            ));
            let empty = parse_source_file(EMPTY);
            let added = parse_source_file(concat!(
                "interface SharedBase { inherited: boolean; }\n",
                "interface SignalPacket { added: number; }\n",
            ));
            let consumer = parse_source_file(concat!(
                "declare const packet: SignalPacket;\n",
                "const original: string = packet.original;\n",
                "const inherited: boolean = packet.inherited;\n",
                "const added: number = packet.added;\n",
                "const wrong: string = packet.added;\n",
            ));
            let mut checker = context(&library, &empty, &added, &consumer);
            let owner = merged_symbol(&checker, interface(&library, LIBRARY_FILE));
            assert_eq!(
                merged_symbol(&checker, interface(&empty, EMPTY_FILE)),
                owner
            );
            assert_eq!(
                merged_symbol(&checker, interface(&added, ADDED_FILE)),
                owner
            );
            assert_eq!(
                checker.store().symbol(owner).unwrap().value_declaration(),
                None
            );
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let fields = [
                ("original", &library, LIBRARY_FILE, bootstrap.string_type),
                ("added", &added, ADDED_FILE, bootstrap.number_type),
                ("inherited", &added, ADDED_FILE, bootstrap.boolean_type),
            ];
            let symbols = fields.map(|(name, parsed, file, _)| {
                merged_symbol(&checker, member(parsed, file, name).0)
            });
            let accesses = fields.map(|(expected, _, _, _)| {
                consumer
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        let NodeData::PropertyAccessExpression(access) = &record.data else {
                            return None;
                        };
                        let NodeData::Identifier(name) = &consumer.arena.get(access.name)?.data
                        else {
                            return None;
                        };
                        (name.text == expected).then_some(NodeRef::new(
                            consumer.arena.id(),
                            CONSUMER_FILE,
                            node,
                        ))
                    })
                    .unwrap()
            });
            let (_, _, annotation) = variable(&consumer, CONSUMER_FILE, "packet");
            let query = |checker: &mut CanonicalCheckerContext<'_>| {
                let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
                assert_eq!(checker.get_type_from_type_node(annotation).unwrap(), type_);
                for ((access, symbol), (_, _, _, expected)) in
                    accesses.into_iter().zip(symbols).zip(fields)
                {
                    assert_eq!(checker.get_type_at_location(access).unwrap(), expected);
                    assert_eq!(
                        checker.get_symbol_at_location(access).unwrap(),
                        Some(symbol)
                    );
                }
                type_
            };
            let early = query_first.then(|| query(&mut checker));
            let order = if added_first {
                [ADDED_FILE, EMPTY_FILE]
            } else {
                [EMPTY_FILE, ADDED_FILE]
            };
            for file in order {
                checker.check_source_file(file).unwrap();
            }
            let type_ = query(&mut checker);
            if let Some(early) = early {
                assert_eq!(type_, early);
            }
            checker.check_source_file(CONSUMER_FILE).unwrap();
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("only the wrong added-property assignment must fail");
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            assert_eq!(
                diagnostic.node,
                Some(variable(&consumer, CONSUMER_FILE, "wrong").1)
            );
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());

            let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data()
            else {
                panic!("the merged type must retain its interface identity");
            };
            assert!(data.base_types_resolved);
            assert!(data.declared_members_resolved);
            assert!(
                checker
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
            let [base] = data.resolved_base_types.as_deref().unwrap() else {
                panic!("the merged interface must retain its ordinary source base");
            };
            assert_eq!(
                checker.store().type_payload(*base).unwrap().symbol(),
                checker.store().get_parent_of_symbol(symbols[2]),
            );
            assert_eq!(
                data.reference.object.structured.properties.as_deref(),
                Some(symbols.as_slice()),
            );
            let table = checker
                .store()
                .symbol_table(data.reference.object.structured.members.unwrap())
                .unwrap();
            assert_eq!(table.len(), symbols.len());
            for ((name, _, _, _), symbol) in fields.into_iter().zip(symbols) {
                assert_eq!(table.get_source(name), Some(symbol));
            }
            let snapshot = |checker: &CanonicalCheckerContext<'_>| {
                let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data()
                else {
                    panic!("the warm merged type must remain an interface");
                };
                let table = checker
                    .store()
                    .symbol_table(data.reference.object.structured.members.unwrap())
                    .unwrap();
                let mut resolved = table
                    .iter()
                    .map(|(name, symbol)| (name.as_utf8().unwrap().to_owned(), symbol))
                    .collect::<Vec<_>>();
                resolved.sort_unstable_by(|left, right| left.0.cmp(&right.0));
                (
                    checker.store().type_payload(type_).unwrap().object_flags(),
                    data.clone(),
                    resolved,
                    members(checker, owner),
                    counts(checker),
                    checker.store().symbol_store().symbol_table_len(),
                    checker.diagnostics().clone(),
                )
            };
            let warm = snapshot(&checker);
            for _ in 0..2 {
                for file in order.into_iter().rev().chain([CONSUMER_FILE]) {
                    checker.recheck_source_file(file).unwrap();
                }
                assert_eq!(query(&mut checker), type_);
                assert_eq!(
                    checker
                        .get_type_at_location(interface(&empty, EMPTY_FILE))
                        .unwrap(),
                    type_
                );
                assert_eq!(snapshot(&checker), warm);
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep cold type queries, source value publication, and replay together.
fn merged_global_interface_named_constructor_annotation_survives_source_value_reads() {
    let library = parse_source_file(concat!(
        "interface Array<T> {}\n",
        "interface ReadonlyArray<T> {}\n",
        "interface SignalPacket { original: string; readOriginal(): string; }\n",
        "interface PacketConstructor {\n",
        "  new (original: string): SignalPacket;\n",
        "  prototype: SignalPacket;\n",
        "}\n",
        "declare var SignalPacket: PacketConstructor;\n",
    ));
    let empty = parse_source_file(EMPTY);
    let added = parse_source_file(ADDED);
    let consumer = parse_source_file("const constructorValue: PacketConstructor = SignalPacket;");
    let mut checker = context(&library, &empty, &added, &consumer);
    let owner = merged_symbol(&checker, interface(&library, LIBRARY_FILE));
    let constructor_declaration = library
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == "PacketConstructor").then_some(NodeRef::new(
                library.arena.id(),
                LIBRARY_FILE,
                node,
            ))
        })
        .unwrap();
    let constructor_owner = merged_symbol(&checker, constructor_declaration);
    let (value_declaration, value_name, annotation) =
        variable(&library, LIBRARY_FILE, "SignalPacket");
    let (consumer_declaration, consumer_name, consumer_annotation) =
        variable(&consumer, CONSUMER_FILE, "constructorValue");
    let NodeData::VariableDeclaration(value) =
        &consumer.arena.get(consumer_declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let value_read = NodeRef::new(
        consumer.arena.id(),
        CONSUMER_FILE,
        value.initializer.unwrap(),
    );

    assert_value_annotation_cold(&checker, &library, owner);
    let signatures = checker.store().signature_len();
    let instance = checker.get_declared_type_of_symbol(owner).unwrap();
    for declaration in [interface(&empty, EMPTY_FILE), interface(&added, ADDED_FILE)] {
        assert_eq!(checker.get_type_at_location(declaration).unwrap(), instance);
    }
    assert!(matches!(
        checker.store().type_payload(instance).unwrap().data(),
        TypeData::Interface(_)
    ));
    assert_eq!(checker.store().signature_len(), signatures);
    assert_value_annotation_cold(&checker, &library, owner);
    for file in [EMPTY_FILE, ADDED_FILE] {
        checker.check_source_file(file).unwrap();
    }
    assert_value_annotation_cold(&checker, &library, owner);

    checker.check_source_file(CONSUMER_FILE).unwrap();
    assert!(checker.diagnostics().is_empty());
    let constructor = checker
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the cross-file source read must publish the value type");
    assert_ne!(constructor, instance);
    assert_eq!(
        checker.store().type_payload(constructor).unwrap().symbol(),
        Some(constructor_owner),
    );
    assert_eq!(
        checker
            .store()
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type),
        Some(constructor),
    );
    assert_eq!(
        checker.store().symbol(owner).unwrap().value_declaration(),
        Some(value_declaration),
    );

    let query = |checker: &mut CanonicalCheckerContext<'_>| {
        assert_eq!(
            checker.get_declared_type_of_symbol(owner).unwrap(),
            instance
        );
        assert_eq!(
            checker
                .get_declared_type_of_symbol(constructor_owner)
                .unwrap(),
            constructor,
        );
        assert_eq!(
            checker
                .get_type_at_location(interface(&empty, EMPTY_FILE))
                .unwrap(),
            instance
        );
        for node in [value_name, value_read, consumer_name] {
            assert_eq!(checker.get_type_at_location(node).unwrap(), constructor);
        }
        for node in [annotation, consumer_annotation] {
            assert_eq!(checker.get_type_from_type_node(node).unwrap(), constructor);
        }
        assert_eq!(
            checker.get_symbol_at_location(value_read).unwrap(),
            Some(owner)
        );
    };
    query(&mut checker);
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        (
            [instance, constructor].map(|type_| {
                let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data()
                else {
                    panic!("both source owners must retain their interface payloads");
                };
                data.clone()
            }),
            [owner, constructor_owner].map(|symbol| {
                let members = checker.store().symbol(symbol).unwrap().members().unwrap();
                checker
                    .store()
                    .symbol_table(members)
                    .unwrap()
                    .iter()
                    .map(|(name, symbol)| {
                        (
                            name.to_owned(),
                            checker.store().get_merged_symbol(symbol).unwrap(),
                        )
                    })
                    .collect::<Vec<_>>()
            }),
            counts(checker),
            checker.store().symbol_store().symbol_table_len(),
            checker.diagnostics().clone(),
        )
    };
    let warm = snapshot(&checker);
    for _ in 0..2 {
        for file in [ADDED_FILE, EMPTY_FILE, CONSUMER_FILE] {
            checker.recheck_source_file(file).unwrap();
        }
        query(&mut checker);
        assert_eq!(snapshot(&checker), warm);
        assert!(checker.diagnostics().is_empty());
    }
}
