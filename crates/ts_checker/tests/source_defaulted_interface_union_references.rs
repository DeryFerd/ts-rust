use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::{InterfaceTypeData, TypeCacheState, TypeParameterData},
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LOCAL: FileId = FileId::new(260_700);
const LIBRARY: FileId = FileId::new(260_701);
const AUGMENTATION: FileId = FileId::new(260_702);
const CONSUMER: FileId = FileId::new(260_703);

fn facts(
    path: &str,
    declaration: bool,
    default_library: bool,
    module: CanonicalModuleState,
) -> CanonicalSourceFileFacts {
    CanonicalSourceFileFacts::new_with_default_library(
        EscapedName::source(path),
        CanonicalSourceLanguage::TypeScript,
        declaration,
        default_library,
        module,
    )
}

fn context<'a>(
    files: &[(FileId, &'a ParseResult, CanonicalSourceFileFacts)],
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, facts) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, *file, facts.clone())
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, *file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
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

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::InterfaceDeclaration(declaration) => declaration.name,
                NodeData::TypeAliasDeclaration(declaration) => declaration.name,
                NodeData::VariableDeclaration(declaration) => declaration.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn alias(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    name: &str,
) -> (SemanticSymbolId, NodeRef) {
    let node = declaration(parsed, file, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!("the declaration helper selected a type alias")
    };
    (
        symbol(checker, node),
        NodeRef::new(node.arena, node.file, alias.type_),
    )
}

fn annotation(parsed: &ParseResult, variable: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(variable_data) =
        &parsed.arena.get(variable.node).unwrap().data
    else {
        panic!("expected an annotated variable")
    };
    NodeRef::new(variable.arena, variable.file, variable_data.type_.unwrap())
}

fn parameters(parsed: &ParseResult, owner: NodeRef) -> Vec<NodeRef> {
    let parameters = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::InterfaceDeclaration(interface) => interface.type_parameters.as_ref(),
        NodeData::ConstructSignatureDeclaration(signature) => signature.type_parameters.as_ref(),
        _ => panic!("expected an interface or construct signature"),
    };
    parameters
        .unwrap()
        .nodes
        .iter()
        .map(|node| NodeRef::new(owner.arena, owner.file, *node))
        .collect()
}

fn default_node(parsed: &ParseResult, parameter: NodeRef) -> Option<NodeRef> {
    let NodeData::TypeParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a type parameter")
    };
    parameter_data
        .default_type
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
}

fn constructor(parsed: &ParseResult, type_literal: NodeRef) -> NodeRef {
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(type_literal.node).unwrap().data
    else {
        panic!("expected a constructor value annotation")
    };
    let [member] = literal.members.nodes.as_slice() else {
        panic!("expected one construct signature")
    };
    let member = NodeRef::new(type_literal.arena, type_literal.file, *member);
    assert_eq!(
        parsed.arena.get(member.node).unwrap().kind,
        SyntaxKind::ConstructSignature
    );
    member
}

fn interface_data<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    target: TypeId,
) -> &'a InterfaceTypeData {
    let TypeData::Interface(interface) = checker.store().type_payload(target).unwrap().data()
    else {
        panic!("the generic target must retain its interface record")
    };
    interface
}

fn parameter_data<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    parameter: TypeId,
) -> &'a TypeParameterData {
    let TypeData::TypeParameter(parameter) =
        checker.store().type_payload(parameter).unwrap().data()
    else {
        panic!("the written formal must retain its type-parameter record")
    };
    parameter
}

fn demand_alias(
    checker: &mut CanonicalCheckerContext<'_>,
    (symbol, rhs): (SemanticSymbolId, NodeRef),
) -> TypeId {
    let result = checker.get_declared_type_of_symbol(symbol).unwrap();
    assert_eq!(checker.get_type_from_type_node(rhs), Ok(result));
    assert_eq!(
        checker
            .store()
            .type_alias_links(symbol)
            .unwrap()
            .declared_type,
        Some(result)
    );
    assert_eq!(
        checker.store().type_node_links(rhs).unwrap().resolved_type,
        Some(result)
    );
    result
}

fn union_reference(
    checker: &CanonicalCheckerContext<'_>,
    union: TypeId,
    target: TypeId,
    arguments: &[TypeId],
) -> TypeId {
    let TypeData::Union(union) = checker.store().type_payload(union).unwrap().data() else {
        panic!("the complete nullable reference must remain a union")
    };
    let null = checker.store().intrinsic_bootstrap().unwrap().null_type;
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&null));
    let reference = *union
        .union
        .types
        .iter()
        .find(|type_| **type_ != null)
        .unwrap();
    let record = checker.store().type_payload(reference).unwrap();
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE)
    );
    assert!(record.alias().is_none());
    let TypeData::TypeReference(data) = record.data() else {
        panic!("the union member must be the actual generic reference, not its default")
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(data.object.mapper, None);
    assert_eq!(data.node, None);
    assert_eq!(data.resolved_type_arguments.as_deref(), Some(arguments));
    assert_eq!(data.object.instantiations, TypeCacheState::Unallocated);
    let TypeCacheState::Allocated(instantiations) = &interface_data(checker, target)
        .reference
        .object
        .instantiations
    else {
        panic!("the interface target must own its canonical reference cache")
    };
    assert_eq!(
        instantiations
            .values()
            .filter(|cached| **cached == reference)
            .count(),
        1
    );
    reference
}

#[test]
#[allow(clippy::too_many_lines)] // Both query orders share the same source and identity checks.
fn dependent_defaults_in_complete_unions_keep_written_formals_and_actual_arguments() {
    let parsed = parse_source_file(concat!(
        "interface Pair<T = string, U = T> { first: T; second: U; }\n",
        "type Explicit = Pair<number, number> | null;\n",
        "type Bare = Pair | null;\n",
        "type Prefix = Pair<number> | null;\n",
        "type FullDefault = Pair<string, string> | null;\n",
        "type Again = Bare;\n",
        "declare const bare: Bare;\n",
        "declare const prefix: Pair<number> | null;\n",
    ));
    let owner_node = declaration(&parsed, LOCAL, SyntaxKind::InterfaceDeclaration, "Pair");
    let parameter_nodes = parameters(&parsed, owner_node);
    let defaults = parameter_nodes
        .iter()
        .map(|parameter| default_node(&parsed, *parameter).unwrap())
        .collect::<Vec<_>>();
    let bare_annotation = annotation(
        &parsed,
        declaration(&parsed, LOCAL, SyntaxKind::VariableDeclaration, "bare"),
    );
    let prefix_annotation = annotation(
        &parsed,
        declaration(&parsed, LOCAL, SyntaxKind::VariableDeclaration, "prefix"),
    );
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), LOCAL, node))
        .collect::<Vec<_>>();

    for source_first in [false, true] {
        let mut checker = context(&[(
            LOCAL,
            &parsed,
            facts(
                "\"/project/defaulted-unions.ts\"",
                false,
                false,
                CanonicalModuleState::Script,
            ),
        )]);
        let owner = symbol(&checker, owner_node);
        let aliases = ["Explicit", "Bare", "Prefix", "FullDefault", "Again"]
            .map(|name| alias(&checker, &parsed, LOCAL, name));
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        for default in &defaults {
            assert!(checker.store().type_node_links(*default).is_none());
        }
        if source_first {
            checker.check_source_file(LOCAL).unwrap();
        }

        let explicit = demand_alias(&mut checker, aliases[0]);
        let target = checker
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        let formals = interface_data(&checker, target)
            .reference
            .resolved_type_arguments
            .clone()
            .unwrap();
        assert_eq!(formals.len(), 2);
        let this = interface_data(&checker, target).this_type.unwrap();
        assert_eq!(
            interface_data(&checker, target)
                .all_type_parameters
                .as_deref(),
            Some([formals[0], formals[1], this].as_slice())
        );
        assert!(parameter_data(&checker, this).is_this_type);
        assert_eq!(parameter_data(&checker, this).constraint, Some(target));
        for (parameter, formal) in parameter_nodes.iter().zip(&formals) {
            assert_eq!(
                checker.store().type_payload(*formal).unwrap().symbol(),
                Some(symbol(&checker, *parameter))
            );
            assert_eq!(parameter_data(&checker, *formal).target, None);
            assert_eq!(parameter_data(&checker, *formal).mapper, None);
            if !source_first {
                assert_eq!(
                    parameter_data(&checker, *formal).resolved_default_type,
                    None
                );
            }
        }
        if !source_first {
            for default in &defaults {
                assert!(checker.store().type_node_links(*default).is_none());
            }
        }
        let explicit_reference = union_reference(&checker, explicit, target, &[number, number]);

        // Query the actual RHS first, then the enclosing alias and source annotation.
        let bare = checker.get_type_from_type_node(aliases[1].1).unwrap();
        assert_eq!(demand_alias(&mut checker, aliases[1]), bare);
        let prefix = demand_alias(&mut checker, aliases[2]);
        let full_default = demand_alias(&mut checker, aliases[3]);
        assert_eq!(demand_alias(&mut checker, aliases[4]), bare);
        let bare_reference = union_reference(&checker, bare, target, &[string, string]);
        assert_eq!(
            union_reference(&checker, prefix, target, &[number, number]),
            explicit_reference
        );
        assert_eq!(
            union_reference(&checker, full_default, target, &[string, string]),
            bare_reference
        );
        assert_ne!(bare_reference, explicit_reference);
        assert_eq!(
            parameter_data(&checker, formals[0]).resolved_default_type,
            Some(string)
        );
        assert_eq!(
            parameter_data(&checker, formals[1]).resolved_default_type,
            Some(formals[0])
        );
        assert!(
            checker
                .store()
                .type_node_links(defaults[0])
                .and_then(|links| links.resolved_type)
                .is_none_or(|type_| type_ == string)
        );
        assert_eq!(
            checker
                .store()
                .type_node_links(defaults[1])
                .unwrap()
                .resolved_type,
            Some(formals[0])
        );
        assert_eq!(
            checker
                .store()
                .symbol_node_links(defaults[1])
                .unwrap()
                .resolved_symbol,
            Some(symbol(&checker, parameter_nodes[0]))
        );
        checker.check_source_file(LOCAL).unwrap();
        assert_eq!(checker.get_type_from_type_node(bare_annotation), Ok(bare));
        let annotated_prefix = checker.get_type_from_type_node(prefix_annotation).unwrap();
        assert_eq!(
            union_reference(&checker, annotated_prefix, target, &[number, number]),
            explicit_reference
        );
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );

        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.symbol_len(),
                    store.merged_symbol_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                interface_data(checker, target).clone(),
                formals
                    .iter()
                    .map(|formal| parameter_data(checker, *formal).clone())
                    .collect::<Vec<_>>(),
                nodes
                    .iter()
                    .map(|node| {
                        (
                            store.type_node_links(*node).cloned(),
                            store.symbol_node_links(*node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                aliases.map(|(symbol, _)| store.type_alias_links(symbol).cloned()),
                checker.diagnostics().clone(),
            )
        };
        let warm = snapshot(&checker);
        for _ in 0..2 {
            for (query, expected) in
                aliases
                    .into_iter()
                    .zip([explicit, bare, prefix, full_default, bare])
            {
                assert_eq!(demand_alias(&mut checker, query), expected);
            }
            assert_eq!(checker.get_type_from_type_node(bare_annotation), Ok(bare));
            assert_eq!(
                checker.get_type_from_type_node(prefix_annotation),
                Ok(annotated_prefix)
            );
            checker.recheck_source_file(LOCAL).unwrap();
            assert_eq!(snapshot(&checker), warm, "source_first={source_first}");
        }
    }
}

#[allow(clippy::too_many_lines)] // Keep the complete merged owner and its cold value side in one control.
fn check_mixed_owner_default(
    library_source: &str,
    augmentation_source: &str,
    expected_default: SyntaxKind,
) {
    let library = parse_source_file(library_source);
    let augmentation = parse_source_file(augmentation_source);
    let consumer = parse_source_file(concat!(
        "type Explicit = Stream<number> | null;\n",
        "type Bare = Stream | null;\n",
        "type Again = Bare;\n",
        "declare const stream: Stream | null;\n",
    ));
    let files = [
        (
            LIBRARY,
            &library,
            facts(
                "\"/lib/lib.stream.d.ts\"",
                true,
                true,
                CanonicalModuleState::Script,
            ),
        ),
        (
            AUGMENTATION,
            &augmentation,
            facts(
                "\"/project/stream-augmentation.d.ts\"",
                true,
                false,
                CanonicalModuleState::External,
            ),
        ),
        (
            CONSUMER,
            &consumer,
            facts(
                "\"/project/stream-consumer.ts\"",
                false,
                false,
                CanonicalModuleState::Script,
            ),
        ),
    ];
    let mut checker = context(&files);
    assert_eq!(checker.file_order(), &[LIBRARY, AUGMENTATION, CONSUMER]);
    let interfaces = [
        declaration(
            &library,
            LIBRARY,
            SyntaxKind::InterfaceDeclaration,
            "Stream",
        ),
        declaration(
            &augmentation,
            AUGMENTATION,
            SyntaxKind::InterfaceDeclaration,
            "Stream",
        ),
    ];
    let variables = [
        declaration(&library, LIBRARY, SyntaxKind::VariableDeclaration, "Stream"),
        declaration(
            &augmentation,
            AUGMENTATION,
            SyntaxKind::VariableDeclaration,
            "Stream",
        ),
    ];
    let value_annotations = [
        annotation(&library, variables[0]),
        annotation(&augmentation, variables[1]),
    ];
    let constructors = [
        constructor(&library, value_annotations[0]),
        constructor(&augmentation, value_annotations[1]),
    ];
    let constructor_parameters = [
        parameters(&library, constructors[0])[0],
        parameters(&augmentation, constructors[1])[0],
    ];
    let formal_nodes = [
        parameters(&library, interfaces[0])[0],
        parameters(&augmentation, interfaces[1])[0],
    ];
    let formal_defaults = [
        default_node(&library, formal_nodes[0]),
        default_node(&augmentation, formal_nodes[1]),
    ];
    let selected_default = formal_defaults.into_iter().flatten().next().unwrap();
    let selected_arena = if selected_default.file == LIBRARY {
        &library.arena
    } else {
        &augmentation.arena
    };
    assert_eq!(
        selected_arena.get(selected_default.node).unwrap().kind,
        expected_default
    );
    let owner = symbol(&checker, interfaces[0]);
    let formal_symbol = symbol(&checker, formal_nodes[0]);
    let owner_declarations = [interfaces[0], variables[0], interfaces[1], variables[1]];
    let assert_owners = |checker: &CanonicalCheckerContext<'_>| {
        let record = checker.store().symbol(owner).unwrap();
        assert!(record.flags().contains(
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
        ));
        assert_eq!(record.declarations(), Some(owner_declarations.as_slice()));
        assert_eq!(record.value_declaration(), Some(variables[0]));
        for declaration in owner_declarations {
            assert_eq!(symbol(checker, declaration), owner);
        }
        assert_eq!(symbol(checker, formal_nodes[1]), formal_symbol);
        assert_eq!(
            checker
                .store()
                .symbol(formal_symbol)
                .unwrap()
                .declarations(),
            Some(formal_nodes.as_slice())
        );
        assert_eq!(
            checker.store().get_parent_of_symbol(formal_symbol),
            Some(owner)
        );
        for parameter in constructor_parameters {
            let constructor_formal = symbol(checker, parameter);
            assert_ne!(constructor_formal, formal_symbol);
            assert!(
                checker
                    .store()
                    .declared_type_links(constructor_formal)
                    .is_none_or(|links| links.declared_type.is_none())
            );
        }
    };
    let assert_cold_values = |checker: &CanonicalCheckerContext<'_>| {
        assert!(
            checker
                .store()
                .value_symbol_links(owner)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        for node in value_annotations {
            assert!(
                checker
                    .store()
                    .type_node_links(node)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
        }
        for signature in constructors {
            assert!(
                checker
                    .store()
                    .signature_links(signature)
                    .is_none_or(|links| links.resolved_signature.signature().is_none())
            );
        }
        for file in [LIBRARY, AUGMENTATION] {
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
    };
    assert_owners(&checker);
    assert_cold_values(&checker);
    for default in formal_defaults.into_iter().flatten() {
        assert!(checker.store().type_node_links(default).is_none());
    }
    let aliases =
        ["Explicit", "Bare", "Again"].map(|name| alias(&checker, &consumer, CONSUMER, name));
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let expected_argument = match expected_default {
        SyntaxKind::StringKeyword => bootstrap.string_type,
        SyntaxKind::AnyKeyword => bootstrap.any_type,
        _ => panic!("this source control has a written string or any default"),
    };
    let explicit = demand_alias(&mut checker, aliases[0]);
    let target = checker
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let interface = interface_data(&checker, target);
    assert_eq!(interface.outer_type_parameter_count, 0);
    let [formal] = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .unwrap()
    else {
        panic!("both interface declarations must share one canonical formal")
    };
    let formal = *formal;
    assert_eq!(
        checker.store().type_payload(target).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        checker.store().type_payload(formal).unwrap().symbol(),
        Some(formal_symbol)
    );
    assert_eq!(interface.reference.object.target, Some(target));
    assert_eq!(
        interface.reference.resolved_type_arguments.as_deref(),
        Some([formal].as_slice())
    );
    let this = interface.this_type.unwrap();
    assert_eq!(
        interface.all_type_parameters.as_deref(),
        Some([formal, this].as_slice())
    );
    assert!(parameter_data(&checker, this).is_this_type);
    assert_eq!(parameter_data(&checker, this).constraint, Some(target));
    assert_eq!(parameter_data(&checker, formal).resolved_default_type, None);
    let explicit_reference = union_reference(&checker, explicit, target, &[number]);
    for default in formal_defaults.into_iter().flatten() {
        assert!(checker.store().type_node_links(default).is_none());
    }
    assert_owners(&checker);
    assert_cold_values(&checker);

    let bare = checker.get_type_from_type_node(aliases[1].1).unwrap();
    assert_eq!(demand_alias(&mut checker, aliases[1]), bare);
    assert_eq!(demand_alias(&mut checker, aliases[2]), bare);
    let bare_reference = union_reference(&checker, bare, target, &[expected_argument]);
    assert_ne!(bare_reference, explicit_reference);
    assert_eq!(parameter_data(&checker, formal).target, None);
    assert_eq!(parameter_data(&checker, formal).mapper, None);
    assert_eq!(
        parameter_data(&checker, formal).resolved_default_type,
        Some(expected_argument)
    );
    assert!(
        checker
            .store()
            .type_node_links(selected_default)
            .and_then(|links| links.resolved_type)
            .is_none_or(|type_| type_ == expected_argument)
    );
    checker.check_source_file(CONSUMER).unwrap();
    let source_annotation = annotation(
        &consumer,
        declaration(
            &consumer,
            CONSUMER,
            SyntaxKind::VariableDeclaration,
            "stream",
        ),
    );
    let annotated = checker.get_type_from_type_node(source_annotation).unwrap();
    assert_eq!(
        union_reference(&checker, annotated, target, &[expected_argument]),
        bare_reference
    );
    assert_owners(&checker);
    assert_cold_values(&checker);
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );

    let nodes = files
        .iter()
        .flat_map(|(file, parsed, _)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), *file, node))
        })
        .collect::<Vec<_>>();
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
        let store = checker.store();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.merged_symbol_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            interface_data(checker, target).clone(),
            parameter_data(checker, formal).clone(),
            [owner, formal_symbol].map(|symbol| {
                (
                    store.symbol(symbol).unwrap().clone(),
                    store.value_symbol_links(symbol).cloned(),
                )
            }),
            nodes
                .iter()
                .map(|node| {
                    (
                        store.type_node_links(*node).cloned(),
                        store.symbol_node_links(*node).cloned(),
                        store.signature_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            aliases.map(|(symbol, _)| store.type_alias_links(symbol).cloned()),
            checker.diagnostics().clone(),
        )
    };
    let warm = snapshot(&checker);
    for _ in 0..2 {
        for (query, expected) in aliases.into_iter().zip([explicit, bare, bare]) {
            assert_eq!(demand_alias(&mut checker, query), expected);
        }
        assert_eq!(
            checker.get_type_from_type_node(source_annotation),
            Ok(annotated)
        );
        checker.recheck_source_file(CONSUMER).unwrap();
        assert_owners(&checker);
        assert_cold_values(&checker);
        assert_eq!(snapshot(&checker), warm);
    }
}

#[test]
fn merged_interface_union_uses_the_default_first_written_in_a_later_declaration() {
    check_mixed_owner_default(
        concat!(
            "interface Stream<R> { value: R; }\n",
            "declare var Stream: { new<R = number>(): Stream<R>; };\n",
        ),
        concat!(
            "export {}; declare global {\n",
            "interface Stream<R = string> { extra: R; }\n",
            "var Stream: { new<R = number>(): Stream<R>; };\n",
            "}\n",
        ),
        SyntaxKind::StringKeyword,
    );
}

#[test]
fn written_any_default_stays_an_argument_of_the_real_mixed_interface_reference() {
    check_mixed_owner_default(
        concat!(
            "interface Stream<R = any> { value: R; }\n",
            "declare var Stream: { new<R = number>(): Stream<R>; };\n",
        ),
        concat!(
            "export {}; declare global {\n",
            "interface Stream<R = any> { extra: R; }\n",
            "var Stream: { new<R = number>(): Stream<R>; };\n",
            "}\n",
        ),
        SyntaxKind::AnyKeyword,
    );
}
