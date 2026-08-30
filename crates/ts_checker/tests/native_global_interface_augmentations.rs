use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, type_records::InterfaceTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(202_820);
const AUGMENTATION: FileId = FileId::new(202_821);
const SCRIPT: FileId = FileId::new(202_822);

fn context<'a>(
    library: &'a ParseResult,
    augmentation: &'a ParseResult,
    script: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (
            LIBRARY,
            library,
            "\"/lib/lib.native.d.ts\"",
            true,
            true,
            CanonicalModuleState::Script,
        ),
        (
            AUGMENTATION,
            augmentation,
            "\"/project/early-augmentation.d.ts\"",
            true,
            false,
            CanonicalModuleState::External,
        ),
        (
            SCRIPT,
            script,
            "\"/project/later-script.ts\"",
            false,
            false,
            CanonicalModuleState::Script,
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, declaration, default_library, module) in files {
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
                    module,
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

fn raw_symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    checker
        .store()
        .get_merged_symbol(raw_symbol(checker, node))
        .unwrap()
}

fn member(parsed: &ParseResult, owner: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("member lookup needs an interface declaration")
    };
    interface
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let name = match &parsed.arena.get(*node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::PropertySignatureDeclaration(property) => property.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
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
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn interface_data<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a InterfaceTypeData {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("native type demand must retain the interface")
    };
    data
}

fn access(parsed: &ParseResult, expected: &str) -> NodeRef {
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
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), SCRIPT, node))
        })
        .unwrap_or_else(|| panic!("missing property access {expected}"))
}

fn call(parsed: &ParseResult, callee: NodeRef) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            (call.expression == callee.node && call.arguments.nodes.is_empty())
                .then_some(NodeRef::new(parsed.arena.id(), SCRIPT, node))
        })
        .unwrap()
}

fn method_signature(
    checker: &mut CanonicalCheckerContext<'_>,
    declaration: NodeRef,
    name: NodeRef,
    expected_return: TypeId,
) -> (TypeId, SignatureId) {
    let owner = symbol(checker, declaration);
    assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
    let type_ = checker.get_type_at_location(name).unwrap();
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("method must have a callable object")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("method must retain one signature")
    };
    let signature = *signature;
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert!(record.parameters().is_empty());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 0);
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert_eq!(
        checker.get_return_type_of_signature(signature),
        Ok(expected_return)
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    (type_, signature)
}

#[test]
#[allow(clippy::too_many_lines)] // Keep both merge phases, their source owners, and both query orders together.
fn native_interface_augmentation_follows_script_merge_and_replays_exact_owners() {
    let library = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {} ",
        "interface First { first: string; } interface Second { second: number; } ",
        "interface Third { third: boolean; } ",
        "interface NativePacket extends First, Second, Third { method(): number; } ",
        "declare var NativePacket: { prototype: NativePacket; new(): NativePacket; };",
    ));
    let augmentation = parse_source_file(
        "export {}; declare global { interface NativePacket { added(): string; } }",
    );
    let script = parse_source_file(concat!(
        "interface NativePacket { late: boolean; } declare const packet: NativePacket; ",
        "const first: string = packet.first; const own: number = packet.method(); ",
        "const added: string = packet.added();",
    ));
    let declarations = [
        interface(&library, LIBRARY, "NativePacket"),
        interface(&script, SCRIPT, "NativePacket"),
        interface(&augmentation, AUGMENTATION, "NativePacket"),
    ];
    let base_declarations =
        ["First", "Second", "Third"].map(|name| interface(&library, LIBRARY, name));
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
    let namespace = augmentation
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ModuleDeclaration(module) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &augmentation.arena.get(module.name)?.data else {
                return None;
            };
            (name.text == "global").then_some(NodeRef::new(
                augmentation.arena.id(),
                AUGMENTATION,
                node,
            ))
        })
        .unwrap();
    let method = member(&library, declarations[0], "method");
    let added = member(&augmentation, declarations[2], "added");
    let late = member(&script, declarations[1], "late");
    let first_access = access(&script, "first");
    let method_access = access(&script, "method");
    let added_access = access(&script, "added");
    let method_call = call(&script, method_access);
    let added_call = call(&script, added_access);
    let nodes = [
        (LIBRARY, &library),
        (AUGMENTATION, &augmentation),
        (SCRIPT, &script),
    ]
    .into_iter()
    .flat_map(|(file, parsed)| {
        parsed
            .arena
            .iter()
            .map(move |(node, _)| NodeRef::new(parsed.arena.id(), file, node))
    })
    .collect::<Vec<_>>();

    for query_first in [false, true] {
        let mut checker = context(&library, &augmentation, &script);
        assert_eq!(checker.file_order(), [LIBRARY, AUGMENTATION, SCRIPT]);
        let owner = symbol(&checker, declarations[0]);
        let raw_namespace = raw_symbol(&checker, namespace);
        let raw_augmentation = raw_symbol(&checker, declarations[2]);
        let exports = checker
            .store()
            .symbol(raw_namespace)
            .unwrap()
            .exports()
            .unwrap();
        let base_owners = base_declarations.map(|node| symbol(&checker, node));
        let assert_owners = |checker: &CanonicalCheckerContext<'_>| {
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
            for declaration in declarations {
                assert_eq!(symbol(checker, declaration), owner);
            }
            assert_eq!(symbol(checker, value_declaration), owner);
            assert_ne!(raw_augmentation, owner);
            assert_eq!(
                checker.store().symbol(raw_namespace).unwrap().exports(),
                Some(exports)
            );
            assert_eq!(
                checker
                    .store()
                    .symbol_table(exports)
                    .unwrap()
                    .get_source("NativePacket"),
                Some(raw_augmentation)
            );
            assert_eq!(
                checker.store().get_merged_symbol(raw_augmentation),
                Some(owner)
            );
            assert_eq!(
                checker.store().symbol(raw_augmentation).unwrap().parent(),
                Some(raw_namespace)
            );
            for (declaration, interface) in [
                (method.0, declarations[0]),
                (added.0, declarations[2]),
                (late.0, declarations[1]),
            ] {
                let member = symbol(checker, declaration);
                let record = checker.store().symbol(member).unwrap();
                assert_eq!(record.declarations(), Some([declaration].as_slice()));
                assert_eq!(record.parent(), Some(raw_symbol(checker, interface)));
                assert_eq!(checker.store().get_parent_of_symbol(member), Some(owner));
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
        assert_owners(&checker);
        assert!(checker.store().declared_type_links(owner).is_none());
        let early = query_first.then(|| {
            let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
            assert_eq!(
                checker.store().type_payload(type_).unwrap().symbol(),
                Some(owner)
            );
            assert!(!interface_data(&checker, type_).declared_members_resolved);
            assert_owners(&checker);
            type_
        });
        for file in [AUGMENTATION, SCRIPT] {
            checker.check_source_file(file).unwrap();
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(file).unwrap())
                    .unwrap()
                    .type_checked
            );
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
            assert_owners(checker);
            let data = interface_data(checker, type_);
            assert!(data.base_types_resolved);
            assert!(data.declared_members_resolved);
            assert_eq!(data.resolved_base_types.as_deref(), Some(bases.as_slice()));
            for declaration in declarations {
                assert_eq!(checker.get_type_at_location(declaration), Ok(type_));
                assert_eq!(checker.get_symbol_at_location(declaration), Ok(Some(owner)));
            }
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let (string, number, boolean) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            );
            let methods = [
                method_signature(checker, method.0, method.1, number),
                method_signature(checker, added.0, added.1, string),
            ];
            assert_ne!(methods[0], methods[1]);
            for ((access, call, declaration), ((callable, _), expected)) in [
                (method_access, method_call, method.0),
                (added_access, added_call, added.0),
            ]
            .into_iter()
            .zip(methods.into_iter().zip([number, string]))
            {
                assert_eq!(
                    checker.get_symbol_at_location(access),
                    Ok(Some(symbol(checker, declaration)))
                );
                assert_eq!(checker.get_type_at_location(access), Ok(callable));
                assert_eq!(checker.get_type_at_location(call), Ok(expected));
            }
            assert_eq!(checker.get_type_at_location(late.1), Ok(boolean));
            let mut properties = vec![
                symbol(checker, method.0),
                symbol(checker, late.0),
                symbol(checker, added.0),
            ];
            for (index, (name, expected)) in
                [("first", string), ("second", number), ("third", boolean)]
                    .into_iter()
                    .enumerate()
            {
                let (declaration, name_node) = member(&library, base_declarations[index], name);
                let property = symbol(checker, declaration);
                assert_eq!(
                    checker.store().get_parent_of_symbol(property),
                    Some(base_owners[index])
                );
                assert_eq!(
                    checker.get_symbol_at_location(name_node),
                    Ok(Some(property))
                );
                assert_eq!(checker.get_type_at_location(name_node), Ok(expected));
                if index == 0 {
                    assert_eq!(
                        checker.get_symbol_at_location(first_access),
                        Ok(Some(property))
                    );
                    assert_eq!(checker.get_type_at_location(first_access), Ok(expected));
                }
                properties.push(property);
            }
            let data = interface_data(checker, type_);
            let structured = &data.reference.object.structured;
            assert_eq!(
                structured.properties.as_deref(),
                Some(properties.as_slice())
            );
            let table = checker
                .store()
                .symbol_table(structured.members.unwrap())
                .unwrap();
            assert_eq!(table.len(), properties.len());
            for property in &properties {
                assert_eq!(
                    table.get(checker.store().symbol(*property).unwrap().name()),
                    Some(*property)
                );
            }
            assert_owners(checker);
            (methods, properties)
        };
        let (methods, properties) = query(&mut checker);
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.symbol_len(),
                    store.merged_symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                std::iter::once(type_)
                    .chain(bases)
                    .map(|type_| interface_data(checker, type_).clone())
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
                properties
                    .iter()
                    .copied()
                    .chain([owner])
                    .map(|symbol| store.value_symbol_links(symbol).cloned())
                    .collect::<Vec<_>>(),
                methods.map(|(type_, signature)| {
                    (
                        format!("{:?}", store.type_payload(type_).unwrap()),
                        format!("{:?}", store.signature(signature).unwrap()),
                    )
                }),
                checker.diagnostics().clone(),
            )
        };
        let warm = snapshot(&checker);
        for _ in 0..2 {
            for file in [AUGMENTATION, SCRIPT] {
                checker.recheck_source_file(file).unwrap();
            }
            assert_eq!(query(&mut checker), (methods, properties.clone()));
            assert_eq!(snapshot(&checker), warm, "query_first={query_first}");
        }
    }
}
