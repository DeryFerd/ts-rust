use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::InterfaceTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(285_000);
const AUGMENTATION: FileId = FileId::new(285_001);
const SCRIPT: FileId = FileId::new(285_002);

// These portable sources test the owner proof. The complete Hono inputs stay in the project gate.
const LIBRARY_TEXT: &str = "interface Packet { library: number; }\n\
declare var Packet: { prototype: Packet; new(): Packet; };\n";
const AUGMENTATION_TEXT: &str = "export {};\n\
declare global {\n\
  interface Packet { node: string; }\n\
  var Packet: typeof globalThis extends { onmessage: any; Packet: infer T } ? T : never;\n\
}\n";
const SCRIPT_TEXT: &str = "interface Packet { user: boolean; }\n\
declare let packet: Packet;\n\
const n = packet.library;\n\
const s = packet.node;\n\
const b = packet.user;\n";

struct Input {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
}

fn inputs(augmentation_first: bool) -> Vec<Input> {
    let library = Input {
        file: LIBRARY,
        path: "\"/lib/packet.d.ts\"",
        parsed: parse_source_file(LIBRARY_TEXT),
    };
    let augmentation = Input {
        file: AUGMENTATION,
        path: "\"/types/packet.d.ts\"",
        parsed: parse_source_file(AUGMENTATION_TEXT),
    };
    let mut inputs = if augmentation_first {
        vec![augmentation, library]
    } else {
        vec![library, augmentation]
    };
    inputs.push(Input {
        file: SCRIPT,
        path: "\"/project/packet.ts\"",
        parsed: parse_source_file(SCRIPT_TEXT),
    });
    inputs
}

fn context(inputs: &[Input]) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in inputs {
        assert!(
            input.parsed.diagnostics.is_empty(),
            "{:?}",
            input.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.file != SCRIPT,
                    input.file == LIBRARY,
                    if input.file == AUGMENTATION {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                ),
            )
            .unwrap();
    }
    for input in inputs {
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        inputs
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(checker: &CanonicalCheckerContext<'_>, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(checker.file(file).unwrap().0.id(), file, node)
}

fn named(
    checker: &CanonicalCheckerContext<'_>,
    file: FileId,
    kind: SyntaxKind,
    name: &str,
) -> NodeRef {
    let arena = checker.file(file).unwrap().0;
    arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::PropertySignatureDeclaration(data) => data.name,
                NodeData::PropertyAccessExpression(data) => data.name,
                NodeData::ModuleDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(reference(checker, file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {name}"))
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

fn annotation(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(data) = &checker
        .file(declaration.file)
        .unwrap()
        .0
        .get(declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    reference(checker, declaration.file, data.type_.unwrap())
}

fn interface_data<'a>(
    checker: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a InterfaceTypeData {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the mixed global keeps its actual Interface identity");
    };
    data
}

fn assert_cold_annotation(checker: &CanonicalCheckerContext<'_>, root: NodeRef) {
    let arena = checker.file(root.file).unwrap().0;
    let range = arena.get(root.node).unwrap().range;
    for (node, record) in arena
        .iter()
        .filter(|(_, record)| record.range.start >= range.start && record.range.end <= range.end)
    {
        let node = reference(checker, root.file, node);
        assert!(
            checker
                .store()
                .type_node_links(node)
                .is_none_or(|links| links.resolved_type.is_none()),
            "{node:?}: {record:?}"
        );
        assert!(
            checker
                .store()
                .signature_links(node)
                .is_none_or(|links| links.resolved_signature.signature().is_none())
        );
        assert!(
            checker
                .store()
                .symbol_node_links(node)
                .is_none_or(|links| links.resolved_symbol.is_none())
        );
    }
}

#[allow(clippy::too_many_lines)]
fn assert_owner(checker: &CanonicalCheckerContext<'_>) -> SemanticSymbolId {
    let library_interface = named(checker, LIBRARY, SyntaxKind::InterfaceDeclaration, "Packet");
    let library_value = named(checker, LIBRARY, SyntaxKind::VariableDeclaration, "Packet");
    let script_interface = named(checker, SCRIPT, SyntaxKind::InterfaceDeclaration, "Packet");
    let node_interface = named(
        checker,
        AUGMENTATION,
        SyntaxKind::InterfaceDeclaration,
        "Packet",
    );
    let node_value = named(
        checker,
        AUGMENTATION,
        SyntaxKind::VariableDeclaration,
        "Packet",
    );
    let owner = symbol(checker, library_interface);
    let declarations = [
        library_interface,
        library_value,
        script_interface,
        node_interface,
        node_value,
    ];
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
    );
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    assert_eq!(record.value_declaration(), Some(library_value));
    assert!(record.parent().is_none());
    assert!(record.export_symbol().is_none());
    let table_symbol = checker
        .store()
        .symbol_table(checker.globals())
        .unwrap()
        .get_source("Packet")
        .unwrap();
    assert_eq!(checker.store().get_merged_symbol(table_symbol), Some(owner));
    for declaration in declarations {
        assert_eq!(symbol(checker, declaration), owner);
    }

    let namespace = named(
        checker,
        AUGMENTATION,
        SyntaxKind::ModuleDeclaration,
        "global",
    );
    let namespace_owner = symbol(checker, namespace);
    let namespace_record = checker.store().symbol(namespace_owner).unwrap();
    assert_eq!(namespace_record.name(), InternalSymbolName::Global.as_ref());
    let exports = namespace_record.exports().unwrap();
    let raw = raw_symbol(checker, node_interface);
    assert_eq!(raw_symbol(checker, node_value), raw);
    assert_ne!(raw, owner);
    assert_eq!(
        checker
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source("Packet"),
        Some(raw)
    );
    let raw_record = checker.store().symbol(raw).unwrap();
    assert_eq!(
        raw_record.flags(),
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
    );
    assert_eq!(
        raw_record.declarations(),
        Some([node_interface, node_value].as_slice())
    );
    assert_eq!(raw_record.value_declaration(), Some(node_value));
    assert_eq!(checker.store().get_merged_symbol(raw), Some(owner));
    assert_eq!(
        raw_record
            .parent()
            .and_then(|symbol| checker.store().get_merged_symbol(symbol)),
        Some(namespace_owner)
    );

    let bound = checker.file(AUGMENTATION).unwrap().1;
    let local = bound.local_symbol(node_interface).unwrap();
    assert_eq!(bound.local_symbol(node_value), Some(local));
    assert_ne!(local, raw);
    assert_ne!(local, owner);
    let local_record = checker.store().symbol(local).unwrap();
    assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(
        local_record.declarations(),
        Some([node_interface, node_value].as_slice())
    );
    assert_eq!(local_record.export_symbol(), Some(raw));
    assert!(local_record.value_declaration().is_none());
    assert_eq!(checker.store().get_merged_symbol(local), Some(local));

    for candidate in [owner, raw, local, raw_symbol(checker, library_value)] {
        assert!(
            checker
                .store()
                .value_symbol_links(candidate)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert!(checker.store().export_type_links(candidate).is_none());
    }
    let library_annotation = annotation(checker, library_value);
    let node_annotation = annotation(checker, node_value);
    assert_eq!(
        checker
            .file(LIBRARY)
            .unwrap()
            .0
            .get(library_annotation.node)
            .unwrap()
            .kind,
        SyntaxKind::TypeLiteral
    );
    assert_eq!(
        checker
            .file(AUGMENTATION)
            .unwrap()
            .0
            .get(node_annotation.node)
            .unwrap()
            .kind,
        SyntaxKind::ConditionalType
    );
    assert_cold_annotation(checker, library_annotation);
    assert_cold_annotation(checker, node_annotation);
    for file in [LIBRARY, AUGMENTATION] {
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
    owner
}

fn assert_members(checker: &mut CanonicalCheckerContext<'_>, expected: TypeId) {
    let owner = assert_owner(checker);
    assert_eq!(
        checker.get_declared_type_of_symbol(owner).unwrap(),
        expected
    );
    assert_eq!(
        checker.store().type_payload(expected).unwrap().symbol(),
        Some(owner)
    );
    let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
    let entries = [
        (LIBRARY, "library", "n", intrinsics.number_type),
        (SCRIPT, "user", "b", intrinsics.boolean_type),
        (AUGMENTATION, "node", "s", intrinsics.string_type),
    ];
    let mut properties = Vec::new();
    for (file, name, variable, expected_type) in entries {
        let declaration = named(checker, file, SyntaxKind::PropertySignature, name);
        let property = symbol(checker, declaration);
        let parent = named(checker, file, SyntaxKind::InterfaceDeclaration, "Packet");
        let record = checker.store().symbol(property).unwrap();
        assert_eq!(record.flags(), SymbolFlags::PROPERTY);
        assert_eq!(record.declarations(), Some([declaration].as_slice()));
        assert_eq!(record.parent(), Some(raw_symbol(checker, parent)));
        assert_eq!(checker.store().get_parent_of_symbol(property), Some(owner));
        let access = named(checker, SCRIPT, SyntaxKind::PropertyAccessExpression, name);
        assert_eq!(
            checker.get_symbol_at_location(access).unwrap(),
            Some(property)
        );
        assert_eq!(checker.get_type_at_location(access).unwrap(), expected_type);
        let variable = named(checker, SCRIPT, SyntaxKind::VariableDeclaration, variable);
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol(checker, variable))
                .unwrap()
                .resolved_type,
            Some(expected_type)
        );
        properties.push(property);
    }
    let interface = interface_data(checker, expected);
    assert!(interface.declared_members_resolved);
    assert!(interface.base_types_resolved);
    assert!(interface.this_type.is_none());
    assert!(interface.all_type_parameters.is_none());
    assert!(interface.reference.object.target.is_none());
    assert!(interface.reference.object.mapper.is_none());
    let structured = &interface.reference.object.structured;
    assert_eq!(
        structured.properties.as_deref(),
        Some(properties.as_slice())
    );
    assert_eq!(structured.call_signature_count, 0);
    assert!(structured.signatures.as_ref().is_none_or(Vec::is_empty));
    let members = checker
        .store()
        .symbol_table(structured.members.unwrap())
        .unwrap();
    assert_eq!(members.len(), properties.len());
    for property in properties {
        assert_eq!(
            members.get(checker.store().symbol(property).unwrap().name()),
            Some(property)
        );
    }
    for file in [LIBRARY, SCRIPT, AUGMENTATION] {
        let declaration = named(checker, file, SyntaxKind::InterfaceDeclaration, "Packet");
        assert_eq!(
            checker.get_symbol_at_location(declaration).unwrap(),
            Some(owner)
        );
        assert_eq!(checker.get_type_at_location(declaration).unwrap(), expected);
    }
    assert_eq!(assert_owner(checker), owner);
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.merged_symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.type_alias_len(),
            store.type_resolution_len(),
            store.symbol_store().symbol_table_len(),
            store.conditional_root_len(),
        ],
        interface_data(checker, type_).clone(),
        store.relation_state_snapshot(),
        checker.diagnostics().clone(),
        checker
            .file_order()
            .iter()
            .map(|&file| {
                (
                    file,
                    store
                        .source_file_links(checker.source_file(file).unwrap())
                        .cloned(),
                )
            })
            .collect::<Vec<_>>(),
        checker
            .file_order()
            .iter()
            .flat_map(|&file| {
                checker.file(file).unwrap().0.iter().map(move |(node, _)| {
                    let node = reference(checker, file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, record)| {
                (
                    symbol,
                    record.clone(),
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

#[test]
fn mixed_global_interface_owners_keep_script_order_and_both_value_annotations_cold() {
    for augmentation_first in [false, true] {
        for query_first in [false, true] {
            let inputs = inputs(augmentation_first);
            let mut checker = context(&inputs);
            assert_eq!(
                checker.file_order(),
                inputs.iter().map(|input| input.file).collect::<Vec<_>>()
            );
            let owner = assert_owner(&checker);
            assert!(checker.store().declared_type_links(owner).is_none());
            let early = query_first.then(|| {
                let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
                assert!(!interface_data(&checker, type_).declared_members_resolved);
                assert_eq!(assert_owner(&checker), owner);
                type_
            });
            checker.check_source_file(SCRIPT).unwrap();
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(SCRIPT).unwrap())
                    .unwrap()
                    .type_checked
            );
            let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
            if let Some(early) = early {
                assert_eq!(early, type_);
            }
            assert_members(&mut checker, type_);
            let warm = snapshot(&checker, type_);
            for _ in 0..2 {
                checker.recheck_source_file(SCRIPT).unwrap();
                assert_members(&mut checker, type_);
                assert_eq!(
                    snapshot(&checker, type_),
                    warm,
                    "augmentation_first={augmentation_first}, query_first={query_first}"
                );
            }
        }
    }
}
