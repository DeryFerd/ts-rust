use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(293_100);
const AUGMENTATION: FileId = FileId::new(293_101);
const CONSUMER: FileId = FileId::new(293_102);

const LIBRARY_TEXT: &str = "interface Packet { library: number; }\n\
declare var Packet: { prototype: Packet; };\n";
const AUGMENTATION_TEXT: &str = "export {};\n\
declare global {\n\
  interface Packet { augmented: string; }\n\
  var Packet: { prototype: Packet; };\n\
}\n";
const CONSUMER_TEXT: &str = "declare let packet: Packet;\n\
const library = packet.library;\n\
const augmented = packet.augmented;\n\
const prototype = Packet.prototype;\n";

struct Input {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
}

fn inputs(consumer: &str) -> [Input; 3] {
    [
        Input {
            file: LIBRARY,
            path: "/lib/packet.d.ts",
            parsed: parse_source_file(LIBRARY_TEXT),
        },
        Input {
            file: AUGMENTATION,
            path: "/types/packet.d.ts",
            parsed: parse_source_file(AUGMENTATION_TEXT),
        },
        Input {
            file: CONSUMER,
            path: "/project/packet.ts",
            parsed: parse_source_file(consumer),
        },
    ]
}

fn context(inputs: &[Input]) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in inputs {
        assert!(input.parsed.diagnostics.is_empty());
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.file != CONSUMER,
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
                NodeData::PropertyDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(reference(checker, file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {name}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn variable_parts(checker: &CanonicalCheckerContext<'_>, name: &str) -> (NodeRef, NodeRef) {
    let declaration = named(checker, CONSUMER, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &checker
        .file(CONSUMER)
        .unwrap()
        .0
        .get(declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    (
        reference(checker, CONSUMER, data.name),
        reference(checker, CONSUMER, data.initializer.unwrap()),
    )
}

fn value_annotation(checker: &CanonicalCheckerContext<'_>, file: FileId) -> NodeRef {
    let declaration = named(checker, file, SyntaxKind::VariableDeclaration, "Packet");
    let NodeData::VariableDeclaration(data) = &checker
        .file(file)
        .unwrap()
        .0
        .get(declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    reference(checker, file, data.type_.unwrap())
}

fn assert_owner(checker: &CanonicalCheckerContext<'_>) -> SemanticSymbolId {
    let declarations = [
        named(checker, LIBRARY, SyntaxKind::InterfaceDeclaration, "Packet"),
        named(checker, LIBRARY, SyntaxKind::VariableDeclaration, "Packet"),
        named(
            checker,
            AUGMENTATION,
            SyntaxKind::InterfaceDeclaration,
            "Packet",
        ),
        named(
            checker,
            AUGMENTATION,
            SyntaxKind::VariableDeclaration,
            "Packet",
        ),
    ];
    let owner = symbol(checker, declarations[0]);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT
    );
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    assert_eq!(record.value_declaration(), Some(declarations[1]));
    assert!(record.parent().is_none());
    for declaration in declarations {
        assert_eq!(symbol(checker, declaration), owner);
    }
    let raw = checker.file(AUGMENTATION).unwrap().1;
    let raw_interface = raw.symbol(declarations[2]).unwrap();
    assert_eq!(raw.symbol(declarations[3]), Some(raw_interface));
    assert_ne!(raw_interface, owner);
    assert_eq!(
        checker
            .store()
            .symbol(raw_interface)
            .unwrap()
            .declarations(),
        Some(&declarations[2..])
    );
    owner
}

fn assert_cold_header(
    checker: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    type_: TypeId,
) {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the real merged owner must keep its interface type")
    };
    assert!(!data.declared_members_resolved);
    assert!(data.declared_members.is_none());
    assert!(data.reference.object.structured.members.is_none());
    assert!(data.reference.object.structured.properties.is_none());
    assert!(
        checker
            .store()
            .value_symbol_links(owner)
            .is_none_or(|links| links.resolved_type.is_none())
    );
    for file in [LIBRARY, AUGMENTATION] {
        assert!(
            checker
                .store()
                .type_node_links(value_annotation(checker, file))
                .is_none_or(|links| links.resolved_type.is_none())
        );
    }
    for (file, name) in [(LIBRARY, "library"), (AUGMENTATION, "augmented")] {
        let property = symbol(
            checker,
            named(checker, file, SyntaxKind::PropertyDeclaration, name),
        );
        assert!(
            checker
                .store()
                .value_symbol_links(property)
                .is_none_or(|links| links.resolved_type.is_none())
        );
    }
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(CONSUMER).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
}

fn assert_reads(checker: &mut CanonicalCheckerContext<'_>, owner: SemanticSymbolId, type_: TypeId) {
    let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
    let reads = [
        (LIBRARY, "library", intrinsics.number_type),
        (AUGMENTATION, "augmented", intrinsics.string_type),
        (LIBRARY, "prototype", type_),
    ];
    for (file, name, expected) in reads {
        let declaration = named(checker, file, SyntaxKind::PropertyDeclaration, name);
        let property = symbol(checker, declaration);
        assert_eq!(
            checker.store().symbol(property).unwrap().declarations(),
            Some([declaration].as_slice())
        );
        if name != "prototype" {
            assert_eq!(checker.store().get_parent_of_symbol(property), Some(owner));
        }
        let (_, access) = variable_parts(checker, name);
        assert_eq!(
            checker
                .file(CONSUMER)
                .unwrap()
                .0
                .get(access.node)
                .unwrap()
                .kind,
            SyntaxKind::PropertyAccessExpression
        );
        assert_eq!(checker.get_type_at_location(access).unwrap(), expected);
        assert_eq!(
            checker.get_symbol_at_location(access).unwrap(),
            Some(property)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(expected)
        );
        let variable = named(checker, CONSUMER, SyntaxKind::VariableDeclaration, name);
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol(checker, variable))
                .unwrap()
                .resolved_type,
            Some(expected)
        );
    }
    assert_eq!(assert_owner(checker), owner);
    assert_eq!(checker.get_declared_type_of_symbol(owner).unwrap(), type_);
    assert_eq!(
        checker.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    let value_type = checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_ne!(value_type, type_);
    assert_eq!(
        checker
            .store()
            .type_node_links(value_annotation(checker, LIBRARY))
            .unwrap()
            .resolved_type,
        Some(value_type)
    );
    assert!(
        checker
            .store()
            .type_node_links(value_annotation(checker, AUGMENTATION))
            .is_none_or(|links| links.resolved_type.is_none())
    );
}

fn check_case(consumer: &str, incompatible: bool) {
    let inputs = inputs(consumer);
    let mut checker = context(&inputs);
    let owner = assert_owner(&checker);
    let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
    assert_cold_header(&checker, owner, type_);
    let (_, access) = variable_parts(&checker, "library");
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;

    // This query starts source checking. The consumer declares no interfaces.
    assert_eq!(checker.get_type_at_location(access).unwrap(), number);
    checker.check_source_file(CONSUMER).unwrap();
    assert_reads(&mut checker, owner, type_);
    if incompatible {
        let (name, rejected) = variable_parts(&checker, "rejected");
        assert_eq!(checker.get_type_at_location(rejected).unwrap(), number);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("only the number assigned to string must fail")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(name));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.related_information.is_empty());
    } else {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
    }
    let diagnostics = checker.diagnostics().clone();
    let owner_value = checker.store().value_symbol_links(owner).cloned();
    let owner_type = checker.store().declared_type_links(owner).cloned();
    for _ in 0..2 {
        checker.recheck_source_file(CONSUMER).unwrap();
        assert_reads(&mut checker, owner, type_);
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(
            checker.store().value_symbol_links(owner),
            owner_value.as_ref()
        );
        assert_eq!(
            checker.store().declared_type_links(owner),
            owner_type.as_ref()
        );
    }
}

#[test]
fn merged_global_property_reads_keep_both_interfaces_and_the_value_owner() {
    check_case(CONSUMER_TEXT, false);
}

#[test]
fn merged_global_property_reads_keep_incompatible_assignment_diagnostics() {
    let consumer = format!("{CONSUMER_TEXT}const rejected: string = packet.library;\n");
    check_case(&consumer, true);
}
