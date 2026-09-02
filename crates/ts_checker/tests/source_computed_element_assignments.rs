use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AssignmentSyntaxRole, AssignmentUnsupported, CanonicalCheckerContext, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SourceCheckError, TypeData, TypeId, UnsupportedSourceSyntax,
    artifact_queries::CanonicalArtifactQueryError,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(920_264);

const GENERIC_WRITES: &str = r#"declare const writableKey: unique symbol;
declare const fixedKey: unique symbol;
interface Cell<T> { [writableKey]: T; readonly [fixedKey]: T; }
declare const text: Cell<string>;
declare const count: Cell<number>;
const textValue: string = text[writableKey];
const countValue: number = count[writableKey];
text[writableKey] = "next";
count[writableKey] = 2;
text[writableKey] = 2;
count[writableKey] = "next";
text[fixedKey] = 2;
count[fixedKey] = "next";
"#;

const OPTIONAL_WRITES: &str = r#"declare const maybeKey: unique symbol;
declare const fixedKey: unique symbol;
interface Cell<T> { [maybeKey]?: T; }
interface Cell<T> { readonly [fixedKey]: T; }
declare const text: Cell<string>;
declare const count: Cell<number>;
const textValue: string | undefined = text[maybeKey];
const countValue: number | undefined = count[maybeKey];
const required: string = text[maybeKey];
text[maybeKey] = "next";
count[maybeKey] = 2;
text[fixedKey] = "next";
"#;

fn parse(source: &str) -> ParseResult {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new_with_default_library(
                EscapedName::source("\"/computed-element-assignments.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            no_unchecked_indexed_access: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let owner = parsed.arena.get(parent.node).unwrap();
    let record = parsed.arena.get(id).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, id)
}

fn variable(parsed: &ParseResult, name: &str) -> NodeRef {
    let declarations = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = declarations.as_slice() else {
        panic!("expected one variable named {name}");
    };
    *declaration
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = variable(parsed, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    child(parsed, declaration, variable.initializer.unwrap())
}

fn annotation(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = variable(parsed, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    child(parsed, declaration, variable.type_.unwrap())
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

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn mapped_property(
    context: &CanonicalCheckerContext<'_>,
    reference: TypeId,
    key: SemanticSymbolId,
    expected: TypeId,
    readonly: bool,
    optional: bool,
) -> SemanticSymbolId {
    let store = context.store();
    let key_type = store
        .value_symbol_links(key)
        .unwrap()
        .resolved_type
        .unwrap();
    let key_record = store.type_payload(key_type).unwrap();
    assert_eq!(key_record.symbol(), Some(key));
    let TypeData::UniqueEsSymbol(unique) = key_record.data() else {
        panic!("the key must retain its unique-symbol type");
    };
    let TypeData::TypeReference(instance) = store.type_payload(reference).unwrap().data() else {
        panic!("the receiver must retain its generic instance");
    };
    let property = store
        .symbol_table(instance.object.structured.members.unwrap())
        .unwrap()
        .get(unique.name.as_ref())
        .unwrap();
    let record = store.symbol(property).unwrap();
    let links = store.value_symbol_links(property).unwrap();
    let original = links
        .target
        .expect("the mapped property must retain its target");
    assert_ne!(property, original);
    assert_ne!(property, key);
    assert_eq!(record.name(), unique.name.as_ref());
    assert_eq!(record.parent(), store.symbol(original).unwrap().parent());
    assert_eq!(
        record.declarations(),
        store.symbol(original).unwrap().declarations()
    );
    assert!(
        record
            .flags()
            .contains(SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
    );
    assert_eq!(record.flags().contains(SymbolFlags::OPTIONAL), optional);
    assert!(record.check_flags().contains(CheckFlags::LATE));
    assert_eq!(
        record.check_flags().contains(CheckFlags::READONLY),
        readonly
    );
    assert_eq!(links.name_type, Some(key_type));
    assert_eq!(links.resolved_type, Some(expected));
    assert!(links.mapper.is_some());
    property
}

fn optional_read(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    expected: TypeId,
) -> TypeId {
    let read = context
        .get_type_at_location(initializer(parsed, name))
        .unwrap();
    let TypeData::Union(optional) = context.store().type_payload(read).unwrap().data() else {
        panic!("the optional read must include undefined");
    };
    let undefined = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    assert_eq!(optional.union.types.len(), 2);
    assert!(optional.union.types.contains(&expected));
    assert!(optional.union.types.contains(&undefined));
    read
}

fn assignment_left(parsed: &ParseResult) -> NodeRef {
    let assignments = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            parsed
                .arena
                .get(binary.operator_token)?
                .kind
                .is_assignment_operator()
                .then_some((node(parsed, id), binary.left))
        })
        .collect::<Vec<_>>();
    let [(assignment, left)] = assignments.as_slice() else {
        panic!("expected one assignment");
    };
    let left = child(parsed, *assignment, *left);
    assert_eq!(
        parsed.arena.get(left.node).unwrap().kind,
        SyntaxKind::ElementAccessExpression
    );
    left
}

#[test]
fn ordinary_computed_writes_keep_each_generic_receiver_and_readonly_diagnostics() {
    let parsed = parse(GENERIC_WRITES);
    for reverse in [false, true] {
        let mut checker = context(&parsed);
        let mut order = [("text", "textValue"), ("count", "countValue")];
        if reverse {
            order.reverse();
        }
        for (receiver, read) in order {
            checker
                .get_type_from_type_node(annotation(&parsed, receiver))
                .unwrap();
            checker
                .get_type_at_location(initializer(&parsed, read))
                .unwrap();
        }
        let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
        let cases = [
            ("text", "textValue", intrinsic.string_type),
            ("count", "countValue", intrinsic.number_type),
        ];
        let writable = symbol(&checker, variable(&parsed, "writableKey"));
        let fixed = symbol(&checker, variable(&parsed, "fixedKey"));
        assert_ne!(writable, fixed);
        let mut identities = Vec::new();
        for (receiver, read, expected) in cases {
            let reference = checker
                .get_type_from_type_node(annotation(&parsed, receiver))
                .unwrap();
            assert_eq!(
                checker
                    .get_type_at_location(initializer(&parsed, read))
                    .unwrap(),
                expected
            );
            for (key, readonly) in [(writable, false), (fixed, true)] {
                let property = mapped_property(&checker, reference, key, expected, readonly, false);
                let links = checker.store().value_symbol_links(property).unwrap();
                identities.push((
                    receiver,
                    reference,
                    key,
                    expected,
                    readonly,
                    property,
                    links.mapper,
                ));
            }
        }
        assert_ne!(identities[0].1, identities[2].1);
        assert_ne!(identities[0].5, identities[2].5);
        assert_ne!(identities[0].6, identities[2].6);
        assert_ne!(identities[1].5, identities[3].5);
        assert_ne!(identities[1].6, identities[3].6);
        checker.check_source_file(FILE).unwrap();
        assert_eq!(
            checker
                .diagnostics()
                .as_slice()
                .iter()
                .map(|entry| entry.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322, 2322, 2540, 2540]
        );
        let before = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            for &(receiver, reference, key, expected, readonly, property, mapper) in &identities {
                assert_eq!(
                    checker
                        .get_type_from_type_node(annotation(&parsed, receiver))
                        .unwrap(),
                    reference
                );
                assert_eq!(
                    mapped_property(&checker, reference, key, expected, readonly, false),
                    property
                );
                assert_eq!(
                    checker.store().value_symbol_links(property).unwrap().mapper,
                    mapper
                );
            }
            for (_, read, expected) in cases {
                assert_eq!(
                    checker
                        .get_type_at_location(initializer(&parsed, read))
                        .unwrap(),
                    expected
                );
            }
            assert_eq!(counts(&checker), before);
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
}

#[test]
fn merged_optional_computed_members_keep_read_types_and_write_diagnostics() {
    let parsed = parse(OPTIONAL_WRITES);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
    let cases = [
        ("text", "textValue", intrinsic.string_type),
        ("count", "countValue", intrinsic.number_type),
    ];
    let maybe = symbol(&checker, variable(&parsed, "maybeKey"));
    let fixed = symbol(&checker, variable(&parsed, "fixedKey"));
    let mut identities = Vec::new();
    for (receiver, read, expected) in cases {
        let reference = checker
            .get_type_from_type_node(annotation(&parsed, receiver))
            .unwrap();
        let read_type = optional_read(&mut checker, &parsed, read, expected);
        let property = mapped_property(&checker, reference, maybe, expected, false, true);
        identities.push((receiver, read, expected, reference, read_type, property));
    }
    assert_ne!(identities[0].3, identities[1].3);
    assert_ne!(identities[0].4, identities[1].4);
    assert_ne!(identities[0].5, identities[1].5);
    mapped_property(&checker, identities[0].3, fixed, cases[0].2, true, false);
    assert_eq!(
        checker
            .diagnostics()
            .as_slice()
            .iter()
            .map(|entry| entry.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322, 2540]
    );
    let before = counts(&checker);
    let diagnostics = checker.diagnostics().clone();
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        for &(receiver, read, expected, reference, read_type, property) in &identities {
            assert_eq!(
                checker
                    .get_type_from_type_node(annotation(&parsed, receiver))
                    .unwrap(),
                reference
            );
            assert_eq!(
                optional_read(&mut checker, &parsed, read, expected),
                read_type
            );
            assert_eq!(
                mapped_property(&checker, reference, maybe, expected, false, true),
                property
            );
        }
        assert_eq!(counts(&checker), before);
        assert_eq!(checker.diagnostics(), &diagnostics);
    }
}

#[test]
fn computed_writes_keep_optional_compound_and_foreign_node_rejections() {
    for (assignment, optional) in [("target?.[key] = 1;", true), ("target[key] += 1;", false)] {
        let parsed = parse(&format!(
            "declare const key: unique symbol;\ninterface Cell {{ [key]: number; }}\ndeclare const target: Cell;\n{assignment}"
        ));
        let left = assignment_left(&parsed);
        let expected = SourceCheckError::Unsupported(if optional {
            UnsupportedSourceSyntax::Element(left)
        } else {
            UnsupportedSourceSyntax::Assignment(AssignmentUnsupported::Syntax {
                node: left,
                kind: SyntaxKind::ElementAccessExpression,
                role: AssignmentSyntaxRole::LeftHandSide,
            })
        });
        let mut checker = context(&parsed);
        assert_eq!(checker.check_source_file(FILE), Err(expected));
        let before = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        assert!(diagnostics.as_slice().is_empty());
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(expected));
            assert_eq!(counts(&checker), before);
            assert_eq!(checker.diagnostics(), &diagnostics);
        }
    }
    let parsed = parse(GENERIC_WRITES);
    let foreign = parse(GENERIC_WRITES);
    assert_ne!(parsed.arena.id(), foreign.arena.id());
    let foreign_read = initializer(&foreign, "textValue");
    let mut checker = context(&parsed);
    let before = counts(&checker);
    for _ in 0..2 {
        assert_eq!(
            checker.get_type_at_location(foreign_read),
            Err(CanonicalArtifactQueryError::ForeignNode(foreign_read))
        );
        assert_eq!(counts(&checker), before);
        assert!(checker.diagnostics().as_slice().is_empty());
    }
}
