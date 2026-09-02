use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_260);
const LIBRARY: FileId = FileId::new(203_261);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

const STRING_EXPRESSION: &str = r#"export {};
const message: string = "ready";
const result = new Error(message);
"#;

const SHADOWED_CONSTRUCTOR: &str = r#"export {};
interface LocalResult { value: string; }
interface LocalConstructor { new(message: string): LocalResult; }
declare const Error: LocalConstructor;
const result = new Error("local");
"#;

#[derive(Clone, Copy)]
enum ConstructorSource {
    Library,
    Local,
}

struct ExpectedConstructor {
    value: NodeRef,
    instance: NodeRef,
    owner: NodeRef,
    signature: NodeRef,
    parameter: NodeRef,
    parameter_type: NodeRef,
    optional: bool,
}

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (
            FILE,
            parsed,
            "\"/project/nongeneric-named-constructors.ts\"",
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            no_unchecked_indexed_access: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, name: &str, kind: SyntaxKind) -> NodeRef {
    let declarations = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = declarations.as_slice() else {
        panic!("expected one {kind:?} named {name}")
    };
    *declaration
}

fn construction(parsed: &ParseResult) -> (NodeRef, NodeRef, NodeRef) {
    let constructions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::NewExpression(data) = &record.data else {
                return None;
            };
            assert_eq!(record.kind, SyntaxKind::NewExpression);
            assert!(data.type_arguments.is_none());
            let [argument] = data.arguments.as_ref().unwrap().nodes.as_slice() else {
                panic!("expected one supplied constructor argument")
            };
            Some((
                node(parsed, FILE, id),
                node(parsed, FILE, data.expression),
                node(parsed, FILE, *argument),
            ))
        })
        .collect::<Vec<_>>();
    let [construction] = constructions.as_slice() else {
        panic!("expected one new expression")
    };
    *construction
}

fn expected_constructor(
    parsed: &ParseResult,
    file: FileId,
    instance_name: &str,
    constructor_name: &str,
) -> ExpectedConstructor {
    let owner = named(
        parsed,
        file,
        constructor_name,
        SyntaxKind::InterfaceDeclaration,
    );
    let NodeData::InterfaceDeclaration(data) = &parsed.arena.get(owner.node).unwrap().data else {
        unreachable!()
    };
    let declarations = data
        .members
        .nodes
        .iter()
        .filter_map(|&id| {
            (parsed.arena.get(id).unwrap().kind == SyntaxKind::ConstructSignature)
                .then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [signature] = declarations.as_slice() else {
        panic!("expected one construct signature in {constructor_name}")
    };
    let signature = *signature;
    assert_eq!(
        parsed.arena.get(signature.node).unwrap().parent,
        Some(owner.node)
    );
    let NodeData::ConstructSignatureDeclaration(data) =
        &parsed.arena.get(signature.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.type_parameters.is_none());
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("expected one declared constructor parameter")
    };
    let parameter = node(parsed, file, *parameter);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.dot_dot_dot_token.is_none());
    let parameter_type = node(parsed, file, data.type_.unwrap());
    assert_eq!(
        parsed.arena.get(parameter_type.node).unwrap().kind,
        SyntaxKind::StringKeyword
    );
    ExpectedConstructor {
        value: named(parsed, file, "Error", SyntaxKind::VariableDeclaration),
        instance: named(
            parsed,
            file,
            instance_name,
            SyntaxKind::InterfaceDeclaration,
        ),
        owner,
        signature,
        parameter,
        parameter_type,
        optional: data.question_token.is_some(),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = checker.file(declaration.file).unwrap().1;
    let raw = bound.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn assert_constructor(
    checker: &mut CanonicalCheckerContext<'_>,
    construction: NodeRef,
    callee: NodeRef,
    expected: &ExpectedConstructor,
) -> (TypeId, TypeId, SignatureId) {
    let instance_owner = symbol(checker, expected.instance);
    let constructor_owner = symbol(checker, expected.owner);
    let value_owner = symbol(checker, expected.value);
    let instance_type = checker.get_declared_type_of_symbol(instance_owner).unwrap();
    let constructor_type = checker
        .get_declared_type_of_symbol(constructor_owner)
        .unwrap();
    assert_eq!(
        checker.get_type_at_location(construction),
        Ok(instance_type)
    );
    assert_eq!(checker.get_type_at_location(callee), Ok(constructor_type));
    assert_eq!(
        checker.get_symbol_at_location(callee),
        Ok(Some(value_owner))
    );
    assert_eq!(
        checker
            .store()
            .type_payload(instance_type)
            .unwrap()
            .symbol(),
        Some(instance_owner)
    );
    assert_eq!(
        checker
            .store()
            .type_payload(constructor_type)
            .unwrap()
            .symbol(),
        Some(constructor_owner)
    );
    assert_ne!(instance_type, constructor_type);
    let selected = signature(checker, construction);
    assert_eq!(
        checker.get_return_type_of_signature(selected),
        Ok(instance_type)
    );
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        checker.get_type_from_type_node(expected.parameter_type),
        Ok(string)
    );
    let record = checker.store().signature(selected).unwrap();
    assert_eq!(record.declaration(), Some(expected.signature));
    assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
    assert!(record.type_parameters().is_empty());
    assert_eq!(
        record.min_argument_count(),
        if expected.optional { 0 } else { 1 }
    );
    assert_eq!(record.parameters(), &[symbol(checker, expected.parameter)]);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(instance_type));
    (instance_type, constructor_type, selected)
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(parsed, FILE, id);
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(owner, _)| {
                (
                    owner,
                    store.value_symbol_links(owner).cloned(),
                    store.declared_type_links(owner).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn check(source: &str, owner: ConstructorSource) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let (construction, callee, argument) = construction(&parsed);
    let global_error = named(&library, LIBRARY, "Error", SyntaxKind::InterfaceDeclaration);
    let global_constructor = named(
        &library,
        LIBRARY,
        "ErrorConstructor",
        SyntaxKind::InterfaceDeclaration,
    );
    let expected = match owner {
        ConstructorSource::Library => {
            expected_constructor(&library, LIBRARY, "Error", "ErrorConstructor")
        }
        ConstructorSource::Local => {
            expected_constructor(&parsed, FILE, "LocalResult", "LocalConstructor")
        }
    };
    let result = named(&parsed, FILE, "result", SyntaxKind::VariableDeclaration);
    let NodeData::VariableDeclaration(result_data) = &parsed.arena.get(result.node).unwrap().data
    else {
        unreachable!()
    };
    let result_name = node(&parsed, FILE, result_data.name);
    for query_first in [false, true] {
        let mut checker = context(&parsed, &library);
        let root = checker.source_file(FILE).unwrap();
        assert!(
            !checker
                .store()
                .source_file_links(root)
                .is_some_and(|links| links.type_checked)
        );
        let cold = query_first.then(|| checker.get_type_at_location(construction).unwrap());
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(root)
                .unwrap()
                .type_checked
        );
        let identities = assert_constructor(&mut checker, construction, callee, &expected);
        if let Some(cold) = cold {
            assert_eq!(cold, identities.0);
        }
        assert_eq!(checker.get_type_at_location(result_name), Ok(identities.0));
        match owner {
            ConstructorSource::Library => {
                assert!(expected.optional);
                assert_eq!(
                    symbol(&checker, expected.value),
                    symbol(&checker, global_error)
                );
                assert_eq!(
                    parsed.arena.get(argument.node).unwrap().kind,
                    SyntaxKind::Identifier
                );
                let message = named(&parsed, FILE, "message", SyntaxKind::VariableDeclaration);
                assert_eq!(
                    checker.get_symbol_at_location(argument),
                    Ok(Some(symbol(&checker, message)))
                );
                let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
                assert_eq!(checker.get_type_at_location(argument), Ok(string));
            }
            ConstructorSource::Local => {
                assert!(!expected.optional);
                assert_eq!(
                    parsed.arena.get(argument.node).unwrap().kind,
                    SyntaxKind::StringLiteral
                );
                assert_ne!(
                    symbol(&checker, expected.value),
                    symbol(&checker, global_error)
                );
                assert_ne!(
                    symbol(&checker, expected.instance),
                    symbol(&checker, global_error)
                );
                assert_ne!(
                    symbol(&checker, expected.owner),
                    symbol(&checker, global_constructor)
                );
            }
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let queries = [construction, callee, argument, result_name];
        let types =
            queries.map(|location| (location, checker.get_type_at_location(location).unwrap()));
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(
                assert_constructor(&mut checker, construction, callee, &expected),
                identities
            );
            for (location, type_) in types {
                assert_eq!(checker.get_type_at_location(location), Ok(type_));
            }
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn nongeneric_named_constructor_checks_string_expression_argument() {
    check(STRING_EXPRESSION, ConstructorSource::Library);
}

#[test]
fn nongeneric_named_constructor_respects_shadowed_binding() {
    check(SHADOWED_CONSTRUCTOR, ConstructorSource::Local);
}
