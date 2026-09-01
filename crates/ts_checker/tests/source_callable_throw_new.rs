use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags, type_records::LiteralValue,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_220);
const LIBRARIES: &[(&str, &str)] = &[
    (
        "\"/lib/lib.es5.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "\"/lib/lib.decorators.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "\"/lib/lib.decorators.legacy.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
    (
        "\"/lib/lib.es2015.collection.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es2015.collection.d.ts"),
    ),
    (
        "\"/lib/lib.es2015.iterable.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es2015.iterable.d.ts"),
    ),
    (
        "\"/lib/lib.es2015.symbol.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
    ),
    (
        "\"/lib/lib.es2021.promise.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es2021.promise.d.ts"),
    ),
    (
        "\"/lib/lib.es2022.error.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es2022.error.d.ts"),
    ),
];

const ARROW: &str = r#"const compile = (_glob?: string | string[], _options?: { partial?: boolean }): unknown => {
  throw new Error("compile() is not ported");
};
"#;

struct Library {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
}

fn libraries(modern: bool) -> Vec<Library> {
    LIBRARIES[..if modern { LIBRARIES.len() } else { 3 }]
        .iter()
        .enumerate()
        .map(|(index, &(path, source))| Library {
            file: FileId::new(203_221 + u32::try_from(index).unwrap()),
            path,
            parsed: parse_source_file(source),
        })
        .collect()
}

fn context<'a>(parsed: &'a ParseResult, libraries: &'a [Library]) -> CanonicalCheckerContext<'a> {
    let files = libraries
        .iter()
        .map(|library| (library.file, &library.parsed, library.path))
        .chain([(FILE, parsed, "\"/project/callable-throw-new.ts\"")])
        .collect::<Vec<_>>();
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != FILE,
                    file != FILE,
                    if file == FILE {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_unchecked_indexed_access: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, FILE, id)))
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "expected one {kind:?}");
    found[0]
}

fn interface(library: &Library, expected: &str) -> NodeRef {
    let found = library
        .parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::InterfaceDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(&library.parsed, library.file, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "expected one library interface {expected}");
    found[0]
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("checking must publish the actual signature")
}

fn checked_type(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .expect("checking must publish the expression type")
}

fn assert_constructor(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    libraries: &[Library],
    construction: NodeRef,
) -> Vec<NodeRef> {
    let NodeData::NewExpression(data) = &parsed.arena.get(construction.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.type_arguments.is_none());
    let callee = node(parsed, FILE, data.expression);
    let [argument] = data.arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one Error argument")
    };
    let argument = node(parsed, FILE, *argument);
    let instance = checked_type(checker, construction);
    let constructor = checked_type(checker, callee);
    let argument_type = checked_type(checker, argument);
    let TypeData::Literal(literal) = checker.store().type_payload(argument_type).unwrap().data()
    else {
        panic!("expected the actual string argument")
    };
    assert_eq!(
        literal.value,
        LiteralValue::String("compile() is not ported".to_owned())
    );

    let error_owner = symbol(checker, interface(&libraries[0], "Error"));
    let constructor_owner = symbol(checker, interface(&libraries[0], "ErrorConstructor"));
    assert_eq!(
        checker.get_declared_type_of_symbol(error_owner),
        Ok(instance)
    );
    assert_eq!(
        checker.get_declared_type_of_symbol(constructor_owner),
        Ok(constructor)
    );
    assert_eq!(
        checker.get_symbol_at_location(callee),
        Ok(Some(error_owner))
    );
    assert_eq!(
        checker.store().type_payload(instance).unwrap().symbol(),
        Some(error_owner)
    );
    assert_eq!(
        checker.store().type_payload(constructor).unwrap().symbol(),
        Some(constructor_owner)
    );
    assert_ne!(instance, constructor);

    let resolved = signature(checker, construction);
    assert_eq!(checker.get_return_type_of_signature(resolved), Ok(instance));
    let record = checker.store().signature(resolved).unwrap();
    assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
    assert_eq!(record.min_argument_count(), 0);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let declaration = record.declaration().unwrap();
    let library = libraries
        .iter()
        .find(|library| library.file == declaration.file)
        .unwrap();
    assert_eq!(declaration.arena, library.parsed.arena.id());
    let declaration_record = library.parsed.arena.get(declaration.node).unwrap();
    assert_eq!(declaration_record.kind, SyntaxKind::ConstructSignature);
    assert_eq!(
        declaration_record.parent,
        Some(interface(library, "ErrorConstructor").node)
    );
    let NodeData::ConstructSignatureDeclaration(data) = &declaration_record.data else {
        unreachable!()
    };
    let parameters = data
        .parameters
        .nodes
        .iter()
        .map(|&id| symbol(checker, node(&library.parsed, library.file, id)))
        .collect::<Vec<_>>();
    assert_eq!(record.parameters(), parameters);
    assert!(parameters.len() == 1 || parameters.len() == 2);
    vec![construction, callee, argument]
}

fn assert_callable(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callable: NodeRef,
) {
    let (body, annotation, parameters) = match &parsed.arena.get(callable.node).unwrap().data {
        NodeData::ArrowFunction(data) => (data.body, data.type_.unwrap(), &data.parameters.nodes),
        NodeData::FunctionDeclaration(data) => (
            data.body.unwrap(),
            data.type_.unwrap(),
            &data.parameters.nodes,
        ),
        NodeData::FunctionExpression(data) => {
            (data.body, data.type_.unwrap(), &data.parameters.nodes)
        }
        _ => panic!("expected the actual callable"),
    };
    let unknown = checker.store().intrinsic_bootstrap().unwrap().unknown_type;
    assert_eq!(
        checker.get_type_from_type_node(node(parsed, FILE, annotation)),
        Ok(unknown)
    );
    let resolved = signature(checker, callable);
    assert_eq!(checker.get_return_type_of_signature(resolved), Ok(unknown));
    let record = checker.store().signature(resolved).unwrap();
    assert_eq!(record.declaration(), Some(callable));
    assert!(!record.flags().contains(SignatureFlags::CONSTRUCT));
    assert_eq!(record.min_argument_count(), 0);
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&id| symbol(checker, node(parsed, FILE, id)))
            .collect::<Vec<_>>()
    );
    assert_eq!(record.parameters().len(), 2);
    assert!(record.type_parameters().is_empty());
    assert!(!record.has_rest_parameter());
    let callable_type = checker.get_type_at_location(callable).unwrap();
    let payload = checker.store().type_payload(callable_type).unwrap();
    assert_eq!(payload.symbol(), Some(symbol(checker, callable)));
    let TypeData::Object(object) = payload.data() else {
        panic!("expected the actual callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[resolved][..])
    );
    let bound = checker.file(FILE).unwrap().1;
    assert_eq!(bound.container(node(parsed, FILE, body)), Some(callable));
    assert_eq!(
        bound.flow_graph().container_is_complete(callable),
        Some(true)
    );
    assert_eq!(bound.flow_graph().container_end(callable), None);
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    invalid: bool,
) {
    if !invalid {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        return;
    }
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one local error: {:?}", checker.diagnostics())
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    assert!(diagnostic.range_override.is_none());
    let location = diagnostic.node.unwrap();
    assert_eq!(location.file, FILE);
    assert_eq!(location.arena, parsed.arena.id());
    let record = parsed.arena.get(location.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::Identifier);
    let start = source.find("count:").unwrap();
    assert_eq!(usize::try_from(record.range.start.get()).unwrap(), start);
    assert_eq!(
        usize::try_from(record.range.end.get()).unwrap(),
        start + "count".len()
    );
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
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        checker.global_types().clone(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn check(source: &str, kind: SyntaxKind, invalid: bool) {
    let parsed = parse_source_file(source);
    let callable = only(&parsed, kind);
    let construction = only(&parsed, SyntaxKind::NewExpression);
    let thrown = only(&parsed, SyntaxKind::ThrowStatement);
    let NodeData::ThrowStatement(data) = &parsed.arena.get(thrown.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(data.expression, construction.node);
    assert_eq!(
        parsed.arena.get(construction.node).unwrap().parent,
        Some(thrown.node)
    );
    assert!(
        parsed
            .arena
            .iter()
            .all(|(_, record)| record.kind != SyntaxKind::ReturnStatement)
    );
    for modern in [false, true] {
        let libraries = libraries(modern);
        for query_first in [false, true] {
            let mut checker = context(&parsed, &libraries);
            assert!(checker.global_types().diagnostics().is_empty());
            assert!(
                !checker
                    .store()
                    .source_file_links(checker.source_file(FILE).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
            let cold = query_first.then(|| checker.get_type_at_location(construction).unwrap());
            checker.check_source_file(FILE).unwrap();
            assert_diagnostics(&checker, &parsed, source, invalid);
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(FILE).unwrap())
                    .unwrap()
                    .type_checked
            );
            assert_eq!(checker.store().type_resolution_len(), 0);
            let mut queries = assert_constructor(&mut checker, &parsed, &libraries, construction);
            if let Some(cold) = cold {
                assert_eq!(cold, checked_type(&checker, construction));
            }
            assert_callable(&mut checker, &parsed, callable);
            queries.push(callable);
            let types = queries
                .iter()
                .map(|&location| (location, checker.get_type_at_location(location).unwrap()))
                .collect::<Vec<_>>();
            assert_diagnostics(&checker, &parsed, source, invalid);
            let before = snapshot(&checker, &parsed);
            for _ in 0..2 {
                checker.check_source_file(FILE).unwrap();
                checker.recheck_source_file(FILE).unwrap();
                for &(location, type_) in &types {
                    assert_eq!(checker.get_type_at_location(location), Ok(type_));
                }
                assert_constructor(&mut checker, &parsed, &libraries, construction);
                assert_callable(&mut checker, &parsed, callable);
                assert_diagnostics(&checker, &parsed, source, invalid);
                assert_eq!(snapshot(&checker, &parsed), before);
            }
        }
    }
}

#[test]
fn stored_arrow_throw_new_keeps_the_real_error_constructor() {
    check(ARROW, SyntaxKind::ArrowFunction, false);
}

#[test]
fn stored_arrow_throw_new_preserves_a_local_type_error() {
    let source = ARROW.replacen(
        "\n  throw",
        "\n  const count: number = \"bad\";\n  throw",
        1,
    );
    assert_eq!(
        source.replace("  const count: number = \"bad\";\n", ""),
        ARROW
    );
    check(&source, SyntaxKind::ArrowFunction, true);
}

#[test]
fn function_declaration_throw_new_keeps_the_real_error_constructor() {
    check(
        r#"function compile(_glob?: string | string[], _options?: { partial?: boolean }): unknown {
  throw new Error("compile() is not ported");
}
"#,
        SyntaxKind::FunctionDeclaration,
        false,
    );
}

#[test]
fn function_expression_throw_new_keeps_the_real_error_constructor() {
    check(
        r#"const compile = function (_glob?: string | string[], _options?: { partial?: boolean }): unknown {
  throw new Error("compile() is not ported");
};
"#,
        SyntaxKind::FunctionExpression,
        false,
    );
}
