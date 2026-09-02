use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const ES5_FILE: FileId = FileId::new(205_460);
const PROMISE_FILE: FileId = FileId::new(205_461);
const SOURCE: FileId = FileId::new(205_462);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const PROMISE: &str = include_str!("../../ts_bundled/libs/lib.es2015.promise.d.ts");

fn context<'a>(
    source: &'a ParseResult,
    es5: &'a ParseResult,
    promise: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (ES5_FILE, es5, "\"/lib/lib.es5.d.ts\""),
        (PROMISE_FILE, promise, "\"/lib/lib.es2015.promise.d.ts\""),
        (SOURCE, source, "\"/project/generic-promise.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let library = file != SOURCE;
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
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
            no_implicit_this: true,
            strict_function_types: true,
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

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((record.range.start, node(parsed, file, id)))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn only(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let nodes = nodes(parsed, file, kind);
    let [node] = nodes.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *node
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    let nodes = nodes(parsed, file, kind)
        .into_iter()
        .filter(|node| {
            let id = match &parsed.arena.get(node.node).unwrap().data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                _ => panic!("expected a variable or interface declaration"),
            };
            matches!(&parsed.arena.get(id).unwrap().data,
                NodeData::Identifier(identifier) if identifier.text == name)
        })
        .collect::<Vec<_>>();
    let [node] = nodes.as_slice() else {
        panic!("expected the real declaration of {name}")
    };
    *node
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let owner = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(record.range.start >= owner.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, parent.file, id)
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
        .expect("the actual declaration or call has a signature")
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the checked value retains its canonical type")
}

fn call_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let structured = checker
        .store()
        .type_payload(type_)
        .unwrap()
        .data()
        .structured()
        .unwrap();
    assert_eq!(structured.call_signature_count, 1);
    let [signature] = structured.signatures.as_deref().unwrap() else {
        panic!("the callback has one call signature")
    };
    *signature
}

#[derive(Clone, Copy)]
struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
}

fn parameter(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> Parameter {
    let declaration = child(parsed, parent, id);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(id).unwrap().data else {
        unreachable!()
    };
    assert!(data.initializer.is_none());
    assert!(data.dot_dot_dot_token.is_none());
    Parameter {
        declaration,
        name: child(parsed, declaration, data.name),
        annotation: data.type_.map(|id| child(parsed, declaration, id)),
    }
}

struct Library {
    value: NodeRef,
    promise: NodeRef,
    promise_like: NodeRef,
    constructor: NodeRef,
    formal: NodeRef,
    executor: Parameter,
    callbacks: [Parameter; 2],
}

fn library_parts(es5: &ParseResult, promise: &ParseResult) -> Library {
    let owner = named(
        promise,
        PROMISE_FILE,
        SyntaxKind::InterfaceDeclaration,
        "PromiseConstructor",
    );
    let constructor = only(promise, PROMISE_FILE, SyntaxKind::ConstructSignature);
    assert_eq!(
        promise.arena.get(constructor.node).unwrap().parent,
        Some(owner.node)
    );
    let NodeData::ConstructSignatureDeclaration(data) =
        &promise.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    let [formal] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the bundled constructor has one type parameter")
    };
    let formal = child(promise, constructor, *formal);
    let [executor] = data.parameters.nodes.as_slice() else {
        panic!("the bundled constructor has one executor parameter")
    };
    let executor = parameter(promise, constructor, *executor);
    let annotation = executor.annotation.unwrap();
    let NodeData::FunctionTypeNode(data) = &promise.arena.get(annotation.node).unwrap().data else {
        unreachable!()
    };
    let [resolve, reject] = data.parameters.nodes.as_slice() else {
        panic!("the bundled executor has resolve and reject parameters")
    };
    Library {
        value: named(
            promise,
            PROMISE_FILE,
            SyntaxKind::VariableDeclaration,
            "Promise",
        ),
        promise: named(es5, ES5_FILE, SyntaxKind::InterfaceDeclaration, "Promise"),
        promise_like: named(
            es5,
            ES5_FILE,
            SyntaxKind::InterfaceDeclaration,
            "PromiseLike",
        ),
        constructor,
        formal,
        executor,
        callbacks: [
            parameter(promise, annotation, *resolve),
            parameter(promise, annotation, *reject),
        ],
    }
}

struct Parts {
    function: NodeRef,
    formal: NodeRef,
    return_annotation: NodeRef,
    construction: NodeRef,
    callee: NodeRef,
    type_argument: NodeRef,
    executor: NodeRef,
    parameters: [Parameter; 2],
    captures: [NodeRef; 2],
    assignments: [(NodeRef, NodeRef, NodeRef); 2],
    promise: NodeRef,
    returned: NodeRef,
    result: NodeRef,
    call: NodeRef,
    wrong_argument: Option<NodeRef>,
}

#[allow(clippy::too_many_lines)] // Each node comes from the real enclosing function and executor.
fn source_parts(source: &ParseResult, invalid: bool) -> Parts {
    let function = only(source, SOURCE, SyntaxKind::FunctionDeclaration);
    let NodeData::FunctionDeclaration(data) = &source.arena.get(function.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.parameters.nodes.is_empty());
    let [formal] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("deferred owns TData")
    };
    let formal = child(source, function, *formal);
    let return_annotation = child(source, function, data.type_.unwrap());
    let promise = named(source, SOURCE, SyntaxKind::VariableDeclaration, "promise");
    let NodeData::VariableDeclaration(data) = &source.arena.get(promise.node).unwrap().data else {
        unreachable!()
    };
    let construction = child(source, promise, data.initializer.unwrap());
    let NodeData::NewExpression(data) = &source.arena.get(construction.node).unwrap().data else {
        panic!("the function-local initializer is the actual new expression")
    };
    let callee = child(source, construction, data.expression);
    let [type_argument] = data.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the actual constructor has one explicit type argument")
    };
    let type_argument = child(source, construction, *type_argument);
    let [executor] = data.arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the actual constructor has one executor")
    };
    let executor = child(source, construction, *executor);
    let NodeData::ArrowFunction(data) = &source.arena.get(executor.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.type_parameters.is_none());
    assert!(data.type_.is_none());
    let [resolve, reject] = data.parameters.nodes.as_slice() else {
        panic!("the source executor keeps both callback parameters")
    };
    let parameters = [
        parameter(source, executor, *resolve),
        parameter(source, executor, *reject),
    ];
    assert!(
        parameters
            .iter()
            .all(|parameter| parameter.annotation.is_none())
    );
    let captures = ["capturedResolve", "capturedReject"]
        .map(|name| named(source, SOURCE, SyntaxKind::VariableDeclaration, name));
    let assignments = nodes(source, SOURCE, SyntaxKind::BinaryExpression);
    let [first, second] = assignments.as_slice() else {
        panic!("the executor keeps both captured assignments")
    };
    let assignments = [*first, *second].map(|assignment| {
        let NodeData::BinaryExpression(data) = &source.arena.get(assignment.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            source.arena.get(data.operator_token).unwrap().kind,
            SyntaxKind::EqualsToken
        );
        (
            assignment,
            child(source, assignment, data.left),
            child(source, assignment, data.right),
        )
    });
    let returned = only(source, SOURCE, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(data) = &source.arena.get(returned.node).unwrap().data else {
        unreachable!()
    };
    let returned = child(source, returned, data.expression.unwrap());
    let result = named(source, SOURCE, SyntaxKind::VariableDeclaration, "result");
    let NodeData::VariableDeclaration(data) = &source.arena.get(result.node).unwrap().data else {
        unreachable!()
    };
    let call = child(source, result, data.initializer.unwrap());
    let wrong_argument = invalid.then(|| only(source, SOURCE, SyntaxKind::NumericLiteral));
    Parts {
        function,
        formal,
        return_annotation,
        construction,
        callee,
        type_argument,
        executor,
        parameters,
        captures,
        assignments,
        promise,
        returned,
        result,
        call,
        wrong_argument,
    }
}

fn assert_reference(
    checker: &CanonicalCheckerContext<'_>,
    actual: TypeId,
    target: TypeId,
    argument: TypeId,
) {
    let TypeData::TypeReference(reference) = checker.store().type_payload(actual).unwrap().data()
    else {
        panic!("the value must retain a canonical generic reference")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );
}

#[derive(Debug, Eq, PartialEq)]
struct Checked {
    formal: TypeId,
    construction: TypeId,
    result: TypeId,
    selected: SignatureId,
    executor: TypeId,
    callbacks: [TypeId; 2],
    captures: [TypeId; 2],
    resolve_value: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the library formal, source formal, and callback owners together.
fn checked_state(
    checker: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    parts: &Parts,
    library: &Library,
) -> Checked {
    let bound = checker.file(SOURCE).unwrap().1;
    assert_eq!(bound.container(parts.promise), Some(parts.function));
    for capture in parts.captures {
        assert_eq!(bound.container(capture), Some(parts.function));
    }
    for parameter in parts.parameters {
        assert_eq!(bound.container(parameter.declaration), Some(parts.executor));
    }
    let formal_owner = symbol(checker, parts.formal);
    let formal = checker.get_declared_type_of_symbol(formal_owner).unwrap();
    let record = checker.store().type_payload(formal).unwrap();
    assert_eq!(record.symbol(), Some(formal_owner));
    let TypeData::TypeParameter(parameter) = record.data() else {
        panic!("TData is the enclosing function's actual type parameter")
    };
    assert!(parameter.constraint.is_none());
    assert!(parameter.resolved_default_type.is_none());
    assert_eq!(
        checker.get_type_from_type_node(parts.type_argument),
        Ok(formal)
    );

    let promise_owner = symbol(checker, library.promise);
    assert_eq!(symbol(checker, library.value), promise_owner);
    let promise_target = checker.get_declared_type_of_symbol(promise_owner).unwrap();
    let promise_like = checker
        .get_declared_type_of_symbol(symbol(checker, library.promise_like))
        .unwrap();
    let construction = checker.get_type_at_location(parts.construction).unwrap();
    assert_reference(checker, construction, promise_target, formal);
    assert_eq!(
        checker.get_type_from_type_node(parts.return_annotation),
        Ok(construction)
    );
    assert_eq!(
        checker.get_type_at_location(parts.returned),
        Ok(construction)
    );
    assert_eq!(
        value_type(checker, symbol(checker, parts.promise)),
        construction
    );
    assert_eq!(
        checker.get_symbol_at_location(parts.callee),
        Ok(Some(promise_owner))
    );

    let original = signature(checker, library.constructor);
    let library_formal = checker
        .get_declared_type_of_symbol(symbol(checker, library.formal))
        .unwrap();
    assert_ne!(library_formal, formal);
    let record = checker.store().signature(original).unwrap();
    assert_eq!(record.declaration(), Some(library.constructor));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.type_parameters(), [library_formal]);
    assert_eq!(
        record.parameters(),
        [symbol(checker, library.executor.declaration)]
    );
    assert_eq!(record.min_argument_count(), 1);
    let selected = signature(checker, parts.construction);
    let record = checker.store().signature(selected).unwrap();
    assert_eq!(record.declaration(), Some(library.constructor));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.target(), Some(original));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(construction));
    let mapper = record.mapper().unwrap();
    assert_eq!(
        checker.store().map_type(mapper, library_formal),
        Some(formal)
    );
    let [executor_parameter] = record.parameters() else {
        panic!("the selected constructor keeps one executor parameter")
    };
    let executor_parameter = *executor_parameter;
    let original_executor = symbol(checker, library.executor.declaration);
    assert_ne!(executor_parameter, original_executor);
    let links = checker
        .store()
        .value_symbol_links(executor_parameter)
        .unwrap();
    assert_eq!(links.target, Some(original_executor));
    assert_eq!(links.mapper, Some(mapper));
    assert_eq!(
        checker
            .store()
            .symbol(executor_parameter)
            .unwrap()
            .declarations(),
        Some(&[library.executor.declaration][..])
    );

    let executor = checker.get_type_at_location(parts.executor).unwrap();
    let executor_owner = symbol(checker, parts.executor);
    assert_eq!(
        checker.store().type_payload(executor).unwrap().symbol(),
        Some(executor_owner)
    );
    assert_eq!(value_type(checker, executor_owner), executor);
    let source_signature = call_signature(checker, executor);
    assert_eq!(source_signature, signature(checker, parts.executor));
    let owners = parts
        .parameters
        .map(|parameter| symbol(checker, parameter.declaration));
    let record = checker.store().signature(source_signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.executor));
    assert_eq!(record.parameters(), owners);
    assert_eq!(record.min_argument_count(), 2);
    assert!(record.type_parameters().is_empty());
    assert!(record.target().is_none());
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(
        checker.get_return_type_of_signature(source_signature),
        Ok(void)
    );
    let callbacks = parts.parameters.map(|parameter| {
        let owner = symbol(checker, parameter.declaration);
        let record = checker.store().symbol(owner).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
        let type_ = checker.get_type_at_location(parameter.name).unwrap();
        assert_eq!(
            checker.get_type_at_location(parameter.declaration),
            Ok(type_)
        );
        assert_eq!(
            checker.get_symbol_at_location(parameter.name),
            Ok(Some(owner))
        );
        assert_eq!(value_type(checker, owner), type_);
        type_
    });
    let callback_signatures = callbacks.map(|type_| call_signature(checker, type_));
    for (index, callback) in callback_signatures.iter().copied().enumerate() {
        let record = checker.store().signature(callback).unwrap();
        assert_eq!(record.declaration(), library.callbacks[index].annotation);
        assert_eq!(record.parameters().len(), 1);
        assert_eq!(record.min_argument_count(), if index == 0 { 1 } else { 0 });
        assert!(record.type_parameters().is_empty());
        assert_eq!(checker.get_return_type_of_signature(callback), Ok(void));
    }
    let resolve_parameter = checker
        .store()
        .signature(callback_signatures[0])
        .unwrap()
        .parameters()[0];
    let resolve_value = value_type(checker, resolve_parameter);
    let TypeData::Union(union) = checker.store().type_payload(resolve_value).unwrap().data() else {
        panic!("resolve accepts the actual TData or PromiseLike<TData>")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&formal));
    let promise_like_value = *union
        .union
        .types
        .iter()
        .find(|&&type_| type_ != formal)
        .unwrap();
    assert_reference(checker, promise_like_value, promise_like, formal);
    let reject_parameter = checker
        .store()
        .signature(callback_signatures[1])
        .unwrap()
        .parameters()[0];
    assert_eq!(
        value_type(checker, reject_parameter),
        checker.store().intrinsic_bootstrap().unwrap().any_type
    );

    let captures = parts.captures.map(|declaration| {
        let NodeData::VariableDeclaration(data) = &source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(data.initializer.is_none());
        let annotation = child(source, declaration, data.type_.unwrap());
        let type_ = checker.get_type_from_type_node(annotation).unwrap();
        assert_eq!(value_type(checker, symbol(checker, declaration)), type_);
        type_
    });
    let captured_resolve = call_signature(checker, captures[0]);
    let captured_value = checker
        .store()
        .signature(captured_resolve)
        .unwrap()
        .parameters()[0];
    assert_eq!(value_type(checker, captured_value), formal);
    assert_ne!(captures[0], callbacks[0]);
    for (index, &(assignment, left, right)) in parts.assignments.iter().enumerate() {
        assert_eq!(
            checker.get_symbol_at_location(left),
            Ok(Some(symbol(checker, parts.captures[index])))
        );
        assert_eq!(
            checker.get_symbol_at_location(right),
            Ok(Some(owners[index]))
        );
        assert_eq!(checker.get_type_at_location(left), Ok(captures[index]));
        assert_eq!(checker.get_type_at_location(right), Ok(callbacks[index]));
        assert_eq!(
            checker.get_type_at_location(assignment),
            Ok(callbacks[index])
        );
    }
    let function_signature = signature(checker, parts.function);
    let record = checker.store().signature(function_signature).unwrap();
    assert_eq!(record.type_parameters(), [formal]);
    assert_eq!(record.resolved_return_type(), Some(construction));
    let result = checker.get_type_at_location(parts.call).unwrap();
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    assert_reference(checker, result, promise_target, string);
    assert_eq!(value_type(checker, symbol(checker, parts.result)), result);
    let record = checker
        .store()
        .signature(signature(checker, parts.call))
        .unwrap();
    assert_eq!(record.target(), Some(function_signature));
    assert_eq!(
        checker.store().map_type(record.mapper().unwrap(), formal),
        Some(string)
    );
    Checked {
        formal,
        construction,
        result,
        selected,
        executor,
        callbacks,
        captures,
        resolve_value,
    }
}

#[allow(clippy::too_many_lines)] // Source-first and query-first paths keep the same nested fixture.
fn check_case(resolve: &str, reject: &str, invalid: bool) {
    let bad_call = if invalid {
        format!("    {resolve}(123);\n")
    } else {
        String::new()
    };
    // The reject annotation mirrors the bundled callback. It is not a fallback type.
    let text = format!(
        "export function deferred<TData>(): Promise<TData> {{\n\
         let capturedResolve: (value: TData) => void;\n\
         let capturedReject: (reason?: any) => void;\n\
         const promise = new Promise<TData>(({resolve}, {reject}) => {{\n\
           capturedResolve = {resolve};\n\
           capturedReject = {reject};\n\
         {bad_call}  }});\n\
         return promise;\n\
         }}\n\
         const result = deferred<string>();\n"
    );
    let source = parse_source_file(&text);
    let es5 = parse_source_file(ES5);
    let promise = parse_source_file(PROMISE);
    let parts = source_parts(&source, invalid);
    let library = library_parts(&es5, &promise);
    for first in [
        None,
        Some(parts.parameters[0].name),
        Some(parts.parameters[1].name),
    ] {
        let mut checker = context(&source, &es5, &promise);
        assert!(checker.global_types().diagnostics().is_empty());
        let early =
            first.map(|location| (location, checker.get_type_at_location(location).unwrap()));
        checker.check_source_file(SOURCE).unwrap();
        let root = checker.source_file(SOURCE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(root)
                .unwrap()
                .type_checked
        );
        let checked = checked_state(&mut checker, &source, &parts, &library);
        if let Some((location, early)) = early {
            assert_eq!(checker.get_type_at_location(location), Ok(early));
        }
        if let Some(argument) = parts.wrong_argument {
            let target = checker.type_to_string(checked.resolve_value).unwrap();
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("the wrong resolve call must produce one native argument error")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.node, Some(argument));
            assert!(diagnostic.range_override.is_none());
            assert_eq!(
                diagnostic.diagnostic.arguments,
                ["number".to_owned(), target]
            );
        } else {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.type_alias_len(),
                ],
                source
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let node = node(&source, SOURCE, id);
                        (
                            store.type_node_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                            store.signature_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                parts.parameters.map(|parameter| {
                    store
                        .value_symbol_links(symbol(checker, parameter.declaration))
                        .cloned()
                }),
                parts
                    .captures
                    .map(|capture| store.value_symbol_links(symbol(checker, capture)).cloned()),
                store.source_file_links(root).cloned(),
                checker.diagnostics().clone(),
            )
        };
        let warm = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(SOURCE).unwrap();
            assert_eq!(
                checked_state(&mut checker, &source, &parts, &library),
                checked
            );
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(
                checked_state(&mut checker, &source, &parts, &library),
                checked
            );
            assert_eq!(snapshot(&checker), warm);
        }
    }
}

#[test]
fn function_local_generic_promise_keeps_bundled_executor_types_and_captured_assignments() {
    check_case("resolve", "reject", false);
    check_case("fulfill", "fail", false);
}

#[test]
fn function_local_generic_promise_rejects_a_wrong_resolve_argument_without_losing_identity() {
    check_case("accept", "decline", true);
}
