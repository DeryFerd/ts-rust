use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeLinks, SignatureId,
    SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeMapperId,
    TypeNodeLinks, ValueSymbolLinks, signatures::SignatureFlags, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(8_310);
const DECLARATIONS: &str = concat!(
    "function id<T>(x: T) { return x; }\n",
    "function bounded<T extends string>(x: T) { return x; }\n",
    "function discard<T>(x: T) { const copy: T = x; }\n",
);

#[derive(Clone, Copy)]
struct FunctionParts {
    declaration: NodeRef,
    name: NodeRef,
    type_parameter: NodeRef,
    type_parameter_name: NodeRef,
    constraint: Option<NodeRef>,
    parameter: NodeRef,
    parameter_name: NodeRef,
    parameter_type: NodeRef,
    returned: Option<NodeRef>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FunctionIdentity {
    owner: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    type_parameter_owner: SemanticSymbolId,
    type_parameter: TypeId,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
    parameter: SemanticSymbolId,
    returned: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CallIdentity {
    signature: SignatureId,
    mapper: TypeMapperId,
    parameter: SemanticSymbolId,
    returned: TypeId,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 5],
    nodes: Vec<(
        NodeRef,
        Option<TypeNodeLinks>,
        Option<SymbolNodeLinks>,
        Option<SignatureLinks>,
    )>,
    symbols: Vec<(
        SemanticSymbolId,
        Option<ValueSymbolLinks>,
        Option<DeclaredTypeLinks>,
    )>,
    source: Option<SourceFileLinks>,
}

fn node_ref(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-function-returns.ts\""),
                CanonicalSourceLanguage::TypeScript,
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
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn function_parts(parsed: &ParseResult, expected: &str) -> FunctionParts {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            if identifier.text != expected {
                return None;
            }
            assert_eq!(function.type_, None, "the return must remain inferred");
            let [type_parameter] = function.type_parameters.as_ref().unwrap().nodes.as_slice()
            else {
                panic!("expected one owned type parameter")
            };
            let NodeData::TypeParameterDeclaration(type_parameter_data) =
                &parsed.arena.get(*type_parameter).unwrap().data
            else {
                panic!("expected the actual type parameter")
            };
            let [parameter] = function.parameters.nodes.as_slice() else {
                panic!("expected one value parameter")
            };
            let NodeData::ParameterDeclaration(parameter_data) =
                &parsed.arena.get(*parameter).unwrap().data
            else {
                panic!("expected the actual value parameter")
            };
            let NodeData::Block(body) = &parsed.arena.get(function.body.unwrap()).unwrap().data
            else {
                panic!("expected a real function body")
            };
            assert!(!body.statements.nodes.is_empty());
            let returned = body.statements.nodes.iter().find_map(|statement| {
                let NodeData::ReturnStatement(returned) =
                    &parsed.arena.get(*statement).unwrap().data
                else {
                    return None;
                };
                returned.expression.map(|node| node_ref(parsed, node))
            });
            Some(FunctionParts {
                declaration: node_ref(parsed, node),
                name: node_ref(parsed, name),
                type_parameter: node_ref(parsed, *type_parameter),
                type_parameter_name: node_ref(parsed, type_parameter_data.name),
                constraint: type_parameter_data
                    .constraint
                    .map(|node| node_ref(parsed, node)),
                parameter: node_ref(parsed, *parameter),
                parameter_name: node_ref(parsed, parameter_data.name),
                parameter_type: node_ref(parsed, parameter_data.type_.unwrap()),
                returned,
            })
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
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
                    node_ref(parsed, node),
                    node_ref(parsed, variable.name),
                    node_ref(parsed, variable.initializer.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the source must publish the value type")
}

// Read producer state before public queries can complete a missing result.
#[allow(clippy::too_many_lines)]
fn function_identity(
    context: &CanonicalCheckerContext<'_>,
    parts: FunctionParts,
) -> FunctionIdentity {
    let store = context.store();
    let owner = symbol(context, parts.declaration);
    let owner_record = store.symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[parts.declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(parts.declaration));
    let type_parameter_owner = symbol(context, parts.type_parameter);
    let parameter = symbol(context, parts.parameter);
    assert_ne!(owner, type_parameter_owner);
    assert_ne!(owner, parameter);
    assert_ne!(type_parameter_owner, parameter);
    let type_parameter = store
        .declared_type_links(type_parameter_owner)
        .and_then(|links| links.declared_type)
        .unwrap();
    let record = store.type_payload(type_parameter).unwrap();
    assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(record.symbol(), Some(type_parameter_owner));
    let TypeData::TypeParameter(data) = record.data() else {
        panic!("the return must use the function's real type parameter")
    };
    assert!(!data.is_this_type);
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    let constraint = data.constraint;
    let default = data.resolved_default_type;
    assert_eq!(value_type(context, parameter), type_parameter);
    assert_eq!(cached_type(context, parts.parameter_type), type_parameter);
    assert_eq!(
        store
            .symbol_node_links(parts.parameter_type)
            .unwrap()
            .resolved_symbol,
        Some(type_parameter_owner)
    );
    let signature = store
        .signature_links(parts.declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let signature_record = store.signature(signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(parts.declaration));
    assert_eq!(signature_record.type_parameters(), &[type_parameter]);
    assert_eq!(signature_record.parameters(), &[parameter]);
    assert_eq!(signature_record.flags(), SignatureFlags::NONE);
    assert_eq!(signature_record.min_argument_count(), 1);
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    let returned = signature_record.resolved_return_type().unwrap();
    if let Some(expression) = parts.returned {
        assert_eq!(returned, type_parameter);
        assert_eq!(cached_type(context, expression), type_parameter);
        assert_eq!(
            store.symbol_node_links(expression).unwrap().resolved_symbol,
            Some(parameter)
        );
    } else {
        assert_eq!(returned, store.intrinsic_bootstrap().unwrap().void_type);
    }
    let callable = value_type(context, owner);
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the function must retain its callable object")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(object.target, None);
    assert_eq!(object.mapper, None);
    FunctionIdentity {
        owner,
        callable,
        signature,
        type_parameter_owner,
        type_parameter,
        constraint,
        default,
        parameter,
        returned,
    }
}

fn function_queries(
    context: &mut CanonicalCheckerContext<'_>,
    parts: FunctionParts,
    expected: FunctionIdentity,
) {
    for node in [parts.declaration, parts.name] {
        assert_eq!(context.get_type_at_location(node), Ok(expected.callable));
    }
    assert_eq!(
        context.get_symbol_at_location(parts.name),
        Ok(Some(expected.owner))
    );
    assert_eq!(
        context.get_symbol_declarations(expected.owner).unwrap(),
        [parts.declaration]
    );
    for (node, type_, owner) in [
        (
            parts.type_parameter_name,
            expected.type_parameter,
            expected.type_parameter_owner,
        ),
        (
            parts.parameter_name,
            expected.type_parameter,
            expected.parameter,
        ),
    ] {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
        assert_eq!(context.get_symbol_at_location(node), Ok(Some(owner)));
    }
    assert_eq!(
        context.get_type_from_type_node(parts.parameter_type),
        Ok(expected.type_parameter)
    );
    if let Some(constraint) = parts.constraint {
        assert_eq!(
            context.get_type_from_type_node(constraint),
            Ok(expected.constraint.unwrap())
        );
    }
    assert_eq!(
        context.get_return_type_of_signature(expected.signature),
        Ok(expected.returned)
    );
    if let Some(expression) = parts.returned {
        assert_eq!(
            context.get_type_at_location(expression),
            Ok(expected.returned)
        );
        assert_eq!(
            context.get_symbol_at_location(expression),
            Ok(Some(expected.parameter))
        );
    }
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = node_ref(parsed, node);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                )
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
    }
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[allow(clippy::too_many_arguments)] // Keep the original signature and its actual call together.
fn call_identity(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    parts: FunctionParts,
    function: FunctionIdentity,
    argument: TypeId,
    returned: TypeId,
) -> CallIdentity {
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected an explicit generic call")
    };
    let [type_argument] = call_data.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("each call must keep its explicit type argument")
    };
    let callee = node_ref(parsed, call_data.expression);
    assert_eq!(cached_type(context, call), returned);
    assert_eq!(cached_type(context, callee), function.callable);
    let store = context.store();
    assert_eq!(
        store.symbol_node_links(callee).unwrap().resolved_symbol,
        Some(function.owner)
    );
    let signature = store
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let selected = store.signature(signature).unwrap();
    assert_eq!(selected.declaration(), Some(parts.declaration));
    assert_eq!(selected.target(), Some(function.signature));
    assert!(selected.type_parameters().is_empty());
    assert_eq!(selected.resolved_return_type(), Some(returned));
    let mapper = selected.mapper().unwrap();
    assert_eq!(
        store.map_type(mapper, function.type_parameter),
        Some(argument)
    );
    let [parameter] = selected.parameters() else {
        panic!("the call must retain its one parameter proxy")
    };
    let parameter = *parameter;
    assert_ne!(parameter, function.parameter);
    let links = store.value_symbol_links(parameter).unwrap();
    assert_eq!(links.target, Some(function.parameter));
    assert_eq!(links.mapper, Some(mapper));
    assert_eq!(links.resolved_type, Some(argument));
    assert_eq!(
        store.symbol(parameter).unwrap().declarations(),
        Some(&[parts.parameter][..])
    );
    assert_eq!(
        context.get_type_from_type_node(node_ref(parsed, *type_argument)),
        Ok(argument)
    );
    assert_eq!(context.get_type_at_location(call), Ok(returned));
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(returned)
    );
    assert_eq!(
        context.get_symbol_at_location(callee),
        Ok(Some(function.owner))
    );
    CallIdentity {
        signature,
        mapper,
        parameter,
        returned,
    }
}

#[test]
fn generic_function_returns_keep_owned_parameters_and_a_nonempty_void_body() {
    for query_first in [false, true] {
        let parsed = parse_source_file(DECLARATIONS);
        let parts = ["id", "bounded", "discard"].map(|name| function_parts(&parsed, name));
        let mut context = context(&parsed);
        assert!(!is_type_checked(&context));
        for function in parts {
            assert!(
                context
                    .store()
                    .signature_links(function.declaration)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .value_symbol_links(symbol(&context, function.declaration))
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .declared_type_links(symbol(&context, function.type_parameter))
                    .is_none()
            );
        }
        let first = query_first.then(|| context.get_type_at_location(parts[0].name).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(is_type_checked(&context));
        assert!(context.diagnostics().is_empty());
        let identities = parts.map(|parts| function_identity(&context, parts));
        assert!(first.is_none_or(|first| first == identities[0].callable));
        for (index, identity) in identities.iter().enumerate() {
            assert!(
                identities[..index]
                    .iter()
                    .all(|earlier| earlier.type_parameter != identity.type_parameter)
            );
        }
        assert_eq!(
            identities[1].constraint,
            Some(context.store().intrinsic_bootstrap().unwrap().string_type)
        );
        let (copy, copy_name, copy_read) = variable(&parsed, "copy");
        assert_eq!(
            value_type(&context, symbol(&context, copy)),
            identities[2].type_parameter
        );
        assert_eq!(
            cached_type(&context, copy_read),
            identities[2].type_parameter
        );
        for (parts, identity) in parts.into_iter().zip(identities) {
            function_queries(&mut context, parts, identity);
        }
        assert_eq!(
            context.get_type_at_location(copy_name),
            Ok(identities[2].type_parameter)
        );
        let warm = publication(&context, &parsed);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for (parts, identity) in parts.into_iter().zip(identities) {
                assert_eq!(function_identity(&context, parts), identity);
                function_queries(&mut context, parts, identity);
            }
            assert_eq!(publication(&context, &parsed), warm);
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
fn explicit_generic_calls_use_the_inferred_return_and_original_signature() {
    let source = format!(
        "const before = id<string>(\"before\");\n{DECLARATIONS}\nconst after = id<number>(1);\nconst boundedResult = bounded<string>(\"ok\");\nconst discarded = discard<number>(2);\n"
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(&source);
        let parts = ["id", "bounded", "discard"].map(|name| function_parts(&parsed, name));
        let mut context = context(&parsed);
        let before = variable(&parsed, "before").2;
        let first = query_first.then(|| context.get_type_at_location(before).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let identities = parts.map(|parts| function_identity(&context, parts));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        assert!(first.is_none_or(|first| first == string));
        let calls = [
            ("before", 0, string, string),
            ("after", 0, number, number),
            ("boundedResult", 1, string, string),
            ("discarded", 2, number, void),
        ];
        let mut selected = Vec::new();
        for (name, index, argument, returned) in calls {
            let (declaration, _, call) = variable(&parsed, name);
            assert_eq!(
                value_type(&context, symbol(&context, declaration)),
                returned
            );
            selected.push(call_identity(
                &mut context,
                &parsed,
                call,
                parts[index],
                identities[index],
                argument,
                returned,
            ));
        }
        assert_ne!(selected[0].signature, selected[1].signature);
        for (parts, identity) in parts.into_iter().zip(identities) {
            function_queries(&mut context, parts, identity);
        }
        let warm = publication(&context, &parsed);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for ((name, index, argument, returned), expected) in calls.into_iter().zip(&selected) {
                assert_eq!(
                    call_identity(
                        &mut context,
                        &parsed,
                        variable(&parsed, name).2,
                        parts[index],
                        identities[index],
                        argument,
                        returned
                    ),
                    *expected
                );
            }
            for (parts, identity) in parts.into_iter().zip(identities) {
                assert_eq!(function_identity(&context, parts), identity);
                function_queries(&mut context, parts, identity);
            }
            assert_eq!(publication(&context, &parsed), warm);
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
fn generic_body_diagnostics_do_not_replace_the_inferred_return() {
    let parsed = parse_source_file(concat!(
        "function broken<T>(x: T) { const bad: string = 1; return x; }\n",
        "const result: number = broken<number>(2);\n",
    ));
    let parts = function_parts(&parsed, "broken");
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(is_type_checked(&context));
    let identity = function_identity(&context, parts);
    let bad = variable(&parsed, "bad").1;
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected only the bad local assignment diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(bad));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    assert!(diagnostic.related_information.is_empty());
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let call = variable(&parsed, "result").2;
    let selected = call_identity(&mut context, &parsed, call, parts, identity, number, number);
    function_queries(&mut context, parts, identity);
    let diagnostics = context.diagnostics().clone();
    let warm = publication(&context, &parsed);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(function_identity(&context, parts), identity);
        assert_eq!(
            call_identity(&mut context, &parsed, call, parts, identity, number, number),
            selected
        );
        function_queries(&mut context, parts, identity);
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(publication(&context, &parsed), warm);
    }
}
