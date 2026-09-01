use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, NodeLinks, SignatureId, SignatureLinks, SourceCheckError,
    SourceFileLinks, SourceFunctionUnsupported, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    UnsupportedSourceSyntax, ValueSymbolLinks, signatures::TypePredicateKind,
    type_records::LiteralValue, types::TypeFlags,
};
use ts_jsnum::Number;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(58_510);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/callable-statements.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            )
            .with_always_strict(true),
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
            no_implicit_any: true,
            strict_function_types: true,
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

#[derive(Clone, Copy)]
struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: NodeRef,
}

fn bindings(parsed: &ParseResult, expected: &str) -> Vec<Binding> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            let declaration = node(parsed, id);
            Some(Binding {
                declaration,
                name: child(parsed, declaration, variable.name),
                annotation: variable.type_.map(|id| child(parsed, declaration, id)),
                initializer: child(parsed, declaration, variable.initializer.unwrap()),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|binding| {
        parsed
            .arena
            .get(binding.declaration.node)
            .unwrap()
            .range
            .start
            .get()
    });
    result
}

fn binding(parsed: &ParseResult, expected: &str) -> Binding {
    let result = bindings(parsed, expected);
    let [result] = result.as_slice() else {
        panic!("expected one binding named {expected}");
    };
    *result
}

struct Callable {
    declaration: NodeRef,
    name: NodeRef,
    binding: Option<NodeRef>,
    body: NodeRef,
    annotation: Option<NodeRef>,
    parameters: Vec<NodeRef>,
}

fn callable(parsed: &ParseResult, expected: &str) -> Callable {
    let mut functions = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
            return None;
        };
        (name.text == expected).then_some((node(parsed, id), function))
    });
    if let Some((declaration, function)) = functions.next() {
        assert!(functions.next().is_none());
        return Callable {
            declaration,
            name: child(parsed, declaration, function.name.unwrap()),
            binding: None,
            body: child(parsed, declaration, function.body.unwrap()),
            annotation: function.type_.map(|id| child(parsed, declaration, id)),
            parameters: function
                .parameters
                .nodes
                .iter()
                .map(|&id| child(parsed, declaration, id))
                .collect(),
        };
    }
    let binding = binding(parsed, expected);
    let declaration = binding.initializer;
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(declaration.node).unwrap().data else {
        panic!("the stored callable must be the actual arrow");
    };
    Callable {
        declaration,
        name: binding.name,
        binding: Some(binding.declaration),
        body: child(parsed, declaration, arrow.body),
        annotation: arrow.type_.map(|id| child(parsed, declaration, id)),
        parameters: arrow
            .parameters
            .nodes
            .iter()
            .map(|&id| child(parsed, declaration, id))
            .collect(),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
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

#[derive(Debug, Eq, PartialEq)]
struct CallableState {
    owner: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the source owner, parameters, and return as one callable.
fn callable_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callable: &Callable,
) -> CallableState {
    let owner = symbol(checker, callable.declaration);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(
        owner_record.declarations(),
        Some(&[callable.declaration][..])
    );
    assert_eq!(owner_record.value_declaration(), Some(callable.declaration));
    let type_ = checker.get_type_at_location(callable.declaration).unwrap();
    assert_eq!(value_type(checker, owner), type_);
    assert_eq!(checker.get_type_at_location(callable.name), Ok(type_));
    if let Some(binding) = callable.binding {
        let binding_owner = symbol(checker, binding);
        assert_ne!(binding_owner, owner);
        assert_eq!(value_type(checker, binding_owner), type_);
        assert_eq!(
            checker.get_symbol_at_location(callable.name),
            Ok(Some(binding_owner))
        );
    } else {
        assert_eq!(
            checker.get_symbol_at_location(callable.name),
            Ok(Some(owner))
        );
    }
    let signature = signature(checker, callable.declaration);
    let type_record = checker.store().type_payload(type_).unwrap();
    assert_eq!(type_record.symbol(), Some(owner));
    let TypeData::Object(object) = type_record.data() else {
        panic!("the callable must keep its source object type");
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let parameters = callable
        .parameters
        .iter()
        .map(|&declaration| {
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the actual parameter declaration");
            };
            let owner = symbol(checker, declaration);
            let name = child(parsed, declaration, parameter.name);
            let type_ = checker.get_type_at_location(name).unwrap();
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
            assert_eq!(value_type(checker, owner), type_);
            assert_eq!(
                checker.get_type_from_type_node(child(
                    parsed,
                    declaration,
                    parameter.type_.unwrap()
                )),
                Ok(type_)
            );
            (owner, type_)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(callable.declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(owner, _)| owner)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert!(record.type_parameters().is_empty());
    assert!(!record.has_rest_parameter());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    if let Some(annotation) = callable.annotation {
        assert_eq!(checker.get_type_from_type_node(annotation), Ok(returned));
    }
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(bound.container(callable.body), Some(callable.declaration));
    assert_eq!(
        bound
            .flow_graph()
            .container_is_complete(callable.declaration),
        Some(true)
    );
    CallableState {
        owner,
        type_,
        signature,
        parameters,
        returned,
    }
}

fn checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Clone, Copy)]
enum QueryOrder {
    Source,
    Callable,
    BodyRead,
}

fn start(
    checker: &mut CanonicalCheckerContext<'_>,
    callable: &Callable,
    read: NodeRef,
    order: QueryOrder,
) {
    assert!(!checked(checker));
    assert!(
        checker
            .store()
            .signature_links(callable.declaration)
            .is_none()
    );
    let first = match order {
        QueryOrder::Source => None,
        QueryOrder::Callable => Some(callable.declaration),
        QueryOrder::BodyRead => Some(read),
    }
    .map(|location| (location, checker.get_type_at_location(location).unwrap()));
    checker.check_source_file(FILE).unwrap();
    assert!(checked(checker));
    assert_eq!(checker.store().type_resolution_len(), 0);
    if let Some((location, type_)) = first {
        assert_eq!(checker.get_type_at_location(location), Ok(type_));
    }
}

fn read(
    checker: &mut CanonicalCheckerContext<'_>,
    location: NodeRef,
    owner: SemanticSymbolId,
    type_: TypeId,
) {
    assert_eq!(checker.get_type_at_location(location), Ok(type_));
    assert_eq!(checker.get_symbol_at_location(location), Ok(Some(owner)));
}

fn return_sites(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callable: &Callable,
) -> Vec<(NodeRef, Option<NodeRef>)> {
    let (_, bound) = checker.file(FILE).unwrap();
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::ReturnStatement(returned) = &record.data else {
                return None;
            };
            let statement = node(parsed, id);
            if bound.container(statement) != Some(callable.declaration) {
                return None;
            }
            assert_eq!(bound.flow_container(statement), Some(callable.declaration));
            assert!(bound.flow_at(statement).is_some());
            Some((
                statement,
                returned.expression.map(|id| child(parsed, statement, id)),
            ))
        })
        .collect::<Vec<_>>();
    result
        .sort_by_key(|&(statement, _)| parsed.arena.get(statement.node).unwrap().range.start.get());
    result
}

fn text_at<'source>(source: &'source str, parsed: &ParseResult, location: NodeRef) -> &'source str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    common: Option<NodeLinks>,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = checker.store();
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.type_resolution_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                NodeState {
                    node,
                    common: store.node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
            })
            .collect(),
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callables: &[&Callable],
    locations: &[NodeRef],
) {
    let states = callables
        .iter()
        .map(|callable| callable_state(checker, parsed, callable))
        .collect::<Vec<_>>();
    let queries = locations
        .iter()
        .map(|&location| {
            (
                location,
                checker.get_type_at_location(location).unwrap(),
                checker.get_symbol_at_location(location).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let before = publication(checker, parsed);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        for (callable, state) in callables.iter().zip(&states) {
            assert_eq!(&callable_state(checker, parsed, callable), state);
        }
        for &(location, type_, owner) in &queries {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(location), Ok(owner));
        }
        assert_eq!(publication(checker, parsed), before);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the shared bodies and ordinary predicate results together.
fn functions_and_stored_arrows_share_local_early_return_and_continuation_flow() {
    let body = concat!(
        "  const entry = value;\n",
        "  if (entry === undefined) { return 'missing'; }\n",
        "  const selected: string = entry;\n",
        "  consume(selected);\n",
        "  ;\n",
        "  return selected;\n",
    );
    for source in [
        format!(
            "function consume(value: string): void {{}}\nfunction select(value: string | undefined): string {{\n{body}}}\nconst answer = select(undefined);"
        ),
        format!(
            "function consume(value: string): void {{}}\nconst select = (value: string | undefined): string => {{\n{body}}};\nconst answer = select(undefined);"
        ),
    ] {
        let parsed = parse_source_file(&source);
        let consume = callable(&parsed, "consume");
        let select = callable(&parsed, "select");
        let entry = binding(&parsed, "entry");
        let selected = binding(&parsed, "selected");
        let answer = binding(&parsed, "answer");
        let consumed = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::CallExpression(call) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(call.expression)?.data else {
                    return None;
                };
                (name.text == "consume").then_some(node(&parsed, id))
            })
            .unwrap();
        for order in [
            QueryOrder::Source,
            QueryOrder::Callable,
            QueryOrder::BodyRead,
        ] {
            let mut checker = context(&parsed);
            start(&mut checker, &select, selected.initializer, order);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let state = callable_state(&mut checker, &parsed, &select);
            let consume_state = callable_state(&mut checker, &parsed, &consume);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let string = bootstrap.string_type;
            let void = bootstrap.void_type;
            assert_eq!(state.returned, string);
            assert_eq!(consume_state.returned, void);
            assert_eq!(state.parameters.len(), 1);
            let (parameter, declared) = state.parameters[0];
            assert_eq!(
                checker.type_to_string(declared).unwrap(),
                "string | undefined"
            );
            read(&mut checker, entry.initializer, parameter, declared);
            let entry_owner = symbol(&checker, entry.declaration);
            read(&mut checker, selected.initializer, entry_owner, string);
            assert_eq!(value_type(&checker, entry_owner), declared);
            let selected_owner = symbol(&checker, selected.declaration);
            let returns = return_sites(&checker, &parsed, &select);
            assert_eq!(returns.len(), 2);
            read(&mut checker, returns[1].1.unwrap(), selected_owner, string);
            assert_eq!(checker.get_type_at_location(answer.initializer), Ok(string));
            assert_eq!(signature(&checker, answer.initializer), state.signature);
            assert_eq!(checker.get_type_at_location(answer.name), Ok(string));
            assert_eq!(checker.get_type_at_location(consumed), Ok(void));
            assert_eq!(signature(&checker, consumed), consume_state.signature);
            let (_, bound) = checker.file(FILE).unwrap();
            assert_ne!(bound.flow_at(returns[0].0), bound.flow_at(returns[1].0));
            assert_eq!(bound.flow_graph().container_end(select.declaration), None);
            replay(
                &mut checker,
                &parsed,
                &[&select, &consume],
                &[
                    entry.initializer,
                    selected.initializer,
                    returns[1].1.unwrap(),
                    answer.initializer,
                    consumed,
                ],
            );
        }
    }
    for header in [
        "function readValue(value: unknown): boolean",
        "const readValue = (value: unknown): boolean =>",
    ] {
        let source = format!(
            "declare function isText(value: unknown): value is string;\n{header} {{ const result = isText(value); return result; }};"
        );
        let parsed = parse_source_file(&source);
        let reader = callable(&parsed, "readValue");
        let result = binding(&parsed, "result");
        let provider = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
                    return None;
                };
                (name.text == "isText").then_some(node(&parsed, id))
            })
            .unwrap();
        for order in [
            QueryOrder::Source,
            QueryOrder::Callable,
            QueryOrder::BodyRead,
        ] {
            let mut checker = context(&parsed);
            start(&mut checker, &reader, result.initializer, order);
            assert!(checker.diagnostics().is_empty());
            let state = callable_state(&mut checker, &parsed, &reader);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let boolean = bootstrap.boolean_type;
            let unknown = bootstrap.unknown_type;
            let string = bootstrap.string_type;
            assert_eq!(state.returned, boolean);
            assert_eq!(state.parameters[0].1, unknown);
            assert_eq!(
                checker.get_type_at_location(result.initializer),
                Ok(boolean)
            );
            let provider_signature = signature(&checker, provider);
            assert_eq!(signature(&checker, result.initializer), provider_signature);
            let record = checker.store().signature(provider_signature).unwrap();
            assert_eq!(record.declaration(), Some(provider));
            assert_eq!(record.resolved_return_type(), Some(boolean));
            let predicate_id = record.resolved_type_predicate().unwrap();
            let predicate = checker.store().type_predicate(predicate_id).unwrap();
            assert_eq!(predicate.kind(), TypePredicateKind::Identifier);
            assert_eq!(predicate.parameter_index(), 0);
            assert_eq!(predicate.parameter_name(), "value");
            assert_eq!(predicate.type_id(), Some(string));
            let result_owner = symbol(&checker, result.declaration);
            assert_eq!(value_type(&checker, result_owner), boolean);
            let returns = return_sites(&checker, &parsed, &reader);
            assert_eq!(returns.len(), 1);
            let returned = returns[0].1.unwrap();
            read(&mut checker, returned, result_owner, boolean);
            let predicate_count = checker.store().type_predicate_len();
            replay(
                &mut checker,
                &parsed,
                &[&reader],
                &[result.initializer, returned],
            );
            assert_eq!(checker.store().type_predicate_len(), predicate_count);
            assert_eq!(
                checker
                    .store()
                    .signature(provider_signature)
                    .unwrap()
                    .resolved_type_predicate(),
                Some(predicate_id)
            );
        }
    }
}

#[test]
fn repeated_early_returns_keep_each_exit_and_the_surviving_local_flow() {
    let body = concat!(
        "  const entry = value;\n",
        "  if (entry === undefined) { return 1; }\n",
        "  const selected: string = entry;\n",
        "  if (stop) { return false; }\n",
        "  const result: string = selected;\n",
        "  return result;\n",
    );
    for source in [
        format!("function select(value: string | undefined, stop: boolean) {{\n{body}}}"),
        format!("const select = (value: string | undefined, stop: boolean) => {{\n{body}}};"),
    ] {
        let parsed = parse_source_file(&source);
        let select = callable(&parsed, "select");
        let selected = binding(&parsed, "selected");
        let result = binding(&parsed, "result");
        for order in [
            QueryOrder::Source,
            QueryOrder::Callable,
            QueryOrder::BodyRead,
        ] {
            let mut checker = context(&parsed);
            start(&mut checker, &select, result.initializer, order);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let state = callable_state(&mut checker, &parsed, &select);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let string = bootstrap.string_type;
            let undefined = bootstrap.undefined_type;
            let number = bootstrap.number_type;
            let selected_owner = symbol(&checker, selected.declaration);
            read(&mut checker, result.initializer, selected_owner, string);
            let entry_owner = symbol(&checker, binding(&parsed, "entry").declaration);
            read(&mut checker, selected.initializer, entry_owner, string);
            let returns = return_sites(&checker, &parsed, &select);
            assert_eq!(returns.len(), 3);
            let expressions = returns
                .iter()
                .map(|&(_, expression)| expression.unwrap())
                .collect::<Vec<_>>();
            let returned = expressions
                .iter()
                .map(|&expression| checker.get_type_at_location(expression).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(returned[2], string);
            let record = checker.store().type_payload(returned[0]).unwrap();
            assert_eq!(record.flags(), TypeFlags::NUMBER_LITERAL);
            let TypeData::Literal(literal) = record.data() else {
                panic!("the first exit must keep the real numeric literal");
            };
            assert_eq!(literal.value, LiteralValue::Number(Number::new(1.0)));
            assert_eq!(checker.type_to_string(returned[1]).unwrap(), "false");
            let TypeData::Union(union) =
                checker.store().type_payload(state.returned).unwrap().data()
            else {
                panic!("all three exit types must contribute to the inferred return");
            };
            assert_eq!(union.union.types.len(), 3);
            for type_ in returned {
                assert!(union.union.types.contains(&type_));
            }
            assert!(!union.union.types.contains(&undefined));
            assert!(!union.union.types.contains(&number));
            let (_, bound) = checker.file(FILE).unwrap();
            let flows = returns
                .iter()
                .map(|&(statement, _)| bound.flow_at(statement).unwrap())
                .collect::<Vec<_>>();
            for (index, flow) in flows.iter().enumerate() {
                assert!(!flows[..index].contains(flow));
            }
            assert_eq!(bound.flow_graph().container_end(select.declaration), None);
            replay(
                &mut checker,
                &parsed,
                &[&select],
                &[
                    selected.initializer,
                    result.initializer,
                    expressions[0],
                    expressions[1],
                    expressions[2],
                ],
            );
        }
    }
}

#[test]
fn nested_conditions_restore_each_block_scope_before_siblings_and_continuation() {
    let source = concat!(
        "function scoped(first: boolean, second: boolean, text: string, count: number): string {\n",
        "  const shadow: string = text;\n",
        "  if (first) {\n",
        "    const shadow: number = count;\n",
        "    if (second) {\n",
        "      const shadow: string = text;\n",
        "      const deep: string = shadow;\n",
        "      return deep;\n",
        "    }\n",
        "    const thenRead: number = shadow;\n",
        "  } else if (second) {\n",
        "    const shadow: number = count;\n",
        "    const middleRead: number = shadow;\n",
        "  } else {\n",
        "    const shadow: string = text;\n",
        "    const elseRead: string = shadow;\n",
        "  }\n",
        "  const after: string = shadow;\n",
        "  return after;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let scoped = callable(&parsed, "scoped");
    let shadows = bindings(&parsed, "shadow");
    assert_eq!(shadows.len(), 5);
    let reads = ["after", "thenRead", "deep", "middleRead", "elseRead"]
        .map(|name| binding(&parsed, name).initializer);
    for order in [
        QueryOrder::Source,
        QueryOrder::Callable,
        QueryOrder::BodyRead,
    ] {
        let mut checker = context(&parsed);
        start(&mut checker, &scoped, reads[0], order);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let state = callable_state(&mut checker, &parsed, &scoped);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let expected = [
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.string_type,
        ];
        assert_eq!(state.returned, expected[0]);
        let owners = shadows
            .iter()
            .map(|binding| symbol(&checker, binding.declaration))
            .collect::<Vec<_>>();
        for (index, owner) in owners.iter().enumerate() {
            assert!(!owners[..index].contains(owner));
        }
        for (index, shadow) in shadows.iter().enumerate() {
            read(&mut checker, reads[index], owners[index], expected[index]);
            assert_eq!(value_type(&checker, owners[index]), expected[index]);
            let (_, bound) = checker.file(FILE).unwrap();
            assert_eq!(
                bound.container(shadow.declaration),
                Some(scoped.declaration)
            );
            assert_eq!(
                bound.block_scope_container(reads[index]),
                bound.block_scope_container(shadow.declaration)
            );
        }
        let (_, bound) = checker.file(FILE).unwrap();
        let scopes = shadows
            .iter()
            .map(|binding| bound.block_scope_container(binding.declaration).unwrap())
            .collect::<Vec<_>>();
        for (index, scope) in scopes.iter().enumerate() {
            assert!(!scopes[..index].contains(scope));
        }
        let returns = return_sites(&checker, &parsed, &scoped);
        assert_eq!(returns.len(), 2);
        assert_eq!(bound.flow_graph().container_end(scoped.declaration), None);
        replay(&mut checker, &parsed, &[&scoped], &reads);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the strict return types and ordered return errors together.
fn bare_and_implicit_exits_keep_undefined_and_annotation_errors_keep_source_order() {
    let source = concat!(
        "function bare(flag: boolean) {\n",
        "  const entry = flag;\n",
        "  if (entry) { return 1; }\n",
        "  return;\n",
        "}\n",
        "const implicit = (flag: boolean) => {\n",
        "  const entry = flag;\n",
        "  if (entry) { return 1; }\n",
        "  const after = entry;\n",
        "};\n",
        "function annotated(first: boolean, second: boolean): number {\n",
        "  const entry = first;\n",
        "  if (entry) { return 'left'; } else if (second) { return; }\n",
        "  const later = second;\n",
        "  return false;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let bare = callable(&parsed, "bare");
    let implicit = callable(&parsed, "implicit");
    let annotated = callable(&parsed, "annotated");
    let after = binding(&parsed, "after");
    for order in [
        QueryOrder::Source,
        QueryOrder::Callable,
        QueryOrder::BodyRead,
    ] {
        let mut checker = context(&parsed);
        start(&mut checker, &implicit, after.initializer, order);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let undefined = bootstrap.undefined_type;
        let number = bootstrap.number_type;
        let void = bootstrap.void_type;
        let mut locations = vec![after.initializer];
        let mut inferred = Vec::new();
        for callable in [&bare, &implicit] {
            let state = callable_state(&mut checker, &parsed, callable);
            let returns = return_sites(&checker, &parsed, callable);
            let expression = returns[0].1.unwrap();
            let literal_type = checker.get_type_at_location(expression).unwrap();
            let record = checker.store().type_payload(literal_type).unwrap();
            assert_eq!(record.flags(), TypeFlags::NUMBER_LITERAL);
            let TypeData::Literal(literal) = record.data() else {
                panic!("the written return must remain the numeric literal");
            };
            assert_eq!(literal.value, LiteralValue::Number(Number::new(1.0)));
            let TypeData::Union(union) =
                checker.store().type_payload(state.returned).unwrap().data()
            else {
                panic!("a value exit and an empty exit must keep their union");
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&literal_type));
            assert!(union.union.types.contains(&undefined));
            assert!(!union.union.types.contains(&number));
            assert!(!union.union.types.contains(&void));
            assert_eq!(
                checker.type_to_string(state.returned).unwrap(),
                "1 | undefined"
            );
            assert_eq!(
                checker.is_type_assignable_to(number, state.returned),
                Ok(false)
            );
            inferred.push(state.returned);
            locations.push(expression);
        }
        assert_eq!(inferred[0], inferred[1]);
        let bare_returns = return_sites(&checker, &parsed, &bare);
        assert_eq!(bare_returns.len(), 2);
        assert_eq!(bare_returns[1].1, None);
        let (_, bound) = checker.file(FILE).unwrap();
        assert_eq!(bound.flow_graph().container_end(bare.declaration), None);
        assert!(
            bound
                .flow_graph()
                .container_end(implicit.declaration)
                .is_some()
        );
        let annotated_state = callable_state(&mut checker, &parsed, &annotated);
        assert_eq!(annotated_state.returned, number);
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
        for (diagnostic, (text, message)) in diagnostics.iter().zip([
            (
                "return 'left';",
                "Type 'string' is not assignable to type 'number'.",
            ),
            (
                "return;",
                "Type 'undefined' is not assignable to type 'number'.",
            ),
            (
                "return false;",
                "Type 'boolean' is not assignable to type 'number'.",
            ),
        ]) {
            let location = diagnostic.node.unwrap();
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                parsed.arena.get(location.node).unwrap().kind,
                SyntaxKind::ReturnStatement
            );
            assert_eq!(text_at(source, &parsed, location), text);
            assert_eq!(
                checker.file(FILE).unwrap().1.container(location),
                Some(annotated.declaration)
            );
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
        }
        replay(
            &mut checker,
            &parsed,
            &[&bare, &implicit, &annotated],
            &locations,
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare the child write, outer read, and const read in one source.
fn local_callbacks_keep_mutable_entry_types_deferred_writes_and_narrowed_const_reads() {
    let source = concat!(
        "function factory(): void {\n",
        "  let value: string | undefined = 'ready';\n",
        "  const readValue = (): string | undefined => {\n",
        "    const readEntry = value;\n",
        "    if (readEntry === undefined) { return undefined; }\n",
        "    const readSelected: string = readEntry;\n",
        "    return readSelected;\n",
        "  };\n",
        "  const cancel = (): void => {\n",
        "    const cancelEntry = value;\n",
        "    if (cancelEntry === undefined) { return; }\n",
        "    const selected: string = cancelEntry;\n",
        "    value = undefined;\n",
        "    const changed: undefined = value;\n",
        "  };\n",
        "  const outside = value;\n",
        "  const stable: string | undefined = 'fixed';\n",
        "  const readStable = (flag: boolean): string => {\n",
        "    const stableEntry = stable;\n",
        "    if (flag) { return stableEntry; }\n",
        "    const stableAfter: string = stable;\n",
        "    return stableAfter;\n",
        "  };\n",
        "  const write = (): void => { value = undefined; };\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let factory = callable(&parsed, "factory");
    let read_value = callable(&parsed, "readValue");
    let cancel = callable(&parsed, "cancel");
    let read_stable = callable(&parsed, "readStable");
    let write = callable(&parsed, "write");
    let value = binding(&parsed, "value");
    let stable = binding(&parsed, "stable");
    let read_entry = binding(&parsed, "readEntry");
    let cancel_entry = binding(&parsed, "cancelEntry");
    let changed = binding(&parsed, "changed");
    let outside = binding(&parsed, "outside");
    let stable_entry = binding(&parsed, "stableEntry");
    let stable_after = binding(&parsed, "stableAfter");
    for order in [
        QueryOrder::Source,
        QueryOrder::Callable,
        QueryOrder::BodyRead,
    ] {
        let mut checker = context(&parsed);
        start(&mut checker, &cancel, cancel_entry.initializer, order);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let undefined = bootstrap.undefined_type;
        let void = bootstrap.void_type;
        let declared = checker
            .get_type_from_type_node(value.annotation.unwrap())
            .unwrap();
        assert_eq!(
            checker.type_to_string(declared).unwrap(),
            "string | undefined"
        );
        let value_owner = symbol(&checker, value.declaration);
        let stable_owner = symbol(&checker, stable.declaration);
        assert_ne!(value_owner, stable_owner);
        assert_eq!(value_type(&checker, value_owner), declared);
        read(&mut checker, read_entry.initializer, value_owner, declared);
        read(
            &mut checker,
            cancel_entry.initializer,
            value_owner,
            declared,
        );
        read(&mut checker, changed.initializer, value_owner, undefined);
        read(&mut checker, outside.initializer, value_owner, string);
        read(&mut checker, stable_entry.initializer, stable_owner, string);
        read(&mut checker, stable_after.initializer, stable_owner, string);
        let read_entry_owner = symbol(&checker, read_entry.declaration);
        let cancel_entry_owner = symbol(&checker, cancel_entry.declaration);
        read(
            &mut checker,
            binding(&parsed, "readSelected").initializer,
            read_entry_owner,
            string,
        );
        read(
            &mut checker,
            binding(&parsed, "selected").initializer,
            cancel_entry_owner,
            string,
        );
        assert_eq!(
            callable_state(&mut checker, &parsed, &factory).returned,
            void
        );
        assert_eq!(
            callable_state(&mut checker, &parsed, &read_value).returned,
            declared
        );
        assert_eq!(
            callable_state(&mut checker, &parsed, &cancel).returned,
            void
        );
        assert_eq!(
            callable_state(&mut checker, &parsed, &read_stable).returned,
            string
        );
        assert_eq!(callable_state(&mut checker, &parsed, &write).returned, void);
        let (_, bound) = checker.file(FILE).unwrap();
        assert_eq!(
            bound.container(value.declaration),
            Some(factory.declaration)
        );
        assert_eq!(
            bound.container(stable.declaration),
            Some(factory.declaration)
        );
        assert_eq!(
            bound.flow_container(outside.initializer),
            Some(factory.declaration)
        );
        assert_eq!(
            bound.flow_container(read_entry.initializer),
            Some(read_value.declaration)
        );
        assert_eq!(
            bound.flow_container(changed.initializer),
            Some(cancel.declaration)
        );
        assert_eq!(
            bound.flow_container(stable_entry.initializer),
            Some(read_stable.declaration)
        );
        replay(
            &mut checker,
            &parsed,
            &[&factory, &read_value, &cancel, &read_stable, &write],
            &[
                read_entry.initializer,
                cancel_entry.initializer,
                changed.initializer,
                outside.initializer,
                stable_entry.initializer,
                stable_after.initializer,
            ],
        );
    }
}

#[test]
fn statement_composition_keeps_unreleased_headers_statements_and_call_effects_rejected() {
    {
        let source = "const run = (flag: boolean): void => { const entry = flag; if (entry) {} try {} catch {} };";
        let parsed = parse_source_file(source);
        let run = callable(&parsed, "run");
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(checked(&checker));
        assert!(checker.diagnostics().is_empty());
        let state = callable_state(&mut checker, &parsed, &run);
        assert_eq!(
            state.returned,
            checker.store().intrinsic_bootstrap().unwrap().void_type
        );
        replay(&mut checker, &parsed, &[&run], &[]);
        assert!(checked(&checker));
    }
    for source in [
        "const run = (flag: boolean): void => { const entry = flag; while (entry) {} };",
        "const run = (flag: boolean): void => { const entry = flag; if (entry); };",
        "const run = <T>(flag: boolean, value: T): T => { const entry = flag; if (entry) { return value; } return value; };",
        "const run = async (flag: boolean) => { const entry = flag; if (entry) { return; } };",
        "const run = (flag: boolean) => { return 1; const later = flag; };",
    ] {
        let parsed = parse_source_file(source);
        let run = callable(&parsed, "run");
        let mut checker = context(&parsed);
        let before = publication(&checker, &parsed);
        let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(run.body));
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(error), "{source}");
            assert_eq!(publication(&checker, &parsed), before);
        }
    }
    let effect_sources = [
        ("declare function effect(): never;", "effect()"),
        (
            "declare function effect(value: boolean): asserts value;",
            "effect(flag)",
        ),
    ]
    .map(|(declaration, call)| {
        format!(
            "{declaration}\nconst run = (flag: boolean) => {{ const entry = flag; if (entry) {{ {call}; }} return 1; }};"
        )
    });
    for source in effect_sources.into_iter().chain([String::from(concat!(
        "declare function effect(value: unknown): value is string;\n",
        "const run = (value: unknown) => { const entry = value; ",
        "if (effect(entry)) { return 2; } return 1; };",
    ))]) {
        let parsed = parse_source_file(&source);
        let run = callable(&parsed, "run");
        let mut checker = context(&parsed);
        let error = checker.check_source_file(FILE).unwrap_err();
        assert_eq!(
            error,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                SourceFunctionUnsupported::FunctionBody(run.body)
            ))
        );
        assert!(!checked(&checker));
        assert_eq!(checker.store().type_resolution_len(), 0);
        let signature = signature(&checker, run.declaration);
        assert_eq!(
            checker
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            None
        );
        assert!(checker.store().type_node_links(run.declaration).is_none());
        let stopped = publication(&checker, &parsed);
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(error));
            assert_eq!(
                checker
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                None
            );
            assert_eq!(publication(&checker, &parsed), stopped);
        }
    }
}
