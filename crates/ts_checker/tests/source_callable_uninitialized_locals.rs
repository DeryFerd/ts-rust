use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalArtifactQueryError, CanonicalCheckerContext, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SourceCheckError, SourceFunctionUnsupported,
    SourceSyntaxRole, TypeData, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(84_210);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/callable-uninitialized-locals.ts\""),
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
                ..IntrinsicBootstrapOptions::default()
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
    assert_eq!(parsed.arena.get(id).unwrap().parent, Some(parent.node));
    node(parsed, id)
}

#[derive(Clone, Copy)]
struct Local {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: Option<NodeRef>,
}

fn locals(parsed: &ParseResult, expected: &str) -> Vec<Local> {
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
            Some(Local {
                declaration,
                name: child(parsed, declaration, variable.name),
                annotation: variable.type_.map(|id| child(parsed, declaration, id)),
                initializer: variable
                    .initializer
                    .map(|id| child(parsed, declaration, id)),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|local| {
        parsed
            .arena
            .get(local.declaration.node)
            .unwrap()
            .range
            .start
            .get()
    });
    result
}

fn local(parsed: &ParseResult, expected: &str) -> Local {
    let result = locals(parsed, expected);
    let [local] = result.as_slice() else {
        panic!("expected one declaration named {expected}");
    };
    *local
}

struct Callable {
    declaration: NodeRef,
    body: NodeRef,
    annotation: Option<NodeRef>,
    storage: Option<NodeRef>,
    parameters: Vec<NodeRef>,
}

fn callable(parsed: &ParseResult) -> Callable {
    let mut functions = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
            return None;
        };
        (name.text == "run").then_some((node(parsed, id), function))
    });
    if let Some((declaration, function)) = functions.next() {
        assert!(functions.next().is_none());
        return Callable {
            declaration,
            body: child(parsed, declaration, function.body.unwrap()),
            annotation: function.type_.map(|id| child(parsed, declaration, id)),
            storage: None,
            parameters: function
                .parameters
                .nodes
                .iter()
                .map(|&id| child(parsed, declaration, id))
                .collect(),
        };
    }
    let storage = local(parsed, "run");
    let declaration = storage.initializer.unwrap();
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(declaration.node).unwrap().data else {
        panic!("expected the real stored arrow");
    };
    Callable {
        declaration,
        body: child(parsed, declaration, arrow.body),
        annotation: arrow.type_.map(|id| child(parsed, declaration, id)),
        storage: Some(storage.declaration),
        parameters: arrow
            .parameters
            .nodes
            .iter()
            .map(|&id| child(parsed, declaration, id))
            .collect(),
    }
}

fn owner(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Debug, Eq, PartialEq)]
struct CallableState {
    owner: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    returned: TypeId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
}

fn callable_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callable: &Callable,
) -> CallableState {
    let owner = owner(checker, callable.declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[callable.declaration][..]));
    assert_eq!(record.value_declaration(), Some(callable.declaration));
    let type_ = checker.get_type_at_location(callable.declaration).unwrap();
    assert_eq!(value_type(checker, owner), type_);
    if let Some(storage) = callable.storage {
        let storage_owner = self::owner(checker, storage);
        assert_ne!(storage_owner, owner);
        assert_eq!(value_type(checker, storage_owner), type_);
    }
    let signature = signature(checker, callable.declaration);
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("expected the callable's real object type");
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
                panic!("expected the actual parameter");
            };
            let symbol = self::owner(checker, declaration);
            let annotation = child(parsed, declaration, parameter.type_.unwrap());
            let type_ = checker.get_type_from_type_node(annotation).unwrap();
            assert_eq!(value_type(checker, symbol), type_);
            (symbol, type_)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(callable.declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(symbol, _)| symbol)
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
        returned,
        parameters,
    }
}

fn absent_local(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callable: &Callable,
    local: Local,
) -> SemanticSymbolId {
    assert!(local.initializer.is_none());
    assert!(local.annotation.is_some());
    let declaration = parsed.arena.get(local.declaration.node).unwrap();
    let NodeData::VariableDeclaration(variable) = &declaration.data else {
        panic!("expected the real local");
    };
    assert!(variable.initializer.is_none());
    assert!(variable.exclamation_token.is_none());
    let list = parsed.arena.get(declaration.parent.unwrap()).unwrap();
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(
        bound.container(local.declaration),
        Some(callable.declaration)
    );
    assert!(bound.flow_at(local.name).is_some());
    let raw = bound.symbol(local.declaration).unwrap();
    let scope = if list.flags.0 == 0 {
        callable.declaration
    } else {
        assert_eq!(list.flags.0, 1);
        bound.block_scope_container(local.declaration).unwrap()
    };
    let NodeData::Identifier(name) = &parsed.arena.get(local.name.node).unwrap().data else {
        panic!("expected the written local name");
    };
    assert_eq!(
        checker
            .store()
            .symbol_table(bound.locals(scope).unwrap())
            .unwrap()
            .get_source(&name.text),
        Some(raw)
    );
    owner(checker, local.declaration)
}

#[derive(Clone, Copy)]
struct Write {
    expression: NodeRef,
    target: NodeRef,
    right: NodeRef,
}

fn writes(parsed: &ParseResult, name: &str) -> Vec<Write> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            if parsed.arena.get(binary.operator_token)?.kind != SyntaxKind::EqualsToken {
                return None;
            }
            let NodeData::Identifier(identifier) = &parsed.arena.get(binary.left)?.data else {
                return None;
            };
            if identifier.text != name {
                return None;
            }
            let expression = node(parsed, id);
            Some(Write {
                expression,
                target: child(parsed, expression, binary.left),
                right: child(parsed, expression, binary.right),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|write| {
        parsed
            .arena
            .get(write.expression.node)
            .unwrap()
            .range
            .start
            .get()
    });
    result
}

fn assert_write(
    checker: &mut CanonicalCheckerContext<'_>,
    callable: &Callable,
    write: Write,
    symbol: SemanticSymbolId,
) {
    assert_eq!(
        checker.get_symbol_at_location(write.target),
        Ok(Some(symbol))
    );
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(bound.container(write.target), Some(callable.declaration));
    assert_eq!(
        bound.flow_container(write.target),
        Some(callable.declaration)
    );
    assert!(bound.flow_at(write.target).is_some());
}

fn assert_read(
    checker: &mut CanonicalCheckerContext<'_>,
    read: NodeRef,
    symbol: SemanticSymbolId,
    type_: TypeId,
) {
    assert_eq!(checker.get_type_at_location(read), Ok(type_));
    assert_eq!(checker.get_symbol_at_location(read), Ok(Some(symbol)));
}

#[derive(Clone, Copy)]
enum QueryOrder {
    Source,
    Callable,
    Read,
}

const ORDERS: [QueryOrder; 3] = [QueryOrder::Source, QueryOrder::Callable, QueryOrder::Read];

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
        QueryOrder::Read => Some(read),
    }
    .map(|location| (location, checker.get_type_at_location(location).unwrap()));
    checker.check_source_file(FILE).unwrap();
    assert!(checked(checker));
    assert_eq!(checker.store().type_resolution_len(), 0);
    if let Some((location, type_)) = first {
        assert_eq!(checker.get_type_at_location(location), Ok(type_));
    }
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
                let location = node(parsed, id);
                let signature = store.signature_links(location).cloned();
                let record = signature
                    .as_ref()
                    .and_then(|links| links.resolved_signature.signature())
                    .map(|id| (id, format!("{:?}", store.signature(id).unwrap())));
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    signature,
                    record,
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.diagnostics().clone(),
    )
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    callable: &Callable,
    reads: &[(NodeRef, SemanticSymbolId, TypeId)],
) {
    let state = callable_state(checker, parsed, callable);
    for &(read, owner, type_) in reads {
        assert_read(checker, read, owner, type_);
    }
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        assert!(checked(checker));
        assert_eq!(callable_state(checker, parsed, callable), state);
        for &(read, owner, type_) in reads {
            assert_read(checker, read, owner, type_);
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

fn assert_ts2454(checker: &CanonicalCheckerContext<'_>, reads: &[NodeRef]) {
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), reads.len(), "{diagnostics:?}");
    for (diagnostic, &read) in diagnostics.iter().zip(reads) {
        assert_eq!(diagnostic.node, Some(read));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2454);
        assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Variable 'value' is used before being assigned."
        );
        assert!(diagnostic.related_information.is_empty());
    }
}

#[test]
fn real_local_writes_feed_shared_function_and_arrow_returns() {
    let body = concat!(
        "  let value: string | undefined;\n",
        "  { value = input; }\n",
        "  if (value === undefined) { return 'missing'; }\n",
        "  const selected: string = value;\n",
        "  return selected;\n",
    );
    for (header, prefix) in [
        ("function run(input: string | undefined)", ""),
        ("const run = (input: string | undefined) =>", ""),
        (
            "const run = (input: string | undefined) =>",
            "  var input: string | undefined;\n",
        ),
    ] {
        let parsed = parse_source_file(&format!("{header} {{\n{prefix}{body}}};"));
        let run = callable(&parsed);
        assert!(run.annotation.is_none());
        let value = local(&parsed, "value");
        let selected = local(&parsed, "selected");
        let writes = writes(&parsed, "value");
        assert_eq!(writes.len(), 1);
        for order in ORDERS {
            let mut checker = context(&parsed);
            let symbol = absent_local(&checker, &parsed, &run, value);
            start(&mut checker, &run, selected.initializer.unwrap(), order);
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let state = callable_state(&mut checker, &parsed, &run);
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let declared = checker
                .get_type_from_type_node(value.annotation.unwrap())
                .unwrap();
            assert_eq!(state.returned, string);
            assert_eq!(state.parameters.len(), 1);
            assert_eq!(state.parameters[0].1, declared);
            assert_eq!(value_type(&checker, symbol), declared);
            if !prefix.is_empty() {
                let redeclaration = local(&parsed, "input");
                assert!(redeclaration.initializer.is_none());
                let parameter = run.parameters[0];
                let parameter_owner = state.parameters[0].0;
                assert_eq!(owner(&checker, redeclaration.declaration), parameter_owner);
                let record = checker.store().symbol(parameter_owner).unwrap();
                assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
                assert_eq!(
                    record.declarations(),
                    Some(&[parameter, redeclaration.declaration][..])
                );
                assert_eq!(record.value_declaration(), Some(parameter));
                assert_eq!(value_type(&checker, parameter_owner), declared);
                assert_eq!(
                    checker.get_type_from_type_node(redeclaration.annotation.unwrap()),
                    Ok(declared)
                );
                assert_eq!(
                    checker.get_symbol_at_location(redeclaration.name),
                    Ok(Some(parameter_owner))
                );
                assert_eq!(
                    checker
                        .file(FILE)
                        .unwrap()
                        .1
                        .block_scope_container(redeclaration.declaration),
                    Some(run.declaration)
                );
            }
            assert_write(&mut checker, &run, writes[0], symbol);
            let reads = [
                (writes[0].right, state.parameters[0].0, declared),
                (selected.initializer.unwrap(), symbol, string),
            ];
            replay(&mut checker, &parsed, &run, &reads);
        }
    }
}

#[test]
fn early_reads_report_once_each_and_true_flow_keeps_its_narrowed_type() {
    let body = concat!(
        "  let value: number;\n",
        "  const early: number = value;\n",
        "  if (value) { const truthy: number = value; return truthy; }\n",
        "  value = input;\n",
        "  const after: number = value;\n",
        "  return after;\n",
    );
    for header in [
        "function run(input: number): number",
        "const run = (input: number): number =>",
    ] {
        let parsed = parse_source_file(&format!("{header} {{\n{body}}};"));
        let run = callable(&parsed);
        let value = local(&parsed, "value");
        let early = local(&parsed, "early").initializer.unwrap();
        let truthy = local(&parsed, "truthy").initializer.unwrap();
        let after = local(&parsed, "after").initializer.unwrap();
        let conditions = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::IfStatement(statement) = &record.data else {
                    return None;
                };
                Some(child(&parsed, node(&parsed, id), statement.expression))
            })
            .collect::<Vec<_>>();
        let [condition] = conditions.as_slice() else {
            panic!("expected the one real truthiness condition");
        };
        let writes = writes(&parsed, "value");
        assert_eq!(writes.len(), 1);
        for order in ORDERS {
            let mut checker = context(&parsed);
            let symbol = absent_local(&checker, &parsed, &run, value);
            start(&mut checker, &run, early, order);
            assert_ts2454(&checker, &[early, *condition]);
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(callable_state(&mut checker, &parsed, &run).returned, number);
            assert_eq!(value_type(&checker, symbol), number);
            assert_write(&mut checker, &run, writes[0], symbol);
            let (_, bound) = checker.file(FILE).unwrap();
            assert_ne!(bound.flow_at(*condition), bound.flow_at(truthy));
            assert_ne!(bound.flow_at(truthy), bound.flow_at(after));
            replay(
                &mut checker,
                &parsed,
                &run,
                &[
                    (early, symbol, number),
                    (*condition, symbol, number),
                    (truthy, symbol, number),
                    (after, symbol, number),
                ],
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the two lexical owners and retained var in the same body.
fn block_writes_keep_outer_state_without_leaking_shadowed_locals() {
    let body = concat!(
        "  let value: string;\n",
        "  { let value: number; value = count; const inner: number = value; }\n",
        "  const before: string = value;\n",
        "  { value = text; var retained: string; retained = text; }\n",
        "  const after: string = value;\n",
        "  const afterVar: string = retained;\n",
        "  return after;\n",
    );
    for header in [
        "function run(text: string, count: number)",
        "const run = (text: string, count: number) =>",
    ] {
        let parsed = parse_source_file(&format!("{header} {{\n{body}}};"));
        let run = callable(&parsed);
        let values = locals(&parsed, "value");
        assert_eq!(values.len(), 2);
        let retained = local(&parsed, "retained");
        let inner = local(&parsed, "inner").initializer.unwrap();
        let before = local(&parsed, "before").initializer.unwrap();
        let after = local(&parsed, "after").initializer.unwrap();
        let after_var = local(&parsed, "afterVar").initializer.unwrap();
        let value_writes = writes(&parsed, "value");
        let var_writes = writes(&parsed, "retained");
        assert_eq!(value_writes.len(), 2);
        assert_eq!(var_writes.len(), 1);
        for order in ORDERS {
            let mut checker = context(&parsed);
            let outer = absent_local(&checker, &parsed, &run, values[0]);
            let shadow = absent_local(&checker, &parsed, &run, values[1]);
            let retained_owner = absent_local(&checker, &parsed, &run, retained);
            assert_ne!(outer, shadow);
            assert_ne!(outer, retained_owner);
            start(&mut checker, &run, before, order);
            assert_ts2454(&checker, &[before]);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let string = bootstrap.string_type;
            let number = bootstrap.number_type;
            let state = callable_state(&mut checker, &parsed, &run);
            assert_eq!(state.returned, string);
            assert_eq!(value_type(&checker, outer), string);
            assert_eq!(value_type(&checker, shadow), number);
            assert_eq!(value_type(&checker, retained_owner), string);
            assert_write(&mut checker, &run, value_writes[0], shadow);
            assert_write(&mut checker, &run, value_writes[1], outer);
            assert_write(&mut checker, &run, var_writes[0], retained_owner);
            let (_, bound) = checker.file(FILE).unwrap();
            let outer_scope = bound.block_scope_container(values[0].declaration).unwrap();
            let inner_scope = bound.block_scope_container(values[1].declaration).unwrap();
            assert_ne!(outer_scope, inner_scope);
            assert_eq!(bound.block_scope_container(inner), Some(inner_scope));
            assert_eq!(bound.block_scope_container(before), Some(outer_scope));
            assert_eq!(bound.block_scope_container(after), Some(outer_scope));
            assert_ne!(
                bound.block_scope_container(retained.declaration),
                bound.block_scope_container(after_var)
            );
            assert_eq!(bound.container(retained.declaration), Some(run.declaration));
            let record = checker.store().symbol(retained_owner).unwrap();
            assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
            replay(
                &mut checker,
                &parsed,
                &run,
                &[
                    (inner, shadow, number),
                    (before, outer, string),
                    (after, outer, string),
                    (after_var, retained_owner, string),
                ],
            );
        }
    }
}

#[test]
fn composed_writes_keep_the_declared_type_and_exact_assignment_error() {
    let body = concat!(
        "  let value: number;\n",
        "  { value = 'wrong'; }\n",
        "  value = input;\n",
        "  const after: number = value;\n",
        "  if (flag) { return after; }\n",
        "  return value;\n",
    );
    for header in [
        "function run(flag: boolean, input: number): number",
        "const run = (flag: boolean, input: number): number =>",
    ] {
        let parsed = parse_source_file(&format!("{header} {{\n{body}}};"));
        let run = callable(&parsed);
        let value = local(&parsed, "value");
        let after = local(&parsed, "after").initializer.unwrap();
        let writes = writes(&parsed, "value");
        assert_eq!(writes.len(), 2);
        for order in ORDERS {
            let mut checker = context(&parsed);
            let symbol = absent_local(&checker, &parsed, &run, value);
            start(&mut checker, &run, after, order);
            let diagnostics = checker.diagnostics().as_slice();
            assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
            assert_eq!(diagnostics[0].node, Some(writes[0].target));
            assert_eq!(diagnostics[0].range_override, None);
            assert_eq!(diagnostics[0].diagnostic.code(), 2322);
            assert_eq!(diagnostics[0].diagnostic.arguments, ["string", "number"]);
            assert_eq!(
                diagnostics[0].diagnostic.render().unwrap(),
                "Type 'string' is not assignable to type 'number'."
            );
            assert!(diagnostics[0].related_information.is_empty());
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(value_type(&checker, symbol), number);
            assert_eq!(callable_state(&mut checker, &parsed, &run).returned, number);
            for &write in &writes {
                assert_write(&mut checker, &run, write, symbol);
            }
            replay(&mut checker, &parsed, &run, &[(after, symbol, number)]);
        }
    }
}

fn assert_planning_rejection(parsed: &ParseResult, run: &Callable, error: SourceCheckError) {
    for query_first in [false, true] {
        let mut checker = context(parsed);
        let before = snapshot(&checker, parsed);
        if query_first {
            assert_eq!(
                checker.get_type_at_location(run.declaration),
                Err(CanonicalArtifactQueryError::SourceCheck(error))
            );
        }
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(error));
            assert!(!checked(&checker));
            assert!(checker.diagnostics().is_empty());
            assert!(checker.store().signature_links(run.declaration).is_none());
            assert_eq!(snapshot(&checker, parsed), before);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the pending capture and the distinct body limits explicit.
fn composed_locals_keep_pending_captures_and_unreleased_writes_rejected() {
    let pending = concat!(
        "  let value: number;\n",
        "  { const shadow: number = input; }\n",
        "  const get = () => value;\n",
        "  value = input;\n",
        "  return get();\n",
    );
    for header in [
        "function run(input: number)",
        "const run = (input: number) =>",
    ] {
        let parsed = parse_source_file(&format!("{header} {{\n{pending}}};"));
        let run = callable(&parsed);
        let get = local(&parsed, "get").initializer.unwrap();
        let NodeData::ArrowFunction(arrow) = &parsed.arena.get(get.node).unwrap().data else {
            panic!("expected the actual local arrow capture");
        };
        let read = child(&parsed, get, arrow.body);
        assert_eq!(
            parsed.arena.get(read.node).unwrap().kind,
            SyntaxKind::Identifier
        );
        assert_planning_rejection(
            &parsed,
            &run,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node: read,
                kind: SyntaxKind::Identifier,
                role: SourceSyntaxRole::FunctionBody,
            }),
        );
    }
    for body in [
        "let value: number; if (flag) { value = input; } return value;",
        "let value: number; if (flag) { { value = input; } } return value;",
    ] {
        for header in [
            "function run(flag: boolean, input: number)",
            "const run = (flag: boolean, input: number) =>",
        ] {
            let parsed = parse_source_file(&format!("{header} {{ {body} }};"));
            let run = callable(&parsed);
            assert_planning_rejection(
                &parsed,
                &run,
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::FunctionBody(run.body),
                )),
            );
        }
    }
    for source in [
        "const run = (flag: boolean, input: number) => { let value: number; { value = input; } while (flag) {} return value; };",
        "const run = async (input: number) => { let value: number; { value = input; } return value; };",
        "const run = (input: number) => { let value: number; { value = input; } const next = ((part: number) => part)(value); return next; };",
    ] {
        let parsed = parse_source_file(source);
        let run = callable(&parsed);
        assert_planning_rejection(
            &parsed,
            &run,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(run.body)),
        );
    }
}

#[test]
fn later_effect_failure_does_not_publish_an_inferred_return_or_local_value() {
    let body = concat!(
        "  let value: number;\n",
        "  { value = input; }\n",
        "  if (flag) { stop(); }\n",
        "  return value;\n",
    );
    for header in [
        "function run(flag: boolean, input: number)",
        "const run = (flag: boolean, input: number) =>",
    ] {
        let source = format!("declare function stop(): never;\n{header} {{\n{body}}};");
        let parsed = parse_source_file(&source);
        let run = callable(&parsed);
        assert!(run.annotation.is_none());
        for query_first in [false, true] {
            let mut checker = context(&parsed);
            let value = absent_local(&checker, &parsed, &run, local(&parsed, "value"));
            let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                SourceFunctionUnsupported::FunctionBody(run.body),
            ));
            if query_first {
                assert_eq!(
                    checker.get_type_at_location(run.declaration),
                    Err(CanonicalArtifactQueryError::SourceCheck(error))
                );
            } else {
                assert_eq!(checker.check_source_file(FILE), Err(error));
            }
            assert!(!checked(&checker));
            assert!(checker.diagnostics().is_empty());
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
            assert!(
                checker
                    .store()
                    .value_symbol_links(value)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            let stopped = snapshot(&checker, &parsed);
            for _ in 0..2 {
                assert_eq!(checker.recheck_source_file(FILE), Err(error));
                assert_eq!(
                    checker.get_type_at_location(run.declaration),
                    Err(CanonicalArtifactQueryError::SourceCheck(error))
                );
                assert_eq!(
                    checker
                        .store()
                        .signature(signature)
                        .unwrap()
                        .resolved_return_type(),
                    None
                );
                assert_eq!(snapshot(&checker, &parsed), stopped);
            }
        }
    }
}
