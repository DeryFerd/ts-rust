use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, NodeLinks, SignatureId, SignatureLinks, SourceCheckError,
    SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax,
    ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(58_710);
const LIBRARY: FileId = FileId::new(58_711);
const ARRAY_LIBRARY: &str = concat!(
    "interface Array<T> { [n: number]: T; }\n",
    "interface ReadonlyArray<T> { readonly [n: number]: T; }\n",
);

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, default_library, name) in [
        (LIBRARY, library, true, "\"/project/lib.d.ts\""),
        (FILE, parsed, false, "\"/project/callable-for-of.ts\""),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    default_library,
                    default_library,
                    CanonicalModuleState::Script,
                )
                .with_always_strict(true),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY, &library.arena), (FILE, &parsed.arena)],
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
            let initializer = variable.initializer?;
            let declaration = node(parsed, id);
            Some(Binding {
                declaration,
                name: child(parsed, declaration, variable.name),
                annotation: variable.type_.map(|id| child(parsed, declaration, id)),
                initializer: child(parsed, declaration, initializer),
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

struct Iteration {
    statement: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    iterable: NodeRef,
    body: NodeRef,
}

fn iteration(parsed: &ParseResult) -> Iteration {
    let mut loops = parsed.arena.iter().filter_map(|(id, record)| {
        (record.kind == SyntaxKind::ForOfStatement).then_some(node(parsed, id))
    });
    let statement = loops.next().unwrap();
    assert!(loops.next().is_none());
    let NodeData::ForInOrOfStatement(loop_) = &parsed.arena.get(statement.node).unwrap().data else {
        panic!("expected the actual for-of statement");
    };
    assert!(loop_.await_modifier.is_none());
    let initializer = child(parsed, statement, loop_.initializer);
    let NodeData::VariableDeclarationList(list) =
        &parsed.arena.get(initializer.node).unwrap().data
    else {
        panic!("expected the lexical loop declaration list");
    };
    let [declaration] = list.declarations.nodes.as_slice() else {
        panic!("expected one loop declaration");
    };
    let declaration = child(parsed, initializer, *declaration);
    let NodeData::VariableDeclaration(variable) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected the actual loop binding");
    };
    assert!(variable.type_.is_none());
    assert!(variable.initializer.is_none());
    Iteration {
        statement,
        declaration,
        name: child(parsed, declaration, variable.name),
        iterable: child(parsed, statement, loop_.expression),
        body: child(parsed, statement, loop_.statement),
    }
}

fn iteration_owner(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    iteration: &Iteration,
    callable: &Callable,
    element: TypeId,
) -> SemanticSymbolId {
    let owner = symbol(checker, iteration.declaration);
    let NodeData::Identifier(name) = &parsed.arena.get(iteration.name.node).unwrap().data else {
        panic!("expected the actual loop identifier");
    };
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(
        bound.container(iteration.declaration),
        Some(callable.declaration)
    );
    assert_eq!(
        bound.block_scope_container(iteration.declaration),
        Some(iteration.statement)
    );
    let locals = bound.locals(iteration.statement).unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(locals)
            .unwrap()
            .get_source(&name.text),
        Some(owner)
    );
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[iteration.declaration][..]));
    assert_eq!(record.value_declaration(), Some(iteration.declaration));
    assert_eq!(value_type(checker, owner), element);
    assert!(bound.flow_at(iteration.name).is_some());
    owner
}

fn array_element(checker: &CanonicalCheckerContext<'_>, type_: TypeId, readonly: bool) -> TypeId {
    let TypeData::TypeReference(reference) = checker.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected the actual library array reference");
    };
    let target = if readonly {
        checker.global_types().readonly_array_type
    } else {
        checker.global_types().array_type
    };
    assert_eq!(reference.object.target, Some(target));
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("expected one retained element type");
    };
    *element
}

#[test]
#[allow(clippy::too_many_lines)] // Keep conditional writes, zero iterations, source owners and caller replay together.
fn callable_for_of_composes_prefix_conditional_write_return_and_continuation() {
    let body = concat!(
        "  const entry = value;\n",
        "  if (entry === undefined) { return undefined; }\n",
        "  const sequence = values;\n",
        "  let best: string | undefined;\n",
        "  for (const item of sequence) {\n",
        "    const selected: string = item;\n",
        "    if (flag) { return selected; }\n",
        "    if (entry) { best = selected; const afterWrite = best; }\n",
        "  }\n",
        "  const afterLoop = best;\n",
        "  return afterLoop;\n",
    );
    for header in [
        "function select(value: string | undefined, values: readonly string[], flag: boolean): string | undefined",
        "const select = (value: string | undefined, values: readonly string[], flag: boolean): string | undefined =>",
    ] {
        let source = format!(
            "{header} {{\n{body}}};\nfunction call(values: readonly string[]): string | undefined {{ const answer = select(undefined, values, true); return answer; }}"
        );
        let parsed = parse_source_file(&source);
        let library = parse_source_file(ARRAY_LIBRARY);
        let select = callable(&parsed, "select");
        let caller = callable(&parsed, "call");
        let iteration = iteration(&parsed);
        let entry = binding(&parsed, "entry");
        let sequence = binding(&parsed, "sequence");
        let selected = binding(&parsed, "selected");
        let after_write = binding(&parsed, "afterWrite");
        let after_loop = binding(&parsed, "afterLoop");
        let answer = binding(&parsed, "answer");
        for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
            let mut checker = context(&parsed, &library);
            start(&mut checker, &select, selected.initializer, order);
            assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
            let state = callable_state(&mut checker, &parsed, &select);
            let caller_state = callable_state(&mut checker, &parsed, &caller);
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let undefined = checker.store().intrinsic_bootstrap().unwrap().undefined_type;
            let declared = state.parameters[0].1;
            assert_eq!(checker.type_to_string(declared).unwrap(), "string | undefined");
            assert_eq!(state.returned, declared);
            assert_eq!(caller_state.returned, declared);
            assert_eq!(array_element(&checker, state.parameters[1].1, true), string);
            assert_eq!(caller_state.parameters[0].1, state.parameters[1].1);
            read(&mut checker, entry.initializer, state.parameters[0].0, declared);
            read(
                &mut checker,
                sequence.initializer,
                state.parameters[1].0,
                state.parameters[1].1,
            );
            let sequence_owner = symbol(&checker, sequence.declaration);
            read(
                &mut checker,
                iteration.iterable,
                sequence_owner,
                state.parameters[1].1,
            );
            let item = iteration_owner(&checker, &parsed, &iteration, &select, string);
            read(&mut checker, iteration.name, item, string);
            read(&mut checker, selected.initializer, item, string);
            assert_eq!(
                checker.get_type_from_type_node(selected.annotation.unwrap()),
                Ok(string)
            );
            let best = checker
                .get_symbol_at_location(after_loop.initializer)
                .unwrap()
                .unwrap();
            assert_ne!(best, item);
            assert_eq!(value_type(&checker, best), declared);
            read(&mut checker, after_write.initializer, best, string);
            read(&mut checker, after_loop.initializer, best, declared);
            let returns = return_sites(&checker, &parsed, &select);
            assert_eq!(returns.len(), 3);
            assert_eq!(
                checker.get_type_at_location(returns[0].1.unwrap()),
                Ok(undefined)
            );
            let selected_owner = symbol(&checker, selected.declaration);
            read(&mut checker, returns[1].1.unwrap(), selected_owner, string);
            let after_loop_owner = symbol(&checker, after_loop.declaration);
            read(&mut checker, returns[2].1.unwrap(), after_loop_owner, declared);
            assert_eq!(checker.get_type_at_location(answer.initializer), Ok(declared));
            assert_eq!(signature(&checker, answer.initializer), state.signature);
            let (_, bound) = checker.file(FILE).unwrap();
            assert_eq!(
                bound.block_scope_container(selected.declaration),
                Some(iteration.body)
            );
            assert_ne!(
                bound.flow_at(after_write.initializer),
                bound.flow_at(after_loop.initializer)
            );
            assert_ne!(bound.flow_at(iteration.statement), bound.flow_at(returns[2].0));
            assert_eq!(bound.flow_graph().container_end(select.declaration), None);
            replay(
                &mut checker,
                &parsed,
                &[&select, &caller],
                &[
                    sequence.initializer,
                    iteration.iterable,
                    iteration.name,
                    selected.initializer,
                    after_write.initializer,
                    after_loop.initializer,
                    returns[1].1.unwrap(),
                    returns[2].1.unwrap(),
                    answer.initializer,
                ],
            );
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check real iterable targets, shadowed names and the exact body diagnostic together.
fn callable_for_of_keeps_iterable_identity_loop_scope_and_body_call_diagnostics() {
    for input in ["string", "string[]", "readonly string[]"] {
        for header in ["function run", "const run ="] {
            let arrow = if header == "const run =" { " =>" } else { "" };
            let source = format!(
                "function consume(value: string): void {{}}\nfunction reject(value: number): void {{}}\n{header}(values: {input}, flag: boolean): void{arrow} {{ const item: number = 1; const sequence = values; if (flag) {{}} for (const item of sequence) {{ const selected: string = item; consume(selected); reject(selected); }} const afterLoop: number = item; reject(afterLoop); }};"
            );
            let parsed = parse_source_file(&source);
            let library = parse_source_file(ARRAY_LIBRARY);
            let run = callable(&parsed, "run");
            let consume = callable(&parsed, "consume");
            let reject = callable(&parsed, "reject");
            let outer = binding(&parsed, "item");
            let sequence = binding(&parsed, "sequence");
            let selected = binding(&parsed, "selected");
            let after_loop = binding(&parsed, "afterLoop");
            let iteration = iteration(&parsed);
            let mut calls = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::CallExpression(call) = &record.data else {
                        return None;
                    };
                    let [argument] = call.arguments.nodes.as_slice() else {
                        return None;
                    };
                    let call_node = node(&parsed, id);
                    Some((
                        call_node,
                        child(&parsed, call_node, call.expression),
                        child(&parsed, call_node, *argument),
                    ))
                })
                .collect::<Vec<_>>();
            calls.sort_by_key(|&(call, _, _)| {
                parsed.arena.get(call.node).unwrap().range.start.get()
            });
            assert_eq!(calls.len(), 3);
            for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
                let mut checker = context(&parsed, &library);
                start(&mut checker, &run, selected.initializer, order);
                let run_state = callable_state(&mut checker, &parsed, &run);
                let consume_state = callable_state(&mut checker, &parsed, &consume);
                let reject_state = callable_state(&mut checker, &parsed, &reject);
                let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
                let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
                let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
                assert_eq!(run_state.returned, void);
                let iterable_type = run_state.parameters[0].1;
                if input == "string" {
                    assert_eq!(iterable_type, string);
                } else {
                    assert_eq!(
                        array_element(&checker, iterable_type, input.starts_with("readonly")),
                        string
                    );
                }
                let sequence_owner = symbol(&checker, sequence.declaration);
                read(
                    &mut checker,
                    sequence.initializer,
                    run_state.parameters[0].0,
                    iterable_type,
                );
                read(&mut checker, iteration.iterable, sequence_owner, iterable_type);
                let item = iteration_owner(&checker, &parsed, &iteration, &run, string);
                let outer_owner = symbol(&checker, outer.declaration);
                assert_ne!(item, outer_owner);
                assert_eq!(value_type(&checker, outer_owner), number);
                read(&mut checker, selected.initializer, item, string);
                read(&mut checker, after_loop.initializer, outer_owner, number);
                let selected_owner = symbol(&checker, selected.declaration);
                let after_loop_owner = symbol(&checker, after_loop.declaration);
                let expected = [
                    (&consume_state, selected_owner, string),
                    (&reject_state, selected_owner, string),
                    (&reject_state, after_loop_owner, number),
                ];
                for (&(call, callee, argument), (target, argument_owner, argument_type)) in
                    calls.iter().zip(expected)
                {
                    assert_eq!(checker.get_type_at_location(call), Ok(void));
                    assert_eq!(signature(&checker, call), target.signature);
                    read(&mut checker, callee, target.owner, target.type_);
                    read(&mut checker, argument, argument_owner, argument_type);
                }
                let [diagnostic] = checker.diagnostics().as_slice() else {
                    panic!(
                        "expected only the wrong-argument diagnostic: {:?}",
                        checker.diagnostics()
                    );
                };
                assert_eq!(diagnostic.diagnostic.code(), 2345);
                assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
                assert_eq!(diagnostic.node, Some(calls[1].2));
                assert_eq!(text_at(&source, &parsed, calls[1].2), "selected");
                assert_eq!(diagnostic.range_override, None);
                assert!(diagnostic.related_information.is_empty());
                let (_, bound) = checker.file(FILE).unwrap();
                assert_eq!(
                    bound.block_scope_container(outer.declaration),
                    Some(run.declaration)
                );
                assert_eq!(
                    bound.block_scope_container(selected.declaration),
                    Some(iteration.body)
                );
                assert!(bound.flow_graph().container_end(run.declaration).is_some());
                let mut locations = vec![
                    iteration.name,
                    iteration.iterable,
                    selected.initializer,
                    after_loop.initializer,
                ];
                locations.extend(
                    calls
                        .iter()
                        .flat_map(|&(call, callee, argument)| [call, callee, argument]),
                );
                replay(&mut checker, &parsed, &[&run, &consume, &reject], &locations);
            }
        }
    }
}

#[test]
fn callable_for_of_keeps_unreleased_headers_and_loop_exits_rejected() {
    for body in [
        "for await (const item of values) {}",
        "for (const item of values) { break; }",
        "for (const item of values) { continue; }",
    ] {
        let source = format!(
            "const run = (values: string[], flag: boolean): void => {{ const sequence = values; if (flag) {{}} {body} }};"
        );
        let parsed = parse_source_file(&source);
        let library = parse_source_file(ARRAY_LIBRARY);
        let run = callable(&parsed, "run");
        let mut checker = context(&parsed, &library);
        let before = publication(&checker, &parsed);
        let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(run.body));
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(error), "{source}");
            assert!(!checked(&checker));
            assert_eq!(publication(&checker, &parsed), before);
        }
    }
}

#[test]
fn callable_for_of_array_binding_reports_non_array_element_with_original_library() {
    let source = "const run = (values: string[], flag: boolean): void => { const sequence = values; if (flag) {} for (const [item] of values) {} };";
    assert_eq!(source.len(), 129);
    assert_eq!(&source[106..112], "[item]");
    let parsed = parse_source_file(source);
    let library = parse_source_file(ARRAY_LIBRARY);
    let patterns = parsed
        .arena
        .iter()
        .filter(|(_, record)| record.kind == SyntaxKind::ArrayBindingPattern)
        .map(|(id, _)| node(&parsed, id))
        .collect::<Vec<_>>();
    let [pattern] = patterns.as_slice() else {
        panic!("expected the original array binding pattern")
    };
    let NodeData::BindingPattern(pattern_data) = &parsed.arena.get(pattern.node).unwrap().data
    else {
        unreachable!()
    };
    let [element] = pattern_data.elements.nodes.as_slice() else {
        panic!("expected the original item binding")
    };
    let element = node(&parsed, *element);
    let NodeData::BindingElement(binding) = &parsed.arena.get(element.node).unwrap().data else {
        unreachable!()
    };
    let name = node(&parsed, binding.name.unwrap());
    let mut checker = context(&parsed, &library);
    checker.check_source_file(FILE).unwrap();
    assert!(checked(&checker));
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected the original library's array-binding diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2461);
    assert_eq!(
        diagnostic.diagnostic.category(),
        ts_diagnostics::Category::Error
    );
    assert_eq!(diagnostic.diagnostic.arguments, ["string".to_owned()]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not an array type."
    );
    assert_eq!(diagnostic.node, Some(*pattern));
    let range = diagnostic.range_override.map_or_else(
        || parsed.arena.get(pattern.node).unwrap().range,
        |range| range.range(),
    );
    assert_eq!((range.start.get(), range.end.get()), (106, 112));
    assert!(diagnostic.related_information.is_empty());
    let item = symbol(&checker, element);
    let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
    assert_eq!(value_type(&checker, item), any);
    assert_eq!(checker.get_type_at_location(name), Ok(any));
    assert_eq!(checker.get_symbol_at_location(name), Ok(Some(item)));
    let before = publication(&checker, &parsed);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        assert!(checked(&checker));
        assert_eq!(checker.get_type_at_location(name), Ok(any));
        assert_eq!(checker.get_symbol_at_location(name), Ok(Some(item)));
        assert_eq!(publication(&checker, &parsed), before);
    }
}
