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

const FILE: FileId = FileId::new(58_511);

fn context(parsed: &ParseResult, unknown_catch: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/callable-try-statements.ts\""),
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
            use_unknown_in_catch_variables: unknown_catch,
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
            if parsed.arena.get(record.parent?)?.kind != SyntaxKind::VariableDeclarationList {
                return None;
            }
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
                initializer: child(parsed, declaration, variable.initializer?),
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

#[derive(Clone, Copy)]
struct CatchBinding {
    clause: NodeRef,
    block: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: Option<NodeRef>,
}

fn catches(parsed: &ParseResult) -> Vec<CatchBinding> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::CatchClause(catch) = &record.data else {
                return None;
            };
            let clause = node(parsed, id);
            let declaration = child(parsed, clause, catch.variable_declaration?);
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("catch must retain its actual variable declaration");
            };
            Some(CatchBinding {
                clause,
                block: child(parsed, clause, catch.block),
                declaration,
                name: child(parsed, declaration, variable.name),
                annotation: variable.type_.map(|id| child(parsed, declaration, id)),
                initializer: variable.initializer.map(|id| child(parsed, declaration, id)),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|catch| {
        parsed.arena.get(catch.clause.node).unwrap().range.start.get()
    });
    result
}

fn catch_owner(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    run: &Callable,
    catch: CatchBinding,
    expected: TypeId,
) -> SemanticSymbolId {
    let owner = symbol(checker, catch.declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[catch.declaration][..]));
    assert_eq!(record.value_declaration(), Some(catch.declaration));
    let NodeData::Identifier(name) = &parsed.arena.get(catch.name.node).unwrap().data else {
        panic!("expected the real catch identifier");
    };
    let (_, bound) = checker.file(FILE).unwrap();
    let locals = bound.locals(catch.clause).unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_store()
            .symbol_table(locals)
            .unwrap()
            .get(EscapedName::source(&name.text).as_ref()),
        Some(owner)
    );
    assert_eq!(bound.container(catch.declaration), Some(run.declaration));
    assert_eq!(
        bound.block_scope_container(catch.declaration),
        Some(catch.clause)
    );
    assert_eq!(bound.flow_container(catch.block), Some(run.declaration));
    assert!(bound.flow_at(catch.block).is_some());
    read(checker, catch.name, owner, expected);
    assert_eq!(value_type(checker, owner), expected);
    if let Some(annotation) = catch.annotation {
        let written = checker.get_type_from_type_node(annotation).unwrap();
        if expected != checker.store().intrinsic_bootstrap().unwrap().error_type {
            assert_eq!(written, expected);
        }
    }
    owner
}

fn throws(parsed: &ParseResult) -> Vec<(NodeRef, NodeRef)> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::ThrowStatement(thrown) = &record.data else {
                return None;
            };
            let statement = node(parsed, id);
            Some((statement, child(parsed, statement, thrown.expression)))
        })
        .collect::<Vec<_>>();
    result
        .sort_by_key(|&(statement, _)| parsed.arena.get(statement.node).unwrap().range.start.get());
    result
}

fn top_level_kinds(parsed: &ParseResult, run: &Callable) -> Vec<SyntaxKind> {
    let NodeData::Block(block) = &parsed.arena.get(run.body.node).unwrap().data else {
        panic!("expected the real callable block");
    };
    block
        .statements
        .nodes
        .iter()
        .map(|&id| {
            parsed
                .arena
                .get(child(parsed, run.body, id).node)
                .unwrap()
                .kind
        })
        .collect()
}

#[test]
fn try_catch_returns_share_function_and_arrow_statement_checks() {
    let body = concat!(
        "const entry = value; try { return entry; } ",
        "catch (error) { if (flag) { return value; } throw error; }"
    );
    for (source, kinds, returns) in [
        (
            String::from(
                "const run = (value: string): string => { try { return value; } catch { throw 'caught'; } };",
            ),
            vec![SyntaxKind::TryStatement],
            1,
        ),
        (
            String::from(
                "const run = (value: string): string => { const entry = value; try { return entry; } catch { return value; } };",
            ),
            vec![SyntaxKind::VariableStatement, SyntaxKind::TryStatement],
            2,
        ),
        (
            format!("function run(flag: boolean, value: string): string {{ {body} }}"),
            vec![SyntaxKind::VariableStatement, SyntaxKind::TryStatement],
            2,
        ),
        (
            format!("const run = (flag: boolean, value: string): string => {{ {body} }};"),
            vec![SyntaxKind::VariableStatement, SyntaxKind::TryStatement],
            2,
        ),
    ] {
        let parsed = parse_source_file(&source);
        let run = callable(&parsed, "run");
        assert_eq!(top_level_kinds(&parsed, &run), kinds);
        for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
            let mut checker = context(&parsed, true);
            let sites = return_sites(&checker, &parsed, &run);
            assert_eq!(sites.len(), returns);
            start(&mut checker, &run, sites[0].1.unwrap(), order);
            assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
            let state = callable_state(&mut checker, &parsed, &run);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let string = bootstrap.string_type;
            let unknown = bootstrap.unknown_type;
            assert_eq!(state.returned, string);
            let mut locations = Vec::new();
            for &(_, expression) in &sites {
                let expression = expression.unwrap();
                assert_eq!(checker.get_type_at_location(expression), Ok(string));
                locations.push(expression);
            }
            for catch in catches(&parsed) {
                catch_owner(&mut checker, &parsed, &run, catch, unknown);
            }
            for (statement, operand) in throws(&parsed) {
                let bound = checker.file(FILE).unwrap().1;
                assert_eq!(bound.flow_container(statement), Some(run.declaration));
                assert!(bound.flow_at(statement).is_some());
                let checked = checker.get_type_at_location(operand).unwrap();
                assert_eq!(
                    checker.store().type_node_links(operand).unwrap().resolved_type,
                    Some(checked)
                );
                locations.push(operand);
            }
            assert_eq!(
                checker.file(FILE).unwrap().1.flow_graph().container_end(run.declaration),
                None
            );
            replay(&mut checker, &parsed, &[&run], &locations);
        }
    }
}

#[test]
fn catch_entries_use_effective_options_and_written_annotations() {
    for unknown_catch in [false, true] {
        for annotation in ["", ": any", ": unknown"] {
            let source = format!(
                "function run(): string {{ try {{ throw 1; }} catch (error{annotation}) {{ return error; }} }}"
            );
            let parsed = parse_source_file(&source);
            let run = callable(&parsed, "run");
            let catch_bindings = catches(&parsed);
            let [catch] = catch_bindings.as_slice() else {
                panic!("expected one catch");
            };
            let catch = *catch;
            for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
                let mut checker = context(&parsed, unknown_catch);
                let returned = return_sites(&checker, &parsed, &run)[0];
                start(&mut checker, &run, returned.1.unwrap(), order);
                let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
                let string = bootstrap.string_type;
                let unknown = annotation == ": unknown" || (annotation.is_empty() && unknown_catch);
                let expected = if unknown {
                    bootstrap.unknown_type
                } else {
                    bootstrap.any_type
                };
                let owner = catch_owner(&mut checker, &parsed, &run, catch, expected);
                read(&mut checker, returned.1.unwrap(), owner, expected);
                assert_eq!(callable_state(&mut checker, &parsed, &run).returned, string);
                let diagnostics = checker.diagnostics().as_slice();
                assert_eq!(diagnostics.len(), usize::from(unknown));
                if unknown {
                    assert_eq!(diagnostics[0].diagnostic.code(), 2322);
                    assert_eq!(diagnostics[0].node, Some(returned.0));
                    assert_eq!(
                        diagnostics[0].diagnostic.render().unwrap(),
                        "Type 'unknown' is not assignable to type 'string'."
                    );
                    assert_eq!(diagnostics[0].range_override, None);
                    assert!(diagnostics[0].related_information.is_empty());
                }
                replay(&mut checker, &parsed, &[&run], &[catch.name, returned.1.unwrap()]);
            }
        }
    }
}

#[test]
fn nested_catch_scopes_restore_outer_and_sibling_bindings() {
    let source = concat!(
        "function run(value: string): string {\n",
        "  const error: string = value;\n",
        "  try { throw 1; } catch (error) {\n",
        "    const outerCatch = error;\n",
        "    try { throw 2; } catch (error: any) { const innerCatch = error; }\n",
        "    const restoredCatch = error;\n",
        "  }\n",
        "  const after = error; return after;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let run = callable(&parsed, "run");
    let catches = catches(&parsed);
    assert_eq!(catches.len(), 2);
    let outer = bindings(&parsed, "error");
    assert_eq!(outer.len(), 1);
    let reads = ["outerCatch", "innerCatch", "restoredCatch", "after"]
        .map(|name| binding(&parsed, name).initializer);
    for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
        let mut checker = context(&parsed, true);
        start(&mut checker, &run, reads[0], order);
        assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let unknown = bootstrap.unknown_type;
        let any = bootstrap.any_type;
        let first = catch_owner(&mut checker, &parsed, &run, catches[0], unknown);
        let second = catch_owner(&mut checker, &parsed, &run, catches[1], any);
        let outside = symbol(&checker, outer[0].declaration);
        assert_eq!(
            checker.get_type_from_type_node(outer[0].annotation.unwrap()),
            Ok(string)
        );
        assert_ne!(first, second);
        assert_ne!(first, outside);
        assert_ne!(second, outside);
        for (location, owner, type_) in [
            (reads[0], first, unknown),
            (reads[1], second, any),
            (reads[2], first, unknown),
            (reads[3], outside, string),
        ] {
            read(&mut checker, location, owner, type_);
        }
        let bound = checker.file(FILE).unwrap().1;
        assert_eq!(bound.block_scope_container(reads[0]), Some(catches[0].block));
        assert_eq!(bound.block_scope_container(reads[1]), Some(catches[1].block));
        assert_eq!(bound.block_scope_container(reads[2]), Some(catches[0].block));
        assert_eq!(bound.block_scope_container(reads[3]), Some(run.declaration));
        assert_eq!(callable_state(&mut checker, &parsed, &run).returned, string);
        replay(&mut checker, &parsed, &[&run], &reads);
    }
}

#[test]
fn exception_entries_keep_before_and_after_parameter_mutation_flow() {
    for body in [
        concat!(
            "if (value === undefined) { return 'missing'; }\n",
            "const beforeMutation = value;\n",
            "try { value = undefined; const afterMutation = value; throw 1; } catch { return value; }"
        ),
        concat!(
            "if (value === undefined) { return 'missing'; }\n",
            "const beforeMutation = value;\n",
            "try {\n",
            "  try { throw 1; } catch {}\n",
            "  value = undefined; const afterMutation = value; throw 2;\n",
            "} catch { return value; }"
        ),
    ] {
        let source = format!(
            "function run(value: string | undefined): string | undefined {{ {body} }}"
        );
        let parsed = parse_source_file(&source);
        let run = callable(&parsed, "run");
        let before = binding(&parsed, "beforeMutation").initializer;
        let after = binding(&parsed, "afterMutation").initializer;
        for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
            let mut checker = context(&parsed, true);
            let returned = return_sites(&checker, &parsed, &run);
            assert_eq!(returned.len(), 2);
            let catch_read = returned[1].1.unwrap();
            start(&mut checker, &run, catch_read, order);
            assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
            let state = callable_state(&mut checker, &parsed, &run);
            let (owner, declared) = state.parameters[0];
            assert_eq!(state.returned, declared);
            read(&mut checker, catch_read, owner, declared);
            let TypeData::Union(union) = checker.store().type_payload(declared).unwrap().data()
            else {
                panic!("catch must retain both sides of the real exception flow");
            };
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&bootstrap.string_type));
            assert!(union.union.types.contains(&bootstrap.undefined_type));
            let string = bootstrap.string_type;
            let undefined = bootstrap.undefined_type;
            read(&mut checker, before, owner, string);
            read(&mut checker, after, owner, undefined);
            assert_eq!(
                checker.file(FILE).unwrap().1.flow_graph().container_end(run.declaration),
                None
            );
            replay(&mut checker, &parsed, &[&run], &[before, after, catch_read]);
        }
    }
}

#[test]
fn throw_operands_do_not_create_return_values_or_implicit_exits() {
    let source = concat!(
        "function declared(value: string) { throw value; }\n",
        "const run = (value: string) => { throw value; };\n",
        "const branch = (flag: boolean, value: string) => { if (flag) { return value; } throw 'stop'; };\n",
    );
    let parsed = parse_source_file(source);
    let declared = callable(&parsed, "declared");
    let run = callable(&parsed, "run");
    let branch = callable(&parsed, "branch");
    assert_eq!(
        top_level_kinds(&parsed, &run),
        vec![SyntaxKind::ThrowStatement]
    );
    for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
        let mut checker = context(&parsed, true);
        let thrown = throws(&parsed);
        assert_eq!(thrown.len(), 3);
        start(&mut checker, &run, thrown[1].1, order);
        assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let void = bootstrap.void_type;
        let never = bootstrap.never_type;
        let string = bootstrap.string_type;
        assert_eq!(callable_state(&mut checker, &parsed, &declared).returned, void);
        assert_eq!(callable_state(&mut checker, &parsed, &run).returned, never);
        assert_eq!(callable_state(&mut checker, &parsed, &branch).returned, string);
        assert!(return_sites(&checker, &parsed, &declared).is_empty());
        assert!(return_sites(&checker, &parsed, &run).is_empty());
        for callable in [&declared, &run, &branch] {
            assert_eq!(
                checker.file(FILE).unwrap().1.flow_graph().container_end(callable.declaration),
                None
            );
        }
        let locations = thrown
            .iter()
            .map(|&(_, operand)| operand)
            .collect::<Vec<_>>();
        for &operand in &locations[..2] {
            assert_eq!(checker.get_type_at_location(operand), Ok(string));
        }
        replay(&mut checker, &parsed, &[&declared, &run, &branch], &locations);
    }
    let parsed = parse_source_file("const run = () => { throw missing; };");
    let run = callable(&parsed, "run");
    let operand = throws(&parsed)[0].1;
    let mut checker = context(&parsed, true);
    start(&mut checker, &run, operand, QueryOrder::BodyRead);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let error = bootstrap.error_type;
    let never = bootstrap.never_type;
    assert_eq!(checker.get_type_at_location(operand), Ok(error));
    assert_eq!(callable_state(&mut checker, &parsed, &run).returned, never);
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].diagnostic.code(), 2304);
    assert_eq!(diagnostics[0].node, Some(operand));
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "Cannot find name 'missing'."
    );
    replay(&mut checker, &parsed, &[&run], &[operand]);
}

fn assert_catch_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    catch: CatchBinding,
    expected: &[u32],
) {
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(
        diagnostics
            .iter()
            .map(|entry| entry.diagnostic.code())
            .collect::<Vec<_>>(),
        expected,
        "{source}: {diagnostics:?}"
    );
    for diagnostic in diagnostics {
        let code = diagnostic.diagnostic.code();
        let (anchor, text, message) = match code {
            1196 => (
                catch.annotation.unwrap(),
                "number",
                "Catch clause variable type annotation must be 'any' or 'unknown' if specified.",
            ),
            1197 => {
                let initializer = catch.initializer.unwrap();
                let text = match &parsed.arena.get(initializer.node).unwrap().data {
                    NodeData::CallExpression(_) => "accept",
                    NodeData::Identifier(_) => "missing",
                    NodeData::NumericLiteral(_) => "1",
                    _ => panic!("unexpected initializer in this grammar control"),
                };
                (
                    initializer,
                    text,
                    "Catch clause variable cannot have an initializer.",
                )
            }
            2492 => (
                binding(parsed, "error").declaration,
                "error",
                "Cannot redeclare identifier 'error' in catch clause.",
            ),
            2304 => (
                catch.initializer.unwrap(),
                "missing",
                "Cannot find name 'missing'.",
            ),
            2345 => {
                let initializer = catch.initializer.unwrap();
                let NodeData::CallExpression(call) =
                    &parsed.arena.get(initializer.node).unwrap().data
                else {
                    panic!("the argument error must come from the real initializer call");
                };
                (
                    child(parsed, initializer, call.arguments.nodes[0]),
                    "'bad'",
                    "Argument of type 'string' is not assignable to parameter of type 'number'.",
                )
            }
            _ => panic!("unexpected catch diagnostic {code}"),
        };
        assert_eq!(diagnostic.node, Some(anchor));
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
        let range = diagnostic.range_override.map_or_else(
            || parsed.arena.get(anchor.node).unwrap().range,
            |range| {
                assert_eq!(range.anchor(), anchor);
                range.range()
            },
        );
        let start = usize::try_from(range.start.get()).unwrap();
        let end = usize::try_from(range.end.get()).unwrap();
        assert_eq!(&source[start..end], text);
        if code == 1196 && text_at(source, parsed, anchor) != text {
            let annotation = parsed.arena.get(anchor.node).unwrap();
            assert_eq!(annotation.kind, SyntaxKind::UnionType);
            assert_eq!(text_at(source, parsed, anchor), "number | string");
            assert_eq!(diagnostic.range_override.unwrap().anchor(), anchor);
            assert_eq!(range.start, annotation.range.start);
            assert!(range.end < annotation.range.end);
        }
        if matches!(code, 2304 | 2345) {
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(text_at(source, parsed, anchor), text);
        }
    }
}

#[test]
fn catch_grammar_errors_keep_expression_order_real_locations_and_replay() {
    for (declaration, body, expected) in [
        ("error: number", "", vec![1196]),
        ("error: number | string", "", vec![1196]),
        ("error = missing", "", vec![2304, 1197]),
        ("error: number = missing", "", vec![2304, 1196]),
        ("error = accept('bad')", "", vec![2345, 1197]),
        ("error: number = accept('bad')", "", vec![2345, 1196]),
        ("error: number = 'text'", "", vec![1196]),
        ("error", "const error = 1;", vec![2492]),
        ("error = 1", "const error = 1;", vec![1197]),
        ("error: any = missing", "const error = 1;", vec![2304]),
        ("error: unknown", "const error = 1;", vec![]),
    ] {
        let source = format!(
            "declare function accept(value: number): number;\nconst run = (): void => {{ try {{}} catch ({declaration}) {{ {body} }} }};"
        );
        let parsed = parse_source_file(&source);
        let parser_diagnostics = parsed.diagnostics.clone();
        assert!(parser_diagnostics.is_empty());
        let run = callable(&parsed, "run");
        let catch_bindings = catches(&parsed);
        let [catch] = catch_bindings.as_slice() else {
            panic!("expected one actual catch");
        };
        let catch = *catch;
        for order in [QueryOrder::Source, QueryOrder::Callable, QueryOrder::BodyRead] {
            let mut checker = context(&parsed, true);
            let first = catch.initializer.unwrap_or(catch.name);
            start(&mut checker, &run, first, order);
            assert_catch_diagnostics(&checker, &parsed, &source, catch, &expected);
            let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
            let void = bootstrap.void_type;
            let number = bootstrap.number_type;
            let error = bootstrap.error_type;
            let entry = if declaration.starts_with("error: number") {
                error
            } else if declaration.starts_with("error: any") {
                bootstrap.any_type
            } else {
                bootstrap.unknown_type
            };
            catch_owner(&mut checker, &parsed, &run, catch, entry);
            assert_eq!(callable_state(&mut checker, &parsed, &run).returned, void);
            let mut locations = vec![catch.name];
            if let Some(initializer) = catch.initializer {
                let actual = checker.get_type_at_location(initializer).unwrap();
                match &parsed.arena.get(initializer.node).unwrap().data {
                    NodeData::Identifier(_) => assert_eq!(actual, error),
                    NodeData::CallExpression(_) => assert_eq!(actual, number),
                    NodeData::StringLiteral(_) => {
                        assert_eq!(checker.type_to_string(actual).unwrap(), "\"text\"");
                        assert_ne!(actual, entry);
                    }
                    NodeData::NumericLiteral(_) => {
                        assert_eq!(checker.type_to_string(actual).unwrap(), "1");
                        assert_ne!(actual, entry);
                    }
                    _ => panic!("expected the actual malformed catch initializer"),
                }
                locations.push(initializer);
            }
            if !body.is_empty() {
                let redeclared = binding(&parsed, "error");
                assert_ne!(
                    symbol(&checker, redeclared.declaration),
                    symbol(&checker, catch.declaration)
                );
                let local_type = checker.get_type_at_location(redeclared.name).unwrap();
                assert_eq!(checker.type_to_string(local_type).unwrap(), "1");
                locations.push(redeclared.name);
            }
            replay(&mut checker, &parsed, &[&run], &locations);
            assert_eq!(parsed.diagnostics, parser_diagnostics);
        }
    }
}

#[test]
fn selected_try_with_finally_keeps_incomplete_flow_and_typed_refusal() {
    let source = "const run = (value: string): string => { try { return value; } catch { throw 'stop'; } finally {} };";
    let parsed = parse_source_file(source);
    let run = callable(&parsed, "run");
    assert_eq!(top_level_kinds(&parsed, &run), vec![SyntaxKind::TryStatement]);
    let mut checker = context(&parsed, true);
    assert_eq!(
        checker.file(FILE).unwrap().1.flow_graph().container_is_complete(run.declaration),
        Some(false)
    );
    let before = publication(&checker, &parsed);
    let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(run.body));
    for _ in 0..2 {
        assert_eq!(checker.recheck_source_file(FILE), Err(error));
        assert!(!checked(&checker));
        assert_eq!(publication(&checker, &parsed), before);
    }
}
