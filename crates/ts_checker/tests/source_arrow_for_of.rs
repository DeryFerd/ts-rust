use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, MappedSymbolLinks, NodeLinks, SignatureId, SignatureLinks,
    SourceFileLinks, SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId, TypeMapperId,
    TypeNodeLinks, ValueSymbolLinks, signatures::SignatureFlags, type_records::ObjectTypeData,
    types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(8_240);
const IMPORTER: FileId = FileId::new(8_241);
const PROVIDER: FileId = FileId::new(8_242);
const ARRAY_LIBRARY: &str = "interface Array<T> { [n: number]: T; } interface ReadonlyArray<T> { readonly [n: number]: T; }";
const CALL_SOURCE: &str = concat!(
    "function consume(value: number): void {}\n",
    "export default (values: number[], wrong: string): void => {\n",
    "  for (const item of values) { consume(item); consume(wrong); }\n",
    "};\n",
);

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().expect("expected this source node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        let name_node = match &record.data {
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::FunctionDeclaration(data) => data.name?,
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
            return None;
        };
        (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().expect("expected the named declaration");
    assert!(nodes.next().is_none(), "expected one declaration of {name}");
    node
}

fn default_arrow(parsed: &ParseResult) -> NodeRef {
    let export = only_node(parsed, PROVIDER, SyntaxKind::ExportAssignment);
    let NodeData::ExportAssignment(data) = &parsed.arena.get(export.node).unwrap().data else {
        unreachable!()
    };
    assert!(!data.is_export_equals);
    NodeRef::new(parsed.arena.id(), PROVIDER, data.expression)
}

fn context<'arena>(files: &[(FileId, &'arena ParseResult)]) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let path = match file {
            LIBRARY => "\"/project/lib.d.ts\"",
            IMPORTER => "\"/project/importer.ts\"",
            PROVIDER => "\"/project/provider.ts\"",
            _ => unreachable!(),
        };
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
                ),
            )
            .unwrap();
    }
    for &(file, parsed) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = files
        .iter()
        .filter(|(file, _)| *file == IMPORTER)
        .map(|&(file, parsed)| {
            let import = only_node(parsed, file, SyntaxKind::ImportDeclaration);
            let NodeData::ImportDeclaration(data) = &parsed.arena.get(import.node).unwrap().data
            else {
                unreachable!()
            };
            CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(parsed.arena.id(), file, data.module_specifier),
                CanonicalResolvedModuleInput::new(
                    PROVIDER,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
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

fn cached_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature_at(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn object<'checker>(
    checker: &'checker CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'checker ObjectTypeData {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the checked object type")
    };
    object
}

fn array_element(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::TypeReference(array) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the canonical array reference")
    };
    assert_eq!(array.object.target, Some(checker.global_types().array_type));
    let [element] = array.resolved_type_arguments.as_deref().unwrap() else {
        panic!("expected one checked array element type")
    };
    *element
}

fn checked(checker: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureState {
    id: SignatureId,
    declaration: Option<NodeRef>,
    flags: SignatureFlags,
    type_parameters: Vec<TypeId>,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
}

fn signature_state(checker: &CanonicalCheckerContext<'_>, id: SignatureId) -> SignatureState {
    let signature = checker.store().signature(id).unwrap();
    SignatureState {
        id,
        declaration: signature.declaration(),
        flags: signature.flags(),
        type_parameters: signature.type_parameters().to_vec(),
        parameters: signature
            .parameters()
            .iter()
            .map(|&symbol| (symbol, value_type(checker, symbol)))
            .collect(),
        returned: signature.resolved_return_type().unwrap(),
        target: signature.target(),
        mapper: signature.mapper(),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct ArrowState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureState,
}

fn arrow_state(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> ArrowState {
    let (arena, bound) = checker.file(declaration.file).unwrap();
    let record = arena.get(declaration.node).unwrap();
    let NodeData::ArrowFunction(arrow) = &record.data else {
        panic!("expected an actual arrow declaration")
    };
    let binding_node = NodeRef::new(declaration.arena, declaration.file, record.parent.unwrap());
    let owner = symbol(checker, declaration);
    let binding = symbol(checker, binding_node);
    assert_ne!(owner, binding);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    assert_eq!(owner_record.parent(), None);
    let expected_binding_flags = match arena.get(binding_node.node).unwrap().kind {
        SyntaxKind::ExportAssignment => SymbolFlags::PROPERTY,
        SyntaxKind::VariableDeclaration => SymbolFlags::BLOCK_SCOPED_VARIABLE,
        _ => panic!("expected a distinct export or local variable owner"),
    };
    let binding_record = checker.store().symbol(binding).unwrap();
    assert_eq!(binding_record.flags(), expected_binding_flags);
    assert_eq!(binding_record.declarations(), Some(&[binding_node][..]));
    assert_eq!(binding_record.value_declaration(), Some(binding_node));
    let type_ = value_type(checker, owner);
    assert_eq!(value_type(checker, binding), type_);
    assert_eq!(
        checker.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    let callable = object(checker, type_);
    let signature = signature_state(checker, signature_at(checker, declaration));
    assert_eq!(
        callable.structured.signatures.as_deref(),
        Some(&[signature.id][..])
    );
    assert_eq!(callable.structured.call_signature_count, 1);
    assert_eq!(callable.target, None);
    assert_eq!(callable.mapper, None);
    assert_eq!(signature.declaration, Some(declaration));
    assert_eq!(signature.flags, SignatureFlags::NONE);
    assert_eq!(signature.target, None);
    assert_eq!(signature.mapper, None);
    let parameters = arrow
        .parameters
        .nodes
        .iter()
        .map(|&node| {
            let parameter = NodeRef::new(declaration.arena, declaration.file, node);
            assert_eq!(bound.container(parameter), Some(declaration));
            symbol(checker, parameter)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        signature
            .parameters
            .iter()
            .map(|&(symbol, _)| symbol)
            .collect::<Vec<_>>(),
        parameters
    );
    let type_parameters = arrow
        .type_parameters
        .as_ref()
        .into_iter()
        .flat_map(|parameters| &parameters.nodes)
        .map(|&node| {
            let declaration = NodeRef::new(declaration.arena, declaration.file, node);
            let owner = symbol(checker, declaration);
            let type_ = checker
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let record = checker.store().type_payload(type_).unwrap();
            assert_eq!(record.symbol(), Some(owner));
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            let TypeData::TypeParameter(parameter) = record.data() else {
                unreachable!()
            };
            assert_eq!(parameter.target, None);
            assert_eq!(parameter.mapper, None);
            type_
        })
        .collect::<Vec<_>>();
    assert_eq!(signature.type_parameters, type_parameters);
    ArrowState {
        owner,
        binding,
        type_,
        signature,
    }
}

struct Iteration {
    statement: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    iterable: NodeRef,
    expressions: Vec<NodeRef>,
}

fn iteration(parsed: &ParseResult) -> Iteration {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), PROVIDER, node);
    let statement = only_node(parsed, PROVIDER, SyntaxKind::ForOfStatement);
    let NodeData::ForInOrOfStatement(data) = &parsed.arena.get(statement.node).unwrap().data else {
        unreachable!()
    };
    assert!(data.await_modifier.is_none());
    let NodeData::VariableDeclarationList(list) = &parsed.arena.get(data.initializer).unwrap().data
    else {
        panic!("expected the original lexical iteration binding")
    };
    let [declaration] = list.declarations.nodes.as_slice() else {
        panic!("expected one loop binding")
    };
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(*declaration).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(data.statement).unwrap().data else {
        panic!("expected the original loop block")
    };
    Iteration {
        statement,
        declaration: node_ref(*declaration),
        name: node_ref(variable.name),
        iterable: node_ref(data.expression),
        expressions: body
            .statements
            .nodes
            .iter()
            .map(|&node| {
                let NodeData::ExpressionStatement(statement) =
                    &parsed.arena.get(node).unwrap().data
                else {
                    panic!("these controls contain only loop expression statements")
                };
                node_ref(statement.expression)
            })
            .collect(),
    }
}

fn assert_iteration_owner(
    checker: &CanonicalCheckerContext<'_>,
    iteration: &Iteration,
    callable: NodeRef,
    element: TypeId,
) -> SemanticSymbolId {
    let (arena, bound) = checker.file(PROVIDER).unwrap();
    let owner = symbol(checker, iteration.declaration);
    assert_eq!(bound.container(iteration.declaration), Some(callable));
    assert_eq!(
        bound.block_scope_container(iteration.declaration),
        Some(iteration.statement)
    );
    let NodeData::Identifier(name) = &arena.get(iteration.name.node).unwrap().data else {
        unreachable!()
    };
    let locals = bound.locals(iteration.statement).unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(locals)
            .unwrap()
            .get_source(&name.text),
        Some(owner)
    );
    assert_eq!(value_type(checker, owner), element);
    owner
}

type Artifact = (NodeRef, TypeId, Option<SemanticSymbolId>);

fn query_artifacts(checker: &mut CanonicalCheckerContext<'_>, artifacts: &[Artifact]) {
    for &(node, type_, symbol) in artifacts {
        assert_eq!(
            checker.get_type_at_location(node),
            Ok(type_),
            "type at {node:?}"
        );
        assert_eq!(
            checker.get_symbol_at_location(node),
            Ok(symbol),
            "symbol at {node:?}"
        );
    }
}

#[derive(Debug, Eq, PartialEq)]
struct NodeCache {
    node: NodeRef,
    flags: Option<NodeLinks>,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct SymbolCache {
    symbol: SemanticSymbolId,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
    alias: Option<AliasSymbolLinks>,
    type_alias: Option<TypeAliasLinks>,
    mapped: Option<MappedSymbolLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    nodes: Vec<NodeCache>,
    symbols: Vec<SymbolCache>,
    files: Vec<(FileId, Option<SourceFileLinks>)>,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, files: &[(FileId, &ParseResult)]) -> Snapshot {
    let store = checker.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: files
            .iter()
            .flat_map(|&(file, parsed)| {
                parsed.arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    NodeCache {
                        node,
                        flags: store.node_links(node).cloned(),
                        type_: store.type_node_links(node).cloned(),
                        symbol: store.symbol_node_links(node).cloned(),
                        signature: store.signature_links(node).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolCache {
                symbol,
                value: store.value_symbol_links(symbol).cloned(),
                declared: store.declared_type_links(symbol).cloned(),
                alias: store.alias_symbol_links(symbol).cloned(),
                type_alias: store.type_alias_links(symbol).cloned(),
                mapped: store.mapped_symbol_links(symbol).cloned(),
            })
            .collect(),
        files: files
            .iter()
            .map(|&(file, _)| {
                (
                    file,
                    store
                        .source_file_links(checker.source_file(file).unwrap())
                        .cloned(),
                )
            })
            .collect(),
    }
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    order: &[FileId],
    artifacts: &[Artifact],
    signatures: &[SignatureState],
) {
    query_artifacts(checker, artifacts);
    let before = snapshot(checker, files);
    let diagnostics = checker.diagnostics().clone();
    for _ in 0..2 {
        for &file in order {
            checker.recheck_source_file(file).unwrap();
            assert!(checked(checker, file));
        }
        query_artifacts(checker, artifacts);
        for signature in signatures {
            assert_eq!(
                checker.get_return_type_of_signature(signature.id),
                Ok(signature.returned)
            );
            assert_eq!(signature_state(checker, signature.id), *signature);
        }
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(snapshot(checker, files), before);
    }
}

fn assert_call_body(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> (Vec<Artifact>, Vec<SignatureState>) {
    assert!(checked(checker, PROVIDER));
    let node_ref = |node| NodeRef::new(parsed.arena.id(), PROVIDER, node);
    let arrow = default_arrow(parsed);
    let state = arrow_state(checker, arrow);
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let void = bootstrap.void_type;
    assert!(state.signature.type_parameters.is_empty());
    assert_eq!(state.signature.returned, void);
    let [(values_symbol, values_type), (wrong_symbol, wrong_type)] =
        state.signature.parameters.as_slice()
    else {
        panic!("expected the two original arrow parameters")
    };
    assert_eq!(array_element(checker, *values_type), number);
    assert_eq!(*wrong_type, string);
    let iteration = iteration(parsed);
    let item = assert_iteration_owner(checker, &iteration, arrow, number);
    assert_ne!(item, *values_symbol);
    assert_ne!(item, *wrong_symbol);
    assert_eq!(cached_type(checker, iteration.iterable), *values_type);
    let consume = declaration(parsed, PROVIDER, "consume");
    let consume_symbol = symbol(checker, consume);
    let consume_type = value_type(checker, consume_symbol);
    let consume_signature = signature_state(checker, signature_at(checker, consume));
    assert_eq!(consume_signature.declaration, Some(consume));
    assert_eq!(consume_signature.parameters.len(), 1);
    assert_eq!(consume_signature.parameters[0].1, number);
    assert_eq!(consume_signature.returned, void);
    let [correct, incorrect] = iteration.expressions.as_slice() else {
        panic!("expected both original calls")
    };
    let mut artifacts = vec![
        (arrow, state.type_, None),
        (iteration.name, number, Some(item)),
        (iteration.iterable, *values_type, Some(*values_symbol)),
    ];
    let mut wrong_read = None;
    for (&call, argument_type, argument_symbol) in
        [(correct, number, item), (incorrect, string, *wrong_symbol)]
    {
        let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
            panic!("expected a real source call")
        };
        let [argument] = data.arguments.nodes.as_slice() else {
            panic!("expected one original argument")
        };
        let callee = node_ref(data.expression);
        let argument = node_ref(*argument);
        assert_eq!(cached_type(checker, callee), consume_type);
        assert_eq!(cached_type(checker, argument), argument_type);
        assert_eq!(cached_type(checker, call), void);
        assert_eq!(signature_at(checker, call), consume_signature.id);
        artifacts.extend([
            (callee, consume_type, Some(consume_symbol)),
            (argument, argument_type, Some(argument_symbol)),
            (call, void, None),
        ]);
        if call == *incorrect {
            wrong_read = Some(argument);
        }
    }
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!(
            "expected one wrong-argument diagnostic: {:?}",
            checker.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
    assert_eq!(diagnostic.node, wrong_read);
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    (artifacts, vec![state.signature, consume_signature])
}

#[test]
fn default_arrow_for_of_checks_calls_and_the_wrong_argument() {
    let library = parse_source_file(ARRAY_LIBRARY);
    let provider = parse_source_file(CALL_SOURCE);
    let files = [(LIBRARY, &library), (PROVIDER, &provider)];
    let mut checker = context(&files);
    checker.check_source_file(PROVIDER).unwrap();
    let (artifacts, signatures) = assert_call_body(&checker, &provider);
    replay(&mut checker, &files, &[PROVIDER], &artifacts, &signatures);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the lexical T, mapped property, body call, and replay in one control.
fn nested_for_of_observer_call_keeps_the_outer_type_parameter() {
    let library = parse_source_file(ARRAY_LIBRARY);
    let provider = parse_source_file(concat!(
        "type Observer<T> = { next: (value: T) => void; };\n",
        "export default <T>(seed: T, _observers: Observer<T>[]): T => {\n",
        "  const next = (value: T) => {\n",
        "    for (const observer of _observers) {\n",
        "      observer.next && observer.next(value);\n",
        "    }\n",
        "  };\n",
        "  return seed;\n",
        "};\n",
    ));
    let files = [(LIBRARY, &library), (PROVIDER, &provider)];
    let mut checker = context(&files);
    checker.check_source_file(PROVIDER).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let node_ref = |node| NodeRef::new(provider.arena.id(), PROVIDER, node);
    let outer = default_arrow(&provider);
    let outer_state = arrow_state(&checker, outer);
    let [t] = outer_state.signature.type_parameters.as_slice() else {
        panic!("expected the factory's own T")
    };
    let t = *t;
    let t_symbol = checker.store().type_payload(t).unwrap().symbol().unwrap();
    let [(seed, seed_type), (observers, observers_type)] =
        outer_state.signature.parameters.as_slice()
    else {
        panic!("expected the original factory parameters")
    };
    assert_eq!(*seed_type, t);
    assert_eq!(outer_state.signature.returned, t);
    let element_type = array_element(&checker, *observers_type);
    let next = declaration(&provider, PROVIDER, "next");
    let NodeData::VariableDeclaration(next_data) = &provider.arena.get(next.node).unwrap().data
    else {
        unreachable!()
    };
    let child = node_ref(next_data.initializer.unwrap());
    let child_state = arrow_state(&checker, child);
    assert_ne!(child_state.owner, outer_state.owner);
    assert_ne!(child_state.binding, outer_state.binding);
    assert!(child_state.signature.type_parameters.is_empty());
    let [(value, parameter_type)] = child_state.signature.parameters.as_slice() else {
        panic!("expected the child's value parameter")
    };
    assert_ne!(*value, *seed);
    assert_eq!(*parameter_type, t);
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(child_state.signature.returned, void);
    let NodeData::ArrowFunction(child_data) = &provider.arena.get(child.node).unwrap().data else {
        unreachable!()
    };
    assert!(child_data.type_.is_none());
    assert!(child_data.type_parameters.is_none());
    let NodeData::ParameterDeclaration(parameter) = &provider
        .arena
        .get(child_data.parameters.nodes[0])
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let annotation = node_ref(parameter.type_.unwrap());
    assert_eq!(cached_type(&checker, annotation), t);
    assert_eq!(
        checker
            .store()
            .symbol_node_links(annotation)
            .unwrap()
            .resolved_symbol,
        Some(t_symbol)
    );
    let iteration = iteration(&provider);
    let observer = assert_iteration_owner(&checker, &iteration, child, element_type);
    assert_ne!(observer, *observers);
    assert_ne!(observer, *value);
    assert_eq!(cached_type(&checker, iteration.iterable), *observers_type);

    let alias = symbol(&checker, declaration(&provider, PROVIDER, "Observer"));
    let alias_links = checker.store().type_alias_links(alias).unwrap();
    let template = alias_links.declared_type.unwrap();
    let [alias_t] = alias_links.type_parameters.as_deref().unwrap() else {
        panic!("expected the alias's separate T")
    };
    assert_ne!(*alias_t, t);
    let instance = object(&checker, element_type);
    assert_eq!(instance.target, Some(template));
    let mapper = instance.mapper.unwrap();
    let property = checker
        .store()
        .symbol_table(instance.structured.members.unwrap())
        .unwrap()
        .get_source("next")
        .unwrap();
    let template_owner = checker
        .store()
        .type_payload(template)
        .unwrap()
        .symbol()
        .unwrap();
    let source_property = checker
        .store()
        .symbol(template_owner)
        .unwrap()
        .members()
        .and_then(|members| checker.store().symbol_table(members))
        .and_then(|members| members.get_source("next"))
        .unwrap();
    assert_eq!(
        source_property,
        symbol(
            &checker,
            only_node(&provider, PROVIDER, SyntaxKind::PropertyDeclaration)
        )
    );
    assert_ne!(property, source_property);
    assert_eq!(
        checker.store().symbol(property).unwrap().flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
    );
    assert_eq!(
        checker.store().symbol(source_property).unwrap().parent(),
        Some(template_owner)
    );
    let source_callable = value_type(&checker, source_property);
    let callable = value_type(&checker, property);
    assert_eq!(object(&checker, callable).target, Some(source_callable));
    assert_eq!(object(&checker, callable).mapper, Some(mapper));
    let [source_signature] = object(&checker, source_callable)
        .structured
        .signatures
        .as_deref()
        .unwrap()
    else {
        panic!("expected the original property signature")
    };
    let [mapped_signature] = object(&checker, callable)
        .structured
        .signatures
        .as_deref()
        .unwrap()
    else {
        panic!("expected the mapped property signature")
    };
    let source_signature = signature_state(&checker, *source_signature);
    let mapped_signature = signature_state(&checker, *mapped_signature);
    assert_eq!(
        source_signature.declaration,
        Some(only_node(&provider, PROVIDER, SyntaxKind::FunctionType))
    );
    assert!(source_signature.type_parameters.is_empty());
    assert_eq!(mapped_signature.target, Some(source_signature.id));
    assert_eq!(mapped_signature.mapper, Some(mapper));
    assert_eq!(mapped_signature.declaration, source_signature.declaration);
    assert!(mapped_signature.type_parameters.is_empty());
    assert_eq!(mapped_signature.parameters.len(), 1);
    assert_eq!(mapped_signature.parameters[0].1, t);
    assert_ne!(mapped_signature.parameters[0].0, *value);
    assert_eq!(mapped_signature.returned, void);
    assert_eq!(source_signature.parameters.len(), 1);
    assert_eq!(source_signature.parameters[0].1, *alias_t);
    let [logical] = iteration.expressions.as_slice() else {
        panic!("expected the original logical statement")
    };
    let NodeData::BinaryExpression(binary) = &provider.arena.get(logical.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(
        provider.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::AmpersandAmpersandToken
    );
    let call = node_ref(binary.right);
    let NodeData::CallExpression(call_data) = &provider.arena.get(call.node).unwrap().data else {
        panic!("expected observer.next(value)")
    };
    let [argument] = call_data.arguments.nodes.as_slice() else {
        panic!("expected the original value argument")
    };
    let argument = node_ref(*argument);
    assert_eq!(cached_type(&checker, argument), t);
    assert_eq!(cached_type(&checker, call), void);
    assert_eq!(signature_at(&checker, call), mapped_signature.id);
    let mut artifacts = vec![
        (outer, outer_state.type_, None),
        (child, child_state.type_, None),
        (
            node_ref(next_data.name),
            child_state.type_,
            Some(child_state.binding),
        ),
        (node_ref(parameter.name), t, Some(*value)),
        (annotation, t, Some(t_symbol)),
        (iteration.name, element_type, Some(observer)),
        (iteration.iterable, *observers_type, Some(*observers)),
        (argument, t, Some(*value)),
        (call, void, None),
    ];
    for access in [node_ref(binary.left), node_ref(call_data.expression)] {
        let NodeData::PropertyAccessExpression(property_data) =
            &provider.arena.get(access.node).unwrap().data
        else {
            panic!("expected each original observer.next access")
        };
        assert_eq!(cached_type(&checker, access), callable);
        assert_eq!(
            checker
                .store()
                .symbol_node_links(access)
                .unwrap()
                .resolved_symbol,
            Some(property)
        );
        let receiver = node_ref(property_data.expression);
        assert_eq!(cached_type(&checker, receiver), element_type);
        artifacts.extend([
            (access, callable, Some(property)),
            (node_ref(property_data.name), callable, Some(property)),
            (receiver, element_type, Some(observer)),
        ]);
    }
    let returned = only_node(&provider, PROVIDER, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(returned) = &provider.arena.get(returned.node).unwrap().data
    else {
        unreachable!()
    };
    let returned = node_ref(returned.expression.unwrap());
    assert_eq!(cached_type(&checker, returned), t);
    artifacts.push((returned, t, Some(*seed)));
    replay(
        &mut checker,
        &files,
        &[PROVIDER],
        &artifacts,
        &[
            outer_state.signature,
            child_state.signature,
            source_signature,
            mapped_signature,
        ],
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Keep signature-only import demand separate from actual body checking.
fn imported_for_of_signature_stays_cold_until_provider_check() {
    let library = parse_source_file(ARRAY_LIBRARY);
    let importer = parse_source_file("import iterate from './provider'; const copy = iterate;");
    let provider = parse_source_file(CALL_SOURCE);
    let files = [
        (LIBRARY, &library),
        (IMPORTER, &importer),
        (PROVIDER, &provider),
    ];
    let mut checker = context(&files);
    let arrow = default_arrow(&provider);
    let iteration = iteration(&provider);
    let import = only_node(&importer, IMPORTER, SyntaxKind::ImportClause);
    let alias = symbol(&checker, import);
    checker.check_source_file(IMPORTER).unwrap();
    assert!(checked(&checker, IMPORTER));
    assert!(!checked(&checker, PROVIDER));
    assert!(checker.diagnostics().is_empty());
    let before_body = arrow_state(&checker, arrow);
    assert_ne!(alias, before_body.owner);
    assert_ne!(alias, before_body.binding);
    assert_eq!(value_type(&checker, alias), before_body.type_);
    let alias_links = checker.store().alias_symbol_links(alias).cloned().unwrap();
    assert_eq!(alias_links.immediate_target, Some(before_body.binding));
    assert_eq!(
        alias_links.alias_target,
        AliasTargetState::Resolved(before_body.binding)
    );
    assert_eq!(alias_links.type_only_declaration, None);
    let module = symbol(&checker, checker.file(PROVIDER).unwrap().1.source_file());
    assert_eq!(
        checker
            .store()
            .symbol(before_body.binding)
            .unwrap()
            .parent(),
        Some(module)
    );
    let exports = checker.store().symbol(module).unwrap().exports().unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(exports)
            .unwrap()
            .get_source("default"),
        Some(before_body.binding)
    );
    let before_query = snapshot(&checker, &files);
    assert_eq!(
        checker.get_return_type_of_signature(before_body.signature.id),
        Ok(before_body.signature.returned)
    );
    assert_eq!(snapshot(&checker, &files), before_query);
    assert!(!checked(&checker, PROVIDER));
    assert!(checker.store().type_node_links(arrow).is_none());
    assert!(
        checker
            .store()
            .value_symbol_links(symbol(&checker, iteration.declaration))
            .is_none()
    );
    let node_ref = |node| NodeRef::new(provider.arena.id(), PROVIDER, node);
    let mut cold_body_nodes = vec![
        iteration.statement,
        iteration.declaration,
        iteration.name,
        iteration.iterable,
    ];
    for &call in &iteration.expressions {
        let NodeData::CallExpression(data) = &provider.arena.get(call.node).unwrap().data else {
            panic!("expected the original loop call")
        };
        cold_body_nodes.extend([call, node_ref(data.expression)]);
        cold_body_nodes.extend(data.arguments.nodes.iter().copied().map(node_ref));
    }
    for node in cold_body_nodes {
        assert!(checker.store().type_node_links(node).is_none());
        assert!(checker.store().symbol_node_links(node).is_none());
        assert!(checker.store().signature_links(node).is_none());
    }
    let consume = declaration(&provider, PROVIDER, "consume");
    assert!(checker.store().signature_links(consume).is_none());
    checker.check_source_file(PROVIDER).unwrap();
    assert_eq!(arrow_state(&checker, arrow), before_body);
    let (mut artifacts, signatures) = assert_call_body(&checker, &provider);
    let NodeData::ImportClause(clause) = &importer.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    let copy = declaration(&importer, IMPORTER, "copy");
    let NodeData::VariableDeclaration(copy_data) = &importer.arena.get(copy.node).unwrap().data
    else {
        unreachable!()
    };
    artifacts.extend([
        (
            NodeRef::new(importer.arena.id(), IMPORTER, clause.name.unwrap()),
            before_body.type_,
            Some(alias),
        ),
        (
            NodeRef::new(importer.arena.id(), IMPORTER, copy_data.name),
            before_body.type_,
            Some(symbol(&checker, copy)),
        ),
    ]);
    replay(
        &mut checker,
        &files,
        &[IMPORTER, PROVIDER],
        &artifacts,
        &signatures,
    );
    assert_eq!(
        checker.store().alias_symbol_links(alias),
        Some(&alias_links)
    );
}
