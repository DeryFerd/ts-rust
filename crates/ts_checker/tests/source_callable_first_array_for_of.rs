use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, NodeLinks, SignatureId, SignatureLinks, SourceCheckError,
    SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(58_760);
const LIBRARY: FileId = FileId::new(58_761);
const ARRAY_LIBRARY: &str = concat!(
    "interface Array<T> { [n: number]: T; }\n",
    "interface ReadonlyArray<T> { readonly [n: number]: T; }\n",
);
const PRELUDE: &str = concat!(
    "type Row = [path: string, glob: string, expected: boolean, todo?: boolean];\n",
    "declare const cases: Row[];\n",
    "declare function suite(title: string, body: () => void): void;\n",
    "declare function takeString(value: string): void;\n",
    "declare function takeBoolean(value: boolean): void;\n",
);
const LOOP_BODY: &str = concat!(
    "  for (const [path, glob, expected, todo] of cases) {\n",
    "    const title: string = path;\n",
    "    if (todo) {\n",
    "      takeString(title);\n",
    "    } else {\n",
    "      suite(title, () => {\n",
    "        takeString(glob);\n",
    "        takeBoolean(expected);\n",
    "        takeBoolean(path);\n",
    "      });\n",
    "    }\n",
    "  }\n",
);

#[derive(Clone, Copy, Debug)]
enum Form {
    Function,
    InlineArrow,
}

fn source(form: Form) -> String {
    match form {
        Form::Function => format!("{PRELUDE}function run(): void {{\n{LOOP_BODY}}}\n"),
        Form::InlineArrow => format!("{PRELUDE}suite(\"outer\", () => {{\n{LOOP_BODY}}});\n"),
    }
}

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, default_library, name) in [
        (LIBRARY, library, true, "\"/project/lib.d.ts\""),
        (
            FILE,
            parsed,
            false,
            "\"/project/callable-first-array-for-of.ts\"",
        ),
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

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)));
    let result = matches.next().expect("expected this source node");
    assert!(matches.next().is_none(), "expected one {kind:?}");
    result
}

fn identifier(parsed: &ParseResult, location: NodeRef) -> &str {
    let NodeData::Identifier(name) = &parsed.arena.get(location.node).unwrap().data else {
        panic!("expected an identifier");
    };
    &name.text
}

fn statements(parsed: &ParseResult, block: NodeRef) -> Vec<NodeRef> {
    let NodeData::Block(body) = &parsed.arena.get(block.node).unwrap().data else {
        panic!("expected the actual callable or statement block");
    };
    body.statements
        .nodes
        .iter()
        .map(|&id| child(parsed, block, id))
        .collect()
}

fn expression(parsed: &ParseResult, statement: NodeRef) -> NodeRef {
    let NodeData::ExpressionStatement(data) = &parsed.arena.get(statement.node).unwrap().data
    else {
        panic!("expected an expression statement");
    };
    child(parsed, statement, data.expression)
}

fn arguments(parsed: &ParseResult, call: NodeRef, name: &str) -> Vec<NodeRef> {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected an ordinary call expression");
    };
    assert_eq!(
        identifier(parsed, child(parsed, call, data.expression)),
        name
    );
    data.arguments
        .nodes
        .iter()
        .map(|&id| child(parsed, call, id))
        .collect()
}

#[derive(Clone, Copy)]
struct Callable {
    declaration: NodeRef,
    body: NodeRef,
}

fn callable(parsed: &ParseResult, declaration: NodeRef) -> Callable {
    let (body, parameters) = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::FunctionDeclaration(function) => {
            (function.body.unwrap(), &function.parameters.nodes)
        }
        NodeData::ArrowFunction(arrow) => (arrow.body, &arrow.parameters.nodes),
        _ => panic!("expected the real function or arrow declaration"),
    };
    assert!(parameters.is_empty());
    Callable {
        declaration,
        body: child(parsed, declaration, body),
    }
}

#[derive(Clone, Copy)]
struct Binding {
    declaration: NodeRef,
    name: NodeRef,
}

struct CaseNodes {
    outer: Callable,
    nested: Callable,
    iteration: NodeRef,
    bindings: [Binding; 4],
    annotations: [NodeRef; 4],
    title: Binding,
    title_annotation: NodeRef,
    title_input: NodeRef,
    title_reads: [NodeRef; 2],
    todo_read: NodeRef,
    nested_reads: [NodeRef; 3],
}

fn tuple_annotations(parsed: &ParseResult) -> [NodeRef; 4] {
    let tuple = only_node(parsed, SyntaxKind::TupleType);
    let NodeData::TupleTypeNode(data) = &parsed.arena.get(tuple.node).unwrap().data else {
        panic!("expected the written Row tuple");
    };
    let elements: [NodeId; 4] = data.elements.nodes.as_slice().try_into().unwrap();
    let names = ["path", "glob", "expected", "todo"];
    std::array::from_fn(|index| {
        let element = child(parsed, tuple, elements[index]);
        let NodeData::NamedTupleMember(member) = &parsed.arena.get(element.node).unwrap().data
        else {
            panic!("expected a named tuple member");
        };
        assert_eq!(
            identifier(parsed, child(parsed, element, member.name)),
            names[index]
        );
        assert_eq!(member.question_token.is_some(), index == 3);
        assert!(member.dot_dot_dot_token.is_none());
        child(parsed, element, member.type_)
    })
}

fn loop_bindings(parsed: &ParseResult, iteration: NodeRef) -> [Binding; 4] {
    let NodeData::ForInOrOfStatement(loop_) = &parsed.arena.get(iteration.node).unwrap().data
    else {
        panic!("expected the actual for-of statement");
    };
    assert!(loop_.await_modifier.is_none());
    let list = child(parsed, iteration, loop_.initializer);
    let NodeData::VariableDeclarationList(data) = &parsed.arena.get(list.node).unwrap().data else {
        panic!("expected the lexical declaration list");
    };
    let [declaration] = data.declarations.nodes.as_slice() else {
        panic!("expected one array-pattern declaration");
    };
    let declaration = child(parsed, list, *declaration);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected the actual loop declaration");
    };
    assert!(variable.type_.is_none());
    assert!(variable.initializer.is_none());
    let pattern = child(parsed, declaration, variable.name);
    let record = parsed.arena.get(pattern.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::ArrayBindingPattern);
    let NodeData::BindingPattern(data) = &record.data else {
        panic!("expected the flat array binding pattern");
    };
    let elements: [NodeId; 4] = data.elements.nodes.as_slice().try_into().unwrap();
    let names = ["path", "glob", "expected", "todo"];
    std::array::from_fn(|index| {
        let declaration = child(parsed, pattern, elements[index]);
        let NodeData::BindingElement(element) = &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected an actual BindingElement");
        };
        assert!(element.dot_dot_dot_token.is_none());
        assert!(element.initializer.is_none());
        assert!(element.property_name.is_none());
        let name = child(parsed, declaration, element.name.unwrap());
        assert_eq!(identifier(parsed, name), names[index]);
        Binding { declaration, name }
    })
}

#[allow(clippy::too_many_lines)] // Keep the loop, branch, and callback syntax checks together.
fn case_nodes(parsed: &ParseResult) -> CaseNodes {
    let iteration = only_node(parsed, SyntaxKind::ForOfStatement);
    let body = node(
        parsed,
        parsed.arena.get(iteration.node).unwrap().parent.unwrap(),
    );
    let declaration = node(parsed, parsed.arena.get(body.node).unwrap().parent.unwrap());
    let outer = callable(parsed, declaration);
    assert_eq!(outer.body, body);
    assert_eq!(statements(parsed, outer.body), [iteration]);

    let NodeData::ForInOrOfStatement(loop_) = &parsed.arena.get(iteration.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        identifier(parsed, child(parsed, iteration, loop_.expression)),
        "cases"
    );
    let loop_body = child(parsed, iteration, loop_.statement);
    let body_statements = statements(parsed, loop_body);
    let [local_statement, if_statement] = body_statements.as_slice() else {
        panic!("expected the local title and the if statement");
    };
    let NodeData::VariableStatement(local) = &parsed.arena.get(local_statement.node).unwrap().data
    else {
        panic!("expected the title declaration statement");
    };
    let list = child(parsed, *local_statement, local.declaration_list);
    let NodeData::VariableDeclarationList(local) = &parsed.arena.get(list.node).unwrap().data
    else {
        unreachable!();
    };
    let [title] = local.declarations.nodes.as_slice() else {
        panic!("expected one title binding");
    };
    let declaration = child(parsed, list, *title);
    let NodeData::VariableDeclaration(title) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let title_binding = Binding {
        declaration,
        name: child(parsed, declaration, title.name),
    };
    assert_eq!(identifier(parsed, title_binding.name), "title");
    let title_annotation = child(parsed, declaration, title.type_.unwrap());
    let title_input = child(parsed, declaration, title.initializer.unwrap());
    assert_eq!(identifier(parsed, title_input), "path");

    let NodeData::IfStatement(branch) = &parsed.arena.get(if_statement.node).unwrap().data else {
        panic!("expected the original todo branch");
    };
    let todo_read = child(parsed, *if_statement, branch.expression);
    assert_eq!(identifier(parsed, todo_read), "todo");
    let then_block = child(parsed, *if_statement, branch.then_statement);
    let then_statements = statements(parsed, then_block);
    let [then_statement] = then_statements.as_slice() else {
        panic!("expected one call in the true branch");
    };
    let then_arguments = arguments(parsed, expression(parsed, *then_statement), "takeString");
    let [then_title] = then_arguments.as_slice() else {
        panic!("expected one title argument");
    };

    let else_block = child(parsed, *if_statement, branch.else_statement.unwrap());
    let else_statements = statements(parsed, else_block);
    let [suite_statement] = else_statements.as_slice() else {
        panic!("expected the suite call in the false branch");
    };
    let suite_arguments = arguments(parsed, expression(parsed, *suite_statement), "suite");
    let [suite_title, nested] = suite_arguments.as_slice() else {
        panic!("expected the title and the actual callback");
    };
    let nested = callable(parsed, *nested);
    assert_eq!(
        parsed.arena.get(nested.declaration.node).unwrap().kind,
        SyntaxKind::ArrowFunction
    );
    let calls: [NodeRef; 3] = statements(parsed, nested.body).try_into().unwrap();
    let call_names = ["takeString", "takeBoolean", "takeBoolean"];
    let nested_reads = std::array::from_fn(|index| {
        let args = arguments(parsed, expression(parsed, calls[index]), call_names[index]);
        let [argument] = args.as_slice() else {
            panic!("expected one captured argument");
        };
        *argument
    });
    for (read, expected) in nested_reads.iter().zip(["glob", "expected", "path"]) {
        assert_eq!(identifier(parsed, *read), expected);
    }
    for read in [*then_title, *suite_title] {
        assert_eq!(identifier(parsed, read), "title");
    }

    CaseNodes {
        outer,
        nested,
        iteration,
        bindings: loop_bindings(parsed, iteration),
        annotations: tuple_annotations(parsed),
        title: title_binding,
        title_annotation,
        title_input,
        title_reads: [*then_title, *suite_title],
        todo_read,
        nested_reads,
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

fn read(
    checker: &mut CanonicalCheckerContext<'_>,
    location: NodeRef,
    owner: SemanticSymbolId,
    type_: TypeId,
) {
    assert_eq!(checker.get_type_at_location(location), Ok(type_));
    assert_eq!(checker.get_symbol_at_location(location), Ok(Some(owner)));
}

#[derive(Debug, Eq, PartialEq)]
struct CallableState {
    owner: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    returned: TypeId,
}

fn callable_state(checker: &mut CanonicalCheckerContext<'_>, callable: Callable) -> CallableState {
    let owner = symbol(checker, callable.declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[callable.declaration][..]));
    assert_eq!(record.value_declaration(), Some(callable.declaration));
    let type_ = checker.get_type_at_location(callable.declaration).unwrap();
    assert_eq!(value_type(checker, owner), type_);
    let signature = checker
        .store()
        .signature_links(callable.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let payload = checker.store().type_payload(type_).unwrap();
    assert_eq!(payload.symbol(), Some(owner));
    let TypeData::Object(object) = payload.data() else {
        panic!("expected the callable's own object type");
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let signature_record = checker.store().signature(signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(callable.declaration));
    assert!(signature_record.parameters().is_empty());
    assert!(signature_record.type_parameters().is_empty());
    assert_eq!(signature_record.min_argument_count(), 0);
    assert!(!signature_record.has_rest_parameter());
    assert_eq!(signature_record.this_parameter(), None);
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    assert_eq!(signature_record.resolved_return_type(), Some(returned));
    assert_eq!(checker.type_to_string(returned).unwrap(), "void");
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
    }
}

fn binding_owner(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    binding: Binding,
    nodes: &CaseNodes,
) -> SemanticSymbolId {
    let owner = symbol(checker, binding.declaration);
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(
        bound.container(binding.declaration),
        Some(nodes.outer.declaration)
    );
    assert_eq!(
        bound.block_scope_container(binding.declaration),
        Some(nodes.iteration)
    );
    let locals = bound.locals(nodes.iteration).unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(locals)
            .unwrap()
            .get_source(identifier(parsed, binding.name)),
        Some(owner)
    );
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[binding.declaration][..]));
    assert_eq!(record.value_declaration(), Some(binding.declaration));
    assert!(bound.flow_at(binding.name).is_some());
    owner
}

fn binding_flow(checker: &CanonicalCheckerContext<'_>, nodes: &CaseNodes) {
    let (_, bound) = checker.file(FILE).unwrap();
    let graph = bound.flow_graph();
    let mut flow = bound.flow_at(nodes.title_input).unwrap();
    for binding in nodes.bindings.iter().rev() {
        let assignment = graph.nodes().get(flow).unwrap();
        assert!(assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(
            assignment.payload,
            Some(FlowNodePayload::Ast(binding.declaration))
        );
        flow = assignment.antecedent.unwrap();
    }
    assert!(
        graph
            .nodes()
            .get(flow)
            .unwrap()
            .flags
            .contains(FlowFlags::LOOP_LABEL)
    );
    assert_eq!(
        bound.flow_container(nodes.title_input),
        Some(nodes.outer.declaration)
    );
}

#[allow(clippy::too_many_lines)] // Verify the element types and both callback owners as one case.
fn verify(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &CaseNodes,
) -> [CallableState; 2] {
    binding_flow(checker, nodes);
    let annotated = nodes
        .annotations
        .map(|annotation| checker.get_type_from_type_node(annotation).unwrap());
    for (type_, display) in annotated
        .iter()
        .zip(["string", "string", "boolean", "boolean"])
    {
        assert_eq!(checker.type_to_string(*type_).unwrap(), display);
    }
    assert_eq!(annotated[0], annotated[1]);
    assert_eq!(annotated[2], annotated[3]);
    let owners = nodes
        .bindings
        .map(|binding| binding_owner(checker, parsed, binding, nodes));
    for (index, binding) in nodes.bindings.iter().enumerate().take(3) {
        assert_eq!(value_type(checker, owners[index]), annotated[index]);
        read(checker, binding.name, owners[index], annotated[index]);
    }

    let todo = checker
        .get_type_at_location(nodes.bindings[3].name)
        .unwrap();
    assert_eq!(value_type(checker, owners[3]), todo);
    assert_eq!(checker.type_to_string(todo).unwrap(), "boolean | undefined");
    let TypeData::Union(union) = checker.store().type_payload(todo).unwrap().data() else {
        panic!("the optional tuple element must retain undefined");
    };
    let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
    assert_eq!(annotated[2], intrinsics.boolean_type);
    assert_eq!(union.union.types.len(), 3);
    for member in [
        intrinsics.regular_false_type,
        intrinsics.regular_true_type,
        intrinsics.undefined_type,
    ] {
        assert!(union.union.types.contains(&member));
    }
    read(checker, nodes.bindings[3].name, owners[3], todo);
    read(checker, nodes.todo_read, owners[3], todo);
    read(checker, nodes.title_input, owners[0], annotated[0]);
    for (read_node, index) in nodes.nested_reads.iter().zip([1, 2, 0]) {
        read(checker, *read_node, owners[index], annotated[index]);
        let (_, bound) = checker.file(FILE).unwrap();
        assert_eq!(bound.container(*read_node), Some(nodes.nested.declaration));
        assert_eq!(
            bound.flow_container(*read_node),
            Some(nodes.nested.declaration)
        );
    }

    let title_owner = symbol(checker, nodes.title.declaration);
    assert_eq!(value_type(checker, title_owner), annotated[0]);
    assert_eq!(
        checker
            .get_type_from_type_node(nodes.title_annotation)
            .unwrap(),
        annotated[0]
    );
    read(checker, nodes.title.name, title_owner, annotated[0]);
    for title_read in nodes.title_reads {
        read(checker, title_read, title_owner, annotated[0]);
    }

    let outer = callable_state(checker, nodes.outer);
    let nested = callable_state(checker, nodes.nested);
    assert_ne!(outer.owner, nested.owner);
    assert_ne!(outer.type_, nested.type_);
    assert_ne!(outer.signature, nested.signature);
    for owner in owners {
        assert_ne!(owner, outer.owner);
        assert_ne!(owner, nested.owner);
    }

    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected exactly the bad captured path argument");
    };
    assert_eq!(diagnostic.node, Some(nodes.nested_reads[2]));
    assert_eq!(diagnostic.diagnostic.code(), 2_345);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "boolean"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'boolean'."
    );
    let expected_range = parsed.arena.get(nodes.nested_reads[2].node).unwrap().range;
    let actual_range = diagnostic
        .range_override
        .map_or(expected_range, |range| range.range());
    assert_eq!(actual_range, expected_range);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(checker.store().type_resolution_len(), 0);
    [outer, nested]
}

fn checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
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

#[derive(Clone, Copy, Debug)]
enum QueryOrder {
    Source,
    BodyRead,
    Callable,
}

fn check_case(form: Form, order: QueryOrder) {
    let source = source(form);
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ARRAY_LIBRARY);
    let nodes = case_nodes(&parsed);
    let mut checker = context(&parsed, &library);
    assert!(!checked(&checker));
    assert!(
        checker
            .store()
            .signature_links(nodes.outer.declaration)
            .is_none()
    );
    let first_location = match order {
        QueryOrder::Source => None,
        QueryOrder::BodyRead => Some(nodes.nested_reads[0]),
        QueryOrder::Callable => Some(nodes.outer.declaration),
    };
    let first = first_location.map(|location| {
        let type_ = checker.get_type_at_location(location).unwrap();
        (location, type_)
    });
    checker.check_source_file(FILE).unwrap();
    assert!(checked(&checker));
    if let Some((location, type_)) = first {
        assert_eq!(checker.get_type_at_location(location), Ok(type_));
    }
    let states = verify(&mut checker, &parsed, &nodes);
    let before = publication(&checker, &parsed);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        assert_eq!(
            verify(&mut checker, &parsed, &nodes),
            states,
            "{form:?}, {order:?}"
        );
        assert_eq!(
            publication(&checker, &parsed),
            before,
            "{form:?}, {order:?}"
        );
    }
}

#[test]
fn ordinary_function_first_array_loop_checks_captured_bindings() {
    check_case(Form::Function, QueryOrder::Source);
}

#[test]
fn inline_arrow_first_array_loop_keeps_distinct_callback_owners() {
    check_case(Form::InlineArrow, QueryOrder::Source);
}

#[test]
fn first_array_loop_cold_queries_and_warm_replay_keep_identity() {
    for form in [Form::Function, Form::InlineArrow] {
        for order in [QueryOrder::BodyRead, QueryOrder::Callable] {
            check_case(form, order);
        }
    }
}

#[test]
fn first_array_loop_rejects_nested_loop_in_the_same_callable() {
    let parsed = parse_source_file(concat!(
        "function run(values: [string][]): void {\n",
        "  for (const [value] of values) {\n",
        "    for (const [next] of values) {}\n",
        "  }\n",
        "}\n",
    ));
    let library = parse_source_file(ARRAY_LIBRARY);
    let mut checker = context(&parsed, &library);
    let before = publication(&checker, &parsed);
    let error = checker.check_source_file(FILE).unwrap_err();
    assert!(matches!(error, SourceCheckError::Unsupported(_)));
    assert!(!checked(&checker));
    assert_eq!(publication(&checker, &parsed), before);
}
