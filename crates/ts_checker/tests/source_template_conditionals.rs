use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalGlobalTypes, DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks, SignatureLinks,
    SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::LiteralValue, types::TypeFlags,
};
use ts_diagnostics::Category;
use ts_jsnum::Number;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(61_470);
const LIBRARY: FileId = FileId::new(61_471);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const PRELUDE: &str = concat!(
    "type Case = [path: string, glob: string, expected: boolean, todo?: boolean];\n",
    "declare const cases: Case[];\n",
);
const TITLE: &str = r#"const title = `${JSON.stringify(path)} ${expected ? "matches" : "does not match"} ${JSON.stringify(glob)}`;"#;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Form {
    Original,
    NumericArm,
    WrittenMismatch,
}

impl Form {
    fn source(self) -> String {
        let title = match self {
            Self::Original => TITLE.to_owned(),
            Self::NumericArm => TITLE.replace("\"does not match\"", "0"),
            Self::WrittenMismatch => TITLE.replace("const title =", "const title: number ="),
        };
        format!("{PRELUDE}for (const [path, glob, expected, todo] of cases) {{\n  {title}\n}}\n")
    }
}

#[derive(Clone, Copy, Debug)]
enum Order {
    SourceFirst,
    ConditionalFirst,
    TemplateFirst,
}

fn context<'a>(source: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, source, "\"/project/template-conditionals.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, is_library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    is_library,
                    is_library,
                    if is_library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
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
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
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

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let owner = parsed.arena.get(parent.node).unwrap();
    let record = parsed.arena.get(id).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, parent.file, id)
}

fn identifier(parsed: &ParseResult, location: NodeRef) -> &str {
    let NodeData::Identifier(name) = &parsed.arena.get(location.node).unwrap().data else {
        panic!("expected the actual identifier");
    };
    &name.text
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, FILE, id)));
    let result = found.next().expect("expected this source node");
    assert!(found.next().is_none(), "expected one {kind:?}");
    result
}

#[derive(Clone, Copy)]
struct Binding {
    declaration: NodeRef,
    name: NodeRef,
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
        panic!("expected the loop declaration");
    };
    assert!(variable.type_.is_none());
    assert!(variable.initializer.is_none());
    let pattern = child(parsed, declaration, variable.name);
    assert_eq!(
        parsed.arena.get(pattern.node).unwrap().kind,
        SyntaxKind::ArrayBindingPattern
    );
    let NodeData::BindingPattern(data) = &parsed.arena.get(pattern.node).unwrap().data else {
        unreachable!();
    };
    let elements: [NodeId; 4] = data.elements.nodes.as_slice().try_into().unwrap();
    std::array::from_fn(|index| {
        let declaration = child(parsed, pattern, elements[index]);
        let NodeData::BindingElement(element) = &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected the actual binding element");
        };
        assert!(element.dot_dot_dot_token.is_none());
        assert!(element.initializer.is_none());
        assert!(element.property_name.is_none());
        let name = child(parsed, declaration, element.name.unwrap());
        assert_eq!(
            identifier(parsed, name),
            ["path", "glob", "expected", "todo"][index]
        );
        Binding { declaration, name }
    })
}

struct Call {
    expression: NodeRef,
    callee: NodeRef,
    receiver: NodeRef,
    member: NodeRef,
    argument: NodeRef,
}

fn json_call(parsed: &ParseResult, expression: NodeRef, argument_name: &str) -> Call {
    let NodeData::CallExpression(call) = &parsed.arena.get(expression.node).unwrap().data else {
        panic!("expected the actual JSON.stringify call");
    };
    let callee = child(parsed, expression, call.expression);
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(callee.node).unwrap().data
    else {
        panic!("expected the actual JSON method access");
    };
    let receiver = child(parsed, callee, property.expression);
    let member = child(parsed, callee, property.name);
    assert_eq!(identifier(parsed, receiver), "JSON");
    assert_eq!(identifier(parsed, member), "stringify");
    let [argument] = call.arguments.nodes.as_slice() else {
        panic!("expected the original single JSON argument");
    };
    let argument = child(parsed, expression, *argument);
    assert_eq!(identifier(parsed, argument), argument_name);
    Call {
        expression,
        callee,
        receiver,
        member,
        argument,
    }
}

struct CaseNodes {
    iteration: NodeRef,
    body: NodeRef,
    bindings: [Binding; 4],
    title: Binding,
    annotation: Option<NodeRef>,
    template: NodeRef,
    span: NodeRef,
    conditional: NodeRef,
    condition: NodeRef,
    when_true: NodeRef,
    when_false: NodeRef,
    calls: [Call; 2],
}

fn title(parsed: &ParseResult, body: NodeRef) -> (Binding, Option<NodeRef>, NodeRef) {
    let NodeData::Block(block) = &parsed.arena.get(body.node).unwrap().data else {
        panic!("expected the loop body");
    };
    let [statement] = block.statements.nodes.as_slice() else {
        panic!("expected the copied title declaration");
    };
    let statement = child(parsed, body, *statement);
    let NodeData::VariableStatement(data) = &parsed.arena.get(statement.node).unwrap().data else {
        panic!("expected the title statement");
    };
    let list = child(parsed, statement, data.declaration_list);
    let NodeData::VariableDeclarationList(data) = &parsed.arena.get(list.node).unwrap().data else {
        unreachable!();
    };
    let [declaration] = data.declarations.nodes.as_slice() else {
        panic!("expected one title declaration");
    };
    let declaration = child(parsed, list, *declaration);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let name = child(parsed, declaration, data.name);
    assert_eq!(identifier(parsed, name), "title");
    (
        Binding { declaration, name },
        data.type_.map(|id| child(parsed, declaration, id)),
        child(parsed, declaration, data.initializer.unwrap()),
    )
}

fn case_nodes(parsed: &ParseResult) -> CaseNodes {
    let iteration = only(parsed, SyntaxKind::ForOfStatement);
    let NodeData::ForInOrOfStatement(loop_) = &parsed.arena.get(iteration.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        identifier(parsed, child(parsed, iteration, loop_.expression)),
        "cases"
    );
    let body = child(parsed, iteration, loop_.statement);
    let (title, annotation, template) = title(parsed, body);
    assert_eq!(template, only(parsed, SyntaxKind::TemplateExpression));
    let NodeData::TemplateExpression(data) = &parsed.arena.get(template.node).unwrap().data else {
        panic!("the initializer must keep its complete template");
    };
    let spans: [NodeId; 3] = data.template_spans.nodes.as_slice().try_into().unwrap();
    let substitutions: [(NodeRef, NodeRef); 3] = std::array::from_fn(|index| {
        let span = child(parsed, template, spans[index]);
        let NodeData::TemplateSpan(data) = &parsed.arena.get(span.node).unwrap().data else {
            panic!("expected a real template span");
        };
        let literal = child(parsed, span, data.literal);
        assert_eq!(
            parsed.arena.get(literal.node).unwrap().kind,
            if index == 2 {
                SyntaxKind::TemplateTail
            } else {
                SyntaxKind::TemplateMiddle
            }
        );
        (span, child(parsed, span, data.expression))
    });
    let (span, conditional) = substitutions[1];
    assert_eq!(conditional, only(parsed, SyntaxKind::ConditionalExpression));
    let NodeData::ConditionalExpression(data) = &parsed.arena.get(conditional.node).unwrap().data
    else {
        unreachable!();
    };
    let condition = child(parsed, conditional, data.condition);
    assert_eq!(identifier(parsed, condition), "expected");
    CaseNodes {
        iteration,
        body,
        bindings: loop_bindings(parsed, iteration),
        title,
        annotation,
        template,
        span,
        conditional,
        condition,
        when_true: child(parsed, conditional, data.when_true),
        when_false: child(parsed, conditional, data.when_false),
        calls: [
            json_call(parsed, substitutions[0].1, "path"),
            json_call(parsed, substitutions[2].1, "glob"),
        ],
    }
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

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("the checked declaration must retain its actual type")
}

fn cached_type(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .expect("source checking must retain this expression result")
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ArmValue {
    Text(String),
    Zero,
}

fn literal(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> ArmValue {
    let record = checker.store().type_payload(type_).unwrap();
    let TypeData::Literal(data) = record.data() else {
        panic!("expected the actual literal type, not a widened or error type");
    };
    match &data.value {
        LiteralValue::String(value) => {
            assert!(record.flags().intersects(TypeFlags::STRING_LITERAL));
            ArmValue::Text(value.clone())
        }
        LiteralValue::Number(value) => {
            assert!(record.flags().intersects(TypeFlags::NUMBER_LITERAL));
            assert_eq!(value, &Number::from_string("0"));
            ArmValue::Zero
        }
        _ => panic!("expected a string literal or the exact numeric zero"),
    }
}

fn assert_union(checker: &CanonicalCheckerContext<'_>, type_: TypeId, form: Form) {
    let record = checker.store().type_payload(type_).unwrap();
    assert!(record.flags().intersects(TypeFlags::UNION));
    let TypeData::Union(data) = record.data() else {
        panic!("expected both conditional result arms");
    };
    assert_eq!(data.union.types.len(), 2);
    let mut actual = data
        .union
        .types
        .iter()
        .map(|&type_| literal(checker, type_))
        .collect::<Vec<_>>();
    let mut expected = vec![
        ArmValue::Text("matches".into()),
        match form {
            Form::NumericArm => ArmValue::Zero,
            Form::Original | Form::WrittenMismatch => ArmValue::Text("does not match".into()),
        },
    ];
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected);
}

fn assert_tuple(parsed: &ParseResult) {
    let tuple = only(parsed, SyntaxKind::TupleType);
    let NodeData::TupleTypeNode(data) = &parsed.arena.get(tuple.node).unwrap().data else {
        unreachable!();
    };
    assert_eq!(data.elements.nodes.len(), 4);
    for (index, &id) in data.elements.nodes.iter().enumerate() {
        let location = child(parsed, tuple, id);
        let NodeData::NamedTupleMember(member) = &parsed.arena.get(id).unwrap().data else {
            panic!("expected the original named tuple member");
        };
        assert_eq!(
            identifier(parsed, child(parsed, location, member.name)),
            ["path", "glob", "expected", "todo"][index]
        );
        assert_eq!(member.question_token.is_some(), index == 3);
        assert!(member.dot_dot_dot_token.is_none());
        let type_ = child(parsed, location, member.type_);
        assert_eq!(
            parsed.arena.get(type_.node).unwrap().kind,
            if index < 2 {
                SyntaxKind::StringKeyword
            } else {
                SyntaxKind::BooleanKeyword
            }
        );
    }
}

fn assert_binding(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    binding: Binding,
    block_scope: NodeRef,
    expected: TypeId,
) -> SemanticSymbolId {
    let owner = symbol(checker, binding.declaration);
    let source = node(parsed, FILE, parsed.source_file);
    let bound = checker.file(FILE).unwrap().1;
    assert_eq!(bound.container(binding.declaration), Some(source));
    assert_eq!(
        bound.block_scope_container(binding.declaration),
        Some(block_scope)
    );
    let locals = bound
        .locals(block_scope)
        .expect("the real lexical scope must own its binding");
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
    assert_eq!(value_type(checker, owner), expected);
    assert_eq!(checker.get_type_at_location(binding.name), Ok(expected));
    assert_eq!(
        checker.get_symbol_at_location(binding.name),
        Ok(Some(owner))
    );
    owner
}

fn assert_loop_flow(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    nodes: &CaseNodes,
) {
    let source = node(parsed, FILE, parsed.source_file);
    let bound = checker.file(FILE).unwrap().1;
    let graph = bound.flow_graph();
    assert_eq!(graph.container_is_complete(source), Some(true));
    let mut flow = bound
        .flow_at(nodes.calls[0].receiver)
        .expect("the first JSON read needs real incoming flow");
    for binding in nodes.bindings.iter().rev() {
        let assignment = graph.nodes().get(flow).unwrap();
        assert!(assignment.flags.contains(FlowFlags::ASSIGNMENT));
        assert_eq!(
            assignment.payload,
            Some(FlowNodePayload::Ast(binding.declaration))
        );
        flow = assignment
            .antecedent
            .expect("each loop binding follows the previous flow");
    }
    assert!(
        graph
            .nodes()
            .get(flow)
            .unwrap()
            .flags
            .contains(FlowFlags::LOOP_LABEL)
    );
    for location in [
        nodes.calls[0].receiver,
        nodes.condition,
        nodes.calls[1].receiver,
    ] {
        assert_eq!(bound.flow_container(location), Some(source));
        let point = bound
            .flow_at(location)
            .expect("the actual reference must have a flow point");
        assert!(graph.nodes().get(point).is_some());
    }
    assert_eq!(bound.container(nodes.conditional), Some(source));
    assert_eq!(
        bound.block_scope_container(nodes.conditional),
        Some(nodes.body)
    );
    assert_eq!(
        parsed.arena.get(nodes.conditional.node).unwrap().parent,
        Some(nodes.span.node)
    );
}

struct JsonProvider {
    declaration: NodeRef,
    interface: NodeRef,
    methods: Vec<NodeRef>,
}

fn json_provider(library: &ParseResult) -> JsonProvider {
    let mut declarations = Vec::new();
    let mut interfaces = Vec::new();
    for (id, record) in library.arena.iter() {
        let name = match &record.data {
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::InterfaceDeclaration(data) => data.name,
            _ => continue,
        };
        let NodeData::Identifier(name) = &library.arena.get(name).unwrap().data else {
            continue;
        };
        if name.text == "JSON" {
            let location = node(library, LIBRARY, id);
            if record.kind == SyntaxKind::VariableDeclaration {
                declarations.push(location);
            } else {
                interfaces.push(location);
            }
        }
    }
    let [declaration] = declarations.as_slice() else {
        panic!("expected the real global JSON declaration");
    };
    let [interface] = interfaces.as_slice() else {
        panic!("expected the real JSON interface");
    };
    let mut methods = library
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &library.arena.get(method.name)?.data else {
                return None;
            };
            (record.parent == Some(interface.node) && name.text == "stringify")
                .then_some(node(library, LIBRARY, id))
        })
        .collect::<Vec<_>>();
    methods.sort_by_key(|location| library.arena.get(location.node).unwrap().range.start);
    assert_eq!(methods.len(), 2);
    JsonProvider {
        declaration: *declaration,
        interface: *interface,
        methods,
    }
}

fn assert_json_call(
    checker: &mut CanonicalCheckerContext<'_>,
    library: &ParseResult,
    provider: &JsonProvider,
    call: &Call,
    argument_owner: SemanticSymbolId,
) {
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
    let json_owner = symbol(checker, provider.declaration);
    assert_eq!(
        checker.get_symbol_at_location(call.receiver),
        Ok(Some(json_owner))
    );
    assert_eq!(
        checker.get_symbol_at_location(call.argument),
        Ok(Some(argument_owner))
    );
    assert_eq!(checker.get_type_at_location(call.argument), Ok(string));
    assert_eq!(cached_type(checker, call.expression), string);
    assert_eq!(checker.get_type_at_location(call.expression), Ok(string));
    let signature = checker
        .store()
        .signature_links(call.expression)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the real JSON call must have a checked signature");
    let signature = checker.store().signature(signature).unwrap();
    let declaration = signature
        .declaration()
        .expect("the signature must retain its library declaration");
    assert!(provider.methods.contains(&declaration));
    assert_eq!(declaration.file, LIBRARY);
    assert_eq!(
        library.arena.get(declaration.node).unwrap().parent,
        Some(provider.interface.node)
    );
    assert!(signature.type_parameters().is_empty());
    assert_eq!(signature.min_argument_count(), 1);
    assert_eq!(signature.resolved_return_type(), Some(string));
    let NodeData::MethodSignatureDeclaration(method) =
        &library.arena.get(declaration.node).unwrap().data
    else {
        panic!("the signature must use a real ES5 method");
    };
    assert_eq!(signature.parameters().len(), 3);
    assert_eq!(method.parameters.nodes.len(), 3);
    for (index, (&parameter, &id)) in signature
        .parameters()
        .iter()
        .zip(&method.parameters.nodes)
        .enumerate()
    {
        let parameter_node = child(library, declaration, id);
        assert_eq!(
            checker
                .store()
                .symbol(parameter)
                .unwrap()
                .value_declaration(),
            Some(parameter_node)
        );
        if index == 0 {
            assert_eq!(value_type(checker, parameter), any);
        }
    }
    let method_owner = symbol(checker, declaration);
    assert_eq!(
        checker.get_symbol_at_location(call.member),
        Ok(Some(method_owner))
    );
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    nodes: &CaseNodes,
    form: Form,
) {
    if form != Form::WrittenMismatch {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        return;
    }
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!(
            "expected exactly one assignment error: {:?}",
            checker.diagnostics()
        );
    };
    assert_eq!(diagnostic.node, Some(nodes.title.name));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    let start = source.find("title: number").unwrap();
    let range = parsed.arena.get(nodes.title.name.node).unwrap().range;
    assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
    assert_eq!(
        usize::try_from(range.end.get()).unwrap(),
        start + "title".len()
    );
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
struct SymbolState {
    symbol: SemanticSymbolId,
    value: Option<ValueSymbolLinks>,
    declared: Option<DeclaredTypeLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    globals: CanonicalGlobalTypes,
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
    flow: String,
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    library: &ParseResult,
) -> Snapshot {
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
            store.type_resolution_len(),
        ],
        globals: checker.global_types().clone(),
        nodes: [(FILE, parsed), (LIBRARY, library)]
            .into_iter()
            .flat_map(|(file, parsed)| {
                parsed.arena.iter().map(move |(id, _)| {
                    let location = node(parsed, file, id);
                    NodeState {
                        node: location,
                        common: store.node_links(location).cloned(),
                        type_: store.type_node_links(location).cloned(),
                        symbol: store.symbol_node_links(location).cloned(),
                        signature: store.signature_links(location).cloned(),
                    }
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| SymbolState {
                symbol,
                value: store.value_symbol_links(symbol).cloned(),
                declared: store.declared_type_links(symbol).cloned(),
            })
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: checker.diagnostics().clone(),
        flow: format!("{:?}", checker.file(FILE).unwrap().1.flow_graph()),
    }
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    library: &ParseResult,
    queries: &[NodeRef],
) {
    let queries = queries
        .iter()
        .map(|&location| {
            (
                location,
                checker.get_type_at_location(location).unwrap(),
                checker.get_symbol_at_location(location).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let before = snapshot(checker, parsed, library);
    let relation = checker.store().relation_state_snapshot();
    let resolution_start = checker.store().type_resolution_start();
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for &(location, type_, owner) in &queries {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(location), Ok(owner));
        }
        assert_eq!(snapshot(checker, parsed, library), before);
        assert_eq!(checker.store().relation_state_snapshot(), relation);
        assert_eq!(checker.store().type_resolution_start(), resolution_start);
    }
}

fn assert_checked(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    library: &ParseResult,
    nodes: &CaseNodes,
    form: Form,
) -> Vec<NodeRef> {
    let (string, number, boolean) = {
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        )
    };
    let union = cached_type(checker, nodes.conditional);
    assert_union(checker, union, form);
    assert_eq!(cached_type(checker, nodes.template), string);
    // Conditional operands deliberately stay uncached until queried separately.
    for location in [nodes.condition, nodes.when_true, nodes.when_false] {
        assert!(checker.store().type_node_links(location).is_none());
    }
    let mut owners = Vec::new();
    for (index, binding) in nodes.bindings.iter().copied().enumerate() {
        let expected = if index < 2 {
            string
        } else if index == 2 {
            boolean
        } else {
            let type_ = value_type(checker, symbol(checker, binding.declaration));
            assert_eq!(
                checker.type_to_string(type_).unwrap(),
                "boolean | undefined"
            );
            type_
        };
        owners.push(assert_binding(
            checker,
            parsed,
            binding,
            nodes.iteration,
            expected,
        ));
    }
    assert!(
        owners
            .iter()
            .enumerate()
            .all(|(index, owner)| !owners[..index].contains(owner))
    );
    let title_type = if form == Form::WrittenMismatch {
        number
    } else {
        string
    };
    let title_owner = assert_binding(checker, parsed, nodes.title, nodes.body, title_type);
    assert!(!owners.contains(&title_owner));
    match nodes.annotation {
        Some(annotation) => {
            assert_eq!(form, Form::WrittenMismatch);
            assert_eq!(checker.get_type_at_location(annotation), Ok(number));
        }
        None => assert_ne!(form, Form::WrittenMismatch),
    }
    assert_eq!(checker.get_type_at_location(nodes.condition), Ok(boolean));
    assert_eq!(
        checker.get_symbol_at_location(nodes.condition),
        Ok(Some(owners[2]))
    );
    let when_true = checker.get_type_at_location(nodes.when_true).unwrap();
    let when_false = checker.get_type_at_location(nodes.when_false).unwrap();
    assert_eq!(
        literal(checker, when_true),
        ArmValue::Text("matches".into())
    );
    assert_eq!(
        literal(checker, when_false),
        if form == Form::NumericArm {
            ArmValue::Zero
        } else {
            ArmValue::Text("does not match".into())
        }
    );
    assert_eq!(checker.get_type_at_location(nodes.conditional), Ok(union));
    assert_eq!(checker.get_type_at_location(nodes.template), Ok(string));
    let provider = json_provider(library);
    for (call, owner) in nodes.calls.iter().zip(&owners) {
        assert_json_call(checker, library, &provider, call, *owner);
    }
    assert_loop_flow(checker, parsed, nodes);
    let mut queries = vec![
        nodes.title.name,
        nodes.template,
        nodes.conditional,
        nodes.condition,
        nodes.when_true,
        nodes.when_false,
    ];
    queries.extend(nodes.bindings.iter().map(|binding| binding.name));
    queries.extend(nodes.annotation);
    for call in &nodes.calls {
        queries.extend([
            call.expression,
            call.callee,
            call.receiver,
            call.member,
            call.argument,
        ]);
    }
    queries
}

fn run(form: Form) {
    let source = form.source();
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ES5);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_tuple(&parsed);
    let nodes = case_nodes(&parsed);
    for order in [
        Order::SourceFirst,
        Order::ConditionalFirst,
        Order::TemplateFirst,
    ] {
        let mut checker = context(&parsed, &library);
        let source_node = checker.source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(source_node)
                .is_none_or(|links| !links.type_checked)
        );
        let cold_node = match order {
            Order::SourceFirst => None,
            Order::ConditionalFirst => Some(nodes.conditional),
            Order::TemplateFirst => Some(nodes.template),
        };
        let cold =
            cold_node.map(|location| (location, checker.get_type_at_location(location).unwrap()));
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(source_node)
                .is_some_and(|links| links.type_checked)
        );
        assert_diagnostics(&checker, &parsed, &source, &nodes, form);
        let queries = assert_checked(&mut checker, &parsed, &library, &nodes, form);
        if let Some((location, type_)) = cold {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
        }
        assert_diagnostics(&checker, &parsed, &source, &nodes, form);
        replay(&mut checker, &parsed, &library, &queries);
        assert_diagnostics(&checker, &parsed, &source, &nodes, form);
    }
}

#[test]
fn for_of_template_conditional_keeps_literal_arms_and_replays() {
    run(Form::Original);
}

#[test]
fn for_of_template_conditional_does_not_inherit_string_context() {
    run(Form::NumericArm);
}

#[test]
fn for_of_template_conditional_reports_the_written_title_mismatch() {
    run(Form::WrittenMismatch);
}
