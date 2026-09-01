use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalGlobalTypes, DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks, SignatureId,
    SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
    ValueSymbolLinks, signatures::SignatureFlags, type_records::LiteralValue,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(58_521);
const FILE: FileId = FileId::new(58_522);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

const COMPILE: &str = r#"const compile = (_glob?: string | string[], _options?: { partial?: boolean }): unknown => {
  throw new Error("compile() is not ported");
};
"#;

const PARSE: &str = r#"interface State {
  input: string;
  index: number;
  output: any[];
}

type Rule = (state: State) => boolean;

const parse = (input: string, rule: Rule): any[] => {
  const state: State = { input, index: 0, output: [] };
  if (rule(state) && state.index === input.length) {
    return state.output;
  }
  throw new Error(`Failed to parse at index ${state.index}`);
};
"#;

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (
            FILE,
            source,
            "\"/project/callable-throw-project-forms.ts\"",
            false,
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
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
            strict_function_types: true,
            no_implicit_any: true,
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

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, FILE, id)))
        .collect::<Vec<_>>();
    found.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    found
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let found = nodes(parsed, kind);
    let [found] = found.as_slice() else {
        panic!("expected one {kind:?}, got {found:?}");
    };
    *found
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    let found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::PropertySignatureDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [found] = found.as_slice() else {
        panic!("expected one {kind:?} named {expected}, got {found:?}");
    };
    *found
}

struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: NodeRef,
}

fn binding(parsed: &ParseResult, expected: &str) -> Binding {
    let declaration = named(parsed, FILE, SyntaxKind::VariableDeclaration, expected);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    Binding {
        declaration,
        name: child(parsed, declaration, data.name),
        annotation: data.type_.map(|id| child(parsed, declaration, id)),
        initializer: child(parsed, declaration, data.initializer.unwrap()),
    }
}

struct Arrow {
    binding: Binding,
    declaration: NodeRef,
    body: NodeRef,
    annotation: NodeRef,
    parameters: Vec<NodeRef>,
}

fn arrow(parsed: &ParseResult, expected: &str) -> Arrow {
    let binding = binding(parsed, expected);
    assert!(binding.annotation.is_none());
    let declaration = binding.initializer;
    let NodeData::ArrowFunction(data) = &parsed.arena.get(declaration.node).unwrap().data else {
        panic!("the initializer must be the actual stored arrow");
    };
    Arrow {
        binding,
        declaration,
        body: child(parsed, declaration, data.body),
        annotation: child(parsed, declaration, data.type_.unwrap()),
        parameters: data
            .parameters
            .nodes
            .iter()
            .map(|&id| child(parsed, declaration, id))
            .collect(),
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
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("source checking must publish the real signature")
}

fn checked_type(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .expect("source checking must publish this expression type")
}

fn assert_optional_type(checker: &CanonicalCheckerContext<'_>, written: TypeId, value: TypeId) {
    let store = checker.store();
    let intrinsic = store.intrinsic_bootstrap().unwrap();
    let mut expected = match store.type_payload(written).unwrap().data() {
        TypeData::Union(data) => data.union.types.clone(),
        _ => vec![written],
    };
    expected.push(intrinsic.undefined_type);
    expected.sort_unstable();
    expected.dedup();
    let record = store.type_payload(value).unwrap();
    let TypeData::Union(data) = record.data() else {
        panic!("the optional parameter must retain its undefined union");
    };
    assert_eq!(data.union.types, expected);
    assert!(record.alias().is_none());
    assert!(data.origin.is_none());
    assert!(!data.union.types.contains(&intrinsic.missing_type));
    assert_eq!(intrinsic.cached_union_type(&expected), Some(value));
}

#[derive(Debug, Eq, PartialEq)]
struct ArrowState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    returned: TypeId,
    parameters: Vec<(SemanticSymbolId, TypeId, TypeId)>,
}

fn arrow_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    arrow: &Arrow,
) -> ArrowState {
    let owner = symbol(checker, arrow.declaration);
    let binding = symbol(checker, arrow.binding.declaration);
    assert_ne!(owner, binding);
    let type_ = checker.get_type_at_location(arrow.declaration).unwrap();
    assert_eq!(checker.get_type_at_location(arrow.binding.name), Ok(type_));
    assert_eq!(
        checker.get_symbol_at_location(arrow.binding.name),
        Ok(Some(binding))
    );
    assert_eq!(value_type(checker, owner), type_);
    assert_eq!(value_type(checker, binding), type_);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[arrow.declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(arrow.declaration));
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the stored arrow must retain its callable object");
    };
    let signature = signature(checker, arrow.declaration);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let mut minimum = 0;
    let parameters = arrow
        .parameters
        .iter()
        .map(|&declaration| {
            let NodeData::ParameterDeclaration(data) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the actual parameter declaration");
            };
            assert!(data.initializer.is_none());
            assert!(data.dot_dot_dot_token.is_none());
            let name = child(parsed, declaration, data.name);
            let annotation = child(parsed, declaration, data.type_.unwrap());
            let owner = symbol(checker, declaration);
            let written = checker.get_type_from_type_node(annotation).unwrap();
            let value = checker.get_type_at_location(name).unwrap();
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(owner)));
            assert_eq!(value_type(checker, owner), value);
            if let Some(question) = data.question_token {
                let question = child(parsed, declaration, question);
                assert_eq!(
                    parsed.arena.get(question.node).unwrap().kind,
                    SyntaxKind::QuestionToken
                );
                assert_optional_type(checker, written, value);
            } else {
                minimum += 1;
                assert_eq!(value, written);
            }
            (owner, written, value)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    assert_eq!(
        checker.get_type_from_type_node(arrow.annotation),
        Ok(returned)
    );
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(arrow.declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(owner, _, _)| owner)
            .collect::<Vec<_>>()
    );
    assert_eq!(record.min_argument_count(), minimum);
    assert!(record.type_parameters().is_empty());
    assert!(!record.has_rest_parameter());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(bound.container(arrow.body), Some(arrow.declaration));
    assert_eq!(
        bound.flow_graph().container_is_complete(arrow.declaration),
        Some(true)
    );
    assert_eq!(bound.flow_graph().container_end(arrow.declaration), None);
    ArrowState {
        owner,
        binding,
        type_,
        signature,
        returned,
        parameters,
    }
}

fn assert_array(checker: &CanonicalCheckerContext<'_>, array: TypeId, element: TypeId) {
    let target = checker.global_types().array_type;
    let TypeData::TypeReference(data) = checker.store().type_payload(array).unwrap().data() else {
        panic!("the array must retain its real library reference");
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(
        data.resolved_type_arguments.as_deref(),
        Some(&[element][..])
    );
    let owner = checker
        .store()
        .type_payload(target)
        .unwrap()
        .symbol()
        .unwrap();
    let declarations = checker
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap();
    assert!(!declarations.is_empty());
    assert!(declarations.iter().all(|node| node.file == LIBRARY));
    assert!(
        declarations
            .iter()
            .all(|&node| symbol(checker, node) == owner)
    );
}

fn body_kinds(parsed: &ParseResult, arrow: &Arrow) -> Vec<SyntaxKind> {
    let NodeData::Block(data) = &parsed.arena.get(arrow.body.node).unwrap().data else {
        panic!("expected the actual arrow block");
    };
    data.statements
        .nodes
        .iter()
        .map(|&id| {
            let statement = child(parsed, arrow.body, id);
            parsed.arena.get(statement.node).unwrap().kind
        })
        .collect()
}

fn throw_expression(parsed: &ParseResult, arrow: &Arrow) -> NodeRef {
    let statement = only(parsed, SyntaxKind::ThrowStatement);
    let NodeData::ThrowStatement(data) = &parsed.arena.get(statement.node).unwrap().data else {
        unreachable!();
    };
    assert_eq!(
        parsed.arena.get(statement.node).unwrap().parent,
        Some(arrow.body.node)
    );
    let expression = child(parsed, statement, data.expression);
    assert_eq!(
        parsed.arena.get(expression.node).unwrap().kind,
        SyntaxKind::NewExpression
    );
    expression
}

fn assert_error_construction(
    checker: &mut CanonicalCheckerContext<'_>,
    library: &ParseResult,
    parsed: &ParseResult,
    expression: NodeRef,
) -> (NodeRef, NodeRef) {
    let NodeData::NewExpression(data) = &parsed.arena.get(expression.node).unwrap().data else {
        unreachable!();
    };
    assert!(data.type_arguments.is_none());
    let callee = child(parsed, expression, data.expression);
    let [argument] = data.arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the real Error construction has one argument");
    };
    let argument = child(parsed, expression, *argument);
    let instance = checked_type(checker, expression);
    let value = checked_type(checker, callee);
    checked_type(checker, argument);
    let signature = signature(checker, expression);
    let declaration = checker
        .store()
        .signature(signature)
        .unwrap()
        .declaration()
        .unwrap();
    assert_eq!(declaration.file, LIBRARY);
    let constructor = named(
        library,
        LIBRARY,
        SyntaxKind::InterfaceDeclaration,
        "ErrorConstructor",
    );
    assert_eq!(
        library.arena.get(declaration.node).unwrap().parent,
        Some(constructor.node)
    );
    assert_eq!(
        library.arena.get(declaration.node).unwrap().kind,
        SyntaxKind::ConstructSignature
    );
    let error = named(library, LIBRARY, SyntaxKind::InterfaceDeclaration, "Error");
    let error_owner = symbol(checker, error);
    let constructor_owner = symbol(checker, constructor);
    assert_ne!(error_owner, constructor_owner);
    assert_eq!(
        checker.get_declared_type_of_symbol(error_owner),
        Ok(instance)
    );
    assert_eq!(
        checker.get_declared_type_of_symbol(constructor_owner),
        Ok(value)
    );
    assert_eq!(checker.get_type_at_location(expression), Ok(instance));
    assert_eq!(checker.get_type_at_location(callee), Ok(value));
    assert_eq!(
        checker.get_symbol_at_location(callee),
        Ok(Some(error_owner))
    );
    assert_eq!(value_type(checker, error_owner), value);
    assert_eq!(
        checker.store().type_payload(instance).unwrap().symbol(),
        Some(error_owner)
    );
    assert_eq!(
        checker.store().type_payload(value).unwrap().symbol(),
        Some(constructor_owner)
    );
    assert_ne!(instance, value);
    assert_eq!(
        checker.get_return_type_of_signature(signature),
        Ok(instance)
    );
    let record = checker.store().signature(signature).unwrap();
    assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
    assert_eq!(record.min_argument_count(), 0);
    assert_eq!(record.parameters().len(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let NodeData::ConstructSignatureDeclaration(data) =
        &library.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let parameter = child(library, declaration, data.parameters.nodes[0]);
    assert_eq!(record.parameters(), &[symbol(checker, parameter)]);
    let NodeData::ParameterDeclaration(data) = &library.arena.get(parameter.node).unwrap().data
    else {
        unreachable!();
    };
    assert!(data.question_token.is_some());
    let written = child(library, parameter, data.type_.unwrap());
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(checker.get_type_from_type_node(written), Ok(string));
    assert_optional_type(
        checker,
        string,
        value_type(checker, symbol(checker, parameter)),
    );
    (callee, argument)
}

#[derive(Clone, Copy, Debug)]
enum QueryOrder {
    Source,
    Arrow,
    ThrowOperand,
}

fn checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn start(
    checker: &mut CanonicalCheckerContext<'_>,
    arrow: &Arrow,
    operand: NodeRef,
    order: QueryOrder,
) {
    assert!(!checked(checker));
    assert!(checker.store().signature_links(arrow.declaration).is_none());
    let first = match order {
        QueryOrder::Source => None,
        QueryOrder::Arrow => Some(arrow.declaration),
        QueryOrder::ThrowOperand => Some(operand),
    }
    .map(|location| (location, checker.get_type_at_location(location).unwrap()));
    checker.check_source_file(FILE).unwrap();
    assert!(checked(checker));
    assert_eq!(checker.store().type_resolution_len(), 0);
    if let Some((location, type_)) = first {
        assert_eq!(checker.get_type_at_location(location), Ok(type_));
    }
    checked_type(checker, operand);
    signature(checker, operand);
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
struct Publication {
    counts: [usize; 8],
    globals: CanonicalGlobalTypes,
    nodes: Vec<NodeState>,
    symbols: Vec<SymbolState>,
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
        globals: checker.global_types().clone(),
        nodes: parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, FILE, id);
                NodeState {
                    node,
                    common: store.node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
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
    }
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    arrow: &Arrow,
    locations: &[NodeRef],
) {
    let state = arrow_state(checker, parsed, arrow);
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
        assert_eq!(arrow_state(checker, parsed, arrow), state);
        for &(location, type_, owner) in &queries {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(location), Ok(owner));
        }
        assert_eq!(publication(checker, parsed), before);
    }
}

fn assert_diagnostic(
    checker: &CanonicalCheckerContext<'_>,
    location: NodeRef,
    code: u32,
    arguments: [&str; 2],
    message: &str,
) {
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!(
            "expected exactly one type error: {:?}",
            checker.diagnostics()
        );
    };
    assert_eq!(diagnostic.node, Some(location));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
}

fn compile_parameters(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    arrow: &Arrow,
    state: &ArrowState,
) {
    assert_eq!(arrow.parameters.len(), 2);
    assert_eq!(
        checker
            .store()
            .signature(state.signature)
            .unwrap()
            .min_argument_count(),
        0
    );
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let TypeData::Union(data) = checker
        .store()
        .type_payload(state.parameters[0].1)
        .unwrap()
        .data()
    else {
        panic!("the first written parameter must retain string | string[]");
    };
    assert_eq!(data.union.types.len(), 2);
    assert!(data.union.types.contains(&string));
    let array = *data
        .union
        .types
        .iter()
        .find(|&&type_| type_ != string)
        .unwrap();
    assert_array(checker, array, string);
    let partial = only(parsed, SyntaxKind::PropertySignature);
    let NodeData::PropertySignatureDeclaration(data) =
        &parsed.arena.get(partial.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        parsed
            .arena
            .get(data.postfix_token.expect("the property must remain optional"))
            .unwrap()
            .kind,
        SyntaxKind::QuestionToken
    );
    let annotation = child(parsed, partial, data.type_);
    let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
    assert_eq!(checker.get_type_from_type_node(annotation), Ok(boolean));
    assert!(matches!(
        checker
            .store()
            .type_payload(state.parameters[1].1)
            .unwrap()
            .data(),
        TypeData::Object(_)
    ));
    for &parameter in &arrow.parameters {
        let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
        else {
            unreachable!();
        };
        assert!(data.question_token.is_some());
    }
}

#[test]
fn sole_throw_arrows_keep_written_unknown_and_optional_parameters() {
    let library = parse_source_file(ES5);
    for bad_result in [false, true] {
        let result_type = if bad_result { "number" } else { "unknown" };
        let source = format!("{COMPILE}const result: {result_type} = compile();\nexport {{}};\n");
        assert!(source.starts_with(COMPILE));
        let parsed = parse_source_file(&source);
        let arrow = arrow(&parsed, "compile");
        let operand = throw_expression(&parsed, &arrow);
        let result = binding(&parsed, "result");
        assert_eq!(
            body_kinds(&parsed, &arrow),
            vec![SyntaxKind::ThrowStatement]
        );
        assert!(nodes(&parsed, SyntaxKind::ReturnStatement).is_empty());
        for order in [
            QueryOrder::Source,
            QueryOrder::Arrow,
            QueryOrder::ThrowOperand,
        ] {
            let mut checker = context(&library, &parsed);
            start(&mut checker, &arrow, operand, order);
            let unknown = checker.store().intrinsic_bootstrap().unwrap().unknown_type;
            let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(checked_type(&checker, result.initializer), unknown);
            let (constructor, argument) =
                assert_error_construction(&mut checker, &library, &parsed, operand);
            let TypeData::Literal(literal) = checker
                .store()
                .type_payload(checked_type(&checker, argument))
                .unwrap()
                .data()
            else {
                panic!("the constructor argument must retain its actual string literal");
            };
            assert_eq!(
                literal.value,
                LiteralValue::String("compile() is not ported".to_owned())
            );
            let state = arrow_state(&mut checker, &parsed, &arrow);
            assert_eq!(state.returned, unknown);
            compile_parameters(&mut checker, &parsed, &arrow, &state);
            assert_eq!(signature(&checker, result.initializer), state.signature);
            assert_eq!(
                checker.get_type_at_location(result.initializer),
                Ok(unknown)
            );
            assert_eq!(
                checker.get_type_at_location(result.name),
                Ok(if bad_result { number } else { unknown })
            );
            assert_eq!(
                checker.get_symbol_at_location(result.name),
                Ok(Some(symbol(&checker, result.declaration)))
            );
            if bad_result {
                assert_diagnostic(
                    &checker,
                    result.name,
                    2322,
                    ["unknown", "number"],
                    "Type 'unknown' is not assignable to type 'number'.",
                );
            } else {
                assert!(
                    checker.diagnostics().is_empty(),
                    "{:?}",
                    checker.diagnostics()
                );
            }
            replay(
                &mut checker,
                &parsed,
                &arrow,
                &[
                    arrow.binding.name,
                    arrow.declaration,
                    operand,
                    constructor,
                    argument,
                    result.initializer,
                    result.name,
                ],
            );
        }
    }
}

#[allow(clippy::too_many_lines)] // Keep one parsed body's source and flow checks together.
fn parse_body(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    arrow: &Arrow,
    bad_argument: bool,
) -> Vec<NodeRef> {
    assert_eq!(
        body_kinds(parsed, arrow),
        vec![
            SyntaxKind::VariableStatement,
            SyntaxKind::IfStatement,
            SyntaxKind::ThrowStatement
        ]
    );
    let local = binding(parsed, "state");
    let call = only(parsed, SyntaxKind::CallExpression);
    let branch = only(parsed, SyntaxKind::IfStatement);
    let returned = only(parsed, SyntaxKind::ReturnStatement);
    let template = only(parsed, SyntaxKind::TemplateExpression);
    let span = only(parsed, SyntaxKind::TemplateSpan);
    let NodeData::IfStatement(branch_data) = &parsed.arena.get(branch.node).unwrap().data else {
        unreachable!();
    };
    let condition = child(parsed, branch, branch_data.expression);
    let NodeData::ReturnStatement(return_data) = &parsed.arena.get(returned.node).unwrap().data
    else {
        unreachable!();
    };
    let return_expression = child(parsed, returned, return_data.expression.unwrap());
    let NodeData::TemplateSpan(span_data) = &parsed.arena.get(span.node).unwrap().data else {
        unreachable!();
    };
    let index = child(parsed, span, span_data.expression);
    let initializer_type = checked_type(checker, local.initializer);
    let call_type = checked_type(checker, call);
    let condition_type = checked_type(checker, condition);
    let returned_type = checked_type(checker, return_expression);
    let template_type = checked_type(checker, template);
    let index_type = checked_type(checker, index);
    let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
    let (string, number, boolean, any) = (
        intrinsic.string_type,
        intrinsic.number_type,
        intrinsic.boolean_type,
        intrinsic.any_type,
    );
    assert!(matches!(
        checker
            .store()
            .type_payload(initializer_type)
            .unwrap()
            .data(),
        TypeData::Object(_)
    ));
    assert_eq!(call_type, boolean);
    assert_eq!(condition_type, boolean);
    assert_eq!(template_type, string);
    assert_eq!(index_type, number);
    assert_array(checker, returned_type, any);
    let state = arrow_state(checker, parsed, arrow);
    assert_eq!(state.parameters.len(), 2);
    assert_eq!(
        checker
            .store()
            .signature(state.signature)
            .unwrap()
            .min_argument_count(),
        2
    );
    assert_eq!(state.parameters[0].1, string);
    assert_eq!(state.returned, returned_type);
    let declaration = named(parsed, FILE, SyntaxKind::InterfaceDeclaration, "State");
    let state_owner = symbol(checker, declaration);
    let state_type = checker.get_declared_type_of_symbol(state_owner).unwrap();
    assert_eq!(
        checker.get_type_from_type_node(local.annotation.unwrap()),
        Ok(state_type)
    );
    assert_eq!(checker.get_type_at_location(local.name), Ok(state_type));
    assert_eq!(
        value_type(checker, symbol(checker, local.declaration)),
        state_type
    );
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let callee = child(parsed, call, call_data.expression);
    let [argument] = call_data.arguments.nodes.as_slice() else {
        panic!("the rule call must retain one argument");
    };
    let argument = child(parsed, call, *argument);
    assert_eq!(
        checker.get_symbol_at_location(callee),
        Ok(Some(state.parameters[1].0))
    );
    assert_eq!(
        checker.get_type_at_location(callee),
        Ok(state.parameters[1].2)
    );
    assert_eq!(
        checker.get_type_at_location(argument),
        Ok(if bad_argument { string } else { state_type })
    );
    assert_eq!(
        checker.get_symbol_at_location(argument),
        Ok(Some(if bad_argument {
            state.parameters[0].0
        } else {
            symbol(checker, local.declaration)
        }))
    );
    let call_signature = signature(checker, call);
    assert_eq!(
        checker.get_return_type_of_signature(call_signature),
        Ok(boolean)
    );
    for (access, property, type_) in [
        (return_expression, "output", returned_type),
        (index, "index", number),
    ] {
        let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(access.node).unwrap().data
        else {
            unreachable!();
        };
        let name = child(parsed, access, data.name);
        let property = named(parsed, FILE, SyntaxKind::PropertySignature, property);
        assert_eq!(
            checker.get_symbol_at_location(name),
            Ok(Some(symbol(checker, property)))
        );
        assert_eq!(checker.get_type_at_location(access), Ok(type_));
    }
    let (_, bound) = checker.file(FILE).unwrap();
    assert_eq!(bound.flow_container(returned), Some(arrow.declaration));
    assert!(bound.flow_at(returned).is_some());
    if bad_argument {
        assert_diagnostic(
            checker,
            argument,
            2345,
            ["string", "State"],
            "Argument of type 'string' is not assignable to parameter of type 'State'.",
        );
    } else {
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
    }
    vec![
        local.name,
        local.initializer,
        callee,
        argument,
        call,
        condition,
        return_expression,
        template,
        index,
    ]
}

#[test]
fn parse_arrows_check_locals_branches_and_throw_operands() {
    let library = parse_source_file(ES5);
    for bad_argument in [false, true] {
        let body = if bad_argument {
            PARSE.replace("rule(state)", "rule(input)")
        } else {
            PARSE.to_owned()
        };
        assert_eq!(body.replace("rule(input)", "rule(state)"), PARSE);
        let parsed = parse_source_file(&format!("{body}export {{}};\n"));
        let arrow = arrow(&parsed, "parse");
        let operand = throw_expression(&parsed, &arrow);
        for order in [
            QueryOrder::Source,
            QueryOrder::Arrow,
            QueryOrder::ThrowOperand,
        ] {
            let mut checker = context(&library, &parsed);
            start(&mut checker, &arrow, operand, order);
            let (constructor, argument) =
                assert_error_construction(&mut checker, &library, &parsed, operand);
            let mut locations = parse_body(&mut checker, &parsed, &arrow, bad_argument);
            assert_eq!(argument, only(&parsed, SyntaxKind::TemplateExpression));
            locations.extend([
                arrow.binding.name,
                arrow.declaration,
                operand,
                constructor,
                argument,
            ]);
            replay(&mut checker, &parsed, &arrow, &locations);
        }
    }
}
