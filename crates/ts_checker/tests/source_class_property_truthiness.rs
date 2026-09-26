use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, EffectsSignatureState, IntrinsicBootstrapOptions, NodeLinks,
    RelationStateSnapshot, SignatureId, SignatureLinks, SourceCheckError, SourceFileLinks,
    SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax,
    ValueSymbolLinks, signatures::TypePredicateKind, types::TypeFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(202_670);
const FILE: FileId = FileId::new(202_671);
const PROVIDER_FILE: FileId = FileId::new(202_672);
const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

fn context<'a>(files: &[(FileId, &'a ParseResult)], exact: bool) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for &(file, source) in files {
        let (path, declaration, default_library) = match file {
            LIBRARY_FILE => ("\"/project/lib.d.ts\"", true, true),
            PROVIDER_FILE => ("\"/project/provider.d.ts\"", true, false),
            FILE => ("\"/project/class-property-truthiness.ts\"", false, false),
            _ => panic!("unexpected source file"),
        };
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    default_library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: exact,
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    parsed
        .arena
        .iter()
        .filter_map(|(node, record)| (record.kind == kind).then_some(reference(parsed, node)))
        .collect()
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let nodes = nodes(parsed, kind);
    let [node] = nodes.as_slice() else {
        panic!("expected one {kind:?}")
    };
    *node
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

fn raw_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked expression at {node:?}"))
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

#[derive(Clone, Copy)]
struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    let variables = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(Variable {
                declaration: reference(parsed, node),
                name: reference(parsed, data.name),
                initializer: reference(parsed, data.initializer?),
            })
        })
        .collect::<Vec<_>>();
    let [variable] = variables.as_slice() else {
        panic!("expected one local named {expected}")
    };
    *variable
}

#[derive(Clone, Copy)]
struct Field {
    owner: SemanticSymbolId,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    name: NodeRef,
    type_: TypeId,
    this_type: TypeId,
}

fn field(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    class_name: &str,
    field_name: &str,
) -> Field {
    let (class_node, class) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name?)?.data else {
                return None;
            };
            (name.text == class_name).then_some((reference(parsed, node), data))
        })
        .unwrap();
    let (declaration, property) = class
        .members
        .nodes
        .iter()
        .find_map(|&node| {
            let NodeData::PropertyDeclaration(data) = &parsed.arena.get(node)?.data else {
                return None;
            };
            let name = match &parsed.arena.get(data.name)?.data {
                NodeData::Identifier(name) => &name.text,
                NodeData::PrivateIdentifier(name) => &name.text,
                _ => return None,
            };
            (name == field_name).then_some((reference(parsed, node), data))
        })
        .unwrap();
    let owner = symbol(checker, class_node);
    let member = symbol(checker, declaration);
    let record = checker.store().symbol(member).unwrap();
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));
    assert!(record.flags().contains(SymbolFlags::PROPERTY));
    assert_eq!(
        record.name().is_private_identifier(),
        field_name.starts_with('#')
    );
    let members = checker.store().symbol(owner).unwrap().members().unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(members)
            .unwrap()
            .get(record.name()),
        Some(member)
    );
    assert_eq!(
        record.flags().contains(SymbolFlags::OPTIONAL),
        property.postfix_token.is_some_and(|token| {
            parsed.arena.get(token).unwrap().kind == SyntaxKind::QuestionToken
        })
    );
    let instance = checker
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(data) = checker.store().type_payload(instance).unwrap().data() else {
        panic!("expected the actual class instance")
    };
    assert_eq!(
        checker.store().type_payload(instance).unwrap().symbol(),
        Some(owner)
    );
    Field {
        owner,
        symbol: member,
        declaration,
        name: reference(parsed, property.name),
        type_: value_type(checker, member),
        this_type: data.this_type.unwrap(),
    }
}

fn assert_members(checker: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[TypeId]) {
    let mut actual = match checker.store().type_payload(type_).unwrap().data() {
        TypeData::Union(union) => union.union.types.clone(),
        _ => vec![type_],
    };
    let mut expected = expected.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    assert_eq!(actual, expected);
}

fn number_member(checker: &CanonicalCheckerContext<'_>, type_: TypeId, text: &str) -> TypeId {
    let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the written numeric union")
    };
    let member = *union
        .union
        .types
        .iter()
        .find(|&&type_| checker.type_to_string(type_).unwrap() == text)
        .unwrap();
    assert!(
        checker
            .store()
            .type_payload(member)
            .unwrap()
            .flags()
            .contains(TypeFlags::NUMBER_LITERAL)
    );
    member
}

type Query = (NodeRef, TypeId, Option<SemanticSymbolId>);

fn property_query(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    access: NodeRef,
    field: Field,
    expected: TypeId,
) -> Query {
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("expected an actual property access")
    };
    let receiver = reference(parsed, property.expression);
    assert_eq!(
        parsed.arena.get(receiver.node).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    assert_eq!(raw_type(checker, receiver), field.this_type);
    assert_eq!(raw_type(checker, access), expected);
    assert_eq!(
        checker
            .store()
            .symbol_node_links(access)
            .unwrap()
            .resolved_symbol,
        Some(field.symbol)
    );
    let container = checker
        .file(FILE)
        .unwrap()
        .1
        .flow_container(access)
        .unwrap();
    assert_eq!(
        parsed.arena.get(container.node).unwrap().parent,
        parsed.arena.get(field.declaration.node).unwrap().parent
    );
    assert!(checker.file(FILE).unwrap().1.flow_at(access).is_some());
    (access, expected, Some(field.symbol))
}

fn local_query(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    field: Field,
    expected: TypeId,
) -> Query {
    let local = variable(parsed, name);
    assert!(
        checker
            .store()
            .value_symbol_links(symbol(checker, local.declaration))
            .is_some()
    );
    property_query(checker, parsed, local.initializer, field, expected)
}

fn assert_guard_edges(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let bound = checker.file(FILE).unwrap().1;
    for branch in nodes(parsed, SyntaxKind::IfStatement) {
        let NodeData::IfStatement(data) = &parsed.arena.get(branch.node).unwrap().data else {
            unreachable!()
        };
        let condition = reference(parsed, data.expression);
        let edges = bound
            .flow_graph()
            .nodes()
            .iter()
            .filter(|flow| {
                flow.payload == Some(FlowNodePayload::Ast(condition))
                    && flow
                        .flags
                        .intersects(FlowFlags::TRUE_CONDITION | FlowFlags::FALSE_CONDITION)
            })
            .collect::<Vec<_>>();
        assert_eq!(edges.len(), 2);
        assert!(
            edges
                .iter()
                .any(|flow| flow.flags.contains(FlowFlags::TRUE_CONDITION))
        );
        assert!(
            edges
                .iter()
                .any(|flow| flow.flags.contains(FlowFlags::FALSE_CONDITION))
        );
        assert!(edges[0].antecedent.is_some());
        assert_eq!(edges[0].antecedent, edges[1].antecedent);
    }
}

type NodePublication = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<TypeAliasLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 8],
    relation: RelationStateSnapshot,
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    files: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(
    checker: &CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
) -> Publication {
    let store = checker.store();
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.type_predicate_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        relation: store.relation_state_snapshot(),
        nodes: files
            .iter()
            .flat_map(|&(file, parsed)| {
                parsed.arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect(),
        files: files
            .iter()
            .map(|&(file, _)| {
                store
                    .source_file_links(checker.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn assert_queries(checker: &mut CanonicalCheckerContext<'_>, queries: &[Query]) {
    for &(node, type_, symbol) in queries {
        assert_eq!(checker.get_type_at_location(node), Ok(type_));
        if let Some(symbol) = symbol {
            assert_eq!(checker.get_symbol_at_location(node), Ok(Some(symbol)));
        }
    }
}

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    queries: &[Query],
) {
    let file = checker.source_file(FILE).unwrap();
    assert!(
        checker
            .store()
            .source_file_links(file)
            .unwrap()
            .type_checked
    );
    let cold = publication(checker, files);
    assert_queries(checker, queries);
    assert_eq!(publication(checker, files), cold);
    checker.check_source_file(FILE).unwrap();
    assert_eq!(publication(checker, files), cold);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        assert_queries(checker, queries);
        assert_eq!(publication(checker, files), cold);
    }
}

fn assert_failed_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
    error: SourceCheckError,
) {
    let file = checker.source_file(FILE).unwrap();
    assert_eq!(checker.store().source_file_links(file), None);
    let failed = publication(checker, files);
    for _ in 0..2 {
        assert_eq!(checker.check_source_file(FILE), Err(error));
        assert_eq!(publication(checker, files), failed);
    }
    assert_eq!(checker.recheck_source_file(FILE), Err(error));
    assert_eq!(publication(checker, files), failed);
}

fn field_query(field: Field) -> Query {
    (field.name, field.type_, Some(field.symbol))
}

fn returned_property(parsed: &ParseResult) -> NodeRef {
    let returns = nodes(parsed, SyntaxKind::ReturnStatement)
        .into_iter()
        .filter_map(|node| {
            let NodeData::ReturnStatement(data) = &parsed.arena.get(node.node)?.data else {
                return None;
            };
            let expression = reference(parsed, data.expression?);
            (parsed.arena.get(expression.node)?.kind == SyntaxKind::PropertyAccessExpression)
                .then_some(expression)
        })
        .collect::<Vec<_>>();
    let [expression] = returns.as_slice() else {
        panic!("expected one property return")
    };
    *expression
}

#[test]
fn class_property_conditions_keep_both_branch_members_and_real_owners() {
    let source = concat!(
        "class Branches {\n",
        "  value?: 0 | 1;\n",
        "  observe(): void {\n",
        "    const before = this.value;\n",
        "    if (this.value) { const truth = this.value; }\n",
        "    else { const falsy = this.value; }\n",
        "    const joined = this.value;\n",
        "    if (!(this.value)) { const negated = this.value; }\n",
        "    else { const negatedElse = this.value; }\n",
        "  }\n",
        "  read(): number { if (this.value) { return this.value; } return 0; }\n",
        "}\n",
        "class Other {\n",
        "  value?: 0 | 1;\n",
        "  #value?: 0 | 1;\n",
        "  observe(): void {\n",
        "    const untouched = this.value;\n",
        "    if (this.#value) {\n",
        "      const privateTruth = this.#value;\n",
        "      const differentField = this.value;\n",
        "    } else { const privateFalse = this.#value; }\n",
        "  }\n",
        "}\n",
    );
    for exact in [false, true] {
        let library = parse_source_file(LIBRARY);
        let parsed = parse_source_file(source);
        let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
        let mut checker = context(&files, exact);
        assert_guard_edges(&checker, &parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let value = field(&checker, &parsed, "Branches", "value");
        let other = field(&checker, &parsed, "Other", "value");
        let private = field(&checker, &parsed, "Other", "#value");
        assert_ne!(value.owner, other.owner);
        assert_ne!(value.symbol, other.symbol);
        assert_ne!(private.symbol, other.symbol);
        assert_eq!(private.owner, other.owner);
        assert_ne!(value.this_type, other.this_type);
        assert_eq!(value.type_, other.type_);
        assert_eq!(private.type_, other.type_);
        let zero = number_member(&checker, value.type_, "0");
        let one = number_member(&checker, value.type_, "1");
        let sentinel = checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_or_missing_type;
        assert_members(&checker, value.type_, &[zero, one]);
        let optional = raw_type(&checker, variable(&parsed, "before").initializer);
        let falsy = raw_type(&checker, variable(&parsed, "falsy").initializer);
        assert_members(&checker, optional, &[zero, one, sentinel]);
        assert_members(&checker, falsy, &[zero, sentinel]);
        let mut queries = vec![field_query(value), field_query(other), field_query(private)];
        for (name, field, expected) in [
            ("before", value, optional),
            ("truth", value, one),
            ("falsy", value, falsy),
            ("joined", value, optional),
            ("negated", value, falsy),
            ("negatedElse", value, one),
            ("untouched", other, optional),
            ("privateTruth", private, one),
            ("privateFalse", private, falsy),
            ("differentField", other, optional),
        ] {
            queries.push(local_query(&checker, &parsed, name, field, expected));
        }
        queries.push(property_query(
            &checker,
            &parsed,
            returned_property(&parsed),
            value,
            one,
        ));
        assert_replay(&mut checker, &files, &queries);
    }
}

fn assert_private_write(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    field: Field,
) -> Vec<Query> {
    let parentheses = only_node(parsed, SyntaxKind::ParenthesizedExpression);
    let NodeData::ParenthesizedExpression(data) = &parsed.arena.get(parentheses.node).unwrap().data
    else {
        unreachable!()
    };
    let assignment = reference(parsed, data.expression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("expected the private destructuring assignment")
    };
    let NodeData::ObjectLiteralExpression(pattern) = &parsed.arena.get(binary.left).unwrap().data
    else {
        panic!("expected the original assignment pattern")
    };
    let [property] = pattern.properties.nodes.as_slice() else {
        panic!("expected one private write leaf")
    };
    let NodeData::PropertyAssignment(property) = &parsed.arena.get(*property).unwrap().data else {
        panic!("expected the selected source property")
    };
    let target = reference(parsed, property.initializer);
    let rhs = reference(parsed, binary.right);
    let object = raw_type(checker, rhs);
    assert_ne!(object, field.type_);
    assert_eq!(
        value_type(
            checker,
            symbol(checker, variable(parsed, "source").declaration)
        ),
        object
    );
    assert_eq!(raw_type(checker, assignment), object);
    assert_eq!(raw_type(checker, parentheses), object);
    assert!(
        checker
            .file(FILE)
            .unwrap()
            .1
            .flow_graph()
            .nodes()
            .iter()
            .any(|flow| {
                flow.flags.contains(FlowFlags::ASSIGNMENT)
                    && flow.payload == Some(FlowNodePayload::Ast(target))
            })
    );
    vec![
        property_query(checker, parsed, target, field, field.type_),
        (
            rhs,
            object,
            Some(symbol(checker, variable(parsed, "source").declaration)),
        ),
        (assignment, object, None),
        (parentheses, object, None),
    ]
}

#[test]
fn class_property_writes_replace_matching_facts_and_keep_sibling_facts() {
    let source = concat!(
        "class Writes {\n",
        "  value?: 0 | 1;\n",
        "  other: number = 0;\n",
        "  #state: number = 0;\n",
        "  update(): void {\n",
        "    if (this.value) {\n",
        "      const initial = this.value;\n",
        "      this.other = 2;\n",
        "      const sibling = this.value;\n",
        "      const source = { value: 2 };\n",
        "      ({ value: this.#state } = source);\n",
        "      const privateValue = this.#state;\n",
        "      const afterPrivate = this.value;\n",
        "      this.value = 0;\n",
        "      const replaced = this.value;\n",
        "    } else {\n",
        "      this.value = 1;\n",
        "      const falseWrite = this.value;\n",
        "    }\n",
        "    const joined = this.value;\n",
        "  }\n",
        "}\n",
    );
    for exact in [false, true] {
        let library = parse_source_file(LIBRARY);
        let parsed = parse_source_file(source);
        let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
        let mut checker = context(&files, exact);
        assert_guard_edges(&checker, &parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let value = field(&checker, &parsed, "Writes", "value");
        let state = field(&checker, &parsed, "Writes", "#state");
        assert_eq!(
            state.type_,
            checker.store().intrinsic_bootstrap().unwrap().number_type
        );
        let zero = number_member(&checker, value.type_, "0");
        let one = number_member(&checker, value.type_, "1");
        let mut queries = vec![field_query(value), field_query(state)];
        for (name, expected) in [
            ("initial", one),
            ("sibling", one),
            ("afterPrivate", one),
            ("replaced", zero),
            ("falseWrite", one),
            ("joined", value.type_),
        ] {
            queries.push(local_query(&checker, &parsed, name, value, expected));
        }
        queries.push(local_query(
            &checker,
            &parsed,
            "privateValue",
            state,
            state.type_,
        ));
        queries.extend(assert_private_write(&checker, &parsed, state));
        assert_replay(&mut checker, &files, &queries);
    }
}

fn assert_initialization_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    field: Field,
) {
    let read = variable(parsed, "after").initializer;
    let NodeData::PropertyAccessExpression(property) = &parsed.arena.get(read.node).unwrap().data
    else {
        unreachable!()
    };
    let expected = [
        (
            2564,
            field.name,
            "Property 'value' has no initializer and is not definitely assigned in the constructor.",
        ),
        (
            2565,
            reference(parsed, property.name),
            "Property 'value' is used before being assigned.",
        ),
    ];
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (code, node, message) in expected {
        let diagnostic = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.diagnostic.code() == code)
            .unwrap();
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
    }
}

#[test]
fn class_property_conditions_keep_constructor_initialization_and_readonly_boundaries() {
    for (source, initialized) in [
        (
            concat!(
                "class Init { gate?: number; readonly value: number;\n",
                "  constructor() {\n",
                "    if (this.gate) { this.value = 1; } else { this.value = 2; }\n",
                "    const after: number = this.value;\n",
                "  }\n",
                "}\n",
            ),
            true,
        ),
        (
            concat!(
                "class Init { gate?: number; value: number;\n",
                "  constructor() {\n",
                "    if (this.gate) { this.value = 1; }\n",
                "    const after: number = this.value;\n",
                "  }\n",
                "}\n",
            ),
            false,
        ),
    ] {
        let library = parse_source_file(LIBRARY);
        let parsed = parse_source_file(source);
        let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
        let mut checker = context(&files, false);
        assert_guard_edges(&checker, &parsed);
        checker.check_source_file(FILE).unwrap();
        let value = field(&checker, &parsed, "Init", "value");
        assert_eq!(
            value.type_,
            checker.store().intrinsic_bootstrap().unwrap().number_type
        );
        if initialized {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        } else {
            assert_initialization_diagnostics(&checker, &parsed, value);
        }
        let query = local_query(&checker, &parsed, "after", value, value.type_);
        assert_replay(&mut checker, &files, &[field_query(value), query]);
    }
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Fixed { readonly value?: number;\n",
        "  update(): void { if (this.value) { this.value = 1; } }\n",
        "}\n",
    ));
    let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
    let mut checker = context(&files, false);
    let assignment = only_node(&parsed, SyntaxKind::BinaryExpression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        unreachable!()
    };
    let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Property(reference(
        &parsed,
        binary.left,
    )));
    let cold = publication(&checker, &files);
    assert_eq!(checker.check_source_file(FILE), Err(error));
    assert_eq!(publication(&checker, &files), cold);
    assert_failed_replay(&mut checker, &files, error);
}

fn assert_array_targets(checker: &CanonicalCheckerContext<'_>, library: &ParseResult) {
    let store = checker.store();
    let bound = checker.file(LIBRARY_FILE).unwrap().1;
    let table = store
        .symbol_table(bound.locals(bound.source_file()).unwrap())
        .unwrap();
    let globals = store.symbol_table(checker.globals()).unwrap();
    for (name, target) in [
        ("Array", checker.global_types().array_type),
        ("ReadonlyArray", checker.global_types().readonly_array_type),
    ] {
        let owner = store
            .get_merged_symbol(table.get_source(name).unwrap())
            .unwrap();
        assert_eq!(globals.get_source(name), Some(owner));
        let [declaration] = store.symbol(owner).unwrap().declarations().unwrap() else {
            panic!("expected the real library declaration")
        };
        assert!(declaration.is_for(library.arena.id(), LIBRARY_FILE));
        assert_eq!(bound.symbol(*declaration), Some(owner));
        assert_eq!(
            store.declared_type_links(owner).unwrap().declared_type,
            Some(target)
        );
        assert_eq!(store.type_payload(target).unwrap().symbol(), Some(owner));
    }
    assert_ne!(
        checker.global_types().array_type,
        checker.global_types().readonly_array_type
    );
}

fn checked_call_signature(checker: &CanonicalCheckerContext<'_>, call: NodeRef) -> SignatureId {
    let links = checker.store().signature_links(call).unwrap();
    assert_eq!(links.effects_signature, EffectsSignatureState::Unresolved);
    let signature = links.resolved_signature.signature().unwrap();
    let declaration = checker
        .store()
        .signature(signature)
        .unwrap()
        .declaration()
        .unwrap();
    assert_eq!(declaration.file, FILE);
    assert_eq!(
        checker
            .store()
            .signature_links(declaration)
            .unwrap()
            .resolved_signature
            .signature(),
        Some(signature)
    );
    signature
}

#[test]
fn class_property_conditions_keep_proved_array_objects_and_ordinary_calls() {
    let source = concat!(
        "interface Contents { items: number[]; }\n",
        "declare function touch(): void;\n",
        "class Holder {\n",
        "  contents?: Contents;\n",
        "  touch(): void {}\n",
        "  read(): void {\n",
        "    touch();\n",
        "    this.touch();\n",
        "    if (this.contents) {\n",
        "      touch();\n",
        "      this.touch();\n",
        "      const present = this.contents;\n",
        "      const items = this.contents.items;\n",
        "    } else { const absent = this.contents; }\n",
        "    const joined = this.contents;\n",
        "  }\n",
        "}\n",
    );
    for exact in [false, true] {
        let library = parse_source_file(LIBRARY);
        let parsed = parse_source_file(source);
        let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
        let mut checker = context(&files, exact);
        assert_array_targets(&checker, &library);
        assert_guard_edges(&checker, &parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let contents = field(&checker, &parsed, "Holder", "contents");
        let interface = only_node(&parsed, SyntaxKind::InterfaceDeclaration);
        assert_eq!(
            checker
                .store()
                .declared_type_links(symbol(&checker, interface))
                .unwrap()
                .declared_type,
            Some(contents.type_)
        );
        let sentinel = checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_or_missing_type;
        let optional = raw_type(&checker, variable(&parsed, "joined").initializer);
        assert_members(&checker, optional, &[contents.type_, sentinel]);
        let mut queries = vec![field_query(contents)];
        for (name, expected) in [
            ("present", contents.type_),
            ("absent", sentinel),
            ("joined", optional),
        ] {
            queries.push(local_query(&checker, &parsed, name, contents, expected));
        }
        let items = variable(&parsed, "items").initializer;
        let array = raw_type(&checker, items);
        let TypeData::TypeReference(data) = checker.store().type_payload(array).unwrap().data()
        else {
            panic!("expected the canonical Array reference")
        };
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(data.object.target, Some(checker.global_types().array_type));
        assert_eq!(data.resolved_type_arguments.as_deref(), Some(&[number][..]));
        let item_declaration = only_node(&parsed, SyntaxKind::PropertySignature);
        let item_symbol = symbol(&checker, item_declaration);
        assert_eq!(value_type(&checker, item_symbol), array);
        assert_eq!(
            checker.store().symbol(item_symbol).unwrap().parent(),
            Some(symbol(&checker, interface))
        );
        queries.push((items, array, Some(item_symbol)));
        let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 4);
        for call in calls {
            let signature = checked_call_signature(&checker, call);
            assert_eq!(
                checker
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                Some(void)
            );
            assert_eq!(raw_type(&checker, call), void);
            queries.push((call, void, None));
        }
        assert_replay(&mut checker, &files, &queries);
    }
}

fn assert_unpublished_local(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) {
    let local = variable(parsed, name);
    assert_eq!(
        checker
            .store()
            .value_symbol_links(symbol(checker, local.declaration)),
        None
    );
    assert_eq!(checker.store().type_node_links(local.name), None);
    assert_eq!(checker.store().type_node_links(local.initializer), None);
}

#[test]
fn class_property_conditions_reject_checked_assertion_and_never_effects() {
    for (source, assertion) in [
        (
            concat!(
                "declare function assertString(value: unknown): asserts value is string;\n",
                "class Guard { value?: string;\n",
                "  read(): void {\n",
                "    if (this.value) {\n",
                "      assertString(this.value);\n",
                "      const after: number = this.value;\n",
                "    }\n",
                "  }\n",
                "}\n",
            ),
            true,
        ),
        (
            concat!(
                "declare function fail(): never;\n",
                "class Guard { value?: string;\n",
                "  read(): void {\n",
                "    if (this.value) {\n",
                "      fail();\n",
                "      const after: number = this.value;\n",
                "    }\n",
                "  }\n",
                "}\n",
            ),
            false,
        ),
    ] {
        let library = parse_source_file(LIBRARY);
        let parsed = parse_source_file(source);
        let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
        let mut checker = context(&files, false);
        assert_guard_edges(&checker, &parsed);
        let call = only_node(&parsed, SyntaxKind::CallExpression);
        let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(call));
        assert_eq!(checker.check_source_file(FILE), Err(error));
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let signature = checked_call_signature(&checker, call);
        let signature = checker.store().signature(signature).unwrap();
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let result = if assertion {
            bootstrap.void_type
        } else {
            bootstrap.never_type
        };
        assert_eq!(signature.resolved_return_type(), Some(result));
        assert_eq!(raw_type(&checker, call), result);
        let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
            unreachable!()
        };
        let callee = reference(&parsed, data.expression);
        let owner = symbol(&checker, signature.declaration().unwrap());
        assert_eq!(
            checker
                .store()
                .symbol_node_links(callee)
                .unwrap()
                .resolved_symbol,
            Some(owner)
        );
        assert_eq!(raw_type(&checker, callee), value_type(&checker, owner));
        if assertion {
            let predicate = checker
                .store()
                .type_predicate(signature.resolved_type_predicate().unwrap())
                .unwrap();
            assert_eq!(predicate.kind(), TypePredicateKind::AssertsIdentifier);
            assert_eq!(predicate.parameter_index(), 0);
            assert_eq!(predicate.parameter_name(), "value");
            assert_eq!(predicate.type_id(), Some(bootstrap.string_type));
            let [argument] = data.arguments.nodes.as_slice() else {
                panic!("expected the actual field argument")
            };
            let field = field(&checker, &parsed, "Guard", "value");
            property_query(
                &checker,
                &parsed,
                reference(&parsed, *argument),
                field,
                bootstrap.string_type,
            );
        } else {
            assert_eq!(signature.resolved_type_predicate(), None);
            assert!(data.arguments.nodes.is_empty());
        }
        assert_unpublished_local(&checker, &parsed, "after");
        assert_failed_replay(&mut checker, &files, error);
    }
}

#[test]
fn class_property_conditions_reject_current_class_destructuring_reads_before_execution() {
    let source = concat!(
        "class Guard { value?: number;\n",
        "  read(): void {\n",
        "    if (this.value) {\n",
        "      const { value } = this;\n",
        "      const after: number = value;\n",
        "    }\n",
        "  }\n",
        "}\n",
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(source);
    let files = [(LIBRARY_FILE, &library), (FILE, &parsed)];
    let mut checker = context(&files, false);
    let pattern = only_node(&parsed, SyntaxKind::ObjectBindingPattern);
    let declaration = reference(
        &parsed,
        parsed.arena.get(pattern.node).unwrap().parent.unwrap(),
    );
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected the real destructuring declaration")
    };
    let receiver = reference(&parsed, data.initializer.unwrap());
    assert_eq!(
        parsed.arena.get(receiver.node).unwrap().kind,
        SyntaxKind::ThisKeyword
    );
    let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(receiver));
    let cold = publication(&checker, &files);
    assert_eq!(checker.check_source_file(FILE), Err(error));
    assert_eq!(publication(&checker, &files), cold);
    assert_unpublished_local(&checker, &parsed, "after");
    assert_failed_replay(&mut checker, &files, error);
}

fn assert_unchecked_merged_provider(
    checker: &CanonicalCheckerContext<'_>,
    files: &[(FileId, &ParseResult)],
) -> SemanticSymbolId {
    let store = checker.store();
    let owner = store
        .symbol_table(checker.globals())
        .unwrap()
        .get_source("Deferred")
        .unwrap();
    let record = store.symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT
    );
    let declarations = record.declarations().unwrap();
    assert_eq!(declarations.len(), 2);
    let members = store.symbol_table(record.members().unwrap()).unwrap();
    assert_eq!(members.len(), 2);
    for &(file, parsed) in files.iter().filter(|(file, _)| *file != FILE) {
        assert_eq!(
            store.source_file_links(checker.source_file(file).unwrap()),
            None
        );
        let declaration = *declarations.iter().find(|node| node.file == file).unwrap();
        assert!(declaration.is_for(parsed.arena.id(), file));
        assert_eq!(symbol(checker, declaration), owner);
        let NodeData::InterfaceDeclaration(data) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected the original provider interface")
        };
        let [member] = data.members.nodes.as_slice() else {
            panic!("expected one member in each original declaration")
        };
        let member = NodeRef::new(parsed.arena.id(), file, *member);
        let symbol = symbol(checker, member);
        let record = store.symbol(symbol).unwrap();
        assert_eq!(store.get_parent_of_symbol(symbol), Some(owner));
        assert_eq!(record.declarations(), Some(&[member][..]));
        assert_eq!(members.get(record.name()), Some(symbol));
        assert_eq!(store.value_symbol_links(symbol), None);
        assert_eq!(store.type_node_links(member), None);
        assert_eq!(store.signature_links(member), None);
    }
    owner
}

#[test]
fn class_property_conditions_do_not_check_an_unproved_merged_provider() {
    let library = parse_source_file(concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Deferred { untyped; }\n",
    ));
    let provider = parse_source_file("interface Deferred { run(): void; }\n");
    let parsed = parse_source_file(concat!(
        "class Guard { value?: Deferred;\n",
        "  read(): void { if (this.value) { const after = this.value; } }\n",
        "}\n",
    ));
    let files = [
        (LIBRARY_FILE, &library),
        (PROVIDER_FILE, &provider),
        (FILE, &parsed),
    ];
    let mut checker = context(&files, false);
    let owner = assert_unchecked_merged_provider(&checker, &files);
    assert_guard_edges(&checker, &parsed);
    let branch = only_node(&parsed, SyntaxKind::IfStatement);
    let NodeData::IfStatement(data) = &parsed.arena.get(branch.node).unwrap().data else {
        unreachable!()
    };
    let guard = reference(&parsed, data.expression);
    let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(guard));
    assert_eq!(checker.check_source_file(FILE), Err(error));
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    assert_eq!(assert_unchecked_merged_provider(&checker, &files), owner);
    let value = field(&checker, &parsed, "Guard", "value");
    assert_eq!(
        checker.store().type_payload(value.type_).unwrap().symbol(),
        Some(owner)
    );
    let TypeData::Interface(data) = checker.store().type_payload(value.type_).unwrap().data()
    else {
        panic!("expected the authentic cold interface")
    };
    assert!(!data.declared_members_resolved);
    let optional = raw_type(&checker, guard);
    let undefined = checker
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    assert_members(&checker, optional, &[value.type_, undefined]);
    property_query(&checker, &parsed, guard, value, optional);
    assert_unpublished_local(&checker, &parsed, "after");
    assert_failed_replay(&mut checker, &files, error);
    assert_eq!(assert_unchecked_merged_provider(&checker, &files), owner);
}
