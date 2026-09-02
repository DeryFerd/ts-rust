use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_975);

fn source(then_write: &str, else_write: &str) -> String {
    format!(
        "interface Context {{\n\
           fetchFn: (path: string) => string;\n\
           label: string;\n\
           readonly fixed: string;\n\
         }}\n\
         interface Behavior {{\n\
           onFetch: (context: Context, enabled: boolean) => void;\n\
         }}\n\
         const behavior: Behavior = {{\n\
           onFetch: (context, enabled) => {{\n\
             if (enabled) {{ {then_write}; }}\n\
             else {{ {else_write}; }}\n\
           }}\n\
         }};"
    )
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
                EscapedName::source("\"/project/arrow-member-assignments.ts\""),
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

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn value_type(checker: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a callable object");
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    *signature
}

fn context_declaration(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == "Context").then_some(node(parsed, id))
        })
        .unwrap()
}

fn on_fetch(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::PropertyAssignment(property) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(property.name)?.data else {
                return None;
            };
            (name.text == "onFetch").then_some(node(parsed, property.initializer))
        })
        .unwrap()
}

fn property_declaration(parsed: &ParseResult, owner: NodeRef, name: &str) -> NodeRef {
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        unreachable!();
    };
    interface
        .members
        .nodes
        .iter()
        .find_map(|&id| {
            let NodeData::PropertySignatureDeclaration(property) = &parsed.arena.get(id)?.data else {
                return None;
            };
            let NodeData::Identifier(actual) = &parsed.arena.get(property.name)?.data else {
                return None;
            };
            (actual.text == name).then_some(node(parsed, id))
        })
        .unwrap()
}

#[derive(Clone, Copy)]
struct Assignment {
    expression: NodeRef,
    left: NodeRef,
    receiver: NodeRef,
    name: NodeRef,
    right: NodeRef,
}

fn assignments(parsed: &ParseResult) -> Vec<Assignment> {
    let mut assignments = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            assert_eq!(
                parsed.arena.get(binary.operator_token).unwrap().kind,
                SyntaxKind::EqualsToken,
            );
            let NodeData::PropertyAccessExpression(property) =
                &parsed.arena.get(binary.left).unwrap().data
            else {
                panic!("the fixture must assign to an actual property");
            };
            assert!(property.question_dot_token.is_none());
            Some(Assignment {
                expression: node(parsed, id),
                left: node(parsed, binary.left),
                receiver: node(parsed, property.expression),
                name: node(parsed, property.name),
                right: node(parsed, binary.right),
            })
        })
        .collect::<Vec<_>>();
    assignments.sort_by_key(|assignment| {
        parsed.arena.get(assignment.expression.node).unwrap().range.start
    });
    assert_eq!(assignments.len(), 2);
    assignments
}

fn assert_contextual_rhs(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    right: NodeRef,
    target_declaration: NodeRef,
    target: TypeId,
) {
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(right.node).unwrap().data else {
        panic!("the valid write must keep its source arrow");
    };
    let owner = symbol(checker, right);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(record.declarations(), Some(&[right][..]));
    assert_eq!(record.value_declaration(), Some(right));
    let type_ = cached_type(checker, right);
    assert_eq!(value_type(checker, owner), type_);
    assert_eq!(checker.store().type_payload(type_).unwrap().symbol(), Some(owner));
    assert_ne!(type_, target);

    let signature = callable_signature(checker, type_);
    let target_signature = callable_signature(checker, target);
    assert_ne!(signature, target_signature);
    let NodeData::PropertySignatureDeclaration(property) =
        &parsed.arena.get(target_declaration.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        checker.store().signature(target_signature).unwrap().declaration(),
        Some(node(parsed, property.type_)),
    );
    assert_eq!(
        checker.store().signature_links(right).unwrap().resolved_signature.signature(),
        Some(signature),
    );
    let [parameter] = arrow.parameters.nodes.as_slice() else {
        panic!("the RHS has one unannotated parameter");
    };
    let parameter = node(parsed, *parameter);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!();
    };
    assert!(data.type_.is_none());
    let parameter_symbol = symbol(checker, parameter);
    let parameter_name = node(parsed, data.name);
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(value_type(checker, parameter_symbol), string);
    assert_eq!(checker.get_type_at_location(parameter_name), Ok(string));
    assert_eq!(checker.get_symbol_at_location(parameter_name), Ok(Some(parameter_symbol)));
    assert_eq!(checker.get_type_at_location(node(parsed, arrow.body)), Ok(string));
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, arrow.body)),
        Ok(Some(parameter_symbol)),
    );
    let source_signature = checker.store().signature(signature).unwrap();
    assert_eq!(source_signature.declaration(), Some(right));
    assert_eq!(source_signature.parameters(), &[parameter_symbol]);
    assert!(source_signature.type_parameters().is_empty());
    assert_eq!(source_signature.target(), None);
    assert_eq!(source_signature.mapper(), None);
    assert_eq!(checker.get_return_type_of_signature(signature), Ok(string));
    let target_parameter = checker.store().signature(target_signature).unwrap().parameters()[0];
    assert_ne!(parameter_symbol, target_parameter);
    assert_eq!(value_type(checker, target_parameter), string);
    assert_eq!(checker.get_return_type_of_signature(target_signature), Ok(string));
}

fn assert_writes(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    assignments: &[Assignment],
) {
    let declaration = context_declaration(parsed);
    let owner = symbol(checker, declaration);
    let callback = on_fetch(parsed);
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(callback.node).unwrap().data else {
        unreachable!();
    };
    let [context_parameter, enabled_parameter] = arrow.parameters.nodes.as_slice() else {
        panic!("onFetch must retain both source parameters");
    };
    let context_parameter = node(parsed, *context_parameter);
    let context_symbol = symbol(checker, context_parameter);
    let receiver_type = value_type(checker, context_symbol);
    assert_eq!(checker.store().type_payload(receiver_type).unwrap().symbol(), Some(owner));
    let callback_type = cached_type(checker, callback);
    let callback_signature = callable_signature(checker, callback_type);
    assert_eq!(
        checker.store().signature(callback_signature).unwrap().declaration(),
        Some(callback),
    );
    assert_eq!(
        checker.store().signature(callback_signature).unwrap().parameters(),
        &[context_symbol, symbol(checker, node(parsed, *enabled_parameter))],
    );
    let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(checker.get_return_type_of_signature(callback_signature), Ok(void));

    for assignment in assignments {
        let NodeData::Identifier(name) = &parsed.arena.get(assignment.name.node).unwrap().data
        else {
            unreachable!();
        };
        let property_node = property_declaration(parsed, declaration, &name.text);
        let property = symbol(checker, property_node);
        let property_record = checker.store().symbol(property).unwrap();
        assert_eq!(property_record.flags(), SymbolFlags::PROPERTY);
        assert_eq!(property_record.declarations(), Some(&[property_node][..]));
        assert_eq!(property_record.value_declaration(), Some(property_node));
        assert_eq!(property_record.parent(), Some(owner));
        let members = checker.store().symbol(owner).unwrap().members().unwrap();
        assert_eq!(
            checker.store().symbol_table(members).unwrap().get_source(&name.text),
            Some(property),
        );
        let declared = value_type(checker, property);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let target = if name.text == "fixed" { bootstrap.error_type } else { declared };
        if name.text != "fetchFn" {
            assert_eq!(declared, bootstrap.string_type);
        }
        assert_eq!(cached_type(checker, assignment.receiver), receiver_type);
        assert_eq!(cached_type(checker, assignment.left), target);
        assert_eq!(
            checker.store().symbol_node_links(assignment.left).unwrap().resolved_symbol,
            Some(property),
        );
        let right = cached_type(checker, assignment.right);
        assert_eq!(cached_type(checker, assignment.expression), right);
        for (node, type_) in [
            (assignment.receiver, receiver_type),
            (assignment.left, target),
            (assignment.right, right),
            (assignment.expression, right),
        ] {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        assert_eq!(checker.get_symbol_at_location(assignment.receiver), Ok(Some(context_symbol)));
        assert_eq!(checker.get_symbol_at_location(assignment.left), Ok(Some(property)));
        assert_eq!(checker.get_symbol_at_location(assignment.name), Ok(Some(property)));
        if name.text == "fetchFn" {
            assert_contextual_rhs(checker, parsed, assignment.right, property_node, declared);
        }
    }
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    assignments: &[Assignment],
    code: Option<u32>,
) {
    let diagnostics = checker.diagnostics().as_slice();
    let Some(code) = code else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        return;
    };
    let [diagnostic] = diagnostics else {
        panic!("expected only error {code}: {diagnostics:?}");
    };
    assert_eq!(diagnostic.diagnostic.code(), code);
    let (node, arguments, message) = match code {
        2322 => (
            assignments[0].left,
            vec!["number", "string"],
            "Type 'number' is not assignable to type 'string'.",
        ),
        2540 => (
            assignments[0].name,
            vec!["fixed"],
            "Cannot assign to 'fixed' because it is a read-only property.",
        ),
        _ => unreachable!(),
    };
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(
        diagnostic.diagnostic.arguments.iter().map(String::as_str).collect::<Vec<_>>(),
        arguments,
    );
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert!(diagnostic.diagnostic.details.is_empty());
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 5],
    types: Vec<Option<TypeNodeLinks>>,
    symbols: Vec<Option<SymbolNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(checker: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = checker.store();
    let nodes = parsed.arena.iter().map(|(id, _)| node(parsed, id)).collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes.iter().map(|node| store.type_node_links(*node).cloned()).collect(),
        symbols: nodes.iter().map(|node| store.symbol_node_links(*node).cloned()).collect(),
        signatures: nodes.iter().map(|node| store.signature_links(*node).cloned()).collect(),
        values: nodes
            .iter()
            .filter_map(|node| checker.file(FILE).unwrap().1.symbol(*node))
            .map(|symbol| {
                store.value_symbol_links(store.get_merged_symbol(symbol).unwrap()).cloned()
            })
            .collect(),
        source: store.source_file_links(checker.source_file(FILE).unwrap()).cloned(),
        diagnostics: checker.diagnostics().clone(),
    }
}

fn check_case(source: &str, code: Option<u32>) {
    let parsed = parse_source_file(source);
    let assignments = assignments(&parsed);
    // Each fresh context starts at source checking, the then assignment, or its RHS.
    for first in [None, Some(assignments[0].expression), Some(assignments[0].right)] {
        let mut checker = context(&parsed);
        let first_type = first.map(|node| (node, checker.get_type_at_location(node).unwrap()));
        checker.check_source_file(FILE).unwrap();
        assert_diagnostics(&checker, &assignments, code);
        assert_writes(&mut checker, &parsed, &assignments);
        if let Some((node, type_)) = first_type {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        let warm = snapshot(&checker, &parsed);
        for recheck in [false, true] {
            if recheck {
                checker.recheck_source_file(FILE).unwrap();
            } else {
                checker.check_source_file(FILE).unwrap();
            }
            assert_diagnostics(&checker, &assignments, code);
            assert_writes(&mut checker, &parsed, &assignments);
            assert_eq!(snapshot(&checker, &parsed), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn arrow_member_writes_contextually_type_function_rhs_and_replay() {
    check_case(
        &source("context.fetchFn = path => path", "context.fetchFn = path => path"),
        None,
    );
}

#[test]
fn arrow_member_writes_report_native_assignment_errors_and_replay() {
    check_case(
        &source("context.label = 1", "context.label = 'next'"),
        Some(2322),
    );
}

#[test]
fn arrow_member_writes_report_native_readonly_errors_and_replay() {
    check_case(
        &source("context.fixed = 'new'", "context.label = 'next'"),
        Some(2540),
    );
}
