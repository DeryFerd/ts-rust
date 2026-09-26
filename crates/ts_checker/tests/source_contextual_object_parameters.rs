use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_906);
const TIMER_PROPERTIES: &str = r#"
    setTimeout: (callback, delay) => setTimeout(callback, delay),
    clearTimeout: (timeoutId) => clearTimeout(timeoutId),
    setInterval: (callback, delay) => setInterval(callback, delay),
    clearInterval: (intervalId) => clearInterval(intervalId),
"#;

fn timer_source(computed_timer_id: bool, properties: &str) -> String {
    let symbols = if computed_timer_id {
        "interface SymbolConstructor { readonly toPrimitive: unique symbol; } \
         declare var Symbol: SymbolConstructor;"
    } else {
        ""
    };
    let timer_id = if computed_timer_id {
        "number | { [Symbol.toPrimitive]: () => number }"
    } else {
        "number"
    };
    format!(
        r#"
{symbols}
type TimeoutCallback = (_: void) => void;
type ManagedTimerId = {timer_id};
type TimeoutProvider<TTimerId extends ManagedTimerId = ManagedTimerId> = {{
    readonly setTimeout: (callback: TimeoutCallback, delay: number) => TTimerId;
    readonly clearTimeout: (timeoutId: TTimerId | undefined) => void;
    readonly setInterval: (callback: TimeoutCallback, delay: number) => TTimerId;
    readonly clearInterval: (intervalId: TTimerId | undefined) => void;
}};
declare function setTimeout(callback: TimeoutCallback, delay: number): number;
declare function clearTimeout(timeoutId: ManagedTimerId | undefined): void;
declare function setInterval(callback: TimeoutCallback, delay: number): number;
declare function clearInterval(intervalId: ManagedTimerId | undefined): void;
const defaultTimeoutProvider: TimeoutProvider = {{ {properties} }};
"#
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
                EscapedName::source("\"/project/contextual-object-parameters.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(bound).unwrap()
}

struct Arrow {
    property: String,
    declaration: NodeRef,
    parameters: Vec<NodeRef>,
    body: NodeRef,
}

fn arrows(parsed: &ParseResult) -> Vec<Arrow> {
    let object = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "defaultTimeoutProvider").then(|| variable.initializer.unwrap())
        })
        .unwrap();
    let NodeData::ObjectLiteralExpression(object) = &parsed.arena.get(object).unwrap().data else {
        panic!("expected the actual annotated object initializer");
    };
    object
        .properties
        .nodes
        .iter()
        .map(|&property| {
            let NodeData::PropertyAssignment(assignment) =
                &parsed.arena.get(property).unwrap().data
            else {
                panic!("expected the actual property assignment");
            };
            let NodeData::Identifier(name) = &parsed.arena.get(assignment.name).unwrap().data
            else {
                panic!("expected a named timer property");
            };
            let record = parsed.arena.get(assignment.initializer).unwrap();
            let NodeData::ArrowFunction(arrow) = &record.data else {
                panic!("expected the actual property arrow");
            };
            assert_eq!(record.kind, SyntaxKind::ArrowFunction);
            assert_eq!(record.parent, Some(property));
            assert!(arrow.type_parameters.is_none());
            assert!(arrow.type_.is_none());
            Arrow {
                property: name.text.clone(),
                declaration: node(parsed, assignment.initializer),
                parameters: arrow
                    .parameters
                    .nodes
                    .iter()
                    .map(|&id| node(parsed, id))
                    .collect(),
                body: node(parsed, arrow.body),
            }
        })
        .collect()
}

fn native_parameters(parsed: &ParseResult, expected: &str) -> Vec<NodeRef> {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                function
                    .parameters
                    .nodes
                    .iter()
                    .map(|&id| node(parsed, id))
                    .collect()
            })
        })
        .unwrap()
}

fn body_read(parsed: &ParseResult, arrow: &Arrow, expected: &str) -> NodeRef {
    let body = parsed.arena.get(arrow.body.node).unwrap().range;
    let mut reads = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::Identifier(name) = &record.data else {
            return None;
        };
        (name.text == expected && record.range.start >= body.start && record.range.end <= body.end)
            .then_some(node(parsed, id))
    });
    let read = reads.next().unwrap();
    assert!(reads.next().is_none());
    read
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[allow(clippy::too_many_lines)] // Keep parameter ownership, signature order, and replay together.
fn assert_types_and_replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let mut types: Vec<(NodeRef, TypeId)> = Vec::new();
    let mut symbols = Vec::new();
    let mut signatures = Vec::new();
    for arrow in arrows(parsed) {
        let owner = symbol(checker, arrow.declaration);
        assert_eq!(
            checker.store().symbol(owner).unwrap().flags(),
            SymbolFlags::FUNCTION,
        );
        assert_eq!(
            checker.get_symbol_declarations(owner).unwrap(),
            &[arrow.declaration],
        );
        let callable = checker.get_type_at_location(arrow.declaration).unwrap();
        assert_eq!(
            checker.store().type_payload(callable).unwrap().symbol(),
            Some(owner),
        );
        types.push((arrow.declaration, callable));
        let targets = native_parameters(parsed, &arrow.property);
        assert_eq!(arrow.parameters.len(), targets.len());
        let mut parameters = Vec::new();
        for (&declaration, &target) in arrow.parameters.iter().zip(&targets) {
            let record = parsed.arena.get(declaration.node).unwrap();
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                panic!("expected the actual arrow parameter");
            };
            assert_eq!(record.parent, Some(arrow.declaration.node));
            assert!(parameter.initializer.is_none());
            let NodeData::Identifier(name) = &parsed.arena.get(parameter.name).unwrap().data else {
                panic!("only identifier parameters are in this repair");
            };
            let expected = checker
                .get_type_at_location(parameter.type_.map_or(target, |id| node(parsed, id)))
                .unwrap();
            let parameter_symbol = symbol(checker, declaration);
            assert_ne!(parameter_symbol, symbol(checker, target));
            assert_eq!(
                checker.get_symbol_declarations(parameter_symbol).unwrap(),
                &[declaration],
            );
            assert_eq!(
                checker.store().symbol(parameter_symbol).unwrap().flags(),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            );
            assert_eq!(
                checker.store().value_symbol_links(parameter_symbol).unwrap().resolved_type,
                Some(expected),
            );
            let read = body_read(parsed, &arrow, &name.text);
            for location in [declaration, node(parsed, parameter.name), read] {
                assert_eq!(checker.get_type_at_location(location), Ok(expected));
                assert_eq!(
                    checker.get_symbol_at_location(location),
                    Ok(Some(parameter_symbol)),
                );
                assert_eq!(
                    checker.file(FILE).unwrap().1.container(location),
                    Some(arrow.declaration),
                );
                types.push((location, expected));
                symbols.push((location, parameter_symbol));
            }
            parameters.push(parameter_symbol);
        }
        let signature = checker
            .store()
            .signature_links(arrow.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let returned = checker.get_type_at_location(arrow.body).unwrap();
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let expected_return = if arrow.property.starts_with("set") {
            bootstrap.number_type
        } else {
            bootstrap.void_type
        };
        assert_eq!(returned, expected_return);
        let record = checker.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(arrow.declaration));
        assert_eq!(record.parameters(), parameters);
        assert_eq!(usize::try_from(record.min_argument_count()).unwrap(), parameters.len());
        assert_eq!(record.resolved_return_type(), Some(expected_return));
        assert!(record.type_parameters().is_empty());
        assert!(record.target().is_none());
        assert!(record.mapper().is_none());
        types.push((arrow.body, returned));
        signatures.push((
            arrow.declaration,
            checker.store().signature_links(arrow.declaration).cloned(),
        ));
    }
    let before = counts(checker);
    let diagnostics = checker.diagnostics().clone();
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for &(location, expected) in &types {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        for &(location, expected) in &symbols {
            assert_eq!(checker.get_symbol_at_location(location), Ok(Some(expected)));
        }
        for (arrow, expected) in &signatures {
            assert_eq!(checker.store().signature_links(*arrow).cloned(), *expected);
        }
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(counts(checker), before);
    }
}

#[test]
fn query_timer_provider_assigns_both_contextual_parameters() {
    // The numeric reduction isolates parameters. The other case keeps Query's computed constraint.
    for computed_timer_id in [false, true] {
        let source = timer_source(computed_timer_id, TIMER_PROPERTIES);
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        if computed_timer_id {
            let callback = arrows(&parsed)[0].parameters[0];
            checker.get_type_at_location(callback).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
        assert_types_and_replay(&mut checker, &parsed);
    }
}

#[test]
fn contextual_parameters_follow_positions_and_property_names() {
    let source = timer_source(false, r#"
        clearInterval: (handle) => clearInterval(handle),
        setInterval: (wait, job) => setInterval(wait, job),
        clearTimeout: (handle) => clearTimeout(handle),
        setTimeout: (delay, callback) => setTimeout(delay, callback),
    "#);
    let parsed = parse_source_file(&source);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(checker.diagnostics().is_empty());
    assert_types_and_replay(&mut checker, &parsed);
    let arrows = arrows(&parsed);
    assert_ne!(
        symbol(&checker, arrows[0].parameters[0]),
        symbol(&checker, arrows[2].parameters[0]),
    );
}

#[test]
fn contextual_parameters_keep_body_errors_and_explicit_annotations() {
    for (replacement, invalid_arguments) in [
        (
            "setTimeout: (callback, delay) => setTimeout(callback, delay === 0)",
            vec![1],
        ),
        (
            "setTimeout: (callback, delay: number | undefined) => setTimeout(callback, delay)",
            vec![1],
        ),
    ] {
        let properties = TIMER_PROPERTIES.replace(
            "setTimeout: (callback, delay) => setTimeout(callback, delay)",
            replacement,
        );
        let source = timer_source(false, &properties);
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let arrow = &arrows(&parsed)[0];
        let NodeData::CallExpression(call) = &parsed.arena.get(arrow.body.node).unwrap().data else {
            panic!("expected the original timer call");
        };
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), invalid_arguments.len(), "{diagnostics:?}");
        for (diagnostic, index) in diagnostics.iter().zip(invalid_arguments) {
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.node, Some(node(&parsed, call.arguments.nodes[index])));
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
        }
        assert_types_and_replay(&mut checker, &parsed);
    }
}

#[test]
fn contextual_object_parameters_keep_unsupported_shapes_unpublished() {
    for source in [
        "const defaultTimeoutProvider = { run: (first, second) => first };",
        "const defaultTimeoutProvider: { run: (first: number) => number } = \
         { run: (first, second) => first };",
        "const defaultTimeoutProvider: { run: (first: number, second: number) => number } = \
         { run: (first = 1, second) => first };",
        "const defaultTimeoutProvider: { run: (first: number, second: number) => number } = \
         { run: (first, ...remaining) => first };",
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        let arrow = &arrows(&parsed)[0];
        let owners = std::iter::once(arrow.declaration)
            .chain(arrow.parameters.iter().copied())
            .map(|declaration| {
                let owner = symbol(&checker, declaration);
                (owner, checker.store().value_symbol_links(owner).cloned())
            })
            .collect::<Vec<_>>();
        let error = checker.check_source_file(FILE).unwrap_err();
        assert!(
            matches!(error, SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(_))),
            "{source}: {error:?}",
        );
        assert_eq!(checker.check_source_file(FILE).unwrap_err(), error);
        assert!(checker.store().signature_links(arrow.declaration).is_none());
        assert!(checker.store().type_node_links(arrow.declaration).is_none());
        for (owner, before) in owners {
            assert_eq!(checker.store().value_symbol_links(owner).cloned(), before);
        }
        assert!(checker.diagnostics().is_empty());
    }
}
