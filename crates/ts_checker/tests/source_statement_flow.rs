use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    SourceFunctionUnsupported, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const FLOW_SOURCE: &str = concat!(
    "function sequential(flag: boolean): number {\n",
    "  let first: number = 1, intermediate: number = first;\n",
    "  const second: number = intermediate;\n",
    "  let third: number = second;\n",
    "  if (((flag))) {\n",
    "    const result: number = third;\n",
    "    return result;\n",
    "  } else {\n",
    "    const result: number = first;\n",
    "    return result;\n",
    "  }\n",
    "}\n",
    "function assigned(flag: boolean): \"a\" | \"b\" {\n",
    "  let choice: \"a\" | \"b\" = \"a\";\n",
    "  const beforeChoice: \"a\" = choice;\n",
    "  if (flag) {\n",
    "    const thenChoice: \"a\" = choice;\n",
    "    return thenChoice;\n",
    "  } else {\n",
    "    const elseChoice: \"a\" = choice;\n",
    "    return elseChoice;\n",
    "  }\n",
    "}\n",
    "function stringTruth(value: string | undefined): string | undefined {\n",
    "  const entryString: string | undefined = value;\n",
    "  if (value) {\n",
    "    const truthyString: string = value;\n",
    "    return truthyString;\n",
    "  } else {\n",
    "    const falsyString: string | undefined = value;\n",
    "    return falsyString;\n",
    "  }\n",
    "}\n",
    "function objectTruth(value: object | undefined): object | undefined {\n",
    "  const entryObject: object | undefined = value;\n",
    "  if (value) {\n",
    "    const truthyObject: object = value;\n",
    "    return truthyObject;\n",
    "  } else {\n",
    "    const falsyObject: undefined = value;\n",
    "    return falsyObject;\n",
    "  }\n",
    "}\n",
    "function branchShadow(flag: boolean): string | number {\n",
    "  const shadow: boolean = flag;\n",
    "  if (flag) {\n",
    "    const shadow: number = 1;\n",
    "    return shadow;\n",
    "  } else {\n",
    "    const shadow: string = \"else\";\n",
    "    return shadow;\n",
    "  }\n",
    "}\n",
    "function objectCondition(value: object): number {\n",
    "  if (value) {\n",
    "    return 1;\n",
    "  } else {\n",
    "    return 2;\n",
    "  }\n",
    "}\n",
    "function literalCondition(value: \"yes\"): number {\n",
    "  if (value) {\n",
    "    return 1;\n",
    "  } else {\n",
    "    return 2;\n",
    "  }\n",
    "}\n",
    "function voidUnionCondition(value: void | boolean): number {\n",
    "  if (value) {\n",
    "    return 1;\n",
    "  } else {\n",
    "    return 2;\n",
    "  }\n",
    "}\n",
);

const DIAGNOSTIC_SOURCE: &str = concat!(
    "function ordered(gate: void): number {\n",
    "  const before: number = \"before\";\n",
    "  if (gate) {\n",
    "    const thenLocal: boolean = 0;\n",
    "    return thenLocal;\n",
    "  } else {\n",
    "    const elseLocal: string = false;\n",
    "    return elseLocal;\n",
    "  }\n",
    "}\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/source-statement-flow.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn variable_declarations(parsed: &ParseResult, file: FileId, expected: &str) -> Vec<NodeRef> {
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                record.range.start.get(),
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|(start, _)| *start);
    declarations
        .into_iter()
        .map(|(_, declaration)| declaration)
        .collect()
}

fn variable_initializer(parsed: &ParseResult, file: FileId, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable.initializer.expect("expected initialized variable"),
    )
}

fn unique_variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declarations = variable_declarations(parsed, file, expected);
    let [declaration] = declarations.as_slice() else {
        panic!("expected one declaration named {expected:?}")
    };
    variable_initializer(parsed, file, *declaration)
}

fn rendered_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    variable: &str,
) -> String {
    let initializer = unique_variable_initializer(parsed, file, variable);
    context
        .type_to_string(resolved_type(context, initializer))
        .unwrap_or_else(|error| panic!("failed to render initializer for {variable}: {error:?}"))
}

fn shadow_return_reads(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut reads = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ReturnStatement(statement) = &record.data else {
                return None;
            };
            let expression = statement.expression?;
            let expression_record = parsed.arena.get(expression)?;
            let NodeData::Identifier(identifier) = &expression_record.data else {
                return None;
            };
            (identifier.text == "shadow").then_some((
                expression_record.range.start.get(),
                NodeRef::new(parsed.arena.id(), file, expression),
            ))
        })
        .collect::<Vec<_>>();
    reads.sort_by_key(|(start, _)| *start);
    reads.into_iter().map(|(_, read)| read).collect()
}

fn function_declaration(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("expected function declaration")
}

fn node_of_kind(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("expected one {kind:?} node"))
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn final_if_flow_checks_sequential_locals_narrowing_shadowing_and_warm_state() {
    let parsed = parse_source_file(FLOW_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    for variable in ["intermediate", "second", "third"] {
        assert_eq!(rendered_type(&context, &parsed, file, variable), "number");
    }
    for declaration in variable_declarations(&parsed, file, "result") {
        let initializer = variable_initializer(&parsed, file, declaration);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, initializer))
                .unwrap(),
            "number",
        );
    }

    for variable in ["beforeChoice", "thenChoice", "elseChoice"] {
        assert_eq!(rendered_type(&context, &parsed, file, variable), "\"a\"");
    }
    assert_eq!(
        rendered_type(&context, &parsed, file, "truthyString"),
        "string",
    );
    assert_eq!(
        rendered_type(&context, &parsed, file, "falsyString"),
        "string | undefined",
    );
    assert_eq!(
        rendered_type(&context, &parsed, file, "truthyObject"),
        "object",
    );
    assert_eq!(
        rendered_type(&context, &parsed, file, "falsyObject"),
        "undefined",
    );

    let shadows = variable_declarations(&parsed, file, "shadow");
    let [outer_shadow, then_shadow, else_shadow] = shadows.as_slice() else {
        panic!("expected outer, then, and else shadow declarations")
    };
    let (_, bound) = context.file(file).unwrap();
    let outer_symbol = bound.symbol(*outer_shadow).unwrap();
    let then_symbol = bound.symbol(*then_shadow).unwrap();
    let else_symbol = bound.symbol(*else_shadow).unwrap();
    assert_ne!(outer_symbol, then_symbol);
    assert_ne!(outer_symbol, else_symbol);
    assert_ne!(then_symbol, else_symbol);

    let shadow_reads = shadow_return_reads(&parsed, file);
    let [then_read, else_read] = shadow_reads.as_slice() else {
        panic!("expected one shadow return read in each branch")
    };
    assert_eq!(
        context
            .store()
            .symbol_node_links(*then_read)
            .and_then(|links| links.resolved_symbol),
        Some(then_symbol),
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(*else_read)
            .and_then(|links| links.resolved_symbol),
        Some(else_symbol),
    );

    assert!(is_type_checked(&context, file));
    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
    assert!(is_type_checked(&context, file));
}

#[test]
fn final_if_flow_preserves_local_condition_and_return_diagnostic_order_and_anchors() {
    let parsed = parse_source_file(DIAGNOSTIC_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.expect("expected node-anchored diagnostic");
            (
                diagnostic.diagnostic.code(),
                parsed.arena.get(node.node).unwrap().kind,
                node_text(DIAGNOSTIC_SOURCE, &parsed, node),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, SyntaxKind::Identifier, "before"),
            (1345, SyntaxKind::Identifier, "gate"),
            (2322, SyntaxKind::Identifier, "thenLocal"),
            (2322, SyntaxKind::ReturnStatement, "return thenLocal;"),
            (2322, SyntaxKind::Identifier, "elseLocal"),
            (2322, SyntaxKind::ReturnStatement, "return elseLocal;"),
        ],
    );
    assert_eq!(
        context.diagnostics().as_slice()[1]
            .diagnostic
            .render()
            .unwrap(),
        "An expression of type 'void' cannot be tested for truthiness.",
    );
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
    assert!(is_type_checked(&context, file));
}

fn assert_final_if_boundary_is_atomic(source: &str, file: FileId) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let declaration = function_declaration(&parsed, file);
    let mut context = context(&parsed, file);
    let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let before = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    let first = context.check_source_file(file).unwrap_err();
    assert!(
        matches!(
            &first,
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                SourceFunctionUnsupported::FunctionBody(_)
            ))
        ),
        "unexpected boundary: {first:?}",
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        before,
    );
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(context.store().signature_links(declaration).is_none());
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));

    let second = context.check_source_file(file).unwrap_err();
    assert_eq!(second, first);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        before,
    );
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(context.store().signature_links(declaration).is_none());
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
}

#[test]
fn missing_else_and_inferred_final_if_remain_explicit_atomic_boundaries() {
    assert_final_if_boundary_is_atomic(
        concat!(
            "function missingElse(value: string | undefined): string {\n",
            "  if (value) {\n",
            "    const result: string = value;\n",
            "    return result;\n",
            "  }\n",
            "}\n",
        ),
        FileId::new(2),
    );
    assert_final_if_boundary_is_atomic(
        concat!(
            "function inferred(value: object | undefined) {\n",
            "  if (value) {\n",
            "    const result: object = value;\n",
            "    return result;\n",
            "  } else {\n",
            "    const result: undefined = value;\n",
            "    return result;\n",
            "  }\n",
            "}\n",
        ),
        FileId::new(3),
    );
}

#[test]
fn final_if_flow_recreates_invocation_state_after_a_later_semantic_failure() {
    let source = concat!(
        "interface Recovery {\n",
        "  (value: number, other: number): string;\n",
        "  (value: string): number;\n",
        "}\n",
        "type Broken = { fn: Recovery };\n",
        "function replay(flag: boolean): number {\n",
        "  let value: number = 1;\n",
        "  if (flag) {\n",
        "    const branch: number = value;\n",
        "    return branch;\n",
        "  } else {\n",
        "    const branch: number = value;\n",
        "    return branch;\n",
        "  }\n",
        "}\n",
        "declare const api: Broken;\n",
        "const stopped = api.fn(true);\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let call = node_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let local_declarations = ["value", "branch"]
        .into_iter()
        .flat_map(|name| variable_declarations(&parsed, file, name))
        .collect::<Vec<_>>();
    let mut context = context(&parsed, file);

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Call(call)),
    );
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
    let (_, bound) = context.file(file).unwrap();
    for declaration in &local_declarations {
        let symbol = bound.symbol(*declaration).unwrap();
        assert!(context.store().value_symbol_links(symbol).is_none());
        let initializer = variable_initializer(&parsed, file, *declaration);
        assert!(context.store().type_node_links(initializer).is_some());
    }
    let first_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Call(call)),
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        first_counts,
    );
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
    let (_, bound) = context.file(file).unwrap();
    for declaration in local_declarations {
        let symbol = bound.symbol(declaration).unwrap();
        assert!(context.store().value_symbol_links(symbol).is_none());
    }
}

#[test]
fn function_declaration_flow_starts_captured_variables_at_their_declared_types() {
    let source = concat!(
        "const fixed: string | number = \"fixed\";\n",
        "let mutable: string | number = \"mutable\";\n",
        "function capture(flag: boolean): string {\n",
        "  const fromConst: string = fixed;\n",
        "  const fromLet: string = mutable;\n",
        "  if (flag) {\n",
        "    return \"ok\";\n",
        "  } else {\n",
        "    return mutable;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(5);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.expect("expected node-anchored diagnostic");
            (
                diagnostic.diagnostic.code(),
                parsed.arena.get(node.node).unwrap().kind,
                node_text(source, &parsed, node),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, SyntaxKind::Identifier, "fromConst"),
            (2322, SyntaxKind::Identifier, "fromLet"),
            (2322, SyntaxKind::ReturnStatement, "return mutable;"),
        ],
    );
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}

#[test]
fn structural_thenable_condition_remains_a_stable_semantic_boundary() {
    let source = concat!(
        "type Thenable = { then: (onfulfilled: (value: number) => unknown) => unknown };\n",
        "function structural(value: Thenable): number {\n",
        "  if (value) {\n",
        "    return 1;\n",
        "  } else {\n",
        "    return 2;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(6);
    let mut context = context(&parsed, file);

    let first = context.check_source_file(file).unwrap_err();
    assert!(matches!(
        first,
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
            SourceFunctionUnsupported::FunctionBody(_)
        ))
    ));
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
    let first_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    assert_eq!(context.check_source_file(file), Err(first));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        first_counts,
    );
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
}

#[test]
fn joined_if_flow_restores_the_named_union_before_trailing_statements() {
    let source = concat!(
        "type Choice = \"yes\" | \"\" | undefined;\n",
        "function joined(value: Choice): Choice {\n",
        "  const before: Choice = value;\n",
        "  if (((value))) {\n",
        "    const truthy: \"yes\" = value;\n",
        "  } else {\n",
        "    const falsy: \"\" | undefined = value;\n",
        "  }\n",
        "  const after: Choice = value;\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(7);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(rendered_type(&context, &parsed, file, "before"), "Choice");
    assert_eq!(rendered_type(&context, &parsed, file, "truthy"), "\"yes\"");
    assert_eq!(
        rendered_type(&context, &parsed, file, "falsy"),
        "\"\" | undefined",
    );
    assert_eq!(rendered_type(&context, &parsed, file, "after"), "Choice");
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}

#[test]
fn joined_if_flow_preserves_branch_then_trailing_diagnostic_order() {
    let source = concat!(
        "type Choice = \"yes\" | \"\" | undefined;\n",
        "function joinedErrors(value: Choice): Choice {\n",
        "  if (value) {\n",
        "    const badTruthy: \"\" = value;\n",
        "  } else {\n",
        "    const badFalsy: \"yes\" = value;\n",
        "  }\n",
        "  const badAfter: \"yes\" = value;\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.expect("expected node-anchored diagnostic");
            (
                diagnostic.diagnostic.code(),
                parsed.arena.get(node.node).unwrap().kind,
                node_text(source, &parsed, node),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, SyntaxKind::Identifier, "badTruthy"),
            (2322, SyntaxKind::Identifier, "badFalsy"),
            (2322, SyntaxKind::Identifier, "badAfter"),
        ],
    );
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}

#[test]
fn joined_if_branch_returns_remain_an_atomic_boundary() {
    assert_final_if_boundary_is_atomic(
        concat!(
            "type Choice = \"yes\" | \"\" | undefined;\n",
            "function branchReturn(value: Choice): Choice {\n",
            "  if (value) {\n",
            "    return value;\n",
            "  } else {\n",
            "    const falsy: \"\" | undefined = value;\n",
            "  }\n",
            "  const after: Choice = value;\n",
            "  return value;\n",
            "}\n",
        ),
        FileId::new(9),
    );
}

#[test]
fn final_if_accepts_direct_and_mixed_return_branches() {
    let source = concat!(
        "function direct(value: string | undefined): string | undefined {\n",
        "  if (value) return value;\n",
        "  else return value;\n",
        "}\n",
        "function mixedThen(value: string | undefined): string | undefined {\n",
        "  if (value) {\n",
        "    const narrowed: string = value;\n",
        "    return narrowed;\n",
        "  } else return value;\n",
        "}\n",
        "function mixedElse(value: string | undefined): string | undefined {\n",
        "  if (value) return value;\n",
        "  else {\n",
        "    const remaining: string | undefined = value;\n",
        "    return remaining;\n",
        "  }\n",
        "}\n",
        "function typed(value: string | number): string | number {\n",
        "  if (typeof value === \"string\") return value;\n",
        "  else return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(10);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(rendered_type(&context, &parsed, file, "narrowed"), "string");
    assert_eq!(
        rendered_type(&context, &parsed, file, "remaining"),
        "string | undefined",
    );

    let mut returns = parsed
        .arena
        .iter()
        .filter_map(|(_, node)| {
            let NodeData::ReturnStatement(statement) = &node.data else {
                return None;
            };
            statement.expression.map(|expression| {
                (
                    node.range.start.get(),
                    NodeRef::new(parsed.arena.id(), file, expression),
                )
            })
        })
        .collect::<Vec<_>>();
    returns.sort_by_key(|(start, _)| *start);
    let return_types = returns
        .into_iter()
        .map(|(_, expression)| {
            context
                .type_to_string(resolved_type(&context, expression))
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        return_types,
        [
            "string",
            "string | undefined",
            "string",
            "string | undefined",
            "string",
            "string | undefined",
            "string",
            "number",
        ],
    );

    let counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        counts,
    );
}

#[test]
fn assignments_to_type_only_namespaces_report_ts2708_and_keep_expression_types() {
    let source = "namespace A {}\nA = undefined;\n";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_160);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one namespace assignment diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2708);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Cannot use namespace 'A' as a value.",
    );
    assert_eq!(node_text(source, &parsed, diagnostic.node.unwrap()), "A",);

    let assignment = node_of_kind(&parsed, file, SyntaxKind::BinaryExpression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("expected namespace assignment")
    };
    let left = NodeRef::new(parsed.arena.id(), file, binary.left);
    let right = NodeRef::new(parsed.arena.id(), file, binary.right);
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, left))
            .unwrap(),
        "any",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, assignment))
            .unwrap(),
        "undefined",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, right))
            .unwrap(),
        "undefined",
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn numeric_runtime_namespace_variables_keep_inferred_and_literal_types() {
    let parsed = parse_source_file("namespace Values { var count = 10; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_161);
    let mut context = context(&parsed, file);
    let declarations = variable_declarations(&parsed, file, "count");
    let [declaration] = declarations.as_slice() else {
        panic!("expected one namespace variable")
    };
    let declaration = *declaration;
    let initializer = variable_initializer(&parsed, file, declaration);
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    assert_eq!(
        context
            .type_to_string(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                    .unwrap(),
            )
            .unwrap(),
        "number",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, initializer))
            .unwrap(),
        "10",
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
