use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "function withDefault(seed: number, value: number = seed + 1): number { return value; }\n",
    "function incompatible(value: number = 'wrong'): number { return value; }\n",
    "const arrow = (seed: number, value: number = seed + 2): number => value;\n",
    "const omitted: number = withDefault(1);\n",
    "const explicitUndefined: number = withDefault(1, undefined);\n",
    "const supplied: number = withDefault(1, 4);\n",
    "const arrowOmitted: number = arrow(1);\n",
    "const wrongCall: number = withDefault(1, 'bad');\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/parameter-initializers.ts\""),
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

fn initialized_parameter(
    source: &str,
    parsed: &ParseResult,
    file: FileId,
    initializer_text: &str,
) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let initializer = parameter.initializer?;
            let initializer = NodeRef::new(parsed.arena.id(), file, initializer);
            (node_text(source, parsed, initializer) == initializer_text)
                .then_some((NodeRef::new(parsed.arena.id(), file, node), initializer))
        })
        .unwrap_or_else(|| panic!("missing initialized parameter {initializer_text:?}"))
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then_some(variable.initializer)
                .flatten()
                .map(|initializer| NodeRef::new(parsed.arena.id(), file, initializer))
        })
        .unwrap_or_else(|| panic!("missing variable initializer for {expected}"))
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

#[test]
fn default_parameter_initializers_check_assignability_scope_calls_and_warm_state() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(SOURCE, &parsed, diagnostic.node.unwrap()),
                diagnostic.diagnostic.render().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (
                2322,
                "value: number = 'wrong'",
                "Type 'string' is not assignable to type 'number'.".to_owned(),
            ),
            (
                2345,
                "'bad'",
                "Argument of type '\"bad\"' is not assignable to parameter of type 'number | undefined'."
                    .to_owned(),
            ),
        ]
    );

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for initializer_text in ["seed + 1", "'wrong'", "seed + 2"] {
        let (parameter, initializer) =
            initialized_parameter(SOURCE, &parsed, file, initializer_text);
        assert!(context.store().type_node_links(initializer).is_some());
        let (_, bound) = context.file(file).unwrap();
        let symbol = bound.symbol(parameter).unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(number),
            "the parameter body type must exclude the call-only undefined",
        );
    }

    let earlier_parameter_reads = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            let parent = record.parent.and_then(|parent| parsed.arena.get(parent))?;
            (identifier.text == "seed" && parent.kind == SyntaxKind::BinaryExpression)
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    assert_eq!(earlier_parameter_reads.len(), 2);
    for read in earlier_parameter_reads {
        assert_eq!(resolved_type(&context, read), number);
        assert!(
            context
                .store()
                .symbol_node_links(read)
                .is_some_and(|links| links.resolved_symbol.is_some())
        );
    }

    for name in [
        "omitted",
        "explicitUndefined",
        "supplied",
        "arrowOmitted",
        "wrongCall",
    ] {
        assert_eq!(
            resolved_type(&context, variable_initializer(&parsed, file, name)),
            number,
            "call result for {name}",
        );
    }

    let body_reads = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| match &record.data {
            NodeData::ReturnStatement(statement) => statement.expression,
            NodeData::ArrowFunction(arrow)
                if parsed
                    .arena
                    .get(arrow.body)
                    .is_some_and(|body| body.kind == SyntaxKind::Identifier) =>
            {
                Some(arrow.body)
            }
            _ => None,
        })
        .map(|node| NodeRef::new(parsed.arena.id(), file, node))
        .collect::<Vec<_>>();
    assert_eq!(body_reads.len(), 3);
    assert!(
        body_reads
            .into_iter()
            .all(|body| resolved_type(&context, body) == number)
    );

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
fn unsupported_initializer_and_arrow_body_retries_do_not_publish_partial_state() {
    for (index, source) in [
        "function unsupported(seed: number, value: number = true ? seed : 0): number { return value; }",
        "const unsupported = (seed: number, value: number = seed): number => true ? value : seed;",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(10 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );

        let first = context.check_source_file(file).unwrap_err();
        assert!(matches!(first, SourceCheckError::Unsupported(_)));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            before,
        );
        assert!(context.diagnostics().is_empty());

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
        assert!(context.diagnostics().is_empty());
    }
}
