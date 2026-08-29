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

fn context(
    parsed: &ParseResult,
    file: FileId,
    strict_null_checks: bool,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/object-equality.ts\""),
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
                strict_null_checks,
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

fn binary_expression(source: &str, parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (record.kind == SyntaxKind::BinaryExpression
                && node_text(source, parsed, node) == expected)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing binary expression {expected:?}"))
}

fn binary_operands(parsed: &ParseResult, expression: NodeRef) -> [NodeRef; 2] {
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("expected a binary expression at {expression:?}")
    };
    [binary.left, binary.right].map(|node| NodeRef::new(expression.arena, expression.file, node))
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
                .map(|node| NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing initializer for {expected}"))
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn semantic_counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.mapper_len(),
        store.signature_len(),
        store.type_alias_len(),
    ]
}

fn assert_boolean_results(context: &CanonicalCheckerContext<'_>, expressions: &[NodeRef]) {
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    for &expression in expressions {
        assert_eq!(resolved_type(context, expression), boolean);
    }
}

fn assert_warm_recheck(context: &mut CanonicalCheckerContext<'_>, file: FileId, nodes: &[NodeRef]) {
    let counts = semantic_counts(context);
    let diagnostics = context.diagnostics().clone();
    let links = nodes
        .iter()
        .map(|&node| context.store().type_node_links(node).cloned())
        .collect::<Vec<_>>();

    context.recheck_source_file(file).unwrap();

    assert_eq!(semantic_counts(context), counts);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(
        nodes
            .iter()
            .map(|&node| context.store().type_node_links(node).cloned())
            .collect::<Vec<_>>(),
        links,
    );
    let source_file = context.source_file(file).unwrap();
    assert!(
        context
            .store()
            .source_file_links(source_file)
            .unwrap()
            .type_checked
    );
}

#[test]
fn all_object_equality_operators_accept_same_and_compatible_types() {
    let source = concat!(
        "interface Value { value: number; }\n",
        "interface Compatible { value: number; extra: string; }\n",
        "declare const value: Value;\n",
        "declare const compatible: Compatible;\n",
        "const sameEqual = value == value;\n",
        "const sameUnequal = value != value;\n",
        "const sameStrictEqual = value === value;\n",
        "const sameStrictUnequal = value !== value;\n",
        "const compatibleEqual = value == compatible;\n",
        "const compatibleUnequal = compatible != value;\n",
        "const compatibleStrictEqual = value === compatible;\n",
        "const compatibleStrictUnequal = compatible !== value;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file, true);
    context.check_source_file(file).unwrap();

    let expressions = [
        "value == value",
        "value != value",
        "value === value",
        "value !== value",
        "value == compatible",
        "compatible != value",
        "value === compatible",
        "compatible !== value",
    ]
    .map(|text| binary_expression(source, &parsed, file, text));
    assert_boolean_results(&context, &expressions);
    assert!(context.diagnostics().is_empty());

    let [value, compatible] =
        binary_operands(&parsed, expressions[4]).map(|node| resolved_type(&context, node));
    assert_ne!(value, compatible);
    assert_eq!(context.is_type_assignable_to(compatible, value), Ok(true));
    assert_eq!(context.is_type_assignable_to(value, compatible), Ok(false));
    assert_warm_recheck(&mut context, file, &expressions);
}

#[test]
fn object_equality_accepts_optional_properties_when_both_assignments_fail() {
    let source = concat!(
        "interface Left { a?: string; b: number; }\n",
        "interface Right { a: string; b?: number; }\n",
        "declare const left: Left;\n",
        "declare const right: Right;\n",
        "const equal = left == right;\n",
        "const unequal = left != right;\n",
        "const strictEqual = left === right;\n",
        "const strictUnequal = left !== right;\n",
        "const reverseEqual = right == left;\n",
        "const reverseUnequal = right != left;\n",
        "const reverseStrictEqual = right === left;\n",
        "const reverseStrictUnequal = right !== left;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    for strict_null_checks in [false, true] {
        let mut context = context(&parsed, file, strict_null_checks);
        context.check_source_file(file).unwrap();
        let expressions = [
            "left == right",
            "left != right",
            "left === right",
            "left !== right",
            "right == left",
            "right != left",
            "right === left",
            "right !== left",
        ]
        .map(|text| binary_expression(source, &parsed, file, text));
        assert_boolean_results(&context, &expressions);
        assert!(context.diagnostics().is_empty());

        let [left, right] =
            binary_operands(&parsed, expressions[0]).map(|node| resolved_type(&context, node));
        assert_ne!(left, right);
        assert_eq!(context.is_type_assignable_to(left, right), Ok(false));
        assert_eq!(context.is_type_assignable_to(right, left), Ok(false));
        assert_eq!(context.is_type_comparable_to(left, right), Ok(true));
        assert_eq!(context.is_type_comparable_to(right, left), Ok(true));
        assert_warm_recheck(&mut context, file, &expressions);
    }
}

#[test]
fn disjoint_object_equality_reports_exact_binary_nodes_and_ordered_type_names() {
    let source = concat!(
        "interface TextBox { value: string; }\n",
        "interface NumberBox { value: number; }\n",
        "declare const textBox: TextBox;\n",
        "declare const numberBox: NumberBox;\n",
        "const equal = textBox == numberBox;\n",
        "const unequal = textBox != numberBox;\n",
        "const strictEqual = textBox === numberBox;\n",
        "const strictUnequal = textBox !== numberBox;\n",
        "const reverseEqual = numberBox == textBox;\n",
        "const reverseUnequal = numberBox != textBox;\n",
        "const reverseStrictEqual = numberBox === textBox;\n",
        "const reverseStrictUnequal = numberBox !== textBox;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = context(&parsed, file, true);
    context.check_source_file(file).unwrap();

    let expected = [
        ("textBox == numberBox", "TextBox", "NumberBox"),
        ("textBox != numberBox", "TextBox", "NumberBox"),
        ("textBox === numberBox", "TextBox", "NumberBox"),
        ("textBox !== numberBox", "TextBox", "NumberBox"),
        ("numberBox == textBox", "NumberBox", "TextBox"),
        ("numberBox != textBox", "NumberBox", "TextBox"),
        ("numberBox === textBox", "NumberBox", "TextBox"),
        ("numberBox !== textBox", "NumberBox", "TextBox"),
    ];
    let expressions = expected.map(|(text, _, _)| binary_expression(source, &parsed, file, text));
    assert_boolean_results(&context, &expressions);
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len());
    for ((diagnostic, expression), (text, left, right)) in
        diagnostics.iter().zip(expressions).zip(expected)
    {
        assert_eq!(diagnostic.node, Some(expression));
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2367);
        assert_eq!(diagnostic.diagnostic.arguments, [left, right]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!(
                "This comparison appears to be unintentional because the types '{left}' and '{right}' have no overlap."
            ),
        );
        let range = parsed.arena.get(expression.node).unwrap().range;
        let start = source.find(text).unwrap();
        assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
        assert_eq!(
            usize::try_from(range.end.get()).unwrap(),
            start + text.len()
        );
    }
    assert_warm_recheck(&mut context, file, &expressions);
}

#[test]
fn direct_null_and_undefined_object_comparisons_work_in_both_strict_null_modes() {
    let source = concat!(
        "interface Value { value: number; }\n",
        "declare const value: Value;\n",
        "const equalNull = value == null;\n",
        "const unequalNull = value != null;\n",
        "const strictEqualNull = value === null;\n",
        "const strictUnequalNull = value !== null;\n",
        "const nullEqual = null == value;\n",
        "const nullUnequal = null != value;\n",
        "const nullStrictEqual = null === value;\n",
        "const nullStrictUnequal = null !== value;\n",
        "const equalUndefined = value == undefined;\n",
        "const unequalUndefined = value != undefined;\n",
        "const strictEqualUndefined = value === undefined;\n",
        "const strictUnequalUndefined = value !== undefined;\n",
        "const undefinedEqual = undefined == value;\n",
        "const undefinedUnequal = undefined != value;\n",
        "const undefinedStrictEqual = undefined === value;\n",
        "const undefinedStrictUnequal = undefined !== value;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let expressions = [
        "value == null",
        "value != null",
        "value === null",
        "value !== null",
        "null == value",
        "null != value",
        "null === value",
        "null !== value",
        "value == undefined",
        "value != undefined",
        "value === undefined",
        "value !== undefined",
        "undefined == value",
        "undefined != value",
        "undefined === value",
        "undefined !== value",
    ]
    .map(|text| binary_expression(source, &parsed, file, text));
    for strict_null_checks in [false, true] {
        let mut context = context(&parsed, file, strict_null_checks);
        context.check_source_file(file).unwrap();
        assert_boolean_results(&context, &expressions);
        assert!(context.diagnostics().is_empty());
        assert_warm_recheck(&mut context, file, &expressions);
    }
}

#[test]
fn ordinary_observer_comparison_keeps_both_object_parameter_types() {
    let source = concat!(
        "type Observer = { value: number; };\n",
        "function differs(o: Observer, observer: Observer): boolean {\n",
        "  const oBefore: Observer = o;\n",
        "  const observerBefore: Observer = observer;\n",
        "  const different = o !== observer;\n",
        "  const oAfter: Observer = o;\n",
        "  const observerAfter: Observer = observer;\n",
        "  return different;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let mut context = context(&parsed, file, true);
    context.check_source_file(file).unwrap();

    let comparison = binary_expression(source, &parsed, file, "o !== observer");
    assert_boolean_results(&context, &[comparison]);
    assert!(context.diagnostics().is_empty());
    let reads = ["oBefore", "observerBefore", "oAfter", "observerAfter"]
        .map(|name| variable_initializer(&parsed, file, name));
    let [left, right] = binary_operands(&parsed, comparison);
    let observer_type = resolved_type(&context, reads[0]);
    assert_eq!(context.type_to_string(observer_type).unwrap(), "Observer");
    for node in reads.into_iter().chain([left, right]) {
        assert_eq!(resolved_type(&context, node), observer_type);
    }

    let parameters = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            matches!(record.data, NodeData::ParameterDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(parameters.len(), 2);
    let parameter_symbols = parameters
        .iter()
        .map(|&node| context.file(file).unwrap().1.symbol(node).unwrap())
        .collect::<Vec<_>>();
    for &symbol in &parameter_symbols {
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(observer_type),
        );
    }

    assert_warm_recheck(
        &mut context,
        file,
        &[
            comparison, left, right, reads[0], reads[1], reads[2], reads[3],
        ],
    );
    for symbol in parameter_symbols {
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(observer_type),
        );
    }
}

#[test]
fn object_equality_in_an_if_condition_remains_unsupported_without_publication() {
    let source = concat!(
        "function differs(o: object, observer: object): boolean {\n",
        "  if(o!==observer) { return true; } else { return false; }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(5);
    let (declaration, body) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, function.body?),
            ))
        })
        .unwrap();
    let comparison = binary_expression(source, &parsed, file, "o!==observer");
    let mut context = context(&parsed, file, true);
    let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let counts = semantic_counts(&context);
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
        SourceFunctionUnsupported::FunctionBody(body),
    ));

    for _ in 0..2 {
        assert_eq!(context.check_source_file(file), Err(expected));
        assert_eq!(semantic_counts(&context), counts);
        assert!(context.diagnostics().is_empty());
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.store().signature_links(declaration).is_none());
        assert!(
            context
                .store()
                .type_node_links(comparison)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        let source_file = context.source_file(file).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source_file)
                .is_some_and(|links| links.type_checked)
        );
    }
}
