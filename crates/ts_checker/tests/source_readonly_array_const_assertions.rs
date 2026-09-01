use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    ArrayLiteralLinks, AssertionLinks, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError, SourceFileLinks,
    SourceSyntaxRole, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::ElementFlags, type_records::LiteralValue, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(0);
const LIBRARY_FILE: FileId = FileId::new(1);
const LIBRARY: &str = concat!(
    "interface Array<T> { length: number; [index: number]: T; }\n",
    "interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; }\n",
);

fn context<'arena>(
    parsed: &'arena ParseResult,
    library: &'arena ParseResult,
    module: CanonicalModuleState,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, declaration, module) in [
        (
            LIBRARY_FILE,
            library,
            "\"/project/arrays.d.ts\"",
            true,
            CanonicalModuleState::Script,
        ),
        (FILE, parsed, "\"/project/const-arrays.ts\"", false, module),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    module,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (FILE, &parsed.arena)],
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

#[derive(Clone, Copy)]
struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(declaration) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| Variable {
                declaration: NodeRef::new(parsed.arena.id(), FILE, node),
                name: NodeRef::new(parsed.arena.id(), FILE, declaration.name),
                initializer: NodeRef::new(
                    parsed.arena.id(),
                    FILE,
                    declaration
                        .initializer
                        .expect("the variable has an initializer"),
                ),
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn variable_symbol(context: &CanonicalCheckerContext<'_>, variable: Variable) -> SemanticSymbolId {
    let symbol = context
        .file(FILE)
        .unwrap()
        .1
        .symbol(variable.declaration)
        .unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn unparenthesized(parsed: &ParseResult, mut node: NodeRef) -> NodeRef {
    while let NodeData::ParenthesizedExpression(data) = &parsed.arena.get(node.node).unwrap().data {
        node = NodeRef::new(parsed.arena.id(), FILE, data.expression);
    }
    node
}

#[derive(Clone, Copy)]
struct Assertion {
    expression: NodeRef,
    operand: NodeRef,
    target: NodeRef,
}

fn assertion(parsed: &ParseResult, initializer: NodeRef) -> Assertion {
    let expression = unparenthesized(parsed, initializer);
    let (operand, target) = match &parsed.arena.get(expression.node).unwrap().data {
        NodeData::AsExpression(data) => (data.expression, data.type_),
        NodeData::TypeAssertion(data) => (data.expression, data.type_),
        _ => panic!("the initializer has an assertion"),
    };
    assert_eq!(
        parsed.arena.get(operand).unwrap().parent,
        Some(expression.node)
    );
    assert_eq!(
        parsed.arena.get(target).unwrap().parent,
        Some(expression.node)
    );
    Assertion {
        expression,
        operand: NodeRef::new(parsed.arena.id(), FILE, operand),
        target: NodeRef::new(parsed.arena.id(), FILE, target),
    }
}

fn array_elements(parsed: &ParseResult, node: NodeRef) -> Vec<NodeRef> {
    let node = unparenthesized(parsed, node);
    let NodeData::ArrayLiteralExpression(array) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("the operand is the original array literal");
    };
    array
        .elements
        .nodes
        .iter()
        .map(|&element| {
            assert_eq!(parsed.arena.get(element).unwrap().parent, Some(node.node));
            NodeRef::new(parsed.arena.id(), FILE, element)
        })
        .collect()
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .expect("source checking publishes the actual node type")
}

fn tuple_elements(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    readonly: bool,
    count: usize,
) -> Vec<TypeId> {
    let record = context.store().type_payload(type_).unwrap();
    assert!(record.object_flags().contains(ObjectFlags::ARRAY_LITERAL));
    let TypeData::TypeReference(reference) = record.data() else {
        panic!("the array literal has a canonical tuple reference");
    };
    let target = reference.object.target.unwrap();
    let TypeData::Tuple(tuple) = context.store().type_payload(target).unwrap().data() else {
        panic!("the reference points to a real tuple target");
    };
    assert_eq!(tuple.metadata.is_readonly(), readonly);
    assert_eq!(tuple.metadata.min_length(), count);
    assert_eq!(tuple.metadata.fixed_length(), count);
    assert_eq!(
        tuple.metadata.element_flags(),
        vec![ElementFlags::REQUIRED; count]
    );
    let elements = reference.resolved_type_arguments.as_ref().unwrap();
    assert_eq!(elements.len(), count);
    elements.clone()
}

fn const_array_type(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    variable: Variable,
) -> TypeId {
    let assertion = assertion(parsed, variable.initializer);
    let type_ = context.get_type_at_location(assertion.expression).unwrap();
    assert_eq!(resolved_type(context, assertion.operand), type_);
    assert_eq!(
        resolved_type(context, unparenthesized(parsed, assertion.operand)),
        type_,
    );
    assert_eq!(
        context.store().assertion_links(assertion.expression),
        Some(&AssertionLinks {
            expr_type: Some(type_)
        }),
    );
    assert!(
        context
            .store()
            .type_node_links(assertion.target)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    type_
}

fn assert_regular_literal(context: &CanonicalCheckerContext<'_>, type_: TypeId, display: &str) {
    let TypeData::Literal(literal) = context.store().type_payload(type_).unwrap().data() else {
        panic!("{display} retains its literal record");
    };
    assert_eq!(literal.regular_type, type_);
    assert_eq!(context.type_to_string(type_).unwrap(), display);
}

fn object_property(
    context: &CanonicalCheckerContext<'_>,
    object: TypeId,
    name: &str,
    readonly: bool,
) -> TypeId {
    let TypeData::Object(data) = context.store().type_payload(object).unwrap().data() else {
        panic!("the element is the source object literal");
    };
    let symbol = data
        .structured
        .properties
        .as_ref()
        .unwrap()
        .iter()
        .copied()
        .find(|&symbol| context.store().symbol(symbol).unwrap().name().as_utf8() == Some(name))
        .unwrap_or_else(|| panic!("missing property {name}"));
    assert_eq!(
        context
            .store()
            .symbol(symbol)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY),
        readonly,
    );
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    source: Option<SourceFileLinks>,
    types: Vec<Option<TypeNodeLinks>>,
    arrays: Vec<Option<ArrayLiteralLinks>>,
    assertions: Vec<Option<AssertionLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Snapshot {
    let store = context.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        types: nodes
            .iter()
            .map(|&node| store.type_node_links(node).cloned())
            .collect(),
        arrays: nodes
            .iter()
            .map(|&node| store.array_literal_links(node).cloned())
            .collect(),
        assertions: nodes
            .iter()
            .map(|&node| store.assertion_links(node).cloned())
            .collect(),
        values: nodes
            .iter()
            .filter_map(|&node| context.file(FILE).unwrap().1.symbol(node))
            .map(|symbol| {
                store
                    .value_symbol_links(store.get_merged_symbol(symbol).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let before = snapshot(context, parsed);
    context.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(context, parsed), before);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(context, parsed), before);
    }
}

fn assert_template_array(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> TypeId {
    let type_ = const_array_type(context, parsed, variable(parsed, "patterns"));
    let elements = tuple_elements(context, type_, true, 1);
    let TypeData::TemplateLiteral(template) =
        context.store().type_payload(elements[0]).unwrap().data()
    else {
        panic!("the const array retains the actual template pattern");
    };
    assert_eq!(template.texts, ["item-", ""]);
    assert_eq!(
        template.types,
        [context.store().intrinsic_bootstrap().unwrap().string_type]
    );
    type_
}

#[test]
fn readonly_array_const_assertions_preserve_original_hono_elements_in_both_query_orders() {
    let library = parse_source_file(LIBRARY);
    let cases: &[(&str, &str, &[&str], CanonicalModuleState)] = &[
        (
            "export const METHODS = ['get', 'post', 'put', 'delete', 'options', 'patch', 'query'] as const\n",
            "METHODS",
            &["get", "post", "put", "delete", "options", "patch", "query"],
            CanonicalModuleState::External,
        ),
        (
            concat!(
                "const queryRepresentationMetadataHeaders = [\n",
                "  'content-type',\n  'content-encoding',\n  'content-language',\n  'content-location',\n",
                "] as const\n",
            ),
            "queryRepresentationMetadataHeaders",
            &[
                "content-type",
                "content-encoding",
                "content-language",
                "content-location",
            ],
            CanonicalModuleState::Script,
        ),
        (
            "const ENCODING_TYPES = ['gzip', 'deflate'] as const\n",
            "ENCODING_TYPES",
            &["gzip", "deflate"],
            CanonicalModuleState::Script,
        ),
        (
            "const secFetchSiteValues = ['same-origin', 'same-site', 'none', 'cross-site'] as const\n",
            "secFetchSiteValues",
            &["same-origin", "same-site", "none", "cross-site"],
            CanonicalModuleState::Script,
        ),
    ];
    for &(text, name, expected, module) in cases {
        let parsed = parse_source_file(text);
        let variable = variable(&parsed, name);
        let assertion = assertion(&parsed, variable.initializer);
        let nodes = array_elements(&parsed, assertion.operand);
        for query_first in [false, true] {
            let mut context = context(&parsed, &library, module);
            if query_first {
                context.get_type_at_location(assertion.expression).unwrap();
            } else {
                context.check_source_file(FILE).unwrap();
            }
            let type_ = const_array_type(&mut context, &parsed, variable);
            assert_eq!(context.get_type_at_location(variable.name).unwrap(), type_);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(variable_symbol(&context, variable))
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            let elements = tuple_elements(&context, type_, true, expected.len());
            assert_eq!(nodes.len(), elements.len());
            for ((&element, &node), &expected) in elements.iter().zip(&nodes).zip(expected) {
                assert_regular_literal(&context, element, &format!("{expected:?}"));
                let TypeData::Literal(literal) =
                    context.store().type_payload(element).unwrap().data()
                else {
                    unreachable!("the regular literal was checked");
                };
                assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
                let raw = context.get_type_at_location(node).unwrap();
                assert_eq!(resolved_type(&context, node), raw);
                let TypeData::Literal(raw_literal) =
                    context.store().type_payload(raw).unwrap().data()
                else {
                    panic!("the element query retains its raw literal");
                };
                assert_eq!(raw_literal.regular_type, element);
                assert_ne!(raw, element);
            }
            assert!(context.diagnostics().is_empty());
            assert_replay(&mut context, &parsed);
            assert_eq!(const_array_type(&mut context, &parsed, variable), type_);
        }
    }
}

#[test]
fn readonly_array_const_assertions_keep_existing_element_and_nested_object_identities() {
    let parsed = parse_source_file(concat!(
        "declare const dynamic: string;\n",
        "const scalar = 'kept';\n",
        "const saved = { value: 4 };\n",
        "const mixed = ['text', (2), -3, 4n, -5n, true, false, null, undefined, `plain`, ",
        "scalar, saved, [6, { value: 7 }], { value: 8 }, saved.value] as const;\n",
        "const empty = [] as const;\n",
        "const wrapped = <const>(['wrapped']);\n",
        "const patterns = [`item-${dynamic}`] as const;\n",
        "const object = { values: [9, { value: 10 }] } as const;\n",
    ));
    let library = parse_source_file(LIBRARY);
    let mixed = variable(&parsed, "mixed");
    let empty = variable(&parsed, "empty");
    let wrapped = variable(&parsed, "wrapped");
    for query_first in [false, true] {
        let mut context = context(&parsed, &library, CanonicalModuleState::Script);
        if query_first {
            context.get_type_at_location(mixed.initializer).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let type_ = const_array_type(&mut context, &parsed, mixed);
        let elements = tuple_elements(&context, type_, true, 15);
        for (&element, display) in elements.iter().zip([
            "\"text\"",
            "2",
            "-3",
            "4n",
            "-5n",
            "true",
            "false",
            "null",
            "undefined",
            "\"plain\"",
            "\"kept\"",
            "{ value: number; }",
            "readonly [6, { readonly value: 7; }]",
            "{ readonly value: 8; }",
            "number",
        ]) {
            assert_eq!(context.type_to_string(element).unwrap(), display);
            if matches!(
                context.store().type_payload(element).unwrap().data(),
                TypeData::Literal(_)
            ) {
                assert_regular_literal(&context, element, display);
            }
        }
        let saved = context
            .get_type_at_location(variable(&parsed, "saved").name)
            .unwrap();
        assert_eq!(elements[11], saved);
        assert_eq!(
            object_property(&context, saved, "value", false),
            elements[14]
        );
        let nested = tuple_elements(&context, elements[12], true, 2);
        assert_regular_literal(&context, nested[0], "6");
        assert_regular_literal(
            &context,
            object_property(&context, nested[1], "value", true),
            "7",
        );
        assert_regular_literal(
            &context,
            object_property(&context, elements[13], "value", true),
            "8",
        );
        let empty_type = const_array_type(&mut context, &parsed, empty);
        assert!(tuple_elements(&context, empty_type, true, 0).is_empty());
        let wrapped_type = const_array_type(&mut context, &parsed, wrapped);
        let wrapped_elements = tuple_elements(&context, wrapped_type, true, 1);
        assert_regular_literal(&context, wrapped_elements[0], "\"wrapped\"");
        let object = context
            .get_type_at_location(variable(&parsed, "object").name)
            .unwrap();
        let object_elements = tuple_elements(
            &context,
            object_property(&context, object, "values", true),
            true,
            2,
        );
        assert_regular_literal(&context, object_elements[0], "9");
        assert_regular_literal(
            &context,
            object_property(&context, object_elements[1], "value", true),
            "10",
        );
        let patterns = assert_template_array(&mut context, &parsed);
        assert!(context.diagnostics().is_empty());
        assert_replay(&mut context, &parsed);
        assert_eq!(const_array_type(&mut context, &parsed, mixed), type_);
        assert_eq!(assert_template_array(&mut context, &parsed), patterns);
    }
}

#[test]
fn readonly_array_const_identifier_spreads_keep_tuple_and_array_element_identities() {
    let parsed = parse_source_file(concat!(
        "const fixed: [1, 'a'] = [1, 'a'];\n",
        "const copied = [...fixed, true] as const;\n",
        "const numbers: number[] = [1, 2];\n",
        "const rest = ['head', ...numbers] as const;\n",
        "const ordinary = ['text', 'other'];\n",
    ));
    let library = parse_source_file(LIBRARY);
    let copied = variable(&parsed, "copied");
    let rest = variable(&parsed, "rest");
    for query_first in [false, true] {
        let mut context = context(&parsed, &library, CanonicalModuleState::Script);
        if query_first {
            context.get_type_at_location(rest.initializer).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let copied_type = const_array_type(&mut context, &parsed, copied);
        let copied_elements = tuple_elements(&context, copied_type, true, 3);
        for (&element, display) in copied_elements.iter().zip(["1", "\"a\"", "true"]) {
            assert_regular_literal(&context, element, display);
        }
        let fixed_type = context
            .get_type_at_location(variable(&parsed, "fixed").name)
            .unwrap();
        let TypeData::TypeReference(fixed) =
            context.store().type_payload(fixed_type).unwrap().data()
        else {
            panic!("the spread retains its annotated tuple");
        };
        assert_eq!(
            fixed.resolved_type_arguments.as_deref(),
            Some(&copied_elements[..2])
        );
        let rest_type = const_array_type(&mut context, &parsed, rest);
        let rest_record = context.store().type_payload(rest_type).unwrap();
        assert!(
            rest_record
                .object_flags()
                .contains(ObjectFlags::ARRAY_LITERAL)
        );
        let TypeData::TypeReference(rest_reference) = rest_record.data() else {
            panic!("the array spread retains a readonly rest tuple");
        };
        let target = rest_reference.object.target.unwrap();
        let TypeData::Tuple(tuple) = context.store().type_payload(target).unwrap().data() else {
            panic!("the rest reference has a tuple target");
        };
        assert!(tuple.metadata.is_readonly());
        assert_eq!(tuple.metadata.min_length(), 1);
        assert_eq!(tuple.metadata.fixed_length(), 1);
        assert_eq!(
            tuple.metadata.element_flags(),
            [ElementFlags::REQUIRED, ElementFlags::REST]
        );
        let rest_elements = rest_reference.resolved_type_arguments.as_ref().unwrap();
        assert_eq!(rest_elements.len(), 2);
        assert_regular_literal(&context, rest_elements[0], "\"head\"");
        assert_eq!(
            rest_elements[1],
            context.store().intrinsic_bootstrap().unwrap().number_type
        );
        assert_eq!(
            context.type_to_string(rest_type).unwrap(),
            "readonly [\"head\", ...number[]]"
        );
        let ordinary = context
            .get_type_at_location(variable(&parsed, "ordinary").name)
            .unwrap();
        let TypeData::TypeReference(ordinary) =
            context.store().type_payload(ordinary).unwrap().data()
        else {
            panic!("an ordinary array keeps its widened mutable reference");
        };
        assert_eq!(
            ordinary.object.target,
            Some(context.global_types().array_type)
        );
        assert_eq!(
            ordinary.resolved_type_arguments.as_deref(),
            Some(&[context.store().intrinsic_bootstrap().unwrap().string_type][..]),
        );
        assert!(context.diagnostics().is_empty());
        assert_replay(&mut context, &parsed);
        assert_eq!(const_array_type(&mut context, &parsed, copied), copied_type);
        assert_eq!(const_array_type(&mut context, &parsed, rest), rest_type);
    }
}

#[test]
fn readonly_array_const_assertions_respect_mutable_contexts_and_reject_readonly_assignment() {
    let parsed = parse_source_file(concat!(
        "var tupleContext: [number, number] = [1, 2] as const;\n",
        "var arrayContext: number[] = [1, 2] as const;\n",
        "var unionContext: number[] | null = [1, 2] as const;\n",
        "const frozen = [1, 2] as const;\n",
        "var readonlyContext: readonly [number, number] = [1, 2] as const;\n",
        "tupleContext = frozen;\n",
        "arrayContext = frozen;\n",
        "readonlyContext = tupleContext;\n",
    ));
    let library = parse_source_file(LIBRARY);
    let frozen = variable(&parsed, "frozen");
    for query_first in [false, true] {
        let mut context = context(&parsed, &library, CanonicalModuleState::Script);
        if query_first {
            context.get_type_at_location(frozen.initializer).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let frozen_type = const_array_type(&mut context, &parsed, frozen);
        let frozen_elements = tuple_elements(&context, frozen_type, true, 2);
        for name in [
            "tupleContext",
            "arrayContext",
            "unionContext",
            "readonlyContext",
        ] {
            let variable = variable(&parsed, name);
            let actual = const_array_type(&mut context, &parsed, variable);
            assert_eq!(
                tuple_elements(&context, actual, name == "readonlyContext", 2),
                frozen_elements
            );
            let target = context.get_type_at_location(variable.name).unwrap();
            assert_eq!(context.is_type_assignable_to(actual, target), Ok(true));
            assert_eq!(
                context.is_type_assignable_to(frozen_type, target),
                Ok(name == "readonlyContext")
            );
        }
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for (diagnostic, (left, target)) in diagnostics.iter().zip([
            ("tupleContext", "[number, number]"),
            ("arrayContext", "number[]"),
        ]) {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, ["readonly [1, 2]", target]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!("Type 'readonly [1, 2]' is not assignable to type '{target}'."),
            );
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            let node = diagnostic.node.unwrap();
            let range = parsed.arena.get(node.node).unwrap().range;
            let text = parsed.arena.source_text().unwrap();
            assert_eq!(
                &text[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                left
            );
        }
        assert_replay(&mut context, &parsed);
    }
}

#[test]
fn array_const_assertions_keep_invalid_const_spread_and_conversion_errors() {
    let library = parse_source_file(LIBRARY);
    for (text, const_refusal) in [
        ("const stored = [1]; const invalid = stored as const;", true),
        ("const invalid = [...[1]] as const;", false),
        ("const invalid = [, 1] as const;", false),
    ] {
        let parsed = parse_source_file(text);
        let invalid = assertion(&parsed, variable(&parsed, "invalid").initializer);
        let mut context = context(&parsed, &library, CanonicalModuleState::Script);
        let before = snapshot(&context, &parsed);
        for _ in 0..2 {
            match context.check_source_file(FILE) {
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::ConstAssertion(
                    node,
                ))) if const_refusal => {
                    assert_eq!(node, invalid.expression);
                }
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                    role: SourceSyntaxRole::ArrayElement,
                    ..
                })) if !const_refusal => {}
                result => panic!("unexpected boundary for {text}: {result:?}"),
            }
            assert_eq!(snapshot(&context, &parsed), before);
            assert!(context.diagnostics().is_empty());
        }
    }
    let parsed = parse_source_file("var value: string[] = ([1] as string[]);");
    let assertion = assertion(&parsed, variable(&parsed, "value").initializer);
    for query_first in [false, true] {
        let mut context = context(&parsed, &library, CanonicalModuleState::Script);
        if query_first {
            context.get_type_at_location(assertion.expression).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the original nonoverlapping conversion keeps one diagnostic");
        };
        assert_eq!(diagnostic.node, Some(assertion.expression));
        assert_eq!(diagnostic.diagnostic.code(), 2352);
        assert_eq!(diagnostic.diagnostic.arguments, ["number[]", "string[]"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Conversion of type 'number[]' to type 'string[]' may be a mistake because neither type sufficiently overlaps with the other. If this was intentional, convert the expression to 'unknown' first.",
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_replay(&mut context, &parsed);
    }
}
