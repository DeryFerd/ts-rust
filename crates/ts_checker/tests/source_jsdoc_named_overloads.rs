use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
    jsdoc::{JsDocTagKind, parse_jsdoc_comment_at, plan_javascript_source_jsdoc},
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_javascript_source_file};

const FILE: FileId = FileId::new(8_222);

const ONE_COMMENT: &str = concat!(
    "/**\n",
    " * @param {string | number} value\n",
    " * @returns {string | number}\n",
    " * @overload\n",
    " * @param {string} value\n",
    " * @returns {string}\n",
    " * @overload\n",
    " * @param {'tag'} value\n",
    " * @returns {'tag'}\n",
    " * @overload\n",
    " * @param {number} value\n",
    " * @param {number} count\n",
    " * @returns {number}\n",
    " */\n",
);

const ADJACENT_COMMENTS: &str = concat!(
    "/** @overload @param {string} value @returns {string} */\n",
    "/** @overload @param {'tag'} value @returns {'tag'} */\n",
    "/** @overload @param {number} value @param {number} count @returns {number} */\n",
    "/** @param {string | number} value @returns {string | number} */\n",
);

struct ParameterNodes {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct FunctionNodes {
    declaration: NodeRef,
    name: NodeRef,
    parameters: Vec<ParameterNodes>,
    returned: NodeRef,
    body: Option<NodeRef>,
}

#[derive(Debug, Eq, PartialEq)]
struct GroupSnapshot {
    owner: SemanticSymbolId,
    callable: TypeId,
    signatures: Vec<SignatureId>,
    parameters: Vec<Vec<SemanticSymbolId>>,
    parameter_types: Vec<Vec<TypeId>>,
    return_types: Vec<TypeId>,
    query_types: Vec<(NodeRef, TypeId)>,
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
                EscapedName::source("\"/project/named-overloads.js\""),
                CanonicalSourceLanguage::JavaScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_javascript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn range(start: usize, end: usize) -> TextRange {
    TextRange::new(
        TextPos::new(start.try_into().unwrap()),
        TextPos::new(end.try_into().unwrap()),
    )
}

fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), FILE, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn functions(parsed: &ParseResult) -> Vec<FunctionNodes> {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected a JavaScript source file")
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    source
        .statements
        .nodes
        .iter()
        .filter_map(|&node| {
            let NodeData::FunctionDeclaration(function) = &parsed.arena.get(node).unwrap().data
            else {
                return None;
            };
            assert!(function.type_parameters.is_none());
            Some(FunctionNodes {
                declaration: node_ref(node),
                name: node_ref(function.name.unwrap()),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .map(|&node| {
                        let NodeData::ParameterDeclaration(parameter) =
                            &parsed.arena.get(node).unwrap().data
                        else {
                            panic!("expected an identifier parameter")
                        };
                        ParameterNodes {
                            declaration: node_ref(node),
                            name: node_ref(parameter.name),
                            annotation: node_ref(parameter.type_.unwrap()),
                        }
                    })
                    .collect(),
                returned: node_ref(function.type_.unwrap()),
                body: function.body.map(node_ref),
            })
        })
        .collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the source node must retain its signature")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().mapper_len(),
    )
}

#[allow(clippy::too_many_lines)] // Keep the source clones, their annotations, and tree ownership together.
fn assert_source_clones(parsed: &ParseResult, functions: &[FunctionNodes]) {
    let source = parsed.arena.source_text().unwrap();
    let comments = source
        .match_indices("/**")
        .map(|(start, _)| {
            let end = start + source[start..].find("*/").unwrap() + 2;
            parse_jsdoc_comment_at(source, range(start, end)).unwrap()
        })
        .collect::<Vec<_>>();
    assert!(
        comments
            .iter()
            .all(|comment| comment.diagnostics().is_empty())
    );
    let tags = comments
        .iter()
        .flat_map(ts_checker::semantic::jsdoc::ParsedJsDocComment::tags)
        .filter(|tag| tag.kind() == JsDocTagKind::Overload)
        .collect::<Vec<_>>();
    let (implementation, overloads) = functions.split_last().unwrap();
    assert_eq!(tags.len(), overloads.len());
    assert!(implementation.body.is_some());
    let implementation_name = parsed.arena.get(implementation.name.node).unwrap();
    let mut names = HashSet::from([implementation.name]);
    let mut parameters = HashSet::new();
    for (overload, tag) in overloads.iter().zip(tags) {
        let record = parsed.arena.get(overload.declaration.node).unwrap();
        assert_eq!(record.flags, NodeFlags::REPARSED);
        assert_eq!(record.parent, Some(parsed.source_file));
        let start = tag.range().start.get() as usize + 1;
        assert_eq!(record.range, range(start, start + "overload".len()));
        assert_eq!(node_text(parsed, overload.declaration), "overload");
        assert!(overload.body.is_none());
        let name = parsed.arena.get(overload.name.node).unwrap();
        assert!(names.insert(overload.name));
        assert_eq!(name.flags, NodeFlags::REPARSED);
        assert_eq!(name.parent, Some(overload.declaration.node));
        assert_eq!(name.range, implementation_name.range);
        assert_eq!(
            node_text(parsed, overload.name),
            node_text(parsed, implementation.name)
        );
        let documented_parameters = tag
            .overload_tags()
            .iter()
            .filter(|tag| tag.kind() == JsDocTagKind::Parameter)
            .collect::<Vec<_>>();
        assert_eq!(overload.parameters.len(), documented_parameters.len());
        for (parameter, documented) in overload.parameters.iter().zip(documented_parameters) {
            assert!(parameters.insert(parameter.declaration));
            let record = parsed.arena.get(parameter.declaration.node).unwrap();
            assert_eq!(record.flags, NodeFlags::REPARSED);
            assert_eq!(record.parent, Some(overload.declaration.node));
            assert_eq!(record.range, documented.range());
            let name = parsed.arena.get(parameter.name.node).unwrap();
            assert_eq!(name.flags, NodeFlags::REPARSED);
            assert_eq!(name.parent, Some(parameter.declaration.node));
            assert_eq!(name.range, documented.name().unwrap().range());
            let annotation = parsed.arena.get(parameter.annotation.node).unwrap();
            assert_eq!(annotation.flags, NodeFlags::REPARSED);
            assert_eq!(annotation.parent, Some(parameter.declaration.node));
            assert_eq!(
                annotation.range,
                documented.type_expression().unwrap().range()
            );
        }
        let documented_return = tag
            .overload_tags()
            .iter()
            .find(|tag| tag.kind() == JsDocTagKind::Return)
            .unwrap();
        let NodeData::FunctionDeclaration(function) = &record.data else {
            unreachable!()
        };
        let first_parameter = tag
            .overload_tags()
            .iter()
            .find(|tag| tag.kind() == JsDocTagKind::Parameter)
            .unwrap();
        assert_eq!(
            function.parameters.range,
            TextRange::new(
                first_parameter.range().start,
                documented_return.range().start
            )
        );
        let returned = parsed.arena.get(overload.returned.node).unwrap();
        assert_eq!(returned.flags, NodeFlags::REPARSED);
        assert_eq!(returned.parent, Some(overload.declaration.node));
        assert_eq!(
            returned.range,
            documented_return.type_expression().unwrap().range()
        );
    }
    assert!(
        implementation
            .parameters
            .iter()
            .all(|parameter| { parameters.insert(parameter.declaration) })
    );
    let mut pending = vec![parsed.source_file];
    let mut reached = HashSet::new();
    while let Some(node) = pending.pop() {
        assert!(reached.insert(node), "the source must remain a tree");
        parsed.arena.get(node).unwrap().for_each_child(|child| {
            assert_eq!(parsed.arena.get(child).unwrap().parent, Some(node));
            pending.push(child);
        });
    }
    assert_eq!(
        reached.len(),
        parsed.arena.len(),
        "no clone may be detached"
    );
}

#[allow(clippy::too_many_lines)] // Check one overload group's complete source and query identities.
fn snapshot(
    context: &mut CanonicalCheckerContext<'_>,
    functions: &[FunctionNodes],
) -> GroupSnapshot {
    let (implementation, overloads) = functions.split_last().unwrap();
    let owner = symbol(context, overloads[0].declaration);
    let declarations = functions
        .iter()
        .map(|function| function.declaration)
        .collect::<Vec<_>>();
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        declarations
    );
    let owner_record = context.store().symbol(owner).unwrap();
    assert_eq!(owner_record.declarations(), Some(declarations.as_slice()));
    assert_eq!(
        owner_record.value_declaration(),
        Some(overloads[0].declaration)
    );
    let callable = context.get_type_at_location(implementation.name).unwrap();
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let mut signatures = Vec::new();
    let mut parameters = Vec::new();
    let mut parameter_types = Vec::new();
    let mut return_types = Vec::new();
    let mut query_types = Vec::new();
    let mut distinct_parameters = HashSet::new();
    for function in functions {
        assert_eq!(symbol(context, function.declaration), owner);
        assert_eq!(
            context.get_symbol_at_location(function.name).unwrap(),
            Some(owner)
        );
        for node in [function.declaration, function.name] {
            assert_eq!(context.get_type_at_location(node).unwrap(), callable);
            query_types.push((node, callable));
        }
        let signature = signature(context, function.declaration);
        let mut symbols = Vec::new();
        let mut types = Vec::new();
        for parameter in &function.parameters {
            let symbol = symbol(context, parameter.declaration);
            assert!(distinct_parameters.insert(symbol));
            assert_eq!(
                context.get_symbol_at_location(parameter.name).unwrap(),
                Some(symbol)
            );
            assert_eq!(
                context.get_symbol_declarations(symbol).unwrap(),
                [parameter.declaration]
            );
            let resolved = context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(resolved)
            );
            for node in [parameter.name, parameter.annotation] {
                assert_eq!(context.get_type_at_location(node).unwrap(), resolved);
                query_types.push((node, resolved));
            }
            symbols.push(symbol);
            types.push(resolved);
        }
        let returned = context.get_return_type_of_signature(signature).unwrap();
        assert_eq!(
            context.get_type_from_type_node(function.returned).unwrap(),
            returned
        );
        assert_eq!(
            context.get_type_at_location(function.returned).unwrap(),
            returned
        );
        query_types.push((function.returned, returned));
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(function.declaration));
        assert_eq!(record.parameters(), symbols);
        assert!(record.type_parameters().is_empty());
        assert_eq!(
            record.min_argument_count(),
            i32::try_from(symbols.len()).unwrap()
        );
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        signatures.push(signature);
        parameters.push(symbols);
        parameter_types.push(types);
        return_types.push(returned);
    }
    assert_eq!(
        signatures.iter().copied().collect::<HashSet<_>>().len(),
        functions.len()
    );
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected the overload owner's callable object")
    };
    assert_eq!(object.structured.call_signature_count, overloads.len());
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&signatures[..overloads.len()])
    );
    GroupSnapshot {
        owner,
        callable,
        signatures,
        parameters,
        parameter_types,
        return_types,
        query_types,
    }
}

fn assert_group_replay(
    context: &mut CanonicalCheckerContext<'_>,
    functions: &[FunctionNodes],
    state: &GroupSnapshot,
    calls: &[NodeRef],
) {
    let display = context.type_to_string(state.callable).unwrap();
    let call_results = calls
        .iter()
        .map(|&call| {
            let type_ = context.get_type_at_location(call).unwrap();
            (call, type_, signature(context, call))
        })
        .collect::<Vec<_>>();
    let diagnostics = context.diagnostics().clone();
    let before = counts(context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(context, functions), *state);
        assert_eq!(context.type_to_string(state.callable).unwrap(), display);
        for &(node, expected) in &state.query_types {
            assert_eq!(context.get_type_at_location(node).unwrap(), expected);
        }
        for &(call, type_, selected) in &call_results {
            assert_eq!(context.get_type_at_location(call).unwrap(), type_);
            assert_eq!(signature(context, call), selected);
        }
        assert_eq!(counts(context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn named_jsdoc_overloads_clone_source_owners_and_select_literals_in_both_comment_forms() {
    for comments in [ONE_COMMENT, ADJACENT_COMMENTS] {
        let source = format!(
            "{comments}function choose(value) {{ return value; }}\nchoose('tag');\nchoose('other');\nchoose(1, 2);\n",
        );
        let parsed = parse_javascript_source_file(&source);
        let functions = functions(&parsed);
        assert_eq!(functions.len(), 4);
        assert_source_clones(&parsed, &functions);
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 3);
        let returned = nodes(&parsed, SyntaxKind::ReturnStatement);
        let [returned] = returned.as_slice() else {
            panic!("only the implementation may have a body")
        };
        let NodeData::ReturnStatement(returned) = &parsed.arena.get(returned.node).unwrap().data
        else {
            unreachable!()
        };
        let body_value = NodeRef::new(parsed.arena.id(), FILE, returned.expression.unwrap());
        for query_first in [false, true] {
            let mut context = context(&parsed);
            let early = query_first.then(|| {
                context
                    .get_type_from_type_node(functions[0].parameters[0].annotation)
                    .unwrap()
            });
            context.check_source_file(FILE).unwrap();
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let state = snapshot(&mut context, &functions);
            assert_eq!(
                context.type_to_string(state.callable).unwrap(),
                concat!(
                    "{ (value: string): string; (value: \"tag\"): \"tag\"; ",
                    "(value: number, count: number): number; }",
                ),
            );
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(state.parameter_types[0], [string]);
            assert_eq!(
                context.type_to_string(state.parameter_types[1][0]).unwrap(),
                "\"tag\"",
            );
            assert_eq!(
                context.type_to_string(state.parameter_types[3][0]).unwrap(),
                "string | number",
            );
            assert_eq!(state.parameter_types[2], [number, number]);
            assert_eq!(
                state.return_types,
                [
                    string,
                    state.parameter_types[1][0],
                    number,
                    state.parameter_types[3][0]
                ],
            );
            if let Some(early) = early {
                assert_eq!(early, state.parameter_types[0][0]);
            }
            assert_eq!(
                context.get_symbol_at_location(body_value).unwrap(),
                Some(state.parameters[3][0])
            );
            assert_eq!(
                context.get_type_at_location(body_value).unwrap(),
                state.parameter_types[3][0]
            );
            for (&call, (index, display)) in
                calls
                    .iter()
                    .zip([(1, "\"tag\""), (0, "string"), (2, "number")])
            {
                let type_ = context.get_type_at_location(call).unwrap();
                assert_eq!(context.type_to_string(type_).unwrap(), display);
                assert_eq!(signature(&context, call), state.signatures[index]);
                assert_ne!(signature(&context, call), state.signatures[3]);
            }
            assert_group_replay(&mut context, &functions, &state, &calls);
        }
    }
}

#[test]
fn named_jsdoc_overload_calls_reject_the_wider_implementation_parameter() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @param {string | number} value @returns {string | number}\n",
        " * @overload @param {string} value @returns {string} */\n",
        "function choose(value) { return value; }\n",
        "choose(1);\n",
    ));
    let functions = functions(&parsed);
    assert_eq!(functions.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one rejected call")
    };
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected only TS2345, got {:?}", context.diagnostics())
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'."
    );
    assert_eq!(node_text(&parsed, diagnostic.node.unwrap()), "1");
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    let state = snapshot(&mut context, &functions);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        context.type_to_string(state.callable).unwrap(),
        "(value: string) => string"
    );
    assert_eq!(state.parameter_types[0], [string]);
    assert_eq!(
        context.type_to_string(state.parameter_types[1][0]).unwrap(),
        "string | number",
    );
    assert_eq!(state.return_types[1], state.parameter_types[1][0]);
    assert_eq!(signature(&context, *call), state.signatures[0]);
    assert_eq!(context.get_type_at_location(*call).unwrap(), string);
    assert_group_replay(&mut context, &functions, &state, &calls);
}

#[test]
fn named_jsdoc_overloads_check_the_implementation_body_and_keep_its_diagnostic() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @overload @param {string} value @returns {string} */\n",
        "/** @param {string} value @returns {string} */\n",
        "function wrong(value) { return 1; }\n",
        "wrong('text');\n",
    ));
    let functions = functions(&parsed);
    assert_eq!(functions.len(), 2);
    let returns = nodes(&parsed, SyntaxKind::ReturnStatement);
    let [returned] = returns.as_slice() else {
        panic!("expected one implementation return")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one call to the valid overload")
    };
    let mut context = context(&parsed);
    let early = context
        .get_type_from_type_node(functions[1].returned)
        .unwrap();
    assert!(context.diagnostics().is_empty());
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected only the body TS2322, got {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'."
    );
    assert_eq!(diagnostic.node, Some(*returned));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    let state = snapshot(&mut context, &functions);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(early, string);
    assert_eq!(state.parameter_types, [vec![string], vec![string]]);
    assert_eq!(state.return_types, [string, string]);
    assert_eq!(signature(&context, *call), state.signatures[0]);
    assert_eq!(context.get_type_at_location(*call).unwrap(), string);
    assert_group_replay(&mut context, &functions, &state, &calls);
}

#[test]
fn named_jsdoc_overloads_report_the_first_incompatible_signature_and_implementation_site() {
    for (overload_parameter, overload_return, implementation_parameter, implementation_return) in [
        ("string", "number", "number", "number"),
        ("number", "string", "number", "number"),
    ] {
        let source = format!(
            "/** @overload @param {{{overload_parameter}}} value @returns {{{overload_return}}} */\n\
             /** @overload @param {{{overload_parameter}}} value @returns {{{overload_return}}} */\n\
             /** @param {{{implementation_parameter}}} value @returns {{{implementation_return}}} */\n\
             function conflict(value) {{ return value; }}\n",
        );
        let parsed = parse_javascript_source_file(&source);
        let functions = functions(&parsed);
        assert_eq!(functions.len(), 3);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected only the first TS2394, got {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(diagnostic.diagnostic.code(), 2394);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This overload signature is not compatible with its implementation signature."
        );
        assert_eq!(diagnostic.node, Some(functions[0].declaration));
        assert_eq!(node_text(&parsed, functions[0].declaration), "overload");
        assert_eq!(diagnostic.range_override, None);
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("TS2394 must retain the implementation site")
        };
        assert_eq!(related.diagnostic.code(), 2750);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "The implementation signature is declared here."
        );
        assert_eq!(related.node, Some(functions[2].name));
        assert_eq!(node_text(&parsed, functions[2].name), "conflict");
        let state = snapshot(&mut context, &functions);
        assert_group_replay(&mut context, &functions, &state, &[]);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the unchanged generic input and its source/query identities together.
fn named_jsdoc_generic_overloads_keep_separate_templates_without_nongeneric_fallback() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @template T @param {T} value @returns {T}\n",
        " * @overload @param {T} value @returns {T} */\n",
        "function keep(value) { return value; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    let [overload, implementation] = declarations.as_slice() else {
        panic!("expected one real generic overload and its implementation")
    };
    let source = NodeRef::new(parsed.arena.id(), FILE, parsed.source_file);
    let planned = plan_javascript_source_jsdoc(&parsed.arena, source).unwrap();
    assert!(planned.diagnostics().is_empty());
    let template_range = planned
        .declaration(*implementation)
        .unwrap()
        .template_parameters()[0]
        .range();
    let source_text = parsed.arena.source_text().unwrap();
    let template_list_range = range(
        source_text.find("@template").unwrap(),
        source_text.find("@param").unwrap(),
    );
    let annotations = source_text
        .match_indices("{T}")
        .map(|(start, _)| range(start + 1, start + 2))
        .collect::<Vec<_>>();
    assert_eq!(annotations.len(), 4);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let owner = symbol(&context, *overload);
    assert_eq!(symbol(&context, *implementation), owner);
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        declarations
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().value_declaration(),
        Some(*overload)
    );
    let callable = context.get_type_at_location(*implementation).unwrap();
    let row_signatures = declarations
        .iter()
        .map(|&node| signature(&context, node))
        .collect::<Vec<_>>();
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected the source overload object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&row_signatures[..1])
    );
    assert_ne!(row_signatures[0], row_signatures[1]);
    let mut template_symbols = Vec::new();
    let mut template_types = Vec::new();
    let mut parameter_symbols = Vec::new();
    let mut queries = Vec::new();
    for (index, &declaration) in declarations.iter().enumerate() {
        let record = parsed.arena.get(declaration.node).unwrap();
        let NodeData::FunctionDeclaration(function) = &record.data else {
            unreachable!()
        };
        assert_eq!(function.body.is_some(), declaration == *implementation);
        if declaration == *overload {
            assert_eq!(record.flags, NodeFlags::REPARSED);
            assert_eq!(node_text(&parsed, declaration), "overload");
            let start = source_text.find("@overload").unwrap() + 1;
            assert_eq!(record.range, range(start, start + "overload".len()));
        }
        let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
        let templates = function.type_parameters.as_ref().unwrap();
        assert_eq!(templates.range, template_list_range);
        let [template] = templates.nodes.as_slice() else {
            panic!("the overload and host must each retain one template")
        };
        let template_record = parsed.arena.get(*template).unwrap();
        assert_eq!(template_record.flags, NodeFlags::REPARSED);
        assert_eq!(template_record.parent, Some(declaration.node));
        assert_eq!(template_record.range, template_range);
        let NodeData::TypeParameterDeclaration(template) = &template_record.data else {
            unreachable!()
        };
        assert_eq!(
            parsed.arena.get(template.name).unwrap().range,
            template_range
        );
        let template_symbol = symbol(&context, node_ref(templates.nodes[0]));
        let template_type = context
            .get_type_at_location(node_ref(template.name))
            .unwrap();
        let type_record = context.store().type_payload(template_type).unwrap();
        assert_eq!(type_record.symbol(), Some(template_symbol));
        assert!(matches!(type_record.data(), TypeData::TypeParameter(_)));
        assert_eq!(
            context.get_symbol_declarations(template_symbol).unwrap(),
            [node_ref(templates.nodes[0])]
        );
        let [parameter_node] = function.parameters.nodes.as_slice() else {
            panic!("the unchanged source has one value parameter")
        };
        let parameter_symbol = symbol(&context, node_ref(*parameter_node));
        let NodeData::ParameterDeclaration(parameter) =
            &parsed.arena.get(*parameter_node).unwrap().data
        else {
            unreachable!()
        };
        let parameter_annotation = parameter.type_.unwrap();
        let return_annotation = function.type_.unwrap();
        let annotation_index = if index == 0 { 2 } else { 0 };
        assert_eq!(
            parsed.arena.get(parameter_annotation).unwrap().range,
            annotations[annotation_index]
        );
        assert_eq!(
            parsed.arena.get(return_annotation).unwrap().range,
            annotations[annotation_index + 1]
        );
        for node in [
            template.name,
            parameter.name,
            parameter_annotation,
            return_annotation,
        ] {
            let node = node_ref(node);
            assert_eq!(context.get_type_at_location(node).unwrap(), template_type);
            queries.push((node, template_type));
        }
        let signature = context.store().signature(row_signatures[index]).unwrap();
        assert_eq!(signature.declaration(), Some(declaration));
        assert_eq!(signature.type_parameters(), [template_type]);
        assert_eq!(signature.parameters(), [parameter_symbol]);
        assert_eq!(signature.target(), None);
        assert_eq!(signature.mapper(), None);
        assert_eq!(
            context
                .get_return_type_of_signature(row_signatures[index])
                .unwrap(),
            template_type
        );
        template_symbols.push(template_symbol);
        template_types.push(template_type);
        parameter_symbols.push(parameter_symbol);
    }
    assert_ne!(template_symbols[0], template_symbols[1]);
    assert_ne!(template_types[0], template_types[1]);
    assert_ne!(parameter_symbols[0], parameter_symbols[1]);
    assert_eq!(
        context.type_to_string(callable).unwrap(),
        "<T>(value: T) => T"
    );
    let before = counts(&context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            context.get_type_at_location(*implementation).unwrap(),
            callable
        );
        assert_eq!(
            context.type_to_string(callable).unwrap(),
            "<T>(value: T) => T"
        );
        for (index, &declaration) in declarations.iter().enumerate() {
            assert_eq!(signature(&context, declaration), row_signatures[index]);
            assert_eq!(
                context
                    .get_return_type_of_signature(row_signatures[index])
                    .unwrap(),
                template_types[index]
            );
        }
        for &(node, type_) in &queries {
            assert_eq!(context.get_type_at_location(node).unwrap(), type_);
        }
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn jsdoc_arrow_overload_tags_still_leave_only_the_host_signature() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @param {string} value @returns {string}\n",
        " * @overload @param {number} value @returns {number} */\n",
        "const echo = value => value;\n",
        "echo('text');\n",
    ));
    assert!(nodes(&parsed, SyntaxKind::FunctionDeclaration).is_empty());
    let arrows = nodes(&parsed, SyntaxKind::ArrowFunction);
    let [arrow] = arrows.as_slice() else {
        panic!("expected one actual arrow")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one arrow call")
    };
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let callable = context.get_type_at_location(*arrow).unwrap();
    let host_signature = signature(&context, *arrow);
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected the arrow's callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[host_signature][..])
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        context
            .get_return_type_of_signature(host_signature)
            .unwrap(),
        string
    );
    assert_eq!(signature(&context, *call), host_signature);
    assert_eq!(context.get_type_at_location(*call).unwrap(), string);
    let before = counts(&context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.get_type_at_location(*arrow).unwrap(), callable);
        assert_eq!(signature(&context, *arrow), host_signature);
        assert_eq!(signature(&context, *call), host_signature);
        assert_eq!(context.get_type_at_location(*call).unwrap(), string);
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}
