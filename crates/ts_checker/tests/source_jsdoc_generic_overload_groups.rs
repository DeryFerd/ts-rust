use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
    jsdoc::{
        JsDocCommentError, JsDocTagKind, parse_jsdoc_comment_at, plan_javascript_source_jsdoc,
    },
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_javascript_source_file};

const FILE: FileId = FileId::new(8_224);

const SHARED_TEMPLATE: &str = concat!(
    "/**\n",
    " * @template T\n",
    " * @param {T} value\n",
    " * @returns {T}\n",
    " * @overload\n",
    " * @param {T} value\n",
    " * @returns {T}\n",
    " * @overload\n",
    " * @param {T} value\n",
    " * @param {number} count\n",
    " * @returns {T}\n",
    " */\n",
);

const ADJACENT_TEMPLATES: &str = concat!(
    "/** @template T @overload @param {T} value @returns {T} */\n",
    "/** @template T @overload @param {T} value @param {number} count @returns {T} */\n",
    "/** @template T @param {T} value @returns {T} */\n",
);

struct ParameterNodes {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct FunctionNodes {
    declaration: NodeRef,
    name: NodeRef,
    template: NodeRef,
    template_name: NodeRef,
    parameters: Vec<ParameterNodes>,
    returned: NodeRef,
    body: Option<NodeRef>,
}

#[derive(Debug, Eq, PartialEq)]
struct RowSnapshot {
    signature: SignatureId,
    template_symbol: SemanticSymbolId,
    template_type: TypeId,
    parameters: Vec<SemanticSymbolId>,
    parameter_types: Vec<TypeId>,
    returned: TypeId,
}

#[derive(Debug, Eq, PartialEq)]
struct GroupSnapshot {
    owner: SemanticSymbolId,
    callable: TypeId,
    rows: Vec<RowSnapshot>,
    queries: Vec<(NodeRef, TypeId)>,
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
                EscapedName::source("\"/project/generic-overload-groups.js\""),
                CanonicalSourceLanguage::JavaScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_javascript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    // The original fixture uses checkJs and noEmit without strict-option overrides.
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
            let [template] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
                panic!("expected one source-owned template per signature")
            };
            let NodeData::TypeParameterDeclaration(template_data) =
                &parsed.arena.get(*template).unwrap().data
            else {
                panic!("expected a real type-parameter declaration")
            };
            assert!(template_data.constraint.is_none());
            assert!(template_data.default_type.is_none());
            Some(FunctionNodes {
                declaration: node_ref(node),
                name: node_ref(function.name.unwrap()),
                template: node_ref(*template),
                template_name: node_ref(template_data.name),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .map(|&node| {
                        let NodeData::ParameterDeclaration(parameter) =
                            &parsed.arena.get(node).unwrap().data
                        else {
                            panic!("expected a required identifier parameter")
                        };
                        assert!(parameter.question_token.is_none());
                        assert!(parameter.dot_dot_dot_token.is_none());
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
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the source node must retain its real signature")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
    )
}

#[allow(clippy::too_many_lines)] // Keep the documented ranges and clone ownership in one check.
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
    let documented = comments
        .iter()
        .flat_map(|comment| {
            comment
                .tags()
                .iter()
                .filter(|tag| tag.kind() == JsDocTagKind::Overload)
                .map(move |tag| (comment, Some(tag), tag.overload_tags()))
        })
        .chain(std::iter::once((
            comments.last().unwrap(),
            None,
            comments.last().unwrap().tags(),
        )))
        .collect::<Vec<_>>();
    assert_eq!(functions.len(), documented.len());
    let implementation = functions.last().unwrap();
    let mut templates = HashSet::new();
    let mut template_names = HashSet::new();
    let mut parameter_nodes = HashSet::new();
    for (function, (comment, overload, tags)) in functions.iter().zip(documented) {
        let record = parsed.arena.get(function.declaration.node).unwrap();
        assert_eq!(record.parent, Some(parsed.source_file));
        let NodeData::FunctionDeclaration(data) = &record.data else {
            unreachable!()
        };
        let template_tag = comment
            .tags()
            .iter()
            .find(|tag| tag.kind() == JsDocTagKind::Template)
            .unwrap();
        let [documented_template] = template_tag.template_parameters() else {
            panic!("expected one template in the signature's containing comment")
        };
        assert_eq!(
            data.type_parameters.as_ref().unwrap().range,
            template_tag.range()
        );
        assert!(templates.insert(function.template));
        assert!(template_names.insert(function.template_name));
        let template = parsed.arena.get(function.template.node).unwrap();
        assert_eq!(template.flags, NodeFlags::REPARSED);
        assert_eq!(template.parent, Some(function.declaration.node));
        assert_eq!(template.range, documented_template.name().range());
        let name = parsed.arena.get(function.template_name.node).unwrap();
        assert_eq!(name.flags, NodeFlags::default());
        assert_eq!(name.parent, Some(function.template.node));
        assert_eq!(name.range, documented_template.name().range());
        assert_eq!(node_text(parsed, function.template_name), "T");

        let parameters = tags
            .iter()
            .filter(|tag| tag.kind() == JsDocTagKind::Parameter)
            .collect::<Vec<_>>();
        assert_eq!(function.parameters.len(), parameters.len());
        let returned = tags
            .iter()
            .find(|tag| tag.kind() == JsDocTagKind::Return)
            .unwrap();
        if let Some(overload) = overload {
            assert_eq!(record.flags, NodeFlags::REPARSED);
            let start = overload.range().start.get() as usize + 1;
            assert_eq!(record.range, range(start, start + "overload".len()));
            assert_eq!(node_text(parsed, function.declaration), "overload");
            assert!(function.body.is_none());
            assert_ne!(function.name, implementation.name);
            let name = parsed.arena.get(function.name.node).unwrap();
            assert_eq!(name.flags, NodeFlags::REPARSED);
            assert_eq!(name.parent, Some(function.declaration.node));
            assert_eq!(
                name.range,
                parsed.arena.get(implementation.name.node).unwrap().range
            );
            assert_eq!(
                data.parameters.range,
                TextRange::new(parameters[0].range().start, returned.range().start)
            );
        } else {
            assert!(function.body.is_some());
            assert!(record.flags.0 & NodeFlags::REPARSED.0 == 0);
        }
        for (parameter, documented) in function.parameters.iter().zip(parameters) {
            assert!(parameter_nodes.insert(parameter.declaration));
            let record = parsed.arena.get(parameter.declaration.node).unwrap();
            assert_eq!(record.parent, Some(function.declaration.node));
            if overload.is_some() {
                assert_eq!(record.flags, NodeFlags::REPARSED);
                assert_eq!(record.range, documented.range());
                assert_eq!(
                    parsed.arena.get(parameter.name.node).unwrap().range,
                    documented.name().unwrap().range()
                );
            }
            let annotation = parsed.arena.get(parameter.annotation.node).unwrap();
            assert_eq!(annotation.flags, NodeFlags::REPARSED);
            assert_eq!(annotation.parent, Some(parameter.declaration.node));
            assert_eq!(
                annotation.range,
                documented.type_expression().unwrap().range()
            );
        }
        let annotation = parsed.arena.get(function.returned.node).unwrap();
        assert_eq!(annotation.flags, NodeFlags::REPARSED);
        assert_eq!(annotation.parent, Some(function.declaration.node));
        assert_eq!(
            annotation.range,
            returned.type_expression().unwrap().range()
        );
    }
    let mut pending = vec![parsed.source_file];
    let mut reached = HashSet::new();
    while let Some(node) = pending.pop() {
        assert!(
            reached.insert(node),
            "the reparsed source must remain a tree"
        );
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

#[allow(clippy::too_many_lines)] // Check each signature against its own binder declarations and types.
fn snapshot(
    context: &mut CanonicalCheckerContext<'_>,
    functions: &[FunctionNodes],
) -> GroupSnapshot {
    let owner = symbol(context, functions[0].declaration);
    let declarations = functions
        .iter()
        .map(|row| row.declaration)
        .collect::<Vec<_>>();
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        declarations
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().value_declaration(),
        Some(functions[0].declaration)
    );
    let callable = context
        .get_type_at_location(functions.last().unwrap().name)
        .unwrap();
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let mut rows = Vec::new();
    let mut queries = Vec::new();
    let mut template_symbols = HashSet::new();
    let mut template_types = HashSet::new();
    let mut parameter_symbols = HashSet::new();
    for function in functions {
        assert_eq!(symbol(context, function.declaration), owner);
        assert_eq!(
            context.get_symbol_at_location(function.name).unwrap(),
            Some(owner)
        );
        for node in [function.declaration, function.name] {
            assert_eq!(context.get_type_at_location(node).unwrap(), callable);
            queries.push((node, callable));
        }
        let signature = signature(context, function.declaration);
        let template_symbol = symbol(context, function.template);
        assert!(template_symbols.insert(template_symbol));
        assert_eq!(
            context.get_symbol_declarations(template_symbol).unwrap(),
            [function.template]
        );
        assert_eq!(
            context
                .get_symbol_at_location(function.template_name)
                .unwrap(),
            Some(template_symbol)
        );
        let template_type = context
            .get_type_at_location(function.template_name)
            .unwrap();
        assert!(template_types.insert(template_type));
        queries.push((function.template_name, template_type));
        assert_eq!(
            context
                .store()
                .declared_type_links(template_symbol)
                .unwrap()
                .declared_type,
            Some(template_type)
        );
        let template = context.store().type_payload(template_type).unwrap();
        assert_eq!(template.symbol(), Some(template_symbol));
        let TypeData::TypeParameter(data) = template.data() else {
            panic!("each overload must keep its own canonical type parameter")
        };
        assert_eq!(data.target, None);
        assert_eq!(data.mapper, None);
        let no_constraint = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .no_constraint_type;
        assert!(
            data.constraint
                .is_none_or(|constraint| constraint == no_constraint)
        );
        let locals = context
            .file(FILE)
            .unwrap()
            .1
            .locals(function.declaration)
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(locals)
                .unwrap()
                .get(EscapedName::source("T").as_ref()),
            Some(template_symbol)
        );
        let mut parameters = Vec::new();
        let mut parameter_types = Vec::new();
        for parameter in &function.parameters {
            let symbol = symbol(context, parameter.declaration);
            assert!(parameter_symbols.insert(symbol));
            assert_eq!(
                context.get_symbol_declarations(symbol).unwrap(),
                [parameter.declaration]
            );
            assert_eq!(
                context.get_symbol_at_location(parameter.name).unwrap(),
                Some(symbol)
            );
            let type_ = context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
            for node in [parameter.name, parameter.annotation] {
                assert_eq!(context.get_type_at_location(node).unwrap(), type_);
                queries.push((node, type_));
            }
            parameters.push(symbol);
            parameter_types.push(type_);
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
        queries.push((function.returned, returned));
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(function.declaration));
        assert_eq!(record.type_parameters(), [template_type]);
        assert_eq!(record.parameters(), parameters);
        assert_eq!(
            record.min_argument_count(),
            i32::try_from(parameters.len()).unwrap()
        );
        assert_eq!(record.resolved_return_type(), Some(returned));
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        rows.push(RowSnapshot {
            signature,
            template_symbol,
            template_type,
            parameters,
            parameter_types,
            returned,
        });
    }
    let signatures = rows.iter().map(|row| row.signature).collect::<Vec<_>>();
    assert_eq!(
        signatures.iter().copied().collect::<HashSet<_>>().len(),
        functions.len()
    );
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected the overload owner's callable object")
    };
    assert_eq!(object.structured.call_signature_count, functions.len() - 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&signatures[..functions.len() - 1])
    );
    GroupSnapshot {
        owner,
        callable,
        rows,
        queries,
    }
}

fn assert_inferred_call(
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
    row: &RowSnapshot,
    display: &str,
) {
    let result = context.get_type_at_location(call).unwrap();
    assert_eq!(context.type_to_string(result).unwrap(), display);
    let selected = signature(context, call);
    let record = context.store().signature(selected).unwrap();
    assert_eq!(record.target(), Some(row.signature));
    assert!(record.mapper().is_some());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(result));
    assert_eq!(
        context.get_return_type_of_signature(selected).unwrap(),
        result
    );
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    functions: &[FunctionNodes],
    state: &GroupSnapshot,
    calls: &[NodeRef],
) {
    let display = context.type_to_string(state.callable).unwrap();
    let results = calls
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
        for &(node, type_) in &state.queries {
            assert_eq!(context.get_type_at_location(node).unwrap(), type_);
        }
        for &(call, type_, selected) in &results {
            assert_eq!(context.get_type_at_location(call).unwrap(), type_);
            assert_eq!(signature(context, call), selected);
            assert_eq!(
                context.get_return_type_of_signature(selected).unwrap(),
                type_
            );
        }
        assert_eq!(counts(context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn generic_jsdoc_overload_rows_own_distinct_templates_and_inferred_calls() {
    for comments in [SHARED_TEMPLATE, ADJACENT_TEMPLATES] {
        let source = format!(
            "{comments}function keep(value) {{ return value; }}\nkeep('kept');\nkeep(2, 3);\nkeep(true);\n"
        );
        let parsed = parse_javascript_source_file(&source);
        let functions = functions(&parsed);
        assert_eq!(functions.len(), 3);
        assert_source_clones(&parsed, &functions);
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 3);
        let returns = nodes(&parsed, SyntaxKind::ReturnStatement);
        let [returned] = returns.as_slice() else {
            panic!("only the implementation may have a body")
        };
        let NodeData::ReturnStatement(returned) = &parsed.arena.get(returned.node).unwrap().data
        else {
            unreachable!()
        };
        let body_value = NodeRef::new(parsed.arena.id(), FILE, returned.expression.unwrap());
        for query_first in [None, Some(0), Some(2)] {
            let mut context = context(&parsed);
            let early = query_first.map(|index| {
                (
                    index,
                    context
                        .get_type_from_type_node(functions[index].returned)
                        .unwrap(),
                )
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
                "{ <T>(value: T): T; <T>(value: T, count: number): T; }"
            );
            if let Some((index, early)) = early {
                assert_eq!(early, state.rows[index].template_type);
            }
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            for row in &state.rows {
                assert_eq!(row.parameter_types[0], row.template_type);
                assert_eq!(row.returned, row.template_type);
            }
            assert_eq!(
                state.rows[1].parameter_types,
                [state.rows[1].template_type, number]
            );
            assert_eq!(
                context.get_type_at_location(body_value).unwrap(),
                state.rows[2].template_type
            );
            assert_eq!(
                context.get_symbol_at_location(body_value).unwrap(),
                Some(state.rows[2].parameters[0])
            );
            for (&call, (row, display)) in
                calls.iter().zip([(0, "\"kept\""), (1, "2"), (0, "true")])
            {
                assert_inferred_call(&mut context, call, &state.rows[row], display);
            }
            assert_replay(&mut context, &functions, &state, &calls);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the generic signatures, fixed returns, and body error together.
fn generic_jsdoc_overload_implementations_keep_their_own_returns_and_diagnostics() {
    for (body, expected) in [
        ("1", None),
        (
            "'wrong'",
            Some("Type 'string' is not assignable to type 'number'."),
        ),
    ] {
        let source = format!(
            "/** @template T @param {{T}} value @returns {{number}}\n\
             * @overload @param {{T}} value @returns {{number}} */\n\
             function numeric(value) {{ return {body}; }}\nnumeric('text');\n"
        );
        let parsed = parse_javascript_source_file(&source);
        let functions = functions(&parsed);
        assert_eq!(functions.len(), 2);
        assert_source_clones(&parsed, &functions);
        let returns = nodes(&parsed, SyntaxKind::ReturnStatement);
        let [returned] = returns.as_slice() else {
            panic!("expected one implementation return")
        };
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 1);
        for query_first in [false, true] {
            let mut context = context(&parsed);
            if query_first {
                context
                    .get_type_from_type_node(functions[1].returned)
                    .unwrap();
                assert!(context.diagnostics().is_empty());
            }
            context.check_source_file(FILE).unwrap();
            if let Some(expected) = expected {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!(
                        "expected one implementation error, got {:?}",
                        context.diagnostics()
                    )
                };
                assert_eq!(diagnostic.diagnostic.code(), 2322);
                assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
                assert_eq!(diagnostic.node, Some(*returned));
                assert_eq!(diagnostic.range_override, None);
                assert_eq!(node_text(&parsed, *returned), format!("return {body};"));
                assert!(diagnostic.related_information.is_empty());
            } else {
                assert!(
                    context.diagnostics().is_empty(),
                    "{:?}",
                    context.diagnostics()
                );
            }
            let state = snapshot(&mut context, &functions);
            assert_eq!(
                context.type_to_string(state.callable).unwrap(),
                "<T>(value: T) => number"
            );
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            for row in &state.rows {
                assert_eq!(row.parameter_types, [row.template_type]);
                assert_eq!(row.returned, number);
            }
            for &call in &calls {
                assert_inferred_call(&mut context, call, &state.rows[0], "number");
            }
            assert_replay(&mut context, &functions, &state, &calls);
        }
    }
}

#[test]
fn generic_jsdoc_overload_compatibility_reports_the_real_overload_and_host_name() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @template T\n",
        " * @param {T} value @param {number} count @returns {T}\n",
        " * @overload @param {T} value @param {string} count @returns {T}\n",
        " * @overload @param {T} value @param {number} count @returns {T} */\n",
        "function conflict(value, count) { return value; }\n",
    ));
    let functions = functions(&parsed);
    assert_eq!(functions.len(), 3);
    assert_source_clones(&parsed, &functions);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one incompatible overload, got {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2394);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "This overload signature is not compatible with its implementation signature."
    );
    assert_eq!(diagnostic.node, Some(functions[0].declaration));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(node_text(&parsed, functions[0].declaration), "overload");
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("TS2394 must retain the real implementation site")
    };
    assert_eq!(related.diagnostic.code(), 2750);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "The implementation signature is declared here."
    );
    assert_eq!(related.node, Some(functions[2].name));
    assert_eq!(node_text(&parsed, functions[2].name), "conflict");
    let state = snapshot(&mut context, &functions);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(state.rows[0].parameter_types[1], bootstrap.string_type);
    assert_eq!(state.rows[1].parameter_types[1], bootstrap.number_type);
    assert_eq!(state.rows[2].parameter_types[1], bootstrap.number_type);
    assert_replay(&mut context, &functions, &state, &[]);
}

#[test]
fn generic_jsdoc_overload_bounds_and_multiple_templates_remain_explicit_boundaries() {
    for template in ["{string} T", "[T=string]", "T, U"] {
        let source = format!(
            "/** @template {template} @param {{T}} value @returns {{T}}\n\
             * @overload @param {{T}} value @returns {{T}} */\n\
             function keep(value) {{ return value; }}\n"
        );
        let parsed = parse_javascript_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
        let [declaration] = declarations.as_slice() else {
            panic!("unsupported templates must not produce erased overload rows")
        };
        let source = NodeRef::new(parsed.arena.id(), FILE, parsed.source_file);
        for _ in 0..2 {
            assert_eq!(
                plan_javascript_source_jsdoc(&parsed.arena, source),
                Err(JsDocCommentError::UnsupportedOverloadDeclaration(
                    *declaration
                ))
            );
        }
    }
}
