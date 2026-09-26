use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_javascript_source_file};

const FILE: FileId = FileId::new(8_226);

const SHARED_TEMPLATE: &str = concat!(
    "/**\n",
    " * @template T\n",
    " * @param {T} value\n",
    " * @returns {number}\n",
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
    "/** @template T @param {T} value @returns {number} */\n",
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
                EscapedName::source("\"/project/jsdoc-generic-call-integration.js\""),
                CanonicalSourceLanguage::JavaScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_javascript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    // Keep the original fixture's checkJs and noEmit behavior without strict overrides.
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

fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
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
                panic!("each source row must own one template")
            };
            let record = parsed.arena.get(*template).unwrap();
            assert_eq!(record.flags, NodeFlags::REPARSED);
            assert_eq!(record.parent, Some(node));
            let NodeData::TypeParameterDeclaration(template_data) = &record.data else {
                panic!("expected a real template declaration")
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
                            panic!("expected a required parameter")
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
        .expect("the source node must retain its resolved signature")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    [
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().symbol_store().symbol_table_len(),
    ]
}

#[allow(clippy::too_many_lines)] // Check all original rows before comparing selected call signatures.
fn snapshot(
    context: &mut CanonicalCheckerContext<'_>,
    functions: &[FunctionNodes],
) -> GroupSnapshot {
    let owner = symbol(context, functions[0].declaration);
    let callable = context
        .get_type_at_location(functions.last().unwrap().name)
        .unwrap();
    let declarations = functions
        .iter()
        .map(|function| function.declaration)
        .collect::<Vec<_>>();
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        declarations
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().value_declaration(),
        Some(functions[0].declaration)
    );
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let mut rows = Vec::new();
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
        }
        let template_symbol = symbol(context, function.template);
        let template_type = context
            .get_type_at_location(function.template_name)
            .unwrap();
        assert!(template_symbols.insert(template_symbol));
        assert!(template_types.insert(template_type));
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
        let record = context.store().type_payload(template_type).unwrap();
        assert_eq!(record.symbol(), Some(template_symbol));
        let TypeData::TypeParameter(template) = record.data() else {
            panic!("source templates must remain canonical type parameters")
        };
        assert_eq!(template.target, None);
        assert_eq!(template.mapper, None);
        let mut parameters = Vec::new();
        let mut parameter_types = Vec::new();
        for parameter in &function.parameters {
            let symbol = symbol(context, parameter.declaration);
            let type_ = context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
            assert!(parameter_symbols.insert(symbol));
            assert_eq!(
                context.get_symbol_declarations(symbol).unwrap(),
                [parameter.declaration]
            );
            assert_eq!(
                context.get_symbol_at_location(parameter.name).unwrap(),
                Some(symbol)
            );
            assert_eq!(context.get_type_at_location(parameter.name).unwrap(), type_);
            assert_eq!(
                context.get_type_at_location(parameter.annotation).unwrap(),
                type_
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
            parameters.push(symbol);
            parameter_types.push(type_);
        }
        let signature = signature(context, function.declaration);
        let returned = context.get_return_type_of_signature(signature).unwrap();
        assert_eq!(
            context.get_type_from_type_node(function.returned).unwrap(),
            returned
        );
        assert_eq!(
            context.get_type_at_location(function.returned).unwrap(),
            returned
        );
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
        panic!("expected the real overload owner")
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
    }
}

fn inferred_call(
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
    row: &RowSnapshot,
    display: &str,
) -> (TypeId, SignatureId) {
    let result = context.get_type_at_location(call).unwrap();
    assert_eq!(context.type_to_string(result).unwrap(), display);
    let selected = signature(context, call);
    let record = context.store().signature(selected).unwrap();
    assert_eq!(record.target(), Some(row.signature));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(result));
    assert_eq!(
        context
            .store()
            .map_type(record.mapper().unwrap(), row.template_type),
        Some(result)
    );
    assert_eq!(record.parameters().len(), row.parameters.len());
    for (index, &parameter) in record.parameters().iter().enumerate() {
        let links = context.store().value_symbol_links(parameter).unwrap();
        assert_eq!(links.target, Some(row.parameters[index]));
        assert_eq!(
            links.resolved_type,
            Some(if index == 0 {
                result
            } else {
                row.parameter_types[index]
            })
        );
    }
    assert_eq!(
        context.get_return_type_of_signature(selected).unwrap(),
        result
    );
    (result, selected)
}

#[test]
#[allow(clippy::too_many_lines)] // Keep call selection, the implementation error, and replay in one control.
fn jsdoc_generic_group_calls_keep_public_templates_and_report_the_real_body_error() {
    for comments in [SHARED_TEMPLATE, ADJACENT_TEMPLATES] {
        let source = format!(
            "{comments}function numeric(value) {{ return value; }}\nnumeric('text');\nnumeric(2, 3);\n"
        );
        let parsed = parse_javascript_source_file(&source);
        let functions = functions(&parsed);
        assert_eq!(functions.len(), 3);
        for function in &functions[..2] {
            assert!(function.body.is_none());
            assert_eq!(node_text(&parsed, function.declaration), "overload");
        }
        let implementation = &functions[2];
        assert_eq!(node_text(&parsed, implementation.returned), "number");
        let NodeData::Block(body) = &parsed
            .arena
            .get(implementation.body.unwrap().node)
            .unwrap()
            .data
        else {
            panic!("only the real implementation has a body")
        };
        let [returned] = body.statements.nodes.as_slice() else {
            panic!("expected the implementation's one return statement")
        };
        let returned = NodeRef::new(parsed.arena.id(), FILE, *returned);
        let NodeData::ReturnStatement(statement) = &parsed.arena.get(returned.node).unwrap().data
        else {
            panic!("expected the original return statement")
        };
        let value = NodeRef::new(parsed.arena.id(), FILE, statement.expression.unwrap());
        assert_eq!(node_text(&parsed, value), "value");
        assert_eq!(node_text(&parsed, returned), "return value;");
        let return_range = parsed.arena.get(returned.node).unwrap().range;
        let return_start = source.find("return value;").unwrap();
        assert_eq!(return_range.start.get() as usize, return_start);
        assert_eq!(
            return_range.end.get() as usize,
            return_start + "return value;".len()
        );
        let mut calls = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::CallExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FILE,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        calls.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
        assert_eq!(calls.len(), 2);
        for early_row in [None, Some(0), Some(1), Some(2)] {
            let mut context = context(&parsed);
            let early = early_row.map(|index| {
                let function = &functions[index];
                (
                    index,
                    context
                        .get_type_from_type_node(function.parameters[0].annotation)
                        .unwrap(),
                    context.get_type_from_type_node(function.returned).unwrap(),
                )
            });
            assert!(context.diagnostics().is_empty());
            context.check_source_file(FILE).unwrap();
            let diagnostics = context.diagnostics().clone();
            let [diagnostic] = diagnostics.as_slice() else {
                panic!("expected only the implementation return error, got {diagnostics:?}")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'T' is not assignable to type 'number'."
            );
            assert_eq!(diagnostic.node, Some(returned));
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            let state = snapshot(&mut context, &functions);
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert_eq!(
                context.type_to_string(state.callable).unwrap(),
                "{ <T>(value: T): T; <T>(value: T, count: number): T; }"
            );
            for row in &state.rows[..2] {
                assert_eq!(row.parameter_types[0], row.template_type);
                assert_eq!(row.returned, row.template_type);
            }
            assert_eq!(
                state.rows[1].parameter_types,
                [state.rows[1].template_type, number]
            );
            assert_eq!(state.rows[2].parameter_types, [state.rows[2].template_type]);
            assert_eq!(state.rows[2].returned, number);
            assert_eq!(
                context.get_type_at_location(value).unwrap(),
                state.rows[2].template_type
            );
            assert_eq!(
                context.get_symbol_at_location(value).unwrap(),
                Some(state.rows[2].parameters[0])
            );
            if let Some((index, parameter, returned)) = early {
                assert_eq!(parameter, state.rows[index].template_type);
                assert_eq!(returned, state.rows[index].returned);
            }
            let selected = calls
                .iter()
                .zip(["\"text\"", "2"])
                .enumerate()
                .map(|(index, (&call, display))| {
                    inferred_call(&mut context, call, &state.rows[index], display)
                })
                .collect::<Vec<_>>();
            let before = counts(&context);
            for _ in 0..2 {
                context.recheck_source_file(FILE).unwrap();
                assert_eq!(snapshot(&mut context, &functions), state);
                assert_eq!(
                    context.get_type_at_location(value).unwrap(),
                    state.rows[2].template_type
                );
                assert_eq!(
                    context.get_symbol_at_location(value).unwrap(),
                    Some(state.rows[2].parameters[0])
                );
                for (index, (&call, display)) in calls.iter().zip(["\"text\"", "2"]).enumerate() {
                    assert_eq!(
                        inferred_call(&mut context, call, &state.rows[index], display),
                        selected[index]
                    );
                }
                assert_eq!(context.diagnostics(), &diagnostics);
                assert_eq!(counts(&context), before);
            }
        }
    }
}
