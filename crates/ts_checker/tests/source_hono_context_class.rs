use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
    types::TypeFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(0);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-booleans.ts\""),
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((record.range.start, node(parsed, id)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, data.name),
                    node(parsed, data.initializer.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

struct Field {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn field(parsed: &ParseResult, expected: &str) -> Field {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::PropertyDeclaration(data) = &record.data else {
                return None;
            };
            let name = match &parsed.arena.get(data.name)?.data {
                NodeData::Identifier(name) => &name.text,
                NodeData::PrivateIdentifier(name) => &name.text,
                _ => return None,
            };
            (name == expected).then(|| Field {
                declaration: node(parsed, id),
                name: node(parsed, data.name),
                initializer: node(parsed, data.initializer.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing field {expected}"))
}

fn field_type(
    context: &mut CanonicalCheckerContext<'_>,
    field: &Field,
) -> (SemanticSymbolId, TypeId) {
    let raw = context
        .file(FILE)
        .unwrap()
        .1
        .symbol(field.declaration)
        .unwrap();
    let symbol = context.store().get_merged_symbol(raw).unwrap();
    let type_ = context.get_type_at_location(field.name).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    (symbol, type_)
}

fn assert_diagnostic(
    context: &CanonicalCheckerContext<'_>,
    index: usize,
    node: NodeRef,
    code: u32,
    arguments: &[&str],
    message: &str,
) {
    let diagnostic = &context.diagnostics().as_slice()[index];
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments.as_slice(), arguments);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    queries: &[NodeRef],
    fields: &[SemanticSymbolId],
) {
    let types = queries
        .iter()
        .map(|&query| context.get_type_at_location(query).unwrap())
        .collect::<Vec<_>>();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.relation_state_snapshot(),
            context.diagnostics().clone(),
            store
                .source_file_links(context.source_file(FILE).unwrap())
                .cloned(),
            parsed
                .arena
                .iter()
                .map(|(id, _)| {
                    let node = node(parsed, id);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            fields
                .iter()
                .map(|&field| (field, store.value_symbol_links(field).cloned()))
                .collect::<Vec<_>>(),
        )
    };
    let warm = snapshot(context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        for (&query, &type_) in queries.iter().zip(&types) {
            assert_eq!(context.get_type_at_location(query).unwrap(), type_);
        }
        assert_eq!(snapshot(context), warm);
    }
}

#[test]
fn generic_class_boolean_fields_keep_read_types_and_call_errors() {
    let parsed = parse_source_file(concat!(
        "class Context<E> {\n",
        "  finalized: boolean = false;\n",
        "  active = true;\n",
        "  finish(value: boolean): boolean { this.finalized = value; return this.finalized; }\n",
        "}\n",
        "declare const state: Context<string>;\n",
        "const initial: boolean = state.finalized;\n",
        "const active: boolean = state.active;\n",
        "const result: boolean = state.finish(true);\n",
        "const badRead: string = state.finalized;\n",
        "state.finish(1);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();

    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    let finalized = field(&parsed, "finalized");
    let active = field(&parsed, "active");
    let fields = [&finalized, &active].map(|field| {
        let (symbol, type_) = field_type(&mut context, field);
        assert_eq!(type_, boolean);
        symbol
    });
    let reads = ["initial", "active", "result", "badRead"].map(|name| variable(&parsed, name).1);
    for read in reads {
        assert_eq!(context.get_type_at_location(read).unwrap(), boolean);
    }
    assert_eq!(context.diagnostics().len(), 2);
    assert_diagnostic(
        &context,
        0,
        variable(&parsed, "badRead").0,
        2322,
        &["boolean", "string"],
        "Type 'boolean' is not assignable to type 'string'.",
    );
    assert_diagnostic(
        &context,
        1,
        nodes(&parsed, SyntaxKind::NumericLiteral)[0],
        2345,
        &["number", "boolean"],
        "Argument of type 'number' is not assignable to parameter of type 'boolean'.",
    );
    let queries = reads
        .into_iter()
        .chain([
            finalized.name,
            finalized.initializer,
            active.name,
            active.initializer,
        ])
        .chain(nodes(&parsed, SyntaxKind::CallExpression))
        .collect::<Vec<_>>();
    assert_replay(&mut context, &parsed, &queries, &fields);
}

#[test]
fn boolean_fields_keep_readonly_static_and_private_access_rules() {
    let parsed = parse_source_file(concat!(
        "class Flags {\n",
        "  readonly fixed = false;\n",
        "  static ready = true;\n",
        "  #hidden: boolean = true;\n",
        "  read(): boolean { return this.#hidden; }\n",
        "}\n",
        "declare const flags: Flags;\n",
        "const fixed: false = flags.fixed;\n",
        "const ready: boolean = Flags.ready;\n",
        "const hidden: boolean = flags.read();\n",
        "flags.fixed = true;\n",
        "const leaked = flags.#hidden;\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();

    let fixed = field(&parsed, "fixed");
    let ready = field(&parsed, "ready");
    let hidden = field(&parsed, "#hidden");
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    let fixed_type = field_type(&mut context, &fixed);
    assert_eq!(context.type_to_string(fixed_type.1).unwrap(), "false");
    let literal_flags = context.store().type_payload(fixed_type.1).unwrap().flags();
    assert_eq!(literal_flags, TypeFlags::BOOLEAN_LITERAL);
    let ready_type = field_type(&mut context, &ready);
    let hidden_type = field_type(&mut context, &hidden);
    assert_eq!(ready_type.1, boolean);
    assert_eq!(hidden_type.1, boolean);
    let fixed_read = variable(&parsed, "fixed").1;
    let read_type = context.get_type_at_location(fixed_read).unwrap();
    assert_eq!(context.type_to_string(read_type).unwrap(), "false");
    for name in ["ready", "hidden"] {
        assert_eq!(
            context
                .get_type_at_location(variable(&parsed, name).1)
                .unwrap(),
            boolean
        );
    }

    let assignment = nodes(&parsed, SyntaxKind::BinaryExpression)[0];
    let NodeData::BinaryExpression(assignment) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::PropertyAccessExpression(target) =
        &parsed.arena.get(assignment.left).unwrap().data
    else {
        unreachable!()
    };
    let leaked = variable(&parsed, "leaked").1;
    let NodeData::PropertyAccessExpression(leaked) = &parsed.arena.get(leaked.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(context.diagnostics().len(), 2);
    assert_diagnostic(
        &context,
        0,
        node(&parsed, target.name),
        2540,
        &["fixed"],
        "Cannot assign to 'fixed' because it is a read-only property.",
    );
    assert_diagnostic(
        &context,
        1,
        node(&parsed, leaked.name),
        18013,
        &["#hidden", "Flags"],
        "Property '#hidden' is not accessible outside class 'Flags' because it has a private identifier.",
    );
    assert_replay(
        &mut context,
        &parsed,
        &[
            fixed.name,
            fixed.initializer,
            ready.name,
            ready.initializer,
            hidden.name,
            hidden.initializer,
            fixed_read,
            variable(&parsed, "ready").1,
            variable(&parsed, "hidden").1,
        ],
        &[fixed_type.0, ready_type.0, hidden_type.0],
    );
}

#[test]
fn boolean_initializers_preserve_annotations_and_report_mismatches() {
    let parsed = parse_source_file(concat!(
        "class Flags { wrong: number = false; readonly annotated: boolean = true; }\n",
        "declare const flags: Flags;\n",
        "const numberValue: number = flags.wrong;\n",
        "const booleanValue: boolean = flags.annotated;\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();

    let wrong = field(&parsed, "wrong");
    let annotated = field(&parsed, "annotated");
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    let wrong_type = field_type(&mut context, &wrong);
    let annotated_type = field_type(&mut context, &annotated);
    assert_eq!(wrong_type.1, number);
    assert_eq!(annotated_type.1, boolean);
    for (name, expected) in [("numberValue", number), ("booleanValue", boolean)] {
        assert_eq!(
            context
                .get_type_at_location(variable(&parsed, name).1)
                .unwrap(),
            expected
        );
    }
    assert_eq!(context.diagnostics().len(), 1);
    assert_diagnostic(
        &context,
        0,
        wrong.name,
        2322,
        &["boolean", "number"],
        "Type 'boolean' is not assignable to type 'number'.",
    );
    assert_replay(
        &mut context,
        &parsed,
        &[
            wrong.name,
            wrong.initializer,
            annotated.name,
            annotated.initializer,
            variable(&parsed, "numberValue").1,
            variable(&parsed, "booleanValue").1,
        ],
        &[wrong_type.0, annotated_type.0],
    );
}
