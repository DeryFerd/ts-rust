use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeData, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/linear-logical.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

#[derive(Clone, Copy)]
struct LogicalNodes {
    left: NodeRef,
    right: NodeRef,
    callee: NodeRef,
    logical: NodeRef,
    argument: NodeRef,
    left_receiver: NodeRef,
    right_receiver: NodeRef,
}

impl LogicalNodes {
    fn all(self) -> [NodeRef; 7] {
        [
            self.left,
            self.right,
            self.callee,
            self.logical,
            self.argument,
            self.left_receiver,
            self.right_receiver,
        ]
    }
}

fn logical_nodes(parsed: &ParseResult, file: FileId) -> LogicalNodes {
    let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
    let (logical, binary) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            (parsed.arena.get(binary.operator_token)?.kind == SyntaxKind::AmpersandAmpersandToken)
                .then_some((reference(node), binary))
        })
        .unwrap();
    let NodeData::PropertyAccessExpression(left) = &parsed.arena.get(binary.left).unwrap().data
    else {
        panic!("the left operand is the actual property read")
    };
    let NodeData::CallExpression(call) = &parsed.arena.get(binary.right).unwrap().data else {
        panic!("the right operand is the actual call")
    };
    let NodeData::PropertyAccessExpression(callee) =
        &parsed.arena.get(call.expression).unwrap().data
    else {
        panic!("the call uses the same property reference")
    };
    let [argument] = call.arguments.nodes.as_slice() else {
        panic!("the control has one source argument")
    };
    LogicalNodes {
        left: reference(binary.left),
        right: reference(binary.right),
        callee: reference(call.expression),
        logical,
        argument: reference(*argument),
        left_receiver: reference(left.expression),
        right_receiver: reference(callee.expression),
    }
}

fn type_at(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[test]
#[allow(clippy::too_many_lines)] // Keep source, call identities, diagnostics, and replay together.
fn required_property_logical_statements_check_calls_and_replay() {
    for (index, (argument_type, diagnostic_code)) in [("string", None), ("number", Some(2345))]
        .into_iter()
        .enumerate()
    {
        let parsed = parse_source_file(&format!(
            "export type Sink = {{ send: (value: string) => void; }}; \
             export function emit(sink: Sink, value: {argument_type}): void {{ \
             sink.send && sink.send(value); }}"
        ));
        let file = FileId::new(45_300 + u32::try_from(index).unwrap());
        let nodes = logical_nodes(&parsed, file);
        let mut context = context(&parsed, file);
        assert!(context.store().type_node_links(nodes.right).is_none());
        assert!(context.store().signature_links(nodes.right).is_none());

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            diagnostic_code.into_iter().collect::<Vec<_>>()
        );
        if let Some(diagnostic) = context.diagnostics().as_slice().first() {
            assert_eq!(diagnostic.node, Some(nodes.argument));
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        }
        let member = context
            .store()
            .symbol_node_links(nodes.left)
            .unwrap()
            .resolved_symbol
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_node_links(nodes.callee)
                .unwrap()
                .resolved_symbol,
            Some(member)
        );
        assert_eq!(
            context.store().symbol_node_links(nodes.left_receiver),
            context.store().symbol_node_links(nodes.right_receiver)
        );
        assert_eq!(
            type_at(&context, nodes.left_receiver),
            type_at(&context, nodes.right_receiver)
        );
        let callable = type_at(&context, nodes.left);
        assert_eq!(type_at(&context, nodes.callee), callable);
        let TypeData::Object(callable) = context.store().type_payload(callable).unwrap().data()
        else {
            panic!("the property retains its source function type")
        };
        let [signature] = callable.structured.signatures.as_deref().unwrap() else {
            panic!("the source property has one call signature")
        };
        let signature = *signature;
        assert_eq!(
            context
                .store()
                .signature_links(nodes.right)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
        let parameter = context.store().signature(signature).unwrap().parameters()[0];
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type,
            Some(bootstrap.string_type)
        );
        assert_eq!(type_at(&context, nodes.right), bootstrap.void_type);
        assert_eq!(type_at(&context, nodes.logical), bootstrap.void_type);
        let source = context.source_file(file).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source)
                .unwrap()
                .type_checked
        );
        let checked_links = context.store().source_file_links(source).unwrap().clone();
        let expression_links = nodes.all().map(|node| {
            (
                context.store().type_node_links(node).cloned(),
                context.store().symbol_node_links(node).cloned(),
            )
        });
        let call_links = context
            .store()
            .signature_links(nodes.right)
            .unwrap()
            .clone();
        let diagnostics = context.diagnostics().clone();
        let before = counts(&context);
        for _ in 0..3 {
            context.recheck_source_file(file).unwrap();
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(counts(&context), before);
            assert_eq!(
                context.store().source_file_links(source),
                Some(&checked_links)
            );
            assert_eq!(
                context.store().signature_links(nodes.right),
                Some(&call_links)
            );
            assert_eq!(
                nodes.all().map(|node| (
                    context.store().type_node_links(node).cloned(),
                    context.store().symbol_node_links(node).cloned(),
                )),
                expression_links
            );
        }
    }
}

#[test]
fn required_noncallable_property_statements_keep_the_call_diagnostic() {
    let parsed = parse_source_file(concat!(
        "export type Sink = { send: number; }; ",
        "export function emit(sink: Sink, value: string): void { ",
        "sink.send && sink.send(value); }",
    ));
    let file = FileId::new(45_302);
    let nodes = logical_nodes(&parsed, file);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the real noncallable property must produce one diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2349);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(type_at(&context, nodes.left), bootstrap.number_type);
    assert_eq!(type_at(&context, nodes.callee), bootstrap.number_type);
    assert_eq!(type_at(&context, nodes.right), bootstrap.error_type);
    let diagnostics = context.diagnostics().clone();
    let before = counts(&context);
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(&context), before);
}

#[test]
fn logical_property_statements_keep_optional_and_nullable_reads_unsupported() {
    for (index, member) in [
        "send?: (value: string) => void",
        "send: ((value: string) => void) | undefined",
        "send: ((value: string) => void) | null",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(&format!(
            "export type Sink = {{ {member}; }}; \
             export function emit(sink: Sink, value: string): void {{ \
             sink.send && sink.send(value); }}"
        ));
        let file = FileId::new(45_303 + u32::try_from(index).unwrap());
        let nodes = logical_nodes(&parsed, file);
        let mut context = context(&parsed, file);
        for _ in 0..2 {
            let error = context.check_source_file(file).unwrap_err();
            assert!(
                matches!(error,
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                    node, kind: SyntaxKind::BinaryExpression, ..
                }) if node == nodes.logical),
                "{error:?}"
            );
            assert!(context.store().type_node_links(nodes.left).is_some());
            assert!(context.store().type_node_links(nodes.right).is_none());
            assert!(context.store().signature_links(nodes.right).is_none());
            assert!(context.diagnostics().is_empty());
            assert!(
                !context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
        }
    }
}
