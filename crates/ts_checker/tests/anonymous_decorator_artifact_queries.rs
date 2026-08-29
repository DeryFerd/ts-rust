use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    ResolvedSignatureState, artifact_queries::CanonicalArtifactQueryError,
};
use ts_parser::{ParseResult, parse_source_file};

const ORIGINAL_SOURCE: &str = "class {\n  @x\n  m() {\n    // ...\n  }\n};\n";

fn context(
    parsed: &ParseResult,
    file: FileId,
    declaration_file: bool,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    let path = if declaration_file {
        "\"/project/decorator.d.ts\""
    } else {
        "\"/project/anonymousClassDecoratorEs2022.ts\""
    };
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source(path),
                CanonicalSourceLanguage::TypeScript,
                declaration_file,
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
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn first_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?}"))
}

fn decorator_expression(parsed: &ParseResult, file: FileId) -> NodeRef {
    let decorator = first_node(parsed, file, SyntaxKind::Decorator);
    let NodeData::Decorator(data) = &parsed.arena.get(decorator.node).unwrap().data else {
        panic!("decorator must retain its expression")
    };
    NodeRef::new(parsed.arena.id(), file, data.expression)
}

fn bound_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let symbol = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

#[allow(clippy::too_many_lines)] // Both query orders must preserve the original recovered class.
fn assert_original_queries(type_first: bool) {
    let parsed = parse_source_file(ORIGINAL_SOURCE);
    let file = FileId::new(4_100);
    let mut context = context(&parsed, file, false);
    let expression = decorator_expression(&parsed, file);
    let class = first_node(&parsed, file, SyntaxKind::ClassDeclaration);
    let method = first_node(&parsed, file, SyntaxKind::MethodDeclaration);
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else {
        panic!("method must retain its name")
    };
    let method_name = NodeRef::new(parsed.arena.id(), file, data.name);
    let class_symbol = bound_symbol(&context, class);
    let method_symbol = bound_symbol(&context, method);
    let missing_type = CanonicalArtifactQueryError::MissingType {
        node: expression,
        kind: SyntaxKind::Identifier,
    };
    let cold_counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    let cold_relations = context.store().relation_state_snapshot();

    if type_first {
        assert_eq!(context.get_type_at_location(expression), Err(missing_type));
    } else {
        assert_eq!(context.get_symbol_at_location(expression), Ok(None));
    }
    assert_eq!(context.get_type_at_location(expression), Err(missing_type));
    assert_eq!(context.get_symbol_at_location(expression), Ok(None));
    assert_eq!(
        context.get_symbol_at_location(method_name),
        Ok(Some(method_symbol))
    );
    assert_eq!(
        context.symbol_to_string(method_symbol).unwrap(),
        "__missing.m"
    );
    assert_eq!(
        context.get_symbol_declarations(method_symbol).unwrap(),
        &[method]
    );
    assert_eq!(
        context.store().symbol(method_symbol).unwrap().parent(),
        Some(class_symbol)
    );
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| {
                let node = diagnostic.node.unwrap();
                let range = diagnostic.range_override.map_or_else(
                    || parsed.arena.get(node.node).unwrap().range,
                    CanonicalCheckerDiagnosticRange::range,
                );
                (
                    diagnostic.diagnostic.code(),
                    range.start.get(),
                    range.end.get(),
                    diagnostic.diagnostic.render().unwrap(),
                )
            })
            .collect::<Vec<_>>(),
        [
            (
                1211,
                0,
                5,
                "A class declaration without the 'default' modifier must have a name.".to_owned(),
            ),
            (2304, 11, 12, "Cannot find name 'x'.".to_owned()),
        ]
    );
    let source = context.source_file(file).unwrap();
    assert!(
        context
            .store()
            .source_file_links(source)
            .unwrap()
            .type_checked
    );
    let diagnostics = context.diagnostics().clone();

    for _ in 0..3 {
        context.recheck_source_file(file).unwrap();
        assert_eq!(context.get_symbol_at_location(expression), Ok(None));
        assert_eq!(context.get_type_at_location(expression), Err(missing_type));
        assert_eq!(
            context.get_symbol_at_location(method_name),
            Ok(Some(method_symbol))
        );
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            cold_counts
        );
        assert_eq!(context.store().relation_state_snapshot(), cold_relations);
        assert!(context.store().declared_type_links(class_symbol).is_none());
        assert!(context.store().value_symbol_links(class_symbol).is_none());
    }
}

#[test]
fn anonymous_decorator_symbol_query_preserves_recovered_method_identity() {
    assert_original_queries(false);
}

#[test]
fn anonymous_decorator_type_query_preserves_missing_type_classification() {
    assert_original_queries(true);
}

#[test]
fn declaration_file_decorators_keep_lexical_symbol_and_type_queries() {
    // Declaration-file queries do not require the source decorator checker.
    for class in ["class", "declare class Named"] {
        let source = format!(
            "declare const decorate: () => void;\n{class} {{\n  @decorate\n  m(): void;\n}}\n"
        );
        let parsed = parse_source_file(&source);
        let file = FileId::new(4_101);
        let mut context = context(&parsed, file, true);
        let expression = decorator_expression(&parsed, file);
        let declaration = first_node(&parsed, file, SyntaxKind::VariableDeclaration);
        let symbol = bound_symbol(&context, declaration);
        let class = first_node(&parsed, file, SyntaxKind::ClassDeclaration);
        let class_symbol = bound_symbol(&context, class);

        assert_eq!(context.get_symbol_at_location(expression), Ok(Some(symbol)));
        let type_ = context.get_type_at_location(expression).unwrap();
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("decorator must have a declared callable annotation")
        };
        let annotation = NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap());
        let ResolvedSignatureState::Resolved(signature) = context
            .store()
            .signature_links(annotation)
            .unwrap()
            .resolved_signature
        else {
            panic!("decorator query must retain its annotation signature")
        };
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(context.store().intrinsic_bootstrap().unwrap().void_type)
        );
        assert_eq!(
            context.store().signature(signature).unwrap().declaration(),
            Some(annotation)
        );
        assert_eq!(context.type_to_string(type_).unwrap(), "() => void");
        assert_eq!(context.symbol_to_string(symbol).unwrap(), "decorate");
        assert_eq!(
            context.get_symbol_declarations(symbol).unwrap(),
            &[declaration]
        );
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        );
        for _ in 0..3 {
            assert_eq!(context.get_type_at_location(expression), Ok(type_));
            assert_eq!(context.get_symbol_at_location(expression), Ok(Some(symbol)));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().relation_state_snapshot(),
                ),
                warm
            );
            assert!(context.store().declared_type_links(class_symbol).is_none());
            assert!(context.store().value_symbol_links(class_symbol).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both cold query orders retain the class value and method identity.
fn qualified_decorators_keep_class_value_and_static_method_queries() {
    for type_first in [false, true] {
        let parsed = parse_source_file(concat!(
            "declare class Decorators { static apply(): void; }\n",
            "declare class Named { @Decorators.apply m(): void; }\n",
        ));
        let file = FileId::new(4_102);
        let mut context = context(&parsed, file, true);
        let expression = decorator_expression(&parsed, file);
        let NodeData::PropertyAccessExpression(access) =
            &parsed.arena.get(expression.node).unwrap().data
        else {
            panic!("decorator must read a static method")
        };
        let receiver = NodeRef::new(parsed.arena.id(), file, access.expression);
        let name = NodeRef::new(parsed.arena.id(), file, access.name);
        let class = first_node(&parsed, file, SyntaxKind::ClassDeclaration);
        let class_symbol = bound_symbol(&context, class);
        let method = first_node(&parsed, file, SyntaxKind::MethodDeclaration);
        let method_symbol = bound_symbol(&context, method);

        assert!(context.store().declared_type_links(class_symbol).is_none());
        assert!(context.store().value_symbol_links(class_symbol).is_none());
        if type_first {
            let receiver_type = context.get_type_at_location(receiver).unwrap();
            assert_eq!(
                context.type_to_string(receiver_type).unwrap(),
                "typeof Decorators"
            );
        } else {
            assert_eq!(
                context.get_symbol_at_location(receiver),
                Ok(Some(class_symbol))
            );
            assert_eq!(
                context.get_symbol_at_location(expression),
                Ok(Some(method_symbol))
            );
            assert!(context.store().declared_type_links(class_symbol).is_none());
            assert!(context.store().value_symbol_links(class_symbol).is_none());
        }
        let receiver_type = context.get_type_at_location(receiver).unwrap();
        assert_eq!(
            context.type_to_string(receiver_type).unwrap(),
            "typeof Decorators"
        );
        let method_type = context.get_type_at_location(expression).unwrap();
        assert_eq!(context.type_to_string(method_type).unwrap(), "() => void");
        assert_eq!(context.get_type_at_location(name), Ok(method_type));
        let shells = context.get_class_query_shells(class_symbol).unwrap();
        assert_eq!(receiver_type, shells.value_type());
        assert_ne!(receiver_type, shells.instance_type());
        assert_eq!(
            context.get_symbol_declarations(method_symbol).unwrap(),
            &[method]
        );
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        );

        for _ in 0..3 {
            assert_eq!(
                context.get_symbol_at_location(receiver),
                Ok(Some(class_symbol))
            );
            assert_eq!(
                context.get_symbol_at_location(expression),
                Ok(Some(method_symbol))
            );
            assert_eq!(
                context.get_symbol_at_location(name),
                Ok(Some(method_symbol))
            );
            assert_eq!(context.get_type_at_location(receiver), Ok(receiver_type));
            assert_eq!(context.get_type_at_location(expression), Ok(method_type));
            assert_eq!(context.get_type_at_location(name), Ok(method_type));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().relation_state_snapshot(),
                ),
                warm
            );
            assert!(context.diagnostics().is_empty());
        }
    }
}
