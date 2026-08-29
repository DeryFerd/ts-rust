use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, DeclaredTypeError,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId, TypeNodeUnavailable,
};
use ts_parser::{ParseResult, parse_source_file};

const CONSUMER: FileId = FileId::new(8_210);
const PRODUCER: FileId = FileId::new(8_211);
const TYPES: FileId = FileId::new(8_212);
const TYPES_SOURCE: &str = "export interface Shape { value: string }";
const PRODUCER_SOURCE: &str =
    "import type { Shape } from './types'; export default (value: Shape): Shape => value;";
const CONSUMER_SOURCE: &str =
    "import keep from './producer'; const result = keep({ value: 'kept' });";

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().expect("the fixture must contain this node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn context<'arena>(
    consumer: &'arena ParseResult,
    producer: &'arena ParseResult,
    types: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (CONSUMER, consumer, "\"/project/consumer.ts\""),
        (PRODUCER, producer, "\"/project/producer.ts\""),
        (TYPES, types, "\"/project/types.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, name) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let resolutions = [(CONSUMER, consumer, PRODUCER), (PRODUCER, producer, TYPES)].map(
        |(file, parsed, target)| {
            let declaration = only_node(parsed, file, SyntaxKind::ImportDeclaration);
            let NodeData::ImportDeclaration(import) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!();
            };
            CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(parsed.arena.id(), file, import.module_specifier),
                CanonicalResolvedModuleInput::new(
                    target,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            )
        },
    );
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn checked(checker: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    checker
        .source_file(file)
        .and_then(|source| checker.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_signature_authority(
    checker: &mut CanonicalCheckerContext<'_>,
    signature: SignatureId,
    annotation: NodeRef,
    alias: SemanticSymbolId,
    expected: TypeId,
) {
    let state = |checker: &CanonicalCheckerContext<'_>| {
        (
            counts(checker),
            checker.store().type_node_links(annotation).cloned(),
            checker.store().symbol_node_links(annotation).cloned(),
            checker.store().alias_symbol_links(alias).cloned(),
        )
    };
    let before = state(checker);
    assert_eq!(
        checker.get_return_type_of_signature(signature),
        Ok(expected)
    );
    // The signature owns this authority. An independent annotation query does not.
    assert_eq!(
        checker.get_type_from_type_node(annotation),
        Err(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::ImportAliasTypeReference {
                node: annotation,
                alias,
            },
        )),
    );
    assert_eq!(state(checker), before);
    assert!(checker.diagnostics().is_empty());
}

#[allow(clippy::too_many_lines)] // Keep import demand, signature authority, and body checking in both source orders.
fn check_order(producer_first: bool) {
    let consumer = parse_source_file(CONSUMER_SOURCE);
    let producer = parse_source_file(PRODUCER_SOURCE);
    let types = parse_source_file(TYPES_SOURCE);
    let declaration = only_node(&producer, PRODUCER, SyntaxKind::ArrowFunction);
    let export = only_node(&producer, PRODUCER, SyntaxKind::ExportAssignment);
    let shape_import = only_node(&producer, PRODUCER, SyntaxKind::ImportSpecifier);
    let value_import = only_node(&consumer, CONSUMER, SyntaxKind::ImportClause);
    let call = only_node(&consumer, CONSUMER, SyntaxKind::CallExpression);
    let shape_declaration = only_node(&types, TYPES, SyntaxKind::InterfaceDeclaration);
    let NodeData::ArrowFunction(arrow) = &producer.arena.get(declaration.node).unwrap().data else {
        unreachable!();
    };
    assert!(arrow.type_parameters.is_none());
    let [parameter] = arrow.parameters.nodes.as_slice() else {
        panic!("the arrow must retain its one typed parameter");
    };
    let parameter = NodeRef::new(producer.arena.id(), PRODUCER, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &producer.arena.get(parameter.node).unwrap().data
    else {
        unreachable!();
    };
    let parameter_annotation =
        NodeRef::new(producer.arena.id(), PRODUCER, parameter_data.type_.unwrap());
    let return_annotation = NodeRef::new(producer.arena.id(), PRODUCER, arrow.type_.unwrap());
    let body = NodeRef::new(producer.arena.id(), PRODUCER, arrow.body);
    let NodeData::ExportAssignment(assignment) = &producer.arena.get(export.node).unwrap().data
    else {
        unreachable!();
    };
    assert!(!assignment.is_export_equals);
    assert_eq!(assignment.expression, declaration.node);

    let mut checker = context(&consumer, &producer, &types);
    assert_eq!(checker.file_order(), [CONSUMER, PRODUCER, TYPES]);
    let owner = symbol(&checker, declaration);
    let exported = symbol(&checker, export);
    let imported = symbol(&checker, value_import);
    let shape_alias = symbol(&checker, shape_import);
    let shape_owner = symbol(&checker, shape_declaration);
    let parameter_symbol = symbol(&checker, parameter);
    let module = symbol(&checker, checker.file(PRODUCER).unwrap().1.source_file());
    assert_ne!(owner, exported);
    assert_ne!(owner, imported);
    assert_ne!(exported, imported);
    for (symbol, flags) in [
        (owner, SymbolFlags::FUNCTION),
        (exported, SymbolFlags::PROPERTY),
        (imported, SymbolFlags::ALIAS),
    ] {
        assert_eq!(checker.store().symbol(symbol).unwrap().flags(), flags);
        assert!(checker.store().value_symbol_links(symbol).is_none());
    }
    assert_eq!(
        checker.store().symbol(exported).unwrap().parent(),
        Some(module)
    );
    let exports = checker.store().symbol(module).unwrap().exports().unwrap();
    assert_eq!(
        checker
            .store()
            .symbol_table(exports)
            .unwrap()
            .get(InternalSymbolName::Default.as_ref()),
        Some(exported),
    );
    assert!(checker.store().signature_links(declaration).is_none());
    for file in [CONSUMER, PRODUCER, TYPES] {
        assert!(!checked(&checker, file));
    }
    if producer_first {
        checker.check_source_file(PRODUCER).unwrap();
    }
    checker.check_source_file(CONSUMER).unwrap();
    assert!(checked(&checker, CONSUMER));
    assert_eq!(checked(&checker, PRODUCER), producer_first);
    if !producer_first {
        assert!(checker.store().type_node_links(declaration).is_none());
        assert!(checker.store().type_node_links(body).is_none());
    }
    let callable = checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        checker.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    for symbol in [exported, imported] {
        assert_eq!(
            checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            Some(callable),
        );
    }
    let signature = checker
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.parameters(), &[parameter_symbol]);
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    let returned = record.resolved_return_type().unwrap();
    let shape = checker.get_declared_type_of_symbol(shape_owner).unwrap();
    assert_eq!(returned, shape);
    let record = checker.store().type_payload(shape).unwrap();
    assert_eq!(record.symbol(), Some(shape_owner));
    assert!(matches!(record.data(), TypeData::Interface(_)));
    for annotation in [parameter_annotation, return_annotation] {
        assert_eq!(
            checker
                .store()
                .type_node_links(annotation)
                .unwrap()
                .resolved_type,
            Some(shape),
        );
    }
    assert_eq!(
        checker
            .store()
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .resolved_type,
        Some(shape),
    );
    let selected = checker
        .store()
        .signature_links(call)
        .unwrap()
        .resolved_signature
        .signature();
    assert_eq!(selected, Some(signature));
    assert_eq!(checker.get_type_at_location(call), Ok(shape));
    assert_signature_authority(
        &mut checker,
        signature,
        return_annotation,
        shape_alias,
        shape,
    );
    assert_eq!(checked(&checker, PRODUCER), producer_first);
    if !producer_first {
        assert!(checker.store().type_node_links(declaration).is_none());
        assert!(checker.store().type_node_links(body).is_none());
    }

    checker.check_source_file(PRODUCER).unwrap();
    checker.check_source_file(TYPES).unwrap();
    assert!(checked(&checker, PRODUCER));
    assert_eq!(checker.get_type_at_location(declaration), Ok(callable));
    assert_eq!(checker.get_type_at_location(body), Ok(shape));
    assert_eq!(
        checker.get_symbol_at_location(body),
        Ok(Some(parameter_symbol))
    );
    let import_links = checker
        .store()
        .alias_symbol_links(imported)
        .cloned()
        .unwrap();
    assert_eq!(import_links.immediate_target, Some(exported));
    assert_eq!(
        import_links.alias_target,
        AliasTargetState::Resolved(exported)
    );
    let type_links = checker
        .store()
        .alias_symbol_links(shape_alias)
        .cloned()
        .unwrap();
    assert_eq!(
        type_links.alias_target,
        AliasTargetState::Resolved(shape_owner)
    );
    let signature_state = format!("{:?}", checker.store().signature(signature).unwrap());
    let warm = counts(&checker);
    for _ in 0..2 {
        checker.recheck_source_file(CONSUMER).unwrap();
        checker.recheck_source_file(PRODUCER).unwrap();
        checker.recheck_source_file(TYPES).unwrap();
        assert_signature_authority(
            &mut checker,
            signature,
            return_annotation,
            shape_alias,
            shape,
        );
        assert_eq!(checker.get_type_at_location(declaration), Ok(callable));
        assert_eq!(checker.get_type_at_location(body), Ok(shape));
        assert_eq!(checker.get_type_at_location(call), Ok(shape));
        assert_eq!(checker.get_declared_type_of_symbol(shape_owner), Ok(shape));
        assert_eq!(
            checker
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature),
        );
        assert_eq!(
            format!("{:?}", checker.store().signature(signature).unwrap()),
            signature_state,
        );
        assert_eq!(
            checker.store().alias_symbol_links(imported),
            Some(&import_links)
        );
        assert_eq!(
            checker.store().alias_symbol_links(shape_alias),
            Some(&type_links)
        );
        assert_eq!(counts(&checker), warm);
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
fn importer_first_arrow_return_uses_signature_owned_interface_authority() {
    check_order(false);
}

#[test]
fn producer_first_arrow_return_keeps_signature_owned_interface_authority() {
    check_order(true);
}
