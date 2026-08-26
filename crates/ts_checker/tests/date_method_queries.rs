use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(4_350);
const SOURCE_FILE: FileId = FileId::new(4_351);
const LIBRARY: &str = concat!(
    "interface Date { toISOString(): string; format(options: DateOptions): string; ignored(); } ",
    "interface DateOptions { ignored(); } ",
    "interface DateConstructor { new(): Date; readonly prototype: Date; } ",
    "declare var Date: DateConstructor;",
);

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, default_library, module_state) in [
        (
            library,
            LIBRARY_FILE,
            "\"/lib/lib.es5.d.ts\"",
            true,
            CanonicalModuleState::Script,
        ),
        (
            source,
            SOURCE_FILE,
            "\"/project/input.d.ts\"",
            false,
            CanonicalModuleState::External,
        ),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    default_library,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (SOURCE_FILE, &source.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn method(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), LIBRARY_FILE, node),
                NodeRef::new(parsed.arena.id(), LIBRARY_FILE, method.name),
            ))
        })
        .unwrap()
}

fn date_reference(source: &ParseResult) -> (NodeRef, NodeRef) {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeReferenceNode(reference) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &source.arena.get(reference.type_name)?.data else {
                return None;
            };
            (name.text == "Date").then_some((
                NodeRef::new(source.arena.id(), SOURCE_FILE, node),
                NodeRef::new(source.arena.id(), SOURCE_FILE, reference.type_name),
            ))
        })
        .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    )
}

#[test]
fn date_annotation_source_query_accepts_the_authenticated_builtin_method() {
    let library = parse_source_file(concat!(
        "interface Date { toISOString(): string; } ",
        "interface DateConstructor { new(): Date; readonly prototype: Date; } ",
        "declare var Date: DateConstructor;",
    ));
    let source = parse_source_file("export declare const stamp: Date;");
    let mut context = context(&library, &source);
    let (reference, _) = date_reference(&source);
    let type_ = context.get_type_from_type_node(reference).unwrap();
    let (declaration, _) = method(&library, "toISOString");
    let selected = symbol(&context, declaration);
    let value = context
        .store()
        .value_symbol_links(selected)
        .unwrap()
        .resolved_type
        .unwrap();
    assert!(matches!(
        context.store().type_payload(value).unwrap().data(),
        TypeData::Object(_)
    ));
    let warm = counts(&context);
    assert_eq!(context.get_type_from_type_node(reference).unwrap(), type_);
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn date_annotation_symbol_and_type_queries_leave_methods_cold() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file("export declare const stamp: Date;");
    let mut context = context(&library, &source);
    let (reference, name) = date_reference(&source);
    let owner = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source("Date")
        .unwrap();
    let owner = context.store().get_merged_symbol(owner).unwrap();
    let cold = counts(&context);
    assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(owner));
    assert_eq!(counts(&context), cold);
    assert!(context.store().declared_type_links(owner).is_none());

    let type_ = context.get_type_at_location(name).unwrap();
    assert_eq!(context.get_type_at_location(reference).unwrap(), type_);
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type,
        Some(type_),
    );
    for method_name in ["toISOString", "format", "ignored"] {
        let (declaration, _) = method(&library, method_name);
        assert!(
            context
                .store()
                .value_symbol_links(symbol(&context, declaration))
                .is_none()
        );
    }
    let warm = counts(&context);
    assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(owner));
    assert_eq!(context.get_type_at_location(name).unwrap(), type_);
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn date_method_location_publishes_only_the_selected_callable() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file("export {};");
    let mut context = context(&library, &source);
    let (declaration, name) = method(&library, "toISOString");
    let selected = symbol(&context, declaration);
    let type_ = context.get_type_at_location(name).unwrap();
    assert_eq!(
        context.get_symbol_at_location(name).unwrap(),
        Some(selected)
    );
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(selected));
    let TypeData::Object(object) = record.data() else {
        panic!("the selected method has one callable object")
    };
    let signatures = object.structured.signatures.as_ref().unwrap();
    assert_eq!(signatures.len(), 1);
    assert_eq!(
        context
            .store()
            .signature(signatures[0])
            .unwrap()
            .resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().string_type),
    );
    for sibling in ["format", "ignored"] {
        let (sibling, _) = method(&library, sibling);
        assert!(
            context
                .store()
                .value_symbol_links(symbol(&context, sibling))
                .is_none()
        );
    }
    let warm = counts(&context);
    assert_eq!(context.get_type_at_location(declaration).unwrap(), type_);
    assert_eq!(context.get_type_at_location(name).unwrap(), type_);
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn date_method_parameter_references_do_not_expand_other_interfaces() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file("export {};");
    let mut context = context(&library, &source);
    let (_, name) = method(&library, "format");
    let type_ = context.get_type_at_location(name).unwrap();
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the selected method has a callable object")
    };
    let signature = context
        .store()
        .signature(object.structured.signatures.as_ref().unwrap()[0])
        .unwrap();
    let parameter = signature.parameters()[0];
    let parameter_type = context
        .store()
        .value_symbol_links(parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    let owner = context
        .store()
        .type_payload(parameter_type)
        .unwrap()
        .symbol()
        .unwrap();
    assert_eq!(
        context.store().symbol(owner).unwrap().name().as_utf8(),
        Some("DateOptions")
    );
    let ignored = context
        .store()
        .symbol(owner)
        .unwrap()
        .members()
        .and_then(|members| context.store().symbol_table(members))
        .unwrap()
        .get_source("ignored")
        .unwrap();
    assert!(context.store().value_symbol_links(ignored).is_none());
    let warm = counts(&context);
    assert_eq!(context.get_type_at_location(name).unwrap(), type_);
    assert_eq!(counts(&context), warm);
}

#[test]
fn date_annotation_symbol_query_preserves_a_local_type_binding() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file(concat!(
        "export interface Date { local(): number; ignored(); } ",
        "export declare const stamp: Date;",
    ));
    let mut context = context(&library, &source);
    let (_, name) = date_reference(&source);
    let declaration = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                source.arena.id(),
                SOURCE_FILE,
                node,
            ))
        })
        .unwrap();
    let local = symbol(&context, declaration);
    let before = counts(&context);
    assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(local));
    assert_eq!(counts(&context), before);
    let type_ = context.get_type_at_location(name).unwrap();
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(local)
    );
}

#[test]
fn date_method_query_does_not_recover_an_unsupported_selected_signature() {
    let library = parse_source_file(LIBRARY);
    let source = parse_source_file("export {};");
    let mut context = context(&library, &source);
    let (_, name) = method(&library, "ignored");
    let before = counts(&context);
    assert!(context.get_type_at_location(name).is_err());
    assert_eq!(counts(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn bundled_date_artifact_queries_leave_unrelated_library_methods_cold() {
    let library = parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts"));
    let source = parse_source_file("export declare const stamp: Date;");
    let mut context = context(&library, &source);
    let (reference, name) = date_reference(&source);
    let date = context.get_symbol_at_location(name).unwrap().unwrap();
    let type_ = context.get_type_at_location(reference).unwrap();
    assert_eq!(
        context.store().type_payload(type_).unwrap().symbol(),
        Some(date)
    );
    let (_, name) = method(&library, "toISOString");
    let value = context.get_type_at_location(name).unwrap();
    let (sibling, _) = method(&library, "toJSON");
    assert!(
        context
            .store()
            .value_symbol_links(symbol(&context, sibling))
            .is_none()
    );
    let warm = counts(&context);
    assert_eq!(context.get_type_at_location(name).unwrap(), value);
    assert_eq!(counts(&context), warm);
}
