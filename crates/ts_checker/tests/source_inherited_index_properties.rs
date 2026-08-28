use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, IntrinsicBootstrapOptions,
    SourceCheckError, TypeData, TypeId, TypeNodeUnavailable,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: &str = concat!(
    "interface IArguments {} interface Object {} interface Function {} ",
    "interface String {} interface Number {} interface Boolean {} interface RegExp {} ",
    "interface Array<T> { length: number; [index: number]: T; } ",
    "interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; } ",
    "interface ThisType<T> {}",
);

fn parsed(text: &str) -> ParseResult {
    let parsed = parse_source_file(text);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed
}

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
    file: FileId,
) -> CanonicalCheckerContext<'arena> {
    let files = [(FileId::new(32_100), library), (file, source)];
    let mut binder = CanonicalBinder::new();
    for (index, &(file, parsed)) in files.iter().enumerate() {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"/inherited-index-{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    index == 0,
                    index == 0,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for &(file, parsed) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed)| (*file, &parsed.arena))
            .collect(),
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

fn derived_node(source: &ParseResult, file: FileId) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                source.arena.id(),
                file,
                node,
            ))
        })
        .unwrap()
}

fn result_type(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    file: FileId,
) -> TypeId {
    let declaration = source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &source.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "result").then_some(NodeRef::new(source.arena.id(), file, node))
        })
        .unwrap();
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let symbol = context.store().get_merged_symbol(symbol).unwrap();
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_inherited_index_identity(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    file: FileId,
) {
    let symbol = context
        .file(file)
        .unwrap()
        .1
        .symbol(derived_node(source, file))
        .unwrap();
    let symbol = context.store().get_merged_symbol(symbol).unwrap();
    let type_ = context
        .store()
        .declared_type_links(symbol)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(derived) = context.store().type_payload(type_).unwrap().data() else {
        panic!("Derived must retain its interface identity")
    };
    assert!(derived.declared_members_resolved);
    assert!(derived.declared_index_infos.is_none());
    let [base] = derived.resolved_base_types.as_deref().unwrap() else {
        panic!("Derived must retain one base")
    };
    let indexes = derived
        .reference
        .object
        .structured
        .index_infos
        .as_deref()
        .unwrap();
    assert_eq!(indexes.len(), 1);
    let base_members = match context.store().type_payload(*base).unwrap().data() {
        TypeData::TypeReference(base) => &base.object.structured,
        TypeData::Interface(base) => &base.reference.object.structured,
        _ => panic!("the array base must retain its reference payload"),
    };
    assert_eq!(base_members.index_infos.as_deref(), Some(indexes));
    let index = context.store().index_info(indexes[0]).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(index.key_type(), number);
    assert_eq!(index.value_type(), number);
    assert!(index.is_readonly());
}

#[test]
fn inherited_numeric_indexes_preserve_unconstrained_own_properties_on_source_replay() {
    let library = parsed(LIBRARY);
    for (property, access, expected) in [
        ("label: string", "values.label", "string"),
        ("readonly label: string", "values.label", "string"),
        ("label?: string", "values.label", "string | undefined"),
        ("\"01\": string", "values[\"01\"]", "string"),
        ("\"-0\": string", "values[\"-0\"]", "string"),
        ("\"1.0\": string", "values[\"1.0\"]", "string"),
        ("0: number", "values[0]", "number"),
        ("\"-1\": number", "values[-1]", "number"),
    ] {
        let source = parsed(&format!(
            "interface Derived extends ReadonlyArray<number> {{ {property}; }} \
             declare const values: Derived; const result = {access};",
        ));
        let file = FileId::new(32_101);
        let mut context = context(&library, &source, file);
        context.check_source_file(file).unwrap_or_else(|error| {
            let symbol = context
                .file(file)
                .unwrap()
                .1
                .symbol(derived_node(&source, file))
                .unwrap();
            let symbol = context.store().get_merged_symbol(symbol).unwrap();
            let derived = context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type);
            panic!("{property}: {error:?}; Derived type: {derived:?}");
        });
        assert!(
            context.diagnostics().is_empty(),
            "{property}: {:?}",
            context.diagnostics()
        );
        let result = result_type(&context, &source, file);
        assert_eq!(
            context.type_to_string(result).unwrap(),
            expected,
            "{property}"
        );
        assert_inherited_index_identity(&context, &source, file);
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().index_info_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                context.diagnostics().clone(),
                result_type(context, &source, file),
            )
        };
        let before = snapshot(&context);
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(&context), before, "{property}");
        assert_inherited_index_identity(&context, &source, file);
    }
}

#[test]
fn inherited_numeric_indexes_reject_incompatible_numeric_names_without_members() {
    let library = parsed(LIBRARY);
    for property in [
        "0: string",
        "\"-1\": string",
        "\"1.5\": string",
        "\"NaN\": string",
        "\"Infinity\": string",
        "0?: number",
    ] {
        let source = parsed(&format!(
            "interface Derived extends ReadonlyArray<number> {{ {property}; }} \
             declare const values: Derived;",
        ));
        let file = FileId::new(32_102);
        let mut context = context(&library, &source, file);
        let expected = SourceCheckError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::UnsupportedSyntax {
                node: derived_node(&source, file),
                kind: SyntaxKind::InterfaceDeclaration,
            },
        ));
        assert_eq!(context.check_source_file(file), Err(expected), "{property}");
        let symbol = context
            .file(file)
            .unwrap()
            .1
            .symbol(derived_node(&source, file))
            .unwrap();
        let symbol = context.store().get_merged_symbol(symbol).unwrap();
        if let Some(type_) = context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
        {
            let TypeData::Interface(derived) = context.store().type_payload(type_).unwrap().data()
            else {
                panic!("Derived must retain its interface identity")
            };
            assert!(!derived.declared_members_resolved, "{property}");
            assert!(
                derived.reference.object.structured.properties.is_none(),
                "{property}"
            );
            assert!(
                derived.reference.object.structured.index_infos.is_none(),
                "{property}"
            );
        }
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().index_info_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                context.diagnostics().clone(),
            )
        };
        let before = snapshot(&context);
        assert_eq!(context.check_source_file(file), Err(expected), "{property}");
        assert_eq!(snapshot(&context), before, "{property}");
    }
}
