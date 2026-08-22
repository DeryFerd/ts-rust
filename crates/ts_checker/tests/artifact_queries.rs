use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, artifact_queries::CanonicalArtifactQueryError,
};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn facts(path: &str, module_state: CanonicalModuleState) -> CanonicalSourceFileFacts {
    CanonicalSourceFileFacts::new(
        EscapedName::source(format!("\"{path}\"")),
        CanonicalSourceLanguage::TypeScript,
        false,
        module_state,
    )
}

fn single_file_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            facts("/project/input.ts", CanonicalModuleState::Script),
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

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn variable(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(declaration) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    node(parsed, file, id),
                    node(parsed, file, declaration.name),
                    node(parsed, file, declaration.initializer.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn declaration_symbol(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
) -> SemanticSymbolId {
    let bound = context.file(declaration.file).unwrap().1;
    context
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap()
}

fn source_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    let source = context.source_file(file).unwrap();
    context
        .store()
        .source_file_links(source)
        .is_some_and(|links| links.type_checked)
}

#[test]
#[allow(clippy::too_many_lines)] // One end-to-end case proves shared type and symbol identity.
fn location_queries_check_once_and_reuse_exact_value_and_property_identities() {
    let parsed = parse_source_file(concat!(
        "const value: number = 1;\n",
        "const object = { value: value };\n",
        "const copy = object.value;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_000);
    let mut context = single_file_context(&parsed, file);
    let (value_declaration, value_name, value_initializer) = variable(&parsed, file, "value");
    let (object_declaration, object_name, object_initializer) = variable(&parsed, file, "object");
    let (copy_declaration, copy_name, access) = variable(&parsed, file, "copy");
    let value_symbol = declaration_symbol(&context, value_declaration);
    let object_symbol = declaration_symbol(&context, object_declaration);
    let copy_symbol = declaration_symbol(&context, copy_declaration);
    let NodeData::PropertyAccessExpression(access_data) =
        &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("copy must read an object property")
    };
    let access_name = node(&parsed, file, access_data.name);
    let access_receiver = node(&parsed, file, access_data.expression);
    let NodeData::ObjectLiteralExpression(object) =
        &parsed.arena.get(object_initializer.node).unwrap().data
    else {
        panic!("object initializer must be an object literal")
    };
    let property = node(&parsed, file, object.properties.nodes[0]);
    let NodeData::PropertyAssignment(property_data) =
        &parsed.arena.get(property.node).unwrap().data
    else {
        panic!("object must contain one property assignment")
    };
    let property_name = node(&parsed, file, property_data.name);

    assert!(!source_checked(&context, file));
    let value_type = context.get_type_at_location(value_name).unwrap();
    assert!(source_checked(&context, file));
    assert_eq!(
        value_type,
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    assert_eq!(
        context.get_symbol_at_location(value_name).unwrap(),
        Some(value_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(value_declaration).unwrap(),
        Some(value_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(object_name).unwrap(),
        Some(object_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(copy_name).unwrap(),
        Some(copy_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(access_receiver).unwrap(),
        Some(object_symbol)
    );

    let property_symbol = declaration_symbol(&context, property);
    let access_symbol = context
        .store()
        .symbol_node_links(access)
        .and_then(|links| links.resolved_symbol)
        .unwrap();
    assert_ne!(access_symbol, property_symbol);
    assert_eq!(
        context
            .store()
            .value_symbol_links(access_symbol)
            .and_then(|links| links.target),
        Some(property_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(property_name).unwrap(),
        Some(property_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(access).unwrap(),
        Some(access_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(access_name).unwrap(),
        Some(access_symbol)
    );
    assert_eq!(
        context.get_type_at_location(property_name).unwrap(),
        value_type
    );
    assert_eq!(
        context.get_type_at_location(access_name).unwrap(),
        value_type
    );
    assert_eq!(context.get_type_at_location(access).unwrap(), value_type);
    assert_eq!(
        context.get_type_at_location(copy_declaration).unwrap(),
        value_type
    );
    assert_eq!(
        context.get_symbol_at_location(value_initializer).unwrap(),
        None
    );
    let literal_type = context.get_type_at_location(value_initializer).unwrap();
    assert_eq!(context.type_to_string(literal_type).unwrap(), "1");
    assert_eq!(context.symbol_to_string(property_symbol).unwrap(), "value");
    assert_eq!(
        context.get_symbol_declarations(property_symbol).unwrap(),
        &[property]
    );
    assert_eq!(
        context.get_symbol_declarations(access_symbol).unwrap(),
        &[property]
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.diagnostics().len(),
    );
    for _ in 0..3 {
        assert_eq!(
            context.get_type_at_location(value_name).unwrap(),
            value_type
        );
        assert_eq!(
            context.get_symbol_at_location(access_name).unwrap(),
            Some(access_symbol)
        );
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.diagnostics().len(),
        ),
        warm
    );
}

#[test]
fn location_queries_resolve_type_reference_names_without_replacing_alias_symbols() {
    let parsed = parse_source_file(concat!(
        "type Label = string;\n",
        "const value: Label = 'ready';\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_001);
    let mut context = single_file_context(&parsed, file);
    let (alias, alias_name) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            Some((node(&parsed, file, id), node(&parsed, file, alias.name)))
        })
        .unwrap();
    let alias_symbol = declaration_symbol(&context, alias);
    let (value, _, _) = variable(&parsed, file, "value");
    let NodeData::VariableDeclaration(declaration) = &parsed.arena.get(value.node).unwrap().data
    else {
        unreachable!("helper selected a variable")
    };
    let reference = node(&parsed, file, declaration.type_.unwrap());
    let NodeData::TypeReferenceNode(reference_data) =
        &parsed.arena.get(reference.node).unwrap().data
    else {
        panic!("fixture annotation must be a type reference")
    };
    let reference_name = node(&parsed, file, reference_data.type_name);

    let string_type = context.get_type_at_location(reference_name).unwrap();
    assert_eq!(
        string_type,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_eq!(
        context.get_symbol_at_location(reference_name).unwrap(),
        Some(alias_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(reference).unwrap(),
        Some(alias_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(alias_name).unwrap(),
        Some(alias_symbol)
    );
    assert_eq!(
        context.get_type_at_location(alias_name).unwrap(),
        string_type
    );
    assert_eq!(
        context.get_symbol_declarations(alias_symbol).unwrap(),
        &[alias]
    );
}

#[test]
fn imported_alias_names_keep_alias_identity_and_original_names_use_the_target() {
    let importer = parse_source_file(concat!(
        "import { value as local } from './target';\n",
        "const copy: number = local;\n",
    ));
    let target = parse_source_file("export const value: number = 1;\n");
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
    let importer_file = FileId::new(4_002);
    let target_file = FileId::new(4_003);
    let (specifier, original_name, local_name) = importer
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ImportSpecifier(specifier) = &record.data else {
                return None;
            };
            Some((
                node(&importer, importer_file, id),
                node(&importer, importer_file, specifier.property_name.unwrap()),
                node(&importer, importer_file, specifier.name),
            ))
        })
        .unwrap();
    let module_name = importer
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(node(&importer, importer_file, import.module_specifier))
        })
        .unwrap();

    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in [
        (importer_file, &importer, "/project/importer.ts"),
        (target_file, &target, "/project/target.ts"),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                facts(path, CanonicalModuleState::External),
            )
            .unwrap();
    }
    for (file, parsed) in [(importer_file, &importer), (target_file, &target)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [
            (importer_file, &importer.arena),
            (target_file, &target.arena),
        ]
        .into_iter()
        .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            module_name,
            CanonicalResolvedModuleInput::new(
                target_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap();
    let alias = declaration_symbol(&context, specifier);
    let (target_declaration, _, _) = variable(&target, target_file, "value");
    let target_symbol = declaration_symbol(&context, target_declaration);

    assert_eq!(
        context.get_symbol_at_location(local_name).unwrap(),
        Some(alias)
    );
    assert_eq!(
        context.get_symbol_at_location(original_name).unwrap(),
        Some(target_symbol)
    );
    assert_eq!(
        context.get_type_at_location(local_name).unwrap(),
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    assert_eq!(
        context.get_symbol_declarations(alias).unwrap(),
        &[specifier]
    );
    assert_eq!(
        context.get_symbol_declarations(target_symbol).unwrap(),
        &[target_declaration]
    );
}

#[test]
fn location_queries_reject_foreign_nodes_symbols_and_nonsemantic_nodes() {
    let first = parse_source_file("const value: number = 1;\n");
    let second = parse_source_file("const value: number = 1;\n");
    let file = FileId::new(4_004);
    let mut context = single_file_context(&first, file);
    let mut foreign_context = single_file_context(&second, file);
    let (_, first_name, _) = variable(&first, file, "value");
    let (foreign_declaration, foreign_name, _) = variable(&second, file, "value");
    let foreign_symbol = declaration_symbol(&foreign_context, foreign_declaration);

    assert_eq!(
        context.get_type_at_location(foreign_name),
        Err(CanonicalArtifactQueryError::ForeignNode(foreign_name))
    );
    assert_eq!(
        context.get_symbol_at_location(foreign_name),
        Err(CanonicalArtifactQueryError::ForeignNode(foreign_name))
    );
    assert_eq!(
        context.get_symbol_declarations(foreign_symbol),
        Err(CanonicalArtifactQueryError::ForeignSymbol(foreign_symbol))
    );
    assert_eq!(
        context.symbol_to_string(foreign_symbol),
        Err(CanonicalArtifactQueryError::ForeignSymbol(foreign_symbol))
    );

    let missing = NodeRef::new(first.arena.id(), FileId::new(4_999), first_name.node);
    assert_eq!(
        context.get_type_at_location(missing),
        Err(CanonicalArtifactQueryError::MissingFile(missing.file))
    );
    let root = node(&first, file, first.source_file);
    assert_eq!(
        context.get_type_at_location(root),
        Err(CanonicalArtifactQueryError::UnsupportedNode {
            node: root,
            kind: SyntaxKind::SourceFile,
        })
    );
    assert_eq!(
        context.get_symbol_at_location(first_name).unwrap(),
        Some(declaration_symbol(
            &context,
            variable(&first, file, "value").0
        ))
    );
    assert_eq!(
        foreign_context
            .get_symbol_at_location(foreign_name)
            .unwrap(),
        Some(foreign_symbol)
    );
}

#[test]
fn class_names_constructor_reads_and_member_names_preserve_their_distinct_types() {
    let parsed = parse_source_file(concat!(
        "class Model { value!: string; }\n",
        "const model = new Model();\n",
        "const value = model.value;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_005);
    let mut context = single_file_context(&parsed, file);
    let (class, class_name) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            Some((
                node(&parsed, file, id),
                node(&parsed, file, class.name.unwrap()),
            ))
        })
        .unwrap();
    let class_symbol = declaration_symbol(&context, class);
    let (_, _, construction) = variable(&parsed, file, "model");
    let NodeData::NewExpression(new_expression) =
        &parsed.arena.get(construction.node).unwrap().data
    else {
        panic!("model initializer must construct the class")
    };
    let constructor = node(&parsed, file, new_expression.expression);
    let (_, _, property_access) = variable(&parsed, file, "value");
    let NodeData::PropertyAccessExpression(access) =
        &parsed.arena.get(property_access.node).unwrap().data
    else {
        panic!("value initializer must read a class property")
    };
    let access_name = node(&parsed, file, access.name);

    let class_value_type = context.get_type_at_location(class_name).unwrap();
    let members = context.get_nongeneric_class_members(class_symbol).unwrap();
    assert_eq!(class_value_type, members.shells().value_type());
    assert_eq!(
        context.get_type_at_location(constructor).unwrap(),
        members.shells().value_type()
    );
    assert_eq!(
        context.get_type_at_location(construction).unwrap(),
        members.shells().instance_type()
    );
    assert_eq!(
        context.get_symbol_at_location(class_name).unwrap(),
        Some(class_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(constructor).unwrap(),
        Some(class_symbol)
    );
    assert_eq!(
        context.get_symbol_at_location(access_name).unwrap(),
        Some(members.instance_properties()[0])
    );
    assert_eq!(
        context.get_type_at_location(access_name).unwrap(),
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
}

#[test]
fn declaration_file_queries_resolve_annotations_without_forcing_source_checks() {
    let parsed = parse_source_file(concat!(
        "declare const value: number;\n",
        "interface Shape { item: string; }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_006);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/input.d.ts\""),
                CanonicalSourceLanguage::TypeScript,
                true,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let (declaration, name) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            Some((node(&parsed, file, id), node(&parsed, file, variable.name)))
        })
        .unwrap();
    let symbol = declaration_symbol(&context, declaration);
    let (property, property_name) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                return None;
            };
            Some((node(&parsed, file, id), node(&parsed, file, property.name)))
        })
        .unwrap();
    let property_symbol = declaration_symbol(&context, property);

    assert!(!source_checked(&context, file));
    assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
    assert_eq!(
        context.get_type_at_location(name).unwrap(),
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    assert_eq!(
        context.get_symbol_at_location(property_name).unwrap(),
        Some(property_symbol)
    );
    assert_eq!(
        context.get_type_at_location(property_name).unwrap(),
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert!(!source_checked(&context, file));
}

#[test]
fn jsx_wrappers_hide_cached_symbols_without_changing_attribute_symbols() {
    let parsed = parse_jsx_source_file(concat!(
        "const single = <div className=\"one\" />;\n",
        "const paired = <div className=\"two\"></div>;\n",
        "const fragment = <><div /></>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_007);
    let mut context = single_file_context(&parsed, file);
    context.check_source_file(file).unwrap();

    let wrappers = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            matches!(
                record.kind,
                SyntaxKind::JsxElement
                    | SyntaxKind::JsxOpeningElement
                    | SyntaxKind::JsxClosingElement
                    | SyntaxKind::JsxSelfClosingElement
                    | SyntaxKind::JsxFragment
                    | SyntaxKind::JsxOpeningFragment
                    | SyntaxKind::JsxClosingFragment
            )
            .then_some((node(&parsed, file, id), record.kind))
        })
        .collect::<Vec<_>>();
    assert_eq!(wrappers.len(), 8);

    let unknown = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .unknown_symbol;
    let cached = wrappers
        .iter()
        .map(|(wrapper, kind)| {
            let symbol = context
                .store()
                .symbol_node_links(*wrapper)
                .and_then(|links| links.resolved_symbol);
            if matches!(
                kind,
                SyntaxKind::JsxOpeningElement
                    | SyntaxKind::JsxClosingElement
                    | SyntaxKind::JsxSelfClosingElement
            ) {
                assert_eq!(symbol, Some(unknown));
            }
            (*wrapper, *kind, symbol)
        })
        .collect::<Vec<_>>();

    for (wrapper, kind, _) in &cached {
        assert_eq!(
            context.get_symbol_at_location(*wrapper).unwrap(),
            None,
            "public JSX symbol query exposed {kind:?}"
        );
    }

    for (wrapper, _, expected) in &cached {
        assert_eq!(
            context
                .store()
                .symbol_node_links(*wrapper)
                .and_then(|links| links.resolved_symbol),
            *expected
        );
    }

    let attributes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::JsxAttribute(attribute) = &record.data else {
                return None;
            };
            Some((node(&parsed, file, id), node(&parsed, file, attribute.name)))
        })
        .collect::<Vec<_>>();
    assert_eq!(attributes.len(), 2);
    for (attribute, name) in attributes {
        let symbol = declaration_symbol(&context, attribute);
        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
    }
}
