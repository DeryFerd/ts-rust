use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeError, TypeData, TypeId, TypeNodeUnavailable,
    TypeRecord, ValueSymbolLinks, type_records::IntersectionTypeData, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const SUPPORTED_SOURCE: &str = concat!(
    "interface Payload { leaf: string }\n",
    "interface PayloadShape { leaf: string }\n",
    "type PayloadAlias = Payload;\n",
    "interface Left {\n",
    "  maybe?: PayloadAlias;\n",
    "  node: PayloadAlias;\n",
    "  inline: { deep: number };\n",
    "  value?: string;\n",
    "  bothOptional?: number;\n",
    "  readonly locked: number;\n",
    "  readonly mixed: string;\n",
    "}\n",
    "type Right = {\n",
    "  value: string;\n",
    "  bothOptional?: number;\n",
    "  readonly locked: number;\n",
    "  mixed: string;\n",
    "  required: boolean;\n",
    "};\n",
    "type Combined = Left & Right;\n",
    "type Shape = {\n",
    "  maybe?: PayloadShape;\n",
    "  node: PayloadShape;\n",
    "  inline: { deep: number };\n",
    "  value: string;\n",
    "  bothOptional?: number;\n",
    "  readonly locked: number;\n",
    "  mixed: string;\n",
    "  required: boolean;\n",
    "};\n",
    "type WeakPresent = { maybe?: PayloadShape };\n",
    "type WeakAbsent = { absent?: string };\n",
    "declare const combined: Combined;\n",
    "const readNode = combined.node;\n",
    "const readInline = combined.inline;\n",
    "const readValue = combined.value;\n",
    "const readRequired = combined.required;\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/intersection-optional-properties.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
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

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(declaration) => declaration.name,
                NodeData::InterfaceDeclaration(declaration) => declaration.name,
                NodeData::VariableDeclaration(declaration) => declaration.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    kind: SyntaxKind,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = declaration(parsed, file, kind, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn alias_rhs(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = declaration(parsed, file, SyntaxKind::TypeAliasDeclaration, expected);
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(declaration.arena, declaration.file, alias.type_)
}

fn declared_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .or_else(|| {
            context
                .store()
                .type_alias_links(symbol)
                .and_then(|links| links.declared_type)
        })
        .unwrap_or_else(|| panic!("missing declared type for {symbol:?}"))
}

fn structured_properties(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> Vec<SemanticSymbolId> {
    match context.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(interface) => interface
            .reference
            .object
            .structured
            .properties
            .clone()
            .unwrap_or_default(),
        TypeData::Object(object) => object.structured.properties.clone().unwrap_or_default(),
        data => panic!("expected a declared property object, got {data:?}"),
    }
}

fn intersection_data<'a>(
    context: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a IntersectionTypeData {
    let Some(TypeData::Intersection(data)) =
        context.store().type_payload(type_).map(TypeRecord::data)
    else {
        panic!("expected an intersection type, got {type_:?}")
    };
    data
}

fn property_by_name(
    context: &CanonicalCheckerContext<'_>,
    properties: &[SemanticSymbolId],
    name: &str,
) -> SemanticSymbolId {
    properties
        .iter()
        .copied()
        .find(|property| {
            context
                .store()
                .symbol(*property)
                .is_some_and(|symbol| symbol.name().as_utf8() == Some(name))
        })
        .unwrap_or_else(|| panic!("missing property {name}"))
}

fn variable_type(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> TypeId {
    let symbol = symbol(
        parsed,
        file,
        context,
        SyntaxKind::VariableDeclaration,
        expected,
    );
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing variable type for {expected}"))
}

#[test]
#[allow(clippy::too_many_lines)]
fn optional_and_composite_intersection_properties_preserve_pinned_merge_semantics() {
    let parsed = parse_source_file(SUPPORTED_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_001);
    let mut context = context(&parsed, file);

    let combined_rhs = alias_rhs(&parsed, file, "Combined");
    let combined = context.get_type_from_type_node(combined_rhs).unwrap();
    let cold = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    assert_eq!(context.get_type_from_type_node(combined_rhs), Ok(combined));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        cold,
    );

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let alias_type = |name: &str| {
        let alias = symbol(
            &parsed,
            file,
            &context,
            SyntaxKind::TypeAliasDeclaration,
            name,
        );
        declared_type(&context, alias)
    };
    let payload = declared_type(
        &context,
        symbol(
            &parsed,
            file,
            &context,
            SyntaxKind::InterfaceDeclaration,
            "Payload",
        ),
    );
    let left = declared_type(
        &context,
        symbol(
            &parsed,
            file,
            &context,
            SyntaxKind::InterfaceDeclaration,
            "Left",
        ),
    );
    let right = alias_type("Right");
    let shape = alias_type("Shape");
    let weak_present = alias_type("WeakPresent");
    let weak_absent = alias_type("WeakAbsent");
    assert_eq!(combined, alias_type("Combined"));

    let properties = intersection_data(&context, combined)
        .intersection
        .resolved_properties
        .as_deref()
        .expect("intersection properties are eager");
    let names = properties
        .iter()
        .map(|property| {
            context
                .store()
                .symbol(*property)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        [
            "maybe",
            "node",
            "inline",
            "value",
            "bothOptional",
            "locked",
            "mixed",
            "required"
        ]
    );

    let left_properties = structured_properties(&context, left);
    let right_properties = structured_properties(&context, right);
    let maybe = property_by_name(&context, properties, "maybe");
    let node = property_by_name(&context, properties, "node");
    let inline = property_by_name(&context, properties, "inline");
    let required = property_by_name(&context, properties, "required");
    assert_eq!(maybe, property_by_name(&context, &left_properties, "maybe"));
    assert_eq!(node, property_by_name(&context, &left_properties, "node"));
    assert_eq!(
        inline,
        property_by_name(&context, &left_properties, "inline")
    );
    assert_eq!(
        required,
        property_by_name(&context, &right_properties, "required")
    );
    assert!(
        context
            .store()
            .symbol(maybe)
            .unwrap()
            .flags()
            .contains(SymbolFlags::OPTIONAL)
    );
    assert_eq!(
        context.store().value_symbol_links(maybe),
        Some(&ValueSymbolLinks {
            resolved_type: Some(payload),
            ..ValueSymbolLinks::default()
        }),
    );

    let value = property_by_name(&context, properties, "value");
    let both_optional = property_by_name(&context, properties, "bothOptional");
    let locked = property_by_name(&context, properties, "locked");
    let mixed = property_by_name(&context, properties, "mixed");
    for property in [value, locked, mixed] {
        let record = context.store().symbol(property).unwrap();
        assert_eq!(
            record.flags(),
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
        );
        assert!(
            record
                .check_flags()
                .contains(CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC)
        );
    }
    assert!(
        !context
            .store()
            .symbol(value)
            .unwrap()
            .flags()
            .contains(SymbolFlags::OPTIONAL),
        "required & optional is required for intersections"
    );
    assert_eq!(
        context.store().symbol(both_optional).unwrap().flags(),
        SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT,
    );
    assert!(
        context
            .store()
            .symbol(both_optional)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC)
    );
    assert!(
        context
            .store()
            .symbol(locked)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY)
    );
    assert!(
        !context
            .store()
            .symbol(mixed)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY),
        "readonly is retained only when every contributor is readonly"
    );

    for (name, synthetic) in [
        ("value", value),
        ("bothOptional", both_optional),
        ("locked", locked),
        ("mixed", mixed),
    ] {
        let sources = [
            property_by_name(&context, &left_properties, name),
            property_by_name(&context, &right_properties, name),
        ];
        let expected = sources
            .into_iter()
            .flat_map(|source| {
                context
                    .store()
                    .symbol(source)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .iter()
                    .copied()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            context.store().symbol(synthetic).unwrap().declarations(),
            Some(expected.as_slice()),
            "{name}",
        );
    }

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(variable_type(&parsed, file, &context, "readNode"), payload);
    assert_eq!(
        variable_type(&parsed, file, &context, "readInline"),
        context
            .store()
            .value_symbol_links(inline)
            .and_then(|links| links.resolved_type)
            .unwrap()
    );
    assert_eq!(
        variable_type(&parsed, file, &context, "readValue"),
        bootstrap.string_type
    );
    assert_eq!(
        variable_type(&parsed, file, &context, "readRequired"),
        bootstrap.boolean_type
    );

    assert_eq!(context.is_type_assignable_to(combined, shape), Ok(true));
    assert_eq!(context.is_type_assignable_to(shape, combined), Ok(true));
    assert_eq!(
        context.is_type_assignable_to(combined, weak_present),
        Ok(true)
    );
    assert_eq!(
        context.is_type_assignable_to(combined, weak_absent),
        Ok(false)
    );
    let warm_relations = context.store().relation_state_snapshot();
    for _ in 0..2 {
        assert_eq!(context.is_type_assignable_to(combined, shape), Ok(true));
        assert_eq!(context.is_type_assignable_to(shape, combined), Ok(true));
        assert_eq!(
            context.is_type_assignable_to(combined, weak_present),
            Ok(true)
        );
        assert_eq!(
            context.is_type_assignable_to(combined, weak_absent),
            Ok(false)
        );
    }
    assert_eq!(context.store().relation_state_snapshot(), warm_relations);

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    context.recheck_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        warm,
    );
}

#[test]
fn optional_never_discriminants_do_not_reduce_their_intersection() {
    let parsed = parse_source_file(concat!(
        "type OptionalKind = { k?: \"a\" } & { k?: \"b\" };\n",
        "type RequiredKind = { k: \"a\" } & { k: \"b\" };\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_002);
    let mut context = context(&parsed, file);
    let optional_rhs = alias_rhs(&parsed, file, "OptionalKind");
    let required_rhs = alias_rhs(&parsed, file, "RequiredKind");
    let optional = context.get_type_from_type_node(optional_rhs).unwrap();
    let required = context.get_type_from_type_node(required_rhs).unwrap();

    let optional_record = context.store().type_payload(optional).unwrap();
    assert!(matches!(optional_record.data(), TypeData::Intersection(_)));
    assert!(
        optional_record
            .object_flags()
            .contains(ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED)
    );
    assert!(
        !optional_record
            .object_flags()
            .contains(ObjectFlags::IS_NEVER_INTERSECTION)
    );
    let optional_property = property_by_name(
        &context,
        intersection_data(&context, optional)
            .intersection
            .resolved_properties
            .as_deref()
            .unwrap(),
        "k",
    );
    assert!(
        context
            .store()
            .symbol(optional_property)
            .unwrap()
            .flags()
            .contains(SymbolFlags::OPTIONAL)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(optional_property)
            .and_then(|links| links.resolved_type),
        context
            .store()
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.never_type),
    );

    let required_record = context.store().type_payload(required).unwrap();
    assert!(matches!(required_record.data(), TypeData::Intersection(_)));
    assert!(required_record.object_flags().contains(
        ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED | ObjectFlags::IS_NEVER_INTERSECTION
    ));

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    assert_eq!(context.get_type_from_type_node(optional_rhs), Ok(optional));
    assert_eq!(context.get_type_from_type_node(required_rhs), Ok(required));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        warm,
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One graph compares successful and rejected composite merges.
fn duplicate_composite_rejection_is_atomic_and_success_cannot_mask_boundaries() {
    let source = concat!(
        "type NestedOne = { leaf: string };\n",
        "type NestedTwo = { leaf: string };\n",
        "type GoodLeft = { value: NestedOne };\n",
        "type GoodRight = { value: NestedOne };\n",
        "type BadLeft = { value: NestedOne };\n",
        "type BadRight = { value: NestedTwo };\n",
        "type Good = GoodLeft & GoodRight;\n",
        "type Bad = BadLeft & BadRight;\n",
        "type GenericBad<T> = GoodLeft & GoodRight;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_003);
    let mut context = context(&parsed, file);

    for name in [
        "NestedOne",
        "NestedTwo",
        "GoodLeft",
        "GoodRight",
        "BadLeft",
        "BadRight",
    ] {
        context
            .get_type_from_type_node(alias_rhs(&parsed, file, name))
            .unwrap();
    }
    let good_rhs = alias_rhs(&parsed, file, "Good");
    let good = context.get_type_from_type_node(good_rhs).unwrap();
    assert_eq!(context.get_type_from_type_node(good_rhs), Ok(good));

    let bad_rhs = alias_rhs(&parsed, file, "Bad");
    let NodeData::IntersectionTypeNode(bad_node) = &parsed.arena.get(bad_rhs.node).unwrap().data
    else {
        unreachable!()
    };
    for constituent in &bad_node.types.nodes {
        context
            .get_type_from_type_node(NodeRef::new(bad_rhs.arena, bad_rhs.file, *constituent))
            .unwrap();
    }
    let before_bad = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    let bad_symbol = symbol(
        &parsed,
        file,
        &context,
        SyntaxKind::TypeAliasDeclaration,
        "Bad",
    );
    assert!(
        context
            .store()
            .type_node_links(bad_rhs)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    assert!(
        context
            .store()
            .type_alias_links(bad_symbol)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    let bad_error = context.get_type_from_type_node(bad_rhs).unwrap_err();
    assert!(matches!(
        bad_error,
        DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::UnsupportedIntersectionPropertyType(_)
        )
    ));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        before_bad,
    );
    assert!(
        context
            .store()
            .type_node_links(bad_rhs)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    assert!(
        context
            .store()
            .type_alias_links(bad_symbol)
            .and_then(|links| links.declared_type)
            .is_none()
    );
    assert_eq!(context.get_type_from_type_node(bad_rhs), Err(bad_error));

    let generic_rhs = alias_rhs(&parsed, file, "GenericBad");
    let generic_error = context.get_type_from_type_node(generic_rhs).unwrap_err();
    assert!(matches!(
        generic_error,
        DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::UnsupportedIntersectionConstituent(_)
        )
    ));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        before_bad,
    );
    assert_eq!(
        context.get_type_from_type_node(generic_rhs),
        Err(generic_error),
    );
}

#[test]
fn recursive_property_adapter_keeps_unsupported_surfaces_prepublication() {
    let cases = [
        (
            "type Bad = ({ a: string } | { b: number }) & { other: boolean };",
            "union distribution",
        ),
        (
            "type Bad = { call: () => string } & { other: boolean };",
            "callable property",
        ),
        (
            "type Bad = { items: string[] } & { other: boolean };",
            "array property",
        ),
        (
            "type A = { a: string }; type B = { b: number }; type Bad = { nested: A & B } & { other: boolean };",
            "nested intersection property",
        ),
        (
            "interface Box<T> { value: T } type Bad = { box: Box<string> } & { other: boolean };",
            "generic interface property",
        ),
        (
            "type Box<T> = { value: T }; type Bad = { box: Box<string> } & { other: boolean };",
            "generic alias property",
        ),
        (
            "class Model { value: string } type Bad = { model: Model } & { other: boolean };",
            "class property",
        ),
        (
            "interface Node { next?: Node } type Bad = { node: Node } & { other: boolean };",
            "recursive property graph",
        ),
        (
            "interface Base { base: string } interface Derived extends Base { own: number } type Bad = Derived & { other: boolean };",
            "heritage constituent",
        ),
        (
            "type Bad = { [key: string]: number } & { other: boolean };",
            "index constituent",
        ),
        (
            "type Bad = { new (): { value: string } } & { other: boolean };",
            "construct constituent",
        ),
    ];

    for (index, (source, label)) in cases.into_iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{label}: {:?}",
            parsed.diagnostics
        );
        let file = FileId::new(2_020 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let rhs = alias_rhs(&parsed, file, "Bad");
        let before = (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        );
        let first = context.get_type_from_type_node(rhs).unwrap_err();
        assert!(
            matches!(first, DeclaredTypeError::TypeNodeUnavailable(_)),
            "{label}: {first:?}",
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().type_alias_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            before,
            "{label}",
        );
        assert_eq!(context.get_type_from_type_node(rhs), Err(first), "{label}");
    }
}

#[test]
fn a_warm_imported_property_surface_cannot_mask_the_local_only_boundary() {
    let importer = parse_source_file(concat!(
        "import type { Remote } from './target';\n",
        "type Bad = { value: Remote } & { other: string };\n",
    ));
    let target = parse_source_file("export interface Remote { value: string }\n");
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
    let importer_file = FileId::new(2_100);
    let target_file = FileId::new(2_101);
    let specifier = importer
        .arena
        .iter()
        .find_map(|(_node, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(NodeRef::new(
                importer.arena.id(),
                importer_file,
                import.module_specifier,
            ))
        })
        .expect("fixture has one import");

    let facts = |name| {
        CanonicalSourceFileFacts::new(
            EscapedName::source(name),
            CanonicalSourceLanguage::TypeScript,
            false,
            CanonicalModuleState::External,
        )
    };
    let mut binder = CanonicalBinder::new();
    for (file, parsed, name) in [
        (importer_file, &importer, "\"/project/importer.ts\""),
        (target_file, &target, "\"/project/target.ts\""),
    ] {
        binder
            .bind_source_file_with_facts(&parsed.arena, parsed.source_file, file, facts(name))
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
            specifier,
            CanonicalResolvedModuleInput::new(
                target_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap();

    context.check_source_file(target_file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let rhs = alias_rhs(&importer, importer_file, "Bad");
    let before = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    let first = context.get_type_from_type_node(rhs).unwrap_err();
    assert!(matches!(first, DeclaredTypeError::TypeNodeUnavailable(_)));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
        ),
        before,
    );
    assert_eq!(context.get_type_from_type_node(rhs), Err(first));
}
