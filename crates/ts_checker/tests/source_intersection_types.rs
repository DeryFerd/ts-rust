use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, TypeData, TypeId,
    TypeNodeUnavailable, TypeRecord, ValueSymbolLinks, type_records::IntersectionTypeData,
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "interface A { a: string; shared: string; readonly stable: number }\n",
    "interface B { b: number; shared: string; readonly stable: number }\n",
    "type AB = A & B;\n",
    "type AB2 = A & B;\n",
    "type BA = B & A;\n",
    "type Nested = (A & B) & { c: boolean };\n",
    "type StructuralLeft = { left: string } & { right: number };\n",
    "type StructuralRight = { left: string } & { right: number } & { left: string };\n",
    "type ReadonlyIntersection = { readonly marker: string } & { stable: number };\n",
    "type MutableIntersection = { marker: string } & { stable: number };\n",
    "type Same = A & A;\n",
    "type Either = A | B;\n",
    "type Full = { a: string; shared: string; readonly stable: number; b: number };\n",
    "type Weak = { c?: string };\n",
    "type RequiredShape = { property: string };\n",
    "type OptionalShape = { property?: string };\n",
    "const full: Full = { a: \"a\", b: 1, shared: \"s\", stable: 0 };\n",
    "const good: AB = full;\n",
    "const directAB: A & B = full;\n",
    "const directBA: B & A = full;\n",
    "const readA = good.a;\n",
    "const readB = good.b;\n",
    "const readShared = good.shared;\n",
    "const readDirectAB = directAB.a;\n",
    "const readDirectBA = directBA.b;\n",
    "interface KindA { kind: \"a\" }\n",
    "interface KindB { kind: \"b\" }\n",
    "type Impossible = KindA & KindB;\n",
    "type ValueNever = { value: string } & { value: number };\n",
    "type AnyNever = { value: any } & { value: never };\n",
    "type BooleanImpossible = { value: boolean } & { value: string };\n",
    "type NullImpossible = { value: null } & { value: string };\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/intersection-types.ts\""),
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
        data => panic!("expected source property object, got {data:?}"),
    }
}

fn intersection_data<'a>(
    context: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a IntersectionTypeData {
    let Some(TypeData::Intersection(data)) =
        context.store().type_payload(type_).map(TypeRecord::data)
    else {
        panic!("expected raw intersection {type_:?}")
    };
    data
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
fn source_intersections_preserve_order_identity_properties_reduction_and_relations() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_901);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let aliases = [
        "AB",
        "AB2",
        "BA",
        "Nested",
        "StructuralLeft",
        "StructuralRight",
        "ReadonlyIntersection",
        "MutableIntersection",
        "Same",
        "Either",
        "Full",
        "Weak",
        "RequiredShape",
        "OptionalShape",
        "Impossible",
        "ValueNever",
        "AnyNever",
        "BooleanImpossible",
        "NullImpossible",
    ]
    .into_iter()
    .map(|name| {
        (
            name,
            symbol(
                &parsed,
                file,
                &context,
                SyntaxKind::TypeAliasDeclaration,
                name,
            ),
        )
    })
    .collect::<std::collections::BTreeMap<_, _>>();
    let interfaces = ["A", "B", "KindA", "KindB"]
        .into_iter()
        .map(|name| {
            (
                name,
                symbol(
                    &parsed,
                    file,
                    &context,
                    SyntaxKind::InterfaceDeclaration,
                    name,
                ),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    let types = aliases
        .iter()
        .map(|(name, symbol)| (*name, declared_type(&context, *symbol)))
        .collect::<std::collections::BTreeMap<_, _>>();
    let type_of = |name: &str| types[name];
    let a = declared_type(&context, interfaces["A"]);
    let b = declared_type(&context, interfaces["B"]);
    let kind_a = declared_type(&context, interfaces["KindA"]);
    let kind_b = declared_type(&context, interfaces["KindB"]);
    let ab = type_of("AB");
    let ab2 = type_of("AB2");
    let ba = type_of("BA");
    let nested = type_of("Nested");
    let structural_left = type_of("StructuralLeft");
    let structural_right = type_of("StructuralRight");
    let readonly_intersection = type_of("ReadonlyIntersection");
    let mutable_intersection = type_of("MutableIntersection");
    let either = type_of("Either");
    let full = type_of("Full");
    let weak = type_of("Weak");
    let required_shape = type_of("RequiredShape");
    let optional_shape = type_of("OptionalShape");
    let impossible = type_of("Impossible");
    let value_never = type_of("ValueNever");
    let any_never = type_of("AnyNever");
    let boolean_impossible = type_of("BooleanImpossible");
    let null_impossible = type_of("NullImpossible");

    let direct_ab = variable_type(&parsed, file, &context, "directAB");
    let direct_ba = variable_type(&parsed, file, &context, "directBA");
    assert_ne!(ab, ab2);
    assert_ne!(direct_ab, direct_ba);
    assert_eq!(type_of("Same"), a);
    assert_eq!(context.type_to_string(ab).unwrap(), "AB");
    assert_eq!(context.type_to_string(ba).unwrap(), "BA");
    assert_eq!(context.type_to_string(impossible).unwrap(), "Impossible");

    assert_eq!(
        intersection_data(&context, ab).intersection.types,
        vec![a, b]
    );
    assert_eq!(
        intersection_data(&context, ab2).intersection.types,
        vec![a, b]
    );
    assert_eq!(
        intersection_data(&context, ba).intersection.types,
        vec![b, a]
    );
    assert_eq!(
        intersection_data(&context, direct_ab).intersection.types,
        vec![a, b]
    );
    assert_eq!(
        intersection_data(&context, direct_ba).intersection.types,
        vec![b, a]
    );
    assert_eq!(
        &intersection_data(&context, nested).intersection.types[..2],
        &[a, b]
    );
    assert_eq!(
        intersection_data(&context, nested).intersection.types.len(),
        3
    );

    let ab_properties = intersection_data(&context, ab)
        .intersection
        .resolved_properties
        .as_deref()
        .expect("intersection properties are resolved");
    let names = ab_properties
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
    assert_eq!(names, ["a", "shared", "stable", "b"]);

    let a_properties = structured_properties(&context, a);
    let b_properties = structured_properties(&context, b);
    assert_eq!(
        property_by_name(&context, ab_properties, "a"),
        property_by_name(&context, &a_properties, "a"),
    );
    assert_eq!(
        property_by_name(&context, ab_properties, "b"),
        property_by_name(&context, &b_properties, "b"),
    );
    let shared = property_by_name(&context, ab_properties, "shared");
    let stable = property_by_name(&context, ab_properties, "stable");
    assert_eq!(
        context.store().symbol(shared).unwrap().flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
    );
    assert!(
        context
            .store()
            .symbol(shared)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::CONTAINS_PUBLIC)
    );
    assert!(
        context
            .store()
            .symbol(stable)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY)
    );
    let (string_type, number_type, boolean_type, never_type) = {
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
            bootstrap.never_type,
        )
    };
    assert_eq!(
        context.store().value_symbol_links(shared),
        Some(&ValueSymbolLinks {
            resolved_type: Some(string_type),
            containing_type: Some(ab),
            ..ValueSymbolLinks::default()
        }),
    );
    let nested_c = property_by_name(
        &context,
        intersection_data(&context, nested)
            .intersection
            .resolved_properties
            .as_deref()
            .unwrap(),
        "c",
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(nested_c)
            .and_then(|links| links.resolved_type),
        Some(boolean_type),
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(stable)
            .and_then(|links| links.resolved_type),
        Some(number_type),
    );

    let impossible_record = context.store().type_payload(impossible).unwrap();
    assert!(impossible_record.object_flags().contains(
        ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED | ObjectFlags::IS_NEVER_INTERSECTION
    ));
    assert_eq!(
        intersection_data(&context, impossible).intersection.types,
        vec![kind_a, kind_b]
    );
    assert_eq!(
        context.is_type_assignable_to(impossible, string_type),
        Ok(true),
    );

    let value_never_record = context.store().type_payload(value_never).unwrap();
    assert!(
        value_never_record
            .object_flags()
            .contains(ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED)
    );
    assert!(
        !value_never_record
            .object_flags()
            .intersects(ObjectFlags::IS_NEVER_INTERSECTION)
    );
    let value_property = property_by_name(
        &context,
        intersection_data(&context, value_never)
            .intersection
            .resolved_properties
            .as_deref()
            .unwrap(),
        "value",
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(value_property)
            .and_then(|links| links.resolved_type),
        Some(never_type),
    );
    let any_never_property = property_by_name(
        &context,
        intersection_data(&context, any_never)
            .intersection
            .resolved_properties
            .as_deref()
            .unwrap(),
        "value",
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(any_never_property)
            .and_then(|links| links.resolved_type),
        Some(never_type),
    );

    for reduced in [boolean_impossible, null_impossible] {
        assert!(
            context
                .store()
                .type_payload(reduced)
                .unwrap()
                .object_flags()
                .contains(
                    ObjectFlags::IS_NEVER_INTERSECTION_COMPUTED
                        | ObjectFlags::IS_NEVER_INTERSECTION
                ),
        );
        assert!(matches!(
            intersection_data(&context, reduced)
                .intersection
                .types
                .as_slice(),
            [_, _]
        ));
        assert_eq!(
            context.is_type_assignable_to(reduced, string_type),
            Ok(true)
        );
    }

    assert_eq!(context.is_type_identical_to(ab, ab2), Ok(true));
    assert_eq!(context.is_type_identical_to(ab, ba), Ok(true));
    assert_eq!(context.is_type_identical_to(ab, nested), Ok(false));
    assert_eq!(
        context.is_type_identical_to(structural_left, structural_right),
        Ok(true),
    );
    assert_eq!(
        context.is_type_identical_to(readonly_intersection, mutable_intersection),
        Ok(false),
    );
    assert_eq!(
        context.is_type_identical_to(required_shape, optional_shape),
        Ok(false),
    );
    assert_eq!(
        context.is_type_identical_to(optional_shape, required_shape),
        Ok(false),
    );
    assert_eq!(context.is_type_assignable_to(ab, a), Ok(true));
    assert_eq!(context.is_type_assignable_to(a, ab), Ok(false));
    assert_eq!(context.is_type_assignable_to(full, ab), Ok(true));
    assert_eq!(context.is_type_assignable_to(ab, full), Ok(true));
    assert_eq!(context.is_type_assignable_to(ab, ba), Ok(true));
    assert_eq!(context.is_type_assignable_to(ba, ab), Ok(true));
    assert_eq!(context.is_type_assignable_to(either, ab), Ok(false));
    assert_eq!(context.is_type_comparable_to(either, ab), Ok(false));
    assert_eq!(context.is_type_assignable_to(ab, weak), Ok(false));
    assert_eq!(
        context.type_to_string(variable_type(&parsed, file, &context, "readA")),
        Ok("string".to_owned()),
    );
    assert_eq!(
        context.type_to_string(variable_type(&parsed, file, &context, "readB")),
        Ok("number".to_owned()),
    );
    assert_eq!(
        context.type_to_string(variable_type(&parsed, file, &context, "readShared")),
        Ok("string".to_owned()),
    );
    assert_eq!(
        context.type_to_string(variable_type(&parsed, file, &context, "readDirectAB")),
        Ok("string".to_owned()),
    );
    assert_eq!(
        context.type_to_string(variable_type(&parsed, file, &context, "readDirectBA")),
        Ok("number".to_owned()),
    );

    let warm_relations = context.store().relation_state_snapshot();
    for _ in 0..2 {
        assert_eq!(context.is_type_identical_to(ab, ab2), Ok(true));
        assert_eq!(context.is_type_identical_to(ab, ba), Ok(true));
        assert_eq!(context.is_type_identical_to(ab, nested), Ok(false));
        assert_eq!(
            context.is_type_identical_to(structural_left, structural_right),
            Ok(true),
        );
        assert_eq!(
            context.is_type_identical_to(readonly_intersection, mutable_intersection),
            Ok(false),
        );
        assert_eq!(
            context.is_type_identical_to(required_shape, optional_shape),
            Ok(false),
        );
        assert_eq!(
            context.is_type_identical_to(optional_shape, required_shape),
            Ok(false),
        );
        assert_eq!(context.is_type_assignable_to(either, ab), Ok(false));
        assert_eq!(context.is_type_comparable_to(either, ab), Ok(false));
        assert_eq!(context.is_type_assignable_to(ab, weak), Ok(false));
    }
    assert_eq!(context.store().relation_state_snapshot(), warm_relations);

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    for name in aliases.keys() {
        assert_eq!(
            context
                .get_type_from_type_node(alias_rhs(&parsed, file, name))
                .unwrap(),
            type_of(name),
        );
    }
    context.recheck_source_file(file).unwrap();
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
fn unsupported_intersection_syntax_fails_before_semantic_writes() {
    let cases = [
        (
            "type Bad = { value: string[] } & { other: number };",
            "array property",
        ),
        (
            "type Bad = ({ a: string } | { b: number }) & { c: boolean };",
            "union constituent",
        ),
        (
            "type Bad = { (): string } & { other: number };",
            "call signature",
        ),
        (
            "type A = { value: string }; type B = { other: number }; type Bad = { nested: A & B } & { final: boolean };",
            "nested intersection property",
        ),
    ];
    for (index, (source, label)) in cases.into_iter().enumerate() {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{label}: {:?}",
            parsed.diagnostics
        );
        let file = FileId::new(1_920 + u32::try_from(index).unwrap());
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
            matches!(
                first,
                DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedIntersectionOptionalProperty(_)
                        | TypeNodeUnavailable::UnsupportedIntersectionConstituent(_)
                        | TypeNodeUnavailable::UnsupportedIntersectionProperty(_)
                )
            ),
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
