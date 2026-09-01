use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, IntrinsicBootstrapOptions,
    TypeData, TypeId, TypeNodeUnavailable, TypeRecord, ValueSymbolLinks,
    type_records::{IntersectionTypeData, TypeAlias},
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

    let left_properties = structured_properties(&context, a);
    let b_properties = structured_properties(&context, b);
    assert_eq!(
        property_by_name(&context, ab_properties, "a"),
        property_by_name(&context, &left_properties, "a"),
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

fn strict_intersection_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/strict-intersection-types.ts\""),
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

fn query_intersection_alias(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    name: &str,
) -> TypeId {
    let owner = symbol(
        parsed,
        file,
        context,
        SyntaxKind::TypeAliasDeclaration,
        name,
    );
    let type_ = context
        .get_type_from_type_node(alias_rhs(parsed, file, name))
        .unwrap();
    assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
    assert_eq!(declared_type(context, owner), type_);
    type_
}

fn assert_intersection_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    aliases: &[(&str, TypeId)],
    reductions: &[(&str, TypeId)],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.relation_state_snapshot(),
            parsed
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    (
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            aliases
                .iter()
                .map(|(_, type_)| {
                    let record = store.type_payload(*type_).unwrap();
                    let (union, intersection) = match record.data() {
                        TypeData::Union(data) => (Some(data.clone()), None),
                        TypeData::Intersection(data) => (None, Some(data.clone())),
                        data => panic!("expected a retained union or intersection, got {data:?}"),
                    };
                    (
                        record.flags(),
                        record.object_flags(),
                        record.alias(),
                        union,
                        intersection,
                    )
                })
                .collect::<Vec<_>>(),
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned(),
            context.diagnostics().clone(),
        )
    };
    let before = snapshot(context);
    for _ in 0..2 {
        for &(name, type_) in aliases.iter().rev() {
            assert_eq!(query_intersection_alias(context, parsed, file, name), type_);
        }
        for &(name, primitive) in reductions.iter().rev() {
            assert_eq!(
                query_intersection_alias(context, parsed, file, name),
                primitive
            );
        }
        context.check_source_file(file).unwrap();
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(context), before);
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn primitive_empty_intersections_keep_order_aliases_and_native_relations() {
    let source = concat!(
        "type Text = string & {};\n",
        "type TextAgain = string & {};\n",
        "type ReverseText = {} & string;\n",
        "type Numeric = number & {};\n",
        "type ReverseNumeric = {} & number;\n",
        "type Empty = {};\n",
        "type ReducedText = string & Empty;\n",
        "type ReducedNumeric = Empty & number;\n",
        "const text: Text = 'value';\n",
        "const numeric: Numeric = 42;\n",
        "const reverseText: ReverseText = text;\n",
        "const reverseNumeric: ReverseNumeric = numeric;\n",
        "const directText: string & {} = text;\n",
        "const directNumeric: number & {} = numeric;\n",
        "const plainText: string = text;\n",
        "const plainNumeric: number = numeric;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_930);
    for source_first in [false, true] {
        let mut context = strict_intersection_context(&parsed, file);
        if source_first {
            context.check_source_file(file).unwrap();
        }
        let aliases = [
            "Text",
            "TextAgain",
            "ReverseText",
            "Numeric",
            "ReverseNumeric",
        ]
        .map(|name| {
            (
                name,
                query_intersection_alias(&mut context, &parsed, file, name),
            )
        });
        let [
            (_, text),
            (_, text_again),
            (_, reverse_text),
            (_, numeric),
            (_, reverse_numeric),
        ] = aliases;
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let empty = bootstrap.empty_type_literal_type;
        assert_eq!(
            query_intersection_alias(&mut context, &parsed, file, "ReducedText"),
            string,
        );
        assert_eq!(
            query_intersection_alias(&mut context, &parsed, file, "ReducedNumeric"),
            number,
        );
        for (type_, expected) in [
            (text, [string, empty]),
            (text_again, [string, empty]),
            (reverse_text, [empty, string]),
            (numeric, [number, empty]),
            (reverse_numeric, [empty, number]),
        ] {
            assert_eq!(
                intersection_data(&context, type_).intersection.types,
                expected
            );
        }
        for (name, type_) in aliases {
            let owner = symbol(
                &parsed,
                file,
                &context,
                SyntaxKind::TypeAliasDeclaration,
                name,
            );
            assert_eq!(
                context
                    .store()
                    .type_payload(type_)
                    .and_then(TypeRecord::alias)
                    .and_then(|alias| context.store().type_alias(alias))
                    .and_then(TypeAlias::symbol),
                Some(owner),
            );
            assert_eq!(context.type_to_string(type_).unwrap(), name);
        }
        assert_ne!(text, text_again);
        assert_ne!(text, reverse_text);
        assert_ne!(numeric, reverse_numeric);
        assert_eq!(context.is_type_identical_to(text, text_again), Ok(true));
        assert_eq!(context.is_type_identical_to(text, reverse_text), Ok(true));
        assert_eq!(
            context.is_type_identical_to(numeric, reverse_numeric),
            Ok(true)
        );
        for (intersection, primitive) in [(text, string), (numeric, number)] {
            assert_eq!(
                context.is_type_assignable_to(intersection, primitive),
                Ok(true)
            );
            assert_eq!(
                context.is_type_assignable_to(primitive, intersection),
                Ok(true)
            );
        }
        assert_eq!(context.is_type_assignable_to(number, text), Ok(false));
        assert_eq!(context.is_type_assignable_to(string, numeric), Ok(false));
        assert_eq!(
            intersection_data(
                &context,
                variable_type(&parsed, file, &context, "directText")
            )
            .intersection
            .types,
            [string, empty],
        );
        assert_eq!(
            intersection_data(
                &context,
                variable_type(&parsed, file, &context, "directNumeric")
            )
            .intersection
            .types,
            [number, empty],
        );
        assert_intersection_replay(
            &mut context,
            &parsed,
            file,
            &aliases,
            &[("ReducedText", string), ("ReducedNumeric", number)],
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn primitive_empty_intersection_union_keeps_literals_and_reports_number_assignment() {
    let source = concat!(
        "type Open = 'known' | (string & {});\n",
        "const good: Open = 'another';\n",
        "const known: Open = 'known';\n",
        "const bad: Open = 42;\n",
        "type CustomHeader = string & {};\n",
        "type NamedOpen = 'known' | CustomHeader;\n",
        "const namedGood: NamedOpen = 'another';\n",
        "const namedKnown: NamedOpen = 'known';\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_931);
    for source_first in [false, true] {
        let mut context = strict_intersection_context(&parsed, file);
        if source_first {
            context.check_source_file(file).unwrap();
        }
        let open = query_intersection_alias(&mut context, &parsed, file, "Open");
        let custom_header = query_intersection_alias(&mut context, &parsed, file, "CustomHeader");
        let named_open = query_intersection_alias(&mut context, &parsed, file, "NamedOpen");
        context.check_source_file(file).unwrap();
        let TypeData::Union(union) = context.store().type_payload(open).unwrap().data() else {
            panic!("the literal and open string must remain separate union constituents")
        };
        let constituents = union.union.types.clone();
        assert_eq!(constituents.len(), 2);
        let intersection = constituents
            .iter()
            .copied()
            .find(|type_| {
                matches!(
                    context.store().type_payload(*type_).unwrap().data(),
                    TypeData::Intersection(_)
                )
            })
            .unwrap();
        let literal = *constituents
            .iter()
            .find(|type_| **type_ != intersection)
            .unwrap();
        assert_eq!(context.type_to_string(literal).unwrap(), "\"known\"");
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        assert_eq!(
            intersection_data(&context, intersection).intersection.types,
            [string, bootstrap.empty_type_literal_type],
        );
        assert_eq!(context.type_to_string(open).unwrap(), "Open");
        assert_eq!(context.is_type_assignable_to(string, open), Ok(true));
        assert_eq!(context.is_type_assignable_to(number, open), Ok(false));
        let TypeData::Union(named_union) = context.store().type_payload(named_open).unwrap().data()
        else {
            panic!("the named intersection must remain a union constituent")
        };
        assert_eq!(named_union.union.types.len(), 2);
        assert!(named_union.union.types.contains(&custom_header));
        assert!(named_union.union.types.contains(&literal));
        assert_eq!(
            context.type_to_string(custom_header).unwrap(),
            "CustomHeader"
        );
        assert_eq!(context.type_to_string(named_open).unwrap(), "NamedOpen");
        assert_eq!(context.is_type_assignable_to(string, named_open), Ok(true));
        assert_eq!(context.is_type_assignable_to(number, named_open), Ok(false));
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, ["42", "Open"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type '42' is not assignable to type 'Open'.",
        );
        let bad = declaration(&parsed, file, SyntaxKind::VariableDeclaration, "bad");
        let NodeData::VariableDeclaration(variable) = &parsed.arena.get(bad.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(
            diagnostic.node,
            Some(NodeRef::new(bad.arena, file, variable.name))
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_intersection_replay(
            &mut context,
            &parsed,
            file,
            &[
                ("Open", open),
                ("CustomHeader", custom_header),
                ("NamedOpen", named_open),
            ],
            &[],
        );
    }
}

#[test]
fn primitive_empty_intersections_reject_null_and_undefined_with_strict_null_checks() {
    let source = concat!(
        "type Text = string & {};\n",
        "type Numeric = number & {};\n",
        "const nullText: Text = null;\n",
        "const undefinedText: Text = undefined;\n",
        "const nullNumeric: Numeric = null;\n",
        "const undefinedNumeric: Numeric = undefined;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_932);
    for source_first in [false, true] {
        let mut context = strict_intersection_context(&parsed, file);
        if source_first {
            context.check_source_file(file).unwrap();
        }
        let text = query_intersection_alias(&mut context, &parsed, file, "Text");
        let numeric = query_intersection_alias(&mut context, &parsed, file, "Numeric");
        context.check_source_file(file).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let null = bootstrap.null_type;
        let undefined = bootstrap.undefined_type;
        for target in [text, numeric] {
            assert_eq!(context.is_type_assignable_to(null, target), Ok(false));
            assert_eq!(context.is_type_assignable_to(undefined, target), Ok(false));
        }
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
        for (diagnostic, (name, source, target, primitive)) in diagnostics.iter().zip([
            ("nullText", "null", "Text", "string"),
            ("undefinedText", "undefined", "Text", "string"),
            ("nullNumeric", "null", "Numeric", "number"),
            ("undefinedNumeric", "undefined", "Numeric", "number"),
        ]) {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, [source, target]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Type '{source}' is not assignable to type '{target}'.\n  Type '{source}' is not assignable to type '{primitive}'."
                ),
            );
            let node = declaration(&parsed, file, SyntaxKind::VariableDeclaration, name);
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(node.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                diagnostic.node,
                Some(NodeRef::new(node.arena, file, variable.name))
            );
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
        }
        assert_intersection_replay(
            &mut context,
            &parsed,
            file,
            &[("Text", text), ("Numeric", numeric)],
            &[],
        );
    }
}
