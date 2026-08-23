use ts_ast::{FileId, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore,
    IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::{LiteralValue, RegularLiteralLink},
    types::{ObjectFlags, TypeFlags},
};
use ts_jsnum::{Number, PseudoBigInt};
use ts_parser::{ParseResult, parse_source_file};

fn checker_store() -> CanonicalTypeMapperStore {
    let mut store = CanonicalTypeMapperStore::new();
    store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        })
        .unwrap();
    store
}

fn string_literal(store: &mut CanonicalTypeMapperStore, value: &str) -> TypeId {
    store
        .get_template_literal_type(&[value.to_owned()], &[])
        .unwrap()
}

fn mapping_symbol(store: &mut CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
    store.alloc_transient_symbol(
        SymbolFlags::TYPE_ALIAS,
        EscapedName::source(name),
        CheckFlags::NONE,
    )
}

fn source_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/template-types.ts\""),
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
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn source_alias(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> (SemanticSymbolId, NodeRef) {
    let (declaration, rhs) = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                NodeRef::new(parsed.arena.id(), file, node),
                NodeRef::new(parsed.arena.id(), file, alias.type_),
            ))
        })
        .unwrap_or_else(|| panic!("missing type alias {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    (context.store().get_merged_symbol(raw).unwrap(), rhs)
}

fn source_alias_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .type_alias_links(symbol)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("missing declared type for alias {symbol:?}"))
}

fn template_parts(
    store: &mut CanonicalTypeMapperStore,
    arena: &NodeArena,
    node: NodeId,
) -> (Vec<String>, Vec<TypeId>) {
    let NodeData::TemplateLiteralTypeNode(template) = &arena.get(node).unwrap().data else {
        panic!("expected a template-literal type node")
    };
    let NodeData::TemplateHead(head) = &arena.get(template.head).unwrap().data else {
        panic!("expected a template head")
    };
    let mut texts = vec![head.text.clone()];
    let mut types = Vec::with_capacity(template.template_spans.nodes.len());
    for span in &template.template_spans.nodes {
        let NodeData::TemplateLiteralTypeSpan(span) = &arena.get(*span).unwrap().data else {
            panic!("expected a template-literal type span")
        };
        types.push(source_type(store, arena, span.type_));
        match &arena.get(span.literal).unwrap().data {
            NodeData::TemplateMiddle(literal) => texts.push(literal.text.clone()),
            NodeData::TemplateTail(literal) => texts.push(literal.text.clone()),
            _ => panic!("expected a template continuation"),
        }
    }
    (texts, types)
}

fn source_type(store: &mut CanonicalTypeMapperStore, arena: &NodeArena, node: NodeId) -> TypeId {
    let record = arena.get(node).unwrap();
    match record.kind {
        SyntaxKind::StringKeyword => store.intrinsic_bootstrap().unwrap().string_type,
        SyntaxKind::NumberKeyword => store.intrinsic_bootstrap().unwrap().number_type,
        SyntaxKind::BigIntKeyword => store.intrinsic_bootstrap().unwrap().bigint_type,
        SyntaxKind::BooleanKeyword => store.intrinsic_bootstrap().unwrap().boolean_type,
        SyntaxKind::NeverKeyword => store.intrinsic_bootstrap().unwrap().never_type,
        SyntaxKind::NullKeyword => store.intrinsic_bootstrap().unwrap().null_type,
        SyntaxKind::UndefinedKeyword => store.intrinsic_bootstrap().unwrap().undefined_type,
        SyntaxKind::LiteralType => {
            let NodeData::LiteralTypeNode(literal) = &record.data else {
                panic!("expected a literal type")
            };
            let value = arena.get(literal.literal).unwrap();
            match &value.data {
                NodeData::StringLiteral(value) => string_literal(store, &value.text),
                NodeData::NumericLiteral(value) => store
                    .alloc_literal_type(
                        TypeFlags::NUMBER_LITERAL,
                        LiteralValue::Number(Number::from_string(&value.text)),
                        RegularLiteralLink::SelfType,
                    )
                    .unwrap(),
                NodeData::BigIntLiteral(value) => store
                    .alloc_literal_type(
                        TypeFlags::BIG_INT_LITERAL,
                        LiteralValue::BigInt(PseudoBigInt::parse_valid(&value.text)),
                        RegularLiteralLink::SelfType,
                    )
                    .unwrap(),
                _ if value.kind == SyntaxKind::TrueKeyword => {
                    store.intrinsic_bootstrap().unwrap().regular_true_type
                }
                _ if value.kind == SyntaxKind::FalseKeyword => {
                    store.intrinsic_bootstrap().unwrap().regular_false_type
                }
                _ if value.kind == SyntaxKind::NullKeyword => {
                    store.intrinsic_bootstrap().unwrap().null_type
                }
                _ => panic!("unsupported fixture literal {:?}", value.kind),
            }
        }
        SyntaxKind::UnionType => {
            let NodeData::UnionTypeNode(union) = &record.data else {
                panic!("expected a union type")
            };
            let mut types = union
                .types
                .nodes
                .iter()
                .map(|node| source_type(store, arena, *node))
                .collect::<Vec<_>>();
            types.sort_by(|left, right| {
                let left = store.type_payload(*left).unwrap();
                let right = store.type_payload(*right).unwrap();
                left.flags()
                    .cmp(&right.flags())
                    .then_with(|| match (left.data(), right.data()) {
                        (TypeData::Literal(left), TypeData::Literal(right)) => {
                            match (&left.value, &right.value) {
                                (LiteralValue::String(left), LiteralValue::String(right)) => {
                                    left.cmp(right)
                                }
                                _ => left.regular_type.cmp(&right.regular_type),
                            }
                        }
                        _ => left.id().cmp(&right.id()),
                    })
            });
            types.dedup();
            store
                .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, types)
                .unwrap()
        }
        SyntaxKind::ParenthesizedType => {
            let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                panic!("expected a parenthesized type")
            };
            source_type(store, arena, parenthesized.type_)
        }
        SyntaxKind::TemplateLiteralType => {
            let (texts, types) = template_parts(store, arena, node);
            store.get_template_literal_type(&texts, &types).unwrap()
        }
        _ => panic!("unsupported fixture type {:?}", record.kind),
    }
}

fn parsed_template(
    store: &mut CanonicalTypeMapperStore,
    source: &str,
) -> (Vec<String>, Vec<TypeId>) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let alias = parsed
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::TypeAliasDeclaration(alias) => Some(alias.type_),
            _ => None,
        })
        .expect("fixture contains a type alias");
    template_parts(store, &parsed.arena, alias)
}

fn literal_text(store: &CanonicalTypeMapperStore, type_: TypeId) -> &str {
    let TypeData::Literal(literal) = store.type_payload(type_).unwrap().data() else {
        panic!("expected a string literal")
    };
    let LiteralValue::String(value) = &literal.value else {
        panic!("expected a string literal")
    };
    value
}

fn union_texts(store: &CanonicalTypeMapperStore, type_: TypeId) -> Vec<String> {
    let TypeData::Union(union) = store.type_payload(type_).unwrap().data() else {
        panic!("expected a union")
    };
    union
        .union
        .types
        .iter()
        .map(|type_| literal_text(store, *type_).to_owned())
        .collect()
}

#[test]
fn production_checker_resolves_source_template_aliases_and_reuses_cached_nodes() {
    let parsed = parse_source_file(concat!(
        "type Prefix = 'read' | 'write';\n",
        "type Literal = `before-${'value'}-${42}-${true}`;\n",
        "type Choices = `${Prefix}-${'start' | 'end'}`;\n",
        "type NumberPattern = `id-${number}`;\n",
        "type Nested = `outer-${`inner-${number}`}`;\n",
        "type Plain = `${string}`;\n",
        "type Empty = `before-${never}`;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = source_context(&parsed, file);
    let aliases = [
        "Literal",
        "Choices",
        "NumberPattern",
        "Nested",
        "Plain",
        "Empty",
    ]
    .into_iter()
    .map(|name| (name, source_alias(&parsed, file, &context, name)))
    .collect::<std::collections::BTreeMap<_, _>>();

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let literal = source_alias_type(&context, aliases["Literal"].0);
    assert_eq!(
        literal_text(context.store(), literal),
        "before-value-42-true"
    );

    let choices = source_alias_type(&context, aliases["Choices"].0);
    assert_eq!(
        union_texts(context.store(), choices),
        ["read-end", "read-start", "write-end", "write-start"]
    );

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for (name, prefix) in [("NumberPattern", "id-"), ("Nested", "outer-inner-")] {
        let type_ = source_alias_type(&context, aliases[name].0);
        let TypeData::TemplateLiteral(template) =
            context.store().type_payload(type_).unwrap().data()
        else {
            panic!("{name} must retain its numeric placeholder")
        };
        assert_eq!(template.texts, [prefix, ""]);
        assert_eq!(template.types, [number]);
    }

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        source_alias_type(&context, aliases["Plain"].0),
        bootstrap.string_type
    );
    assert_eq!(
        source_alias_type(&context, aliases["Empty"].0),
        bootstrap.never_type
    );

    for (name, (symbol, rhs)) in &aliases {
        assert_eq!(
            context
                .store()
                .type_node_links(*rhs)
                .and_then(|links| links.resolved_type),
            Some(source_alias_type(&context, *symbol)),
            "{name} must cache its source template node"
        );
    }

    let type_count = context.store().type_len();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), type_count);
}

#[test]
fn production_checker_matches_templates_with_multiple_target_placeholders() {
    let parsed = parse_source_file(concat!(
        "type Source = `<<${string}>.<${number}-${number}>>`;\n",
        "type Target = `<${string}.${string}>`;\n",
        "type Matched = Source extends Target ? true : false;\n",
        "type Rejected = `<<${string}><${number}-${number}>>` extends Target ? true : false;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8);
    let mut context = source_context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    for (name, expected) in [("Matched", "true"), ("Rejected", "false")] {
        let (alias, _) = source_alias(&parsed, file, &context, name);
        assert_eq!(
            context
                .type_to_string(source_alias_type(&context, alias))
                .unwrap(),
            expected,
            "alias {name}",
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().conditional_root_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().conditional_root_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn production_checker_applies_intrinsic_string_mappings_from_source_aliases() {
    let parsed = parse_source_file(concat!(
        "type Uppercase<Input extends string> = intrinsic;\n",
        "type Lowercase<Input extends string> = intrinsic;\n",
        "type Capitalize<Input extends string> = intrinsic;\n",
        "type Uncapitalize<Input extends string> = intrinsic;\n",
        "type Loud = Uppercase<'hello'>;\n",
        "type Quiet = Lowercase<'HELLO'>;\n",
        "type Head = Capitalize<'hello'>;\n",
        "type Tail = Uncapitalize<'Hello'>;\n",
        "type Choices = Uppercase<'left' | 'right'>;\n",
        "type Pattern = Uppercase<`path-${string}`>;\n",
        "type Generic = Uppercase<string>;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = source_context(&parsed, file);
    let aliases = [
        "Loud", "Quiet", "Head", "Tail", "Choices", "Pattern", "Generic",
    ]
    .into_iter()
    .map(|name| (name, source_alias(&parsed, file, &context, name)))
    .collect::<std::collections::BTreeMap<_, _>>();
    let uppercase = source_alias(&parsed, file, &context, "Uppercase").0;

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    for (name, expected) in [
        ("Loud", "HELLO"),
        ("Quiet", "hello"),
        ("Head", "Hello"),
        ("Tail", "hello"),
    ] {
        assert_eq!(
            literal_text(
                context.store(),
                source_alias_type(&context, aliases[name].0)
            ),
            expected
        );
    }
    assert_eq!(
        union_texts(
            context.store(),
            source_alias_type(&context, aliases["Choices"].0)
        ),
        ["LEFT", "RIGHT"]
    );

    let generic = source_alias_type(&context, aliases["Generic"].0);
    let TypeData::StringMapping(mapping) = context.store().type_payload(generic).unwrap().data()
    else {
        panic!("Uppercase<string> must retain a generic mapping")
    };
    assert_eq!(
        mapping.target,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_eq!(
        context.store().type_payload(generic).unwrap().symbol(),
        Some(uppercase)
    );

    let pattern = source_alias_type(&context, aliases["Pattern"].0);
    let TypeData::TemplateLiteral(template) = context.store().type_payload(pattern).unwrap().data()
    else {
        panic!("mapped templates must retain their substitution")
    };
    assert_eq!(template.texts, ["PATH-", ""]);
    assert_eq!(template.types, [generic]);
}

#[test]
fn production_checker_replays_intrinsic_aliases_with_lone_surrogate_escapes() {
    let parsed = parse_source_file(concat!(
        "type Uppercase<Input extends string> = intrinsic;\n",
        "type Lowercase<Input extends string> = intrinsic;\n",
        "type Capitalize<Input extends string> = intrinsic;\n",
        "type Uncapitalize<Input extends string> = intrinsic;\n",
        "type U = Uppercase<\"\\uD800\">;\n",
        "type L = Lowercase<\"A\\uD800B\">;\n",
        "type C = Capitalize<\"\\uDC00x\">;\n",
        "type Un = Uncapitalize<\"\\uD834X\">;\n",
        "type ReplayU = U;\n",
        "type ReplayL = L;\n",
        "type ReplayC = C;\n",
        "type ReplayUn = Un;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = source_context(&parsed, file);
    let aliases = [
        "U", "L", "C", "Un", "ReplayU", "ReplayL", "ReplayC", "ReplayUn",
    ]
    .into_iter()
    .map(|name| (name, source_alias(&parsed, file, &context, name)))
    .collect::<std::collections::BTreeMap<_, _>>();

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    for (original, replay) in [
        ("U", "ReplayU"),
        ("L", "ReplayL"),
        ("C", "ReplayC"),
        ("Un", "ReplayUn"),
    ] {
        assert_eq!(
            source_alias_type(&context, aliases[original].0),
            source_alias_type(&context, aliases[replay].0),
            "{replay} must preserve the cached {original} identity"
        );
    }

    let count = context.store().type_len();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), count);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn production_checker_reports_excessive_template_unions_without_fatal_invariants() {
    let parsed = parse_source_file(concat!(
        "type N = 0 | 1 | 2 | 3;\n",
        "type TooComplex = `${N}${N}${N}${N}${N}${N}${N}${N}${N}`;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = source_context(&parsed, file);
    let (alias, template) = source_alias(&parsed, file, &context, "TooComplex");

    context.check_source_file(file).unwrap();

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].diagnostic.code(), 2590);
    assert_eq!(diagnostics[0].node, Some(template));
    let error = context.store().intrinsic_bootstrap().unwrap().error_type;
    assert_eq!(source_alias_type(&context, alias), error);
    assert_eq!(
        context
            .store()
            .type_node_links(template)
            .and_then(|links| links.resolved_type),
        Some(error)
    );

    let count = context.store().type_len();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), count);
    assert_eq!(context.diagnostics().as_slice().len(), 1);
}

#[test]
fn source_template_folds_literal_number_boolean_null_and_bigint_spans() {
    let mut store = checker_store();
    let (texts, types) = parsed_template(
        &mut store,
        "type Value = `left-${'right'}-${42}-${true}-${null}-${undefined}-${7n}`;",
    );

    let result = store.get_template_literal_type(&texts, &types).unwrap();
    assert_eq!(
        literal_text(&store, result),
        "left-right-42-true-null-undefined-7"
    );
    assert_eq!(
        store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_string_literal_type("left-right-42-true-null-undefined-7"),
        Some(result)
    );

    let count = store.type_len();
    assert_eq!(store.get_template_literal_type(&texts, &types), Ok(result));
    assert_eq!(store.type_len(), count);
}

#[test]
fn source_template_distributes_union_spans_and_reuses_the_canonical_union() {
    let mut store = checker_store();
    let (texts, types) = parsed_template(
        &mut store,
        "type Event = `${'read' | 'write'}-${'start' | 'end'}`;",
    );

    assert_eq!(store.get_template_cross_product_union_size(&types), Ok(4));
    let result = store.get_template_literal_type(&texts, &types).unwrap();
    assert_eq!(
        union_texts(&store, result),
        ["read-end", "read-start", "write-end", "write-start"]
    );

    let count = store.type_len();
    assert_eq!(store.get_template_literal_type(&texts, &types), Ok(result));
    assert_eq!(store.type_len(), count);
}

#[test]
fn source_template_flattens_nested_patterns_and_reuses_bootstrap_number_identity() {
    let mut store = checker_store();
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    let numeric_string = store.intrinsic_bootstrap().unwrap().numeric_string_type;

    let (texts, types) = parsed_template(&mut store, "type Numeric = `${number}`;");
    assert_eq!(
        store.get_template_literal_type(&texts, &types),
        Ok(numeric_string)
    );

    let (texts, types) = parsed_template(
        &mut store,
        "type Nested = `prefix-${`inner-${number}`}-suffix`;",
    );
    let nested = store.get_template_literal_type(&texts, &types).unwrap();
    let TypeData::TemplateLiteral(template) = store.type_payload(nested).unwrap().data() else {
        panic!("nested template must retain a number pattern")
    };
    assert_eq!(template.texts, ["prefix-inner-", "-suffix"]);
    assert_eq!(template.types, [number]);

    let count = store.type_len();
    assert_eq!(store.get_template_literal_type(&texts, &types), Ok(nested));
    assert_eq!(store.type_len(), count);
}

#[test]
fn source_template_distributes_union_prefixes_across_number_patterns() {
    let mut store = checker_store();
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    let (texts, types) = parsed_template(
        &mut store,
        "type Route = `${'first' | 'second'}-${number}`;",
    );

    let result = store.get_template_literal_type(&texts, &types).unwrap();
    let TypeData::Union(union) = store.type_payload(result).unwrap().data() else {
        panic!("union placeholders must distribute into template patterns")
    };
    assert_eq!(union.union.types.len(), 2);
    for (pattern, prefix) in union.union.types.iter().zip(["first-", "second-"]) {
        let TypeData::TemplateLiteral(template) = store.type_payload(*pattern).unwrap().data()
        else {
            panic!("each distributed branch must retain its number placeholder")
        };
        assert_eq!(template.texts, [prefix, ""]);
        assert_eq!(template.types, [number]);
    }

    let count = store.type_len();
    assert_eq!(store.get_template_literal_type(&texts, &types), Ok(result));
    assert_eq!(store.type_len(), count);
}

#[test]
fn source_template_preserves_string_never_boolean_and_wildcard_rules() {
    let mut store = checker_store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let never = bootstrap.never_type;
    let wildcard = bootstrap.wildcard_type;

    let (texts, types) = parsed_template(&mut store, "type Plain = `${string}`;");
    assert_eq!(store.get_template_literal_type(&texts, &types), Ok(string));

    let (texts, types) = parsed_template(&mut store, "type Empty = `before-${never}-after`;");
    assert_eq!(store.get_template_literal_type(&texts, &types), Ok(never));

    let (texts, types) = parsed_template(&mut store, "type Flag = `flag-${boolean}`;");
    let flags = store.get_template_literal_type(&texts, &types).unwrap();
    assert_eq!(union_texts(&store, flags), ["flag-false", "flag-true"]);

    assert_eq!(
        store.get_template_literal_type(&["prefix".into(), "suffix".into()], &[wildcard]),
        Ok(wildcard)
    );
}

#[test]
fn intrinsic_string_mappings_follow_unicode_case_rules_and_distribute_unions() {
    let mut store = checker_store();
    let uppercase = mapping_symbol(&mut store, "Uppercase");
    let lowercase = mapping_symbol(&mut store, "Lowercase");
    let capitalize = mapping_symbol(&mut store, "Capitalize");
    let uncapitalize = mapping_symbol(&mut store, "Uncapitalize");

    let sharp_s = string_literal(&mut store, "\u{00DF}foo");
    let dotted_i = string_literal(&mut store, "\u{0130}STANBUL");
    let sigma = string_literal(&mut store, "\u{039F}\u{03A3}");
    let recent_uppercase = string_literal(&mut store, "\u{1C89}\u{03A3}");
    let recent_lowercase = string_literal(&mut store, "\u{1C8A}");

    let upper = store.get_string_mapping_type(uppercase, sharp_s).unwrap();
    let capitalized = store.get_string_mapping_type(capitalize, sharp_s).unwrap();
    let lower = store.get_string_mapping_type(lowercase, dotted_i).unwrap();
    let uncapped = store
        .get_string_mapping_type(uncapitalize, dotted_i)
        .unwrap();
    let final_sigma = store.get_string_mapping_type(lowercase, sigma).unwrap();
    let unchanged_uppercase = store
        .get_string_mapping_type(lowercase, recent_uppercase)
        .unwrap();
    let unchanged_lowercase = store
        .get_string_mapping_type(uppercase, recent_lowercase)
        .unwrap();

    assert_eq!(literal_text(&store, upper), "SSFOO");
    assert_eq!(literal_text(&store, capitalized), "SSfoo");
    assert_eq!(literal_text(&store, lower), "i\u{0307}stanbul");
    assert_eq!(literal_text(&store, uncapped), "i\u{0307}STANBUL");
    assert_eq!(literal_text(&store, final_sigma), "\u{03BF}\u{03C2}");
    assert_eq!(
        literal_text(&store, unchanged_uppercase),
        "\u{1C89}\u{03C3}"
    );
    assert_eq!(literal_text(&store, unchanged_lowercase), "\u{1C8A}");

    let first = string_literal(&mut store, "first");
    let second = string_literal(&mut store, "second");
    let union = store
        .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, vec![first, second])
        .unwrap();
    let mapped = store.get_string_mapping_type(uppercase, union).unwrap();
    assert_eq!(union_texts(&store, mapped), ["FIRST", "SECOND"]);
}

#[test]
fn intrinsic_string_mappings_preserve_symbol_identity_and_transform_patterns() {
    let mut store = checker_store();
    let uppercase = mapping_symbol(&mut store, "Uppercase");
    let lowercase = mapping_symbol(&mut store, "Lowercase");
    let capitalize = mapping_symbol(&mut store, "Capitalize");
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    let numeric_string = store.intrinsic_bootstrap().unwrap().numeric_string_type;

    let generic = store.get_string_mapping_type(uppercase, string).unwrap();
    let TypeData::StringMapping(mapping) = store.type_payload(generic).unwrap().data() else {
        panic!("mapping string must create a generic string-mapping type")
    };
    assert_eq!(mapping.target, string);
    assert_eq!(
        store.type_payload(generic).unwrap().symbol(),
        Some(uppercase)
    );
    assert_eq!(
        store.get_string_mapping_type(uppercase, generic),
        Ok(generic)
    );
    assert_ne!(
        store.get_string_mapping_type(lowercase, string).unwrap(),
        generic
    );

    let mapped_number = store.get_string_mapping_type(uppercase, number).unwrap();
    let TypeData::StringMapping(mapping) = store.type_payload(mapped_number).unwrap().data() else {
        panic!("mapping number must wrap the canonical numeric-string pattern")
    };
    assert_eq!(mapping.target, numeric_string);

    let (texts, types) = parsed_template(&mut store, "type Path = `before-${string}-after`;");
    let pattern = store.get_template_literal_type(&texts, &types).unwrap();
    let upper = store.get_string_mapping_type(uppercase, pattern).unwrap();
    let TypeData::TemplateLiteral(mapped) = store.type_payload(upper).unwrap().data() else {
        panic!("mapping a pattern must retain a template")
    };
    assert_eq!(mapped.texts, ["BEFORE-", "-AFTER"]);
    assert_eq!(mapped.types, [generic]);

    let capped = store.get_string_mapping_type(capitalize, pattern).unwrap();
    let TypeData::TemplateLiteral(mapped) = store.type_payload(capped).unwrap().data() else {
        panic!("capitalization must retain the template")
    };
    assert_eq!(mapped.texts, ["Before-", "-after"]);
    assert_eq!(mapped.types, [string]);

    let (texts, types) = parsed_template(&mut store, "type Prefix = `${string}-after`;");
    let prefix = store.get_template_literal_type(&texts, &types).unwrap();
    let capped_prefix = store.get_string_mapping_type(capitalize, prefix).unwrap();
    let TypeData::TemplateLiteral(mapped) = store.type_payload(capped_prefix).unwrap().data()
    else {
        panic!("capitalization must map an initial placeholder")
    };
    assert_eq!(mapped.texts, ["", "-after"]);
    let TypeData::StringMapping(mapping) = store.type_payload(mapped.types[0]).unwrap().data()
    else {
        panic!("initial placeholder must receive the capitalization mapping")
    };
    assert_eq!(mapping.target, string);
}

#[test]
fn template_cross_product_limit_rejects_one_hundred_thousand_without_allocating() {
    let mut store = checker_store();
    let members = (0..10)
        .map(|index| string_literal(&mut store, &index.to_string()))
        .collect::<Vec<_>>();
    let union = store
        .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, members)
        .unwrap();
    let texts = vec![String::new(); 6];
    let types = vec![union; 5];
    let count = store.type_len();

    assert_eq!(
        store.get_template_cross_product_union_size(&types),
        Ok(100_000)
    );
    let error = store.get_template_literal_type(&texts, &types).unwrap_err();
    assert!(error.to_string().contains("100000"), "{error}");
    assert_eq!(store.type_len(), count);
}

#[test]
fn template_queries_reject_invalid_shapes_foreign_types_and_unknown_mappings() {
    let mut store = checker_store();
    let string = store.intrinsic_bootstrap().unwrap().string_type;
    let other = checker_store();
    let foreign = other.intrinsic_bootstrap().unwrap().string_type;

    assert!(store.get_template_literal_type(&[], &[]).is_err());
    assert!(
        store
            .get_template_literal_type(&[String::new()], &[string])
            .is_err()
    );
    assert!(
        store
            .get_template_literal_type(&[String::new(), String::new()], &[foreign])
            .is_err()
    );

    let unknown = mapping_symbol(&mut store, "NotAnIntrinsic");
    assert!(store.get_string_mapping_type(unknown, string).is_err());
    let uppercase = mapping_symbol(&mut store, "Uppercase");
    assert!(store.get_string_mapping_type(uppercase, foreign).is_err());
}
