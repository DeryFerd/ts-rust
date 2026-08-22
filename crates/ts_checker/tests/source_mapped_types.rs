use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
    canonical_has_syntactic_modifier,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore, DeclaredTypeLinks,
    IntrinsicBootstrapOptions, MappedTypeError, MappedTypeModifiers, MappedTypeRequest, TypeData,
    TypeId, ValueSymbolLinks,
    signatures::IndexFlags,
    type_records::{LiteralValue, RegularLiteralLink},
    types::{AccessFlags, ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "interface Shape {\n",
    "  readonly fixed: string;\n",
    "  maybe?: number;\n",
    "  plain: boolean;\n",
    "}\n",
    "type PartialShape = { [P in keyof Shape]?: Shape[P] };\n",
    "type RequiredShape = { [P in keyof Shape]-?: Shape[P] };\n",
    "type ReadonlyShape = { readonly [P in keyof Shape]: Shape[P] };\n",
    "type MutableShape = { -readonly [P in keyof Shape]-?: Shape[P] };\n",
    "type ComposedShape = { [P in keyof PartialShape]-?: PartialShape[P] };\n",
    "type PickShape = { [P in \"fixed\" | \"maybe\"]: Shape[P] };\n",
    "type RenamedShape = { [P in \"fixed\" | \"plain\" as \"value\"]: Shape[P] };\n",
    "type ConstantShape = { [P in keyof Shape]: boolean };\n",
);

struct Fixture {
    parsed: ParseResult,
    file: FileId,
    bound: BoundFile,
    store: CanonicalTypeMapperStore,
    shape: TypeId,
}

impl Fixture {
    fn new(options: IntrinsicBootstrapOptions) -> Self {
        let parsed = parse_source_file(SOURCE);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(0);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/mapped-types.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (mut symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        for (node, record) in parsed.arena.iter() {
            if matches!(
                record.kind,
                SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
            ) && canonical_has_syntactic_modifier(
                &parsed.arena,
                node,
                SyntaxKind::ReadonlyKeyword,
            ) {
                let declaration = NodeRef::new(parsed.arena.id(), file, node);
                let symbol = bound.symbol(declaration).unwrap();
                assert!(symbols.set_source_property_readonly(symbol, true));
            }
        }
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store.initialize_intrinsic_bootstrap(options).unwrap();

        let shape_declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(shape_declaration).unwrap();
        let shape = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
            .unwrap();
        assert!(store.set_declared_type_links(
            owner,
            DeclaredTypeLinks {
                declared_type: Some(shape),
                ..DeclaredTypeLinks::default()
            },
        ));
        let members = store.symbol(owner).unwrap().members().unwrap();
        let NodeData::InterfaceDeclaration(interface) =
            &parsed.arena.get(shape_declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let mut properties = Vec::with_capacity(interface.members.nodes.len());
        for member in &interface.members.nodes {
            let declaration = NodeRef::new(parsed.arena.id(), file, *member);
            let symbol = bound.symbol(declaration).unwrap();
            let name = store
                .symbol(symbol)
                .unwrap()
                .name()
                .as_utf8()
                .unwrap()
                .to_owned();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let (string, number, boolean, missing) = (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
                bootstrap.undefined_or_missing_type,
            );
            let type_ = match name.as_str() {
                "fixed" => string,
                "maybe" => {
                    if options.strict_null_checks {
                        store
                            .alloc_union_type(ObjectFlags::NONE, vec![missing, number])
                            .unwrap()
                    } else {
                        number
                    }
                }
                "plain" => boolean,
                _ => unreachable!(),
            };
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            properties.push(symbol);
        }
        assert!(store.set_interface_base_resolution(shape, true, None, None));
        assert!(
            store.set_interface_declared_members(shape, true, Some(members), None, None, None,)
        );
        assert!(store.set_structured_type_members(
            shape,
            Some(members),
            Some(properties),
            None,
            None,
            None,
        ));

        Self {
            parsed,
            file,
            bound,
            store,
            shape,
        }
    }

    fn mapped_declaration(&self, alias_name: &str) -> NodeRef {
        self.parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.parsed.arena.get(alias.name)?.data else {
                    return None;
                };
                (name.text == alias_name).then_some(NodeRef::new(
                    self.parsed.arena.id(),
                    self.file,
                    alias.type_,
                ))
            })
            .unwrap_or_else(|| panic!("missing mapped alias {alias_name}"))
    }

    fn source_property(&self, name: &str) -> SemanticSymbolId {
        let TypeData::Interface(interface) = self.store.type_payload(self.shape).unwrap().data()
        else {
            unreachable!()
        };
        self.store
            .symbol_table(interface.declared_members.unwrap())
            .and_then(|table| table.get_source(name))
            .unwrap()
    }

    fn create_mapped(&mut self, alias_name: &str) -> (TypeId, MappedTypeModifiers) {
        self.create_mapped_with_source(alias_name, self.shape)
    }

    fn create_mapped_with_source(
        &mut self,
        alias_name: &str,
        source: TypeId,
    ) -> (TypeId, MappedTypeModifiers) {
        let declaration = self.mapped_declaration(alias_name);
        let (parameter_node, readonly_token, question_token) = {
            let NodeData::MappedTypeNode(mapped) =
                &self.parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            (
                NodeRef::new(declaration.arena, declaration.file, mapped.type_parameter),
                mapped.readonly_token,
                mapped.question_token,
            )
        };
        let parameter_symbol = self.bound.symbol(parameter_node).unwrap();
        let parameter = self
            .store
            .alloc_type_parameter(Some(parameter_symbol))
            .unwrap();
        assert!(self.store.set_declared_type_links(
            parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        let constraint = match alias_name {
            "PickShape" => self.literal_key_union(&["fixed", "maybe"]),
            "RenamedShape" => self.literal_key_union(&["fixed", "plain"]),
            _ => self
                .store
                .alloc_index_type(source, IndexFlags::NONE)
                .unwrap(),
        };
        assert!(self.store.set_type_parameter_resolution(
            parameter,
            Some(constraint),
            None,
            None,
            None
        ));
        let template = if alias_name == "ConstantShape" {
            self.store.intrinsic_bootstrap().unwrap().boolean_type
        } else {
            self.store
                .alloc_indexed_access_type(source, parameter, AccessFlags::NONE)
                .unwrap()
        };
        let symbol = self.bound.symbol(declaration).unwrap();
        let mut request =
            MappedTypeRequest::new(declaration, symbol, parameter, constraint, template, source);
        if alias_name == "RenamedShape" {
            let name_type = self
                .store
                .alloc_literal_type(
                    TypeFlags::STRING_LITERAL,
                    LiteralValue::String("value".to_owned()),
                    RegularLiteralLink::SelfType,
                )
                .unwrap();
            request = request.with_name_type(name_type);
        }
        let modifiers = MappedTypeModifiers::from_token_kinds(
            readonly_token.and_then(|token| self.parsed.arena.get(token).map(|record| record.kind)),
            question_token.and_then(|token| self.parsed.arena.get(token).map(|record| record.kind)),
        )
        .unwrap();
        let type_ = self.store.create_mapped_type(request).unwrap();
        (type_, modifiers)
    }

    fn literal_key_union(&mut self, names: &[&str]) -> TypeId {
        let mut keys = names
            .iter()
            .map(|name| {
                self.store
                    .intrinsic_bootstrap()
                    .and_then(|bootstrap| bootstrap.cached_string_literal_type(name))
                    .unwrap_or_else(|| panic!("homomorphic mapping must initialize key {name}"))
            })
            .collect::<Vec<_>>();
        keys.sort_unstable();
        self.store
            .alloc_union_type(ObjectFlags::NONE, keys)
            .unwrap()
    }
}

fn strict_fixture() -> Fixture {
    Fixture::new(IntrinsicBootstrapOptions {
        strict_null_checks: true,
        exact_optional_property_types: false,
    })
}

#[test]
fn source_partial_creates_lazy_mapped_properties_and_preserves_readonly() {
    let mut fixture = strict_fixture();
    let fixed_source = fixture.source_property("fixed");
    let maybe_source = fixture.source_property("maybe");
    let (mapped, modifiers) = fixture.create_mapped("PartialShape");
    assert_eq!(modifiers, MappedTypeModifiers::INCLUDE_OPTIONAL);

    let before = fixture.store.type_payload(mapped).unwrap();
    assert_eq!(before.object_flags(), ObjectFlags::MAPPED);
    let TypeData::Mapped(before_data) = before.data() else {
        panic!("mapped declarations must use canonical mapped records");
    };
    assert!(before_data.object.structured.members.is_none());

    let members = fixture
        .store
        .resolve_mapped_type_members(mapped, modifiers)
        .unwrap();
    assert_eq!(members.properties().len(), 3);
    for property in members.properties() {
        let symbol = fixture.store.symbol(*property).unwrap();
        assert!(symbol.flags().contains(SymbolFlags::TRANSIENT));
        assert!(symbol.flags().contains(SymbolFlags::OPTIONAL));
        assert!(symbol.check_flags().contains(CheckFlags::MAPPED));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(*property)
                .unwrap()
                .resolved_type,
            None,
        );
    }

    let fixed = fixture
        .store
        .resolve_mapped_type_property(mapped, "fixed", modifiers)
        .unwrap()
        .unwrap();
    assert!(fixed.is_optional());
    assert!(fixed.is_readonly());
    assert_eq!(
        fixture
            .store
            .mapped_symbol_links(fixed.symbol())
            .unwrap()
            .synthetic_origin,
        Some(fixed_source),
    );
    assert_eq!(
        fixture.store.symbol(fixed.symbol()).unwrap().declarations(),
        fixture.store.symbol(fixed_source).unwrap().declarations(),
    );
    let TypeData::Union(fixed_type) = fixture.store.type_payload(fixed.type_id()).unwrap().data()
    else {
        panic!("strict Partial must include undefined in a required property's type");
    };
    let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
    assert!(fixed_type.union.types.contains(&bootstrap.string_type));
    assert!(fixed_type.union.types.contains(&bootstrap.undefined_type));

    let maybe = fixture
        .store
        .resolve_mapped_type_property(mapped, "maybe", modifiers)
        .unwrap()
        .unwrap();
    assert_eq!(
        fixture
            .store
            .mapped_symbol_links(maybe.symbol())
            .unwrap()
            .synthetic_origin,
        Some(maybe_source),
    );
    assert!(maybe.is_optional());
    assert!(!maybe.is_readonly());
}

#[test]
fn source_required_and_readonly_apply_the_full_modifier_matrix() {
    let mut fixture = strict_fixture();
    let (required, required_modifiers) = fixture.create_mapped("RequiredShape");
    let required_maybe = fixture
        .store
        .resolve_mapped_type_property(required, "maybe", required_modifiers)
        .unwrap()
        .unwrap();
    assert!(!required_maybe.is_optional());
    assert_eq!(
        required_maybe.type_id(),
        fixture.store.intrinsic_bootstrap().unwrap().number_type,
    );
    assert!(
        fixture
            .store
            .symbol(required_maybe.symbol())
            .unwrap()
            .check_flags()
            .contains(CheckFlags::STRIP_OPTIONAL)
    );

    let (readonly, readonly_modifiers) = fixture.create_mapped("ReadonlyShape");
    for name in ["fixed", "maybe", "plain"] {
        let property = fixture
            .store
            .resolve_mapped_type_property(readonly, name, readonly_modifiers)
            .unwrap()
            .unwrap();
        assert!(property.is_readonly(), "{name} should be readonly");
        assert_eq!(property.is_optional(), name == "maybe");
    }

    let (mutable, mutable_modifiers) = fixture.create_mapped("MutableShape");
    for name in ["fixed", "maybe", "plain"] {
        let property = fixture
            .store
            .resolve_mapped_type_property(mutable, name, mutable_modifiers)
            .unwrap()
            .unwrap();
        assert!(!property.is_readonly(), "{name} should be mutable");
        assert!(!property.is_optional(), "{name} should be required");
    }
}

#[test]
fn source_required_can_consume_an_unresolved_partial_property_surface() {
    let mut fixture = strict_fixture();
    let (partial, partial_modifiers) = fixture.create_mapped("PartialShape");
    let partial_members = fixture
        .store
        .resolve_mapped_type_members(partial, partial_modifiers)
        .unwrap();
    assert!(partial_members.properties().iter().all(|property| {
        fixture
            .store
            .value_symbol_links(*property)
            .unwrap()
            .resolved_type
            .is_none()
    }));

    let (required, modifiers) = fixture.create_mapped_with_source("ComposedShape", partial);
    for name in ["fixed", "maybe", "plain"] {
        let property = fixture
            .store
            .resolve_mapped_type_property(required, name, modifiers)
            .unwrap()
            .unwrap();
        assert!(!property.is_optional(), "{name} should be required");
        assert_eq!(property.is_readonly(), name == "fixed");
    }
    let maybe = fixture
        .store
        .resolve_mapped_type_property(required, "maybe", modifiers)
        .unwrap()
        .unwrap();
    assert_eq!(
        maybe.type_id(),
        fixture.store.intrinsic_bootstrap().unwrap().number_type,
    );
}

#[test]
fn source_pick_filters_keys_and_preserves_source_modifiers() {
    let mut fixture = strict_fixture();
    let (partial, modifiers) = fixture.create_mapped("PartialShape");
    fixture
        .store
        .resolve_mapped_type_members(partial, modifiers)
        .unwrap();

    let (picked, modifiers) = fixture.create_mapped("PickShape");
    let members = fixture
        .store
        .resolve_mapped_type_members(picked, modifiers)
        .unwrap();
    assert_eq!(members.properties().len(), 2);
    assert!(
        fixture
            .store
            .resolve_mapped_type_property(picked, "plain", modifiers)
            .unwrap()
            .is_none()
    );

    let fixed = fixture
        .store
        .resolve_mapped_type_property(picked, "fixed", modifiers)
        .unwrap()
        .unwrap();
    assert!(!fixed.is_optional());
    assert!(fixed.is_readonly());

    let maybe = fixture
        .store
        .resolve_mapped_type_property(picked, "maybe", modifiers)
        .unwrap()
        .unwrap();
    assert!(maybe.is_optional());
    assert!(!maybe.is_readonly());
}

#[test]
fn source_key_remapping_merges_duplicate_names_without_source_declarations() {
    let mut fixture = strict_fixture();
    let (partial, modifiers) = fixture.create_mapped("PartialShape");
    fixture
        .store
        .resolve_mapped_type_members(partial, modifiers)
        .unwrap();

    let (renamed, modifiers) = fixture.create_mapped("RenamedShape");
    let members = fixture
        .store
        .resolve_mapped_type_members(renamed, modifiers)
        .unwrap();
    assert_eq!(members.properties().len(), 1);
    let property = fixture
        .store
        .resolve_mapped_type_property(renamed, "value", modifiers)
        .unwrap()
        .unwrap();
    assert!(
        fixture
            .store
            .symbol(property.symbol())
            .unwrap()
            .declarations()
            .is_none()
    );
    let key = fixture
        .store
        .mapped_symbol_links(property.symbol())
        .unwrap()
        .key_type
        .unwrap();
    let TypeData::Union(keys) = fixture.store.type_payload(key).unwrap().data() else {
        panic!("duplicate mapped names must retain the complete key union");
    };
    assert_eq!(keys.union.types.len(), 2);
    let TypeData::Union(values) = fixture
        .store
        .type_payload(property.type_id())
        .unwrap()
        .data()
    else {
        panic!("duplicate mapped names must retain the complete value union");
    };
    let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
    assert!(values.union.types.contains(&bootstrap.string_type));
    assert!(
        values.union.types.contains(&bootstrap.boolean_type)
            || values.union.types.contains(&bootstrap.regular_false_type)
                && values.union.types.contains(&bootstrap.regular_true_type),
    );
}

#[test]
fn source_mapped_members_and_property_values_reuse_exact_warm_identities() {
    let mut fixture = strict_fixture();
    let (mapped, modifiers) = fixture.create_mapped("ConstantShape");
    let cold_members = fixture
        .store
        .resolve_mapped_type_members(mapped, modifiers)
        .unwrap();
    let cold_property = fixture
        .store
        .resolve_mapped_type_property(mapped, "fixed", modifiers)
        .unwrap()
        .unwrap();
    let state = (
        fixture.store.type_len(),
        fixture.store.mapper_len(),
        fixture.store.symbol_len(),
        fixture.store.symbol_store().symbol_table_len(),
        fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_literal_cache_len(),
        fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .union_cache_len(),
    );

    for _ in 0..3 {
        assert_eq!(
            fixture
                .store
                .resolve_mapped_type_members(mapped, modifiers)
                .unwrap(),
            cold_members,
        );
        assert_eq!(
            fixture
                .store
                .resolve_mapped_type_property(mapped, "fixed", modifiers)
                .unwrap()
                .unwrap(),
            cold_property,
        );
    }
    assert_eq!(
        (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .string_literal_cache_len(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        ),
        state,
    );
    assert_eq!(
        fixture
            .store
            .resolve_mapped_type_members(mapped, MappedTypeModifiers::INCLUDE_OPTIONAL),
        Err(MappedTypeError::InvalidCachedProperty(
            cold_members.properties()[0],
        )),
    );
}

#[test]
fn source_required_removes_the_exact_optional_missing_sentinel() {
    let mut fixture = Fixture::new(IntrinsicBootstrapOptions {
        strict_null_checks: true,
        exact_optional_property_types: true,
    });
    let (mapped, modifiers) = fixture.create_mapped("RequiredShape");
    let property = fixture
        .store
        .resolve_mapped_type_property(mapped, "maybe", modifiers)
        .unwrap()
        .unwrap();
    assert_eq!(
        property.type_id(),
        fixture.store.intrinsic_bootstrap().unwrap().number_type,
    );
}

#[test]
fn production_source_checking_resolves_homomorphic_mapped_type_aliases() {
    let source = concat!(
        "interface Shape { readonly fixed: string; maybe?: number; plain: boolean }\n",
        "type PartialShape = { [P in keyof Shape]?: Shape[P] };\n",
        "type RequiredShape = { [P in keyof Shape]-?: Shape[P] };\n",
        "type ReadonlyShape = { readonly [P in keyof Shape]: Shape[P] };\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/production-mapped-types.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    for expected in ["PartialShape", "RequiredShape", "ReadonlyShape"] {
        let (alias, mapped) = parsed
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
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(alias).unwrap();
        let resolved = context
            .store()
            .type_alias_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap_or_else(|| panic!("production checking did not resolve {expected}"));
        assert_eq!(
            context
                .store()
                .type_node_links(mapped)
                .and_then(|links| links.resolved_type),
            Some(resolved),
        );
        let TypeData::Mapped(record) = context.store().type_payload(resolved).unwrap().data()
        else {
            panic!("{expected} must resolve to a canonical mapped record");
        };
        assert_eq!(record.declaration, Some(mapped));
        assert!(record.type_parameter.is_some());
        assert!(record.constraint_type.is_some());
    }
}
