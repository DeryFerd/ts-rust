use std::collections::HashMap;

use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
    canonical_has_syntactic_modifier,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore, DeclaredTypeLinks,
    DirectGenericReferenceError, GenericInterfaceArrayTarget, GenericInterfaceMemberError,
    IntrinsicBootstrapOptions, TypeData, TypeId, ValueSymbolLinks, type_records::CacheHashKey,
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};
use xxhash_rust::xxh3::Xxh3;

const SOURCE: &str = concat!(
    "interface Array<E> {}\n",
    "interface Pair<A, B> {\n",
    "  first: A;\n",
    "  second: B;\n",
    "}\n",
    "interface Link<T, U> {\n",
    "  value: T;\n",
    "  readonly frozen: T;\n",
    "  items: U[];\n",
    "  pair: Pair<T, U>;\n",
    "  next: Link<T, U>;\n",
    "  maybe?: U;\n",
    "  choice: U | \"object\";\n",
    "  tag: \"object\";\n",
    "  self: this;\n",
    "}\n",
);

struct Target {
    type_: TypeId,
    parameters: Vec<TypeId>,
    this_type: TypeId,
    owner: SemanticSymbolId,
}

struct Fixture {
    parsed: ParseResult,
    file: FileId,
    bound: BoundFile,
    store: CanonicalTypeMapperStore,
}

impl Fixture {
    fn new(source: &str, file: FileId) -> Self {
        Self::with_options(source, file, IntrinsicBootstrapOptions::default())
    }

    fn with_options(source: &str, file: FileId, options: IntrinsicBootstrapOptions) -> Self {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-interface-members.ts\""),
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
                let symbol = bound
                    .symbol(declaration)
                    .expect("bound readonly property signature");
                assert!(symbols.set_source_property_readonly(symbol, true));
            }
        }
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store.initialize_intrinsic_bootstrap(options).unwrap();
        Self {
            parsed,
            file,
            bound,
            store,
        }
    }

    fn interface(&self, name: &str) -> NodeRef {
        self.parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &self.parsed.arena.get(interface.name)?.data
                else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(
                    self.parsed.arena.id(),
                    self.file,
                    node,
                ))
            })
            .unwrap_or_else(|| panic!("missing interface {name}"))
    }

    fn initialize_target(&mut self, name: &str) -> Target {
        let declaration = self.interface(name);
        let NodeData::InterfaceDeclaration(interface) =
            &self.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let owner = self.bound.symbol(declaration).unwrap();
        let parameter_nodes = interface
            .type_parameters
            .as_ref()
            .expect("generic test target")
            .nodes
            .clone();
        let mut parameters = Vec::with_capacity(parameter_nodes.len());
        for parameter_node in parameter_nodes {
            let parameter = NodeRef::new(declaration.arena, declaration.file, parameter_node);
            let symbol = self.bound.symbol(parameter).unwrap();
            let type_ = self.store.alloc_type_parameter(Some(symbol)).unwrap();
            assert!(self.store.set_declared_type_links(
                symbol,
                DeclaredTypeLinks {
                    declared_type: Some(type_),
                    ..DeclaredTypeLinks::default()
                },
            ));
            parameters.push(type_);
        }
        let type_ = self
            .store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
            .unwrap();
        assert!(self.store.set_declared_type_links(
            owner,
            DeclaredTypeLinks {
                declared_type: Some(type_),
                ..DeclaredTypeLinks::default()
            },
        ));
        let this_type = self.store.alloc_type_parameter(Some(owner)).unwrap();
        let mut all = parameters.clone();
        all.push(this_type);
        assert!(self.store.initialize_interface_type_parameters(
            type_,
            all,
            0,
            this_type,
            type_list_key(&parameters),
        ));
        Target {
            type_,
            parameters,
            this_type,
            owner,
        }
    }

    fn resolve_declared_properties(
        &mut self,
        target: &Target,
        property_types: &HashMap<&str, TypeId>,
    ) -> Vec<SemanticSymbolId> {
        let declaration = self.interface(
            self.store
                .symbol(target.owner)
                .and_then(|symbol| symbol.name().as_utf8())
                .unwrap(),
        );
        let NodeData::InterfaceDeclaration(interface) =
            &self.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let raw_members = self
            .store
            .symbol(target.owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .expect("generic interface binder target has a raw member table");
        assert!(
            self.store.symbol_table(raw_members).unwrap().len() > interface.members.nodes.len(),
            "the current binder table also contains the interface type parameters",
        );
        let declared_members =
            (!interface.members.nodes.is_empty()).then(|| self.store.alloc_symbol_table());
        let mut properties = Vec::new();
        for member in &interface.members.nodes {
            let member = NodeRef::new(declaration.arena, declaration.file, *member);
            let record = self.parsed.arena.get(member.node).unwrap();
            let NodeData::PropertyDeclaration(property) = &record.data else {
                panic!("test targets contain property signatures only");
            };
            assert_eq!(record.kind, SyntaxKind::PropertyDeclaration);
            let NodeData::Identifier(identifier) =
                &self.parsed.arena.get(property.name).unwrap().data
            else {
                panic!("test properties use identifiers");
            };
            let symbol = self.bound.symbol(member).unwrap();
            let mut type_ = property_types[identifier.text.as_str()];
            let bootstrap = self.store.intrinsic_bootstrap().unwrap();
            if bootstrap.options.strict_null_checks
                && self
                    .store
                    .symbol(symbol)
                    .unwrap()
                    .flags()
                    .contains(SymbolFlags::OPTIONAL)
            {
                let missing_or_undefined = bootstrap.undefined_or_missing_type;
                if type_ != missing_or_undefined
                    && !matches!(
                        self.store.type_payload(type_).unwrap().data(),
                        TypeData::Union(union)
                            if union.union.types.contains(&missing_or_undefined)
                    )
                {
                    type_ = self
                        .store
                        .alloc_union_type(ObjectFlags::NONE, vec![missing_or_undefined, type_])
                        .unwrap();
                }
            }
            assert!(self.store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
            assert_eq!(
                self.store.insert_symbol(
                    declared_members.expect("a declared property owns a member table"),
                    EscapedName::source(identifier.text.clone()),
                    symbol,
                ),
                Some(None),
            );
            properties.push(symbol);
        }
        assert_eq!(
            self.store.symbol(target.owner).unwrap().members(),
            Some(raw_members),
            "declared-member preparation must not replace binder ownership",
        );
        assert_ne!(declared_members, Some(raw_members));
        assert!(
            self.store
                .set_interface_base_resolution(target.type_, true, None, None,)
        );
        assert!(self.store.set_interface_declared_members(
            target.type_,
            true,
            declared_members,
            None,
            None,
            None,
        ));
        properties
    }

    fn declared_property(&self, target: &Target, name: &str) -> SemanticSymbolId {
        let TypeData::Interface(interface) = self.store.type_payload(target.type_).unwrap().data()
        else {
            unreachable!()
        };
        self.store
            .symbol_table(interface.declared_members.unwrap())
            .and_then(|table| table.get_source(name))
            .unwrap_or_else(|| panic!("missing declared property {name}"))
    }

    fn declared_members(&self, target: &Target) -> ts_binder::SymbolTableId {
        let TypeData::Interface(interface) = self.store.type_payload(target.type_).unwrap().data()
        else {
            unreachable!()
        };
        interface.declared_members.unwrap()
    }
}

fn type_list_key(types: &[TypeId]) -> CacheHashKey {
    let mut hasher = Xxh3::new();
    hasher.update(&(types.len() as u64).to_le_bytes());
    for type_ in types {
        hasher.update(&type_.get().to_le_bytes());
    }
    CacheHashKey::new(hasher.digest128())
}

fn counts(store: &CanonicalTypeMapperStore) -> (usize, usize, usize, usize) {
    (
        store.type_len(),
        store.mapper_len(),
        store.symbol_len(),
        store.symbol_store().symbol_table_len(),
    )
}

#[test]
#[allow(clippy::too_many_lines)] // One fixture proves all admitted property-type families together.
fn property_only_generic_interfaces_instantiate_recursively_and_replay_warm() {
    let mut fixture = Fixture::new(SOURCE, FileId::new(2_101));
    let array = fixture.initialize_target("Array");
    let pair = fixture.initialize_target("Pair");
    let link = fixture.initialize_target("Link");
    let (string, number) = {
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        (bootstrap.string_type, bootstrap.number_type)
    };
    let object_literal = fixture
        .store
        .intrinsic_bootstrap()
        .unwrap()
        .cached_string_literal_type("object")
        .unwrap();

    fixture.resolve_declared_properties(
        &pair,
        &HashMap::from([
            ("first", pair.parameters[0]),
            ("second", pair.parameters[1]),
        ]),
    );
    let array_of_u = fixture
        .store
        .create_direct_generic_reference_type(array.type_, &[link.parameters[1]])
        .unwrap();
    let pair_of_t_u = fixture
        .store
        .create_direct_generic_reference_type(pair.type_, &[link.parameters[0], link.parameters[1]])
        .unwrap();
    let choice = fixture
        .store
        .alloc_union_type(ObjectFlags::NONE, vec![link.parameters[1], object_literal])
        .unwrap();
    fixture.resolve_declared_properties(
        &link,
        &HashMap::from([
            ("value", link.parameters[0]),
            ("frozen", link.parameters[0]),
            ("items", array_of_u),
            ("pair", pair_of_t_u),
            ("next", link.type_),
            ("maybe", link.parameters[1]),
            ("choice", choice),
            ("tag", object_literal),
            ("self", link.this_type),
        ]),
    );

    let array_target = Some(GenericInterfaceArrayTarget::new(array.type_));
    let pair_target_members = fixture
        .store
        .resolve_generic_interface_members(pair.type_, array_target)
        .unwrap();
    assert_eq!(pair_target_members.reference(), pair.type_);
    assert_ne!(
        pair_target_members.members(),
        Some(fixture.declared_members(&pair)),
        "the target's instantiated structured table is distinct from its raw declared table",
    );

    let raw_value = fixture.declared_property(&link, "value");
    let raw_tag = fixture.declared_property(&link, "tag");
    let raw_self = fixture.declared_property(&link, "self");
    let target_members = fixture
        .store
        .resolve_generic_interface_members(link.type_, array_target)
        .unwrap();
    assert_eq!(target_members.reference(), link.type_);
    assert_eq!(target_members.target(), link.type_);
    assert_eq!(target_members.properties().len(), 9);
    assert_ne!(
        target_members.members(),
        Some(fixture.declared_members(&link)),
        "the canonical target also receives a separate instantiated table",
    );
    assert_eq!(
        fixture
            .store
            .map_type(target_members.mapper().unwrap(), link.this_type),
        Some(link.type_),
        "the target identity mapper closes its implicit this parameter over itself",
    );
    let target_value = fixture
        .store
        .resolve_generic_interface_property(link.type_, "value", array_target)
        .unwrap()
        .unwrap();
    let target_tag = fixture
        .store
        .resolve_generic_interface_property(link.type_, "tag", array_target)
        .unwrap()
        .unwrap();
    let target_self = fixture
        .store
        .resolve_generic_interface_property(link.type_, "self", array_target)
        .unwrap()
        .unwrap();
    let target_choice = fixture
        .store
        .resolve_generic_interface_property(link.type_, "choice", array_target)
        .unwrap()
        .unwrap();
    assert_ne!(target_value.symbol(), raw_value);
    assert!(
        fixture
            .store
            .symbol(target_value.symbol())
            .unwrap()
            .flags()
            .contains(SymbolFlags::TRANSIENT)
    );
    assert_eq!(
        target_tag.symbol(),
        raw_tag,
        "an invariant resolved source property is reused instead of proxied",
    );
    assert_eq!(target_tag.type_id(), object_literal);
    assert_ne!(target_self.symbol(), raw_self);
    assert_eq!(target_self.type_id(), link.type_);
    assert_eq!(target_choice.type_id(), choice);
    let target_counts = counts(&fixture.store);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_members(link.type_, array_target)
            .unwrap(),
        target_members,
    );
    assert_eq!(counts(&fixture.store), target_counts);

    let reference = fixture
        .store
        .create_direct_generic_reference_type(link.type_, &[string, number])
        .unwrap();
    assert_eq!(
        fixture
            .store
            .create_direct_generic_reference_type(link.type_, &[string, number]),
        Ok(reference),
    );
    let members = fixture
        .store
        .resolve_generic_interface_members(reference, array_target)
        .unwrap();
    assert_eq!(members.reference(), reference);
    assert_eq!(members.target(), link.type_);
    assert_eq!(members.properties().len(), 9);
    assert_eq!(
        fixture
            .store
            .map_type(members.mapper().unwrap(), link.this_type),
        Some(reference),
        "the implicit this parameter maps to the already-interned concrete shell",
    );

    let value = fixture
        .store
        .resolve_generic_interface_property(reference, "value", array_target)
        .unwrap()
        .unwrap();
    let frozen = fixture
        .store
        .resolve_generic_interface_property(reference, "frozen", array_target)
        .unwrap()
        .unwrap();
    let items = fixture
        .store
        .resolve_generic_interface_property(reference, "items", array_target)
        .unwrap()
        .unwrap();
    let nested_pair = fixture
        .store
        .resolve_generic_interface_property(reference, "pair", array_target)
        .unwrap()
        .unwrap();
    let next = fixture
        .store
        .resolve_generic_interface_property(reference, "next", array_target)
        .unwrap()
        .unwrap();
    let maybe = fixture
        .store
        .resolve_generic_interface_property(reference, "maybe", array_target)
        .unwrap()
        .unwrap();
    let choice = fixture
        .store
        .resolve_generic_interface_property(reference, "choice", array_target)
        .unwrap()
        .unwrap();
    let tag = fixture
        .store
        .resolve_generic_interface_property(reference, "tag", array_target)
        .unwrap()
        .unwrap();
    let self_property = fixture
        .store
        .resolve_generic_interface_property(reference, "self", array_target)
        .unwrap()
        .unwrap();
    assert_eq!(value.type_id(), string);
    assert_eq!(frozen.type_id(), string);
    assert!(frozen.is_readonly());
    assert_eq!(
        items.type_id(),
        fixture
            .store
            .create_direct_generic_reference_type(array.type_, &[number])
            .unwrap(),
    );
    assert_eq!(
        nested_pair.type_id(),
        fixture
            .store
            .create_direct_generic_reference_type(pair.type_, &[string, number])
            .unwrap(),
    );
    assert_eq!(next.type_id(), reference);
    assert_eq!(maybe.type_id(), number);
    assert!(maybe.is_optional());
    assert!(!maybe.is_readonly());
    let TypeData::Union(choice_data) = fixture.store.type_payload(choice.type_id()).unwrap().data()
    else {
        panic!("number and a string literal remain an anonymous union")
    };
    assert_eq!(choice_data.union.types.len(), 2);
    assert!(choice_data.union.types.contains(&number));
    assert!(choice_data.union.types.contains(&object_literal));
    assert_eq!(tag.type_id(), object_literal);
    assert_eq!(tag.symbol(), raw_tag);
    assert_ne!(value.symbol(), raw_value);
    assert_ne!(value.symbol(), target_value.symbol());
    assert_eq!(self_property.type_id(), reference);
    assert_ne!(self_property.symbol(), raw_self);
    assert_ne!(self_property.symbol(), target_self.symbol());
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(reference, "missing", array_target),
        Ok(None),
    );

    let nested_members = fixture
        .store
        .resolve_generic_interface_members(nested_pair.type_id(), array_target)
        .unwrap();
    assert_eq!(nested_members.properties().len(), 2);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(nested_pair.type_id(), "second", array_target)
            .unwrap()
            .unwrap()
            .type_id(),
        number,
    );

    let cold_counts = counts(&fixture.store);
    let cold_properties = members.properties().to_vec();
    let warm = fixture
        .store
        .resolve_generic_interface_members(reference, array_target)
        .unwrap();
    assert_eq!(warm.properties(), cold_properties);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(reference, "next", array_target),
        Ok(Some(next)),
    );
    assert_eq!(counts(&fixture.store), cold_counts);

    let other = fixture
        .store
        .create_direct_generic_reference_type(link.type_, &[number, string])
        .unwrap();
    let other_members = fixture
        .store
        .resolve_generic_interface_members(other, array_target)
        .unwrap();
    assert_ne!(other, reference);
    assert_ne!(other_members.properties()[0], members.properties()[0]);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(other, "tag", array_target)
            .unwrap()
            .unwrap()
            .symbol(),
        raw_tag,
    );
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(other, "value", array_target)
            .unwrap()
            .unwrap()
            .type_id(),
        number,
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Cache poisoning cases share one canonical member graph.
fn poisoned_lazy_property_and_foreign_references_fail_closed() {
    let mut fixture = Fixture::new(
        "interface Box<T> { value: T; maybe?: T; tag: \"object\" }\n",
        FileId::new(2_102),
    );
    let box_ = fixture.initialize_target("Box");
    let object_literal = fixture
        .store
        .intrinsic_bootstrap()
        .unwrap()
        .cached_string_literal_type("object")
        .unwrap();
    fixture.resolve_declared_properties(
        &box_,
        &HashMap::from([
            ("value", box_.parameters[0]),
            ("maybe", box_.parameters[0]),
            ("tag", object_literal),
        ]),
    );
    let (string, number) = {
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        (bootstrap.string_type, bootstrap.number_type)
    };
    let raw_tag = fixture.declared_property(&box_, "tag");
    let target_members = fixture
        .store
        .resolve_generic_interface_members(box_.type_, None)
        .unwrap();
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(box_.type_, "tag", None)
            .unwrap()
            .unwrap()
            .symbol(),
        raw_tag,
    );
    let warm_target_counts = counts(&fixture.store);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_members(box_.type_, None)
            .unwrap(),
        target_members,
    );
    assert_eq!(counts(&fixture.store), warm_target_counts);

    let reference = fixture
        .store
        .create_direct_generic_reference_type(box_.type_, &[string])
        .unwrap();
    let value = fixture
        .store
        .resolve_generic_interface_property(reference, "value", None)
        .unwrap()
        .unwrap();
    let links = fixture
        .store
        .value_symbol_links(value.symbol())
        .cloned()
        .unwrap();
    assert!(fixture.store.set_value_symbol_links(
        value.symbol(),
        ValueSymbolLinks {
            resolved_type: Some(number),
            ..links
        },
    ));
    let poisoned_counts = counts(&fixture.store);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(reference, "value", None),
        Err(GenericInterfaceMemberError::InvalidCachedProperty(
            value.symbol()
        )),
    );
    assert_eq!(counts(&fixture.store), poisoned_counts);

    let raw_tag_links = fixture.store.value_symbol_links(raw_tag).cloned().unwrap();
    assert!(fixture.store.set_value_symbol_links(
        raw_tag,
        ValueSymbolLinks {
            target: Some(raw_tag),
            mapper: target_members.mapper(),
            ..raw_tag_links
        },
    ));
    let poisoned_source_counts = counts(&fixture.store);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_property(reference, "tag", None),
        Err(GenericInterfaceMemberError::InvalidMember(raw_tag)),
    );
    assert_eq!(counts(&fixture.store), poisoned_source_counts);

    let mut foreign = Fixture::new("interface Box<T> { value: T }\n", FileId::new(2_103));
    let foreign_box = foreign.initialize_target("Box");
    foreign.resolve_declared_properties(
        &foreign_box,
        &HashMap::from([("value", foreign_box.parameters[0])]),
    );
    let foreign_string = foreign.store.intrinsic_bootstrap().unwrap().string_type;
    let foreign_reference = foreign
        .store
        .create_direct_generic_reference_type(foreign_box.type_, &[foreign_string])
        .unwrap();
    let before = counts(&fixture.store);
    assert!(matches!(
        fixture
            .store
            .resolve_generic_interface_members(foreign_reference, None),
        Err(GenericInterfaceMemberError::Reference(
            DirectGenericReferenceError::InvalidCachedReference { .. }
        )),
    ));
    assert_eq!(counts(&fixture.store), before);
}

#[test]
#[allow(clippy::too_many_lines)] // Composite poison cases must preserve one atomic graph setup.
fn poisoned_composite_property_caches_fail_before_materialization() {
    for property_name in ["items", "nested", "choice"] {
        let mut fixture = Fixture::new(
            concat!(
                "interface Array<E> {}\n",
                "interface Pair<T> { value: T }\n",
                "interface Box<T> {\n",
                "  items: T[];\n",
                "  nested: Pair<T>;\n",
                "  choice: T | \"object\";\n",
                "}\n",
            ),
            FileId::new(2_105),
        );
        let array = fixture.initialize_target("Array");
        let pair = fixture.initialize_target("Pair");
        let box_ = fixture.initialize_target("Box");
        fixture.resolve_declared_properties(&pair, &HashMap::from([("value", pair.parameters[0])]));
        let items = fixture
            .store
            .create_direct_generic_reference_type(array.type_, &[box_.parameters[0]])
            .unwrap();
        let nested = fixture
            .store
            .create_direct_generic_reference_type(pair.type_, &[box_.parameters[0]])
            .unwrap();
        let object = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .cached_string_literal_type("object")
            .unwrap();
        let choice = fixture
            .store
            .alloc_union_type(ObjectFlags::NONE, vec![box_.parameters[0], object])
            .unwrap();
        fixture.resolve_declared_properties(
            &box_,
            &HashMap::from([("items", items), ("nested", nested), ("choice", choice)]),
        );
        let (number, string) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let reference = fixture
            .store
            .create_direct_generic_reference_type(box_.type_, &[number])
            .unwrap();
        let capability = Some(GenericInterfaceArrayTarget::new(array.type_));
        let members = fixture
            .store
            .resolve_generic_interface_members(reference, capability)
            .unwrap();
        let symbol = fixture
            .store
            .symbol_table(members.members().unwrap())
            .and_then(|table| table.get_source(property_name))
            .unwrap();
        let links = fixture.store.value_symbol_links(symbol).cloned().unwrap();
        assert!(links.resolved_type.is_none());
        assert!(fixture.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..links
            },
        ));
        let before = counts(&fixture.store);
        let before_unions = fixture
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .union_cache_len();

        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_members(reference, capability),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol)),
            "a poisoned {property_name} property must invalidate the whole member cache",
        );
        assert_eq!(counts(&fixture.store), before);
        assert_eq!(
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
            before_unions,
        );
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(reference, property_name, capability),
            Err(GenericInterfaceMemberError::InvalidCachedProperty(symbol)),
        );
        assert_eq!(counts(&fixture.store), before);
        assert_eq!(
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
            before_unions,
        );
    }
}

#[test]
fn union_property_reduction_preserves_lazy_and_warm_cache_identity() {
    let mut fixture = Fixture::new(
        "interface Box<T> { choice: T | \"object\" }\n",
        FileId::new(2_106),
    );
    let box_ = fixture.initialize_target("Box");
    let (string, number, any, unknown, never, object) = {
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.any_type,
            bootstrap.unknown_type,
            bootstrap.never_type,
            bootstrap.cached_string_literal_type("object").unwrap(),
        )
    };
    let template = fixture
        .store
        .alloc_union_type(ObjectFlags::NONE, vec![box_.parameters[0], object])
        .unwrap();
    fixture.resolve_declared_properties(&box_, &HashMap::from([("choice", template)]));

    for (argument, expected) in [
        (string, Some(string)),
        (number, None),
        (any, Some(any)),
        (unknown, Some(unknown)),
        (never, Some(object)),
        (object, Some(object)),
    ] {
        let reference = fixture
            .store
            .create_direct_generic_reference_type(box_.type_, &[argument])
            .unwrap();
        let members = fixture
            .store
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        let symbol = members.properties()[0];
        assert_eq!(
            fixture
                .store
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type,
            None,
        );
        let before_demand = counts(&fixture.store);
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_members(reference, None),
            Ok(members),
        );
        assert_eq!(counts(&fixture.store), before_demand);

        let property = fixture
            .store
            .resolve_generic_interface_property(reference, "choice", None)
            .unwrap()
            .unwrap();
        if let Some(expected) = expected {
            assert_eq!(property.type_id(), expected);
        } else {
            let TypeData::Union(union) = fixture
                .store
                .type_payload(property.type_id())
                .unwrap()
                .data()
            else {
                panic!("number and a string literal must remain a union")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&number));
            assert!(union.union.types.contains(&object));
        }
        let after_demand = counts(&fixture.store);
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(reference, "choice", None),
            Ok(Some(property)),
        );
        assert_eq!(counts(&fixture.store), after_demand);
    }
}

#[test]
fn invariant_and_empty_generic_interfaces_resolve_without_transient_properties() {
    let mut fixture = Fixture::new(
        concat!(
            "interface Empty<T> {}\n",
            "interface Label<T> { label: string }\n",
        ),
        FileId::new(2_107),
    );
    let empty = fixture.initialize_target("Empty");
    let label = fixture.initialize_target("Label");
    let (string, number) = {
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        (bootstrap.string_type, bootstrap.number_type)
    };
    fixture.resolve_declared_properties(&empty, &HashMap::new());
    fixture.resolve_declared_properties(&label, &HashMap::from([("label", string)]));

    for target in [&empty, &label] {
        let source_symbols = fixture.store.symbol_len();
        let target_members = fixture
            .store
            .resolve_generic_interface_members(target.type_, None)
            .unwrap();
        assert_eq!(fixture.store.symbol_len(), source_symbols);
        let target_state = counts(&fixture.store);
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_members(target.type_, None),
            Ok(target_members),
        );
        assert_eq!(counts(&fixture.store), target_state);

        let reference = fixture
            .store
            .create_direct_generic_reference_type(target.type_, &[number])
            .unwrap();
        let before_symbols = fixture.store.symbol_len();
        let members = fixture
            .store
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        assert_eq!(fixture.store.symbol_len(), before_symbols);
        assert_eq!(
            members.properties().len(),
            usize::from(target.type_ == label.type_)
        );
        if target.type_ == label.type_ {
            let raw = fixture.declared_property(&label, "label");
            let property = fixture
                .store
                .resolve_generic_interface_property(reference, "label", None)
                .unwrap()
                .unwrap();
            assert_eq!(property.symbol(), raw);
            assert_eq!(property.type_id(), string);
        } else {
            assert_eq!(
                fixture
                    .store
                    .resolve_generic_interface_property(reference, "missing", None),
                Ok(None),
            );
            assert_eq!(members.members(), None);
        }
        let warm_state = counts(&fixture.store);
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_members(reference, None),
            Ok(members),
        );
        assert_eq!(counts(&fixture.store), warm_state);
    }
}

#[test]
fn strict_optional_generic_properties_preserve_the_canonical_optional_sentinel() {
    for exact_optional_property_types in [false, true] {
        let mut fixture = Fixture::with_options(
            "interface Box<T> { value?: T }\n",
            FileId::new(2_108),
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types,
            },
        );
        let box_ = fixture.initialize_target("Box");
        fixture.resolve_declared_properties(&box_, &HashMap::from([("value", box_.parameters[0])]));
        let (string, sentinel) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_or_missing_type)
        };
        let raw = fixture.declared_property(&box_, "value");
        let template = fixture
            .store
            .value_symbol_links(raw)
            .unwrap()
            .resolved_type
            .unwrap();
        let TypeData::Union(template_union) = fixture.store.type_payload(template).unwrap().data()
        else {
            panic!("strict optional source properties must retain their optional sentinel")
        };
        assert!(template_union.union.types.contains(&box_.parameters[0]));
        assert!(template_union.union.types.contains(&sentinel));

        let target_property = fixture
            .store
            .resolve_generic_interface_property(box_.type_, "value", None)
            .unwrap()
            .unwrap();
        assert_eq!(target_property.type_id(), template);
        assert!(target_property.is_optional());

        let reference = fixture
            .store
            .create_direct_generic_reference_type(box_.type_, &[string])
            .unwrap();
        let property = fixture
            .store
            .resolve_generic_interface_property(reference, "value", None)
            .unwrap_or_else(|error| {
                panic!(
                    "strict optional instantiation failed with exactOptionalPropertyTypes={exact_optional_property_types}: {error:?}"
                )
            })
            .unwrap();
        let TypeData::Union(instantiated) = fixture
            .store
            .type_payload(property.type_id())
            .unwrap()
            .data()
        else {
            panic!("strict optional instantiated properties must remain unions")
        };
        assert_eq!(instantiated.union.types.len(), 2);
        assert!(instantiated.union.types.contains(&string));
        assert!(instantiated.union.types.contains(&sentinel));
        let warm = counts(&fixture.store);
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(reference, "value", None),
            Ok(Some(property)),
        );
        assert_eq!(counts(&fixture.store), warm);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One source proves member identity, reads, and assignability.
fn production_source_checks_generic_interface_properties_and_assignability() {
    let parsed = parse_source_file(concat!(
        "interface Box<T> { value: T; readonly label: string }\n",
        "declare const text: Box<string>;\n",
        "const value: string = text.value;\n",
        "const label: string = text.label;\n",
        "const mismatch: Box<number> = text;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_109);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-interface-production.ts\""),
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
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();

    context.check_source_file(file).unwrap();

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        vec![2322],
    );
    let text_declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "text").then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let text = context
        .file(file)
        .unwrap()
        .1
        .symbol(text_declaration)
        .unwrap();
    let text_type = context
        .store()
        .value_symbol_links(text)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let TypeData::TypeReference(reference) =
        context.store().type_payload(text_type).unwrap().data()
    else {
        panic!("the ambient source variable must retain its Box<string> reference")
    };
    let members = reference.object.structured.members.unwrap();
    let table = context.store().symbol_table(members).unwrap();
    let value = table.get_source("value").unwrap();
    let label = table.get_source("label").unwrap();
    assert!(
        context
            .store()
            .symbol(value)
            .unwrap()
            .flags()
            .contains(SymbolFlags::TRANSIENT)
    );
    assert!(
        context
            .store()
            .symbol(label)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY)
    );
    assert!(
        !context
            .store()
            .symbol(label)
            .unwrap()
            .flags()
            .contains(SymbolFlags::TRANSIENT)
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        context
            .store()
            .value_symbol_links(value)
            .unwrap()
            .resolved_type,
        Some(string),
    );
    for expected in ["value", "label"] {
        let access = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
#[allow(clippy::too_many_lines)] // The class boundary needs a complete canonical generic shell.
fn composite_union_members_resolve_while_class_boundaries_remain_explicit() {
    let mut fixture = Fixture::new(
        concat!(
            "class Box<T> { value!: T }\n",
            "interface Pair<T> { value: T }\n",
            "interface Bad<T> { mixed: Pair<T> | T }\n",
        ),
        FileId::new(2_104),
    );
    let pair = fixture.initialize_target("Pair");
    let bad = fixture.initialize_target("Bad");
    fixture.resolve_declared_properties(&pair, &HashMap::from([("value", pair.parameters[0])]));
    let pair_of_t = fixture
        .store
        .create_direct_generic_reference_type(pair.type_, &[bad.parameters[0]])
        .unwrap();
    let mixed = fixture
        .store
        .alloc_union_type(ObjectFlags::NONE, vec![pair_of_t, bad.parameters[0]])
        .unwrap();
    fixture.resolve_declared_properties(&bad, &HashMap::from([("mixed", mixed)]));
    let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
    let bad_reference = fixture
        .store
        .create_direct_generic_reference_type(bad.type_, &[string])
        .unwrap();
    let members = fixture
        .store
        .resolve_generic_interface_members(bad_reference, None)
        .unwrap();
    assert_eq!(members.properties().len(), 1);
    let property = fixture
        .store
        .resolve_generic_interface_property(bad_reference, "mixed", None)
        .unwrap()
        .unwrap();
    let pair_of_string = fixture
        .store
        .create_direct_generic_reference_type(pair.type_, &[string])
        .unwrap();
    let TypeData::Union(instantiated) = fixture
        .store
        .type_payload(property.type_id())
        .unwrap()
        .data()
    else {
        panic!("the composite generic property must remain a union")
    };
    assert_eq!(instantiated.union.types.len(), 2);
    assert!(instantiated.union.types.contains(&pair_of_string));
    assert!(instantiated.union.types.contains(&string));
    let warm = counts(&fixture.store);
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_members(bad_reference, None),
        Ok(members),
    );
    assert_eq!(counts(&fixture.store), warm);

    let class_declaration = fixture
        .parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                node,
            ))
        })
        .unwrap();
    let NodeData::ClassDeclaration(class) = &fixture
        .parsed
        .arena
        .get(class_declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let owner = fixture.bound.symbol(class_declaration).unwrap();
    assert!(
        fixture
            .store
            .symbol(owner)
            .unwrap()
            .flags()
            .contains(SymbolFlags::CLASS)
    );
    let parameter_node = NodeRef::new(
        class_declaration.arena,
        class_declaration.file,
        class.type_parameters.as_ref().unwrap().nodes[0],
    );
    let parameter_symbol = fixture.bound.symbol(parameter_node).unwrap();
    let parameter = fixture
        .store
        .alloc_type_parameter(Some(parameter_symbol))
        .unwrap();
    assert!(fixture.store.set_declared_type_links(
        parameter_symbol,
        DeclaredTypeLinks {
            declared_type: Some(parameter),
            ..DeclaredTypeLinks::default()
        },
    ));
    let class_type = fixture
        .store
        .alloc_interface_type(ObjectFlags::CLASS, Some(owner))
        .unwrap();
    assert!(fixture.store.set_declared_type_links(
        owner,
        DeclaredTypeLinks {
            declared_type: Some(class_type),
            ..DeclaredTypeLinks::default()
        },
    ));
    let this_type = fixture.store.alloc_type_parameter(Some(owner)).unwrap();
    assert!(fixture.store.initialize_interface_type_parameters(
        class_type,
        vec![parameter, this_type],
        0,
        this_type,
        type_list_key(&[parameter]),
    ));
    let class_reference = fixture
        .store
        .create_direct_generic_reference_type(class_type, &[string])
        .unwrap();
    assert_eq!(
        fixture
            .store
            .resolve_generic_interface_members(class_reference, None),
        Err(GenericInterfaceMemberError::UnsupportedTarget(class_type)),
    );
}
