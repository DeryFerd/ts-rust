use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalTypeMapperStore, DeclaredTypeLinks,
    GenericInterfaceMemberError, IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId,
    ValueSymbolLinks,
    links::{
        LateBoundLinks, MembersAndExportsLinks, MembersOrExportsResolutionKind, SymbolNodeLinks,
        TypeNodeLinks,
    },
    type_records::CacheHashKey,
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};
use xxhash_rust::xxh3::Xxh3;

const FILE: FileId = FileId::new(920_260);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")))),+]
    };
}

const LIBRARIES: &[(&str, &str)] = libraries!(
    "es5",
    "es2015",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "decorators",
    "decorators.legacy",
);

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str, bundled_libraries: bool) -> Self {
        let parse = |name: &str, text: &str| {
            let parsed = parse_source_file(text);
            assert!(
                parsed.diagnostics.is_empty(),
                "{name}: {:?}",
                parsed.diagnostics
            );
            parsed
        };
        Self {
            source: parse("/computed-properties.ts", source),
            libraries: if bundled_libraries {
                LIBRARIES
                    .iter()
                    .map(|(name, text)| parse(name, text))
                    .collect()
            } else {
                Vec::new()
            },
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/__typescript/lib/{}\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([(
                FILE,
                &self.source,
                "\"/computed-properties.ts\"".to_owned(),
                false,
            )])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                strict_function_types: true,
                strict_builtin_iterator_return: true,
                no_implicit_any: true,
                no_unchecked_indexed_access: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn library(&self, name: &str) -> (FileId, &ParseResult) {
        let index = LIBRARIES
            .iter()
            .position(|(entry, _)| *entry == name)
            .unwrap();
        (
            FileId::new(u32::try_from(index).unwrap()),
            &self.libraries[index],
        )
    }

    fn variable(&self, name: &str) -> NodeRef {
        let declarations = named(&self.source, FILE, name, SyntaxKind::VariableDeclaration);
        let [declaration] = declarations.as_slice() else {
            panic!("one variable named {name}")
        };
        *declaration
    }

    fn initializer(&self, name: &str) -> NodeRef {
        let declaration = self.variable(name);
        let NodeData::VariableDeclaration(variable) =
            &self.source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        node(&self.source, FILE, variable.initializer.unwrap())
    }

    fn annotation(&self, name: &str) -> NodeRef {
        let declaration = self.variable(name);
        let NodeData::VariableDeclaration(variable) =
            &self.source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        node(&self.source, FILE, variable.type_.unwrap())
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, name: &str, kind: SyntaxKind) -> Vec<NodeRef> {
    parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name_id = match &record.data {
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_id)?.data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .collect()
}

fn interface_members(parsed: &ParseResult, file: FileId, owner: &str) -> Vec<NodeRef> {
    named(parsed, file, owner, SyntaxKind::InterfaceDeclaration)
        .into_iter()
        .flat_map(|declaration| {
            let NodeData::InterfaceDeclaration(interface) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            interface
                .members
                .nodes
                .iter()
                .map(|id| node(parsed, file, *id))
        })
        .collect()
}

fn member_name(parsed: &ParseResult, member: NodeRef) -> Option<NodeId> {
    match &parsed.arena.get(member.node)?.data {
        NodeData::PropertyDeclaration(property) => Some(property.name),
        NodeData::PropertySignatureDeclaration(property) => Some(property.name),
        NodeData::MethodDeclaration(method) => Some(method.name),
        NodeData::MethodSignatureDeclaration(method) => Some(method.name),
        _ => None,
    }
}

fn named_property(parsed: &ParseResult, file: FileId, owner: &str, name: &str) -> NodeRef {
    interface_members(parsed, file, owner)
        .into_iter()
        .find(|member| {
            member_name(parsed, *member).is_some_and(|name_id| {
                matches!(
                    &parsed.arena.get(name_id).unwrap().data,
                    NodeData::Identifier(identifier) if identifier.text == name
                )
            })
        })
        .unwrap_or_else(|| panic!("missing property {owner}.{name}"))
}

fn computed_members(parsed: &ParseResult, file: FileId, owner: &str, key: &str) -> Vec<NodeRef> {
    interface_members(parsed, file, owner)
        .into_iter()
        .filter(|member| {
            let Some(name_id) = member_name(parsed, *member) else {
                return false;
            };
            let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(name_id).unwrap().data
            else {
                return false;
            };
            let expression = &parsed.arena.get(computed.expression).unwrap().data;
            let key_id = match expression {
                NodeData::PropertyAccessExpression(access) => access.name,
                NodeData::Identifier(_) => computed.expression,
                _ => return false,
            };
            matches!(
                &parsed.arena.get(key_id).unwrap().data,
                NodeData::Identifier(identifier) if identifier.text == key
            )
        })
        .collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn table(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SymbolTableId {
    match context.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(interface) => interface.declared_members,
        TypeData::TypeReference(reference) => reference.object.structured.members,
        data => panic!("expected an interface or an instantiated interface, got {data:?}"),
    }
    .expect("the interface members must be prepared")
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the original declaration must retain its signature")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn late_member(
    context: &CanonicalCheckerContext<'_>,
    owner_type: TypeId,
    declarations: &[NodeRef],
    key: SemanticSymbolId,
    flags: SymbolFlags,
    readonly: bool,
) -> (SemanticSymbolId, TypeId) {
    let store = context.store();
    let key_type = store
        .value_symbol_links(key)
        .unwrap()
        .resolved_type
        .unwrap();
    let key_record = store.type_payload(key_type).unwrap();
    assert_eq!(key_record.symbol(), Some(key));
    let TypeData::UniqueEsSymbol(unique) = key_record.data() else {
        panic!("the property key must retain its unique-symbol type")
    };
    let member = store
        .symbol_table(table(context, owner_type))
        .unwrap()
        .get(unique.name.as_ref())
        .unwrap();
    let record = store.symbol(member).unwrap();
    let owner = store.type_payload(owner_type).unwrap().symbol().unwrap();
    assert_ne!(member, key);
    assert_ne!(store.get_parent_of_symbol(key), Some(owner));
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.name(), unique.name.as_ref());
    assert_eq!(record.flags(), flags | SymbolFlags::TRANSIENT);
    assert_eq!(
        record.check_flags(),
        CheckFlags::LATE
            | if readonly {
                CheckFlags::READONLY
            } else {
                CheckFlags::NONE
            }
    );
    assert_eq!(record.declarations(), Some(declarations));
    for declaration in declarations {
        assert_ne!(symbol(context, *declaration), member);
        assert_eq!(
            store
                .symbol_node_links(*declaration)
                .and_then(|links| links.resolved_symbol),
            Some(member)
        );
        let arena = context.file(declaration.file).unwrap().0;
        let name = match &arena.get(declaration.node).unwrap().data {
            NodeData::PropertyDeclaration(property) => property.name,
            NodeData::PropertySignatureDeclaration(property) => property.name,
            NodeData::MethodDeclaration(method) => method.name,
            NodeData::MethodSignatureDeclaration(method) => method.name,
            _ => panic!("a late member must retain its actual property or method declaration"),
        };
        let NodeData::ComputedPropertyName(computed) = &arena.get(name).unwrap().data else {
            panic!("a late member must retain its actual computed name")
        };
        let expression = NodeRef::new(arena.id(), declaration.file, computed.expression);
        assert_eq!(
            store
                .symbol_node_links(expression)
                .and_then(|links| links.resolved_symbol),
            Some(key)
        );
        assert_eq!(
            store
                .type_node_links(expression)
                .and_then(|links| links.resolved_type),
            Some(key_type)
        );
    }
    if let Some(raw_members) = store.symbol(owner).unwrap().members() {
        assert_ne!(raw_members, table(context, owner_type));
        assert_eq!(
            store
                .symbol_table(raw_members)
                .unwrap()
                .get(unique.name.as_ref()),
            None
        );
    }
    assert_eq!(
        store.value_symbol_links(member).unwrap().name_type,
        Some(key_type)
    );
    (member, key_type)
}

#[test]
#[allow(clippy::too_many_lines)]
fn real_set_overloads_keep_computed_property_and_argument_checks() {
    let fixture = Fixture::new(
        r#"const pathSeparators = new Set(["/", "\\", undefined]);
declare const mutableValues: number[];
declare const readonlyValues: readonly number[];
declare const iterableValues: Iterable<number>;
const mutable = new Set(mutableValues);
const frozen = new Set(readonlyValues);
const iterable = new Set(iterableValues);
const badScalar = new Set(1);
const badElement = new Set<number>(["wrong"]);
"#,
        true,
    );
    let (collection_file, collection) = fixture.library("lib.es2015.collection.d.ts");
    let (iterable_file, iterable) = fixture.library("lib.es2015.iterable.d.ts");
    let (well_known_file, well_known) = fixture.library("lib.es2015.symbol.wellknown.d.ts");
    let owners = [
        named(
            collection,
            collection_file,
            "SetConstructor",
            SyntaxKind::InterfaceDeclaration,
        )[0],
        named(
            iterable,
            iterable_file,
            "SetConstructor",
            SyntaxKind::InterfaceDeclaration,
        )[0],
        named(
            well_known,
            well_known_file,
            "SetConstructor",
            SyntaxKind::InterfaceDeclaration,
        )[0],
    ];
    let overloads =
        [(collection_file, collection), (iterable_file, iterable)].map(|(file, parsed)| {
            let constructors = interface_members(parsed, file, "SetConstructor")
                .into_iter()
                .filter(|member| {
                    parsed.arena.get(member.node).unwrap().kind == SyntaxKind::ConstructSignature
                })
                .collect::<Vec<_>>();
            let [constructor] = constructors.as_slice() else {
                panic!("one actual Set constructor declaration in each library")
            };
            *constructor
        });
    let species = computed_members(well_known, well_known_file, "SetConstructor", "species");
    assert_eq!(species.len(), 1);
    let key_declaration =
        named_property(well_known, well_known_file, "SymbolConstructor", "species");
    for query_first in [false, true] {
        let mut context = fixture.context();
        let owner = symbol(&context, owners[0]);
        let key = symbol(&context, key_declaration);
        if query_first {
            context
                .get_type_at_location(fixture.initializer("pathSeparators"))
                .unwrap();
        }
        context.check_source_file(FILE).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2769, 2769]
        );
        assert_eq!(context.get_symbol_declarations(owner).unwrap(), owners);
        for declaration in owners {
            assert_eq!(symbol(&context, declaration), owner);
        }
        let owner_type = context.get_declared_type_of_symbol(owner).unwrap();
        let (property, key_type) = late_member(
            &context,
            owner_type,
            &species,
            key,
            SymbolFlags::PROPERTY,
            true,
        );
        assert_eq!(
            context.store().value_symbol_links(property),
            Some(&ValueSymbolLinks {
                resolved_type: Some(owner_type),
                name_type: Some(key_type),
                ..ValueSymbolLinks::default()
            })
        );
        let TypeData::Interface(interface) =
            context.store().type_payload(owner_type).unwrap().data()
        else {
            panic!("the real SetConstructor owner must remain an interface")
        };
        assert_eq!(
            interface.reference.object.structured.call_signature_count,
            0
        );
        let candidates = interface
            .reference
            .object
            .structured
            .signatures
            .clone()
            .unwrap();
        assert_eq!(
            candidates,
            overloads.map(|declaration| signature(&context, declaration))
        );
        for (candidate, declaration) in candidates.iter().zip(overloads) {
            let record = context.store().signature(*candidate).unwrap();
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(record.type_parameters().len(), 1);
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
        }
        let results = [
            ("pathSeparators", "Set<string | undefined>"),
            ("mutable", "Set<number>"),
            ("frozen", "Set<number>"),
            ("iterable", "Set<number>"),
        ]
        .map(|(name, expected)| {
            let expression = fixture.initializer(name);
            let result = context.get_type_at_location(expression).unwrap();
            assert_eq!(context.type_to_string(result).unwrap(), expected);
            let selected = context
                .store()
                .signature(signature(&context, expression))
                .unwrap();
            assert!(candidates.contains(&selected.target().unwrap()));
            assert_eq!(selected.resolved_return_type(), Some(result));
            (expression, result)
        });
        let TypeData::TypeReference(original) =
            context.store().type_payload(results[0].1).unwrap().data()
        else {
            panic!("the original expression must infer a Set reference")
        };
        let [element] = original.resolved_type_arguments.as_deref().unwrap() else {
            panic!("Set must retain its one inferred type argument")
        };
        let TypeData::Union(elements) = context.store().type_payload(*element).unwrap().data()
        else {
            panic!("strict null checks must retain both string and undefined")
        };
        let intrinsics = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(elements.union.types.len(), 2);
        assert!(elements.union.types.contains(&intrinsics.string_type));
        assert!(elements.union.types.contains(&intrinsics.undefined_type));
        let failed = context
            .get_type_at_location(fixture.initializer("badScalar"))
            .unwrap();
        assert_eq!(context.type_to_string(failed).unwrap(), "Set<unknown>");
        for name in ["badScalar", "badElement"] {
            let expression = fixture.initializer(name);
            let NodeData::NewExpression(construction) =
                &fixture.source.arena.get(expression.node).unwrap().data
            else {
                unreachable!()
            };
            let argument = node(
                &fixture.source,
                FILE,
                construction.arguments.as_ref().unwrap().nodes[0],
            );
            assert!(
                context
                    .diagnostics()
                    .as_slice()
                    .iter()
                    .any(|diagnostic| diagnostic.node == Some(argument))
            );
        }
        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        context.recheck_source_file(FILE).unwrap();
        for (expression, expected) in results {
            assert_eq!(context.get_type_at_location(expression).unwrap(), expected);
        }
        assert_eq!(
            context.get_declared_type_of_symbol(owner).unwrap(),
            owner_type
        );
        assert_eq!(
            late_member(
                &context,
                owner_type,
                &species,
                key,
                SymbolFlags::PROPERTY,
                true
            ),
            (property, key_type)
        );
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn merged_computed_members_keep_self_readonly_optional_and_method_overloads() {
    let fixture = Fixture::new(
        r#"interface Keys {
  readonly self: unique symbol;
  readonly open: unique symbol;
  readonly maybe: unique symbol;
  readonly method: unique symbol;
}
declare const keys: Keys;
interface Owner {
  readonly [keys.self]: Owner;
  [keys.open]: number;
  [keys.maybe]?: string;
  [keys.method](value: number): number;
  [keys.method](value: string): string;
  new(value: number): Owner;
}
interface Owner {
  label: string;
  new(value: string): Owner;
}
declare const owner: Owner;
const self: Owner = owner[keys.self];
const open: number = owner[keys.open];
const maybe: string | undefined = owner[keys.maybe];
owner[keys.open] = 1;
owner[keys.self] = owner;
"#,
        false,
    );
    let declarations = named(
        &fixture.source,
        FILE,
        "Owner",
        SyntaxKind::InterfaceDeclaration,
    );
    let mut context = fixture.context();
    let owner = symbol(&context, declarations[0]);
    let raw_members = context.store().symbol(owner).unwrap().members().unwrap();
    let raw_count = context.store().symbol_table(raw_members).unwrap().len();
    let owner_type = context.get_declared_type_of_symbol(owner).unwrap();
    let intrinsics = context.store().intrinsic_bootstrap().unwrap();
    let (number, string, undefined) = (
        intrinsics.number_type,
        intrinsics.string_type,
        intrinsics.undefined_type,
    );
    let mut identities = Vec::new();
    for (key_name, readonly, flags) in [
        ("self", true, SymbolFlags::PROPERTY),
        ("open", false, SymbolFlags::PROPERTY),
        (
            "maybe",
            false,
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
        ),
        ("method", false, SymbolFlags::METHOD),
    ] {
        let key = symbol(
            &context,
            named_property(&fixture.source, FILE, "Keys", key_name),
        );
        let members = computed_members(&fixture.source, FILE, "Owner", key_name);
        let (property, key_type) =
            late_member(&context, owner_type, &members, key, flags, readonly);
        let value = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        match key_name {
            "self" => assert_eq!(value, owner_type),
            "open" => assert_eq!(value, number),
            "maybe" => {
                assert_eq!(value, string);
                let read = context
                    .get_type_at_location(fixture.initializer("maybe"))
                    .unwrap();
                let TypeData::Union(optional) = context.store().type_payload(read).unwrap().data()
                else {
                    panic!("the optional property read must include undefined")
                };
                assert_eq!(optional.union.types.len(), 2);
                assert!(optional.union.types.contains(&string));
                assert!(optional.union.types.contains(&undefined));
            }
            "method" => {
                let TypeData::Object(method) = context.store().type_payload(value).unwrap().data()
                else {
                    panic!("the computed method must keep its callable type")
                };
                assert_eq!(method.structured.call_signature_count, 2);
                assert_eq!(
                    method.structured.signatures.as_deref().unwrap(),
                    members
                        .iter()
                        .map(|declaration| signature(&context, *declaration))
                        .collect::<Vec<_>>()
                );
            }
            _ => unreachable!(),
        }
        identities.push((members, key, flags, readonly, property, key_type));
    }
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        declarations
    );
    let constructors = interface_members(&fixture.source, FILE, "Owner")
        .into_iter()
        .filter(|member| {
            fixture.source.arena.get(member.node).unwrap().kind == SyntaxKind::ConstructSignature
        })
        .map(|declaration| signature(&context, declaration))
        .collect::<Vec<_>>();
    assert_eq!(constructors.len(), 2);
    let TypeData::Interface(interface) = context.store().type_payload(owner_type).unwrap().data()
    else {
        unreachable!()
    };
    assert_eq!(
        interface.reference.object.structured.signatures.as_deref(),
        Some(constructors.as_slice())
    );
    let members = context
        .store()
        .symbol_table(table(&context, owner_type))
        .unwrap();
    assert_eq!(members.len(), raw_count + identities.len());
    assert!(members.get_source("label").is_some());
    assert_eq!(
        context.store().symbol_table(raw_members).unwrap().len(),
        raw_count
    );
    context.check_source_file(FILE).unwrap();
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2540]
    );
    let before = counts(&context);
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            context.get_declared_type_of_symbol(owner).unwrap(),
            owner_type
        );
        for (members, key, flags, readonly, property, key_type) in &identities {
            assert_eq!(
                late_member(&context, owner_type, members, *key, *flags, *readonly),
                (*property, *key_type)
            );
        }
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn generic_computed_properties_map_each_receiver_in_both_orders() {
    let fixture = Fixture::new(
        r#"declare const key: unique symbol;
interface Box<T> { readonly [key]: T; }
declare const text: Box<string>;
declare const count: Box<number>;
const textValue: string = text[key];
const countValue: number = count[key];
const wrongText: number = text[key];
const wrongCount: string = count[key];
text[key] = "again";
count[key] = 1;
"#,
        false,
    );
    let declaration = named(
        &fixture.source,
        FILE,
        "Box",
        SyntaxKind::InterfaceDeclaration,
    )[0];
    let properties = computed_members(&fixture.source, FILE, "Box", "key");
    for reverse in [false, true] {
        let mut context = fixture.context();
        let owner = symbol(&context, declaration);
        let key = symbol(&context, fixture.variable("key"));
        let mut order = [("text", "textValue"), ("count", "countValue")];
        if reverse {
            order.reverse();
        }
        for (variable, read) in order {
            context
                .get_type_from_type_node(fixture.annotation(variable))
                .unwrap();
            context
                .get_type_at_location(fixture.initializer(read))
                .unwrap();
        }
        let target = context.get_declared_type_of_symbol(owner).unwrap();
        let (source_property, key_type) = late_member(
            &context,
            target,
            &properties,
            key,
            SymbolFlags::PROPERTY,
            true,
        );
        let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
        else {
            panic!("Box must retain its generic interface target")
        };
        let parameter = interface.all_type_parameters.as_ref().unwrap()[0];
        assert_eq!(
            context
                .store()
                .value_symbol_links(source_property)
                .unwrap()
                .resolved_type,
            Some(parameter)
        );
        let intrinsics = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (intrinsics.string_type, intrinsics.number_type);
        let source_name = context
            .store()
            .symbol(source_property)
            .unwrap()
            .name()
            .to_owned();
        let instances = [
            ("text", "textValue", string),
            ("count", "countValue", number),
        ]
        .map(|(variable, read, expected)| {
            let reference = context
                .get_type_from_type_node(fixture.annotation(variable))
                .unwrap();
            assert_eq!(
                context
                    .get_type_at_location(fixture.initializer(read))
                    .unwrap(),
                expected
            );
            let property = context
                .store()
                .symbol_table(table(&context, reference))
                .unwrap()
                .get(source_name.as_ref())
                .unwrap();
            let links = context.store().value_symbol_links(property).unwrap();
            assert_eq!(links.target, Some(source_property));
            assert_eq!(links.resolved_type, Some(expected));
            assert_eq!(links.name_type, Some(key_type));
            assert!(links.mapper.is_some());
            assert_ne!(property, source_property);
            assert_ne!(property, key);
            let record = context.store().symbol(property).unwrap();
            assert_eq!(record.name(), source_name.as_ref());
            assert_eq!(record.parent(), Some(owner));
            assert_eq!(record.declarations(), Some(properties.as_slice()));
            assert_eq!(
                record.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            );
            assert!(
                record
                    .check_flags()
                    .contains(CheckFlags::LATE | CheckFlags::READONLY)
            );
            (
                variable,
                read,
                reference,
                property,
                links.mapper.unwrap(),
                expected,
            )
        });
        assert_ne!(instances[0].2, instances[1].2);
        assert_ne!(instances[0].3, instances[1].3);
        assert_ne!(instances[0].4, instances[1].4);
        assert!(
            !context
                .is_type_assignable_to(instances[0].2, instances[1].2)
                .unwrap()
        );
        assert!(
            !context
                .is_type_assignable_to(instances[1].2, instances[0].2)
                .unwrap()
        );
        context.check_source_file(FILE).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322, 2322, 2540, 2540]
        );
        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for (variable, read, reference, property, mapper, expected) in instances {
                assert_eq!(
                    context
                        .get_type_from_type_node(fixture.annotation(variable))
                        .unwrap(),
                    reference
                );
                assert_eq!(
                    context
                        .get_type_at_location(fixture.initializer(read))
                        .unwrap(),
                    expected
                );
                let links = context.store().value_symbol_links(property).unwrap();
                assert_eq!(links.target, Some(source_property));
                assert_eq!(links.mapper, Some(mapper));
                assert_eq!(links.name_type, Some(key_type));
                assert_eq!(links.resolved_type, Some(expected));
            }
            assert_eq!(counts(&context), before);
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn computed_property_cache_and_key_conflicts_fail_closed() {
    check_late_property_caches();
    let fixture = Fixture::new(
        r#"interface LeftKeys { readonly value: unique symbol; }
interface RightKeys { readonly value: unique symbol; }
declare const leftKeys: LeftKeys;
declare const rightKeys: RightKeys;
interface Identity {
  [leftKeys.value]: string;
  [rightKeys.value]: number;
}
declare const value: Identity;
const left: string = value[leftKeys.value];
const right: number = value[rightKeys.value];
"#,
        false,
    );
    let mut context = fixture.context();
    let owner = symbol(
        &context,
        named(
            &fixture.source,
            FILE,
            "Identity",
            SyntaxKind::InterfaceDeclaration,
        )[0],
    );
    let owner_type = context.get_declared_type_of_symbol(owner).unwrap();
    let declarations = interface_members(&fixture.source, FILE, "Identity");
    assert_eq!(declarations.len(), 2);
    let keys = ["LeftKeys", "RightKeys"].map(|name| {
        symbol(
            &context,
            named_property(&fixture.source, FILE, name, "value"),
        )
    });
    assert_ne!(keys[0], keys[1]);
    assert_eq!(
        context.store().symbol(keys[0]).unwrap().name(),
        context.store().symbol(keys[1]).unwrap().name()
    );
    let left = late_member(
        &context,
        owner_type,
        &declarations[..1],
        keys[0],
        SymbolFlags::PROPERTY,
        false,
    );
    let right = late_member(
        &context,
        owner_type,
        &declarations[1..],
        keys[1],
        SymbolFlags::PROPERTY,
        false,
    );
    assert_ne!(left.0, right.0);
    assert_ne!(left.1, right.1);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let before = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), before);
    assert_eq!(
        late_member(
            &context,
            owner_type,
            &declarations[..1],
            keys[0],
            SymbolFlags::PROPERTY,
            false
        ),
        left
    );
    assert_eq!(
        late_member(
            &context,
            owner_type,
            &declarations[1..],
            keys[1],
            SymbolFlags::PROPERTY,
            false
        ),
        right
    );

    for source in [
        "interface LocalKeys { readonly species: symbol; }\n\
         declare const Symbol: LocalKeys;\n\
         interface Invalid { readonly [Symbol.species]: Invalid; }\n",
        "declare const key: unique symbol;\n\
         interface Invalid { readonly [key]: string; [key](): number; }\n",
        "declare const key: unique symbol;\n\
         interface Invalid { readonly [key]: string; }\n\
         interface Invalid { readonly [key]: number; }\n",
    ] {
        let invalid = Fixture::new(source, false);
        let mut context = invalid.context();
        let owner = symbol(
            &context,
            named(
                &invalid.source,
                FILE,
                "Invalid",
                SyntaxKind::InterfaceDeclaration,
            )[0],
        );
        for _ in 0..2 {
            assert!(
                context.get_declared_type_of_symbol(owner).is_err(),
                "a non-unique or conflicting key must not produce a usable interface"
            );
        }
    }
}

#[allow(clippy::too_many_lines)]
fn check_late_property_caches() {
    let fixture = Fixture::new(
        r#"declare const key: unique symbol;
declare const otherKey: unique symbol;
interface CacheBox<T> {
  readonly [key]: T;
  readonly [otherKey]: T;
}
interface Other {}
"#,
        false,
    );
    let parsed = &fixture.source;
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/computed-property-caches.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
    let bound = files.remove(&FILE).unwrap();
    let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
    store
        .register_source_file(&parsed.arena, parsed.source_file, FILE)
        .unwrap();
    store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        })
        .unwrap();
    let declaration = named(parsed, FILE, "CacheBox", SyntaxKind::InterfaceDeclaration)[0];
    let owner = bound.symbol(declaration).unwrap();
    let other = bound
        .symbol(named(parsed, FILE, "Other", SyntaxKind::InterfaceDeclaration)[0])
        .unwrap();
    let NodeData::InterfaceDeclaration(interface) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter_node] = interface.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the cache control has one actual type parameter")
    };
    let parameter_owner = bound.symbol(node(parsed, FILE, *parameter_node)).unwrap();
    let parameter = store.alloc_type_parameter(Some(parameter_owner)).unwrap();
    assert!(store.set_declared_type_links(
        parameter_owner,
        DeclaredTypeLinks {
            declared_type: Some(parameter),
            ..DeclaredTypeLinks::default()
        }
    ));
    let target = store
        .alloc_interface_type(ObjectFlags::INTERFACE, Some(owner))
        .unwrap();
    assert!(store.set_declared_type_links(
        owner,
        DeclaredTypeLinks {
            declared_type: Some(target),
            ..DeclaredTypeLinks::default()
        }
    ));
    let this_type = store.alloc_type_parameter(Some(owner)).unwrap();
    let mut hasher = Xxh3::new();
    hasher.update(&1_u64.to_le_bytes());
    hasher.update(&parameter.get().to_le_bytes());
    assert!(store.initialize_interface_type_parameters(
        target,
        vec![parameter, this_type],
        0,
        this_type,
        CacheHashKey::new(hasher.digest128())
    ));
    let keys = ["key", "otherKey"].map(|name| bound.symbol(fixture.variable(name)).unwrap());
    let key_types = keys.map(|key| store.alloc_unique_es_symbol_type(key).unwrap());
    let names = keys.map(|key| store.unique_symbol_name(key).unwrap());
    let declarations = ["key", "otherKey"].map(|name| {
        let members = computed_members(parsed, FILE, "CacheBox", name);
        let [declaration] = members.as_slice() else {
            panic!("each cache control property has one computed declaration")
        };
        *declaration
    });
    let early = declarations.map(|declaration| bound.symbol(declaration).unwrap());
    for index in 0..keys.len() {
        let key_annotation = fixture.annotation(["key", "otherKey"][index]);
        assert_eq!(
            parsed.arena.get(key_annotation.node).unwrap().kind,
            SyntaxKind::TypeOperator
        );
        assert!(store.set_type_node_links(
            key_annotation,
            TypeNodeLinks {
                resolved_type: Some(key_types[index]),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(store.set_value_symbol_links(
            keys[index],
            ValueSymbolLinks {
                resolved_type: Some(key_types[index]),
                ..ValueSymbolLinks::default()
            }
        ));
        let (name, annotation) = match &parsed.arena.get(declarations[index].node).unwrap().data {
            NodeData::PropertyDeclaration(property) => (property.name, property.type_.unwrap()),
            NodeData::PropertySignatureDeclaration(property) => (property.name, property.type_),
            _ => panic!("the cache control keeps an actual interface property"),
        };
        let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(name).unwrap().data else {
            unreachable!()
        };
        let expression = node(parsed, FILE, computed.expression);
        assert!(store.set_symbol_node_links(
            expression,
            SymbolNodeLinks {
                resolved_symbol: Some(keys[index])
            }
        ));
        assert!(store.set_type_node_links(
            expression,
            TypeNodeLinks {
                resolved_type: Some(key_types[index]),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(store.set_type_node_links(
            node(parsed, FILE, annotation),
            TypeNodeLinks {
                resolved_type: Some(parameter),
                ..TypeNodeLinks::default()
            }
        ));
    }
    let counts = |store: &CanonicalTypeMapperStore| {
        (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
        )
    };
    let members = store.alloc_symbol_table();
    let occupied = store.alloc_symbol_table();
    assert_eq!(
        store.insert_symbol(occupied, names[0].clone(), early[1]),
        Some(None)
    );
    let before = counts(&store);
    assert_eq!(
        store.create_late_bound_property_symbol(other, early[0], key_types[0], members),
        None
    );
    assert_eq!(
        store.create_late_bound_property_symbol(owner, early[0], key_types[0], occupied),
        None
    );
    assert_eq!(counts(&store), before);
    let late = [0, 1].map(|index| {
        let property = store
            .create_late_bound_property_symbol(owner, early[index], key_types[index], members)
            .unwrap();
        assert_eq!(
            store.symbol(property).unwrap().check_flags(),
            CheckFlags::LATE | CheckFlags::READONLY
        );
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(parameter),
                name_type: Some(key_types[index]),
                ..ValueSymbolLinks::default()
            }
        ));
        property
    });
    let valid_links = store.value_symbol_links(late[0]).cloned().unwrap();
    let before = counts(&store);
    for name_type in [None, Some(key_types[1])] {
        assert!(store.set_value_symbol_links(
            late[0],
            ValueSymbolLinks {
                name_type,
                ..valid_links.clone()
            }
        ));
        assert_eq!(
            store.create_late_bound_property_symbol(owner, early[0], key_types[0], members),
            None
        );
        assert_eq!(counts(&store), before);
        assert!(store.set_value_symbol_links(late[0], valid_links.clone()));
        assert_eq!(
            store.create_late_bound_property_symbol(owner, early[0], key_types[0], members),
            Some(late[0])
        );
    }
    assert!(store.set_late_bound_links(
        early[0],
        LateBoundLinks {
            late_symbol: Some(late[1])
        }
    ));
    assert_eq!(
        store.create_late_bound_property_symbol(owner, early[0], key_types[0], members),
        None
    );
    assert!(store.set_late_bound_links(
        early[0],
        LateBoundLinks {
            late_symbol: Some(late[0])
        }
    ));
    assert_eq!(counts(&store), before);
    let foreign = Fixture::new("declare const foreignKey: unique symbol;", false);
    let mut foreign_context = foreign.context();
    let foreign_key = foreign_context
        .get_type_from_type_node(foreign.annotation("foreignKey"))
        .unwrap();
    assert!(matches!(
        foreign_context
            .store()
            .type_payload(foreign_key)
            .unwrap()
            .data(),
        TypeData::UniqueEsSymbol(_)
    ));
    assert_eq!(
        store.create_late_bound_property_symbol(owner, early[0], foreign_key, members),
        None
    );
    assert_eq!(counts(&store), before);
    assert!(store.set_interface_base_resolution(target, true, None, None));
    assert!(store.set_interface_declared_members(target, true, Some(members), None, None, None));
    let raw_members = store.symbol(owner).unwrap().members().unwrap();
    let resolved_members = store.clone_symbol_table(raw_members).unwrap();
    for (name, property) in names.iter().zip(late) {
        assert_eq!(
            store.insert_symbol(resolved_members, name.clone(), property),
            Some(None)
        );
    }
    let mut resolved_links = MembersAndExportsLinks::default();
    resolved_links.tables[MembersOrExportsResolutionKind::ResolvedMembers as usize] =
        Some(resolved_members);
    assert!(store.set_members_and_exports_links(owner, resolved_links));
    store
        .resolve_generic_interface_members(target, None)
        .unwrap();
    let intrinsics = store.intrinsic_bootstrap().unwrap();
    let (string, number) = (intrinsics.string_type, intrinsics.number_type);
    let references = [string, number].map(|type_| {
        store
            .create_direct_generic_reference_type(target, &[type_])
            .unwrap()
    });
    let properties = references.map(|reference| {
        store
            .resolve_generic_interface_property_by_key(reference, names[0].as_ref(), None)
            .unwrap()
            .unwrap()
            .symbol()
    });
    assert_ne!(properties[0], properties[1]);
    for (property, expected) in properties.into_iter().zip([string, number]) {
        let links = store.value_symbol_links(property).unwrap();
        assert_eq!(links.target, Some(late[0]));
        assert_eq!(links.name_type, Some(key_types[0]));
        assert_eq!(links.resolved_type, Some(expected));
    }
    let good_instance = store.value_symbol_links(properties[0]).cloned().unwrap();
    assert!(store.set_value_symbol_links(
        properties[0],
        ValueSymbolLinks {
            resolved_type: Some(number),
            ..good_instance.clone()
        }
    ));
    let before = counts(&store);
    assert_eq!(
        store.resolve_generic_interface_property_by_key(references[0], names[0].as_ref(), None),
        Err(GenericInterfaceMemberError::InvalidCachedProperty(
            properties[0]
        ))
    );
    assert_eq!(counts(&store), before);
    assert!(store.set_value_symbol_links(properties[0], good_instance));
    assert_eq!(
        store
            .resolve_generic_interface_property_by_key(references[0], names[0].as_ref(), None)
            .unwrap()
            .unwrap()
            .symbol(),
        properties[0]
    );
    assert_eq!(counts(&store), before);
}
