use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(9_120);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")))),+]
    };
}

// The real ES2015 reference closure, in bundled library priority order.
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

const SOURCE: &str = r#"const pathSeparators = new Set(["/", "\\", undefined]);
declare const expected: Set<string | undefined>;
"#;

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
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
            source: parse("/set-constructor.ts", source),
            libraries: LIBRARIES
                .iter()
                .map(|(name, text)| parse(name, text))
                .collect(),
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
                "\"/set-constructor.ts\"".to_owned(),
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

    fn declaration(&self, library: &str, name: &str, kind: SyntaxKind) -> NodeRef {
        let (file, parsed) = self.library(library);
        named(parsed, file, name, kind)
    }

    fn constructor(&self, library: &str) -> NodeRef {
        let (file, parsed) = self.library(library);
        let owner = named(
            parsed,
            file,
            "SetConstructor",
            SyntaxKind::InterfaceDeclaration,
        );
        let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
        else {
            unreachable!()
        };
        let constructors = interface
            .members
            .nodes
            .iter()
            .filter_map(|&id| {
                (parsed.arena.get(id).unwrap().kind == SyntaxKind::ConstructSignature)
                    .then_some(node(parsed, file, id))
            })
            .collect::<Vec<_>>();
        let [constructor] = constructors.as_slice() else {
            panic!("one real Set overload per library")
        };
        *constructor
    }

    fn construction(&self) -> (NodeRef, NodeRef, NodeRef) {
        let nodes = self
            .source
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::NewExpression(expression) = &record.data else {
                    return None;
                };
                let [argument] = expression.arguments.as_ref().unwrap().nodes.as_slice() else {
                    panic!("one actual constructor argument")
                };
                Some((
                    node(&self.source, FILE, id),
                    node(&self.source, FILE, expression.expression),
                    node(&self.source, FILE, *argument),
                ))
            })
            .collect::<Vec<_>>();
        let [construction] = nodes.as_slice() else {
            panic!("one actual new expression")
        };
        *construction
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, name: &str, kind: SyntaxKind) -> NodeRef {
    let matches = parsed
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
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_id).unwrap().data else {
                return None;
            };
            (identifier.text == name).then_some(node(parsed, file, id))
        })
        .collect::<Vec<_>>();
    let [declaration] = matches.as_slice() else {
        panic!("one declaration of {name} in this file")
    };
    *declaration
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

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the actual declaration or expression retains its signature")
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

fn assert_positive(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
) -> (TypeId, TypeId, SignatureId) {
    let (construction, _, argument) = fixture.construction();
    let result = context.get_type_at_location(construction).unwrap();
    let expected = named(
        &fixture.source,
        FILE,
        "expected",
        SyntaxKind::VariableDeclaration,
    );
    let NodeData::VariableDeclaration(variable) =
        &fixture.source.arena.get(expected.node).unwrap().data
    else {
        unreachable!()
    };
    let expected = context
        .get_type_from_type_node(node(&fixture.source, FILE, variable.type_.unwrap()))
        .unwrap();
    assert_eq!(result, expected);
    assert_eq!(
        context.type_to_string(result).unwrap(),
        "Set<string | undefined>"
    );

    let set = fixture.declaration(
        "lib.es2015.collection.d.ts",
        "Set",
        SyntaxKind::InterfaceDeclaration,
    );
    let set_owner = symbol(context, set);
    let set_target = context.get_declared_type_of_symbol(set_owner).unwrap();
    let TypeData::TypeReference(reference) = context.store().type_payload(result).unwrap().data()
    else {
        panic!("the inferred result must be a real Set reference")
    };
    assert_eq!(reference.object.target, Some(set_target));
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("one Set argument")
    };
    let element = *element;
    let TypeData::Union(union) = context.store().type_payload(element).unwrap().data() else {
        panic!("strict null checks must retain undefined")
    };
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&bootstrap.string_type));
    assert!(union.union.types.contains(&bootstrap.undefined_type));
    let actual = context.get_type_at_location(argument).unwrap();
    let TypeData::TypeReference(array) = context.store().type_payload(actual).unwrap().data()
    else {
        panic!("the actual argument must retain its canonical array type")
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some(&[element][..])
    );

    let selected = assert_constructor(fixture, context, result);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    (result, actual, selected)
}

fn assert_constructor(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    result: TypeId,
) -> SignatureId {
    let (construction, callee, _) = fixture.construction();
    let set = fixture.declaration(
        "lib.es2015.collection.d.ts",
        "Set",
        SyntaxKind::InterfaceDeclaration,
    );
    let set_owner = symbol(context, set);
    let set_value = fixture.declaration(
        "lib.es2015.collection.d.ts",
        "Set",
        SyntaxKind::VariableDeclaration,
    );
    let value_owner = symbol(context, set_value);
    assert_eq!(value_owner, set_owner);
    assert_eq!(
        context.get_symbol_at_location(callee).unwrap(),
        Some(value_owner)
    );
    assert_eq!(
        context.get_symbol_declarations(value_owner).unwrap(),
        [
            set,
            set_value,
            fixture.declaration(
                "lib.es2015.iterable.d.ts",
                "Set",
                SyntaxKind::InterfaceDeclaration
            ),
            fixture.declaration(
                "lib.es2015.symbol.wellknown.d.ts",
                "Set",
                SyntaxKind::InterfaceDeclaration
            ),
        ]
    );

    let collection = fixture.declaration(
        "lib.es2015.collection.d.ts",
        "SetConstructor",
        SyntaxKind::InterfaceDeclaration,
    );
    let iterable = fixture.declaration(
        "lib.es2015.iterable.d.ts",
        "SetConstructor",
        SyntaxKind::InterfaceDeclaration,
    );
    let owner = symbol(context, collection);
    assert_eq!(symbol(context, iterable), owner);
    let well_known = fixture.declaration(
        "lib.es2015.symbol.wellknown.d.ts",
        "SetConstructor",
        SyntaxKind::InterfaceDeclaration,
    );
    assert_eq!(symbol(context, well_known), owner);
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        [collection, iterable, well_known]
    );
    let value = context.get_type_at_location(callee).unwrap();
    let constructor_type = context.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(value, constructor_type);
    let record = context.store().type_payload(value).unwrap();
    let structured = match record.data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("the actual constructor interface must be a structured type"),
    };
    assert_eq!(record.symbol(), Some(owner));
    assert_eq!(structured.call_signature_count, 0);
    let candidates = structured.signatures.clone().unwrap();
    assert_eq!(candidates.len(), 2);
    let declarations = [
        fixture.constructor("lib.es2015.collection.d.ts"),
        fixture.constructor("lib.es2015.iterable.d.ts"),
    ];
    for declaration in declarations {
        let candidate = signature(context, declaration);
        assert!(candidates.contains(&candidate));
        let record = context.store().signature(candidate).unwrap();
        assert_eq!(record.declaration(), Some(declaration));
        assert_eq!(record.type_parameters().len(), 1);
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
    }
    assert_eq!(
        candidates,
        declarations.map(|declaration| signature(context, declaration))
    );
    let selected = signature(context, construction);
    let record = context.store().signature(selected).unwrap();
    assert!(record.type_parameters().is_empty());
    // Native overload resolution tries the later declaration group first.
    assert_eq!(record.target(), Some(candidates[1]));
    assert_eq!(record.declaration(), Some(declarations[1]));
    assert!(record.mapper().is_some());
    assert_eq!(record.resolved_return_type(), Some(result));
    selected
}

fn check_orders(
    fixture: &Fixture,
    check: fn(&Fixture, &mut CanonicalCheckerContext<'_>) -> (TypeId, TypeId, SignatureId),
) {
    let (construction, _, _) = fixture.construction();
    for query_first in [false, true] {
        let mut context = fixture.context();
        let source_root = context.source_file(FILE).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source_root)
                .is_some_and(|links| links.type_checked)
        );
        if query_first {
            context.get_type_at_location(construction).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        let identities = check(fixture, &mut context);
        context.check_source_file(FILE).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source_root)
                .unwrap()
                .type_checked
        );
        assert_eq!(check(fixture, &mut context), identities);
        let nodes = fixture
            .source
            .arena
            .iter()
            .map(|(id, _)| node(&fixture.source, FILE, id))
            .collect::<Vec<_>>();
        let links = nodes
            .iter()
            .map(|&node| {
                (
                    context.store().type_node_links(node).cloned(),
                    context.store().symbol_node_links(node).cloned(),
                    context.store().signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>();
        let warm_counts = counts(&context);
        let diagnostics = context.diagnostics().clone();
        let source_links = context.store().source_file_links(source_root).cloned();
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(check(fixture, &mut context), identities);
            assert_eq!(counts(&context), warm_counts);
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(
                context.store().source_file_links(source_root).cloned(),
                source_links
            );
            assert_eq!(
                nodes
                    .iter()
                    .map(|&node| (
                        context.store().type_node_links(node).cloned(),
                        context.store().symbol_node_links(node).cloned(),
                        context.store().signature_links(node).cloned(),
                    ))
                    .collect::<Vec<_>>(),
                links
            );
        }
    }
}

#[test]
fn real_set_constructor_infers_strict_array_elements_and_reuses_signatures() {
    check_orders(&Fixture::new(SOURCE), assert_positive);
}

fn assert_negative(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
) -> (TypeId, TypeId, SignatureId) {
    let (construction, _, argument) = fixture.construction();
    let result = context.get_type_at_location(construction).unwrap();
    let actual = context.get_type_at_location(argument).unwrap();
    assert_eq!(context.type_to_string(actual).unwrap(), "1");
    assert_eq!(context.type_to_string(result).unwrap(), "Set<unknown>");
    let owner = symbol(
        context,
        fixture.declaration(
            "lib.es2015.collection.d.ts",
            "Set",
            SyntaxKind::InterfaceDeclaration,
        ),
    );
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    let TypeData::TypeReference(reference) = context.store().type_payload(result).unwrap().data()
    else {
        panic!("native overload failure retains a Set reference, not an any fallback")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[context.store().intrinsic_bootstrap().unwrap().unknown_type,][..])
    );
    let selected = assert_constructor(fixture, context, result);

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the bad constructor argument must produce one native overload error")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2769);
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(
        fixture.source.arena.get(argument.node).unwrap().kind,
        SyntaxKind::NumericLiteral
    );
    let range = fixture.source.arena.get(argument.node).unwrap().range;
    assert_eq!((range.start.get(), range.end.get()), (8, 9));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "No overload matches this call.\n",
            "  The last overload gave the following error.\n",
            "    Argument of type 'number' is not assignable to parameter of type 'readonly any[]'.",
        )
    );
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the error must identify only the last failed overload")
    };
    assert_eq!(related.diagnostic.code(), 2771);
    assert_eq!(
        related.node,
        Some(fixture.constructor("lib.es2015.collection.d.ts"))
    );
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "The last overload is declared here."
    );
    (result, actual, selected)
}

#[test]
fn real_set_constructor_rejects_number_and_keeps_native_unknown_recovery() {
    // Pinned Go reports the last overload, but recovers from the first candidate.
    check_orders(&Fixture::new("new Set(1);\n"), assert_negative);
}

fn assert_string_only(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
) -> (TypeId, TypeId, SignatureId) {
    let (construction, _, argument) = fixture.construction();
    let result = context.get_type_at_location(construction).unwrap();
    let actual = context.get_type_at_location(argument).unwrap();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let owner = symbol(
        context,
        fixture.declaration(
            "lib.es2015.collection.d.ts",
            "Set",
            SyntaxKind::InterfaceDeclaration,
        ),
    );
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    let TypeData::TypeReference(reference) = context.store().type_payload(result).unwrap().data()
    else {
        panic!("the string-only constructor must retain its real Set reference")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[string][..])
    );
    assert_eq!(context.type_to_string(result).unwrap(), "Set<string>");
    let TypeData::TypeReference(array) = context.store().type_payload(actual).unwrap().data()
    else {
        panic!("the actual string-only argument must retain its array reference")
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some(&[string][..])
    );
    let selected = assert_constructor(fixture, context, result);
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    (result, actual, selected)
}

#[test]
fn real_set_constructor_keeps_iterator_return_undefined_out_of_string_elements() {
    // Iterator completion must not add undefined to the inferred element type.
    check_orders(
        &Fixture::new(
            r#"const pathSeparators = new Set(["/", "\\"]);
"#,
        ),
        assert_string_only,
    );
}
