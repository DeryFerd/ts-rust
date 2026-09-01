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

const FILE: FileId = FileId::new(9_121);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")))),+]
    };
}

// The same real ES2015 closure and order as the generic library constructor tests.
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

const POSITIVE: &str = "declare const values: Array<string>;\n\
                       const iterable: Iterable<string> = values;\n";
const NEGATIVE: &str = "declare const values: Array<string>;\n\
                       const iterable: Iterable<number> = values;\n";

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
            source: parse("/array-iterable.ts", source),
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
                "\"/array-iterable.ts\"".to_owned(),
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

    fn interface(&self, library: &str, name: &str) -> NodeRef {
        let (file, parsed) = self.library(library);
        named(parsed, file, name, SyntaxKind::InterfaceDeclaration)
    }

    fn iterator_method(&self, interface_name: &str) -> NodeRef {
        let library = "lib.es2015.iterable.d.ts";
        let (file, parsed) = self.library(library);
        let owner = self.interface(library, interface_name);
        let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
        else {
            unreachable!()
        };
        let text = LIBRARIES
            .iter()
            .find(|(name, _)| *name == library)
            .unwrap()
            .1;
        let methods = interface
            .members
            .nodes
            .iter()
            .filter_map(|&id| {
                let record = parsed.arena.get(id).unwrap();
                let range = record.range;
                (record.kind == SyntaxKind::MethodSignature
                    && text[range.start.get() as usize..range.end.get() as usize]
                        .contains("[Symbol.iterator]("))
                .then_some(node(parsed, file, id))
            })
            .collect::<Vec<_>>();
        let [method] = methods.as_slice() else {
            panic!("one actual {interface_name} iterator method")
        };
        *method
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

struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: Option<NodeRef>,
}

fn binding(fixture: &Fixture, name: &str) -> Binding {
    let declaration = named(&fixture.source, FILE, name, SyntaxKind::VariableDeclaration);
    let NodeData::VariableDeclaration(variable) =
        &fixture.source.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    Binding {
        declaration,
        name: node(&fixture.source, FILE, variable.name),
        annotation: node(&fixture.source, FILE, variable.type_.unwrap()),
        initializer: variable
            .initializer
            .map(|id| node(&fixture.source, FILE, id)),
    }
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

fn declared(context: &mut CanonicalCheckerContext<'_>, declaration: NodeRef) -> TypeId {
    let owner = symbol(context, declaration);
    context.get_declared_type_of_symbol(owner).unwrap()
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    actual: TypeId,
    target: TypeId,
    arguments: &[TypeId],
) {
    let TypeData::TypeReference(reference) = context.store().type_payload(actual).unwrap().data()
    else {
        panic!("the type must retain its actual generic library reference")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(arguments)
    );
}

#[derive(Debug, PartialEq, Eq)]
struct IteratorState {
    property: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    returned: TypeId,
}

fn iterator_state(
    context: &mut CanonicalCheckerContext<'_>,
    owner: TypeId,
    declaration: NodeRef,
) -> IteratorState {
    let TypeData::TypeReference(reference) = context.store().type_payload(owner).unwrap().data()
    else {
        unreachable!()
    };
    let properties = reference.object.structured.properties.clone().unwrap();
    let matched = properties
        .into_iter()
        .filter(|&property| {
            context
                .get_symbol_declarations(property)
                .unwrap()
                .contains(&declaration)
        })
        .collect::<Vec<_>>();
    let [property] = matched.as_slice() else {
        panic!("the relation must retain the actual library iterator member")
    };
    let property = *property;
    let callable = context
        .store()
        .value_symbol_links(property)
        .and_then(|links| links.resolved_type)
        .expect("the relation must demand the matched iterator member type");
    let record = context.store().type_payload(callable).unwrap();
    let structured = match record.data() {
        TypeData::Object(object) => &object.structured,
        TypeData::Interface(interface) => &interface.reference.object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("the real iterator method must remain callable"),
    };
    assert_eq!(structured.call_signature_count, 1);
    let signatures = structured.signatures.as_ref().unwrap();
    let [signature] = signatures.as_slice() else {
        panic!("one actual iterator method signature")
    };
    let signature = *signature;
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert!(record.type_parameters().is_empty());
    assert!(record.parameters().is_empty());
    assert_eq!(record.min_argument_count(), 0);
    let returned = context.get_return_type_of_signature(signature).unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(returned)
    );
    IteratorState {
        property,
        callable,
        signature,
        returned,
    }
}

#[derive(Debug, PartialEq, Eq)]
struct State {
    source: TypeId,
    target: TypeId,
    source_iterator: IteratorState,
    target_iterator: IteratorState,
}

fn observe(
    fixture: &Fixture,
    context: &mut CanonicalCheckerContext<'_>,
    compatible: bool,
) -> State {
    let values = binding(fixture, "values");
    let iterable = binding(fixture, "iterable");
    let source = context.get_type_at_location(values.name).unwrap();
    let target = context.get_type_at_location(iterable.name).unwrap();
    let source_owner = symbol(context, values.declaration);
    let target_owner = symbol(context, iterable.declaration);
    assert_eq!(
        context.get_symbol_at_location(values.name),
        Ok(Some(source_owner))
    );
    assert_eq!(
        context.get_symbol_at_location(iterable.name),
        Ok(Some(target_owner))
    );
    let initializer = iterable.initializer.unwrap();
    assert_eq!(
        context.get_symbol_at_location(initializer),
        Ok(Some(source_owner))
    );
    assert_eq!(context.get_type_at_location(initializer), Ok(source));
    assert_eq!(
        context.get_type_from_type_node(values.annotation),
        Ok(source)
    );
    assert_eq!(
        context.get_type_from_type_node(iterable.annotation),
        Ok(target)
    );
    assert_eq!(context.type_to_string(source).unwrap(), "string[]");
    assert_eq!(
        context.type_to_string(target).unwrap(),
        if compatible {
            "Iterable<string>"
        } else {
            "Iterable<number>"
        }
    );

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let element = if compatible {
        string
    } else {
        bootstrap.number_type
    };
    let any = bootstrap.any_type;
    let array = fixture.interface("lib.es5.d.ts", "Array");
    let array_extension = fixture.interface("lib.es2015.iterable.d.ts", "Array");
    assert_eq!(symbol(context, array), symbol(context, array_extension));
    let array_target = declared(context, array);
    assert_eq!(array_target, context.global_types().array_type);
    assert_reference(context, source, array_target, &[string]);
    let iterable_target = declared(
        context,
        fixture.interface("lib.es2015.iterable.d.ts", "Iterable"),
    );
    // The trailing any types are the real library's defaults, not replacement declarations.
    assert_reference(context, target, iterable_target, &[element, any, any]);

    assert_eq!(
        context.is_type_assignable_to(source, target),
        Ok(compatible)
    );
    let source_iterator = iterator_state(context, source, fixture.iterator_method("Array"));
    let target_iterator = iterator_state(context, target, fixture.iterator_method("Iterable"));
    let array_iterator_target = declared(
        context,
        fixture.interface("lib.es2015.iterable.d.ts", "ArrayIterator"),
    );
    let iterator_target = declared(
        context,
        fixture.interface("lib.es2015.iterable.d.ts", "Iterator"),
    );
    assert_reference(
        context,
        source_iterator.returned,
        array_iterator_target,
        &[string],
    );
    assert_reference(
        context,
        target_iterator.returned,
        iterator_target,
        &[element, any, any],
    );
    State {
        source,
        target,
        source_iterator,
        target_iterator,
    }
}

fn assert_diagnostics(fixture: &Fixture, context: &CanonicalCheckerContext<'_>, compatible: bool) {
    if compatible {
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        return;
    }
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "the bad assignment must report exactly one native type error: {:?}",
            context.diagnostics()
        )
    };
    let location = binding(fixture, "iterable").name;
    assert_eq!(diagnostic.node, Some(location));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["string[]", "Iterable<number>"]
    );
    let record = fixture.source.arena.get(location.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::Identifier);
    assert_eq!((record.range.start.get(), record.range.end.get()), (43, 51));
    assert_eq!(&NEGATIVE[43..51], "iterable");
    // Derived from pinned Go relation/formatting code, not a new compiler run.
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        concat!(
            "Type 'string[]' is not assignable to type 'Iterable<number>'.\n",
            "  The types returned by '[Symbol.iterator]().next(...)' are incompatible between these types.\n",
            "    Type 'IteratorResult<string, undefined>' is not assignable to type 'IteratorResult<number, any>'.\n",
            "      Type 'IteratorYieldResult<string>' is not assignable to type 'IteratorResult<number, any>'.\n",
            "        Type 'IteratorYieldResult<string>' is not assignable to type 'IteratorYieldResult<number>'.\n",
            "          Type 'string' is not assignable to type 'number'.",
        )
    );
    assert!(diagnostic.related_information.is_empty());
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

fn check_orders(source: &str, compatible: bool) {
    let fixture = Fixture::new(source);
    let initializer = binding(&fixture, "iterable").initializer.unwrap();
    for query_first in [false, true] {
        let mut context = fixture.context();
        let source_root = context.source_file(FILE).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source_root)
                .is_some_and(|links| links.type_checked)
        );
        let first = if query_first {
            Some(context.get_type_at_location(initializer).unwrap())
        } else {
            None
        };
        context.check_source_file(FILE).unwrap();
        // Check source diagnostics before later queries can prepare missing state.
        assert_diagnostics(&fixture, &context, compatible);
        let diagnostics = context.diagnostics().clone();
        let state = observe(&fixture, &mut context, compatible);
        if let Some(first) = first {
            assert_eq!(first, state.source);
        }
        assert_eq!(context.diagnostics(), &diagnostics);
        assert!(
            context
                .store()
                .source_file_links(source_root)
                .unwrap()
                .type_checked
        );
        context.check_source_file(FILE).unwrap();
        assert_eq!(observe(&fixture, &mut context, compatible), state);
        assert_eq!(context.diagnostics(), &diagnostics);

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
        let source_links = context.store().source_file_links(source_root).cloned();
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_diagnostics(&fixture, &context, compatible);
            assert_eq!(observe(&fixture, &mut context, compatible), state);
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(counts(&context), warm_counts);
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
fn real_array_string_assigns_to_real_iterable_string() {
    check_orders(POSITIVE, true);
}

#[test]
fn real_array_string_rejects_real_iterable_number() {
    check_orders(NEGATIVE, false);
}
