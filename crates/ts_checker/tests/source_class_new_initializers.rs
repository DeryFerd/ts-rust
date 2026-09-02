use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(93_210);

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

#[derive(Clone, Copy)]
struct Field {
    declaration: NodeRef,
    initializer: NodeRef,
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
            source: parse("/new-fields.ts", source),
            libraries: LIBRARIES
                .iter()
                .map(|(name, text)| parse(name, text))
                .collect(),
        }
    }

    fn node(&self, id: NodeId) -> NodeRef {
        NodeRef::new(self.source.arena.id(), FILE, id)
    }

    fn class(&self, expected: &str) -> NodeRef {
        self.source
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.source.arena.get(class.name?)?.data else {
                    return None;
                };
                (name.text == expected).then_some(self.node(id))
            })
            .unwrap_or_else(|| panic!("missing class {expected}"))
    }

    fn field(&self, class_name: &str, expected: &str) -> Field {
        let class = self.class(class_name);
        let NodeData::ClassDeclaration(class) = &self.source.arena.get(class.node).unwrap().data
        else {
            unreachable!()
        };
        class
            .members
            .nodes
            .iter()
            .find_map(|&id| {
                let NodeData::PropertyDeclaration(property) = &self.source.arena.get(id)?.data
                else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.source.arena.get(property.name)?.data else {
                    return None;
                };
                (name.text == expected).then(|| Field {
                    declaration: self.node(id),
                    initializer: self.node(property.initializer.expect("initialized field")),
                })
            })
            .unwrap_or_else(|| panic!("missing field {class_name}.{expected}"))
    }

    fn check(&self, field: Field) -> CanonicalCheckerContext<'_> {
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
            .chain([(FILE, &self.source, "\"/new-fields.ts\"".to_owned(), false)])
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
        let mut context = CanonicalCheckerContext::new(
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
        .unwrap();
        let source = context.source_file(FILE).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(source)
                .is_some_and(|links| links.type_checked)
        );
        assert!(
            context
                .store()
                .type_node_links(field.initializer)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        context.check_source_file(FILE).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source)
                .unwrap()
                .type_checked
        );
        context
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

fn member_type(context: &CanonicalCheckerContext<'_>, field: Field) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol(context, field.declaration))
        .and_then(|links| links.resolved_type)
        .expect("the checked field has its real type")
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

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, field: Field, expected: TypeId) {
    assert_eq!(
        context.get_type_at_location(field.initializer).unwrap(),
        expected
    );
    let member = symbol(context, field.declaration);
    let type_links = context.store().type_node_links(field.initializer).cloned();
    let signature_links = context.store().signature_links(field.initializer).cloned();
    let value_links = context.store().value_symbol_links(member).cloned();
    let signature = signature_links
        .as_ref()
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(expected)
    );
    let diagnostics = context.diagnostics().clone();
    let warm_counts = counts(context);

    context.recheck_source_file(FILE).unwrap();
    assert_eq!(member_type(context, field), expected);
    assert_eq!(
        context.get_type_at_location(field.initializer).unwrap(),
        expected
    );
    assert_eq!(
        context.store().type_node_links(field.initializer).cloned(),
        type_links
    );
    assert_eq!(
        context.store().signature_links(field.initializer).cloned(),
        signature_links
    );
    assert_eq!(
        context.store().value_symbol_links(member).cloned(),
        value_links
    );
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(context), warm_counts);
}

#[test]
fn protected_new_set_field_keeps_class_type_parameter() {
    let fixture = Fixture::new(
        "class Listeners<TListener extends Function> { protected listeners = new Set<TListener>(); }\n",
    );
    let field = fixture.field("Listeners", "listeners");
    let mut context = fixture.check(field);
    let result = member_type(&context, field);

    let set = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source("Set")
        .unwrap();
    let set = context.store().get_merged_symbol(set).unwrap();
    let set_target = context.get_declared_type_of_symbol(set).unwrap();
    let TypeData::TypeReference(reference) = context.store().type_payload(result).unwrap().data()
    else {
        panic!("the field must retain the canonical Set reference")
    };
    assert_eq!(reference.object.target, Some(set_target));
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("one Set element type")
    };
    let element = *element;
    let class = fixture.class("Listeners");
    let NodeData::ClassDeclaration(class_data) =
        &fixture.source.arena.get(class.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = class_data
        .type_parameters
        .as_ref()
        .unwrap()
        .nodes
        .as_slice()
    else {
        panic!("one class type parameter")
    };
    let parameter = symbol(&context, fixture.node(*parameter));
    assert_eq!(
        context.get_declared_type_of_symbol(parameter).unwrap(),
        element
    );
    assert_eq!(
        context.store().type_payload(element).unwrap().symbol(),
        Some(parameter)
    );
    assert!(matches!(
        context.store().type_payload(element).unwrap().data(),
        TypeData::TypeParameter(_)
    ));
    assert_eq!(
        context.store().symbol(parameter).unwrap().parent(),
        Some(symbol(&context, class))
    );
    assert_eq!(
        context
            .store()
            .symbol(symbol(&context, field.declaration))
            .unwrap()
            .parent(),
        Some(symbol(&context, class))
    );
    assert_eq!(context.type_to_string(result).unwrap(), "Set<TListener>");
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_replay(&mut context, field, result);
}

#[test]
fn user_constructor_field_keeps_instance_and_member_types() {
    let fixture = Fixture::new(concat!(
        "class Model { value: string = \"ready\"; constructor(count: number) {} }\n",
        "class Owner { model = new Model(1); }\n",
    ));
    let field = fixture.field("Owner", "model");
    let mut context = fixture.check(field);
    let result = member_type(&context, field);
    let model = symbol(&context, fixture.class("Model"));
    assert_eq!(result, context.get_declared_type_of_symbol(model).unwrap());
    assert_eq!(
        context.store().type_payload(result).unwrap().symbol(),
        Some(model)
    );
    assert_eq!(
        member_type(&context, fixture.field("Model", "value")),
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_eq!(context.type_to_string(result).unwrap(), "Model");
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_replay(&mut context, field, result);
}

#[test]
fn new_field_initializer_reports_invalid_constructor_argument() {
    let fixture = Fixture::new(concat!(
        "class Model { value: string = \"ready\"; constructor(count: number) {} }\n",
        "class Owner { model = new Model(\"bad\"); }\n",
    ));
    let field = fixture.field("Owner", "model");
    let mut context = fixture.check(field);
    let result = member_type(&context, field);
    let model = symbol(&context, fixture.class("Model"));
    assert_eq!(result, context.get_declared_type_of_symbol(model).unwrap());
    let NodeData::NewExpression(construction) = &fixture
        .source
        .arena
        .get(field.initializer.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let [argument] = construction.arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("one constructor argument")
    };
    let argument = fixture.node(*argument);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "one invalid constructor argument diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert_replay(&mut context, field, result);
}
