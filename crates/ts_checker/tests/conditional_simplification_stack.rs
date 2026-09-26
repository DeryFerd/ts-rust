use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_700);

// Keep the complete upstream conditionalTypeSimplification.ts declarations.
const SOURCE: &str = concat!(
    "// @target: es2015\r\n",
    "// Repro from #30794\r\n",
    "\r\n",
    "interface AbstractSchema<S, V> {\r\n",
    "  m1<T> (v: T): SchemaType<S, Exclude<V, T>>;\r\n",
    "  m2<T> (v: T): SchemaType<S, T>;\r\n",
    "}\r\n",
    "\r\n",
    "type SchemaType<S, V> = S extends object ? AnySchema<V> : never;\r\n",
    "interface AnySchema<V> extends AnySchemaType<AnySchema<undefined>, V> { }\r\n",
    "interface AnySchemaType<S extends AbstractSchema<any, any>, V> extends AbstractSchema<S, V> { }\r\n",
);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")))),+]
    };
}

// The complete ES2015 default-library closure used by the public compiler fixtures.
const LIBRARIES: &[(&str, &str)] = libraries!(
    "es6",
    "es5",
    "es2015",
    "dom",
    "dom.iterable",
    "webworker.importscripts",
    "scripthost",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "es2018.asynciterable",
    "decorators",
    "decorators.legacy",
);

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            source: parse_source_file(source),
            libraries: LIBRARIES
                .iter()
                .map(|(_, source)| parse_source_file(source))
                .collect(),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let options = CompilerOptions {
            target: ScriptTarget::Es2015,
            ..CompilerOptions::default()
        };
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
            .chain(std::iter::once((
                FILE,
                &self.source,
                "\"/project/conditional-simplification.ts\"".to_owned(),
                false,
            )))
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
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
                    strict_null_checks: options.strict_null_checks,
                    exact_optional_property_types: options.exact_optional_property_types,
                },
                strict_bind_call_apply: options.strict_bind_call_apply,
                strict_builtin_iterator_return: options.strict_builtin_iterator_return,
                strict_function_types: options.strict_function_types,
                strict_property_initialization: options.strict_property_initialization,
                use_unknown_in_catch_variables: options.use_unknown_in_catch_variables,
                no_implicit_any: options.no_implicit_any,
                no_implicit_this: options.no_implicit_this,
                module_kind: options.module,
                name_resolution: (&options).into(),
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn node(&self, id: NodeId) -> NodeRef {
        NodeRef::new(self.source.arena.id(), FILE, id)
    }

    fn declaration(&self, expected: &str) -> NodeRef {
        self.source
            .arena
            .iter()
            .find_map(|(id, record)| {
                let name = match &record.data {
                    NodeData::InterfaceDeclaration(data) => data.name,
                    NodeData::TypeAliasDeclaration(data) => data.name,
                    NodeData::VariableDeclaration(data) => data.name,
                    _ => return None,
                };
                matches!(&self.source.arena.get(name)?.data,
                NodeData::Identifier(name) if name.text == expected)
                .then_some(self.node(id))
            })
            .unwrap_or_else(|| panic!("missing declaration {expected}"))
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn formals(
    checker: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
    declaration: NodeRef,
) -> Vec<TypeId> {
    let parameters = match &fixture.source.arena.get(declaration.node).unwrap().data {
        NodeData::InterfaceDeclaration(data) => data.type_parameters.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.type_parameters.as_ref(),
        _ => panic!("expected a generic source declaration"),
    }
    .unwrap();
    parameters
        .nodes
        .iter()
        .map(|&parameter| {
            let parameter = fixture.node(parameter);
            assert_eq!(
                fixture.source.arena.get(parameter.node).unwrap().parent,
                Some(declaration.node)
            );
            let owner = symbol(checker, parameter);
            let type_ = checker
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let record = checker.store().type_payload(type_).unwrap();
            assert_eq!(record.symbol(), Some(owner));
            let TypeData::TypeParameter(data) = record.data() else {
                panic!("expected the real type parameter");
            };
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            type_
        })
        .collect()
}

fn reference(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> (TypeId, Vec<TypeId>) {
    let record = checker.store().type_payload(type_).unwrap();
    let data = match record.data() {
        TypeData::Interface(data) => &data.reference,
        TypeData::TypeReference(data) => data,
        _ => panic!("expected the actual canonical generic reference"),
    };
    assert_eq!(data.object.mapper, None);
    (
        data.object.target.unwrap(),
        data.resolved_type_arguments.clone().unwrap(),
    )
}

fn single_base(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> TypeId {
    let TypeData::Interface(data) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the declared interface target");
    };
    assert!(data.base_types_resolved);
    assert_eq!(data.resolved_base_constructor_type, None);
    let [base] = data.resolved_base_types.as_deref().unwrap() else {
        panic!("expected the written single base");
    };
    *base
}

fn assert_schema_types(checker: &mut CanonicalCheckerContext<'_>, fixture: &Fixture) {
    let mut declared = Vec::new();
    for name in ["AbstractSchema", "AnySchema", "AnySchemaType"] {
        let declaration = fixture.declaration(name);
        let owner = symbol(checker, declaration);
        let type_ = checker.get_declared_type_of_symbol(owner).unwrap();
        assert_eq!(
            checker
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type,
            Some(type_)
        );
        assert_eq!(
            checker.store().type_payload(type_).unwrap().symbol(),
            Some(owner)
        );
        let parameters = formals(checker, fixture, declaration);
        assert_eq!(reference(checker, type_), (type_, parameters.clone()));
        declared.push((type_, parameters));
    }
    let [
        (abstract_schema, abstract_parameters),
        (any_schema, any_parameters),
        (schema_type, schema_parameters),
    ] = declared.as_slice()
    else {
        unreachable!();
    };
    assert_eq!(abstract_parameters.len(), 2);
    assert_eq!(any_parameters.len(), 1);
    assert_eq!(schema_parameters.len(), 2);
    assert_ne!(abstract_parameters, schema_parameters);
    assert_ne!(any_parameters[0], schema_parameters[1]);
    assert_eq!(
        reference(checker, single_base(checker, *schema_type)),
        (*abstract_schema, schema_parameters.clone())
    );
    let (base_target, arguments) = reference(checker, single_base(checker, *any_schema));
    assert_eq!(base_target, *schema_type);
    assert_eq!(arguments.len(), 2);
    assert_eq!(arguments[1], any_parameters[0]);
    let undefined = checker
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    assert_eq!(
        reference(checker, arguments[0]),
        (*any_schema, vec![undefined])
    );
    let TypeData::TypeParameter(parameter) = checker
        .store()
        .type_payload(schema_parameters[0])
        .unwrap()
        .data()
    else {
        unreachable!();
    };
    let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
    assert_eq!(
        reference(checker, parameter.constraint.unwrap()),
        (*abstract_schema, vec![any, any])
    );
    assert!(checker.store().type_resolution_is_empty());
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    fixture: &Fixture,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.type_alias_len(),
            store.type_resolution_len(),
        ],
        fixture
            .source
            .arena
            .iter()
            .map(|(id, _)| {
                let node = fixture.node(id);
                (
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(owner, _)| {
                (
                    owner,
                    store.declared_type_links(owner).cloned(),
                    store.value_symbol_links(owner).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.diagnostics().clone(),
    )
}

#[test]
fn recursive_schema_arguments_keep_their_real_bases_and_terminate() {
    let fixture = Fixture::new(SOURCE);
    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            let owner = symbol(&checker, fixture.declaration("AnySchema"));
            checker.get_declared_type_of_symbol(owner).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert_schema_types(&mut checker, &fixture);
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let before = snapshot(&checker, &fixture);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_schema_types(&mut checker, &fixture);
            assert_eq!(snapshot(&checker, &fixture), before);
        }
    }
}

#[test]
fn recursive_schema_bases_keep_native_constraint_diagnostics() {
    let source = format!("{SOURCE}declare const invalid: AnySchemaType<number, string>;\r\n");
    let fixture = Fixture::new(&source);
    let declaration = fixture.declaration("invalid");
    let NodeData::VariableDeclaration(variable) =
        &fixture.source.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let annotation = fixture.node(variable.type_.unwrap());
    let NodeData::TypeReferenceNode(reference) =
        &fixture.source.arena.get(annotation.node).unwrap().data
    else {
        unreachable!();
    };
    let arguments = reference.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 2);
    let number = fixture.node(arguments.nodes[0]);
    assert_eq!(
        fixture.source.arena.get(number.node).unwrap().kind,
        SyntaxKind::NumberKeyword
    );
    let mut checker = fixture.context();
    checker.check_source_file(FILE).unwrap();
    assert_schema_types(&mut checker, &fixture);
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.node, Some(number));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2344);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["number", "AbstractSchema<any, any>"]
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'AbstractSchema<any, any>'."
    );
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    let before = snapshot(&checker, &fixture);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert_schema_types(&mut checker, &fixture);
        assert_eq!(snapshot(&checker, &fixture), before);
    }
}
