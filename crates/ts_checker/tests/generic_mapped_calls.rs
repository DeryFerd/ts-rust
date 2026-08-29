use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalImportCallMode,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId,
    signatures::IndexFlags,
    type_records::{LiteralValue, TypeParameterData},
    types::TypeFlags,
};
use ts_core::{TextPos, TextRange};
use ts_options::{CompilerOptions, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE_FILE: FileId = FileId::new(202_101);

// Exact upstream fixture, including spacing, comments, and the final LF.
const ORIGINAL: &str = concat!(
    "// @target: es2015\n",
    "declare function pick<O, T extends keyof O>(keys: T[], obj?: O): Pick<O, T>;\n",
    "const _    = pick(['b'], { a: 'a', b: 'b' }); // T: \"b\"\n",
    "const {  } = pick(['b'], { a: 'a', b: 'b' }); // T: \"b\" | \"a\" ??? (before fix)\n",
);

// The complete lib.es6.d.ts closure in the compiler's semantic file order.
const LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es6.d.ts",
        include_str!("../../ts_bundled/libs/lib.es6.d.ts"),
    ),
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.es2015.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.d.ts"),
    ),
    (
        "lib.dom.d.ts",
        include_str!("../../ts_bundled/libs/lib.dom.d.ts"),
    ),
    (
        "lib.dom.iterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.dom.iterable.d.ts"),
    ),
    (
        "lib.webworker.importscripts.d.ts",
        include_str!("../../ts_bundled/libs/lib.webworker.importscripts.d.ts"),
    ),
    (
        "lib.scripthost.d.ts",
        include_str!("../../ts_bundled/libs/lib.scripthost.d.ts"),
    ),
    (
        "lib.es2015.core.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts"),
    ),
    (
        "lib.es2015.collection.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.collection.d.ts"),
    ),
    (
        "lib.es2015.generator.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.generator.d.ts"),
    ),
    (
        "lib.es2015.iterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.iterable.d.ts"),
    ),
    (
        "lib.es2015.promise.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.promise.d.ts"),
    ),
    (
        "lib.es2015.proxy.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.proxy.d.ts"),
    ),
    (
        "lib.es2015.reflect.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.reflect.d.ts"),
    ),
    (
        "lib.es2015.symbol.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
    ),
    (
        "lib.es2015.symbol.wellknown.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.wellknown.d.ts"),
    ),
    (
        "lib.es2018.asynciterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2018.asynciterable.d.ts"),
    ),
    (
        "lib.decorators.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "lib.decorators.legacy.d.ts",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
    path: &'static str,
}

impl Fixture {
    fn new(source: &str, path: &'static str) -> Self {
        let source = parse_source_file(source);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let libraries = LIBRARIES
            .iter()
            .map(|(name, text)| {
                let parsed = parse_source_file(text);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{name}: {:?}",
                    parsed.diagnostics
                );
                parsed
            })
            .collect();
        Self {
            source,
            libraries,
            path,
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        // CanonicalCheckerOptions::default does not apply the compiler's strict defaults.
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
                SOURCE_FILE,
                &self.source,
                format!("\"/project/{}\"", self.path),
                false,
            )))
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
                import_call_mode: CanonicalImportCallMode::Unsupported,
                check_bigint_target: true,
                name_resolution: (&options).into(),
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn function(&self) -> FunctionParts {
        let arena = &self.source.arena;
        let node_ref = |node| NodeRef::new(arena.id(), SOURCE_FILE, node);
        arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::FunctionDeclaration(function) = &record.data else {
                    return None;
                };
                let return_type = function.type_.unwrap();
                let NodeData::TypeReferenceNode(reference) = &arena.get(return_type).unwrap().data
                else {
                    panic!("expected a mapped alias return annotation");
                };
                Some(FunctionParts {
                    declaration: node_ref(node),
                    name: node_ref(function.name.unwrap()),
                    return_type: node_ref(return_type),
                    return_name: node_ref(reference.type_name),
                    type_parameters: function
                        .type_parameters
                        .as_ref()
                        .unwrap()
                        .nodes
                        .iter()
                        .copied()
                        .map(node_ref)
                        .collect(),
                })
            })
            .unwrap()
    }

    fn calls(&self) -> Vec<CallParts> {
        let arena = &self.source.arena;
        let node_ref = |node| NodeRef::new(arena.id(), SOURCE_FILE, node);
        let mut calls = arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::CallExpression(call) = &record.data else {
                    return None;
                };
                let [array, object] = call.arguments.nodes.as_slice() else {
                    panic!("expected keys and object arguments");
                };
                let NodeData::VariableDeclaration(variable) =
                    &arena.get(record.parent.unwrap()).unwrap().data
                else {
                    panic!("expected a call that initializes the original binding");
                };
                Some(CallParts {
                    node: node_ref(node),
                    binding: node_ref(variable.name),
                    callee: node_ref(call.expression),
                    array: node_ref(*array),
                    object: node_ref(*object),
                })
            })
            .collect::<Vec<_>>();
        calls.sort_by_key(|call| arena.get(call.node.node).unwrap().range.start);
        calls
    }
}

struct FunctionParts {
    declaration: NodeRef,
    name: NodeRef,
    return_type: NodeRef,
    return_name: NodeRef,
    type_parameters: Vec<NodeRef>,
}

struct CallParts {
    node: NodeRef,
    binding: NodeRef,
    callee: NodeRef,
    array: NodeRef,
    object: NodeRef,
}

#[derive(Debug, Eq, PartialEq)]
struct GenericSnapshot {
    callable: TypeId,
    signature: SignatureId,
    owner: SemanticSymbolId,
    type_parameters: Vec<(TypeId, TypeParameterData)>,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    return_type: TypeId,
}

#[derive(Debug, Eq, PartialEq)]
struct CallSnapshot {
    node: NodeRef,
    return_type: TypeId,
    signature: SignatureId,
    object: TypeId,
    key: TypeId,
    array: TypeId,
    property: SemanticSymbolId,
    origin: SemanticSymbolId,
}

fn bound_symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn alias_arguments(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    owner: SemanticSymbolId,
) -> [TypeId; 2] {
    let record = checker.store().type_payload(type_).unwrap();
    assert!(matches!(record.data(), TypeData::Mapped(_)));
    let alias = checker.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(alias.symbol(), Some(owner));
    alias.type_arguments().unwrap().try_into().unwrap()
}

fn alias_owner(checker: &mut CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let raw = checker
        .store()
        .symbol_table(checker.globals())
        .unwrap()
        .get_source(name)
        .unwrap();
    let owner = checker.store().get_merged_symbol(raw).unwrap();
    let declarations = checker.get_symbol_declarations(owner).unwrap();
    let [declaration] = declarations else {
        panic!("expected one source-owned mapped alias");
    };
    if name == "Pick" {
        let es5_index = LIBRARIES
            .iter()
            .position(|(name, _)| *name == "lib.es5.d.ts")
            .unwrap();
        assert_eq!(
            declaration.file,
            FileId::new(u32::try_from(es5_index).unwrap())
        );
        assert!(
            checker
                .file(declaration.file)
                .unwrap()
                .1
                .source_facts()
                .unwrap()
                .is_default_library()
        );
    } else {
        assert_eq!(declaration.file, SOURCE_FILE);
    }
    owner
}

#[allow(clippy::too_many_lines)] // Keep the declared signature and its parameter ownership together.
fn generic_snapshot(
    checker: &mut CanonicalCheckerContext<'_>,
    function: &FunctionParts,
    alias: SemanticSymbolId,
) -> GenericSnapshot {
    let owner = bound_symbol(checker, function.declaration);
    assert_eq!(
        checker.get_symbol_at_location(function.name).unwrap(),
        Some(owner)
    );
    assert_eq!(
        checker
            .get_symbol_at_location(function.return_name)
            .unwrap(),
        Some(alias)
    );
    let callable = checker.get_type_at_location(function.name).unwrap();
    let signature = checker
        .store()
        .signature_links(function.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let return_type = checker.get_return_type_of_signature(signature).unwrap();
    assert_eq!(
        checker
            .get_type_from_type_node(function.return_type)
            .unwrap(),
        return_type
    );
    let parameters = checker
        .store()
        .signature(signature)
        .unwrap()
        .parameters()
        .iter()
        .map(|&symbol| {
            let type_ = checker
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap();
            (symbol, type_)
        })
        .collect::<Vec<_>>();
    let type_parameters = function
        .type_parameters
        .iter()
        .map(|&declaration| {
            let symbol = bound_symbol(checker, declaration);
            let type_ = checker
                .store()
                .declared_type_links(symbol)
                .unwrap()
                .declared_type
                .unwrap();
            let record = checker.store().type_payload(type_).unwrap();
            assert_eq!(record.symbol(), Some(symbol));
            assert_eq!(
                checker.get_symbol_declarations(symbol).unwrap(),
                [declaration]
            );
            let TypeData::TypeParameter(parameter) =
                checker.store().type_payload(type_).unwrap().data()
            else {
                panic!("the generic signature must retain its declared parameters");
            };
            (type_, parameter.clone())
        })
        .collect::<Vec<_>>();
    let parameter_types = type_parameters
        .iter()
        .map(|(type_, _)| *type_)
        .collect::<Vec<_>>();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(function.declaration));
    assert_eq!(record.type_parameters(), parameter_types);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        alias_arguments(checker, return_type, alias).as_slice(),
        parameter_types.as_slice()
    );
    let [(object, _), (key, key_parameter)] = type_parameters.as_slice() else {
        panic!("expected the original O and T parameters");
    };
    let TypeData::Index(constraint) = checker
        .store()
        .type_payload(key_parameter.constraint.unwrap())
        .unwrap()
        .data()
    else {
        panic!("T must retain its symbolic keyof O constraint");
    };
    assert_eq!(constraint.target, *object);
    assert_eq!(constraint.index_flags, IndexFlags::NONE);
    let [(_, keys_type), (_, object_type)] = parameters.as_slice() else {
        panic!("expected the original keys and obj parameter types");
    };
    assert_array(checker, *keys_type, *key);
    assert_optional_object(checker, *object_type, *object);
    GenericSnapshot {
        callable,
        signature,
        owner,
        type_parameters,
        parameters,
        return_type,
    }
}

fn assert_regular_literal(checker: &CanonicalCheckerContext<'_>, key: TypeId, expected: &str) {
    let record = checker.store().type_payload(key).unwrap();
    assert_eq!(record.flags(), TypeFlags::STRING_LITERAL);
    let TypeData::Literal(literal) = record.data() else {
        panic!("the selected key must be a literal");
    };
    assert_eq!(literal.value, LiteralValue::String(expected.to_owned()));
    assert_eq!(literal.regular_type, key);
}

fn assert_array(checker: &CanonicalCheckerContext<'_>, array: TypeId, key: TypeId) {
    let TypeData::TypeReference(reference) = checker.store().type_payload(array).unwrap().data()
    else {
        panic!("expected a canonical array reference");
    };
    assert_eq!(
        reference.object.target,
        Some(checker.global_types().array_type)
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[key][..])
    );
    assert_eq!(
        checker.type_to_string(array).unwrap(),
        format!("{}[]", checker.type_to_string(key).unwrap())
    );
}

fn assert_optional_object(checker: &CanonicalCheckerContext<'_>, type_: TypeId, object: TypeId) {
    let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the optional parameter must retain undefined under compiler defaults");
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&object));
    assert!(
        union.union.types.contains(
            &checker
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type,
        )
    );
}

fn assert_object_source(
    checker: &mut CanonicalCheckerContext<'_>,
    object: TypeId,
    source: NodeRef,
) -> SemanticSymbolId {
    let TypeData::Object(record) = checker.store().type_payload(object).unwrap().data() else {
        panic!("O must be inferred from the source object literal");
    };
    let properties = record.structured.properties.clone().unwrap();
    assert_eq!(properties.len(), 2);
    let arena = checker.file(source.file).unwrap().0;
    let NodeData::ObjectLiteralExpression(literal) = &arena.get(source.node).unwrap().data else {
        panic!("expected the original object literal");
    };
    assert_eq!(literal.properties.nodes.len(), 2);
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    for ((&property, &declaration), name) in properties
        .iter()
        .zip(&literal.properties.nodes)
        .zip(["a", "b"])
    {
        let declaration = NodeRef::new(source.arena, source.file, declaration);
        let NodeData::PropertyAssignment(syntax) = &arena.get(declaration.node).unwrap().data
        else {
            panic!("expected an object property assignment");
        };
        let raw = bound_symbol(checker, declaration);
        let name_node = NodeRef::new(source.arena, source.file, syntax.name);
        assert_eq!(
            checker.get_symbol_at_location(name_node).unwrap(),
            Some(raw)
        );
        assert_eq!(checker.get_symbol_declarations(raw).unwrap(), [declaration]);
        assert_eq!(
            checker.get_symbol_declarations(property).unwrap(),
            [declaration]
        );
        assert_eq!(
            checker.store().symbol(property).unwrap().name().as_utf8(),
            Some(name)
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(property)
                .unwrap()
                .resolved_type,
            Some(string)
        );
    }
    assert_eq!(
        checker.type_to_string(object).unwrap(),
        "{ a: string; b: string; }"
    );
    properties[1]
}

#[allow(clippy::too_many_lines)] // Keep each return, selected member, and source origin together.
fn call_snapshot(
    checker: &mut CanonicalCheckerContext<'_>,
    call: &CallParts,
    generic: &GenericSnapshot,
    alias: SemanticSymbolId,
    alias_name: &str,
) -> CallSnapshot {
    assert_eq!(
        checker.get_symbol_at_location(call.callee).unwrap(),
        Some(generic.owner)
    );
    let return_type = checker.get_type_at_location(call.node).unwrap();
    let [object, key] = alias_arguments(checker, return_type, alias);
    assert_regular_literal(checker, key, "b");
    let origin = assert_object_source(checker, object, call.object);
    let array = checker.get_type_at_location(call.array).unwrap();
    assert_array(checker, array, key);
    let signature = checker
        .store()
        .signature_links(call.node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(
        checker.get_return_type_of_signature(signature).unwrap(),
        return_type
    );
    let selected = checker.store().signature(signature).unwrap();
    assert_eq!(selected.target(), Some(generic.signature));
    assert!(selected.mapper().is_some());
    assert!(selected.type_parameters().is_empty());
    let [keys_parameter, object_parameter] = selected.parameters() else {
        panic!("the selected signature must retain both value parameters");
    };
    let keys_type = checker
        .store()
        .value_symbol_links(*keys_parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_array(checker, keys_type, key);
    let optional_object = checker
        .store()
        .value_symbol_links(*object_parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_optional_object(checker, optional_object, object);
    assert_eq!(
        checker.type_to_string(return_type).unwrap(),
        format!("{alias_name}<{{ a: string; b: string; }}, \"b\">")
    );

    // This public relation demands the lazy mapped member and its value type.
    assert!(checker.is_type_assignable_to(object, return_type).unwrap());
    assert!(!checker.is_type_assignable_to(return_type, object).unwrap());
    let TypeData::Mapped(mapped) = checker.store().type_payload(return_type).unwrap().data() else {
        panic!("the call must retain its mapped alias result");
    };
    let declared = checker
        .store()
        .type_alias_links(alias)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(mapped.object.target, Some(declared));
    assert_eq!(mapped.modifiers_type, Some(object));
    assert_eq!(mapped.constraint_type, Some(key));
    let [property] = mapped.object.structured.properties.as_deref().unwrap() else {
        panic!("the return must select only b");
    };
    let property = *property;
    let members = checker
        .store()
        .symbol_table(mapped.object.structured.members.unwrap())
        .unwrap();
    assert_eq!(members.len(), 1);
    assert_eq!(members.get_source("b"), Some(property));
    assert_eq!(members.get_source("a"), None);
    let value = checker.store().value_symbol_links(property).unwrap();
    assert_eq!(
        value.resolved_type,
        Some(checker.store().intrinsic_bootstrap().unwrap().string_type)
    );
    assert_eq!(value.containing_type, Some(return_type));
    let links = checker.store().mapped_symbol_links(property).unwrap();
    assert_eq!(links.key_type, Some(key));
    assert_eq!(links.synthetic_origin, Some(origin));
    assert_eq!(
        checker.get_symbol_declarations(property).unwrap(),
        checker.get_symbol_declarations(origin).unwrap()
    );
    CallSnapshot {
        node: call.node,
        return_type,
        signature,
        object,
        key,
        array,
        property,
        origin,
    }
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 8] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
        store.properties_type_cache_len(),
    ]
}

fn check_both_calls(fixture: &Fixture, alias_name: &str) {
    let function = fixture.function();
    let calls = fixture.calls();
    assert_eq!(calls.len(), 2);
    assert!(matches!(
        fixture
            .source
            .arena
            .get(calls[0].binding.node)
            .unwrap()
            .data,
        NodeData::Identifier(_)
    ));
    let NodeData::BindingPattern(binding) = &fixture
        .source
        .arena
        .get(calls[1].binding.node)
        .unwrap()
        .data
    else {
        panic!("the second call must keep the original empty binding pattern");
    };
    assert!(binding.elements.nodes.is_empty());
    for annotation_first in [true, false] {
        let mut checker = fixture.context();
        let alias = alias_owner(&mut checker, alias_name);
        let source = checker.source_file(SOURCE_FILE).unwrap();
        let early = if annotation_first {
            let type_ = checker
                .get_type_from_type_node(function.return_type)
                .unwrap();
            assert!(
                !checker
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
            Some(type_)
        } else {
            // The existing artifact API starts checking this ordinary source file.
            checker.get_type_at_location(calls[0].node).unwrap();
            assert!(
                checker
                    .store()
                    .source_file_links(source)
                    .unwrap()
                    .type_checked
            );
            None
        };
        checker.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        assert!(checker.global_type_diagnostics().next().is_none());
        let generic = generic_snapshot(&mut checker, &function, alias);
        if let Some(early) = early {
            assert_eq!(generic.return_type, early);
        }
        let cold = calls
            .iter()
            .map(|call| call_snapshot(&mut checker, call, &generic, alias, alias_name))
            .collect::<Vec<_>>();
        assert_eq!(
            checker.get_type_at_location(calls[0].binding).unwrap(),
            cold[0].return_type
        );
        assert_ne!(
            cold[0].origin, cold[1].origin,
            "the two object literals must retain their own b declarations"
        );
        assert_eq!(generic_snapshot(&mut checker, &function, alias), generic);
        let before = counts(&checker);
        checker.check_source_file(SOURCE_FILE).unwrap();
        checker.recheck_source_file(SOURCE_FILE).unwrap();
        let mut warm = calls
            .iter()
            .rev()
            .map(|call| call_snapshot(&mut checker, call, &generic, alias, alias_name))
            .collect::<Vec<_>>();
        warm.reverse();
        assert_eq!(warm, cold);
        assert_eq!(
            checker.get_type_at_location(calls[0].binding).unwrap(),
            cold[0].return_type
        );
        assert_eq!(generic_snapshot(&mut checker, &function, alias), generic);
        assert_eq!(counts(&checker), before);
        assert!(checker.diagnostics().is_empty());
    }
}

#[test]
fn original_pick_calls_keep_the_key_literal_in_both_binding_contexts() {
    let fixture = Fixture::new(
        ORIGINAL,
        "bindingPatternContextualTypeDoesNotCauseWidening.ts",
    );
    check_both_calls(&fixture, "Pick");
}

#[test]
fn selected_fields_alias_calls_do_not_depend_on_the_utility_name() {
    let fixture = Fixture::new(
        concat!(
            "// @target: es2015\n",
            "type SelectedFields<S, K extends keyof S> = { [P in K]: S[P] };\n",
            "declare function chooseFields<O, T extends keyof O>(keys: T[], obj?: O): SelectedFields<O, T>;\n",
            "const result = chooseFields(['b'], { a: 'a', b: 'b' });\n",
            "const { } = chooseFields(['b'], { a: 'a', b: 'b' });\n",
        ),
        "selected-fields-mapped-calls.ts",
    );
    check_both_calls(&fixture, "SelectedFields");
}

#[test]
fn selected_member_assignment_reports_ts2322() {
    let fixture = Fixture::new(
        concat!(
            "// @target: es2015\n",
            "declare function pick<O, T extends keyof O>(keys: T[], obj?: O): Pick<O, T>;\n",
            "const selected = pick(['b'], { a: 'a', b: 'b' });\n",
            "const bad: number = selected.b;\n",
        ),
        "mapped-call-assignment.ts",
    );
    let function = fixture.function();
    let calls = fixture.calls();
    let [call] = calls.as_slice() else {
        panic!("expected one Pick call");
    };
    let mut checker = fixture.context();
    checker.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = checker.diagnostics().clone();
    let [diagnostic] = diagnostics.as_slice() else {
        panic!("expected one assignment diagnostic: {diagnostics:?}");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    let arena = &fixture.source.arena;
    let bad = arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == "bad").then_some(NodeRef::new(arena.id(), SOURCE_FILE, variable.name))
        })
        .unwrap();
    assert_eq!(diagnostic.node, Some(bad));
    assert_eq!(diagnostic.range_override, None);
    let member = arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::PropertyAccessExpression).then_some(NodeRef::new(
                arena.id(),
                SOURCE_FILE,
                node,
            ))
        })
        .unwrap();
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(checker.get_type_at_location(member).unwrap(), string);
    let alias = alias_owner(&mut checker, "Pick");
    let generic = generic_snapshot(&mut checker, &function, alias);
    let cold = call_snapshot(&mut checker, call, &generic, alias, "Pick");
    let before = counts(&checker);
    checker.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(checker.get_type_at_location(member).unwrap(), string);
    assert_eq!(
        call_snapshot(&mut checker, call, &generic, alias, "Pick"),
        cold
    );
    assert_eq!(generic_snapshot(&mut checker, &function, alias), generic);
    assert_eq!(counts(&checker), before);
    assert_eq!(checker.diagnostics(), &diagnostics);
    assert!(checker.global_type_diagnostics().next().is_none());
}

#[test]
#[allow(clippy::too_many_lines)] // Preserve the pinned diagnostic, recovery types, and warm replay.
fn invalid_pick_key_keeps_the_pinned_diagnostic_and_recovery_types() {
    let fixture = Fixture::new(
        concat!(
            "// @target: es2015\n",
            "declare function pick<O, T extends keyof O>(keys: T[], obj?: O): Pick<O, T>;\n",
            "const invalid = pick(['c'], { a: 'a', b: 'b' });\n",
        ),
        "invalid-pick-key.ts",
    );
    let function = fixture.function();
    let calls = fixture.calls();
    let [call] = calls.as_slice() else {
        panic!("expected one invalid Pick call");
    };
    let mut checker = fixture.context();
    checker.check_source_file(SOURCE_FILE).unwrap();
    let diagnostics = checker.diagnostics().clone();
    let [diagnostic] = diagnostics.as_slice() else {
        panic!("expected one invalid-key diagnostic: {diagnostics:?}");
    };
    // Pinned Go dc37b5249ab60e2bbce936f71b883e6c8136167e, cold source result.
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type '\"c\"' is not assignable to type '\"a\" | \"b\"'."
    );
    assert!(diagnostic.related_information.is_empty());
    let node = diagnostic.node.unwrap();
    assert_eq!(node.file, SOURCE_FILE);
    let range = diagnostic.range_override.map_or_else(
        || fixture.source.arena.get(node.node).unwrap().range,
        |range| range.range(),
    );
    assert_eq!(range, TextRange::new(TextPos::new(118), TextPos::new(121)));

    let alias = alias_owner(&mut checker, "Pick");
    let generic = generic_snapshot(&mut checker, &function, alias);
    let return_type = checker.get_type_at_location(call.node).unwrap();
    let [object, key] = alias_arguments(&checker, return_type, alias);
    let origin = assert_object_source(&mut checker, object, call.object);
    let TypeData::Union(union) = checker.store().type_payload(key).unwrap().data() else {
        panic!("invalid-key recovery must use the actual keyof O constraint");
    };
    let [a, b] = union.union.types.as_slice() else {
        panic!("the constraint must contain exactly a and b");
    };
    assert_regular_literal(&checker, *a, "a");
    assert_regular_literal(&checker, *b, "b");
    assert_eq!(
        checker.type_to_string(return_type).unwrap(),
        "Pick<{ a: string; b: string; }, \"a\" | \"b\">"
    );
    let array = checker.get_type_at_location(call.array).unwrap();
    let TypeData::TypeReference(reference) = checker.store().type_payload(array).unwrap().data()
    else {
        panic!("expected a literal-c array");
    };
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("expected one array element type");
    };
    assert_regular_literal(&checker, *element, "c");
    assert_array(&checker, array, *element);
    let signature = checker
        .store()
        .signature_links(call.node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(
        checker.store().signature(signature).unwrap().target(),
        Some(generic.signature)
    );
    assert_eq!(
        checker.get_return_type_of_signature(signature).unwrap(),
        return_type
    );

    assert!(checker.is_type_assignable_to(object, return_type).unwrap());
    assert!(checker.is_type_assignable_to(return_type, object).unwrap());
    let TypeData::Mapped(mapped) = checker.store().type_payload(return_type).unwrap().data() else {
        panic!("invalid-key recovery must retain its actual mapped alias");
    };
    let members = checker
        .store()
        .symbol_table(mapped.object.structured.members.unwrap())
        .unwrap();
    assert_eq!(members.len(), 2);
    assert!(members.get_source("a").is_some());
    let b = members.get_source("b").unwrap();
    assert_eq!(
        checker
            .store()
            .mapped_symbol_links(b)
            .unwrap()
            .synthetic_origin,
        Some(origin)
    );
    let before = counts(&checker);
    checker.recheck_source_file(SOURCE_FILE).unwrap();
    assert_eq!(
        checker.get_type_at_location(call.node).unwrap(),
        return_type
    );
    assert_eq!(checker.get_type_at_location(call.array).unwrap(), array);
    assert_eq!(
        checker.get_return_type_of_signature(signature).unwrap(),
        return_type
    );
    assert_eq!(alias_arguments(&checker, return_type, alias), [object, key]);
    assert_eq!(generic_snapshot(&mut checker, &function, alias), generic);
    assert_eq!(counts(&checker), before);
    assert_eq!(checker.diagnostics(), &diagnostics);
    assert!(checker.global_type_diagnostics().next().is_none());
}
