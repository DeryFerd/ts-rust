use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_262);
const LIBRARY: FileId = FileId::new(203_263);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/annotated-typed-arrows.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == LIBRARY,
                    file == LIBRARY,
                    if file == LIBRARY {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

#[derive(Clone, Copy)]
struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: NodeRef,
    body: NodeRef,
}

fn checked_variable(parsed: &ParseResult) -> Variable {
    let variables = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            if name.text != "checked" {
                return None;
            }
            let initializer = data.initializer.unwrap();
            let initializer_record = parsed.arena.get(initializer).unwrap();
            let NodeData::ArrowFunction(arrow) = &initializer_record.data else {
                panic!("expected the written arrow initializer");
            };
            assert_eq!(initializer_record.parent, Some(id));
            let return_annotation = parsed.arena.get(arrow.type_.unwrap()).unwrap();
            assert_eq!(return_annotation.parent, Some(initializer));
            let body = parsed.arena.get(arrow.body).unwrap();
            assert_eq!(body.parent, Some(initializer));
            assert!(matches!(&body.data, NodeData::Identifier(name) if name.text == "value"));
            Some(Variable {
                declaration: node(parsed, id),
                name: node(parsed, data.name),
                annotation: node(parsed, data.type_.unwrap()),
                initializer: node(parsed, initializer),
                body: node(parsed, arrow.body),
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(variables.len(), 1);
    variables[0]
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn assert_signature(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    type_: TypeId,
    declaration: NodeRef,
    parameter_type: TypeId,
    return_type: TypeId,
) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected the actual callable type");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let signatures = object.structured.signatures.as_deref().unwrap();
    assert_eq!(signatures.len(), 1);
    let signature = signatures[0];
    let parameters = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::FunctionTypeNode(data) => &data.parameters,
        NodeData::ArrowFunction(data) => &data.parameters,
        _ => panic!("expected the actual callable declaration"),
    };
    assert_eq!(parameters.nodes.len(), 1);
    let parameter = node(parsed, parameters.nodes[0]);
    let parameter_record = parsed.arena.get(parameter.node).unwrap();
    assert_eq!(parameter_record.parent, Some(declaration.node));
    let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
        unreachable!();
    };
    let annotation = node(parsed, data.type_.unwrap());
    let parameter_symbol = symbol(checker, parameter);
    assert_eq!(
        checker.get_type_from_type_node(annotation),
        Ok(parameter_type)
    );
    assert_eq!(
        checker.get_type_at_location(node(parsed, data.name)),
        Ok(parameter_type)
    );
    assert_eq!(
        checker.get_return_type_of_signature(signature),
        Ok(return_type)
    );
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), &[parameter_symbol]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert!(!record.has_rest_parameter());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(return_type));
    signature
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let location = node(parsed, id);
                (
                    location,
                    store.node_links(location).cloned(),
                    store.type_node_links(location).cloned(),
                    store.symbol_node_links(location).cloned(),
                    store.signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(owner, _)| (owner, store.value_symbol_links(owner).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

#[derive(Clone, Copy)]
enum ErrorSite {
    Body,
    Variable,
}

fn assert_exported_variable(
    checker: &mut CanonicalCheckerContext<'_>,
    variable: Variable,
    declared_type: TypeId,
) {
    assert_eq!(
        checker.get_type_at_location(variable.name),
        Ok(declared_type)
    );
    let exported = symbol(checker, variable.declaration);
    let local = checker
        .file(FILE)
        .unwrap()
        .1
        .local_symbol(variable.declaration)
        .unwrap();
    let local = checker.store().get_merged_symbol(local).unwrap();
    assert_ne!(local, exported);
    assert_eq!(
        checker.store().symbol(local).unwrap().export_symbol(),
        Some(exported)
    );
    let record = checker.store().symbol(exported).unwrap();
    assert!(record.flags().contains(SymbolFlags::BLOCK_SCOPED_VARIABLE));
    assert_eq!(record.declarations(), Some(&[variable.declaration][..]));
    assert_eq!(record.value_declaration(), Some(variable.declaration));
    assert_eq!(
        checker.get_symbol_at_location(variable.name),
        Ok(Some(exported))
    );
    assert_eq!(
        checker
            .store()
            .value_symbol_links(exported)
            .unwrap()
            .resolved_type,
        Some(declared_type)
    );
}

fn assert_error(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    variable: Variable,
    initializer_type: TypeId,
    error: ErrorSite,
) {
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let string_type = bootstrap.string_type;
    let number_type = bootstrap.number_type;
    let (parameter_type, declared_return_type, location, arguments, message) = match error {
        ErrorSite::Body => (
            string_type,
            number_type,
            variable.body,
            ["string", "number"],
            "Type 'string' is not assignable to type 'number'.",
        ),
        ErrorSite::Variable => (
            number_type,
            string_type,
            variable.name,
            ["(value: number) => number", "(value: number) => string"],
            "Type '(value: number) => number' is not assignable to type '(value: number) => string'.",
        ),
    };
    let declared_type = checker
        .get_type_from_type_node(variable.annotation)
        .unwrap();
    let declared_signature = assert_signature(
        checker,
        parsed,
        declared_type,
        variable.annotation,
        parameter_type,
        declared_return_type,
    );
    assert_eq!(
        checker.get_type_at_location(variable.initializer),
        Ok(initializer_type)
    );
    let initializer_signature = assert_signature(
        checker,
        parsed,
        initializer_type,
        variable.initializer,
        parameter_type,
        number_type,
    );
    assert_ne!(declared_signature, initializer_signature);
    assert_eq!(
        checker.get_type_at_location(variable.body),
        Ok(parameter_type)
    );
    assert_exported_variable(checker, variable, declared_type);
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.node, Some(location));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    assert!(diagnostic.related_information.is_empty());
}

fn check_error(source: &str, error: ErrorSite) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let variable = checked_variable(&parsed);
    for source_first in [false, true] {
        let mut checker = context(&parsed, &library);
        if source_first {
            checker.check_source_file(FILE).unwrap();
        }
        let initializer_type = checker.get_type_at_location(variable.initializer).unwrap();
        checker.check_source_file(FILE).unwrap();
        assert_error(&mut checker, &parsed, variable, initializer_type, error);
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_error(&mut checker, &parsed, variable, initializer_type, error);
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn annotated_typed_arrow_checks_written_return_type() {
    check_error(
        "export const checked: (value: string) => number = (value: string): number => value;",
        ErrorSite::Body,
    );
}

#[test]
fn annotated_typed_arrow_checks_variable_assignment() {
    check_error(
        "export const checked: (value: number) => string = (value: number): number => value;",
        ErrorSite::Variable,
    );
}
