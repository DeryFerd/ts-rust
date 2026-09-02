use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SourceCheckError, TypeData, TypeId, UnsupportedSourceSyntax, VariableUnsupported,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_260);
const LIBRARY: FileId = FileId::new(203_261);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(parsed: &'a ParseResult, library: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\""),
        (FILE, parsed, "\"/project/deferred-annotated-const.ts\""),
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
}

fn variable(parsed: &ParseResult, expected: &str) -> Variable {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| Variable {
                declaration: node(parsed, id),
                name: node(parsed, data.name),
                annotation: node(parsed, data.type_.unwrap()),
                initializer: node(parsed, data.initializer.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn call_to(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    let calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(call.expression)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                assert_eq!(call.arguments.nodes.len(), 1);
                (
                    node(parsed, id),
                    node(parsed, call.expression),
                    node(parsed, call.arguments.nodes[0]),
                )
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1, "expected one call to {expected}");
    calls[0]
}

fn assert_exported_variable(
    checker: &mut CanonicalCheckerContext<'_>,
    variable: Variable,
    type_: TypeId,
) -> SemanticSymbolId {
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
    assert_eq!(checker.get_type_at_location(variable.name), Ok(type_));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(exported)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    exported
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
        NodeData::FunctionExpression(data) => &data.parameters,
        NodeData::ArrowFunction(data) => &data.parameters,
        _ => panic!("expected the actual callable declaration"),
    };
    assert_eq!(parameters.nodes.len(), 1);
    let parameter = node(parsed, parameters.nodes[0]);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!();
    };
    let parameter_symbol = symbol(checker, parameter);
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

fn assert_forward_types(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let (string_type, number_type) = {
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        (bootstrap.string_type, bootstrap.number_type)
    };
    let caller = variable(parsed, "caller");
    let later = variable(parsed, "later");
    let (call, callee, argument) = call_to(parsed, "later");
    for variable in [caller, later] {
        let declared = checker
            .get_type_from_type_node(variable.annotation)
            .unwrap();
        let declared_signature = assert_signature(
            checker,
            parsed,
            declared,
            variable.annotation,
            string_type,
            number_type,
        );
        let owner = assert_exported_variable(checker, variable, declared);
        let initializer = checker.get_type_at_location(variable.initializer).unwrap();
        let initializer_signature = assert_signature(
            checker,
            parsed,
            initializer,
            variable.initializer,
            string_type,
            number_type,
        );
        assert_ne!(declared_signature, initializer_signature);
        if variable.declaration == later.declaration {
            assert_eq!(checker.get_symbol_at_location(callee), Ok(Some(owner)));
            assert_eq!(checker.get_type_at_location(callee), Ok(declared));
        }
    }
    assert_eq!(checker.get_type_at_location(argument), Ok(string_type));
    assert_eq!(checker.get_type_at_location(call), Ok(number_type));
    let result = variable(parsed, "result");
    assert_eq!(checker.get_type_at_location(result.name), Ok(number_type));
    assert_eq!(
        checker.get_type_at_location(result.initializer),
        Ok(number_type)
    );
    assert!(
        checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
}

fn check_forward_reference(later_initializer: &str) {
    let source = format!(
        "export const caller: (value: string) => number = function(value: string): number {{
            return later(value);
        }};
        export const later: (value: string) => number = {later_initializer};
        const result: number = caller(\"input\");"
    );
    let parsed = parse_source_file(&source);
    let library = parse_source_file(ES5);
    let (_, callee, _) = call_to(&parsed, "later");
    for source_first in [false, true] {
        let mut checker = context(&parsed, &library);
        if source_first {
            checker.check_source_file(FILE).unwrap();
        }
        let first_type = checker.get_type_at_location(callee).unwrap();
        checker.check_source_file(FILE).unwrap();
        assert_forward_types(&mut checker, &parsed);
        assert_eq!(checker.get_type_at_location(callee), Ok(first_type));
        let before = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_forward_types(&mut checker, &parsed);
            assert_eq!(checker.get_type_at_location(callee), Ok(first_type));
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

fn assert_prior_variable_rejection(source: &str) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let later = variable(&parsed, "later");
    let reads = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| match &record.data {
            NodeData::Identifier(name) if name.text == "later" && id != later.name.node => {
                Some(node(&parsed, id))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(reads.len(), 1);
    let mut checker = context(&parsed, &library);
    let owner = symbol(&checker, later.declaration);
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Variable(
        VariableUnsupported::IdentifierNotPrior {
            node: reads[0],
            symbol: owner,
            declaration: later.declaration,
        },
    ));
    for _ in 0..2 {
        assert_eq!(checker.check_source_file(FILE), Err(expected));
        assert!(checker.diagnostics().is_empty());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
        assert!(
            checker
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
    }
}

enum BodyError {
    Argument,
    Return,
}

fn check_body_error(source: &str, error: BodyError) {
    let parsed = parse_source_file(source);
    let library = parse_source_file(ES5);
    let (location, code, arguments, message) = match error {
        BodyError::Argument => (
            call_to(&parsed, "later").2,
            2345,
            ["number", "string"],
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        ),
        BodyError::Return => {
            let later = variable(&parsed, "later");
            let NodeData::FunctionExpression(function) =
                &parsed.arena.get(later.initializer.node).unwrap().data
            else {
                unreachable!();
            };
            let returns = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| match &record.data {
                    NodeData::ReturnStatement(statement)
                        if record.parent == Some(function.body) =>
                    {
                        statement.expression.map(|_| node(&parsed, id))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(returns.len(), 1);
            (
                returns[0],
                2322,
                ["string", "number"],
                "Type 'string' is not assignable to type 'number'.",
            )
        }
    };
    let mut checker = context(&parsed, &library);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.node, Some(location));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
        checker.recheck_source_file(FILE).unwrap();
    }
}

#[test]
fn exported_function_expression_uses_later_annotated_function_signature() {
    check_forward_reference("function(value: string): number { return 1; }");
}

#[test]
fn exported_function_expression_uses_later_annotated_arrow_signature() {
    check_forward_reference("(value: string): number => 1");
}

#[test]
fn deferred_body_reports_wrong_argument() {
    check_body_error(
        "export const caller: (value: number) => number = function(value: number): number {
            return later(value);
        };
        export const later: (value: string) => number = function(value: string): number {
            return 1;
        };",
        BodyError::Argument,
    );
}

#[test]
fn later_annotated_const_still_checks_its_body_return() {
    check_body_error(
        "export const caller: (value: string) => number = function(value: string): number {
            return later(value);
        };
        export const later: (value: string) => number = function(value: string): number {
            return value;
        };",
        BodyError::Return,
    );
}

#[test]
fn direct_early_read_keeps_prior_variable_rejection() {
    assert_prior_variable_rejection(
        "export const early: (value: string) => number = later;
        export const later: (value: string) => number = function(value: string): number {
            return 1;
        };",
    );
}

#[test]
fn direct_early_call_keeps_prior_variable_rejection() {
    assert_prior_variable_rejection(
        "export const early: number = later(\"input\");
        export const later: (value: string) => number = function(value: string): number {
            return 1;
        };",
    );
}

#[test]
fn immediate_function_call_keeps_prior_variable_rejection() {
    assert_prior_variable_rejection(
        "export const early: number = (function(value: string): number {
            return later(value);
        })(\"input\");
        export const later: (value: string) => number = function(value: string): number {
            return 1;
        };",
    );
}

#[test]
fn same_body_later_local_keeps_prior_variable_rejection() {
    assert_prior_variable_rejection(
        "export const caller: (value: string) => number = function(value: string): number {
            const result: number = later(value);
            const later: (value: string) => number = function(value: string): number {
                return 1;
            };
            return result;
        };",
    );
}
