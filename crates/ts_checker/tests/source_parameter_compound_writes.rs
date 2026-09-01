use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId, type_records::LiteralValue,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_310);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/parameter-compound-writes.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(binder.finish(), vec![(FILE, &parsed.arena)], options()).unwrap()
}

fn options() -> CanonicalCheckerOptions {
    CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
        no_implicit_any: true,
        strict_function_types: true,
        no_unchecked_indexed_access: true,
        ..CanonicalCheckerOptions::default()
    }
}

fn node(parsed: &ParseResult, id: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect::<Vec<_>>();
    result.sort_by_key(|item| parsed.arena.get(item.node).unwrap().range.start);
    result
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 4] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    ]
}

#[derive(Debug, PartialEq)]
struct Snapshot {
    owners: Vec<SemanticSymbolId>,
    types: Vec<TypeId>,
    signatures: Vec<SignatureId>,
    counts: [usize; 4],
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    owners: Vec<SemanticSymbolId>,
    types: Vec<TypeId>,
    signatures: Vec<SignatureId>,
    previous: &mut Option<Snapshot>,
) {
    let current = Snapshot {
        owners,
        types,
        signatures,
        counts: counts(checker),
        diagnostics: checker.diagnostics().clone(),
    };
    if let Some(previous) = previous {
        assert_eq!(previous, &current);
    } else {
        *previous = Some(current);
    }
}

fn checked_type(checker: &mut CanonicalCheckerContext<'_>, at: NodeRef) -> TypeId {
    let type_ = checker.get_type_at_location(at).unwrap();
    assert_eq!(
        checker.store().type_node_links(at).unwrap().resolved_type,
        Some(type_)
    );
    type_
}

fn assert_string_result(checker: &CanonicalCheckerContext<'_>, type_: TypeId) {
    use ts_checker::semantic::types::TypeFlags;
    let record = checker.store().type_payload(type_).unwrap();
    if let TypeData::Union(union) = record.data() {
        assert!(!union.union.types.is_empty());
        for &member in &union.union.types {
            assert_string_result(checker, member);
        }
    } else {
        assert!(record.flags().intersects(TypeFlags::STRING_LIKE));
    }
}

fn small_control(source: &str, number: bool, literal_union: bool) {
    let parsed = parse_source_file(source);
    let function = nodes(&parsed, SyntaxKind::FunctionExpression)[0];
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    let expression = nodes(&parsed, SyntaxKind::BinaryExpression)[0];
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
    else {
        unreachable!()
    };
    let left = node(&parsed, binary.left);
    let right = node(&parsed, binary.right);
    let NodeData::FunctionExpression(data) = &parsed.arena.get(function.node).unwrap().data else {
        unreachable!()
    };
    let parameter = node(&parsed, data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = node(&parsed, data.type_.unwrap());
    let returned = nodes(&parsed, SyntaxKind::ReturnStatement)[0];
    let NodeData::ReturnStatement(data) = &parsed.arena.get(returned.node).unwrap().data else {
        unreachable!()
    };
    let read = node(&parsed, data.expression.unwrap());
    let binding = nodes(&parsed, SyntaxKind::VariableDeclaration)[0];

    for first in [None, Some(expression), Some(call)] {
        let mut checker = context(&parsed);
        let early = first.map(|at| checker.get_type_at_location(at).unwrap());
        checker.check_source_file(FILE).unwrap();
        let mut previous = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
            }
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let numeric = checker.store().intrinsic_bootstrap().unwrap().number_type;
            let expected = if number { numeric } else { string };
            let owner = symbol(&checker, function);
            let parameter_owner = symbol(&checker, parameter);
            let binding_owner = symbol(&checker, binding);
            assert_ne!(owner, parameter_owner);
            assert_ne!(owner, binding_owner);
            assert_ne!(parameter_owner, binding_owner);
            for at in [left, read] {
                assert_eq!(
                    checker.get_symbol_at_location(at),
                    Ok(Some(parameter_owner))
                );
            }
            let declared = checker.get_type_at_location(annotation).unwrap();
            if literal_union {
                assert_ne!(declared, string);
                let TypeData::Union(union) = checker.store().type_payload(declared).unwrap().data()
                else {
                    panic!("the declared parameter must retain its literal union")
                };
                let mut values = union
                    .union
                    .types
                    .iter()
                    .map(|&member| {
                        let TypeData::Literal(literal) =
                            checker.store().type_payload(member).unwrap().data()
                        else {
                            panic!("the parameter union must contain its original string literals")
                        };
                        let LiteralValue::String(value) = &literal.value else {
                            panic!("the parameter union must contain strings")
                        };
                        value.as_str()
                    })
                    .collect::<Vec<_>>();
                values.sort_unstable();
                assert_eq!(values, ["", "/"]);
            } else {
                assert_eq!(declared, expected);
            }
            let left_type = checked_type(&mut checker, left);
            assert_eq!(left_type, expected);
            let right_type = checked_type(&mut checker, right);
            let TypeData::Literal(literal) =
                checker.store().type_payload(right_type).unwrap().data()
            else {
                panic!("the actual slash operand must keep its literal type")
            };
            assert_eq!(literal.value, LiteralValue::String("/".to_owned()));
            assert_eq!(checked_type(&mut checker, expression), string);
            assert_eq!(checked_type(&mut checker, read), expected);
            assert_eq!(checked_type(&mut checker, call), expected);
            let function_type = checker.get_type_at_location(function).unwrap();
            assert_eq!(
                checker
                    .store()
                    .type_payload(function_type)
                    .unwrap()
                    .symbol(),
                Some(owner)
            );
            let function_signature = signature(&checker, function);
            assert_eq!(signature(&checker, call), function_signature);
            assert_eq!(
                checker.get_return_type_of_signature(function_signature),
                Ok(expected)
            );
            let record = checker.store().signature(function_signature).unwrap();
            assert_eq!(record.declaration(), Some(function));
            assert_eq!(record.parameters(), &[parameter_owner]);
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(parameter_owner)
                    .unwrap()
                    .resolved_type,
                Some(declared)
            );
            if number {
                let diagnostics = checker.diagnostics().as_slice();
                assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
                let diagnostic = &diagnostics[0];
                assert_eq!(diagnostic.node, Some(left));
                assert_eq!(diagnostic.range_override, None);
                assert_eq!(diagnostic.diagnostic.code(), 2322);
                assert_eq!(
                    diagnostic.diagnostic.category(),
                    ts_diagnostics::Category::Error
                );
                assert_eq!(diagnostic.diagnostic.arguments, ["string", "number"]);
                assert!(diagnostic.diagnostic.details.is_empty());
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Type 'string' is not assignable to type 'number'."
                );
                assert!(diagnostic.related_information.is_empty());
                let range = parsed.arena.get(left.node).unwrap().range;
                assert_eq!(range.start.get() as usize, source.find("path +=").unwrap());
                assert_eq!(range.end.get() - range.start.get(), 4);
            } else {
                assert!(
                    checker.diagnostics().is_empty(),
                    "{:?}",
                    checker.diagnostics()
                );
            }
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(expression) {
                        string
                    } else {
                        expected
                    }
                );
            }
            snapshot(
                &checker,
                vec![owner, parameter_owner, binding_owner],
                vec![
                    declared,
                    left_type,
                    right_type,
                    string,
                    expected,
                    function_type,
                ],
                vec![function_signature],
                &mut previous,
            );
        }
    }
}

#[test]
fn string_parameter_compound_write_keeps_operands_and_replay() {
    small_control(
        "const append = function(path: string) { path += '/'; return path; }; const result = append('a');",
        false,
        false,
    );
}

#[test]
fn literal_union_parameter_compound_write_widens_without_error() {
    small_control(
        "const append = function(path: '' | '/') { path += '/'; return path; }; const result = append('');",
        false,
        true,
    );
}

#[test]
fn numeric_parameter_compound_write_reports_left_target_and_keeps_number_flow() {
    small_control(
        "const append = function(path: number) { path += '/'; return path; }; const result = append(1);",
        true,
        false,
    );
}

const PROVIDER: FileId = FileId::new(204_311);
const INTERNAL: FileId = FileId::new(204_312);
const LIBRARIES: &[(&str, &str)] = &[
    (
        "\"/lib/lib.es5.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "\"/lib/lib.es2015.core.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts"),
    ),
    (
        "\"/lib/lib.decorators.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "\"/lib/lib.decorators.legacy.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

fn composition_context<'a>(
    parsed: &'a ParseResult,
    provider: &'a ParseResult,
    internal: &'a ParseResult,
    libraries: &'a [ParseResult],
) -> CanonicalCheckerContext<'a> {
    use ts_checker::semantic::{
        CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
        CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
    };
    use ts_options::ModuleKind;

    let mut files = libraries
        .iter()
        .enumerate()
        .map(|(index, parsed)| {
            (
                FileId::new(204_320 + index as u32),
                parsed,
                LIBRARIES[index].0,
                true,
                true,
            )
        })
        .collect::<Vec<_>>();
    files.extend([
        (
            PROVIDER,
            provider,
            "\"/project/node_modules/@types/node/path.d.ts\"",
            true,
            false,
        ),
        (
            INTERNAL,
            internal,
            "\"/project/_internal.ts\"",
            false,
            false,
        ),
        (FILE, parsed, "\"/project/_path.ts\"", false, false),
    ]);
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, declaration, library) in &files {
        assert!(
            parsed.diagnostics.is_empty(),
            "{path}: {:?}",
            parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    library,
                    if declaration {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                )
                .with_implied_node_format(if declaration {
                    ModuleKind::CommonJs
                } else {
                    ModuleKind::EsNext
                }),
            )
            .unwrap();
    }
    for &(file, parsed, _, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut entries = Vec::new();
    for (file, source) in [(FILE, parsed), (PROVIDER, provider)] {
        for (_, record) in source.arena.iter() {
            let (specifier, require) = match &record.data {
                NodeData::ImportDeclaration(import) => (import.module_specifier, false),
                NodeData::ImportEqualsDeclaration(import) => {
                    let NodeData::ExternalModuleReference(reference) =
                        &source.arena.get(import.module_reference).unwrap().data
                    else {
                        continue;
                    };
                    (reference.expression, true)
                }
                _ => continue,
            };
            let NodeData::StringLiteral(text) = &source.arena.get(specifier).unwrap().data else {
                unreachable!()
            };
            let target = if text.text == "./_internal" {
                INTERNAL
            } else {
                assert_eq!(text.text, "node:path");
                PROVIDER
            };
            entries.push(CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(source.arena.id(), file, specifier),
                CanonicalResolvedModuleInput::new(
                    target,
                    if require {
                        CanonicalModuleResolutionMode::CommonJs
                    } else {
                        CanonicalModuleResolutionMode::Esm
                    },
                    if target == PROVIDER {
                        CanonicalModuleResolutionMode::CommonJs
                    } else {
                        CanonicalModuleResolutionMode::Esm
                    },
                ),
            ));
        }
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _, _, _)| (file, &parsed.arena))
            .collect(),
        options(),
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn named_variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
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
            (name.text == expected)
                .then(|| (node(parsed, id), node(parsed, data.initializer.unwrap())))
        })
        .unwrap()
}

fn composition_control(negative: bool) {
    let mut source = String::from(
        "import type path from \"node:path\";\nimport { normalizeWindowsPath } from \"./_internal\";\n",
    );
    source.push_str(PATH_REGEX);
    source.push_str(NORMALIZE);
    source.push_str(PATH_HELPERS);
    source.push_str("\nconst valid = normalize(\".\");\n");
    if negative {
        source.push_str(
            "const badArgument = normalize(1);\nconst badResult: number = normalize(\".\");\n",
        );
    }
    let parsed = parse_source_file(&source);
    let provider = parse_source_file(NODE_PATH);
    let internal = parse_source_file(WINDOWS_HELPER);
    let libraries = LIBRARIES
        .iter()
        .map(|(_, text)| parse_source_file(text))
        .collect::<Vec<_>>();
    let (binding, function) = named_variable(&parsed, "normalize");
    let (_, call) = named_variable(&parsed, "valid");
    let NodeData::FunctionExpression(data) = &parsed.arena.get(function.node).unwrap().data else {
        unreachable!()
    };
    let parameter = node(&parsed, data.parameters.nodes[0]);
    let body_range = parsed.arena.get(data.body).unwrap().range;
    let in_body = |at: &NodeRef| {
        let range = parsed.arena.get(at.node).unwrap().range;
        range.start >= body_range.start && range.end <= body_range.end
    };
    let writes = nodes(&parsed, SyntaxKind::BinaryExpression)
        .into_iter()
        .filter(in_body)
        .filter(|at| {
            let NodeData::BinaryExpression(data) = &parsed.arena.get(at.node).unwrap().data else {
                unreachable!()
            };
            parsed.arena.get(data.operator_token).unwrap().kind == SyntaxKind::PlusEqualsToken
        })
        .collect::<Vec<_>>();
    assert_eq!(writes.len(), 2);
    let returns = nodes(&parsed, SyntaxKind::ReturnStatement)
        .into_iter()
        .filter(in_body)
        .collect::<Vec<_>>();
    assert_eq!(returns.len(), 6);
    let calls = nodes(&parsed, SyntaxKind::CallExpression)
        .into_iter()
        .filter(in_body)
        .collect::<Vec<_>>();
    let comparisons = nodes(&parsed, SyntaxKind::BinaryExpression)
        .into_iter()
        .filter(in_body)
        .filter(|at| {
            let NodeData::BinaryExpression(data) = &parsed.arena.get(at.node).unwrap().data else {
                unreachable!()
            };
            parsed.arena.get(data.operator_token).unwrap().kind
                == SyntaxKind::EqualsEqualsEqualsToken
        })
        .collect::<Vec<_>>();
    assert_eq!(comparisons.len(), 3);
    let indexed = nodes(&parsed, SyntaxKind::ElementAccessExpression)
        .into_iter()
        .filter(in_body)
        .collect::<Vec<_>>();
    assert_eq!(indexed.len(), 1);
    let (import, import_name) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ImportClause(data) = &record.data else {
                return None;
            };
            data.name
                .map(|name| (node(&parsed, id), node(&parsed, name)))
        })
        .unwrap();

    for first in [None, Some(function), Some(call)] {
        let mut checker = composition_context(&parsed, &provider, &internal, &libraries);
        let early = first.map(|at| checker.get_type_at_location(at).unwrap());
        // A later unsupported helper stays visible here. This is not an expected-failure test.
        checker.check_source_file(FILE).unwrap();
        checker.check_source_file(INTERNAL).unwrap();
        let mut previous = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(FILE).unwrap();
                checker.recheck_source_file(INTERNAL).unwrap();
            }
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let owner = symbol(&checker, function);
            let parameter_owner = symbol(&checker, parameter);
            let binding_owner = symbol(&checker, binding);
            let import_owner = symbol(&checker, import);
            assert_ne!(owner, binding_owner);
            assert_ne!(parameter_owner, import_owner);
            assert_ne!(parameter_owner, binding_owner);
            assert_eq!(
                checker.get_symbol_at_location(import_name),
                Ok(Some(import_owner))
            );
            let function_type = checker.get_type_at_location(function).unwrap();
            let function_signature = signature(&checker, function);
            assert_eq!(
                checker.get_return_type_of_signature(function_signature),
                Ok(string)
            );
            assert_eq!(
                checker
                    .store()
                    .signature(function_signature)
                    .unwrap()
                    .parameters(),
                &[parameter_owner]
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(parameter_owner)
                    .unwrap()
                    .resolved_type,
                Some(string)
            );
            assert_eq!(checked_type(&mut checker, call), string);
            let provider_signature = signature(&checker, call);
            assert_ne!(provider_signature, function_signature);
            let provider_declaration = checker
                .store()
                .signature(provider_signature)
                .unwrap()
                .declaration()
                .unwrap();
            assert_eq!(provider_declaration.file, PROVIDER);
            let NodeData::FunctionDeclaration(provider_function) =
                &provider.arena.get(provider_declaration.node).unwrap().data
            else {
                panic!("normalize must use its actual Node declaration")
            };
            assert_eq!(provider_function.parameters.nodes.len(), 1);
            let provider_parameter = NodeRef::new(
                provider.arena.id(),
                PROVIDER,
                provider_function.parameters.nodes[0],
            );
            let provider_parameter_owner = symbol(&checker, provider_parameter);
            assert_ne!(parameter_owner, provider_parameter_owner);
            assert_ne!(import_owner, provider_parameter_owner);
            let NodeData::ParameterDeclaration(provider_parameter_data) =
                &provider.arena.get(provider_parameter.node).unwrap().data
            else {
                unreachable!()
            };
            let provider_parameter_name =
                NodeRef::new(provider.arena.id(), PROVIDER, provider_parameter_data.name);
            assert_eq!(
                checker.get_symbol_at_location(provider_parameter_name),
                Ok(Some(provider_parameter_owner))
            );
            assert_eq!(
                checker.get_type_at_location(provider_parameter_name),
                Ok(string)
            );
            assert_eq!(
                checker
                    .store()
                    .signature(provider_signature)
                    .unwrap()
                    .parameters(),
                &[provider_parameter_owner]
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(provider_parameter_owner)
                    .unwrap()
                    .resolved_type,
                Some(string)
            );
            assert_eq!(
                checker.get_return_type_of_signature(provider_signature),
                Ok(string)
            );
            let mut types = vec![function_type, string];
            for &write in &writes {
                let NodeData::BinaryExpression(data) = &parsed.arena.get(write.node).unwrap().data
                else {
                    unreachable!()
                };
                let left = node(&parsed, data.left);
                let right = node(&parsed, data.right);
                assert_eq!(
                    checker.get_symbol_at_location(left),
                    Ok(Some(parameter_owner))
                );
                assert_eq!(checked_type(&mut checker, left), string);
                let right_type = checked_type(&mut checker, right);
                let TypeData::Literal(literal) =
                    checker.store().type_payload(right_type).unwrap().data()
                else {
                    panic!("expected original slash literal")
                };
                assert_eq!(literal.value, LiteralValue::String("/".to_owned()));
                assert_eq!(checked_type(&mut checker, write), string);
                types.push(right_type);
            }
            for &returned in &returns {
                let NodeData::ReturnStatement(data) =
                    &parsed.arena.get(returned.node).unwrap().data
                else {
                    unreachable!()
                };
                let type_ = checker
                    .get_type_at_location(node(&parsed, data.expression.unwrap()))
                    .unwrap();
                assert_string_result(&checker, type_);
                types.push(type_);
            }
            let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
            for &comparison in &comparisons {
                assert_eq!(checked_type(&mut checker, comparison), boolean);
            }
            let index_type = checked_type(&mut checker, indexed[0]);
            let undefined = checker
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type;
            let TypeData::Union(union) = checker.store().type_payload(index_type).unwrap().data()
            else {
                panic!("the real unchecked string index includes undefined")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&string));
            assert!(union.union.types.contains(&undefined));
            types.extend([boolean, index_type]);
            let mut signatures = vec![function_signature, provider_signature];
            for &at in &calls {
                types.push(checked_type(&mut checker, at));
                let signature = signature(&checker, at);
                let declaration = checker
                    .store()
                    .signature(signature)
                    .unwrap()
                    .declaration()
                    .unwrap();
                let NodeData::CallExpression(data) = &parsed.arena.get(at.node).unwrap().data
                else {
                    unreachable!()
                };
                if let NodeData::PropertyAccessExpression(property) =
                    &parsed.arena.get(data.expression).unwrap().data
                {
                    let NodeData::Identifier(name) = &parsed.arena.get(property.name).unwrap().data
                    else {
                        unreachable!()
                    };
                    assert!(name.text == "match" || name.text == "test");
                    assert!(
                        (0..LIBRARIES.len())
                            .any(|index| declaration.file == FileId::new(204_320 + index as u32))
                    );
                }
                signatures.push(signature);
            }
            if negative {
                let (_, bad_call) = named_variable(&parsed, "badArgument");
                let NodeData::CallExpression(data) = &parsed.arena.get(bad_call.node).unwrap().data
                else {
                    unreachable!()
                };
                let argument = node(&parsed, data.arguments.nodes[0]);
                let (bad_result, _) = named_variable(&parsed, "badResult");
                let diagnostics = checker.diagnostics().as_slice();
                assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
                for (diagnostic, (expected_node, code, message)) in diagnostics.iter().zip([
                    (argument, 2345, "Argument of type 'number' is not assignable to parameter of type 'string'."),
                    (bad_result, 2322, "Type 'string' is not assignable to type 'number'."),
                ]) {
                    assert_eq!(diagnostic.node, Some(expected_node));
                    assert_eq!(diagnostic.range_override, None);
                    assert_eq!(diagnostic.diagnostic.code(), code);
                    assert_eq!(diagnostic.diagnostic.category(), ts_diagnostics::Category::Error);
                    assert_eq!(diagnostic.diagnostic.arguments, if code == 2345 { ["number", "string"] } else { ["string", "number"] });
                    assert!(diagnostic.diagnostic.details.is_empty());
                    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
                    assert!(diagnostic.related_information.is_empty());
                }
            } else {
                assert!(
                    checker.diagnostics().is_empty(),
                    "{:?}",
                    checker.diagnostics()
                );
            }
            if let Some(early) = early {
                assert_eq!(
                    early,
                    if first == Some(function) {
                        function_type
                    } else {
                        string
                    }
                );
            }
            snapshot(
                &checker,
                vec![
                    owner,
                    parameter_owner,
                    binding_owner,
                    import_owner,
                    provider_parameter_owner,
                ],
                types,
                signatures,
                &mut previous,
            );
        }
    }
}

#[test]
fn original_normalize_body_keeps_real_helpers_libraries_and_compound_writes() {
    composition_control(false);
}

#[test]
fn original_normalize_body_reports_argument_and_receiving_variable_errors() {
    composition_control(true);
}

// Complete @types/node 26.1.0 path.d.ts. Original SHA-256:
// ec501101c2a96133a6c695f934c8f6642149cc728571b29cbb7b770984c1088e.
const NODE_PATH: &str = r###"declare module "node:path" {
    namespace path {
        /**
         * A parsed path object generated by path.parse() or consumed by path.format().
         */
        interface ParsedPath {
            /**
             * The root of the path such as '/' or 'c:\'
             */
            root: string;
            /**
             * The full directory path such as '/home/user/dir' or 'c:\path\dir'
             */
            dir: string;
            /**
             * The file name including extension (if any) such as 'index.html'
             */
            base: string;
            /**
             * The file extension (if any) such as '.html'
             */
            ext: string;
            /**
             * The file name without extension (if any) such as 'index'
             */
            name: string;
        }
        interface FormatInputPathObject {
            /**
             * The root of the path such as '/' or 'c:\'
             */
            root?: string | undefined;
            /**
             * The full directory path such as '/home/user/dir' or 'c:\path\dir'
             */
            dir?: string | undefined;
            /**
             * The file name including extension (if any) such as 'index.html'
             */
            base?: string | undefined;
            /**
             * The file extension (if any) such as '.html'
             */
            ext?: string | undefined;
            /**
             * The file name without extension (if any) such as 'index'
             */
            name?: string | undefined;
        }
        /**
         * Normalize a string path, reducing '..' and '.' parts.
         * When multiple slashes are found, they're replaced by a single one; when the path contains a trailing slash, it is preserved. On Windows backslashes are used. If the path is a zero-length string, '.' is returned, representing the current working directory.
         *
         * @param path string path to normalize.
         * @throws {TypeError} if `path` is not a string.
         */
        function normalize(path: string): string;
        /**
         * Join all arguments together and normalize the resulting path.
         *
         * @param paths paths to join.
         * @throws {TypeError} if any of the path segments is not a string.
         */
        function join(...paths: string[]): string;
        /**
         * The right-most parameter is considered {to}. Other parameters are considered an array of {from}.
         *
         * Starting from leftmost {from} parameter, resolves {to} to an absolute path.
         *
         * If {to} isn't already absolute, {from} arguments are prepended in right to left order,
         * until an absolute path is found. If after using all {from} paths still no absolute path is found,
         * the current working directory is used as well. The resulting path is normalized,
         * and trailing slashes are removed unless the path gets resolved to the root directory.
         *
         * @param paths A sequence of paths or path segments.
         * @throws {TypeError} if any of the arguments is not a string.
         */
        function resolve(...paths: string[]): string;
        /**
         * The `path.matchesGlob()` method determines if `path` matches the `pattern`.
         * @param path The path to glob-match against.
         * @param pattern The glob to check the path against.
         * @returns Whether or not the `path` matched the `pattern`.
         * @throws {TypeError} if `path` or `pattern` are not strings.
         * @since v22.5.0
         */
        function matchesGlob(path: string, pattern: string): boolean;
        /**
         * Determines whether {path} is an absolute path. An absolute path will always resolve to the same location, regardless of the working directory.
         *
         * If the given {path} is a zero-length string, `false` will be returned.
         *
         * @param path path to test.
         * @throws {TypeError} if `path` is not a string.
         */
        function isAbsolute(path: string): boolean;
        /**
         * Solve the relative path from {from} to {to} based on the current working directory.
         * At times we have two absolute paths, and we need to derive the relative path from one to the other. This is actually the reverse transform of path.resolve.
         *
         * @throws {TypeError} if either `from` or `to` is not a string.
         */
        function relative(from: string, to: string): string;
        /**
         * Return the directory name of a path. Similar to the Unix dirname command.
         *
         * @param path the path to evaluate.
         * @throws {TypeError} if `path` is not a string.
         */
        function dirname(path: string): string;
        /**
         * Return the last portion of a path. Similar to the Unix basename command.
         * Often used to extract the file name from a fully qualified path.
         *
         * @param path the path to evaluate.
         * @param suffix optionally, an extension to remove from the result.
         * @throws {TypeError} if `path` is not a string or if `ext` is given and is not a string.
         */
        function basename(path: string, suffix?: string): string;
        /**
         * Return the extension of the path, from the last '.' to end of string in the last portion of the path.
         * If there is no '.' in the last portion of the path or the first character of it is '.', then it returns an empty string.
         *
         * @param path the path to evaluate.
         * @throws {TypeError} if `path` is not a string.
         */
        function extname(path: string): string;
        /**
         * The platform-specific file separator. '\\' or '/'.
         */
        const sep: "\\" | "/";
        /**
         * The platform-specific file delimiter. ';' or ':'.
         */
        const delimiter: ";" | ":";
        /**
         * Returns an object from a path string - the opposite of format().
         *
         * @param path path to evaluate.
         * @throws {TypeError} if `path` is not a string.
         */
        function parse(path: string): ParsedPath;
        /**
         * Returns a path string from an object - the opposite of parse().
         *
         * @param pathObject path to evaluate.
         */
        function format(pathObject: FormatInputPathObject): string;
        /**
         * On Windows systems only, returns an equivalent namespace-prefixed path for the given path.
         * If path is not a string, path will be returned without modifications.
         * This method is meaningful only on Windows system.
         * On POSIX systems, the method is non-operational and always returns path without modifications.
         */
        function toNamespacedPath(path: string): string;
    }
    namespace path {
        export {
            /**
             * The `path.posix` property provides access to POSIX specific implementations of the `path` methods.
             *
             * The API is accessible via `require('node:path').posix` or `require('node:path/posix')`.
             */
            path as posix,
            /**
             * The `path.win32` property provides access to Windows-specific implementations of the `path` methods.
             *
             * The API is accessible via `require('node:path').win32` or `require('node:path/win32')`.
             */
            path as win32,
        };
    }
    export = path;
}
declare module "path" {
    import path = require("node:path");
    export = path;
}
"###;
// Original Pathe normalize declaration and direct helpers, without rewritten bodies.
const NORMALIZE: &str = r###"export const normalize: typeof path.normalize = function (path: string) {
  if (path.length === 0) {
    return ".";
  }

  // Normalize windows argument
  path = normalizeWindowsPath(path);

  const isUNCPath = path.match(_UNC_REGEX);
  const isPathAbsolute = isAbsolute(path);
  const trailingSeparator = path[path.length - 1] === "/";

  // Normalize the path
  path = normalizeString(path, !isPathAbsolute);

  if (path.length === 0) {
    if (isPathAbsolute) {
      return "/";
    }
    return trailingSeparator ? "./" : ".";
  }
  if (trailingSeparator) {
    path += "/";
  }
  if (_DRIVE_LETTER_RE.test(path)) {
    path += "/";
  }

  if (isUNCPath) {
    if (!isPathAbsolute) {
      return `//./${path}`;
    }
    return `//${path}`;
  }

  return isPathAbsolute && !isAbsolute(path) ? `/${path}` : path;
};
"###;
const PATH_HELPERS: &str = r###"export function normalizeString(path: string, allowAboveRoot: boolean) {
  let res = "";
  let lastSegmentLength = 0;
  let lastSlash = -1;
  let dots = 0;
  let char: string | null = null;
  for (let index = 0; index <= path.length; ++index) {
    if (index < path.length) {
      // casted because we know it exists thanks to the length check
      char = path[index] as string;
    } else if (char === "/") {
      break;
    } else {
      char = "/";
    }
    if (char === "/") {
      if (lastSlash === index - 1 || dots === 1) {
        // NOOP
      } else if (dots === 2) {
        if (
          res.length < 2 ||
          lastSegmentLength !== 2 ||
          res[res.length - 1] !== "." ||
          res[res.length - 2] !== "."
        ) {
          if (res.length > 2) {
            const lastSlashIndex = res.length - lastSegmentLength - 1;
            if (lastSlashIndex === -1) {
              res = "";
              lastSegmentLength = 0;
            } else {
              res = res.slice(0, lastSlashIndex);
              lastSegmentLength = res.length - 1 - res.lastIndexOf("/");
            }
            lastSlash = index;
            dots = 0;
            continue;
          } else if (res.length > 0) {
            res = "";
            lastSegmentLength = 0;
            lastSlash = index;
            dots = 0;
            continue;
          }
        }
        if (allowAboveRoot) {
          res += res.length > 0 ? "/.." : "..";
          lastSegmentLength = 2;
        }
      } else {
        if (res.length > 0) {
          res += `/${path.slice(lastSlash + 1, index)}`;
        } else {
          res = path.slice(lastSlash + 1, index);
        }
        lastSegmentLength = index - lastSlash - 1;
      }
      lastSlash = index;
      dots = 0;
    } else if (char === "." && dots !== -1) {
      ++dots;
    } else {
      dots = -1;
    }
  }
  return res;
}

export const isAbsolute: typeof path.isAbsolute = function (p) {
  return _IS_ABSOLUTE_RE.test(p);
};
"###;
const WINDOWS_HELPER: &str = r###"// Util to normalize windows paths to posix
export function normalizeWindowsPath(input = "") {
  if (!input) {
    return input;
  }

  let normalized = input;
  if (normalized.includes("\\")) {
    normalized = normalized.replace(/\\/g, "/");
  }

  const driveLetter = normalized[0];
  if (
    driveLetter &&
    normalized[1] === ":" &&
    normalized[2] === "/" &&
    driveLetter >= "a" &&
    driveLetter <= "z"
  ) {
    normalized = driveLetter.toUpperCase() + normalized.slice(1);
  }

  return normalized;
}
"###;
const PATH_REGEX: &str = r###"const _UNC_REGEX = /^[/\\]{2}/;
const _IS_ABSOLUTE_RE = /^[/\\](?![/\\])|^[/\\]{2}(?!\.)|^[A-Za-z]:[/\\]/;
const _DRIVE_LETTER_RE = /^[A-Za-z]:$/;
"###;
