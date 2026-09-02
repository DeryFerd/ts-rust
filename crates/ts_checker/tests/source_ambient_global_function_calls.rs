use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(0);
const DECORATORS: FileId = FileId::new(1);
const LEGACY_DECORATORS: FileId = FileId::new(2);
const SOURCE: FileId = FileId::new(3);

struct Inputs {
    library: ParseResult,
    decorators: ParseResult,
    legacy_decorators: ParseResult,
    source: ParseResult,
}

impl Inputs {
    fn new(source: &str) -> Self {
        Self {
            library: parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
            decorators: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.d.ts"
            )),
            legacy_decorators: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.legacy.d.ts"
            )),
            source: parse_source_file(source),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = [
            (LIBRARY, &self.library, "/lib.es5.d.ts"),
            (DECORATORS, &self.decorators, "/lib.decorators.d.ts"),
            (
                LEGACY_DECORATORS,
                &self.legacy_decorators,
                "/lib.decorators.legacy.d.ts",
            ),
            (SOURCE, &self.source, "/consumer.ts"),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in files {
            assert!(parsed.diagnostics.is_empty(), "{path}: {:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        file != SOURCE,
                        file != SOURCE,
                        if file == SOURCE {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
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
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.diagnostics().is_empty());
        context
    }
}

fn library_function(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            assert!(function.body.is_none());
            Some(NodeRef::new(parsed.arena.id(), LIBRARY, node))
        })
        .unwrap_or_else(|| panic!("missing library function {expected}"))
}

fn calls(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression)
                .then_some(NodeRef::new(parsed.arena.id(), SOURCE, node))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
    calls
}

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a source call")
    };
    NodeRef::new(call.arena, call.file, call_data.expression)
}

fn argument(parsed: &ParseResult, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a source call")
    };
    NodeRef::new(call.arena, call.file, call_data.arguments.nodes[index])
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration and its calls must retain their signatures")
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> Vec<TypeId> {
    context
        .store()
        .signature(signature(context, declaration))
        .unwrap()
        .parameters()
        .iter()
        .map(|parameter| {
            context
                .store()
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .unwrap()
        })
        .collect()
}

fn assert_library_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    declaration: NodeRef,
    result: TypeId,
) {
    let raw = context.file(LIBRARY).unwrap().1.symbol(declaration).unwrap();
    let owner = context.store().get_merged_symbol(raw).unwrap();
    let declared = signature(context, declaration);
    let record = context.store().signature(declared).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.resolved_return_type(), Some(result));
    assert!(record.type_parameters().is_empty());
    assert_eq!(signature(context, call), declared);
    assert_eq!(
        context.store().type_node_links(call).unwrap().resolved_type,
        Some(result),
    );
    assert_eq!(context.get_type_at_location(call), Ok(result));
    let callee = callee(parsed, call);
    assert_eq!(context.get_symbol_at_location(callee), Ok(Some(owner)));
    let callable = context.get_type_at_location(callee).unwrap();
    let payload = context.store().type_payload(callable).unwrap();
    assert_eq!(payload.symbol(), Some(owner));
    let TypeData::Object(object) = payload.data() else {
        panic!("the library function must keep its callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(object.structured.signatures.as_deref(), Some(&[declared][..]));
}

fn assert_libraries_unchecked(context: &CanonicalCheckerContext<'_>) {
    for file in [LIBRARY, DECORATORS, LEGACY_DECORATORS] {
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_some_and(|links| links.type_checked),
        );
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    calls: &[NodeRef],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            context.diagnostics().clone(),
            calls
                .iter()
                .map(|call| {
                    (
                        context.store().type_node_links(*call).cloned(),
                        context.store().signature_links(*call).cloned(),
                        context
                            .store()
                            .symbol_node_links(callee(parsed, *call))
                            .cloned(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let warm = snapshot(context);
    for _ in 0..2 {
        context.recheck_source_file(SOURCE).unwrap();
        for call in calls {
            let expected = context
                .store()
                .type_node_links(*call)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(context.get_type_at_location(*call), Ok(expected));
        }
        assert_libraries_unchecked(context);
        assert_eq!(snapshot(context), warm);
    }
}

#[test]
fn real_library_global_calls_keep_union_parameters_and_canonical_signatures() {
    let inputs = Inputs::new(concat!(
        "export {};\n",
        "function encodeHeader(value: string): string { return encodeURIComponent(value); }\n",
        "const text: string = encodeURIComponent('x y');\n",
        "const numeric: string = encodeURIComponent(42);\n",
        "const flag: string = encodeURIComponent(true);\n",
        "const decimal: number = parseInt('42');\n",
        "const hexadecimal: number = parseInt('ff', 16);\n",
        "const finite: boolean = isFinite(1);\n",
    ));
    let encode = library_function(&inputs.library, "encodeURIComponent");
    let parse = library_function(&inputs.library, "parseInt");
    let finite = library_function(&inputs.library, "isFinite");
    let calls = calls(&inputs.source);
    assert_eq!(calls.len(), 7);

    for query_first in [false, true] {
        let mut context = inputs.context();
        assert!(context.store().signature_links(encode).is_none());
        assert_libraries_unchecked(&context);
        let early = query_first.then(|| {
            context
                .get_type_at_location(callee(&inputs.source, calls[0]))
                .unwrap()
        });
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let boolean = bootstrap.boolean_type;
        let undefined = bootstrap.undefined_type;
        for (call, (declaration, result)) in calls.iter().copied().zip([
            (encode, string),
            (encode, string),
            (encode, string),
            (encode, string),
            (parse, number),
            (parse, number),
            (finite, boolean),
        ]) {
            assert_library_call(&mut context, &inputs.source, call, declaration, result);
        }
        if let Some(early) = early {
            assert_eq!(
                context.get_type_at_location(callee(&inputs.source, calls[0])),
                Ok(early),
            );
        }
        let encode_parameters = parameter_types(&context, encode);
        assert_eq!(encode_parameters.len(), 1);
        assert_eq!(
            context.type_to_string(encode_parameters[0]).unwrap(),
            "string | number | boolean",
        );
        let parse_signature = context.store().signature(signature(&context, parse)).unwrap();
        assert_eq!(parse_signature.min_argument_count(), 1);
        let parse_parameters = parameter_types(&context, parse);
        assert_eq!(parse_parameters.len(), 2);
        assert_eq!(parse_parameters[0], string);
        let TypeData::Union(optional) = context
            .store()
            .type_payload(parse_parameters[1])
            .unwrap()
            .data()
        else {
            panic!("the optional radix parameter must include undefined")
        };
        let mut expected = [number, undefined];
        expected.sort_unstable();
        assert_eq!(optional.union.types, expected);
        assert_libraries_unchecked(&context);
        assert_replay(&mut context, &inputs.source, &calls);
    }
}

fn assert_diagnostic(
    diagnostic: &CanonicalCheckerDiagnostic,
    code: u32,
    node: NodeRef,
    message: &str,
) {
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the call ranges and library parameter note together.
fn real_library_global_calls_keep_argument_and_arity_diagnostics_on_replay() {
    let inputs = Inputs::new(concat!(
        "export {};\n",
        "const nullInput = encodeURIComponent(null);\n",
        "const wrongText = parseInt(true);\n",
        "const missing = parseInt();\n",
        "const extra = parseInt('42', 10, 8);\n",
    ));
    let encode = library_function(&inputs.library, "encodeURIComponent");
    let parse = library_function(&inputs.library, "parseInt");
    let calls = calls(&inputs.source);
    let [null_call, wrong_call, missing_call, extra_call] = calls.as_slice() else {
        panic!("the source must retain four invalid calls")
    };

    for query_first in [false, true] {
        let mut context = inputs.context();
        if query_first {
            context
                .get_type_at_location(callee(&inputs.source, *null_call))
                .unwrap();
        }
        context.check_source_file(SOURCE).unwrap();
        let [null, wrong, missing, extra] = context.diagnostics().as_slice() else {
            panic!("expected the four native call diagnostics: {:?}", context.diagnostics())
        };
        assert_diagnostic(
            null,
            2345,
            argument(&inputs.source, *null_call, 0),
            concat!(
                "Argument of type 'null' is not assignable to parameter of type ",
                "'string | number | boolean'.",
            ),
        );
        assert_diagnostic(
            wrong,
            2345,
            argument(&inputs.source, *wrong_call, 0),
            "Argument of type 'boolean' is not assignable to parameter of type 'string'.",
        );
        assert_diagnostic(
            missing,
            2554,
            callee(&inputs.source, *missing_call),
            "Expected 1-2 arguments, but got 0.",
        );
        for diagnostic in [null, wrong, missing] {
            assert!(diagnostic.range_override.is_none());
        }
        for diagnostic in [null, wrong, extra] {
            assert!(diagnostic.related_information.is_empty());
        }
        let [related] = missing.related_information.as_slice() else {
            panic!("the missing argument must point to the real library parameter")
        };
        let NodeData::FunctionDeclaration(function) =
            &inputs.library.arena.get(parse.node).unwrap().data
        else {
            panic!("parseInt must retain its library declaration")
        };
        assert_eq!(related.diagnostic.code(), 6210);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "An argument for 'string' was not provided.",
        );
        assert_eq!(
            related.node,
            Some(NodeRef::new(
                parse.arena,
                LIBRARY,
                function.parameters.nodes[0],
            )),
        );
        assert_diagnostic(
            extra,
            2554,
            *extra_call,
            "Expected 1-2 arguments, but got 3.",
        );
        let extra_range = extra.range_override.unwrap();
        assert_eq!(extra_range.anchor(), *extra_call);
        assert_eq!(
            extra_range.range(),
            inputs
                .source
                .arena
                .get(argument(&inputs.source, *extra_call, 2).node)
                .unwrap()
                .range,
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        for (call, declaration, result) in [
            (*null_call, encode, string),
            (*wrong_call, parse, number),
            (*missing_call, parse, number),
            (*extra_call, parse, number),
        ] {
            assert_library_call(&mut context, &inputs.source, call, declaration, result);
        }
        assert_libraries_unchecked(&context);
        assert_replay(&mut context, &inputs.source, &calls);
    }
}
