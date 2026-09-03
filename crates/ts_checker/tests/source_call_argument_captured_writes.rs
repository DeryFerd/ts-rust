use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(207_840);
const SOURCE_FILE: FileId = FileId::new(207_841);
const LIBRARY: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY_FILE, library, "\"/lib/lib.es5.d.ts\"", true),
        (
            SOURCE_FILE,
            source,
            "\"/project/call-argument-captured-writes.ts\"",
            false,
        ),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path, library) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
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
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), SOURCE_FILE, id)
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)));
    let result = nodes.next().expect("the written node must exist");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    result
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(SOURCE_FILE)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn call_signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected the real callable type")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one fixed signature")
    };
    *signature
}

#[derive(Debug, PartialEq, Eq)]
struct Observed {
    callback_type: TypeId,
    callback_signature: SignatureId,
    selected_signature: SignatureId,
    parameter_type: TypeId,
    declared_capture: TypeId,
    outer_return: TypeId,
}

fn check_capture(declared: &str, initializer: &str, parameter: &str, returned: &str, bad: bool) {
    let text = format!(
        "export function capture(run: (callback: (value: {parameter}) => {parameter}) => void): {returned} {{\n\
         let data: {declared}{initializer};\n\
         run((value) => {{ data = value; return value; }});\n\
         return data;\n\
         }}"
    );
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(&text);
    let function = only_node(&parsed, SyntaxKind::FunctionDeclaration);
    let arrow = only_node(&parsed, SyntaxKind::ArrowFunction);
    let call = only_node(&parsed, SyntaxKind::CallExpression);
    let assignment = only_node(&parsed, SyntaxKind::BinaryExpression);
    let local = only_node(&parsed, SyntaxKind::VariableDeclaration);
    let NodeData::FunctionDeclaration(function_data) =
        &parsed.arena.get(function.node).unwrap().data
    else {
        unreachable!()
    };
    let run = node(&parsed, function_data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(run_data) = &parsed.arena.get(run.node).unwrap().data else {
        unreachable!()
    };
    let run_annotation = node(&parsed, run_data.type_.unwrap());
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(arrow_data.parameters.nodes.len(), 1);
    let parameter_node = node(&parsed, arrow_data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter_node.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter_data.type_.is_none());
    let parameter_name = node(&parsed, parameter_data.name);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(call_data.arguments.nodes.as_slice(), &[arrow.node]);
    assert_eq!(
        parsed.arena.get(arrow.node).unwrap().parent,
        Some(call.node)
    );
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        unreachable!()
    };
    let target = node(&parsed, binary.left);
    let right = node(&parsed, binary.right);
    let NodeData::VariableDeclaration(local_data) = &parsed.arena.get(local.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = node(&parsed, local_data.type_.unwrap());
    let mut returns = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ReturnStatement(returned) = &record.data else {
                return None;
            };
            Some((
                record.parent.unwrap(),
                node(&parsed, returned.expression.unwrap()),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(returns.len(), 2);
    let callback_return = returns
        .remove(
            returns
                .iter()
                .position(|(parent, _)| *parent == arrow_data.body)
                .unwrap(),
        )
        .1;
    let (outer_body, outer_return) = returns.pop().unwrap();
    assert_eq!(Some(outer_body), function_data.body);

    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        assert!(context.global_type_diagnostics().next().is_none());
        let parameter_symbol = symbol(&context, parameter_node);
        let local_symbol = symbol(&context, local);
        let callback_owner = symbol(&context, arrow);
        assert!(context.store().signature_links(arrow).is_none());
        let early = query_first.then(|| context.get_type_at_location(parameter_name).unwrap());
        context.check_source_file(SOURCE_FILE).unwrap();
        if bad {
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!(
                    "expected only the captured assignment error: {:?}",
                    context.diagnostics()
                )
            };
            assert_eq!(diagnostic.node, Some(target));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' is not assignable to type 'string'."
            );
            assert!(diagnostic.related_information.is_empty());
        } else {
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        }
        let diagnostics = context.diagnostics().as_slice().to_vec();
        let observe = |context: &mut CanonicalCheckerContext<'_>| {
            let parameter_type = context.get_type_at_location(parameter_name).unwrap();
            assert_eq!(context.type_to_string(parameter_type).unwrap(), parameter);
            assert_eq!(value_type(context, parameter_symbol), parameter_type);
            for location in [right, callback_return] {
                assert_eq!(
                    context.get_symbol_at_location(location),
                    Ok(Some(parameter_symbol))
                );
                assert_eq!(context.get_type_at_location(location), Ok(parameter_type));
            }
            let declared_capture = context.get_type_from_type_node(annotation).unwrap();
            assert_eq!(value_type(context, local_symbol), declared_capture);
            assert_eq!(
                context.get_symbol_at_location(target),
                Ok(Some(local_symbol))
            );
            assert_eq!(
                context.get_symbol_at_location(outer_return),
                Ok(Some(local_symbol))
            );
            assert_eq!(context.get_type_at_location(assignment), Ok(parameter_type));
            let outer_return_type = context.get_type_at_location(outer_return).unwrap();
            assert_eq!(context.type_to_string(outer_return_type).unwrap(), returned);
            if declared == "unknown" {
                assert_eq!(declared_capture, parameter_type);
                assert_eq!(outer_return_type, parameter_type);
            } else if !bad {
                let TypeData::Union(union) = context
                    .store()
                    .type_payload(declared_capture)
                    .unwrap()
                    .data()
                else {
                    panic!("the capture must keep its declared union")
                };
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&parameter_type));
                assert!(union.union.types.contains(&outer_return_type));
                assert_ne!(parameter_type, outer_return_type);
            }
            let callback_type = context.get_type_at_location(arrow).unwrap();
            assert_eq!(value_type(context, callback_owner), callback_type);
            assert_eq!(
                context
                    .store()
                    .type_payload(callback_type)
                    .unwrap()
                    .symbol(),
                Some(callback_owner)
            );
            let owner = context.store().symbol(callback_owner).unwrap();
            assert_eq!(owner.flags(), SymbolFlags::FUNCTION);
            assert_eq!(owner.declarations(), Some(&[arrow][..]));
            assert_eq!(owner.value_declaration(), Some(arrow));
            let callback_signature = signature(context, arrow);
            assert_eq!(call_signature(context, callback_type), callback_signature);
            let record = context.store().signature(callback_signature).unwrap();
            assert_eq!(record.declaration(), Some(arrow));
            assert_eq!(record.flags(), SignatureFlags::NONE);
            assert_eq!(record.parameters(), &[parameter_symbol]);
            assert_eq!(record.min_argument_count(), 1);
            assert!(record.type_parameters().is_empty());
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            assert_eq!(
                context.get_return_type_of_signature(callback_signature),
                Ok(parameter_type)
            );
            let selected_signature = signature(context, call);
            let run_type = context.get_type_from_type_node(run_annotation).unwrap();
            assert_eq!(call_signature(context, run_type), selected_signature);
            assert_eq!(
                context
                    .store()
                    .signature(selected_signature)
                    .unwrap()
                    .declaration(),
                Some(run_annotation)
            );
            assert_eq!(value_type(context, symbol(context, run)), run_type);
            let callback_parameter = context
                .store()
                .signature(selected_signature)
                .unwrap()
                .parameters()[0];
            let expected_callback =
                call_signature(context, value_type(context, callback_parameter));
            assert_ne!(expected_callback, callback_signature);
            let expected_parameter = context
                .store()
                .signature(expected_callback)
                .unwrap()
                .parameters()[0];
            assert_eq!(value_type(context, expected_parameter), parameter_type);
            assert_eq!(
                context.get_return_type_of_signature(expected_callback),
                Ok(parameter_type)
            );
            let bound = context.file(SOURCE_FILE).unwrap().1;
            assert_eq!(bound.container(local), Some(function));
            assert_eq!(bound.container(call), Some(function));
            assert_eq!(bound.container(target), Some(arrow));
            assert_eq!(bound.flow_container(target), Some(arrow));
            assert_eq!(bound.container(outer_return), Some(function));
            Observed {
                callback_type,
                callback_signature,
                selected_signature,
                parameter_type,
                declared_capture,
                outer_return: outer_return_type,
            }
        };
        let observed = observe(&mut context);
        if let Some(early) = early {
            assert_eq!(early, observed.parameter_type);
        }
        for _ in 0..2 {
            context.check_source_file(SOURCE_FILE).unwrap();
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(observe(&mut context), observed);
            assert_eq!(context.diagnostics().as_slice(), diagnostics);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn call_argument_write_keeps_the_outer_unknown_type() {
    check_capture("unknown", "", "unknown", "unknown", false);
}

#[test]
fn call_argument_write_does_not_change_outer_flow() {
    check_capture(
        "string | number",
        " = \"before\"",
        "number",
        "string",
        false,
    );
}

#[test]
fn call_argument_write_keeps_the_native_assignment_error() {
    check_capture("string", " = \"before\"", "number", "string", true);
}
