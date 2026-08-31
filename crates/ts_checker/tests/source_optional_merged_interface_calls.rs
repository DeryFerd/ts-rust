use std::collections::HashSet;

use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, TypeMapperId, ValueSymbolLinks, signatures::SignatureFlags,
    type_records::StructuredTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(286_000);

struct Input {
    file: FileId,
    path: String,
    declaration: bool,
    library: bool,
    module: CanonicalModuleState,
    parsed: ParseResult,
}

fn source(text: &str, module: CanonicalModuleState) -> Input {
    Input {
        file: SOURCE,
        path: "\"/project/optional-interface-calls.ts\"".to_owned(),
        declaration: false,
        library: false,
        module,
        parsed: parse_source_file(text),
    }
}

fn context(inputs: &[Input], strict: bool, exact: bool) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in inputs {
        assert!(
            input.parsed.diagnostics.is_empty(),
            "{}: {:?}",
            input.path,
            input.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(&input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.declaration,
                    input.library,
                    input.module,
                ),
            )
            .unwrap();
    }
    for input in inputs {
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        inputs
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: strict,
                exact_optional_property_types: exact,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(input: &Input, node: NodeId) -> NodeRef {
    NodeRef::new(input.parsed.arena.id(), input.file, node)
}

fn nodes(input: &Input, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut result = input
        .parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(input, id)))
        .collect::<Vec<_>>();
    result.sort_by_key(|node| input.parsed.arena.get(node.node).unwrap().range.start);
    result
}

fn interfaces(input: &Input, expected: &str) -> Vec<NodeRef> {
    nodes(input, SyntaxKind::InterfaceDeclaration)
        .into_iter()
        .filter(|node| {
            let NodeData::InterfaceDeclaration(data) =
                &input.parsed.arena.get(node.node).unwrap().data
            else {
                unreachable!();
            };
            matches!(&input.parsed.arena.get(data.name).unwrap().data,
                NodeData::Identifier(name) if name.text == expected)
        })
        .collect()
}

fn raw_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(raw_symbol(context, node))
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration or checked call must retain its signature")
}

fn callee(input: &Input, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(data) = &input.parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the original call expression");
    };
    node(input, data.expression)
}

const fn structured(data: &TypeData) -> &StructuredTypeData {
    match data {
        TypeData::Object(data) => &data.structured,
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::TypeReference(data) => &data.object.structured,
        _ => panic!("the interface call must retain its structured owner"),
    }
}

struct Parameter {
    declaration: NodeRef,
    annotation: NodeRef,
    optional: bool,
}

struct CallRow {
    declaration: NodeRef,
    parameters: Vec<Parameter>,
    returned: NodeRef,
}

fn call_rows(input: &Input, name: &str) -> Vec<CallRow> {
    interfaces(input, name)
        .into_iter()
        .flat_map(|declaration| {
            let NodeData::InterfaceDeclaration(data) =
                &input.parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!();
            };
            data.members.nodes.iter().filter_map(|&member| {
                let NodeData::CallSignatureDeclaration(data) =
                    &input.parsed.arena.get(member).unwrap().data
                else {
                    return None;
                };
                Some(CallRow {
                    declaration: node(input, member),
                    parameters: data
                        .parameters
                        .nodes
                        .iter()
                        .map(|&parameter| {
                            let NodeData::ParameterDeclaration(data) =
                                &input.parsed.arena.get(parameter).unwrap().data
                            else {
                                panic!("expected the original declared parameter");
                            };
                            assert!(data.initializer.is_none());
                            assert!(data.dot_dot_dot_token.is_none());
                            Parameter {
                                declaration: node(input, parameter),
                                annotation: node(input, data.type_.unwrap()),
                                optional: data.question_token.is_some(),
                            }
                        })
                        .collect(),
                    returned: node(input, data.type_.unwrap()),
                })
            })
        })
        .collect()
}

fn assert_optional(
    context: &CanonicalCheckerContext<'_>,
    annotation: TypeId,
    value: TypeId,
    optional: bool,
) {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    if !optional || !bootstrap.options.strict_null_checks {
        assert_eq!(value, annotation);
        return;
    }
    let mut expected = match store.type_payload(annotation).unwrap().data() {
        TypeData::Union(data) => data.union.types.clone(),
        _ => vec![annotation],
    };
    expected.push(bootstrap.undefined_type);
    expected.sort_unstable();
    expected.dedup();
    let record = store.type_payload(value).unwrap();
    let TypeData::Union(data) = record.data() else {
        panic!("a strict optional parameter must keep its canonical undefined union");
    };
    assert!(record.alias().is_none());
    assert_eq!(data.union.types, expected);
    assert!(!data.union.types.contains(&bootstrap.missing_type));
    assert_eq!(bootstrap.cached_union_type(&expected), Some(value));
}

#[derive(Debug, Eq, PartialEq)]
struct RowState {
    signature: SignatureId,
    symbols: Vec<SemanticSymbolId>,
    annotations: Vec<TypeId>,
    parameters: Vec<TypeId>,
    returned: TypeId,
}

fn read_row(context: &mut CanonicalCheckerContext<'_>, row: &CallRow) -> RowState {
    let signature = signature(context, row.declaration);
    let mut symbols = Vec::new();
    let mut annotations = Vec::new();
    let mut parameters = Vec::new();
    for parameter in &row.parameters {
        let owner = symbol(context, parameter.declaration);
        let annotation = context
            .get_type_from_type_node(parameter.annotation)
            .unwrap();
        let links = context.store().value_symbol_links(owner).unwrap();
        let value = links.resolved_type.unwrap();
        assert!(links.target.is_none());
        assert!(links.mapper.is_none());
        assert_optional(context, annotation, value, parameter.optional);
        let record = context.store().symbol(owner).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
        assert_eq!(record.value_declaration(), Some(parameter.declaration));
        symbols.push(owner);
        annotations.push(annotation);
        parameters.push(value);
    }
    let returned = context.get_type_from_type_node(row.returned).unwrap();
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(returned)
    );
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(row.declaration));
    assert_eq!(record.parameters(), symbols);
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert!(record.type_parameters().is_empty());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert!(record.this_parameter().is_none());
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(row.parameters.iter().take_while(|p| !p.optional).count()).unwrap()
    );
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(record.resolved_min_argument_count(), -1);
    assert!(record.composite().is_none());
    RowState {
        signature,
        symbols,
        annotations,
        parameters,
        returned,
    }
}

fn query_annotations(context: &mut CanonicalCheckerContext<'_>, rows: &[CallRow]) {
    for row in rows {
        for parameter in &row.parameters {
            context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
        }
        context.get_type_from_type_node(row.returned).unwrap();
    }
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct CallState {
    call: NodeRef,
    callable: TypeId,
    returned: TypeId,
    signature: SignatureId,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
    minimum: i32,
    parameters: Vec<(SemanticSymbolId, ValueSymbolLinks)>,
}

fn read_call(context: &mut CanonicalCheckerContext<'_>, input: &Input, call: NodeRef) -> CallState {
    let callable = context.get_type_at_location(callee(input, call)).unwrap();
    let returned = context.get_type_at_location(call).unwrap();
    let signature = signature(context, call);
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(returned)
    );
    let record = context.store().signature(signature).unwrap();
    assert!(!record.flags().contains(SignatureFlags::CONSTRUCT));
    CallState {
        call,
        callable,
        returned,
        signature,
        target: record.target(),
        mapper: record.mapper(),
        minimum: record.min_argument_count(),
        parameters: record
            .parameters()
            .iter()
            .map(|&parameter| {
                (
                    parameter,
                    context
                        .store()
                        .value_symbol_links(parameter)
                        .unwrap()
                        .clone(),
                )
            })
            .collect(),
    }
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, input: &Input, rows: &[CallRow]) {
    let calls = nodes(input, SyntaxKind::CallExpression);
    let expected_calls = calls
        .iter()
        .map(|&call| read_call(context, input, call))
        .collect::<Vec<_>>();
    let expected_rows = rows
        .iter()
        .map(|row| read_row(context, row))
        .collect::<Vec<_>>();
    let source_file = context.source_file(input.file).unwrap();
    let warm = (
        counts(context),
        context.diagnostics().clone(),
        context.store().source_file_links(source_file).cloned(),
    );
    for _ in 0..2 {
        context.recheck_source_file(input.file).unwrap();
        for (&call, expected) in calls.iter().zip(&expected_calls) {
            assert_eq!(&read_call(context, input, call), expected);
        }
        let actual = rows
            .iter()
            .map(|row| read_row(context, row))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected_rows);
        assert_eq!(
            (
                counts(context),
                context.diagnostics().clone(),
                context.store().source_file_links(source_file).cloned(),
            ),
            warm
        );
    }
}

fn assert_argument_error(
    context: &CanonicalCheckerContext<'_>,
    input: &Input,
    diagnostic: usize,
    call: NodeRef,
    argument: usize,
    message: &str,
) {
    let NodeData::CallExpression(data) = &input.parsed.arena.get(call.node).unwrap().data else {
        unreachable!();
    };
    let diagnostic = &context.diagnostics().as_slice()[diagnostic];
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.node,
        Some(node(input, data.arguments.nodes[argument]))
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep exact diagnostics and both optional-type modes with the same source.
fn optional_interface_calls_keep_annotation_types_and_strict_undefined() {
    let inputs = [source(
        concat!(
            "interface Reader { (value: string, count?: number): number; }\n",
            "declare const read: Reader;\n",
            "const omitted: number = read('one');\n",
            "const supplied: number = read('two', 2);\n",
            "const explicitUndefined: number = read('three', undefined);\n",
            "read('bad', 'no');\n",
            "read('null', null);\n",
            "read();\n",
        ),
        CanonicalModuleState::Script,
    )];
    let input = &inputs[0];
    let rows = call_rows(input, "Reader");
    assert_eq!(rows.len(), 1);
    let calls = nodes(input, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 6);
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        for annotation_first in [false, true] {
            let mut context = context(&inputs, strict, exact);
            if annotation_first {
                query_annotations(&mut context, &rows);
            }
            context.check_source_file(SOURCE).unwrap();
            let row = read_row(&mut context, &rows[0]);
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(row.annotations, [string, number]);
            assert_eq!(row.returned, number);
            for &call in &calls {
                let actual = read_call(&mut context, input, call);
                assert_eq!(actual.signature, row.signature);
                assert_eq!(actual.returned, number);
                assert_eq!(actual.minimum, 1);
            }
            assert_eq!(context.diagnostics().len(), if strict { 3 } else { 2 });
            assert_argument_error(
                &context,
                input,
                0,
                calls[3],
                1,
                if strict {
                    "Argument of type '\"no\"' is not assignable to parameter of type 'number | undefined'."
                } else {
                    "Argument of type 'string' is not assignable to parameter of type 'number'."
                },
            );
            if strict {
                assert_argument_error(
                    &context,
                    input,
                    1,
                    calls[4],
                    1,
                    "Argument of type 'null' is not assignable to parameter of type 'number | undefined'.",
                );
            }
            let missing = context.diagnostics().as_slice().last().unwrap();
            assert_eq!(missing.diagnostic.code(), 2554);
            assert_eq!(missing.node, Some(callee(input, calls[5])));
            assert!(missing.range_override.is_none());
            assert_eq!(
                missing.diagnostic.render().unwrap(),
                "Expected 1-2 arguments, but got 0."
            );
            let [related] = missing.related_information.as_slice() else {
                panic!("the missing argument must identify the real required parameter");
            };
            assert_eq!(related.diagnostic.code(), 6210);
            assert_eq!(related.node, Some(rows[0].parameters[0].declaration));
            assert_eq!(
                related.diagnostic.render().unwrap(),
                "An argument for 'value' was not provided."
            );
            assert_replay(&mut context, input, &rows);
        }
    }
}

#[test]
fn optional_interface_overloads_keep_minimum_arity_and_declaration_order() {
    let inputs = [source(
        concat!(
            "interface Request { path: string; }\n",
            "interface Options { secure: boolean; }\n",
            "interface Cookie {\n",
            "  (request: Request): boolean;\n",
            "  (request: Request, name: string): string;\n",
            "  (request: Request, name: string, options?: Options): number;\n",
            "}\n",
            "interface Style { (options?: Options): string; }\n",
            "declare const cookie: Cookie;\n",
            "declare const request: Request;\n",
            "declare const options: Options;\n",
            "declare const style: Style;\n",
            "const all: boolean = cookie(request);\n",
            "const named: string = cookie(request, 'name');\n",
            "const configured: number = cookie(request, 'name', options);\n",
            "const explicitUndefined: number = cookie(request, 'name', undefined);\n",
            "const empty: string = style();\n",
            "const undefinedStyle: string = style(undefined);\n",
            "const configuredStyle: string = style(options);\n",
        ),
        CanonicalModuleState::Script,
    )];
    let input = &inputs[0];
    let mut rows = call_rows(input, "Cookie");
    rows.extend(call_rows(input, "Style"));
    assert_eq!(rows.len(), 4);
    let calls = nodes(input, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 7);
    for annotation_first in [false, true] {
        let mut context = context(&inputs, true, true);
        if annotation_first {
            query_annotations(&mut context, &rows);
        }
        context.check_source_file(SOURCE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let states = rows
            .iter()
            .map(|row| read_row(&mut context, row))
            .collect::<Vec<_>>();
        for (state, minimum) in states.iter().zip([1, 2, 2, 0]) {
            assert_eq!(
                context
                    .store()
                    .signature(state.signature)
                    .unwrap()
                    .min_argument_count(),
                minimum
            );
        }
        for (&call, selected) in calls.iter().zip([0, 1, 2, 2, 3, 3, 3]) {
            let actual = read_call(&mut context, input, call);
            assert_eq!(actual.signature, states[selected].signature);
            assert_eq!(actual.returned, states[selected].returned);
        }
        let callable = context
            .get_type_at_location(callee(input, calls[0]))
            .unwrap();
        let stored = structured(context.store().type_payload(callable).unwrap().data());
        let expected = states[..3]
            .iter()
            .map(|row| row.signature)
            .collect::<Vec<_>>();
        assert_eq!(stored.signatures.as_deref(), Some(expected.as_slice()));
        assert_eq!(stored.call_signature_count, 3);
        assert_replay(&mut context, input, &rows);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare both real receiver mappings and their optional parameter values.
fn exported_generic_optional_calls_keep_original_and_copied_parameters() {
    let inputs = [source(
        concat!(
            "export interface Optional<T> { (required: string, options?: T): T; }\n",
            "declare const numeric: Optional<number>;\n",
            "declare const textual: Optional<string>;\n",
            "const first: number = numeric('one');\n",
            "const second: number = numeric('two', 2);\n",
            "const third: number = numeric('three', undefined);\n",
            "const fourth: string = textual('four');\n",
            "const fifth: string = textual('five', 'value');\n",
            "const sixth: string = textual('six', undefined);\n",
            "numeric('bad', 'wrong');\n",
            "textual('bad', 1);\n",
        ),
        CanonicalModuleState::External,
    )];
    let input = &inputs[0];
    let rows = call_rows(input, "Optional");
    assert_eq!(rows.len(), 1);
    let calls = nodes(input, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 8);
    for strict in [false, true] {
        for annotation_first in [false, true] {
            let mut context = context(&inputs, strict, false);
            if annotation_first {
                query_annotations(&mut context, &rows);
            }
            context.check_source_file(SOURCE).unwrap();
            let row = read_row(&mut context, &rows[0]);
            let declaration = interfaces(input, "Optional")[0];
            let owner = symbol(&context, declaration);
            let target = context.get_declared_type_of_symbol(owner).unwrap();
            let formal_node = nodes(input, SyntaxKind::TypeParameter)[0];
            let formal_owner = symbol(&context, formal_node);
            let formal = context.get_declared_type_of_symbol(formal_owner).unwrap();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(row.annotations, [string, formal]);
            assert_eq!(row.returned, formal);
            assert_eq!(
                context.store().type_payload(formal).unwrap().symbol(),
                Some(formal_owner)
            );
            let TypeData::Interface(data) = context.store().type_payload(target).unwrap().data()
            else {
                panic!("the exported declaration must keep its generic interface target");
            };
            assert_eq!(
                data.declared_call_signatures.as_deref(),
                Some(&[row.signature][..])
            );
            let mut selected = Vec::new();
            for (&call, argument) in calls.iter().zip([
                number, number, number, string, string, string, number, string,
            ]) {
                let actual = read_call(&mut context, input, call);
                assert_ne!(actual.signature, row.signature);
                assert_eq!(actual.target, Some(row.signature));
                assert_eq!(actual.minimum, 1);
                assert_eq!(actual.returned, argument);
                let mapper = actual.mapper.unwrap();
                let store = context.store();
                let TypeData::TypeReference(reference) =
                    store.type_payload(actual.callable).unwrap().data()
                else {
                    panic!("the call must retain its actual applied interface");
                };
                assert_eq!(reference.object.target, Some(target));
                assert_eq!(
                    reference.resolved_type_arguments.as_deref(),
                    Some(&[argument][..])
                );
                assert_eq!(reference.object.structured.call_signature_count, 1);
                assert_eq!(
                    reference.object.structured.signatures.as_deref(),
                    Some(&[actual.signature][..])
                );
                assert_eq!(store.map_type(mapper, formal), Some(argument));
                assert_eq!(
                    store.signature(actual.signature).unwrap().declaration(),
                    Some(rows[0].declaration)
                );
                assert!(
                    store
                        .signature(actual.signature)
                        .unwrap()
                        .type_parameters()
                        .is_empty()
                );
                assert_eq!(
                    store
                        .signature(actual.signature)
                        .unwrap()
                        .resolved_return_type(),
                    Some(argument)
                );
                assert_eq!(
                    store
                        .signature(actual.signature)
                        .unwrap()
                        .resolved_min_argument_count(),
                    -1
                );
                assert!(
                    store
                        .signature(actual.signature)
                        .unwrap()
                        .composite()
                        .is_none()
                );
                assert_eq!(actual.parameters.len(), 2);
                for (index, (parameter, links)) in actual.parameters.iter().enumerate() {
                    assert_ne!(*parameter, row.symbols[index]);
                    assert_eq!(links.target, Some(row.symbols[index]));
                    assert_eq!(links.mapper, Some(mapper));
                    assert_optional(
                        &context,
                        if index == 0 { string } else { argument },
                        links.resolved_type.unwrap(),
                        index == 1,
                    );
                }
                selected.push(actual.signature);
            }
            assert_eq!(selected[0], selected[1]);
            assert_eq!(selected[0], selected[2]);
            assert_eq!(selected[0], selected[6]);
            assert_eq!(selected[3], selected[4]);
            assert_eq!(selected[3], selected[5]);
            assert_eq!(selected[3], selected[7]);
            assert_ne!(selected[0], selected[3]);
            assert_eq!(context.diagnostics().len(), 2);
            assert_argument_error(
                &context,
                input,
                0,
                calls[6],
                1,
                if strict {
                    "Argument of type '\"wrong\"' is not assignable to parameter of type 'number | undefined'."
                } else {
                    "Argument of type 'string' is not assignable to parameter of type 'number'."
                },
            );
            assert_argument_error(
                &context,
                input,
                1,
                calls[7],
                1,
                if strict {
                    "Argument of type '1' is not assignable to parameter of type 'string | undefined'."
                } else {
                    "Argument of type 'number' is not assignable to parameter of type 'string'."
                },
            );
            assert_replay(&mut context, input, &rows);
        }
    }
}

// Keep all six real SymbolConstructor contributors and their reference-lib closure.
const SYMBOL_LIBRARIES: &[(&str, &str)] = &[
    (
        "lib.es5.d.ts",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        "lib.es2015.symbol.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
    ),
    (
        "lib.es2015.iterable.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2015.iterable.d.ts"),
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
        "lib.es2020.symbol.wellknown.d.ts",
        include_str!("../../ts_bundled/libs/lib.es2020.symbol.wellknown.d.ts"),
    ),
    (
        "lib.esnext.disposable.d.ts",
        include_str!("../../ts_bundled/libs/lib.esnext.disposable.d.ts"),
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

#[allow(clippy::too_many_lines)] // Prove every raw contributor and member against the complete merged Call owner.
fn assert_merged_owner(
    context: &mut CanonicalCheckerContext<'_>,
    inputs: &[Input],
    name: &str,
    expected_declarations: usize,
    expected_calls: usize,
) -> (TypeId, Vec<CallRow>) {
    let declarations = inputs
        .iter()
        .flat_map(|input| interfaces(input, name))
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), expected_declarations);
    let owner = symbol(context, declarations[0]);
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    let store = context.store();
    let record = store.symbol(owner).unwrap();
    assert_eq!(
        record.flags().without(SymbolFlags::TRANSIENT),
        SymbolFlags::INTERFACE
    );
    assert_eq!(record.declarations(), Some(declarations.as_slice()));
    assert!(record.value_declaration().is_none());
    let table = store.symbol_table(record.members().unwrap()).unwrap();
    assert!(table.get(InternalSymbolName::New.as_ref()).is_none());
    let call_owner = table.get(InternalSymbolName::Call.as_ref()).unwrap();
    let call_owner = store.get_merged_symbol(call_owner).unwrap();
    let mut members = HashSet::new();
    for declaration in &declarations {
        let raw_owner = raw_symbol(context, *declaration);
        assert_eq!(store.get_merged_symbol(raw_owner), Some(owner));
        assert_ne!(raw_owner, owner);
        let input = inputs
            .iter()
            .find(|input| input.file == declaration.file)
            .unwrap();
        let NodeData::InterfaceDeclaration(data) =
            &input.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        for &member in &data.members.nodes {
            let declaration = node(input, member);
            let raw = raw_symbol(context, declaration);
            let canonical = store.get_merged_symbol(raw).unwrap();
            let raw_record = store.symbol(raw).unwrap();
            assert_eq!(raw_record.parent(), Some(raw_owner));
            assert_eq!(store.get_parent_of_symbol(canonical), Some(owner));
            assert_eq!(
                table
                    .get(raw_record.name())
                    .and_then(|id| store.get_merged_symbol(id)),
                Some(canonical)
            );
            assert!(
                store
                    .symbol(canonical)
                    .unwrap()
                    .declarations()
                    .unwrap()
                    .contains(&declaration)
            );
            members.insert(canonical);
        }
    }
    assert_eq!(table.len(), members.len());
    assert_eq!(store.type_payload(type_).unwrap().symbol(), Some(owner));
    let rows = inputs
        .iter()
        .flat_map(|input| call_rows(input, name))
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), expected_calls);
    let call_declarations = rows.iter().map(|row| row.declaration).collect::<Vec<_>>();
    assert_eq!(
        store.symbol(call_owner).unwrap().declarations(),
        Some(call_declarations.as_slice())
    );
    assert_ne!(store.symbol(call_owner).unwrap().parent(), Some(owner));
    assert_eq!(
        store
            .symbol(call_owner)
            .unwrap()
            .flags()
            .without(SymbolFlags::TRANSIENT),
        SymbolFlags::SIGNATURE
    );
    let raw_calls = rows
        .iter()
        .map(|row| raw_symbol(context, row.declaration))
        .collect::<Vec<_>>();
    for &raw in &raw_calls {
        assert_eq!(store.get_merged_symbol(raw), Some(call_owner));
        if expected_calls > 1 {
            assert_ne!(raw, call_owner);
        }
    }
    assert_eq!(
        raw_calls.iter().copied().collect::<HashSet<_>>().len(),
        expected_calls
    );
    let signatures = structured(store.type_payload(type_).unwrap().data());
    let expected = rows
        .iter()
        .map(|row| signature(context, row.declaration))
        .collect::<Vec<_>>();
    assert_eq!(
        expected.iter().copied().collect::<HashSet<_>>().len(),
        expected_calls
    );
    assert_eq!(signatures.call_signature_count, expected_calls);
    assert_eq!(signatures.signatures.as_deref(), Some(expected.as_slice()));
    (type_, rows)
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the full real library group and the renamed two-call group together.
fn real_symbol_and_renamed_merged_calls_keep_all_contributors() {
    let mut inputs = SYMBOL_LIBRARIES
        .iter()
        .enumerate()
        .map(|(index, (name, text))| Input {
            file: FileId::new(286_100 + u32::try_from(index).unwrap()),
            path: format!("\"/__typescript/lib/{name}\""),
            declaration: true,
            library: true,
            module: CanonicalModuleState::Script,
            parsed: parse_source_file(text),
        })
        .collect::<Vec<_>>();
    for (file, path, text) in [
        (
            286_200,
            "\"/types/renamed-call.d.ts\"",
            concat!(
                "interface RenamedFactory {\n",
                "  readonly prototype: Symbol;\n",
                "  (description?: string | number): symbol;\n",
                "  for(key: string): symbol;\n",
                "  keyFor(sym: symbol): string | undefined;\n",
                "}\n",
                "declare var Renamed: RenamedFactory;\n",
            ),
        ),
        (
            286_201,
            "\"/types/renamed-extra.d.ts\"",
            "interface RenamedFactory { readonly marker: number; (enabled: boolean): boolean; }\n",
        ),
        (
            286_202,
            "\"/types/grouped-first.d.ts\"",
            concat!(
                "interface GroupedFactory { (value: string): number; }\n",
                "declare var grouped: GroupedFactory;\n",
            ),
        ),
        (
            286_203,
            "\"/types/grouped-second.d.ts\"",
            "interface GroupedFactory { (value: string): string; }\n",
        ),
    ] {
        inputs.push(Input {
            file: FileId::new(file),
            path: path.to_owned(),
            declaration: true,
            library: false,
            module: CanonicalModuleState::Script,
            parsed: parse_source_file(text),
        });
    }
    inputs.push(Input {
        file: FileId::new(286_204),
        path: "\"/project/grouped-interface-call.ts\"".to_owned(),
        declaration: false,
        library: false,
        module: CanonicalModuleState::Script,
        parsed: parse_source_file("const groupedValue: string = grouped('value');\n"),
    });
    inputs.push(source(
        concat!(
            "const empty: symbol = Symbol();\n",
            "const text: symbol = Symbol('RENDERER');\n",
            "const number: symbol = Symbol(1);\n",
            "const absent: symbol = Symbol(undefined);\n",
            "const renamedEmpty: symbol = Renamed();\n",
            "const renamedText: symbol = Renamed('RENDERER');\n",
            "const renamedNumber: symbol = Renamed(1);\n",
            "const renamedAbsent: symbol = Renamed(undefined);\n",
            "const renamedBoolean: boolean = Renamed(true);\n",
        ),
        CanonicalModuleState::Script,
    ));
    let input = inputs.last().unwrap();
    let calls = nodes(input, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 9);
    let grouped_input = inputs
        .iter()
        .find(|input| input.file == FileId::new(286_204))
        .unwrap();
    let grouped_calls = nodes(grouped_input, SyntaxKind::CallExpression);
    assert_eq!(grouped_calls.len(), 1);
    for query_first in [false, true] {
        let mut context = context(&inputs, true, true);
        let early = query_first.then(|| {
            [calls[0], calls[4]]
                .map(|call| context.get_type_at_location(callee(input, call)).unwrap())
        });
        let early_grouped = query_first.then(|| {
            context
                .get_type_at_location(callee(grouped_input, grouped_calls[0]))
                .unwrap()
        });
        context.check_source_file(SOURCE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let (original, mut rows) =
            assert_merged_owner(&mut context, &inputs, "SymbolConstructor", 6, 1);
        let (renamed, renamed_rows) =
            assert_merged_owner(&mut context, &inputs, "RenamedFactory", 2, 2);
        assert_ne!(original, renamed);
        rows.extend(renamed_rows);
        let states = rows
            .iter()
            .map(|row| read_row(&mut context, row))
            .collect::<Vec<_>>();
        let es_symbol = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .es_symbol_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
        let mut annotation_types = [string, number];
        annotation_types.sort_unstable();
        for state in &states[..2] {
            assert_eq!(state.returned, es_symbol);
            let TypeData::Union(data) = context
                .store()
                .type_payload(state.annotations[0])
                .unwrap()
                .data()
            else {
                panic!("the written call annotation must remain string or number");
            };
            assert_eq!(data.union.types, annotation_types);
            assert_eq!(
                context
                    .store()
                    .signature(state.signature)
                    .unwrap()
                    .min_argument_count(),
                0
            );
        }
        assert_eq!(states[2].annotations, [boolean]);
        assert_eq!(states[2].parameters, [boolean]);
        assert_eq!(states[2].returned, boolean);
        assert_eq!(
            context
                .store()
                .signature(states[2].signature)
                .unwrap()
                .min_argument_count(),
            1
        );
        for (index, &call) in calls.iter().enumerate() {
            let actual = read_call(&mut context, input, call);
            let selected = if index < 4 {
                0
            } else if index < 8 {
                1
            } else {
                2
            };
            assert_eq!(actual.signature, states[selected].signature);
            assert_eq!(actual.callable, [original, renamed, renamed][selected]);
            assert_eq!(actual.returned, states[selected].returned);
            assert_eq!(actual.minimum, i32::from(selected == 2));
            assert!(actual.target.is_none());
            assert!(actual.mapper.is_none());
        }
        if let Some(early) = early {
            assert_eq!(early, [original, renamed]);
        }
        assert_replay(&mut context, input, &rows);

        context.check_source_file(grouped_input.file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let (grouped, grouped_rows) =
            assert_merged_owner(&mut context, &inputs, "GroupedFactory", 2, 2);
        assert_ne!(grouped, original);
        assert_ne!(grouped, renamed);
        let grouped_states = grouped_rows
            .iter()
            .map(|row| read_row(&mut context, row))
            .collect::<Vec<_>>();
        for (state, returned) in grouped_states.iter().zip([number, string]) {
            assert_eq!(state.annotations, [string]);
            assert_eq!(state.parameters, [string]);
            assert_eq!(state.returned, returned);
            assert_eq!(
                context
                    .store()
                    .signature(state.signature)
                    .unwrap()
                    .min_argument_count(),
                1
            );
        }
        let actual = read_call(&mut context, grouped_input, grouped_calls[0]);
        assert_eq!(actual.callable, grouped);
        assert_eq!(actual.signature, grouped_states[1].signature);
        assert_ne!(actual.signature, grouped_states[0].signature);
        assert_eq!(actual.returned, string);
        assert_eq!(actual.minimum, 1);
        assert!(actual.target.is_none());
        assert!(actual.mapper.is_none());
        if let Some(early) = early_grouped {
            assert_eq!(early, grouped);
        }
        assert_replay(&mut context, grouped_input, &grouped_rows);
        assert_replay(&mut context, input, &rows);
    }
}
