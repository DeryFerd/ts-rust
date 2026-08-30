use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SourceCheckError, SourceFileLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_source_file};

const FIRST: FileId = FileId::new(202_700);
const SECOND: FileId = FileId::new(202_701);
const SOURCE: FileId = FileId::new(202_702);

fn context<'a>(
    first: &'a ParseResult,
    second: &'a ParseResult,
    source: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [(FIRST, first), (SECOND, second), (SOURCE, source)];
    let mut binder = CanonicalBinder::new();
    for (file, parsed) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let path = match file {
            FIRST => "\"/project/first.d.ts\"",
            SECOND => "\"/project/second.d.ts\"",
            SOURCE => "\"/project/main.ts\"",
            _ => unreachable!(),
        };
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != SOURCE,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed)| (file, &parsed.arena))
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

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn method_name(parsed: &ParseResult, method: NodeRef) -> NodeRef {
    let NodeData::MethodSignatureDeclaration(data) = &parsed.arena.get(method.node).unwrap().data
    else {
        panic!("expected a real method signature");
    };
    NodeRef::new(method.arena, method.file, data.name)
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap_or_else(|| panic!("missing signature for {node:?}"))
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, signature: SignatureId) -> Vec<TypeId> {
    context
        .store()
        .signature(signature)
        .unwrap()
        .parameters()
        .iter()
        .map(|symbol| {
            context
                .store()
                .value_symbol_links(*symbol)
                .and_then(|links| links.resolved_type)
                .unwrap()
        })
        .collect()
}

fn assert_method_group(
    context: &mut CanonicalCheckerContext<'_>,
    declarations: &[NodeRef],
    names: &[NodeRef],
) -> (SemanticSymbolId, TypeId, Vec<SignatureId>) {
    assert_eq!(declarations.len(), names.len());
    let owner = context.get_symbol_at_location(names[0]).unwrap().unwrap();
    let callable = context.get_type_at_location(names[0]).unwrap();
    let symbol = context.store().symbol(owner).unwrap();
    assert!(symbol.flags().contains(SymbolFlags::METHOD));
    assert_eq!(symbol.declarations(), Some(declarations));
    let payload = context.store().type_payload(callable).unwrap();
    assert_eq!(payload.symbol(), Some(owner));
    let TypeData::Object(object) = payload.data() else {
        panic!("method overloads must retain their callable object");
    };
    let signatures = object.structured.signatures.as_ref().unwrap().clone();
    assert_eq!(signatures.len(), declarations.len());
    for ((&declaration, &name), &stored) in declarations.iter().zip(names).zip(&signatures) {
        let raw = context
            .file(declaration.file)
            .unwrap()
            .1
            .symbol(declaration)
            .unwrap();
        assert_eq!(context.store().get_merged_symbol(raw), Some(owner));
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(owner)));
        assert_eq!(context.get_type_at_location(name), Ok(callable));
        assert_eq!(context.get_type_at_location(declaration), Ok(callable));
        assert_eq!(signature(context, declaration), stored);
        assert_eq!(
            context.store().signature(stored).unwrap().declaration(),
            Some(declaration),
        );
    }
    (owner, callable, signatures)
}

fn assert_call(
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
    expected: &str,
) -> (SignatureId, TypeId) {
    let selected = signature(context, call);
    let result = context.get_type_at_location(call).unwrap();
    assert_eq!(context.type_to_string(result).unwrap(), expected);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(result));
    (selected, result)
}

fn assert_instantiation(
    context: &CanonicalCheckerContext<'_>,
    selected: SignatureId,
    target: SignatureId,
    parameters: &[TypeId],
) {
    assert_ne!(selected, target);
    let record = context.store().signature(selected).unwrap();
    assert_eq!(record.target(), Some(target));
    assert!(record.mapper().is_some());
    assert!(record.type_parameters().is_empty());
    assert_eq!(parameter_types(context, selected), parameters);
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    types: Vec<Option<TypeNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, files: &[(FileId, &ParseResult)]) -> Snapshot {
    let store = context.store();
    let nodes = files
        .iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), *file, node))
        })
        .collect::<Vec<_>>();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        values: nodes
            .iter()
            .filter_map(|node| context.file(node.file).unwrap().1.symbol(*node))
            .map(|symbol| {
                store
                    .value_symbol_links(store.get_merged_symbol(symbol).unwrap())
                    .cloned()
            })
            .collect(),
        sources: files
            .iter()
            .map(|(file, _)| {
                store
                    .source_file_links(context.source_file(*file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    first: &ParseResult,
    second: &ParseResult,
    source: &ParseResult,
) {
    let files = [(FIRST, first), (SECOND, second), (SOURCE, source)];
    let mut queries = Vec::new();
    let mut returns = Vec::new();
    for &(file, parsed) in &files {
        for method in nodes(parsed, file, SyntaxKind::MethodSignature) {
            for query in [method, method_name(parsed, method)] {
                queries.push((query, context.get_type_at_location(query).unwrap()));
            }
            let stored = signature(context, method);
            returns.push((
                stored,
                context.get_return_type_of_signature(stored).unwrap(),
            ));
        }
    }
    for kind in [
        SyntaxKind::CallExpression,
        SyntaxKind::PropertyAccessExpression,
    ] {
        for query in nodes(source, SOURCE, kind) {
            queries.push((query, context.get_type_at_location(query).unwrap()));
            if kind == SyntaxKind::CallExpression {
                let selected = signature(context, query);
                returns.push((
                    selected,
                    context.get_return_type_of_signature(selected).unwrap(),
                ));
            }
        }
    }
    let warm = snapshot(context, &files);
    for recheck in [false, true, true] {
        if recheck {
            context.recheck_source_file(SOURCE).unwrap();
        } else {
            context.check_source_file(SOURCE).unwrap();
        }
        for &(query, expected) in &queries {
            assert_eq!(
                context.get_type_at_location(query),
                Ok(expected),
                "{query:?}"
            );
        }
        for &(stored, expected) in &returns {
            assert_eq!(context.get_return_type_of_signature(stored), Ok(expected));
        }
        assert_eq!(snapshot(context, &files), warm);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn merged_generic_methods_preserve_literal_priority_and_declaration_order() {
    let first = parse_source_file(concat!(
        "interface Picker { ",
        "pick<T>(value: T): T; ",
        "pick(value: 'fixed'): 'literal'; }",
    ));
    let second = parse_source_file("interface Picker { pick(value: string): number; }");
    let source = parse_source_file(concat!(
        "declare const picker: Picker;\n",
        "const literal = picker.pick('fixed');\n",
        "const newer = picker.pick('ordinary');\n",
        "const inferred = picker.pick(1);\n",
        "const explicit = picker.pick<string>('fixed');\n",
        "const repeated = picker.pick<string>('ordinary');\n",
    ));
    let mut declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    declarations.extend(nodes(&second, SECOND, SyntaxKind::MethodSignature));
    let names = declarations
        .iter()
        .map(|&method| {
            method_name(
                if method.file == FIRST {
                    &first
                } else {
                    &second
                },
                method,
            )
        })
        .collect::<Vec<_>>();
    for query_first in [false, true] {
        let mut context = context(&first, &second, &source);
        let early = query_first.then(|| context.get_type_at_location(names[0]).unwrap());
        context.check_source_file(SOURCE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let (owner, callable, signatures) =
            assert_method_group(&mut context, &declarations, &names);
        assert!(early.is_none_or(|early| early == callable));
        let raw = declarations
            .iter()
            .map(|declaration| {
                context
                    .file(declaration.file)
                    .unwrap()
                    .1
                    .symbol(*declaration)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(raw[0], raw[1]);
        assert_ne!(raw[0], raw[2]);
        assert_eq!(
            context.store().symbol(owner).unwrap().flags(),
            SymbolFlags::METHOD | SymbolFlags::TRANSIENT
        );
        let generic = signatures[0];
        let type_parameter = context
            .store()
            .signature(generic)
            .unwrap()
            .type_parameters()[0];
        assert_eq!(parameter_types(&context, generic), [type_parameter]);
        assert_eq!(
            context.get_return_type_of_signature(generic),
            Ok(type_parameter)
        );
        let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 5);
        let (literal, _) = assert_call(&mut context, calls[0], "\"literal\"");
        let (newer, _) = assert_call(&mut context, calls[1], "number");
        let (inferred, inferred_type) = assert_call(&mut context, calls[2], "1");
        let (explicit, string) = assert_call(&mut context, calls[3], "string");
        let (repeated, _) = assert_call(&mut context, calls[4], "string");
        assert_eq!(literal, signatures[1]);
        assert_eq!(newer, signatures[2]);
        assert_instantiation(&context, inferred, generic, &[inferred_type]);
        assert_instantiation(&context, explicit, generic, &[string]);
        assert_eq!(explicit, repeated);
        for access in nodes(&source, SOURCE, SyntaxKind::PropertyAccessExpression) {
            assert_eq!(context.get_symbol_at_location(access), Ok(Some(owner)));
            assert_eq!(context.get_type_at_location(access), Ok(callable));
        }
        assert_replay(&mut context, &first, &second, &source);
    }
}

#[test]
fn type_literal_generic_methods_run_subtype_before_assignable() {
    let first = parse_source_file(concat!(
        "type Choice = { ",
        "select<T = number>(value: string): T; ",
        "select(value: any): 'fallback'; ",
        "assign<T = string>(value: number): T; ",
        "assign(value: string): boolean; };",
    ));
    let second = parse_source_file("");
    let source = parse_source_file(concat!(
        "declare const choice: Choice;\n",
        "declare const input: any;\n",
        "const subtype = choice.select(input);\n",
        "const assignable = choice.assign(input);\n",
    ));
    let declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    let names = declarations
        .iter()
        .map(|&method| method_name(&first, method))
        .collect::<Vec<_>>();
    let mut context = context(&first, &second, &source);
    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let (_, _, select) = assert_method_group(&mut context, &declarations[..2], &names[..2]);
    let (_, _, assign) = assert_method_group(&mut context, &declarations[2..], &names[2..]);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let (subtype, _) = assert_call(&mut context, calls[0], "\"fallback\"");
    assert_eq!(subtype, select[1]);
    let (assignable, string) = assert_call(&mut context, calls[1], "string");
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(
        string,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_instantiation(&context, assignable, assign[0], &[number]);
    assert_replay(&mut context, &first, &second, &source);
}

#[test]
fn generic_method_candidates_keep_primitive_constraints_and_defaults() {
    let first = parse_source_file(concat!(
        "interface Converter { ",
        "convert<T extends string>(value: T): T; ",
        "convert<T extends number>(value: T): T; ",
        "convert<T = string>(): T; ",
        "convert(value: boolean, repeat: number): boolean; }",
    ));
    let second = parse_source_file("");
    let source = parse_source_file(concat!(
        "declare const converter: Converter;\n",
        "const text = converter.convert('text');\n",
        "const count = converter.convert(1);\n",
        "const defaulted = converter.convert();\n",
        "const explicitDefault = converter.convert<string>();\n",
        "const otherDefault = converter.convert<number>();\n",
        "const explicitText = converter.convert<string>('text');\n",
        "const explicitCount = converter.convert<number>(1);\n",
        "const repeated = converter.convert<string>('again');\n",
        "const concrete = converter.convert(true, 2);\n",
    ));
    let declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    let names = declarations
        .iter()
        .map(|&method| method_name(&first, method))
        .collect::<Vec<_>>();
    let mut context = context(&first, &second, &source);
    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let (_, _, signatures) = assert_method_group(&mut context, &declarations, &names);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 9);
    let expected = [
        "\"text\"", "1", "string", "string", "number", "string", "number", "string", "boolean",
    ];
    let selected = calls
        .iter()
        .zip(expected)
        .map(|(&call, expected)| assert_call(&mut context, call, expected))
        .collect::<Vec<_>>();
    for (index, target) in [(0, 0), (1, 1), (5, 0), (6, 1), (7, 0)] {
        assert_instantiation(
            &context,
            selected[index].0,
            signatures[target],
            &[selected[index].1],
        );
    }
    for index in [2, 3, 4] {
        assert_instantiation(&context, selected[index].0, signatures[2], &[]);
    }
    assert_eq!(selected[2].0, selected[3].0);
    assert_ne!(selected[2].0, selected[4].0);
    assert_eq!(selected[5].0, selected[7].0);
    assert_eq!(selected[8].0, signatures[3]);
    assert_replay(&mut context, &first, &second, &source);
}

#[test]
fn mixed_method_failure_separates_error_candidate_from_recovery_signature() {
    let first = parse_source_file("interface Adapter { map<T extends string>(value: T): T; }");
    let second =
        parse_source_file("interface Adapter { map(value: number, scale: number): number; }");
    let source_text = concat!(
        "declare const adapter: Adapter;\n",
        "const good = adapter.map<string>('ok');\n",
        "const pair = adapter.map(1, 2);\n",
        "const badArgument = adapter.map<string>(1);\n",
        "const badConstraint = adapter.map<number>(1);\n",
    );
    let source = parse_source_file(source_text);
    let mut declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    declarations.extend(nodes(&second, SECOND, SyntaxKind::MethodSignature));
    let names = declarations
        .iter()
        .map(|&method| {
            method_name(
                if method.file == FIRST {
                    &first
                } else {
                    &second
                },
                method,
            )
        })
        .collect::<Vec<_>>();
    for query_first in [false, true] {
        let mut context = context(&first, &second, &source);
        if query_first {
            context.get_type_at_location(names[0]).unwrap();
        }
        context.check_source_file(SOURCE).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, (code, message, text)) in diagnostics.iter().zip([
            (
                2345,
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
                "1",
            ),
            (
                2344,
                "Type 'number' does not satisfy the constraint 'string'.",
                "number",
            ),
        ]) {
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            let node = diagnostic.node.unwrap();
            assert_eq!(node.file, SOURCE);
            let range = source.arena.get(node.node).unwrap().range;
            assert_eq!(
                &source_text[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                text
            );
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
        }
        let (_, _, signatures) = assert_method_group(&mut context, &declarations, &names);
        let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 4);
        let (good, string) = assert_call(&mut context, calls[0], "string");
        assert_instantiation(&context, good, signatures[0], &[string]);
        for &call in &calls[1..] {
            let (selected, number) = assert_call(&mut context, call, "number");
            assert_eq!(selected, signatures[1]);
            assert_eq!(parameter_types(&context, selected), [number, number]);
            assert!(
                context
                    .store()
                    .signature(selected)
                    .unwrap()
                    .target()
                    .is_none()
            );
        }
        assert_replay(&mut context, &first, &second, &source);
    }
}

#[test]
fn generic_method_type_arity_errors_keep_separate_recovery_signatures() {
    let first = parse_source_file(concat!(
        "interface Matcher { ",
        "m<T>(value: T): T; ",
        "m(left: number, right: number): number; }",
    ));
    let second = parse_source_file("");
    let source_text = concat!(
        "declare const matcher: Matcher;\n",
        "const first = matcher.m<string, number>('one');\n",
        "const second = matcher.m<string, number>('two');\n",
    );
    let source = parse_source_file(source_text);
    let declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    let names = declarations
        .iter()
        .map(|&method| method_name(&first, method))
        .collect::<Vec<_>>();
    let mut context = context(&first, &second, &source);
    context.check_source_file(SOURCE).unwrap();
    let (_, _, signatures) = assert_method_group(&mut context, &declarations, &names);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2);
    for ((diagnostic, &call), (start, type_list)) in diagnostics
        .iter()
        .zip(&calls)
        .zip(source_text.match_indices("string, number"))
    {
        assert_eq!(diagnostic.diagnostic.code(), 2558);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Expected 1 type arguments, but got 2.",
        );
        assert_eq!(diagnostic.node, Some(call));
        assert_eq!(
            diagnostic.range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                call,
                TextRange::new(
                    TextPos::new(u32::try_from(start).unwrap()),
                    TextPos::new(u32::try_from(start + type_list.len()).unwrap()),
                ),
            )),
        );
        assert!(diagnostic.related_information.is_empty());
    }
    let (first_recovery, string) = assert_call(&mut context, calls[0], "string");
    let (second_recovery, _) = assert_call(&mut context, calls[1], "string");
    assert_ne!(first_recovery, second_recovery);
    assert_eq!(
        string,
        context.store().intrinsic_bootstrap().unwrap().string_type,
    );
    let target_parameter = context
        .store()
        .signature(signatures[0])
        .unwrap()
        .parameters()[0];
    let parameters = [first_recovery, second_recovery].map(|recovery| {
        let record = context.store().signature(recovery).unwrap();
        assert_eq!(record.target(), Some(signatures[0]));
        assert!(record.mapper().is_some());
        assert!(record.type_parameters().is_empty());
        let [parameter] = record.parameters() else {
            panic!("the recovery signature must keep its original parameter");
        };
        let links = context.store().value_symbol_links(*parameter).unwrap();
        assert_eq!(links.target, Some(target_parameter));
        assert_eq!(links.mapper, record.mapper());
        assert!(links.resolved_type.is_none());
        (*parameter, links.clone())
    });
    assert_replay(&mut context, &first, &second, &source);
    for (parameter, expected) in parameters {
        assert_eq!(
            context.store().value_symbol_links(parameter),
            Some(&expected)
        );
    }
}

#[test]
fn multiple_generic_method_argument_errors_keep_call_results_unpublished() {
    let first = parse_source_file(concat!(
        "interface Matcher { ",
        "m<T extends string>(value: T): T; ",
        "m<T extends number>(value: T): T; ",
        "m(left: boolean, right: boolean): boolean; }",
    ));
    let second = parse_source_file("");
    let source = parse_source_file(concat!(
        "declare const matcher: Matcher;\n",
        "const bad = matcher.m(true);\n",
    ));
    let declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    let names = declarations
        .iter()
        .map(|&method| method_name(&first, method))
        .collect::<Vec<_>>();
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one unsupported overload call");
    };
    let mut context = context(&first, &second, &source);
    assert_method_group(&mut context, &declarations, &names);
    assert!(matches!(
        context.check_source_file(SOURCE),
        Err(SourceCheckError::Call(node)) if node == *call
    ));
    assert!(context.diagnostics().is_empty());
    assert!(context.store().type_node_links(*call).is_none());
    assert!(context.store().signature_links(*call).is_none());
    assert!(
        !context
            .store()
            .source_file_links(context.source_file(SOURCE).unwrap())
            .is_some_and(|links| links.type_checked),
    );
    let files = [(FIRST, &first), (SECOND, &second), (SOURCE, &source)];
    let failed = snapshot(&context, &files);
    for recheck in [false, true, true] {
        let result = if recheck {
            context.recheck_source_file(SOURCE)
        } else {
            context.check_source_file(SOURCE)
        };
        assert!(matches!(
            result,
            Err(SourceCheckError::Call(node)) if node == *call
        ));
        assert_eq!(snapshot(&context, &files), failed);
        assert!(context.store().type_node_links(*call).is_none());
        assert!(context.store().signature_links(*call).is_none());
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn generic_method_calls_can_omit_void_parameters_without_changing_signature_arity() {
    let first = parse_source_file(concat!(
        "interface Omitted { ",
        "m<T = string>(value: void): T; ",
        "m(value: number): number; }",
    ));
    let second = parse_source_file("");
    let source = parse_source_file(concat!(
        "declare const omitted: Omitted;\n",
        "const defaulted = omitted.m();\n",
        "const explicit = omitted.m<string>();\n",
        "const supplied = omitted.m(1);\n",
    ));
    let declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    let names = declarations
        .iter()
        .map(|&method| method_name(&first, method))
        .collect::<Vec<_>>();
    let mut context = context(&first, &second, &source);
    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let (_, _, signatures) = assert_method_group(&mut context, &declarations, &names);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 3);
    let (defaulted, string) = assert_call(&mut context, calls[0], "string");
    let (explicit, _) = assert_call(&mut context, calls[1], "string");
    let (supplied, _) = assert_call(&mut context, calls[2], "number");
    assert_eq!(defaulted, explicit);
    assert_eq!(supplied, signatures[1]);
    assert_eq!(
        string,
        context.store().intrinsic_bootstrap().unwrap().string_type,
    );
    let generic = context.store().signature(signatures[0]).unwrap();
    assert_eq!(generic.min_argument_count(), 1);
    let target_parameter = generic.parameters()[0];
    let instantiated = context.store().signature(defaulted).unwrap();
    assert_eq!(instantiated.target(), Some(signatures[0]));
    assert!(instantiated.mapper().is_some());
    assert!(instantiated.type_parameters().is_empty());
    assert_eq!(instantiated.min_argument_count(), 1);
    let [parameter] = instantiated.parameters() else {
        panic!("the omitted parameter must remain in the selected signature");
    };
    let parameter = *parameter;
    let links = context
        .store()
        .value_symbol_links(parameter)
        .unwrap()
        .clone();
    assert_eq!(links.target, Some(target_parameter));
    assert_eq!(links.mapper, instantiated.mapper());
    assert_replay(&mut context, &first, &second, &source);
    assert_eq!(context.store().value_symbol_links(parameter), Some(&links));
}

#[test]
fn merged_generic_method_arity_notes_use_the_original_parameter_declaration() {
    let first = parse_source_file("interface Api { m<T>(old: T): T; }");
    let second = parse_source_file("interface Api { m(newer: number): number; }");
    let source = parse_source_file(concat!(
        "declare const api: Api;\n",
        "const missing = api.m();\n",
    ));
    let mut declarations = nodes(&first, FIRST, SyntaxKind::MethodSignature);
    declarations.extend(nodes(&second, SECOND, SyntaxKind::MethodSignature));
    let names = declarations
        .iter()
        .map(|&method| {
            method_name(
                if method.file == FIRST {
                    &first
                } else {
                    &second
                },
                method,
            )
        })
        .collect::<Vec<_>>();
    let mut context = context(&first, &second, &source);
    context.check_source_file(SOURCE).unwrap();
    let (_, _, signatures) = assert_method_group(&mut context, &declarations, &names);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one missing-argument call");
    };
    let accesses = nodes(&source, SOURCE, SyntaxKind::PropertyAccessExpression);
    let NodeData::PropertyAccessExpression(access) =
        &source.arena.get(accesses[0].node).unwrap().data
    else {
        unreachable!();
    };
    let name = NodeRef::new(source.arena.id(), SOURCE, access.name);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the missing argument must produce one diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0.",
    );
    assert_eq!(diagnostic.node, Some(name));
    assert!(diagnostic.range_override.is_none());
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the arity error must retain its missing-parameter note");
    };
    let first_parameter = nodes(&first, FIRST, SyntaxKind::Parameter)[0];
    assert_eq!(related.node, Some(first_parameter));
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'old' was not provided.",
    );
    let (recovery, _) = assert_call(&mut context, *call, "number");
    assert_eq!(recovery, signatures[1]);
    assert_replay(&mut context, &first, &second, &source);
}
