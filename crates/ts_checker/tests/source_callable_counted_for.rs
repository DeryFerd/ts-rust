use std::io::Write as _;

use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolver, CanonicalNameResolverOptions,
    CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, RelationUnavailable,
    SourceCheckError, SourceFunctionUnsupported, TypeData, UnsupportedSourceSyntax,
};
use ts_diagnostics::Category;
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_240);
const ES5_FILE: FileId = FileId::new(203_241);
const DECORATORS_FILE: FileId = FileId::new(203_242);
const LEGACY_DECORATORS_FILE: FileId = FileId::new(203_243);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.d.ts");
const LEGACY_DECORATORS: &str = include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts");

const GUARD: &str = r#"export const sequence = (nodes: string[]): string => {
  if (nodes.length === 0) {
    return "";
  }
  return nodes[0]!;
};
"#;

const COUNTED: &str = r#"declare function visit(left: string, right: string): void;
export const sequence = (nodes: string[]): string => {
  if (nodes.length === 0) {
    return "";
  }
  for (let i = nodes.length - 1; i >= 1; i--) {
    visit(nodes[i - 1]!, nodes[i]!);
  }
  return nodes[0]!;
};
"#;

const BAD_INCREMENT: &str = r#"export const sequence = (keepGoing: boolean): string => {
  for (let i = "bad"; keepGoing; i--) {}
  return "";
};
"#;

fn name_options() -> CanonicalNameResolverOptions {
    CanonicalNameResolverOptions {
        isolated_modules: true,
        verbatim_module_syntax: true,
        emit_target: ScriptTarget::EsNext,
        ..CanonicalNameResolverOptions::default()
    }
}

fn context<'a>(
    parsed: &'a ParseResult,
    libraries: &'a [ParseResult; 3],
) -> CanonicalCheckerContext<'a> {
    let files = [
        (ES5_FILE, &libraries[0], "\"/lib/lib.es5.d.ts\""),
        (
            DECORATORS_FILE,
            &libraries[1],
            "\"/lib/lib.decorators.d.ts\"",
        ),
        (
            LEGACY_DECORATORS_FILE,
            &libraries[2],
            "\"/lib/lib.decorators.legacy.d.ts\"",
        ),
        (FILE, parsed, "\"/project/callable-counted-for.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != FILE,
                    file != FILE,
                    if file == FILE {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_unchecked_indexed_access: true,
            no_unused_locals: true,
            isolated_modules: true,
            module_kind: ModuleKind::EsNext,
            no_emit: true,
            name_resolution: name_options(),
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn libraries() -> [ParseResult; 3] {
    [ES5, DECORATORS, LEGACY_DECORATORS].map(parse_source_file)
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn text<'a>(source: &'a str, parsed: &ParseResult, location: NodeRef) -> &'a str {
    assert_eq!(location.arena, parsed.arena.id());
    assert_eq!(location.file, FILE);
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn locations(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)))
        .collect()
}

fn expression(parsed: &ParseResult, source: &str, kind: SyntaxKind, expected: &str) -> NodeRef {
    let matches = locations(parsed, kind)
        .into_iter()
        .filter(|&location| text(source, parsed, location) == expected)
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one {expected:?}");
    matches[0]
}

fn callable(parsed: &ParseResult) -> (NodeRef, NodeRef) {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let body = match &record.data {
                NodeData::ArrowFunction(data) => data.body,
                NodeData::FunctionDeclaration(data) => data.body?,
                _ => return None,
            };
            Some((node(parsed, id), node(parsed, body)))
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1);
    matches[0]
}

fn declaration(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let name = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::ParameterDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some((node(parsed, id), node(parsed, name)))
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one declaration of {expected}");
    matches[0]
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn resolve(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    location: NodeRef,
    name: &str,
) -> Option<SemanticSymbolId> {
    let mut host = checker.name_resolver_host(name_options()).unwrap();
    let mut resolver = CanonicalNameResolver::new(
        &parsed.arena,
        checker.file(FILE).unwrap().1,
        checker.store().symbol_store(),
        &mut host,
    )
    .unwrap();
    resolver
        .resolve(
            Some(location.into()),
            name,
            SymbolFlags::VALUE,
            None,
            false,
            false,
        )
        .unwrap()
}

fn checked(checker: &CanonicalCheckerContext<'_>) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
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
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        checker.file(FILE).unwrap().1.flow_graph().clone(),
        checker.diagnostics().clone(),
    )
}

fn replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, queries: &[NodeRef]) {
    let types = queries
        .iter()
        .map(|&location| (location, checker.get_type_at_location(location).unwrap()))
        .collect::<Vec<_>>();
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        assert!(checked(checker));
        for &(location, expected) in &types {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

fn assert_signature(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let (callable, _) = callable(parsed);
    let (parameter, parameter_name) = declaration(parsed, "nodes");
    let parameter_symbol = symbol(checker, parameter);
    let callable_type = checker.get_type_at_location(callable).unwrap();
    let parameter_type = checker.get_type_at_location(parameter_name).unwrap();
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let TypeData::TypeReference(reference) =
        checker.store().type_payload(parameter_type).unwrap().data()
    else {
        panic!("expected the real string array reference");
    };
    assert_eq!(
        reference.object.target,
        Some(checker.global_types().array_type)
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[string][..])
    );
    let TypeData::Object(object) = checker.store().type_payload(callable_type).unwrap().data()
    else {
        panic!("expected the actual callable type");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature");
    };
    let signature = checker.store().signature(*signature).unwrap();
    assert_eq!(signature.declaration(), Some(callable));
    assert_eq!(signature.parameters(), &[parameter_symbol]);
    assert_eq!(signature.resolved_return_type(), Some(string));
    assert!(signature.type_parameters().is_empty());
    assert_eq!(
        checker.get_symbol_at_location(parameter_name),
        Ok(Some(parameter_symbol))
    );
}

fn assert_loop_bindings(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
) -> Vec<NodeRef> {
    let (callable, body) = callable(parsed);
    let loops = locations(parsed, SyntaxKind::ForStatement);
    let [loop_node] = loops.as_slice() else {
        panic!("expected one counted loop");
    };
    let (declaration, name) = declaration(parsed, "i");
    let owner = symbol(checker, declaration);
    let bound = checker.file(FILE).unwrap().1;
    assert_eq!(bound.container(declaration), Some(callable));
    assert_eq!(bound.block_scope_container(declaration), Some(*loop_node));
    let local = |scope| {
        bound
            .locals(scope)
            .and_then(|table| checker.store().symbol_table(table))
            .and_then(|table| table.get_source("i"))
    };
    assert_eq!(local(*loop_node), Some(owner));
    assert_eq!(local(callable), None);
    assert_eq!(local(body), None);
    assert_eq!(
        checker.store().symbol(owner).unwrap().flags(),
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    );
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let uses = locations(parsed, SyntaxKind::Identifier)
        .into_iter()
        .filter(|&location| text(source, parsed, location) == "i")
        .collect::<Vec<_>>();
    assert!(uses.contains(&name));
    let expected_uses = if source.contains("if (i === 1)") {
        6
    } else {
        5
    };
    assert_eq!(uses.len(), expected_uses);
    for &location in &uses {
        assert_eq!(checker.get_symbol_at_location(location), Ok(Some(owner)));
        assert_eq!(checker.get_type_at_location(location), Ok(number));
        assert_eq!(resolve(checker, parsed, location, "i"), Some(owner));
    }
    let after = expression(
        parsed,
        source,
        SyntaxKind::ReturnStatement,
        "return nodes[0]!;",
    );
    assert_eq!(resolve(checker, parsed, after, "i"), None);
    uses
}

fn failure_call_source<'a>(
    parsed: &ParseResult,
    source: &'a str,
    location: NodeRef,
) -> Result<(SyntaxKind, usize, usize, &'a str), &'static str> {
    if location.arena != parsed.arena.id() {
        return Err("arena_mismatch");
    }
    if location.file != FILE {
        return Err("file_mismatch");
    }
    let Some(record) = parsed.arena.get(location.node) else {
        return Err("missing_node");
    };
    let (Ok(start), Ok(end)) = (
        usize::try_from(record.range.start.get()),
        usize::try_from(record.range.end.get()),
    ) else {
        return Err("range_conversion");
    };
    if start > end || end > source.len() {
        return Err("range_out_of_bounds");
    }
    let Some(slice) = source.get(start..end) else {
        return Err("range_not_utf8");
    };
    Ok((record.kind, start, end, slice))
}

// Record only a failed check. Leave the original result and test state unchanged.
fn observe_source_check_failure(
    parsed: &ParseResult,
    source: &str,
    site: &str,
    case: (&str, Option<usize>),
    query_first: bool,
    expected: Option<ExpectedDiagnostic>,
    error: &SourceCheckError,
) {
    let error_tag = match error {
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(_)) => "unsupported_call",
        SourceCheckError::RelationUnavailable(RelationUnavailable::UnresolvedPropertyType(_)) => {
            "unresolved_property_type"
        }
        SourceCheckError::Unsupported(_) => "unsupported_other",
        SourceCheckError::RelationUnavailable(_) => "relation_unavailable_other",
        _ => "other_source_check_error",
    };
    let mut record = [0_u8; 1024];
    let Some(mut output) = record.get_mut(..1000) else {
        return;
    };
    let mut truncated = write!(
        output,
        "loop_failure family=counted_test stage=check_source_file site={} case={} query_first={query_first} source_bytes={} error={error_tag}",
        site.as_bytes().escape_ascii(),
        case.0.as_bytes().escape_ascii(),
        source.len(),
    )
    .is_err();
    if let Some(index) = case.1 {
        truncated |= write!(output, " case_index_zero_based={index}").is_err();
    }
    if let Some(expected) = expected {
        truncated |= write!(
            output,
            " expected_code={} expected_text=\"{}\" expected_start={} expected_end={}",
            expected.code,
            expected.text.as_bytes().escape_ascii(),
            expected.start,
            expected.end,
        )
        .is_err();
    }
    if let SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(location)) = error {
        match failure_call_source(parsed, source, *location) {
            Ok((kind, start, end, source_slice)) => {
                let mut length = source_slice.len().min(96);
                while length > 0 && !source_slice.is_char_boundary(length) {
                    length = length.saturating_sub(1);
                }
                if let Some(slice) = source_slice.get(..length) {
                    truncated |= write!(
                        output,
                        " call_validation=valid call_kind={kind:?} call_start={start} call_end={end} source_slice=\"{}\" source_slice_truncated={}",
                        slice.as_bytes().escape_ascii(),
                        length < source_slice.len(),
                    )
                    .is_err();
                } else {
                    truncated |= write!(output, " call_validation=slice_unavailable").is_err();
                }
            }
            Err(validation) => {
                truncated |= write!(output, " call_validation={validation}").is_err();
            }
        }
    }
    let used = 1000_usize.saturating_sub(output.len());
    let suffix = if truncated {
        b" record_truncated=1\n"
    } else {
        b" record_truncated=0\n"
    };
    let Some(end) = used.checked_add(suffix.len()) else {
        return;
    };
    let Some(tail) = record.get_mut(used..end) else {
        return;
    };
    tail.copy_from_slice(suffix);
    if let Some(bytes) = record.get(..end) {
        let _ = std::io::stderr().write_all(bytes);
    }
}

fn assert_valid(source: &str, libraries: &[ParseResult; 3], case: &str) {
    let parsed = parse_source_file(source);
    let returned = expression(&parsed, source, SyntaxKind::NonNullExpression, "nodes[0]!");
    for query_first in [false, true] {
        let mut checker = context(&parsed, libraries);
        assert!(!checked(&checker));
        let first_type = query_first.then(|| checker.get_type_at_location(returned).unwrap());
        let result = checker.check_source_file(FILE);
        if let Err(error) = &result {
            observe_source_check_failure(
                &parsed,
                source,
                "assert_valid",
                (case, None),
                query_first,
                None,
                error,
            );
        }
        result.unwrap();
        assert!(checked(&checker));
        // Check body diagnostics before later expression queries can demand them.
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        assert_eq!(checker.store().type_resolution_len(), 0);
        assert_signature(&mut checker, &parsed);
        let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
        let (string, undefined, number, boolean, void) = (
            intrinsics.string_type,
            intrinsics.undefined_type,
            intrinsics.number_type,
            intrinsics.boolean_type,
            intrinsics.void_type,
        );
        if let Some(first_type) = first_type {
            assert_eq!(first_type, string);
        }
        let mut queries = vec![callable(&parsed).0, returned];
        for location in locations(&parsed, SyntaxKind::ElementAccessExpression) {
            let type_ = checker.get_type_at_location(location).unwrap();
            let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
                panic!("unchecked indexed reads must retain undefined");
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&string));
            assert!(union.union.types.contains(&undefined));
            queries.push(location);
        }
        for location in locations(&parsed, SyntaxKind::NonNullExpression) {
            assert_eq!(checker.get_type_at_location(location), Ok(string));
            queries.push(location);
        }
        for (id, record) in parsed.arena.iter() {
            let location = node(&parsed, id);
            let expected = match record.kind {
                SyntaxKind::PropertyAccessExpression
                | SyntaxKind::PrefixUnaryExpression
                | SyntaxKind::PostfixUnaryExpression => Some(number),
                SyntaxKind::BinaryExpression => match text(source, &parsed, location) {
                    "nodes.length === 0" | "i >= 1" | "i === 1" => Some(boolean),
                    "nodes.length - 1" | "i - 1" => Some(number),
                    other => panic!("unlisted binary expression {other}"),
                },
                SyntaxKind::CallExpression => Some(void),
                _ => None,
            };
            if let Some(expected) = expected {
                assert_eq!(checker.get_type_at_location(location), Ok(expected));
                queries.push(location);
            }
        }
        if !locations(&parsed, SyntaxKind::ForStatement).is_empty() {
            queries.extend(assert_loop_bindings(&mut checker, &parsed, source));
        }
        assert!(checker.diagnostics().is_empty());
        replay(&mut checker, &parsed, &queries);
    }
}

#[derive(Clone, Copy)]
struct ExpectedDiagnostic {
    code: u32,
    kind: SyntaxKind,
    text: &'static str,
    start: usize,
    end: usize,
    arguments: &'static [&'static str],
}

fn assert_diagnostic(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    expected: ExpectedDiagnostic,
) {
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one diagnostic: {:?}", checker.diagnostics());
    };
    assert_eq!(diagnostic.diagnostic.code(), expected.code);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.arguments, expected.arguments);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(diagnostic.range_override, None);
    let location = diagnostic.node.expect("expected a source diagnostic");
    let record = parsed.arena.get(location.node).unwrap();
    assert_eq!(record.kind, expected.kind);
    assert_eq!(text(source, parsed, location), expected.text);
    assert_eq!(
        usize::try_from(record.range.start.get()).unwrap(),
        expected.start
    );
    assert_eq!(
        usize::try_from(record.range.end.get()).unwrap(),
        expected.end
    );
}

#[test]
fn callable_counted_for_checks_arrow_and_function_bodies() {
    let libraries = libraries();
    assert_eq!(GUARD.len(), 125);
    assert_eq!(COUNTED.len(), 273);
    let loop_only = COUNTED.replacen(
        "  if (nodes.length === 0) {\n    return \"\";\n  }\n",
        "",
        1,
    );
    assert_eq!(loop_only.len(), 226);
    let function = COUNTED.replacen(
        "export const sequence = (nodes: string[]): string => {",
        "export function sequence(nodes: string[]): string {",
        1,
    );
    let function = format!("{}}}\n", function.strip_suffix("};\n").unwrap());
    for (case, source) in [
        ("guard", GUARD),
        ("counted", COUNTED),
        ("loop_only", &loop_only),
        ("function", &function),
    ] {
        assert_valid(source, &libraries, case);
    }
    for update in ["--i", "i++", "++i"] {
        assert_valid(&COUNTED.replacen("i--", update, 1), &libraries, update);
    }
}

#[test]
fn callable_counted_for_prepares_scalar_body_condition() {
    let libraries = libraries();
    let source = COUNTED.replacen("    visit(", "    if (i === 1) return \"\";\n    visit(", 1);
    assert_eq!(source.len(), 301);
    assert_valid(&source, &libraries, "scalar_body_condition");
}

#[test]
fn callable_counted_for_checks_each_header_part_and_return() {
    let libraries = libraries();
    let cases = [
        (
            COUNTED.replacen("nodes.length - 1", "nodes.length - \"bad\"", 1),
            277,
            ExpectedDiagnostic {
                code: 2363,
                kind: SyntaxKind::StringLiteral,
                text: "\"bad\"",
                start: 191,
                end: 196,
                arguments: &[],
            },
        ),
        (
            COUNTED.replacen("i >= 1", "i >= true", 1),
            276,
            ExpectedDiagnostic {
                code: 2365,
                kind: SyntaxKind::BinaryExpression,
                text: "i >= true",
                start: 194,
                end: 203,
                arguments: &[">=", "number", "boolean"],
            },
        ),
        (
            BAD_INCREMENT.to_owned(),
            115,
            ExpectedDiagnostic {
                code: 2356,
                kind: SyntaxKind::Identifier,
                text: "i",
                start: 91,
                end: 92,
                arguments: &[],
            },
        ),
        (
            COUNTED.replacen(
                "visit(nodes[i - 1]!, nodes[i]!)",
                "visit(nodes[i - 1]!, i)",
                1,
            ),
            265,
            ExpectedDiagnostic {
                code: 2345,
                kind: SyntaxKind::Identifier,
                text: "i",
                start: 234,
                end: 235,
                arguments: &["number", "string"],
            },
        ),
        (
            COUNTED.replacen("return nodes[0]!;", "return nodes.length;", 1),
            276,
            ExpectedDiagnostic {
                code: 2322,
                kind: SyntaxKind::ReturnStatement,
                text: "return nodes.length;",
                start: 252,
                end: 272,
                arguments: &["number", "string"],
            },
        ),
        (
            GUARD.replacen("return \"\";", "return nodes.length;", 1),
            135,
            ExpectedDiagnostic {
                code: 2322,
                kind: SyntaxKind::ReturnStatement,
                text: "return nodes.length;",
                start: 87,
                end: 107,
                arguments: &["number", "string"],
            },
        ),
    ];
    // Program conversion selects the return token from the retained statement anchor.
    for (case_index, (source, bytes, expected)) in cases.into_iter().enumerate() {
        assert_eq!(source.len(), bytes);
        let parsed = parse_source_file(&source);
        let callable = callable(&parsed).0;
        for query_first in [false, true] {
            let mut checker = context(&parsed, &libraries);
            assert!(!checked(&checker));
            let first_type = query_first.then(|| checker.get_type_at_location(callable).unwrap());
            let result = checker.check_source_file(FILE);
            if let Err(error) = &result {
                observe_source_check_failure(
                    &parsed,
                    &source,
                    "checks_each_header_part_and_return",
                    ("diagnostic", Some(case_index)),
                    query_first,
                    Some(expected),
                    error,
                );
            }
            result.unwrap();
            assert!(checked(&checker));
            assert_diagnostic(&checker, &parsed, &source, expected);
            if let Some(first_type) = first_type {
                assert_eq!(checker.get_type_at_location(callable), Ok(first_type));
            }
            replay(&mut checker, &parsed, &[callable]);
            assert_diagnostic(&checker, &parsed, &source, expected);
        }
    }
}

#[test]
fn callable_counted_for_rejects_unsupported_header_and_body_forms() {
    let libraries = libraries();
    for body in [
        "let i = 0; for (; keepGoing; i--) {}",
        "for (let i: number; keepGoing; i--) {}",
        "for (let i = 0; ; i--) {}",
        "for (let i = 0; keepGoing; ) {}",
        "for (let i = 0, j = 1; keepGoing; i--) {}",
        "for (var i = 0; keepGoing; i--) {}",
        "for (let i = 0; keepGoing; i += 1) {}",
        "let outside = 0; for (let i = 0; keepGoing; outside--) {}",
        "for (let i = 0; keepGoing; i--) { for (let j = 0; keepGoing; j--) {} }",
        "for (let i = 0; keepGoing; i--) { for (const value of [0]) {} }",
        "for (let i = 0; keepGoing; i--) { try {} catch {} }",
        "for (let i = 0; keepGoing; i--) { break; }",
        "for (let i = 0; keepGoing; i--) { continue; }",
        "for (let i = 0; keepGoing; i--) { return; }",
        "for (let i = 0; keepGoing; i--) { throw \"\"; }",
    ] {
        let source =
            format!("export const sequence = (keepGoing: boolean): void => {{ {body} }};\n");
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed, &libraries);
        let before = snapshot(&checker, &parsed);
        let error =
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(callable(&parsed).1));
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(error), "{source}");
            assert!(!checked(&checker));
            assert!(checker.diagnostics().is_empty());
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn callable_counted_for_rejects_unprepared_loop_body_conditions() {
    let libraries = libraries();
    for (parameters, condition) in [
        (
            "keepGoing: boolean, value: { item: string }",
            "\"item\" in value",
        ),
        (
            "keepGoing: boolean, value: { kind: string }",
            "value.kind === \"ready\"",
        ),
    ] {
        let source = format!(
            "export const sequence = ({parameters}): void => {{\n  for (let i = 0; keepGoing; i--) {{\n    if ({condition}) {{}}\n  }}\n}};\n"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed, &libraries);
        let before = snapshot(&checker, &parsed);
        let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
            SourceFunctionUnsupported::FunctionBody(callable(&parsed).1),
        ));
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(FILE), Err(error), "{source}");
            assert!(!checked(&checker));
            assert!(checker.diagnostics().is_empty());
            assert_eq!(snapshot(&checker, &parsed), before);
        }
    }
}

#[test]
fn callable_counted_for_keeps_loop_local_out_of_post_loop_scope() {
    let libraries = libraries();
    let parsed = parse_source_file(COUNTED);
    let (declaration, _) = declaration(&parsed, "i");
    let condition = expression(&parsed, COUNTED, SyntaxKind::BinaryExpression, "i >= 1");
    let after = expression(
        &parsed,
        COUNTED,
        SyntaxKind::ReturnStatement,
        "return nodes[0]!;",
    );
    for query_first in [false, true] {
        let mut checker = context(&parsed, &libraries);
        let owner = symbol(&checker, declaration);
        if query_first {
            assert_eq!(resolve(&checker, &parsed, after, "i"), None);
            assert_eq!(resolve(&checker, &parsed, condition, "i"), Some(owner));
        }
        let result = checker.check_source_file(FILE);
        if let Err(error) = &result {
            observe_source_check_failure(
                &parsed,
                COUNTED,
                "keeps_loop_local_out_of_post_loop_scope",
                ("scope_counted", None),
                query_first,
                None,
                error,
            );
        }
        result.unwrap();
        assert!(checker.diagnostics().is_empty());
        let queries = assert_loop_bindings(&mut checker, &parsed, COUNTED);
        replay(&mut checker, &parsed, &queries);
        assert_eq!(resolve(&checker, &parsed, after, "i"), None);
        assert_eq!(resolve(&checker, &parsed, condition, "i"), Some(owner));
    }
}
