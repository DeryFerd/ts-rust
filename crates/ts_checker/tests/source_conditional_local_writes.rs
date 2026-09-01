use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_970);
const ES5_FILE: FileId = FileId::new(202_971);
const CORE_FILE: FileId = FileId::new(202_972);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const ES2015_CORE: &str = include_str!("../../ts_bundled/libs/lib.es2015.core.d.ts");

// Exact src/_internal.ts from the retained Pathe input, including its final newline.
const NORMALIZER: &str = r#"// Util to normalize windows paths to posix
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
"#;

fn context<'a>(
    parsed: &'a ParseResult,
    libraries: Option<[&'a ParseResult; 2]>,
) -> CanonicalCheckerContext<'a> {
    let mut files = Vec::new();
    if let Some([es5, core]) = libraries {
        files.push((ES5_FILE, es5, "\"/lib/lib.es5.d.ts\""));
        files.push((CORE_FILE, core, "\"/lib/lib.es2015.core.d.ts\""));
    }
    files.push((FILE, parsed, "\"/project/conditional-local-writes.ts\""));
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
                    if file == FILE && libraries.is_some() {
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

fn text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn expression(parsed: &ParseResult, source: &str, kind: SyntaxKind, expected: &str) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let node = NodeRef::new(parsed.arena.id(), FILE, id);
            (record.kind == kind && text(source, parsed, node) == expected).then_some(node)
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one {expected:?}");
    matches[0]
}

struct Local {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
    annotation: Option<NodeRef>,
}

fn local(parsed: &ParseResult, name: &str) -> Local {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(data.name)?.data else {
                return None;
            };
            (identifier.text == name).then(|| Local {
                declaration: NodeRef::new(parsed.arena.id(), FILE, id),
                name: NodeRef::new(parsed.arena.id(), FILE, data.name),
                initializer: NodeRef::new(parsed.arena.id(), FILE, data.initializer.unwrap()),
                annotation: data
                    .type_
                    .map(|id| NodeRef::new(parsed.arena.id(), FILE, id)),
            })
        })
        .unwrap()
}

fn last_return(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ReturnStatement(data) = &record.data else {
                return None;
            };
            data.expression.map(|id| {
                (
                    record.range.start.get(),
                    NodeRef::new(parsed.arena.id(), FILE, id),
                )
            })
        })
        .max_by_key(|(start, _)| *start)
        .unwrap()
        .1
}

fn assignment(parsed: &ParseResult, source: &str, expected: &str) -> (NodeRef, NodeRef) {
    let node = expression(parsed, source, SyntaxKind::BinaryExpression, expected);
    let NodeData::BinaryExpression(data) = &parsed.arena.get(node.node).unwrap().data else {
        unreachable!();
    };
    assert_eq!(
        parsed.arena.get(data.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    (
        NodeRef::new(parsed.arena.id(), FILE, data.left),
        NodeRef::new(parsed.arena.id(), FILE, data.right),
    )
}

fn declared_type(checker: &mut CanonicalCheckerContext<'_>, local: &Local) -> TypeId {
    let raw = checker
        .file(FILE)
        .unwrap()
        .1
        .symbol(local.declaration)
        .unwrap();
    let symbol = checker.store().get_merged_symbol(raw).unwrap();
    assert_eq!(checker.get_symbol_at_location(local.name), Ok(Some(symbol)));
    checker
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn check(checker: &mut CanonicalCheckerContext<'_>, query: NodeRef, query_first: bool) -> TypeId {
    assert!(
        !checker
            .store()
            .source_file_links(checker.source_file(FILE).unwrap())
            .is_some_and(|links| links.type_checked)
    );
    let cold_type = query_first.then(|| checker.get_type_at_location(query).unwrap());
    checker.check_source_file(FILE).unwrap();
    let result = checker.get_type_at_location(query).unwrap();
    if let Some(cold_type) = cold_type {
        assert_eq!(cold_type, result);
    }
    result
}

fn diagnostic(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &str,
    target: NodeRef,
    code: u32,
    arguments: &[&str],
) {
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected one diagnostic: {:?}", checker.diagnostics());
    };
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.node, Some(target));
    assert_eq!(text(source, parsed, target), "value");
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    assert!(diagnostic.diagnostic.details.is_empty());
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
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
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
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
        .map(|&node| (node, checker.get_type_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for &(node, type_) in &types {
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        assert_eq!(snapshot(checker, parsed), before);
    }
}

#[test]
fn conditional_inferred_local_writes_use_the_declared_string_type() {
    let source = concat!(
        "function update(input: string, flag: boolean): string {\n",
        "  let value = input;\n",
        "  if (flag) { value = \"changed\"; }\n",
        "  if (flag) { let value = 1; value = 2; }\n",
        "  if (value === \"changed\") {\n",
        "    const narrowed: \"changed\" = value;\n",
        "    value = \"other\";\n",
        "  }\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let value = local(&parsed, "value");
    let narrowed = local(&parsed, "narrowed");
    let returned = last_return(&parsed);
    let (target, rhs) = assignment(&parsed, source, "value = \"other\"");
    let (inner_target, inner_rhs) = assignment(&parsed, source, "value = 2");
    assert!(value.annotation.is_none());
    for query_first in [false, true] {
        let mut checker = context(&parsed, None);
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(check(&mut checker, returned, query_first), string);
        assert_eq!(declared_type(&mut checker, &value), string);
        assert_eq!(checker.get_type_at_location(value.initializer), Ok(string));
        assert_eq!(checker.get_type_at_location(target), Ok(string));
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(checker.get_type_at_location(inner_target), Ok(number));
        assert_ne!(
            checker
                .get_symbol_at_location(inner_target)
                .unwrap()
                .unwrap(),
            checker.get_symbol_at_location(target).unwrap().unwrap()
        );
        let narrowed_type = checker.get_type_at_location(narrowed.initializer).unwrap();
        assert_eq!(
            checker.type_to_string(narrowed_type).unwrap(),
            "\"changed\""
        );
        let rhs_type = checker.get_type_at_location(rhs).unwrap();
        assert_eq!(checker.type_to_string(rhs_type).unwrap(), "\"other\"");
        assert_ne!(rhs_type, string);
        assert!(checker.diagnostics().as_slice().is_empty());
        replay(
            &mut checker,
            &parsed,
            &[
                returned,
                target,
                rhs,
                narrowed.initializer,
                inner_target,
                inner_rhs,
            ],
        );
    }
}

#[test]
fn conditional_inferred_local_writes_reject_a_numeric_rhs() {
    let source = "function update(input: string, flag: boolean): string { let value = input; if (flag) { value = 1; } return value; }";
    let parsed = parse_source_file(source);
    let value = local(&parsed, "value");
    let returned = last_return(&parsed);
    let (target, rhs) = assignment(&parsed, source, "value = 1");
    for query_first in [false, true] {
        let mut checker = context(&parsed, None);
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(check(&mut checker, returned, query_first), string);
        assert_eq!(declared_type(&mut checker, &value), string);
        assert_eq!(checker.get_type_at_location(target), Ok(string));
        diagnostic(
            &checker,
            &parsed,
            source,
            target,
            2322,
            &["number", "string"],
        );
        replay(&mut checker, &parsed, &[returned, target, rhs]);
    }
}

#[test]
fn conditional_initialized_union_writes_keep_the_full_declared_domain() {
    let source = "function update(input: string, flag: boolean): string | number { let value: string | number = input; if (flag) { value = 1; } return value; }";
    let parsed = parse_source_file(source);
    let value = local(&parsed, "value");
    let returned = last_return(&parsed);
    let (target, rhs) = assignment(&parsed, source, "value = 1");
    for query_first in [false, true] {
        let mut checker = context(&parsed, None);
        let result = check(&mut checker, returned, query_first);
        let declared = checker
            .get_type_from_type_node(value.annotation.unwrap())
            .unwrap();
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(checker.type_to_string(declared).unwrap(), "string | number");
        assert_eq!(declared_type(&mut checker, &value), declared);
        assert_eq!(checker.get_type_at_location(value.initializer), Ok(string));
        assert_eq!(checker.get_type_at_location(target), Ok(declared));
        assert_eq!(result, declared);
        assert!(checker.diagnostics().as_slice().is_empty());
        replay(
            &mut checker,
            &parsed,
            &[returned, target, rhs, value.initializer],
        );
    }
}

#[test]
fn conditional_local_write_join_retains_undefined_from_the_skip_branch() {
    let source = "function update(input: string | undefined, flag: boolean): string | undefined { let value = input; if (flag) { value = \"set\"; } return value; }";
    let parsed = parse_source_file(source);
    let value = local(&parsed, "value");
    let returned = last_return(&parsed);
    let (target, rhs) = assignment(&parsed, source, "value = \"set\"");
    assert!(value.annotation.is_none());
    for query_first in [false, true] {
        let mut checker = context(&parsed, None);
        let result = check(&mut checker, returned, query_first);
        let declared = declared_type(&mut checker, &value);
        assert_eq!(
            checker.type_to_string(declared).unwrap(),
            "string | undefined"
        );
        assert_eq!(result, declared);
        assert_eq!(
            checker.get_type_at_location(value.initializer),
            Ok(declared)
        );
        assert_eq!(checker.get_type_at_location(target), Ok(declared));
        assert!(checker.diagnostics().as_slice().is_empty());
        replay(
            &mut checker,
            &parsed,
            &[returned, target, rhs, value.initializer],
        );
    }
}

#[test]
fn conditional_const_write_reports_the_real_target_and_keeps_later_reads() {
    let source = "function update(input: string, flag: boolean): string { const value = input; if (flag) { value = 1; } return value; }";
    let parsed = parse_source_file(source);
    let value = local(&parsed, "value");
    let returned = last_return(&parsed);
    let (target, rhs) = assignment(&parsed, source, "value = 1");
    for query_first in [false, true] {
        let mut checker = context(&parsed, None);
        let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
        let (string, error) = (intrinsics.string_type, intrinsics.error_type);
        assert_eq!(check(&mut checker, returned, query_first), string);
        assert_eq!(declared_type(&mut checker, &value), string);
        assert_eq!(checker.get_type_at_location(target), Ok(error));
        diagnostic(&checker, &parsed, source, target, 2588, &["value"]);
        replay(&mut checker, &parsed, &[returned, target, rhs]);
    }
}

#[test]
fn real_pathe_normalizer_checks_its_conditional_writes_and_library_calls() {
    let parsed = parse_source_file(NORMALIZER);
    let es5 = parse_source_file(ES5);
    let core = parse_source_file(ES2015_CORE);
    let normalized = local(&parsed, "normalized");
    let returned = last_return(&parsed);
    assert!(normalized.annotation.is_none());
    for query_first in [false, true] {
        let mut checker = context(&parsed, Some([&es5, &core]));
        let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
        let (string, boolean) = (intrinsics.string_type, intrinsics.boolean_type);
        assert_eq!(check(&mut checker, returned, query_first), string);
        assert_eq!(declared_type(&mut checker, &normalized), string);
        assert_eq!(
            checker.get_type_at_location(normalized.initializer),
            Ok(string)
        );
        let mut queries = vec![returned, normalized.initializer];
        for (call_text, expected, library) in [
            (r#"normalized.includes("\\")"#, boolean, CORE_FILE),
            (r#"normalized.replace(/\\/g, "/")"#, string, ES5_FILE),
            ("driveLetter.toUpperCase()", string, ES5_FILE),
            ("normalized.slice(1)", string, ES5_FILE),
        ] {
            let call = expression(&parsed, NORMALIZER, SyntaxKind::CallExpression, call_text);
            assert_eq!(checker.get_type_at_location(call), Ok(expected));
            let signature = checker
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            assert_eq!(
                checker
                    .store()
                    .signature(signature)
                    .unwrap()
                    .declaration()
                    .unwrap()
                    .file,
                library
            );
            queries.push(call);
        }
        assert!(checker.diagnostics().as_slice().is_empty());
        replay(&mut checker, &parsed, &queries);
    }
}

#[test]
fn conditional_const_union_write_reports_2588_and_still_updates_branch_flow() {
    let source = concat!(
        "function update(input: string, flag: boolean): string | number {\n",
        "  const value: string | number = input;\n",
        "  if (flag) {\n",
        "    value = 1;\n",
        "    const taken: number = value;\n",
        "  }\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let value = local(&parsed, "value");
    let taken = local(&parsed, "taken");
    let returned = last_return(&parsed);
    let (target, rhs) = assignment(&parsed, source, "value = 1");
    for query_first in [false, true] {
        let mut checker = context(&parsed, None);
        let result = check(&mut checker, returned, query_first);
        let declared = checker
            .get_type_from_type_node(value.annotation.unwrap())
            .unwrap();
        let intrinsics = checker.store().intrinsic_bootstrap().unwrap();
        let (string, number, error) = (
            intrinsics.string_type,
            intrinsics.number_type,
            intrinsics.error_type,
        );
        diagnostic(&checker, &parsed, source, target, 2588, &["value"]);
        assert_eq!(checker.get_type_at_location(target), Ok(error));
        assert_eq!(checker.type_to_string(declared).unwrap(), "string | number");
        assert_eq!(declared_type(&mut checker, &value), declared);
        assert_eq!(checker.get_type_at_location(value.initializer), Ok(string));
        assert_eq!(checker.get_type_at_location(taken.initializer), Ok(number));
        assert_eq!(declared_type(&mut checker, &taken), number);
        assert_eq!(result, declared);
        replay(
            &mut checker,
            &parsed,
            &[returned, target, rhs, taken.initializer, value.initializer],
        );
    }
}
