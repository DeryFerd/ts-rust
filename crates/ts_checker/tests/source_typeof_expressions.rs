use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::LiteralValue,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const ES5_FILE: FileId = FileId::new(300_430);
const DOM_FILE: FileId = FileId::new(300_431);
const FILE: FileId = FileId::new(300_432);

struct Fixture {
    es5: ParseResult,
    dom: ParseResult,
    source: ParseResult,
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            es5: parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
            dom: parse_source_file(include_str!("../../ts_bundled/libs/lib.dom.d.ts")),
            source: parse_source_file(source),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = [
            (ES5_FILE, &self.es5, "\"/lib/lib.es5.d.ts\""),
            (DOM_FILE, &self.dom, "\"/lib/lib.dom.d.ts\""),
            (FILE, &self.source, "\"/project/typeof-expressions.ts\""),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in files {
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
                        file != FILE,
                        file != FILE,
                        CanonicalModuleState::Script,
                    ),
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
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                no_implicit_any: true,
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }
}

struct Variable {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: Option<NodeRef>,
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn variable(parsed: &ParseResult, file: FileId, expected: &str) -> Variable {
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
                declaration: node(parsed, file, id),
                name: node(parsed, file, data.name),
                annotation: data.type_.map(|id| node(parsed, file, id)),
                initializer: data.initializer.map(|id| node(parsed, file, id)),
            })
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
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

fn operand(parsed: &ParseResult, expression: NodeRef) -> NodeRef {
    let NodeData::TypeOfExpression(data) = &parsed.arena.get(expression.node).unwrap().data else {
        panic!("expected a typeof expression")
    };
    node(parsed, expression.file, data.expression)
}

fn assert_typeof_type(checker: &CanonicalCheckerContext<'_>) -> TypeId {
    let store = checker.store();
    let type_ = store.intrinsic_bootstrap().unwrap().typeof_type;
    let TypeData::Union(union) = store.type_payload(type_).unwrap().data() else {
        panic!("typeof must use the canonical string-literal union")
    };
    let mut names = union
        .union
        .types
        .iter()
        .map(|&member| {
            let TypeData::Literal(literal) = store.type_payload(member).unwrap().data() else {
                panic!("typeof members must be real literal types")
            };
            let LiteralValue::String(value) = &literal.value else {
                panic!("typeof members must be string literals")
            };
            assert_eq!(literal.regular_type, member);
            value.as_str()
        })
        .collect::<Vec<_>>();
    names.sort_unstable();
    assert_eq!(
        names,
        [
            "bigint", "boolean", "function", "number", "object", "string", "symbol", "undefined",
        ]
    );
    type_
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn replay(checker: &mut CanonicalCheckerContext<'_>, locations: &[(NodeRef, TypeId)]) {
    let warm_counts = counts(checker);
    let diagnostics = checker.diagnostics().clone();
    let source = checker.source_file(FILE).unwrap();
    let source_links = checker.store().source_file_links(source).cloned();
    assert!(source_links.as_ref().unwrap().type_checked);
    let links = |checker: &CanonicalCheckerContext<'_>| {
        locations
            .iter()
            .map(|&(location, _)| {
                (
                    checker.store().type_node_links(location).cloned(),
                    checker.store().symbol_node_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let warm_links = links(checker);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        for &(location, expected) in locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        assert_eq!(counts(checker), warm_counts);
        assert_eq!(links(checker), warm_links);
        assert_eq!(
            checker.store().source_file_links(source),
            source_links.as_ref()
        );
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep operand identities, the nested argument, and replay together.
fn typeof_checks_bundled_dom_local_and_call_operands_and_replays() {
    let fixture = Fixture::new(concat!(
        "declare function readCount(input: number): number;\n",
        "declare function consume(value: string): number;\n",
        "const count: number = 1;\n",
        "const browserKind = typeof window;\n",
        "const localKind = typeof count;\n",
        "const callKind = typeof readCount(count);\n",
        "const accepted: string = typeof window;\n",
        "const consumed: number = consume(typeof count);\n",
    ));
    let source = &fixture.source;
    let values =
        ["browserKind", "localKind", "callKind"].map(|name| variable(source, FILE, name));
    let accepted = variable(source, FILE, "accepted");
    let consumed = variable(source, FILE, "consumed");
    let NodeData::CallExpression(consume) =
        &source.arena.get(consumed.initializer.unwrap().node).unwrap().data
    else {
        panic!("expected the call with a typeof argument")
    };
    let nested = node(source, FILE, consume.arguments.nodes[0]);
    let dom_window = variable(&fixture.dom, DOM_FILE, "window");
    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            checker
                .get_type_at_location(values[0].initializer.unwrap())
                .unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let typeof_type = assert_typeof_type(&checker);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let mut locations = Vec::new();
        for value in &values {
            for location in [value.initializer.unwrap(), value.name] {
                assert_eq!(checker.get_type_at_location(location), Ok(typeof_type));
                locations.push((location, typeof_type));
            }
        }
        let window_operand = operand(source, values[0].initializer.unwrap());
        let window_symbol = symbol(&checker, dom_window.declaration);
        assert_eq!(
            checker.get_symbol_at_location(window_operand),
            Ok(Some(window_symbol))
        );
        assert_eq!(
            checker.store().symbol(window_symbol).unwrap().name().as_utf8(),
            Some("window")
        );
        let window_type = checker.get_type_at_location(window_operand).unwrap();
        assert_eq!(
            checker.get_type_from_type_node(dom_window.annotation.unwrap()),
            Ok(window_type)
        );
        let TypeData::Intersection(window) =
            checker.store().type_payload(window_type).unwrap().data()
        else {
            panic!("window must keep its bundled Window and globalThis intersection")
        };
        assert_eq!(window.intersection.types.len(), 2);
        locations.push((window_operand, window_type));
        for value in &values[1..] {
            let location = operand(source, value.initializer.unwrap());
            assert_eq!(checker.get_type_at_location(location), Ok(number));
            locations.push((location, number));
        }
        let call = operand(source, values[2].initializer.unwrap());
        let signature = checker
            .store()
            .signature_links(call)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(
            checker.store().signature(signature).unwrap().resolved_return_type(),
            Some(number)
        );
        assert_eq!(checker.get_type_at_location(accepted.name), Ok(string));
        assert_eq!(
            checker.get_type_at_location(accepted.initializer.unwrap()),
            Ok(typeof_type)
        );
        locations.extend([
            (accepted.name, string),
            (accepted.initializer.unwrap(), typeof_type),
            (consumed.name, number),
            (consumed.initializer.unwrap(), number),
            (nested, typeof_type),
            (operand(source, nested), number),
        ]);
        for &(location, expected) in &locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        replay(&mut checker, &locations);
    }
}

#[test]
fn typeof_keeps_native_name_assignment_and_argument_errors_on_replay() {
    let fixture = Fixture::new(concat!(
        "declare function readCount(input: number): number;\n",
        "const wrong: number = typeof 1;\n",
        "const unresolved = typeof missingOperand;\n",
        "const invalidCall = typeof readCount('wrong');\n",
    ));
    let source = &fixture.source;
    let values =
        ["wrong", "unresolved", "invalidCall"].map(|name| variable(source, FILE, name));
    let missing = operand(source, values[1].initializer.unwrap());
    let call = operand(source, values[2].initializer.unwrap());
    let NodeData::CallExpression(call_data) = &source.arena.get(call.node).unwrap().data else {
        panic!("expected the checked call operand")
    };
    let argument = node(source, FILE, call_data.arguments.nodes[0]);
    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            checker
                .get_type_at_location(values[0].initializer.unwrap())
                .unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
        for (code, location) in [(2322, values[0].name), (2304, missing), (2345, argument)] {
            let matching = diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.diagnostic.code() == code)
                .collect::<Vec<_>>();
            let [diagnostic] = matching.as_slice() else {
                panic!("expected one native diagnostic {code}: {diagnostics:?}")
            };
            assert_eq!(diagnostic.node, Some(location));
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            if code == 2304 {
                assert_eq!(diagnostic.diagnostic.arguments, ["missingOperand"]);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "Cannot find name 'missingOperand'."
                );
            } else {
                assert_eq!(diagnostic.diagnostic.arguments.len(), 2);
                assert_eq!(diagnostic.diagnostic.arguments[1], "number");
            }
        }
        let typeof_type = assert_typeof_type(&checker);
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let mut locations = vec![(values[0].name, number), (call, number)];
        for value in &values {
            let expression = value.initializer.unwrap();
            assert_eq!(checker.get_type_at_location(expression), Ok(typeof_type));
            locations.push((expression, typeof_type));
        }
        for value in &values[1..] {
            assert_eq!(checker.get_type_at_location(value.name), Ok(typeof_type));
            locations.push((value.name, typeof_type));
        }
        for &(location, expected) in &locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        replay(&mut checker, &locations);
    }
}
