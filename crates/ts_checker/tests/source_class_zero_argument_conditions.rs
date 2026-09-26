use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(300_490);
const SOURCE: &str = r"class Base {
  protected hasListeners(): boolean { return false; }
}
class Manager extends Base {
  isOnline(): boolean { return true; }
  needsFlag(flag?: boolean): boolean { return true; }
  read(): number {
    if (this.isOnline()) { return 1; }
    if (!this.hasListeners()) {
      return 2;
    } else {
      return 3;
    }
  }
  checkFlag(): void {
    if (this.needsFlag()) {}
  }
}
";

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-zero-argument-conditions.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn named(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(id, record)| {
        let name = match &record.data {
            NodeData::ClassDeclaration(class) => class.name?,
            NodeData::MethodDeclaration(method) => method.name,
            _ => return None,
        };
        let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, id))
    });
    let result = nodes.next().unwrap_or_else(|| panic!("missing {expected}"));
    assert!(nodes.next().is_none(), "more than one {expected}");
    result
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn call_nodes(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    let mut nodes = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::CallExpression(call) = &record.data else {
            return None;
        };
        let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(call.expression)?.data
        else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
            return None;
        };
        if name.text != expected {
            return None;
        }
        assert!(call.arguments.nodes.is_empty());
        assert!(call.type_arguments.is_none());
        assert_eq!(
            parsed.arena.get(access.expression)?.kind,
            SyntaxKind::ThisKeyword
        );
        Some((
            node(parsed, id),
            node(parsed, call.expression),
            node(parsed, access.expression),
        ))
    });
    let result = nodes
        .next()
        .unwrap_or_else(|| panic!("missing {expected} call"));
    assert!(nodes.next().is_none());
    result
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        [
            "Base",
            "Manager",
            "hasListeners",
            "isOnline",
            "needsFlag",
            "read",
            "checkFlag",
        ]
        .map(|name| {
            let symbol = symbol(checker, named(parsed, name));
            (
                store.declared_type_links(symbol).cloned(),
                store.value_symbol_links(symbol).cloned(),
            )
        }),
        store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
        checker.diagnostics().clone(),
    )
}

#[test]
fn zero_argument_class_conditions_keep_calls_branches_diagnostics_and_replay() {
    for invalid in [false, true] {
        let source = if invalid {
            SOURCE
                .replace("flag?: boolean", "flag: boolean")
                .replace("return 2;", "return 'absent';")
                .replace("return 3;", "return 'present';")
        } else {
            SOURCE.to_owned()
        };
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let flag_access = call_nodes(&parsed, "needsFlag").1;
        let NodeData::PropertyAccessExpression(access) =
            &parsed.arena.get(flag_access.node).unwrap().data
        else {
            unreachable!()
        };
        let flag_name = node(&parsed, access.name);
        if invalid {
            let branch_returns = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::ReturnStatement(returned) = &record.data else {
                        return None;
                    };
                    let expression = parsed.arena.get(returned.expression?)?;
                    (expression.kind == SyntaxKind::StringLiteral).then_some(node(&parsed, id))
                })
                .collect::<Vec<_>>();
            assert_eq!(branch_returns.len(), 2);
            let diagnostics = checker.diagnostics().as_slice();
            assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
            for (code, site) in [
                (2322, branch_returns[0]),
                (2322, branch_returns[1]),
                (2554, flag_name),
            ] {
                let matches = diagnostics
                    .iter()
                    .filter(|diagnostic| {
                        diagnostic.diagnostic.code() == code && diagnostic.node == Some(site)
                    })
                    .collect::<Vec<_>>();
                let [diagnostic] = matches.as_slice() else {
                    panic!("missing diagnostic {code} at {site:?}: {diagnostics:?}")
                };
                assert_eq!(diagnostic.diagnostic.category(), Category::Error);
                assert_eq!(diagnostic.range_override, None);
                if code == 2554 {
                    assert_eq!(
                        diagnostic.diagnostic.arguments,
                        ["1".to_owned(), "0".to_owned()]
                    );
                    assert_eq!(
                        diagnostic.diagnostic.render().unwrap(),
                        "Expected 1 arguments, but got 0."
                    );
                }
            }
        } else {
            assert!(
                checker.diagnostics().as_slice().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }

        let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
        let manager = symbol(&checker, named(&parsed, "Manager"));
        let instance = checker.get_declared_type_of_symbol(manager).unwrap();
        let mut queries = Vec::new();
        let mut symbols = Vec::new();
        for (name, owner, minimum) in [
            ("isOnline", "Manager", 0),
            ("hasListeners", "Base", 0),
            ("needsFlag", "Manager", i32::from(invalid)),
        ] {
            let declaration = named(&parsed, name);
            let method = symbol(&checker, declaration);
            assert_eq!(
                checker.store().symbol(method).unwrap().parent(),
                Some(symbol(&checker, named(&parsed, owner)))
            );
            let (call, access, receiver) = call_nodes(&parsed, name);
            assert_eq!(checker.get_type_at_location(call), Ok(boolean));
            assert_eq!(checker.get_symbol_at_location(access), Ok(Some(method)));
            let signature = checker
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            assert_eq!(checker.get_return_type_of_signature(signature), Ok(boolean));
            let signature = checker.store().signature(signature).unwrap();
            assert_eq!(signature.declaration(), Some(declaration));
            assert_eq!(signature.min_argument_count(), minimum);
            assert_eq!(
                signature.parameters().len(),
                usize::from(name == "needsFlag")
            );
            assert!(signature.type_parameters().is_empty());
            let this_type = checker.get_type_at_location(receiver).unwrap();
            let this_record = checker.store().type_payload(this_type).unwrap();
            assert_eq!(this_record.symbol(), Some(manager));
            let TypeData::TypeParameter(this) = this_record.data() else {
                panic!("the receiver keeps Manager's own this type")
            };
            assert!(this.is_this_type);
            assert_eq!(this.constraint, Some(instance));
            queries.extend([(call, boolean), (receiver, this_type)]);
            symbols.push((access, method));
        }
        let negation = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                (record.kind == SyntaxKind::PrefixUnaryExpression).then_some(node(&parsed, id))
            })
            .unwrap();
        assert_eq!(checker.get_type_at_location(negation), Ok(boolean));
        queries.push((negation, boolean));
        let warm = snapshot(&checker, &parsed);
        for recheck in [false, true] {
            if recheck {
                checker.recheck_source_file(FILE).unwrap();
            } else {
                checker.check_source_file(FILE).unwrap();
            }
            for &(node, expected) in &queries {
                assert_eq!(checker.get_type_at_location(node), Ok(expected));
            }
            for &(node, expected) in &symbols {
                assert_eq!(checker.get_symbol_at_location(node), Ok(Some(expected)));
            }
            assert_eq!(snapshot(&checker, &parsed), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}
