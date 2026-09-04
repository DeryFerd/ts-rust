use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(300_492);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-object-equality.ts\""),
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
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        checker.diagnostics().clone(),
    )
}

fn check_class_object_equality(operator: &str, invalid_return: bool) {
    let return_type = if invalid_return {
        "string"
    } else {
        "string | number"
    };
    let source = format!(
        "type Box<T> = {{ value: T }};\n\
         declare const initial: Box<string | number>;\n\
         class Reader {{\n  current: Box<string | number> = initial;\n  \
         read(other: Box<string>): {return_type} {{\n    \
         if (this.current {operator} other) {{\n      \
         return this.current.value;\n    }} else {{\n      \
         return this.current.value;\n    }}\n  }}\n}}\n"
    );
    let parsed = parse_source_file(&source);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(
        diagnostics.len(),
        if invalid_return { 2 } else { 0 },
        "{diagnostics:?}"
    );
    if invalid_return {
        let starts = source
            .match_indices("return this.current.value;")
            .map(|(start, _)| start);
        for (diagnostic, start) in diagnostics.iter().zip(starts) {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(
                diagnostic.diagnostic.arguments,
                ["string | number", "string"]
            );
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
            let node = parsed.arena.get(diagnostic.node.unwrap().node).unwrap();
            assert!(matches!(node.data, NodeData::ReturnStatement(_)));
            assert_eq!(node.range.start.get() as usize, start);
            assert_eq!(
                node.range.end.get() as usize,
                start + "return this.current.value;".len()
            );
        }
    }

    let mut current_reads = Vec::new();
    let mut value_reads = Vec::new();
    for (id, node) in parsed.arena.iter() {
        if !matches!(node.data, NodeData::PropertyAccessExpression(_)) {
            continue;
        }
        let reference = NodeRef::new(parsed.arena.id(), FILE, id);
        match &source[node.range.start.get() as usize..node.range.end.get() as usize] {
            "this.current" => current_reads.push(reference),
            "this.current.value" => value_reads.push(reference),
            _ => {}
        }
    }
    assert_eq!(current_reads.len(), 3);
    assert_eq!(value_reads.len(), 2);
    let current = checker.get_type_at_location(current_reads[0]).unwrap();
    let member = checker
        .get_symbol_at_location(current_reads[0])
        .unwrap()
        .unwrap();
    assert!(matches!(
        checker.store().type_payload(current).unwrap().data(),
        TypeData::Object(_)
    ));
    for node in &current_reads {
        assert_eq!(checker.get_type_at_location(*node), Ok(current));
        assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(member)));
    }
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let mut expected = vec![bootstrap.string_type, bootstrap.number_type];
    expected.sort();
    for node in &value_reads {
        let type_ = checker.get_type_at_location(*node).unwrap();
        let TypeData::Union(union) = checker.store().type_payload(type_).unwrap().data() else {
            panic!("expected the original string | number value type");
        };
        let mut actual = union.union.types.clone();
        actual.sort();
        assert_eq!(actual, expected);
    }
    let warm = snapshot(&checker, &parsed);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        for node in &current_reads {
            assert_eq!(checker.get_type_at_location(*node), Ok(current));
            assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(member)));
        }
        assert_eq!(snapshot(&checker, &parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
    }
}

#[test]
fn class_object_equality_keeps_alias_identity_on_both_branches() {
    for operator in ["!==", "===", "==", "!="] {
        check_class_object_equality(operator, false);
    }
}

#[test]
fn class_object_equality_reports_invalid_returns_on_both_branches() {
    for operator in ["!==", "===", "==", "!="] {
        check_class_object_equality(operator, true);
    }
}

#[test]
fn class_object_equality_filters_disjoint_aliases_to_never() {
    for operator in ["!==", "===", "==", "!="] {
        let equal = matches!(operator, "===" | "==");
        let (true_type, false_type) = if equal {
            ("never", "Box<string>")
        } else {
            ("Box<string>", "never")
        };
        let source = format!(
            "type Box<T> = {{ value: T }};\n\
             declare const initial: Box<string>;\n\
             class Reader {{\n  current: Box<string> = initial;\n  \
             read(other: Box<number>): unknown {{\n    \
             if (this.current {operator} other) {{\n      \
             const whenTrue: {true_type} = this.current;\n      \
             return 1;\n    }} else {{\n      \
             const whenFalse: {false_type} = this.current;\n      \
             return this.current;\n    }}\n  }}\n}}\n"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&parsed);
        checker.check_source_file(FILE).unwrap();
        let diagnostics = checker.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.diagnostic.code(), 2367);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["Box<string>", "Box<number>"]
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        let condition = format!("this.current {operator} other");
        let start = source.find(&condition).unwrap();
        let node = parsed.arena.get(diagnostic.node.unwrap().node).unwrap();
        assert!(matches!(node.data, NodeData::BinaryExpression(_)));
        assert_eq!(node.range.start.get() as usize, start);
        assert_eq!(node.range.end.get() as usize, start + condition.len());

        let mut reads = parsed
            .arena
            .iter()
            .filter_map(|(id, node)| {
                if matches!(node.data, NodeData::PropertyAccessExpression(_))
                    && &source[node.range.start.get() as usize..node.range.end.get() as usize]
                        == "this.current"
                {
                    Some((node.range.start, NodeRef::new(parsed.arena.id(), FILE, id)))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        reads.sort_by_key(|(start, _)| *start);
        assert_eq!(reads.len(), 4);
        let incoming = checker.get_type_at_location(reads[0].1).unwrap();
        assert!(matches!(
            checker.store().type_payload(incoming).unwrap().data(),
            TypeData::Object(_)
        ));
        let never = checker.store().intrinsic_bootstrap().unwrap().never_type;
        let member = checker.get_symbol_at_location(reads[0].1).unwrap().unwrap();
        let expected = if equal {
            [incoming, never, incoming, incoming]
        } else {
            [incoming, incoming, never, never]
        };
        for ((_, node), expected) in reads.iter().zip(expected) {
            assert_eq!(checker.get_type_at_location(*node), Ok(expected));
            assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(member)));
        }
        let warm = snapshot(&checker, &parsed);
        for _ in 0..2 {
            checker.recheck_source_file(FILE).unwrap();
            for ((_, node), expected) in reads.iter().zip(expected) {
                assert_eq!(checker.get_type_at_location(*node), Ok(expected));
                assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(member)));
            }
            assert_eq!(snapshot(&checker, &parsed), warm);
            assert!(checker.store().type_resolution_is_empty());
            assert!(
                checker
                    .store()
                    .source_file_links(checker.source_file(FILE).unwrap())
                    .unwrap()
                    .type_checked
            );
        }
    }
}

fn check_class_object_union(operator: &str, invalid_assignment: bool, named: bool) {
    let equal = matches!(operator, "===" | "==");
    let alias = if named {
        "type Pair = Box<string> | Box<number>;\n"
    } else {
        ""
    };
    let original = if named {
        "Pair | Box<boolean>"
    } else {
        "Box<string> | Box<number> | Box<boolean>"
    };
    let filtered = if named {
        "Pair"
    } else {
        "Box<string> | Box<number>"
    };
    let true_type = if invalid_assignment {
        "Box<boolean>"
    } else if equal {
        filtered
    } else {
        original
    };
    let false_type = if equal { original } else { filtered };
    let source = format!(
        "type Box<T> = {{ value: T }};\n{alias}\
             declare const initial: {original};\n\
             class Reader {{\n  current: {original} = initial;\n  \
             read(other: {filtered}): unknown {{\n    \
             if (this.current {operator} other) {{\n      \
             const whenTrue: {true_type} = this.current;\n      \
             return 1;\n    }} else {{\n      \
             const whenFalse: {false_type} = this.current;\n      \
             return this.current;\n    }}\n  }}\n}}\n"
    );
    let parsed = parse_source_file(&source);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(
        diagnostics.len(),
        usize::from(invalid_assignment),
        "{diagnostics:?}"
    );
    if invalid_assignment {
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.arguments, [filtered, "Box<boolean>"]);
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        let node = parsed.arena.get(diagnostic.node.unwrap().node).unwrap();
        assert_eq!(
            node.range.start.get() as usize,
            source.find("whenTrue").unwrap()
        );
        assert_eq!(
            &source[node.range.start.get() as usize..node.range.end.get() as usize],
            "whenTrue"
        );
    }
    let mut reads = parsed
        .arena
        .iter()
        .filter_map(|(id, node)| {
            if matches!(node.data, NodeData::PropertyAccessExpression(_))
                && &source[node.range.start.get() as usize..node.range.end.get() as usize]
                    == "this.current"
            {
                Some((node.range.start, NodeRef::new(parsed.arena.id(), FILE, id)))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    reads.sort_by_key(|(start, _)| *start);
    assert_eq!(reads.len(), 4);
    let other_start = source.find("other)").unwrap();
    let other = parsed
        .arena
        .iter()
        .find_map(|(id, node)| {
            (node.range.start.get() as usize == other_start
                && node.range.end.get() as usize == other_start + "other".len())
            .then_some(NodeRef::new(parsed.arena.id(), FILE, id))
        })
        .unwrap();
    let incoming = checker.get_type_at_location(reads[0].1).unwrap();
    let narrowed = checker.get_type_at_location(other).unwrap();
    assert_ne!(incoming, narrowed);
    let TypeData::Union(original_union) = checker.store().type_payload(incoming).unwrap().data()
    else {
        panic!("expected the three-member input union");
    };
    let TypeData::Union(filtered_union) = checker.store().type_payload(narrowed).unwrap().data()
    else {
        panic!("expected the two-member comparison union");
    };
    assert_eq!(original_union.union.types.len(), 3);
    assert_eq!(filtered_union.union.types.len(), 2);
    assert!(
        filtered_union
            .union
            .types
            .iter()
            .all(|type_| original_union.union.types.contains(type_))
    );
    if named {
        let origin = original_union
            .origin
            .expect("the input must retain its named union origin");
        let TypeData::Union(origin) = checker.store().type_payload(origin).unwrap().data() else {
            panic!("expected a union origin");
        };
        assert!(origin.union.types.contains(&narrowed));
        assert!(
            checker
                .store()
                .type_payload(narrowed)
                .unwrap()
                .alias()
                .is_some()
        );
    }
    let member = checker.get_symbol_at_location(reads[0].1).unwrap().unwrap();
    let expected = if equal {
        [incoming, narrowed, incoming, incoming]
    } else {
        [incoming, incoming, narrowed, narrowed]
    };
    for ((_, node), expected) in reads.iter().zip(expected) {
        assert_eq!(checker.get_type_at_location(*node), Ok(expected));
        assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(member)));
    }
    let warm = snapshot(&checker, &parsed);
    for _ in 0..2 {
        checker.recheck_source_file(FILE).unwrap();
        for ((_, node), expected) in reads.iter().zip(expected) {
            assert_eq!(checker.get_type_at_location(*node), Ok(expected));
            assert_eq!(checker.get_symbol_at_location(*node), Ok(Some(member)));
        }
        assert_eq!(snapshot(&checker, &parsed), warm);
        assert!(checker.store().type_resolution_is_empty());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
    }
}

#[test]
fn class_object_equality_filters_object_unions_and_replays() {
    for (operator, invalid_assignment) in [
        ("!==", false),
        ("===", false),
        ("==", false),
        ("!=", false),
        ("===", true),
    ] {
        check_class_object_union(operator, invalid_assignment, false);
    }
}

#[test]
fn class_object_equality_retains_the_named_union_origin() {
    check_class_object_union("===", false, true);
}
