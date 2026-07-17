use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, SymbolNodeLinks,
    TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

fn checker_context(
    parsed: &ParseResult,
    file: FileId,
    declaration_file: bool,
    module_state: CanonicalModuleState,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/ambient-variables.ts\""),
                CanonicalSourceLanguage::TypeScript,
                declaration_file,
                module_state,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = variable_declaration(parsed, file, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable
            .initializer
            .expect("fixture variable is initialized"),
    )
}

fn variable_type_node(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = variable_declaration(parsed, file, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable.type_.expect("fixture variable is annotated"),
    )
}

fn variable_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = variable_declaration(parsed, file, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn ambient_variables_hoist_exact_types_in_scripts_and_external_modules() {
    for (index, (prefix, module_state)) in [
        ("", CanonicalModuleState::Script),
        ("export {};\n", CanonicalModuleState::External),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!(
            "{prefix}{}",
            concat!(
                "const beforeConst = ambientConst;\n",
                "const beforeLet = ambientLet;\n",
                "const beforeVar = ambientVar;\n",
                "declare const ambientConst: LaterNumber;\n",
                "declare let ambientLet: string;\n",
                "declare var ambientVar: boolean;\n",
                "type LaterNumber = number;\n",
                "const afterConst = ambientConst;\n",
                "const afterLet = ambientLet;\n",
                "const afterVar = ambientVar;\n",
                "ambientLet = \"next\";\n",
                "ambientVar = false;\n",
            ),
        );
        let parsed = parse_source_file(&source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_100 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, false, module_state);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
        let ambient = [
            (
                variable_symbol(&parsed, file, &context, "ambientConst"),
                number,
            ),
            (
                variable_symbol(&parsed, file, &context, "ambientLet"),
                string,
            ),
            (
                variable_symbol(&parsed, file, &context, "ambientVar"),
                boolean,
            ),
        ];
        let reads = [
            ("beforeConst", ambient[0]),
            ("beforeLet", ambient[1]),
            ("beforeVar", ambient[2]),
            ("afterConst", ambient[0]),
            ("afterLet", ambient[1]),
            ("afterVar", ambient[2]),
        ]
        .map(|(name, (symbol, type_))| {
            (
                variable_initializer(&parsed, file, name),
                variable_symbol(&parsed, file, &context, name),
                symbol,
                type_,
            )
        });
        let alias_root = variable_type_node(&parsed, file, "ambientConst");

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        assert!(is_type_checked(&context, file));
        for (symbol, type_) in ambient {
            assert_eq!(
                context.store().value_symbol_links(symbol),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            );
        }
        for (read, owner, resolved_symbol, type_) in reads {
            assert_eq!(
                context.store().symbol_node_links(read),
                Some(&SymbolNodeLinks {
                    resolved_symbol: Some(resolved_symbol),
                })
            );
            assert_eq!(
                context.store().type_node_links(read),
                Some(&TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                })
            );
            assert_eq!(
                context.store().value_symbol_links(owner),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
            );
        }
        assert_eq!(
            context.store().type_node_links(alias_root),
            Some(&TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            })
        );

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            ambient.map(|(symbol, _)| context.store().value_symbol_links(symbol).cloned()),
            reads.map(|(read, owner, _, _)| {
                (
                    context.store().symbol_node_links(read).cloned(),
                    context.store().type_node_links(read).cloned(),
                    context.store().value_symbol_links(owner).cloned(),
                )
            }),
            context.store().type_node_links(alias_root).cloned(),
            context.diagnostics().len(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
                ambient.map(|(symbol, _)| context.store().value_symbol_links(symbol).cloned()),
                reads.map(|(read, owner, _, _)| {
                    (
                        context.store().symbol_node_links(read).cloned(),
                        context.store().type_node_links(read).cloned(),
                        context.store().value_symbol_links(owner).cloned(),
                    )
                }),
                context.store().type_node_links(alias_root).cloned(),
                context.diagnostics().len(),
            ),
            warm
        );
    }
}

#[test]
fn ambient_annotation_can_name_a_later_interface() {
    let parsed = parse_source_file(concat!(
        "const beforeModel = ambientModel;\n",
        "declare const ambientModel: LaterModel;\n",
        "interface LaterModel { value: number; }\n",
        "const afterModel = ambientModel;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_102);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let ambient = variable_symbol(&parsed, file, &context, "ambientModel");
    let before_owner = variable_symbol(&parsed, file, &context, "beforeModel");
    let after_owner = variable_symbol(&parsed, file, &context, "afterModel");
    let before = variable_initializer(&parsed, file, "beforeModel");
    let after = variable_initializer(&parsed, file, "afterModel");
    let annotation = variable_type_node(&parsed, file, "ambientModel");

    context.check_source_file(file).unwrap();

    let interface_type = context
        .store()
        .type_node_links(annotation)
        .and_then(|links| links.resolved_type)
        .expect("the interface reference must retain its canonical type");
    for symbol in [ambient, before_owner, after_owner] {
        assert_eq!(
            context.store().value_symbol_links(symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(interface_type),
                ..ValueSymbolLinks::default()
            })
        );
    }
    for read in [before, after] {
        assert_eq!(
            context.store().symbol_node_links(read),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(ambient),
            })
        );
        assert_eq!(
            context.store().type_node_links(read),
            Some(&TypeNodeLinks {
                resolved_type: Some(interface_type),
                ..TypeNodeLinks::default()
            })
        );
    }
    assert!(context.diagnostics().is_empty());
    assert!(is_type_checked(&context, file));

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().relation_state_snapshot(),
        context.store().type_node_links(annotation).cloned(),
        [ambient, before_owner, after_owner]
            .map(|symbol| context.store().value_symbol_links(symbol).cloned()),
        [before, after].map(|read| {
            (
                context.store().symbol_node_links(read).cloned(),
                context.store().type_node_links(read).cloned(),
            )
        }),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().relation_state_snapshot(),
            context.store().type_node_links(annotation).cloned(),
            [ambient, before_owner, after_owner]
                .map(|symbol| context.store().value_symbol_links(symbol).cloned()),
            [before, after].map(|read| {
                (
                    context.store().symbol_node_links(read).cloned(),
                    context.store().type_node_links(read).cloned(),
                )
            }),
        ),
        warm
    );
}

#[test]
fn later_missing_ambient_annotation_is_typed_atomic_and_repeatable() {
    let parsed = parse_source_file(concat!(
        "const early = 1;\n",
        "declare const valid: number;\n",
        "const read = valid;\n",
        "declare let missing;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_103);
    let mut context = checker_context(&parsed, file, false, CanonicalModuleState::Script);
    let missing = variable_declaration(&parsed, file, "missing");
    let early = variable_symbol(&parsed, file, &context, "early");
    let valid = variable_symbol(&parsed, file, &context, "valid");
    let read_owner = variable_symbol(&parsed, file, &context, "read");
    let read = variable_initializer(&parsed, file, "read");
    let before = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().relation_state_snapshot(),
    );
    let expected =
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::MissingVariableType(missing));

    for _ in 0..2 {
        assert_eq!(context.check_source_file(file), Err(expected));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
        for symbol in [early, valid, read_owner] {
            assert!(context.store().value_symbol_links(symbol).is_none());
        }
        assert!(context.store().symbol_node_links(read).is_none());
        assert!(context.store().type_node_links(read).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}

#[test]
fn ambient_variable_forms_outside_the_exact_leaf_remain_typed_boundaries() {
    for (index, (source, declaration_file, module_state)) in [
        (
            "declare const initialized: number = 1;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare const { value }: { value: number };",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "export declare const exported: number;",
            false,
            CanonicalModuleState::External,
        ),
        (
            "declare var merged: number; declare var merged: number;",
            false,
            CanonicalModuleState::Script,
        ),
        (
            "declare const explicit: number;",
            true,
            CanonicalModuleState::Script,
        ),
        (
            "declare const fixed: number; fixed = 1;",
            false,
            CanonicalModuleState::Script,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_110 + u32::try_from(index).unwrap());
        let mut context = checker_context(&parsed, file, declaration_file, module_state);
        assert!(
            matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(_))
            ),
            "fixture unexpectedly escaped its typed boundary: {source}",
        );
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
    }
}
