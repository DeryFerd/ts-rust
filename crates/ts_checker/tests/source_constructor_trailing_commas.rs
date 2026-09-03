use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassMembers, IntrinsicBootstrapOptions,
    signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(213_710);

fn source(defaulted: bool, invalid: bool) -> String {
    let default = if defaulted { " = \"ready\"" } else { "" };
    let minimum = if defaulted { "2" } else { "2, \"minimum\"" };
    let errors = if invalid {
        if defaulted {
            "const wrongType = new Packet(\"bad\", \"ok\");\nconst missing = new Packet();\n"
        } else {
            "const wrongType = new Packet(\"bad\", \"ok\");\nconst missing = new Packet(1);\n"
        }
    } else {
        ""
    };
    format!(
        "class Packet {{\n\
           count: number;\n\
           label: string;\n\
           constructor(count: number, label: string{default},) {{\n\
             this.count = count;\n\
             this.label = label;\n\
           }}\n\
         }}\n\
         const full = new Packet(1, \"full\");\n\
         const minimum = new Packet({minimum});\n\
         const count: number = full.count;\n\
         const label: string = full.label;\n\
         {errors}"
    )
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/constructor-trailing-commas.ts\""),
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
            strict_property_initialization: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: ts_ast::NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let parent_record = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(parent_record.range.start <= record.range.start);
    assert!(record.range.end <= parent_record.range.end);
    node(parsed, id)
}

#[derive(Clone, Copy)]
struct Parts {
    class: NodeRef,
    constructor: NodeRef,
    parameters: [NodeRef; 2],
    fields: [NodeRef; 2],
}

fn parts(parsed: &ParseResult, defaulted: bool) -> Parts {
    let classes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::ClassDeclaration).then_some(node(parsed, id))
        })
        .collect::<Vec<_>>();
    let [class] = classes.as_slice() else {
        panic!("the fixture has one class")
    };
    let class = *class;
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    let [count, label, constructor] = data.members.nodes.as_slice() else {
        panic!("Packet has two fields and one constructor")
    };
    let fields = [*count, *label].map(|id| child(parsed, class, id));
    let constructor = child(parsed, class, *constructor);
    let NodeData::ConstructorDeclaration(data) = &parsed.arena.get(constructor.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.parameters.has_trailing_comma);
    assert!(data.body.is_some());
    let [count, label] = data.parameters.nodes.as_slice() else {
        panic!("the comma must not add a parameter")
    };
    let parameters = [*count, *label].map(|id| child(parsed, constructor, id));
    for (index, parameter) in parameters.into_iter().enumerate() {
        let record = parsed.arena.get(parameter.node).unwrap();
        assert!(data.parameters.range.start <= record.range.start);
        assert!(record.range.end <= data.parameters.range.end);
        let NodeData::ParameterDeclaration(parameter_data) = &record.data else {
            unreachable!()
        };
        assert!(parameter_data.dot_dot_dot_token.is_none());
        assert!(parameter_data.question_token.is_none());
        assert_eq!(
            parameter_data.initializer.is_some(),
            defaulted && index == 1
        );
        child(parsed, parameter, parameter_data.name);
        child(parsed, parameter, parameter_data.type_.unwrap());
    }
    Parts {
        class,
        constructor,
        parameters,
        fields,
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
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
            (name.text == expected)
                .then(|| child(parsed, node(parsed, id), data.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing initialized variable {expected}"))
}

fn assert_checked(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    parts: Parts,
    defaulted: bool,
) -> ClassMembers {
    let owner = symbol(context, parts.class);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let signature = members.default_construct_signature();
    let parameter_symbols = parts.parameters.map(|parameter| symbol(context, parameter));
    let field_symbols = parts.fields.map(|field| symbol(context, field));
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.constructor));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.parameters(), parameter_symbols);
    assert_eq!(record.min_argument_count(), if defaulted { 1 } else { 2 });
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        record.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    assert_eq!(members.declared_instance_properties(), field_symbols);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let types = [bootstrap.number_type, bootstrap.string_type];
    for (index, parameter) in parts.parameters.into_iter().enumerate() {
        let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
        else {
            unreachable!()
        };
        let parameter_symbol = parameter_symbols[index];
        let record = context.store().symbol(parameter_symbol).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some([parameter].as_slice()));
        assert_eq!(record.value_declaration(), Some(parameter));
        assert_ne!(parameter_symbol, field_symbols[index]);
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter_symbol)
                .unwrap()
                .resolved_type,
            Some(types[index]),
        );
        assert_eq!(
            context.get_type_from_type_node(child(parsed, parameter, data.type_.unwrap())),
            Ok(types[index]),
        );
        assert_eq!(
            context.get_type_at_location(child(parsed, parameter, data.name)),
            Ok(types[index])
        );
    }
    for (name, type_) in ["count", "label"].into_iter().zip(types) {
        assert_eq!(
            context.get_type_at_location(initializer(parsed, name)),
            Ok(type_)
        );
    }
    for (id, record) in parsed.arena.iter() {
        if record.kind == SyntaxKind::NewExpression {
            let construction = node(parsed, id);
            assert_eq!(
                context.get_type_at_location(construction),
                Ok(members.shells().instance_type()),
            );
            assert_eq!(
                context
                    .store()
                    .signature_links(construction)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(signature),
            );
        }
    }
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(members.shells().instance_type())
    );
    members
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
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
        context.diagnostics().clone(),
        store.relation_state_snapshot(),
    )
}

#[test]
fn constructor_trailing_commas_keep_parameter_types_defaults_and_replay() {
    for defaulted in [false, true] {
        let parsed = parse_source_file(&source(defaulted, false));
        assert!(parsed.diagnostics.is_empty());
        let parts = parts(&parsed, defaulted);
        for query_first in [false, true] {
            let mut context = context(&parsed);
            let owner = symbol(&context, parts.class);
            let early = query_first.then(|| context.get_nongeneric_class_members(owner).unwrap());
            context.check_source_file(FILE).unwrap();
            let members = assert_checked(&mut context, &parsed, parts, defaulted);
            if let Some(early) = early {
                assert_eq!(early, members);
            }
            assert!(context.diagnostics().is_empty());
            let before = snapshot(&context, &parsed);
            for _ in 0..2 {
                context.recheck_source_file(FILE).unwrap();
                assert_eq!(
                    assert_checked(&mut context, &parsed, parts, defaulted),
                    members
                );
                assert_eq!(snapshot(&context, &parsed), before);
            }
        }
    }
}

#[test]
fn constructor_trailing_commas_keep_native_argument_and_arity_errors() {
    for defaulted in [false, true] {
        let parsed = parse_source_file(&source(defaulted, true));
        assert!(parsed.diagnostics.is_empty());
        let parts = parts(&parsed, defaulted);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let members = assert_checked(&mut context, &parsed, parts, defaulted);
        let wrong = initializer(&parsed, "wrongType");
        let NodeData::NewExpression(data) = &parsed.arena.get(wrong.node).unwrap().data else {
            unreachable!()
        };
        let wrong_argument = child(&parsed, wrong, data.arguments.as_ref().unwrap().nodes[0]);
        let missing = initializer(&parsed, "missing");
        let [argument, arity] = context.diagnostics().as_slice() else {
            panic!("expected only the wrong-type and missing-argument diagnostics")
        };
        assert_eq!(argument.diagnostic.code(), 2345);
        assert_eq!(argument.node, Some(wrong_argument));
        assert_eq!(argument.range_override, None);
        assert!(argument.related_information.is_empty());
        assert_eq!(
            argument.diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'.",
        );
        assert_eq!(arity.diagnostic.code(), 2554);
        assert_eq!(arity.node, Some(missing));
        assert_eq!(arity.range_override, None);
        assert_eq!(
            arity.diagnostic.render().unwrap(),
            if defaulted {
                "Expected 1-2 arguments, but got 0."
            } else {
                "Expected 2 arguments, but got 1."
            },
        );
        let [note] = arity.related_information.as_slice() else {
            panic!("the missing argument must name its actual parameter")
        };
        let missing_index = usize::from(!defaulted);
        assert_eq!(note.diagnostic.code(), 6210);
        assert_eq!(note.node, Some(parts.parameters[missing_index]));
        assert_eq!(
            note.diagnostic.render().unwrap(),
            if defaulted {
                "An argument for 'count' was not provided."
            } else {
                "An argument for 'label' was not provided."
            },
        );
        let before = snapshot(&context, &parsed);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                assert_checked(&mut context, &parsed, parts, defaulted),
                members
            );
            assert_eq!(snapshot(&context, &parsed), before);
        }
    }
}
