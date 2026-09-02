use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_161);
const SOURCE: &str = concat!(
    "type ManagedTimerId = number;\n",
    "export abstract class Removable {\n",
    "  gcTime!: number;\n",
    "  #gcTimeout?: ManagedTimerId;\n",
    "  protected abstract policy: number;\n",
    "  destroy(): void { this.clearGcTimeout(); }\n",
    "  protected scheduleGc(): void {\n",
    "    this.#gcTimeout = this.gcTime;\n",
    "    this.optionalRemove();\n",
    "  }\n",
    "  protected clearGcTimeout() {\n",
    "    const before = this.#gcTimeout;\n",
    "    if (this.#gcTimeout !== undefined) {\n",
    "      const timer: number = this.#gcTimeout;\n",
    "      this.#gcTimeout = undefined;\n",
    "      const cleared = this.#gcTimeout;\n",
    "    }\n",
    "  }\n",
    "  protected abstract optionalRemove(): void;\n",
    "}\n",
);

fn context(parsed: &ParseResult, module: CanonicalModuleState) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/abstract-removable.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                module,
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
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn class(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::ClassDeclaration).then_some(reference(parsed, node))
        })
        .unwrap()
}

fn member(parsed: &ParseResult, expected: &str) -> NodeRef {
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(class(parsed).node).unwrap().data
    else {
        unreachable!()
    };
    class
        .members
        .nodes
        .iter()
        .find_map(|&node| {
            let name = match &parsed.arena.get(node)?.data {
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::MethodDeclaration(method) => method.name,
                _ => return None,
            };
            let text = match &parsed.arena.get(name)?.data {
                NodeData::Identifier(name) => &name.text,
                NodeData::PrivateIdentifier(name) => &name.text,
                _ => return None,
            };
            (text == expected).then_some(reference(parsed, node))
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| reference(parsed, variable.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing initializer {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let bound = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(bound).unwrap()
}

fn checked_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn snapshot(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> String {
    let store = context.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| {
            let node = reference(parsed, node);
            (
                store.type_node_links(node),
                store.symbol_node_links(node),
                store.signature_links(node),
            )
        })
        .collect::<Vec<_>>();
    format!(
        "{:?}",
        (
            [
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
            ],
            nodes,
            store.source_file_links(context.source_file(FILE).unwrap()),
            context.diagnostics(),
        ),
    )
}

fn replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let before = snapshot(context, parsed);
    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(snapshot(context, parsed), before);
}

#[test]
fn visibility_modifiers_preserve_abstract_member_types_and_calls() {
    for visibility in ["public", "protected"] {
        let source = format!(
            "export abstract class Base {{\n\
               {visibility} abstract value: number;\n\
               {visibility} abstract read(): number;\n\
               run(): number {{ const value: number = this.value; return this.read(); }}\n\
             }}\n",
        );
        for members_first in [false, true] {
            let parsed = parse_source_file(&source);
            let mut context = context(&parsed, CanonicalModuleState::External);
            let owner = symbol(&context, class(&parsed));
            let early = members_first.then(|| context.get_nongeneric_class_members(owner).unwrap());
            context.check_source_file(FILE).unwrap();
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let members = context.get_nongeneric_class_members(owner).unwrap();
            if let Some(early) = early {
                assert_eq!(members, early);
            }
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let field = symbol(&context, member(&parsed, "value"));
            let value = initializer(&parsed, "value");
            assert_eq!(context.store().symbol(field).unwrap().parent(), Some(owner));
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(field)
                    .unwrap()
                    .resolved_type,
                Some(number),
            );
            assert_eq!(checked_type(&context, value), number);
            assert_eq!(context.get_type_at_location(value).unwrap(), number);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(value)
                    .unwrap()
                    .resolved_symbol,
                Some(field),
            );
            let method = symbol(&context, member(&parsed, "read"));
            for (node, record) in parsed.arena.iter() {
                let NodeData::CallExpression(call) = &record.data else {
                    continue;
                };
                assert_eq!(checked_type(&context, reference(&parsed, node)), number);
                assert_eq!(
                    context
                        .store()
                        .symbol_node_links(reference(&parsed, call.expression))
                        .unwrap()
                        .resolved_symbol,
                    Some(method),
                );
            }
            replay(&mut context, &parsed);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both query orders retain the same class and member identities.
fn abstract_private_alias_fields_keep_narrowing_and_protected_method_identity() {
    for members_first in [false, true] {
        let parsed = parse_source_file(SOURCE);
        let mut context = context(&parsed, CanonicalModuleState::External);
        let owner = symbol(&context, class(&parsed));
        let early = members_first.then(|| context.get_nongeneric_class_members(owner).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let members = context.get_nongeneric_class_members(owner).unwrap();
        if let Some(early) = early {
            assert_eq!(early, members);
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let timer = symbol(&context, member(&parsed, "#gcTimeout"));
        for name in ["gcTime", "#gcTimeout", "policy"] {
            let declaration = member(&parsed, name);
            let field = symbol(&context, declaration);
            let record = context.store().symbol(field).unwrap();
            assert_eq!(record.parent(), Some(owner));
            assert_eq!(record.declarations(), Some(&[declaration][..]));
            assert_eq!(record.value_declaration(), Some(declaration));
            assert_eq!(record.name().is_private_identifier(), name.starts_with('#'));
            assert_eq!(
                record.flags().contains(SymbolFlags::OPTIONAL),
                name == "#gcTimeout"
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(field)
                    .unwrap()
                    .resolved_type,
                Some(number),
            );
        }
        for (name, expected) in [
            ("before", "number | undefined"),
            ("timer", "number"),
            ("cleared", "undefined"),
        ] {
            let node = initializer(&parsed, name);
            let type_ = checked_type(&context, node);
            assert_eq!(context.type_to_string(type_).unwrap(), expected, "{name}");
            assert_eq!(context.get_type_at_location(node).unwrap(), type_);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .unwrap()
                    .resolved_symbol,
                Some(timer),
            );
        }
        let abstract_method = member(&parsed, "optionalRemove");
        let abstract_symbol = symbol(&context, abstract_method);
        let NodeData::MethodDeclaration(method) =
            &parsed.arena.get(abstract_method.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(method.body.is_none());
        let abstract_signature = context
            .store()
            .signature_links(abstract_method)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let void = context.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            context
                .store()
                .signature(abstract_signature)
                .unwrap()
                .resolved_return_type(),
            Some(void),
        );
        for (node, record) in parsed.arena.iter() {
            let NodeData::CallExpression(call) = &record.data else {
                continue;
            };
            let NodeData::PropertyAccessExpression(access) =
                &parsed.arena.get(call.expression).unwrap().data
            else {
                panic!("the class must call its own methods")
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name).unwrap().data else {
                unreachable!()
            };
            let expected = if name.text == "optionalRemove" {
                abstract_symbol
            } else {
                symbol(&context, member(&parsed, "clearGcTimeout"))
            };
            assert_eq!(checked_type(&context, reference(&parsed, node)), void);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(reference(&parsed, call.expression))
                    .unwrap()
                    .resolved_symbol,
                Some(expected),
            );
        }
        replay(&mut context, &parsed);
    }
}

#[test]
fn abstract_private_alias_classes_keep_write_access_and_construction_errors() {
    let source = format!(
        "{SOURCE}{}",
        concat!(
            "const forbidden = new Removable();\n",
            "declare const removable: Removable;\n",
            "const denied = removable.optionalRemove;\n",
            "removable.gcTime = 'bad';\n",
        ),
    );
    let parsed = parse_source_file(&source);
    let mut context = context(&parsed, CanonicalModuleState::External);
    context.check_source_file(FILE).unwrap();
    let denied = initializer(&parsed, "denied");
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(denied.node).unwrap().data
    else {
        unreachable!()
    };
    let assignment = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::BinaryExpression(binary) = &record.data else {
                return None;
            };
            let right = parsed.arena.get(binary.right)?;
            (right.kind == SyntaxKind::StringLiteral).then_some(reference(&parsed, binary.left))
        })
        .unwrap();
    let expected = [
        (
            initializer(&parsed, "forbidden"),
            2511,
            vec![],
            "Cannot create an instance of an abstract class.",
        ),
        (
            reference(&parsed, access.name),
            2445,
            vec!["optionalRemove", "Removable"],
            "Property 'optionalRemove' is protected and only accessible within class 'Removable' and its subclasses.",
        ),
        (
            assignment,
            2322,
            vec!["string", "number"],
            "Type 'string' is not assignable to type 'number'.",
        ),
    ];
    assert_eq!(
        context.diagnostics().len(),
        expected.len(),
        "{:?}",
        context.diagnostics()
    );
    for (diagnostic, (node, code, arguments, message)) in
        context.diagnostics().as_slice().iter().zip(expected)
    {
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
        assert!(diagnostic.range_override.is_none());
    }
    let method = symbol(&context, member(&parsed, "optionalRemove"));
    assert_eq!(
        context
            .store()
            .symbol_node_links(denied)
            .unwrap()
            .resolved_symbol,
        Some(method),
    );
    replay(&mut context, &parsed);
}

#[test]
fn protected_abstract_method_bodies_keep_the_native_implementation_error() {
    let parsed = parse_source_file(concat!(
        "abstract class Invalid {\n",
        "  protected abstract optionalRemove() {}\n",
        "}\n",
    ));
    let mut context = context(&parsed, CanonicalModuleState::Script);
    context.check_source_file(FILE).unwrap();
    let method = member(&parsed, "optionalRemove");
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(method.node).unwrap().data else {
        unreachable!()
    };
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.node, Some(reference(&parsed, method.name)));
    assert_eq!(diagnostic.diagnostic.code(), 1245);
    assert_eq!(diagnostic.diagnostic.arguments, ["optionalRemove"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Method 'optionalRemove' cannot have an implementation because it is marked abstract.",
    );
    assert!(diagnostic.related_information.is_empty());
    assert!(diagnostic.range_override.is_none());
    replay(&mut context, &parsed);
}
