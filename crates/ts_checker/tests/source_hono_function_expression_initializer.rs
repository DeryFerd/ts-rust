use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(470_180);
const PROVIDER: FileId = FileId::new(470_181);

macro_rules! libraries {
    ($($name:literal),+ $(,)?) => {
        &[$((concat!("lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")))),+]
    };
}

const LIBRARIES: &[(&str, &str)] = libraries!(
    "es5",
    "es2015",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "decorators",
    "decorators.legacy",
);

const MIDDLEWARE: &str = concat!(
    "export interface Context {\n",
    "  username: string;\n",
    "  accept(username: string, valid: boolean): void;\n",
    "}\n",
    "export type Next = () => Promise<void>;\n",
    "export type MiddlewareHandler = (ctx: Context, next: Next) => Promise<void>;\n",
);

struct Fixture {
    libraries: Vec<ParseResult>,
    provider: ParseResult,
    source: ParseResult,
}

impl Fixture {
    fn new(invalid: bool) -> Self {
        let use_bindings = if invalid {
            "ctx.accept(valid, valid);\n        const wrong: string = valid;"
        } else {
            "ctx.accept(username, valid);"
        };
        let source = format!(
            "import type {{ MiddlewareHandler }} from './middleware';\n\
             declare function compare(user: string, realm: string): Promise<[string, boolean]>;\n\
             export const basicAuth = (realm: string, users: string[]): MiddlewareHandler => {{\n\
               return async function basicAuth(ctx, next) {{\n\
                 const requestUser = ctx.username;\n\
                 if (requestUser) {{\n\
                   for (const user of users) {{\n\
                     const [username, valid] = await compare(user, realm);\n\
                     {use_bindings}\n\
                     if (valid) {{\n\
                       await next();\n\
                       return;\n\
                     }}\n\
                   }}\n\
                 }}\n\
               }};\n\
             }};\n\
             const factory = basicAuth;\n"
        );
        Self {
            libraries: LIBRARIES
                .iter()
                .map(|(_, source)| parse_source_file(source))
                .collect(),
            provider: parse_source_file(MIDDLEWARE),
            source: parse_source_file(&source),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/lib/{}\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([
                (
                    PROVIDER,
                    &self.provider,
                    "\"/project/middleware.ts\"".to_owned(),
                    false,
                ),
                (
                    FILE,
                    &self.source,
                    "\"/project/function-expression-initializer.ts\"".to_owned(),
                    false,
                ),
            ])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        if *library {
                            CanonicalModuleState::Script
                        } else {
                            CanonicalModuleState::External
                        },
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        let import = only(&self.source, FILE, SyntaxKind::ImportDeclaration);
        let NodeData::ImportDeclaration(data) =
            &self.source.arena.get(import.node).unwrap().data
        else {
            unreachable!();
        };
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    exact_optional_property_types: false,
                },
                no_implicit_any: true,
                strict_function_types: true,
                strict_builtin_iterator_return: true,
                ..CanonicalCheckerOptions::default()
            },
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    node(&self.source, FILE, data.module_specifier),
                    CanonicalResolvedModuleInput::new(
                        PROVIDER,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ),
            ]),
        )
        .unwrap()
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn only(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, file, id)));
    let result = matches.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(matches.next().is_none(), "more than one {kind:?}");
    result
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        if record.kind != kind {
            return None;
        }
        let name_id = match &record.data {
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::ImportSpecifier(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name_id)?.data else {
            return None;
        };
        (identifier.text == name).then_some(node(parsed, file, id))
    });
    let result = matches.next().unwrap_or_else(|| panic!("missing {name}"));
    assert!(matches.next().is_none(), "more than one {name}");
    result
}

fn call(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef, Vec<NodeRef>) {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::CallExpression(data) = &record.data else {
            return None;
        };
        let callee = parsed.arena.get(data.expression)?;
        let name_id = match &callee.data {
            NodeData::Identifier(_) => data.expression,
            NodeData::PropertyAccessExpression(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name_id)?.data else {
            return None;
        };
        (identifier.text == name).then(|| {
            (
                node(parsed, FILE, id),
                node(parsed, FILE, data.expression),
                data.arguments
                    .nodes
                    .iter()
                    .map(|&id| node(parsed, FILE, id))
                    .collect(),
            )
        })
    });
    let result = matches.next().unwrap_or_else(|| panic!("missing {name} call"));
    assert!(matches.next().is_none(), "more than one {name} call");
    result
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

fn signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature");
    };
    *signature
}

fn reference_arguments(
    checker: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> (TypeId, Vec<TypeId>) {
    let TypeData::TypeReference(reference) = checker.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected a canonical type reference");
    };
    (
        reference.object.target.unwrap(),
        reference.resolved_type_arguments.clone().unwrap(),
    )
}

fn library_type(checker: &mut CanonicalCheckerContext<'_>, name: &str) -> TypeId {
    let store = checker.store();
    let globals = store.intrinsic_bootstrap().unwrap().globals;
    let raw = store.symbol_table(globals).unwrap().get_source(name).unwrap();
    let owner = store.get_merged_symbol(raw).unwrap();
    assert!(
        store
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap()
            .iter()
            .all(|node| node.file != FILE && node.file != PROVIDER)
    );
    checker.get_declared_type_of_symbol(owner).unwrap()
}

fn assert_diagnostic(
    checker: &CanonicalCheckerContext<'_>,
    code: u32,
    location: NodeRef,
    message: &str,
) {
    let matches = checker
        .diagnostics()
        .as_slice()
        .iter()
        .filter(|diagnostic| {
            diagnostic.diagnostic.code() == code && diagnostic.node == Some(location)
        })
        .collect::<Vec<_>>();
    let [diagnostic] = matches.as_slice() else {
        panic!("missing {code} at {location:?}: {:?}", checker.diagnostics());
    };
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
}

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    locations: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
    returns: &[(SignatureId, TypeId)],
) {
    let snapshot = |checker: &CanonicalCheckerContext<'_>| {
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
                store.type_resolution_len(),
            ],
            locations
                .iter()
                .map(|&(location, _)| {
                    (
                        store.node_links(location).cloned(),
                        store.type_node_links(location).cloned(),
                        store.symbol_node_links(location).cloned(),
                        store.signature_links(location).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            symbols
                .iter()
                .map(|&(_, symbol)| {
                    (
                        store.value_symbol_links(symbol).cloned(),
                        store.alias_symbol_links(symbol).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store
                .source_file_links(checker.source_file(FILE).unwrap())
                .cloned(),
            checker.diagnostics().clone(),
        )
    };
    let warm = snapshot(checker);
    assert!(warm.3.as_ref().unwrap().type_checked);
    for recheck in [false, true] {
        if recheck {
            checker.recheck_source_file(FILE).unwrap();
        } else {
            checker.check_source_file(FILE).unwrap();
        }
        for &(location, expected) in locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        for &(location, expected) in symbols {
            assert_eq!(checker.get_symbol_at_location(location), Ok(Some(expected)));
        }
        for &(signature, expected) in returns {
            assert_eq!(checker.get_return_type_of_signature(signature), Ok(expected));
        }
        assert_eq!(snapshot(checker), warm);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[allow(clippy::too_many_lines)] // Keep the source types, binding owners and replay in one control.
fn check_case(invalid: bool) {
    let fixture = Fixture::new(invalid);
    let parsed = &fixture.source;
    let function = only(parsed, FILE, SyntaxKind::FunctionExpression);
    let NodeData::FunctionExpression(inner) = &parsed.arena.get(function.node).unwrap().data else {
        unreachable!();
    };
    let function_name = node(parsed, FILE, inner.name.unwrap());
    let returned = node(
        parsed,
        FILE,
        parsed.arena.get(function.node).unwrap().parent.unwrap(),
    );
    let NodeData::ReturnStatement(returned_data) = &parsed.arena.get(returned.node).unwrap().data
    else {
        panic!("the measured function is returned, not a variable initializer");
    };
    assert_eq!(returned_data.expression, Some(function.node));
    let outer = only(parsed, FILE, SyntaxKind::ArrowFunction);
    let NodeData::ArrowFunction(outer_data) = &parsed.arena.get(outer.node).unwrap().data else {
        unreachable!();
    };
    let annotation = node(parsed, FILE, outer_data.type_.unwrap());
    let parameters = |ids: &[NodeId]| {
        ids.iter()
            .map(|&id| {
                let NodeData::ParameterDeclaration(data) = &parsed.arena.get(id).unwrap().data
                else {
                    unreachable!();
                };
                (node(parsed, FILE, id), node(parsed, FILE, data.name))
            })
            .collect::<Vec<_>>()
    };
    let inner_parameters = parameters(&inner.parameters.nodes);
    let outer_parameters = parameters(&outer_data.parameters.nodes);
    assert_eq!(inner_parameters.len(), 2);
    assert_eq!(outer_parameters.len(), 2);
    for &(declaration, _) in &inner_parameters {
        let NodeData::ParameterDeclaration(data) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        assert!(data.type_.is_none());
    }
    let pattern = only(parsed, FILE, SyntaxKind::ArrayBindingPattern);
    let NodeData::BindingPattern(data) = &parsed.arena.get(pattern.node).unwrap().data else {
        unreachable!();
    };
    let bindings = data
        .elements
        .nodes
        .iter()
        .map(|&id| {
            let record = parsed.arena.get(id).unwrap();
            assert_eq!(record.parent, Some(pattern.node));
            let NodeData::BindingElement(data) = &record.data else {
                unreachable!();
            };
            assert!(data.initializer.is_none());
            assert!(data.dot_dot_dot_token.is_none());
            assert!(data.property_name.is_none());
            (node(parsed, FILE, id), node(parsed, FILE, data.name.unwrap()))
        })
        .collect::<Vec<_>>();
    assert_eq!(bindings.len(), 2);
    for ((_, name), expected) in bindings.iter().zip(["username", "valid"]) {
        let NodeData::Identifier(data) = &parsed.arena.get(name.node).unwrap().data else {
            unreachable!();
        };
        assert_eq!(data.text, expected);
    }
    let iteration = only(parsed, FILE, SyntaxKind::ForOfStatement);
    let NodeData::ForInOrOfStatement(loop_) = &parsed.arena.get(iteration.node).unwrap().data else {
        unreachable!();
    };
    let loop_body = node(parsed, FILE, loop_.statement);
    let users_read = node(parsed, FILE, loop_.expression);
    let user = named(parsed, FILE, SyntaxKind::VariableDeclaration, "user");
    let (compare_call, compare_read, compare_arguments) = call(parsed, "compare");
    let awaited = node(
        parsed,
        FILE,
        parsed.arena.get(compare_call.node).unwrap().parent.unwrap(),
    );
    let NodeData::AwaitExpression(awaited_data) = &parsed.arena.get(awaited.node).unwrap().data
    else {
        panic!("the array initializer must await the real compare call");
    };
    assert_eq!(awaited_data.expression, compare_call.node);
    let array_declaration = node(
        parsed,
        FILE,
        parsed.arena.get(pattern.node).unwrap().parent.unwrap(),
    );
    let NodeData::VariableDeclaration(array_data) =
        &parsed.arena.get(array_declaration.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(array_data.initializer, Some(awaited.node));
    assert!(array_data.type_.is_none());
    let (accept_call, _, accept_arguments) = call(parsed, "accept");
    let (next_call, next_read, _) = call(parsed, "next");
    let next_await = node(
        parsed,
        FILE,
        parsed.arena.get(next_call.node).unwrap().parent.unwrap(),
    );
    let factory = named(parsed, FILE, SyntaxKind::VariableDeclaration, "factory");
    let NodeData::VariableDeclaration(factory_data) = &parsed.arena.get(factory.node).unwrap().data
    else {
        unreachable!();
    };
    let factory_read = node(parsed, FILE, factory_data.initializer.unwrap());

    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            checker.get_type_at_location(bindings[0].1).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        if invalid {
            assert_eq!(
                checker.diagnostics().as_slice().len(),
                2,
                "{:?}",
                checker.diagnostics()
            );
            assert_diagnostic(
                &checker,
                2345,
                accept_arguments[0],
                "Argument of type 'boolean' is not assignable to parameter of type 'string'.",
            );
            let wrong = named(parsed, FILE, SyntaxKind::VariableDeclaration, "wrong");
            let NodeData::VariableDeclaration(data) = &parsed.arena.get(wrong.node).unwrap().data
            else {
                unreachable!();
            };
            assert_diagnostic(
                &checker,
                2322,
                node(parsed, FILE, data.name),
                "Type 'boolean' is not assignable to type 'string'.",
            );
        } else {
            assert!(checker.diagnostics().is_empty(), "{:?}", checker.diagnostics());
        }
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let boolean = bootstrap.boolean_type;
        let void = bootstrap.void_type;
        let promise = library_type(&mut checker, "Promise");
        let array = library_type(&mut checker, "Array");
        let tuple_annotation = only(parsed, FILE, SyntaxKind::TupleType);
        let tuple = checker.get_type_from_type_node(tuple_annotation).unwrap();
        let (tuple_target, arguments) = reference_arguments(&checker, tuple);
        assert_eq!(arguments, [string, boolean]);
        assert!(matches!(
            checker.store().type_payload(tuple_target).unwrap().data(),
            TypeData::Tuple(_)
        ));
        let compare_type = checker.get_type_at_location(compare_read).unwrap();
        let compare_signature = signature(&checker, compare_type);
        let compare_return = checker.get_return_type_of_signature(compare_signature).unwrap();
        assert_eq!(
            reference_arguments(&checker, compare_return),
            (promise, vec![tuple])
        );
        let actual = checker.get_type_at_location(function).unwrap();
        let inner_signature = signature(&checker, actual);
        let inner_return = checker.get_return_type_of_signature(inner_signature).unwrap();
        assert_eq!(
            reference_arguments(&checker, inner_return),
            (promise, vec![void])
        );
        let target = checker.get_type_from_type_node(annotation).unwrap();
        let target_signature = signature(&checker, target);
        assert_eq!(
            checker.get_return_type_of_signature(target_signature),
            Ok(inner_return)
        );
        let outer_type = checker.get_type_at_location(outer).unwrap();
        let outer_signature = signature(&checker, outer_type);
        assert_eq!(
            checker.get_return_type_of_signature(outer_signature),
            Ok(target)
        );
        let context_owner = symbol(
            &checker,
            named(&fixture.provider, PROVIDER, SyntaxKind::InterfaceDeclaration, "Context"),
        );
        let context = checker.get_declared_type_of_symbol(context_owner).unwrap();
        let next_owner = symbol(
            &checker,
            named(&fixture.provider, PROVIDER, SyntaxKind::TypeAliasDeclaration, "Next"),
        );
        let next = checker.get_declared_type_of_symbol(next_owner).unwrap();
        let self_owner = symbol(&checker, function);
        let factory_owner = symbol(
            &checker,
            named(parsed, FILE, SyntaxKind::VariableDeclaration, "basicAuth"),
        );
        assert_ne!(self_owner, factory_owner);
        assert_eq!(
            checker.store().signature(inner_signature).unwrap().declaration(),
            Some(function)
        );
        assert_eq!(
            checker.store().symbol(self_owner).unwrap().declarations(),
            Some(&[function][..])
        );
        let parameter_owners = inner_parameters
            .iter()
            .map(|&(declaration, _)| symbol(&checker, declaration))
            .collect::<Vec<_>>();
        assert_eq!(
            checker.store().signature(inner_signature).unwrap().parameters(),
            parameter_owners
        );
        for (index, &owner) in parameter_owners.iter().enumerate() {
            assert_ne!(
                owner,
                checker.store().signature(target_signature).unwrap().parameters()[index]
            );
        }
        let alias = symbol(
            &checker,
            named(parsed, FILE, SyntaxKind::ImportSpecifier, "MiddlewareHandler"),
        );
        let handler = symbol(
            &checker,
            named(
                &fixture.provider,
                PROVIDER,
                SyntaxKind::TypeAliasDeclaration,
                "MiddlewareHandler",
            ),
        );
        assert_ne!(alias, handler);
        assert_eq!(checker.get_declared_type_of_symbol(handler), Ok(target));
        let alias_links = checker.store().alias_symbol_links(alias).cloned();
        assert_eq!(
            alias_links.as_ref().unwrap().alias_target,
            AliasTargetState::Resolved(handler)
        );
        let bound = checker.file(FILE).unwrap().1;
        assert_eq!(bound.container(function), Some(outer));
        assert_eq!(bound.flow_graph().container_is_complete(function), Some(true));
        assert_eq!(bound.container(array_declaration), Some(function));
        assert_eq!(bound.block_scope_container(array_declaration), Some(loop_body));
        assert_eq!(bound.container(compare_arguments[1]), Some(function));
        for &(declaration, name) in &bindings {
            assert_eq!(bound.container(declaration), Some(function));
            assert_eq!(bound.block_scope_container(declaration), Some(loop_body));
            assert_eq!(bound.block_scope_container(name), Some(loop_body));
        }
        let mut locations = vec![
            (function, actual),
            (outer, outer_type),
            (inner_parameters[0].1, context),
            (inner_parameters[1].1, next),
            (bindings[0].1, string),
            (bindings[1].1, boolean),
            (awaited, tuple),
            (compare_call, compare_return),
            (compare_arguments[0], string),
            (compare_arguments[1], string),
            (accept_call, void),
            (accept_arguments[0], if invalid { boolean } else { string }),
            (accept_arguments[1], boolean),
            (next_call, inner_return),
            (next_await, void),
            (factory_read, outer_type),
        ];
        let users_type = checker.get_type_at_location(outer_parameters[1].1).unwrap();
        assert_eq!(reference_arguments(&checker, users_type), (array, vec![string]));
        locations.extend([(users_read, users_type), (outer_parameters[0].1, string)]);
        if invalid {
            let wrong = named(parsed, FILE, SyntaxKind::VariableDeclaration, "wrong");
            let NodeData::VariableDeclaration(data) = &parsed.arena.get(wrong.node).unwrap().data
            else {
                unreachable!();
            };
            locations.push((node(parsed, FILE, data.name), string));
            locations.push((node(parsed, FILE, data.initializer.unwrap()), boolean));
        }
        let mut symbols = vec![
            (function_name, self_owner),
            (factory_read, factory_owner),
            (inner_parameters[0].1, parameter_owners[0]),
            (inner_parameters[1].1, parameter_owners[1]),
            (next_read, parameter_owners[1]),
            (users_read, symbol(&checker, outer_parameters[1].0)),
            (compare_arguments[0], symbol(&checker, user)),
            (compare_arguments[1], symbol(&checker, outer_parameters[0].0)),
        ];
        for (index, &(declaration, name)) in bindings.iter().enumerate() {
            let owner = symbol(&checker, declaration);
            assert_eq!(
                checker.store().symbol(owner).unwrap().declarations(),
                Some(&[declaration][..])
            );
            assert_eq!(
                checker.store().value_symbol_links(owner).unwrap().resolved_type,
                Some([string, boolean][index])
            );
            symbols.push((name, owner));
        }
        assert_ne!(symbol(&checker, bindings[0].0), symbol(&checker, bindings[1].0));
        symbols.push((
            accept_arguments[0],
            symbol(&checker, bindings[usize::from(invalid)].0),
        ));
        symbols.push((accept_arguments[1], symbol(&checker, bindings[1].0)));
        for &(location, expected) in &locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        for &(location, expected) in &symbols {
            assert_eq!(checker.get_symbol_at_location(location), Ok(Some(expected)));
        }
        replay(
            &mut checker,
            &locations,
            &symbols,
            &[
                (inner_signature, inner_return),
                (outer_signature, target),
                (target_signature, inner_return),
                (compare_signature, compare_return),
            ],
        );
        assert_eq!(checker.store().alias_symbol_links(alias), alias_links.as_ref());
    }
}

#[test]
fn returned_async_nested_array_binding_keeps_context_captures_and_tuple_types() {
    check_case(false);
}

#[test]
fn returned_async_nested_array_binding_keeps_native_argument_and_assignment_errors() {
    check_case(true);
}
