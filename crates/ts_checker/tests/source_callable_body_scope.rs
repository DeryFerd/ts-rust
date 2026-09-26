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

const FILE: FileId = FileId::new(300_450);
const PROVIDER: FileId = FileId::new(300_451);

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
    "dom",
);

const MIDDLEWARE: &str = concat!(
    "export interface Context { res: Response; }\n",
    "export type Next = () => Promise<void>;\n",
    "export type MiddlewareHandler<R = Response> = ",
    "(c: Context, next: Next) => Promise<R | void>;\n",
);

struct Fixture {
    libraries: Vec<ParseResult>,
    provider: ParseResult,
    source: ParseResult,
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            libraries: LIBRARIES
                .iter()
                .map(|(_, source)| parse_source_file(source))
                .collect(),
            provider: parse_source_file(MIDDLEWARE),
            source: parse_source_file(source),
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
                    "\"/project/body-scope.ts\"".to_owned(),
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
        let resolutions = self.source.arena.iter().filter_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            Some(CanonicalModuleResolutionEntry::resolved(
                node(&self.source, FILE, import.module_specifier),
                CanonicalResolvedModuleInput::new(
                    PROVIDER,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ))
        });
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
            CanonicalModuleResolutionManifestInput::new(resolutions),
        )
        .unwrap()
    }
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        if record.kind != kind {
            return None;
        }
        let name_id = match &record.data {
            NodeData::VariableDeclaration(data) => data.name,
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::FunctionExpression(data) => data.name?,
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
        panic!("expected a callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature")
    };
    *signature
}

fn global_type(checker: &mut CanonicalCheckerContext<'_>, name: &str) -> TypeId {
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

fn assert_reference(
    checker: &CanonicalCheckerContext<'_>,
    actual: TypeId,
    target: TypeId,
    argument: TypeId,
) {
    let TypeData::TypeReference(reference) = checker.store().type_payload(actual).unwrap().data()
    else {
        panic!("expected a canonical generic reference")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );
}

fn variable(parsed: &ParseResult, name: &str) -> (NodeRef, NodeRef, Option<NodeRef>, NodeRef) {
    let declaration = named(parsed, FILE, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    (
        declaration,
        node(parsed, FILE, data.name),
        data.type_.map(|id| node(parsed, FILE, id)),
        node(parsed, FILE, data.initializer.unwrap()),
    )
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

fn replay(
    checker: &mut CanonicalCheckerContext<'_>,
    locations: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
    signatures: &[(SignatureId, TypeId)],
) {
    let links = |checker: &CanonicalCheckerContext<'_>| {
        locations
            .iter()
            .map(|&(location, _)| {
                (
                    checker.store().type_node_links(location).cloned(),
                    checker.store().symbol_node_links(location).cloned(),
                    checker.store().signature_links(location).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let values = |checker: &CanonicalCheckerContext<'_>| {
        symbols
            .iter()
            .map(|&(_, symbol)| {
                (
                    checker.store().value_symbol_links(symbol).cloned(),
                    checker.store().alias_symbol_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let warm = (counts(checker), links(checker), values(checker));
    let diagnostics = checker.diagnostics().clone();
    let source = checker.source_file(FILE).unwrap();
    let source_links = checker.store().source_file_links(source).cloned();
    assert!(source_links.as_ref().unwrap().type_checked);
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
        for &(signature, expected) in signatures {
            assert_eq!(checker.get_return_type_of_signature(signature), Ok(expected));
        }
        assert_eq!((counts(checker), links(checker), values(checker)), warm);
        assert_eq!(
            checker.store().source_file_links(source),
            source_links.as_ref()
        );
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert!(checker.store().type_resolution_is_empty());
    }
}

fn assert_diagnostic(checker: &CanonicalCheckerContext<'_>, code: u32, location: NodeRef) {
    let matches = checker
        .diagnostics()
        .as_slice()
        .iter()
        .filter(|diagnostic| {
            diagnostic.diagnostic.code() == code && diagnostic.node == Some(location)
        })
        .collect::<Vec<_>>();
    let [diagnostic] = matches.as_slice() else {
        panic!(
            "missing diagnostic {code} at {location:?}: {:?}",
            checker.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
}

#[test]
#[allow(clippy::too_many_lines)] // Keep context, body, owners, and replay in one control.
fn returned_named_async_body_keeps_imported_context_and_captures() {
    for declaration in [
        "export const poweredBy = (options?: PoweredByOptions): MiddlewareHandler =>",
        "export function poweredBy(options?: PoweredByOptions): MiddlewareHandler",
    ] {
        let fixture = Fixture::new(&format!(
            "import type {{ MiddlewareHandler }} from './middleware';\n\
             type PoweredByOptions = {{ serverName?: string }};\n\
             {declaration} {{\n\
               return async function poweredBy(c, next) {{\n\
                 await next();\n\
                 c.res.headers.set('X-Powered-By', options?.serverName ?? 'Hono');\n\
               }};\n\
             }};\n\
             const factory = poweredBy;\n"
        ));
        let parsed = &fixture.source;
        let function = named(parsed, FILE, SyntaxKind::FunctionExpression, "poweredBy");
        let NodeData::FunctionExpression(data) = &parsed.arena.get(function.node).unwrap().data
        else {
            unreachable!()
        };
        let name = node(parsed, FILE, data.name.unwrap());
        let parameters = data
            .parameters
            .nodes
            .iter()
            .map(|&id| {
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(id).unwrap().data
                else {
                    unreachable!()
                };
                assert!(parameter.type_.is_none());
                (node(parsed, FILE, id), node(parsed, FILE, parameter.name))
            })
            .collect::<Vec<_>>();
        assert_eq!(parameters.len(), 2);
        let returned = parsed.arena.get(function.node).unwrap().parent.unwrap();
        let block = parsed.arena.get(returned).unwrap().parent.unwrap();
        let owner = node(
            parsed,
            FILE,
            parsed.arena.get(block).unwrap().parent.unwrap(),
        );
        let factory_declaration = if parsed.arena.get(owner.node).unwrap().kind
            == SyntaxKind::ArrowFunction
        {
            node(parsed, FILE, parsed.arena.get(owner.node).unwrap().parent.unwrap())
        } else {
            owner
        };
        let (annotation, option) = match &parsed.arena.get(owner.node).unwrap().data {
            NodeData::ArrowFunction(outer) => (outer.type_.unwrap(), outer.parameters.nodes[0]),
            NodeData::FunctionDeclaration(outer) => {
                (outer.type_.unwrap(), outer.parameters.nodes[0])
            }
            _ => panic!("expected the enclosing source callable"),
        };
        let NodeData::ParameterDeclaration(option_data) = &parsed.arena.get(option).unwrap().data
        else {
            unreachable!()
        };
        let option_name = node(parsed, FILE, option_data.name);
        let NodeData::Block(body) = &parsed.arena.get(data.body).unwrap().data else {
            unreachable!()
        };
        let expressions = body
            .statements
            .nodes
            .iter()
            .map(|&id| {
                let NodeData::ExpressionStatement(statement) = &parsed.arena.get(id).unwrap().data
                else {
                    panic!("expected both original expression statements")
                };
                node(parsed, FILE, statement.expression)
            })
            .collect::<Vec<_>>();
        let [awaited, header_call] = expressions.as_slice() else {
            panic!("expected the await and following header call")
        };
        let NodeData::AwaitExpression(await_data) = &parsed.arena.get(awaited.node).unwrap().data
        else {
            unreachable!()
        };
        let next_call = node(parsed, FILE, await_data.expression);
        let NodeData::CallExpression(next_data) = &parsed.arena.get(next_call.node).unwrap().data
        else {
            unreachable!()
        };
        let next_read = node(parsed, FILE, next_data.expression);
        let NodeData::CallExpression(header_data) =
            &parsed.arena.get(header_call.node).unwrap().data
        else {
            unreachable!()
        };
        let label = node(parsed, FILE, header_data.arguments.nodes[1]);
        let NodeData::BinaryExpression(fallback) = &parsed.arena.get(label.node).unwrap().data
        else {
            unreachable!()
        };
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(fallback.left).unwrap().data
        else {
            unreachable!()
        };
        let option_read = node(parsed, FILE, property.expression);
        let (_, factory_name, _, factory_read) = variable(parsed, "factory");
        for query_first in [false, true] {
            let mut checker = fixture.context();
            if query_first {
                checker.get_type_at_location(function).unwrap();
            }
            checker.check_source_file(FILE).unwrap();
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
            let actual = checker.get_type_at_location(function).unwrap();
            let inner_signature = signature(&checker, actual);
            let target = checker
                .get_type_from_type_node(node(parsed, FILE, annotation))
                .unwrap();
            let target_signature = signature(&checker, target);
            let context_owner = symbol(
                &checker,
                named(
                    &fixture.provider,
                    PROVIDER,
                    SyntaxKind::InterfaceDeclaration,
                    "Context",
                ),
            );
            let context = checker.get_declared_type_of_symbol(context_owner).unwrap();
            let next_owner = symbol(
                &checker,
                named(
                    &fixture.provider,
                    PROVIDER,
                    SyntaxKind::TypeAliasDeclaration,
                    "Next",
                ),
            );
            let next = checker.get_declared_type_of_symbol(next_owner).unwrap();
            let expected_parameters = [context, next];
            let parameter_symbols = parameters
                .iter()
                .map(|&(declaration, _)| symbol(&checker, declaration))
                .collect::<Vec<_>>();
            let inner = checker.store().signature(inner_signature).unwrap();
            assert_eq!(inner.declaration(), Some(function));
            assert_eq!(inner.parameters(), parameter_symbols);
            for (index, &(parameter, name)) in parameters.iter().enumerate() {
                assert_eq!(
                    checker.get_type_at_location(name),
                    Ok(expected_parameters[index])
                );
                assert_eq!(
                    checker.get_symbol_at_location(name),
                    Ok(Some(symbol(&checker, parameter)))
                );
                assert_ne!(
                    parameter_symbols[index],
                    checker.store().signature(target_signature).unwrap().parameters()[index],
                );
            }
            let inner_owner = symbol(&checker, function);
            let factory_owner = checker
                .get_symbol_at_location(factory_read)
                .unwrap()
                .unwrap();
            assert_eq!(factory_owner, symbol(&checker, factory_declaration));
            assert_ne!(inner_owner, factory_owner);
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(inner_owner)));
            let inner = checker.store().symbol(inner_owner).unwrap();
            assert_eq!(inner.name().as_utf8(), Some("poweredBy"));
            assert_eq!(inner.declarations(), Some(&[function][..]));
            assert_eq!(checker.file(FILE).unwrap().1.container(next_call), Some(function));
            assert_eq!(checker.file(FILE).unwrap().1.container(option_read), Some(function));
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
            assert_eq!(
                checker.store().alias_symbol_links(alias).unwrap().alias_target,
                AliasTargetState::Resolved(handler)
            );
            let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let promise = global_type(&mut checker, "Promise");
            let response = global_type(&mut checker, "Response");
            let returned = checker
                .get_return_type_of_signature(inner_signature)
                .unwrap();
            assert_reference(&checker, returned, promise, void);
            let next_signature = signature(&checker, next);
            assert_eq!(checker.get_return_type_of_signature(next_signature), Ok(returned));
            let context_return = checker
                .get_return_type_of_signature(target_signature)
                .unwrap();
            let TypeData::TypeReference(reference) =
                checker.store().type_payload(context_return).unwrap().data()
            else {
                panic!("the imported handler must return its real Promise")
            };
            assert_eq!(reference.object.target, Some(promise));
            let [result] = reference.resolved_type_arguments.as_deref().unwrap() else {
                panic!("expected the default Response or void result")
            };
            let TypeData::Union(union) = checker.store().type_payload(*result).unwrap().data()
            else {
                panic!("the handler default must retain Response and void")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&response));
            assert!(union.union.types.contains(&void));
            let outer_type = checker.get_type_at_location(owner).unwrap();
            let outer_signature = signature(&checker, outer_type);
            assert_eq!(
                checker.get_return_type_of_signature(outer_signature),
                Ok(target)
            );
            let option_type = checker.get_type_at_location(option_name).unwrap();
            let locations = [
                (function, actual),
                (owner, outer_type),
                (factory_name, outer_type),
                (parameters[0].1, context),
                (parameters[1].1, next),
                (next_call, returned),
                (*awaited, void),
                (*header_call, void),
                (label, string),
                (option_name, option_type),
                (option_read, option_type),
            ];
            let symbols = [
                (name, inner_owner),
                (factory_read, factory_owner),
                (parameters[0].1, parameter_symbols[0]),
                (parameters[1].1, parameter_symbols[1]),
                (next_read, parameter_symbols[1]),
                (option_read, symbol(&checker, node(parsed, FILE, option))),
            ];
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
                    (inner_signature, returned),
                    (outer_signature, target),
                    (target_signature, context_return),
                    (next_signature, returned),
                ],
            );
        }
    }
}

#[test]
fn returned_async_body_keeps_native_argument_return_and_name_errors() {
    let fixture = Fixture::new(concat!(
        "import type { MiddlewareHandler } from './middleware';\n",
        "export const make = (): MiddlewareHandler => {\n",
        "  return async function middleware(c, next) {\n",
        "    await next();\n",
        "    c.res.headers.set('X-Powered-By', 1);\n",
        "    return 2;\n",
        "  };\n",
        "};\n",
        "const escaped = middleware;\n",
    ));
    let parsed = &fixture.source;
    let function = named(parsed, FILE, SyntaxKind::FunctionExpression, "middleware");
    let returned = node(
        parsed,
        FILE,
        parsed.arena.get(function.node).unwrap().parent.unwrap(),
    );
    let (_, _, _, missing) = variable(parsed, "escaped");
    let argument = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            (call.arguments.nodes.len() == 2).then(|| node(parsed, FILE, call.arguments.nodes[1]))
        })
        .unwrap();
    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            checker.get_type_at_location(function).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert_eq!(
            checker.diagnostics().as_slice().len(),
            3,
            "{:?}",
            checker.diagnostics()
        );
        assert_diagnostic(&checker, 2345, argument);
        assert_diagnostic(&checker, 2322, returned);
        assert_diagnostic(&checker, 2304, missing);
        let missing_error = checker
            .diagnostics()
            .as_slice()
            .iter()
            .find(|diagnostic| diagnostic.diagnostic.code() == 2304)
            .unwrap();
        assert_eq!(missing_error.diagnostic.arguments, ["middleware"]);
        let argument_error = checker
            .diagnostics()
            .as_slice()
            .iter()
            .find(|diagnostic| diagnostic.diagnostic.code() == 2345)
            .unwrap();
        assert_eq!(
            argument_error.diagnostic.render().unwrap(),
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        let actual = checker.get_type_at_location(function).unwrap();
        let signature = signature(&checker, actual);
        let returned = checker.get_return_type_of_signature(signature).unwrap();
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let promise = global_type(&mut checker, "Promise");
        assert_reference(&checker, returned, promise, number);
        replay(
            &mut checker,
            &[(function, actual)],
            &[],
            &[(signature, returned)],
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the generic body and its call substitutions together.
fn generic_local_new_keeps_array_parameter_set_result_and_argument_error() {
    let fixture = Fixture::new(concat!(
        "export function collect<T>(array1: Array<T>, array2: Array<T>): Set<T> {\n",
        "  const excludeSet = new Set(array2);\n",
        "  return excludeSet;\n",
        "}\n",
        "declare const numbers: Array<number>;\n",
        "declare const strings: Array<string>;\n",
        "const actual: Set<number> = collect<number>(numbers, numbers);\n",
        "const invalid = collect<number>(numbers, strings);\n",
    ));
    let parsed = &fixture.source;
    let function = named(parsed, FILE, SyntaxKind::FunctionDeclaration, "collect");
    let NodeData::FunctionDeclaration(data) = &parsed.arena.get(function.node).unwrap().data
    else {
        unreachable!()
    };
    let array2 = node(parsed, FILE, data.parameters.nodes[1]);
    let type_parameter = node(parsed, FILE, data.type_parameters.as_ref().unwrap().nodes[0]);
    let (_, local_name, _, construction) = variable(parsed, "excludeSet");
    let NodeData::NewExpression(new) = &parsed.arena.get(construction.node).unwrap().data else {
        unreachable!()
    };
    let argument = node(parsed, FILE, new.arguments.as_ref().unwrap().nodes[0]);
    let constructor = node(parsed, FILE, new.expression);
    let (_, actual_name, annotation, call) = variable(parsed, "actual");
    let (_, invalid_name, _, bad_call) = variable(parsed, "invalid");
    let NodeData::CallExpression(bad) = &parsed.arena.get(bad_call.node).unwrap().data else {
        unreachable!()
    };
    let bad_argument = node(parsed, FILE, bad.arguments.nodes[1]);
    for query_first in [false, true] {
        let mut checker = fixture.context();
        if query_first {
            checker.get_type_at_location(construction).unwrap();
        }
        checker.check_source_file(FILE).unwrap();
        assert_eq!(
            checker.diagnostics().as_slice().len(),
            1,
            "{:?}",
            checker.diagnostics()
        );
        assert_diagnostic(&checker, 2345, bad_argument);
        let function_type = checker.get_type_at_location(function).unwrap();
        let function_signature = signature(&checker, function_type);
        let parameters = checker
            .store()
            .signature(function_signature)
            .unwrap()
            .type_parameters();
        let [parameter] = parameters else {
            panic!("the function must retain its own type parameter")
        };
        let parameter = *parameter;
        assert!(matches!(
            checker.store().type_payload(parameter).unwrap().data(),
            TypeData::TypeParameter(_)
        ));
        assert_eq!(
            checker.store().type_payload(parameter).unwrap().symbol(),
            Some(symbol(&checker, type_parameter))
        );
        let result = checker.get_type_at_location(construction).unwrap();
        let set = global_type(&mut checker, "Set");
        assert_reference(&checker, result, set, parameter);
        let array = checker.get_type_at_location(argument).unwrap();
        assert_reference(&checker, array, checker.global_types().array_type, parameter);
        let array2_owner = symbol(&checker, array2);
        assert_eq!(
            checker.get_symbol_at_location(argument),
            Ok(Some(array2_owner))
        );
        assert_eq!(
            checker.store().signature(function_signature).unwrap().parameters()[1],
            array2_owner
        );
        assert_eq!(
            checker.get_return_type_of_signature(function_signature),
            Ok(result)
        );
        let constructed = checker
            .store()
            .signature_links(construction)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(checker.get_return_type_of_signature(constructed), Ok(result));
        assert!(
            checker
                .store()
                .signature(constructed)
                .unwrap()
                .declaration()
                .is_some_and(|declaration| declaration.file != FILE && declaration.file != PROVIDER)
        );
        let constructor_owner = checker
            .get_symbol_at_location(constructor)
            .unwrap()
            .unwrap();
        assert_eq!(
            checker.store().type_payload(set).unwrap().symbol(),
            Some(constructor_owner)
        );
        let expected = checker
            .get_type_from_type_node(annotation.unwrap())
            .unwrap();
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        let bad_array = checker.get_type_at_location(bad_argument).unwrap();
        assert_reference(&checker, expected, set, number);
        assert_reference(&checker, bad_array, checker.global_types().array_type, string);
        let locations = [
            (function, function_type),
            (construction, result),
            (local_name, result),
            (argument, array),
            (actual_name, expected),
            (call, expected),
            (invalid_name, expected),
            (bad_call, expected),
            (bad_argument, bad_array),
        ];
        for &(location, expected) in &locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        replay(
            &mut checker,
            &locations,
            &[(argument, array2_owner), (constructor, constructor_owner)],
            &[(function_signature, result), (constructed, result)],
        );
    }
}
