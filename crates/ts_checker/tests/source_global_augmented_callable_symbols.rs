use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(0);
const DECORATORS: FileId = FileId::new(1);
const LEGACY_DECORATORS: FileId = FileId::new(2);
const AUGMENTATION: FileId = FileId::new(3);
const SOURCE: FileId = FileId::new(4);

const AUGMENTATION_BODY: &str = concat!(
    "function parseInt(value: string, radix: number): string;\n",
    "export function parseInt(value: boolean): boolean;\n",
    "namespace parseInt { const label: string; const radix: number; }\n",
);
const CONSUMER: &str = concat!(
    "export {};\n",
    "const decimal = parseInt('10');\n",
    "const overlap = parseInt('10', 2);\n",
    "const flag = parseInt(true);\n",
    "const label = parseInt.label;\n",
    "const radix = parseInt.radix;\n",
    "const rejected = parseInt(null);\n",
    "const extra = parseInt('10', 2, 3);\n",
);

struct Inputs {
    library: ParseResult,
    decorators: ParseResult,
    legacy_decorators: ParseResult,
    augmentation: ParseResult,
    source: ParseResult,
    nested: bool,
}

impl Inputs {
    fn new(nested: bool) -> Self {
        Self::with_augmentation_body(nested, AUGMENTATION_BODY)
    }

    fn with_augmentation_body(nested: bool, body: &str) -> Self {
        let augmentation = if nested {
            format!(
                "declare module 'callable-augmentation' {{ global {{\n{body}}} }}\n"
            )
        } else {
            format!("export {{}};\ndeclare global {{\n{body}}}\n")
        };
        Self {
            library: parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
            decorators: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.d.ts"
            )),
            legacy_decorators: parse_source_file(include_str!(
                "../../ts_bundled/libs/lib.decorators.legacy.d.ts"
            )),
            augmentation: parse_source_file(&augmentation),
            source: parse_source_file(CONSUMER),
            nested,
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = [
            (LIBRARY, &self.library, "/lib.es5.d.ts"),
            (DECORATORS, &self.decorators, "/lib.decorators.d.ts"),
            (
                LEGACY_DECORATORS,
                &self.legacy_decorators,
                "/lib.decorators.legacy.d.ts",
            ),
            (AUGMENTATION, &self.augmentation, "/augmentation.d.ts"),
            (SOURCE, &self.source, "/consumer.ts"),
        ];
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in files {
            assert!(parsed.diagnostics.is_empty(), "{path}: {:?}", parsed.diagnostics);
            let module = if file == SOURCE || file == AUGMENTATION && !self.nested {
                CanonicalModuleState::External
            } else {
                CanonicalModuleState::Script
            };
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        file != SOURCE,
                        file != SOURCE && file != AUGMENTATION,
                        module,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
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
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        assert!(context.diagnostics().is_empty());
        context
    }
}

fn functions(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(function.name?)?.data else {
                return None;
            };
            if name.text != "parseInt" {
                return None;
            }
            assert!(function.body.is_none());
            Some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    declarations
}

struct Declarations {
    functions: [NodeRef; 3],
    namespace: NodeRef,
}

impl Declarations {
    fn new(inputs: &Inputs) -> Self {
        let library = functions(&inputs.library, LIBRARY);
        let augmentation = functions(&inputs.augmentation, AUGMENTATION);
        assert_eq!(library.len(), 1);
        assert_eq!(augmentation.len(), 2);
        let namespace = inputs
            .augmentation
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                (module.keyword == SyntaxKind::NamespaceKeyword)
                    .then_some(NodeRef::new(inputs.augmentation.arena.id(), AUGMENTATION, node))
            })
            .expect("the augmentation must retain its namespace");
        let arena = &inputs.augmentation.arena;
        let block = arena.get(augmentation[0].node).unwrap().parent.unwrap();
        assert_eq!(arena.get(block).unwrap().kind, SyntaxKind::ModuleBlock);
        for declaration in [augmentation[1], namespace] {
            assert_eq!(arena.get(declaration.node).unwrap().parent, Some(block));
        }
        let global = arena.get(block).unwrap().parent.unwrap();
        let global_record = arena.get(global).unwrap();
        let NodeData::ModuleDeclaration(global_data) = &global_record.data else {
            panic!("the shared ModuleBlock must belong to declare global")
        };
        assert_eq!(global_data.keyword, SyntaxKind::GlobalKeyword);
        assert_eq!(global_data.body, Some(block));
        let parent = arena.get(global_record.parent.unwrap()).unwrap();
        assert_eq!(
            parent.kind,
            if inputs.nested {
                SyntaxKind::ModuleBlock
            } else {
                SyntaxKind::SourceFile
            },
        );
        if inputs.nested {
            let NodeData::ModuleDeclaration(module) =
                &arena.get(parent.parent.unwrap()).unwrap().data
            else {
                panic!("the nested global must belong to the ambient module")
            };
            assert_eq!(module.keyword, SyntaxKind::ModuleKeyword);
            assert_eq!(arena.get(module.name).unwrap().kind, SyntaxKind::StringLiteral);
        }
        Self {
            functions: [library[0], augmentation[0], augmentation[1]],
            namespace,
        }
    }
}

fn raw_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context.file(node.file).unwrap().1.symbol(node).unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(raw_symbol(context, node))
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration or call must retain its signature")
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .expect("the symbol must retain its real value type")
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MergedCallable {
    owner: SemanticSymbolId,
    callable: TypeId,
    signatures: [SignatureId; 3],
    members: [SemanticSymbolId; 2],
}

#[allow(clippy::too_many_lines)] // Keep each signature with its source parameter types.
fn assert_merged_callable(
    context: &CanonicalCheckerContext<'_>,
    declarations: &Declarations,
) -> MergedCallable {
    let owner = symbol(context, declarations.functions[0]);
    let raw_library = raw_symbol(context, declarations.functions[0]);
    let raw_augmentation = raw_symbol(context, declarations.functions[1]);
    assert_ne!(raw_library, raw_augmentation);
    assert_ne!(owner, raw_library);
    assert_ne!(owner, raw_augmentation);
    let store = context.store();
    let record = store.symbol(owner).unwrap();
    assert_eq!(
        record.flags(),
        SymbolFlags::FUNCTION | SymbolFlags::VALUE_MODULE | SymbolFlags::TRANSIENT,
    );
    assert_eq!(record.parent(), None);
    let ordered = [
        declarations.functions[0],
        declarations.functions[1],
        declarations.functions[2],
        declarations.namespace,
    ];
    assert_eq!(record.declarations(), Some(&ordered[..]));
    assert_eq!(record.value_declaration(), Some(declarations.functions[0]));
    for declaration in ordered {
        assert_eq!(symbol(context, declaration), owner);
    }
    let global = store
        .symbol_table(context.globals())
        .unwrap()
        .get_source("parseInt")
        .unwrap();
    assert_eq!(store.get_merged_symbol(global), Some(owner));
    let signatures = declarations.functions.map(|node| signature(context, node));
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    let boolean = bootstrap.boolean_type;
    let undefined = bootstrap.undefined_type;
    let mut parameter_types = Vec::new();
    for (index, declaration) in declarations.functions.iter().copied().enumerate() {
        let record = store.signature(signatures[index]).unwrap();
        assert_eq!(record.declaration(), Some(declaration));
        assert_eq!(record.flags(), SignatureFlags::NONE);
        assert_eq!(record.min_argument_count(), [1, 2, 1][index]);
        assert_eq!(record.parameters().len(), [2, 2, 1][index]);
        assert_eq!(
            record.resolved_return_type(),
            Some([number, string, boolean][index]),
        );
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        let (arena, bound) = context.file(declaration.file).unwrap();
        let NodeData::FunctionDeclaration(function) = &arena.get(declaration.node).unwrap().data
        else {
            panic!("each signature must retain its function declaration")
        };
        assert_eq!(function.parameters.nodes.len(), record.parameters().len());
        for (&node, &parameter) in function.parameters.nodes.iter().zip(record.parameters()) {
            assert_eq!(arena.get(node).unwrap().parent, Some(declaration.node));
            assert_eq!(
                bound.symbol(NodeRef::new(arena.id(), declaration.file, node)),
                Some(parameter),
            );
        }
        parameter_types.push(
            record
                .parameters()
                .iter()
                .map(|&parameter| value_type(context, parameter))
                .collect::<Vec<_>>(),
        );
    }
    assert_eq!(parameter_types[0][0], string);
    let TypeData::Union(optional) = store.type_payload(parameter_types[0][1]).unwrap().data()
    else {
        panic!("the real library radix parameter must remain optional")
    };
    let mut optional_types = [number, undefined];
    optional_types.sort_unstable();
    assert_eq!(optional.union.types, optional_types);
    assert_eq!(parameter_types[1], [string, number]);
    assert_eq!(parameter_types[2], [boolean]);
    let callable = value_type(context, owner);
    let payload = store.type_payload(callable).unwrap();
    assert_eq!(payload.symbol(), Some(owner));
    let TypeData::Object(object) = payload.data() else {
        panic!("the merged global must retain its callable object")
    };
    assert_eq!(object.structured.call_signature_count, 3);
    assert_eq!(object.structured.signatures.as_deref(), Some(&signatures[..]));
    let exports = store.symbol_table(record.exports().unwrap()).unwrap();
    assert_eq!(exports.len(), 2);
    let members = ["label", "radix"].map(|name| exports.get_source(name).unwrap());
    for member in members {
        let record = store.symbol(member).unwrap();
        assert_eq!(store.get_merged_symbol(record.parent().unwrap()), Some(owner));
        let [declaration] = record.declarations().unwrap() else {
            panic!("each namespace member must keep its one source declaration")
        };
        assert_eq!(declaration.file, AUGMENTATION);
        assert_eq!(symbol(context, *declaration), member);
    }
    MergedCallable {
        owner,
        callable,
        signatures,
        members,
    }
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
            (name.text == expected)
                .then(|| NodeRef::new(parsed.arena.id(), SOURCE, variable.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing initializer {expected}"))
}

fn call_parts(parsed: &ParseResult, call: NodeRef) -> (NodeRef, Vec<NodeRef>) {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a source call")
    };
    (
        NodeRef::new(call.arena, call.file, data.expression),
        data.arguments
            .nodes
            .iter()
            .map(|&node| NodeRef::new(call.arena, call.file, node))
            .collect(),
    )
}

fn assert_queries(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    merged: &MergedCallable,
) {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    let boolean = bootstrap.boolean_type;
    for (name, selected, result) in [
        ("decimal", merged.signatures[0], number),
        ("overlap", merged.signatures[1], string),
        ("flag", merged.signatures[2], boolean),
    ] {
        let call = initializer(source, name);
        let (callee, _) = call_parts(source, call);
        assert_eq!(signature(context, call), selected);
        assert_eq!(context.get_type_at_location(call), Ok(result));
        assert_eq!(context.get_type_at_location(callee), Ok(merged.callable));
        assert_eq!(context.get_symbol_at_location(callee), Ok(Some(merged.owner)));
        assert_eq!(
            context.store().type_node_links(call).unwrap().resolved_type,
            Some(result),
        );
    }
    for ((name, member), expected) in ["label", "radix"]
        .into_iter()
        .zip(merged.members)
        .zip([string, number])
    {
        let access = initializer(source, name);
        let NodeData::PropertyAccessExpression(data) = &source.arena.get(access.node).unwrap().data
        else {
            panic!("the consumer must read the namespace member")
        };
        let name = NodeRef::new(access.arena, access.file, data.name);
        assert_eq!(context.get_type_at_location(access), Ok(expected));
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(member)));
        assert_eq!(value_type(context, member), expected);
    }
}

fn assert_failures(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    declarations: &Declarations,
    merged: &MergedCallable,
) {
    let rejected = initializer(source, "rejected");
    let extra = initializer(source, "extra");
    let (_, rejected_arguments) = call_parts(source, rejected);
    let (_, extra_arguments) = call_parts(source, extra);
    let [argument_error, arity_error] = context.diagnostics().as_slice() else {
        panic!("only the two invalid calls must report diagnostics: {:?}", context.diagnostics())
    };
    assert_eq!(argument_error.diagnostic.code(), 2769);
    assert_eq!(argument_error.node, Some(rejected_arguments[0]));
    assert_eq!(argument_error.range_override, None);
    assert_eq!(
        argument_error.diagnostic.render().unwrap(),
        concat!(
            "No overload matches this call.\n",
            "  The last overload gave the following error.\n",
            "    Argument of type 'null' is not assignable to parameter of type 'string'.",
        ),
    );
    let [related] = argument_error.related_information.as_slice() else {
        panic!("the argument error must point to the real last library overload")
    };
    assert_eq!(related.diagnostic.code(), 2771);
    assert_eq!(related.node, Some(declarations.functions[0]));
    assert_eq!(related.diagnostic.render().unwrap(), "The last overload is declared here.");
    assert_eq!(arity_error.diagnostic.code(), 2554);
    assert_eq!(arity_error.node, Some(extra));
    assert_eq!(arity_error.diagnostic.render().unwrap(), "Expected 1-2 arguments, but got 3.");
    assert!(arity_error.related_information.is_empty());
    let range = arity_error.range_override.unwrap();
    assert_eq!(range.anchor(), extra);
    assert_eq!(range.range(), source.arena.get(extra_arguments[2].node).unwrap().range);
    for call in [rejected, extra] {
        let recovered = signature(context, call);
        assert!(!merged.signatures.contains(&recovered));
        assert_eq!(
            context.store().signature(recovered).unwrap().flags(),
            SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE,
        );
        let returned = context.get_return_type_of_signature(recovered).unwrap();
        assert_eq!(context.get_type_at_location(call), Ok(returned));
    }
}

fn assert_providers_unchecked(context: &CanonicalCheckerContext<'_>) {
    for file in [LIBRARY, DECORATORS, LEGACY_DECORATORS, AUGMENTATION] {
        assert!(
            !context.store().source_file_links(context.source_file(file).unwrap())
                .is_some_and(|links| links.type_checked),
        );
    }
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    declarations: &Declarations,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.signature_len(),
            store.mapper_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
        ],
        context.diagnostics().clone(),
        declarations
            .functions
            .map(|node| store.signature_links(node).cloned()),
        [AUGMENTATION, SOURCE]
            .into_iter()
            .flat_map(|file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(arena.id(), file, id);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
    )
}

fn check_augmented_callable(nested: bool) {
    let inputs = Inputs::new(nested);
    let declarations = Declarations::new(&inputs);
    let (callee, _) = call_parts(&inputs.source, initializer(&inputs.source, "decimal"));
    for query_first in [false, true] {
        let mut context = inputs.context();
        assert_providers_unchecked(&context);
        let early = query_first.then(|| context.get_type_at_location(callee).unwrap());
        context.check_source_file(SOURCE).unwrap();
        let merged = assert_merged_callable(&context, &declarations);
        if let Some(early) = early {
            assert_eq!(early, merged.callable);
        }
        assert_queries(&mut context, &inputs.source, &merged);
        assert_failures(&mut context, &inputs.source, &declarations, &merged);
        assert_providers_unchecked(&context);
        let before = snapshot(&context, &declarations);
        for _ in 0..2 {
            context.check_source_file(SOURCE).unwrap();
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(assert_merged_callable(&context, &declarations), merged);
            assert_queries(&mut context, &inputs.source, &merged);
            assert_failures(&mut context, &inputs.source, &declarations, &merged);
            assert_providers_unchecked(&context);
            assert_eq!(snapshot(&context, &declarations), before);
        }
    }
}

#[test]
fn external_global_augmentation_keeps_library_overloads_members_and_replay() {
    check_augmented_callable(false);
}

#[test]
fn ambient_module_global_augmentation_keeps_library_overloads_members_and_replay() {
    check_augmented_callable(true);
}

fn check_augmented_callable_type_query(nested: bool) {
    let mut inputs = Inputs::new(nested);
    inputs.source = parse_source_file(&format!("type Parser = typeof parseInt;\n{CONSUMER}"));
    check_augmented_callable_type_query_inputs(inputs, None);
}

fn check_augmented_callable_type_query_inputs(inputs: Inputs, return_query: Option<NodeRef>) {
    let declarations = Declarations::new(&inputs);
    let queries = inputs
        .source
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::TypeQueryNode(query) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(inputs.source.arena.id(), SOURCE, node),
                query.expr_name,
            ))
        })
        .collect::<Vec<_>>();
    let [(query, name)] = queries.as_slice() else {
        panic!("one direct type query is required");
    };
    let query = *query;
    let name = NodeRef::new(query.arena, SOURCE, *name);
    for query_first in [false, true] {
        let mut context = inputs.context();
        let owner = symbol(&context, declarations.functions[0]);
        assert!(
            context
                .store()
                .value_symbol_links(owner)
                .and_then(|links| links.resolved_type)
                .is_none()
        );
        let early = if query_first {
            let type_ = context.get_type_from_type_node(query).unwrap();
            assert_eq!(value_type(&context, owner), type_);
            let payload = context.store().type_payload(type_).unwrap();
            assert_eq!(payload.symbol(), Some(owner));
            let TypeData::Object(object) = payload.data() else {
                panic!("a callable value must be an object");
            };
            assert!(object.structured.signatures.is_none());
            assert!(object.structured.members.is_none());
            for declaration in declarations.functions {
                assert!(
                    context
                        .store()
                        .signature_links(declaration)
                        .is_none_or(|links| links.resolved_signature.signature().is_none())
                );
            }
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(name)
                    .unwrap()
                    .resolved_symbol,
                Some(owner)
            );
            assert_providers_unchecked(&context);
            assert!(
                !context
                    .store()
                    .source_file_links(context.source_file(SOURCE).unwrap())
                    .is_some_and(|links| links.type_checked)
            );
            let before = snapshot(&context, &declarations);
            assert_eq!(context.get_type_from_type_node(query), Ok(type_));
            assert_eq!(snapshot(&context, &declarations), before);
            Some(type_)
        } else {
            None
        };
        if let Some(return_query) = return_query {
            assert!(
                context
                    .store()
                    .type_node_links(return_query)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
        }
        context.check_source_file(SOURCE).unwrap();
        let merged = assert_merged_callable(&context, &declarations);
        if let Some(early) = early {
            assert_eq!(early, merged.callable);
        }
        assert_eq!(context.get_type_from_type_node(query), Ok(merged.callable));
        assert_queries(&mut context, &inputs.source, &merged);
        assert_failures(&mut context, &inputs.source, &declarations, &merged);
        assert_providers_unchecked(&context);
        let before = snapshot(&context, &declarations);
        for _ in 0..2 {
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(context.get_type_from_type_node(query), Ok(merged.callable));
            assert_eq!(assert_merged_callable(&context, &declarations), merged);
            assert_queries(&mut context, &inputs.source, &merged);
            assert_failures(&mut context, &inputs.source, &declarations, &merged);
            assert_providers_unchecked(&context);
            assert_eq!(snapshot(&context, &declarations), before);
        }
    }
}

#[test]
fn external_global_type_query_keeps_lazy_identity_through_overload_demand() {
    check_augmented_callable_type_query(false);
}

#[test]
fn conditional_return_inference_demands_pending_global_overloads() {
    for nested in [false, true] {
        let inputs = Inputs {
            source: parse_source_file(concat!(
                "export {};\n",
                "type Last<T> = T extends (...args: any) => infer R ? R : never;\n",
                "type Actual = Last<typeof parseInt>;\n",
            )),
            ..Inputs::new(nested)
        };
        let declarations = Declarations::new(&inputs);
        let arena = &inputs.source.arena;
        let query = arena.iter().find_map(|(id, node)| {
            (node.kind == SyntaxKind::TypeQuery)
                .then_some(NodeRef::new(arena.id(), SOURCE, id))
        }).unwrap();
        let actual = arena.iter().find_map(|(_, node)| {
            let NodeData::TypeAliasDeclaration(alias) = &node.data else { return None };
            let NodeData::Identifier(name) = &arena.get(alias.name)?.data else { return None };
            (name.text == "Actual")
                .then_some(NodeRef::new(arena.id(), SOURCE, alias.type_))
        }).unwrap();
        for query_first in [true, false] {
            let mut context = inputs.context();
            let early = query_first.then(|| {
                let callable = context.get_type_from_type_node(query).unwrap();
                let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
                else { panic!("expected a pending callable") };
                assert!(object.structured.signatures.is_none());
                assert!(object.structured.members.is_none());
                let expected = context.store().intrinsic_bootstrap().unwrap().boolean_type;
                assert_eq!(context.get_type_from_type_node(actual), Ok(expected));
                assert_providers_unchecked(&context);
                assert!(!context.store().source_file_links(context.source_file(SOURCE).unwrap())
                    .is_some_and(|links| links.type_checked));
                assert_eq!(context.get_type_from_type_node(query), Ok(callable));
                callable
            });
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
            let expected = context.store().intrinsic_bootstrap().unwrap().boolean_type;
            assert_eq!(context.get_type_from_type_node(actual), Ok(expected));
            let callable = context.get_type_from_type_node(query).unwrap();
            assert!(early.is_none_or(|early| early == callable));
            let owner = symbol(&context, declarations.functions[0]);
            assert_eq!(value_type(&context, owner), callable);
            let signatures = declarations.functions.map(|node| signature(&context, node));
            let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
            else { panic!("expected the completed callable") };
            assert_eq!(object.structured.signatures.as_deref(), Some(signatures.as_slice()));
            assert_eq!(context.get_return_type_of_signature(signatures[2]), Ok(expected));
            assert_providers_unchecked(&context);
            let before = (snapshot(&context, &declarations), context.store().relation_state_snapshot());
            for _ in 0..2 {
                context.recheck_source_file(SOURCE).unwrap();
                assert_eq!(context.get_type_from_type_node(query), Ok(callable));
                assert_eq!(context.get_type_from_type_node(actual), Ok(expected));
                assert_providers_unchecked(&context);
                assert_eq!((snapshot(&context, &declarations), context.store().relation_state_snapshot()), before);
            }
        }
    }
}

#[test]
fn ambient_module_global_type_query_keeps_lazy_identity_through_overload_demand() {
    check_augmented_callable_type_query(true);
}

#[test]
fn return_type_checks_pending_global_overload_constraints_and_replays() {
    for nested in [false, true] {
        let inputs = Inputs {
            source: parse_source_file(concat!(
                "export {};\n",
                "type Actual = ReturnType<typeof parseInt>;\n",
            )),
            ..Inputs::new(nested)
        };
        let declarations = Declarations::new(&inputs);
        let arena = &inputs.source.arena;
        let query = arena.iter().find_map(|(id, node)| {
            (node.kind == SyntaxKind::TypeQuery)
                .then_some(NodeRef::new(arena.id(), SOURCE, id))
        }).unwrap();
        let actual = arena.iter().find_map(|(_, node)| {
            let NodeData::TypeAliasDeclaration(alias) = &node.data else { return None };
            let NodeData::Identifier(name) = &arena.get(alias.name)?.data else { return None };
            (name.text == "Actual")
                .then_some(NodeRef::new(arena.id(), SOURCE, alias.type_))
        }).unwrap();
        let library = &inputs.library.arena;
        let constraint = library.iter().find_map(|(_, node)| {
            let NodeData::TypeAliasDeclaration(alias) = &node.data else { return None };
            let NodeData::Identifier(name) = &library.get(alias.name)?.data else { return None };
            if name.text != "ReturnType" {
                return None;
            }
            let [parameter] = alias.type_parameters.as_ref()?.nodes.as_slice() else {
                panic!("ReturnType must have one formal");
            };
            let NodeData::TypeParameterDeclaration(parameter) = &library.get(*parameter)?.data
            else { panic!("expected the ReturnType formal") };
            Some(NodeRef::new(library.id(), LIBRARY, parameter.constraint?))
        }).unwrap();
        for query_first in [true, false] {
            let mut context = inputs.context();
            let expected = context.store().intrinsic_bootstrap().unwrap().boolean_type;
            let early = query_first.then(|| {
                let callable = context.get_type_from_type_node(query).unwrap();
                let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
                else { panic!("expected a pending callable") };
                assert!(object.structured.signatures.is_none());
                assert!(object.structured.members.is_none());
                let result = context.get_type_from_type_node(actual);
                let constraint_type = context.get_type_from_type_node(constraint).unwrap();
                let TypeData::Object(constraint_object) = context.store()
                    .type_payload(constraint_type).unwrap().data()
                else { panic!("expected the ReturnType function constraint") };
                let [constraint_signature] = constraint_object.structured.signatures
                    .as_deref().unwrap() else {
                    panic!("ReturnType must retain one constraint signature");
                };
                let constraint_signature = *constraint_signature;
                context.get_return_type_of_signature(constraint_signature).unwrap();
                assert_eq!(
                    context.is_type_assignable_to(callable, constraint_type),
                    Ok(true),
                    "ReturnType alias result: {result:?}",
                );
                assert_eq!(result, Ok(expected));
                assert_providers_unchecked(&context);
                assert!(!context.store().source_file_links(context.source_file(SOURCE).unwrap())
                    .is_some_and(|links| links.type_checked));
                assert_eq!(context.get_type_from_type_node(query), Ok(callable));
                callable
            });
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
            assert_eq!(context.get_type_from_type_node(actual), Ok(expected));
            let callable = context.get_type_from_type_node(query).unwrap();
            assert!(early.is_none_or(|early| early == callable));
            let owner = symbol(&context, declarations.functions[0]);
            assert_eq!(value_type(&context, owner), callable);
            let signatures = declarations.functions.map(|node| signature(&context, node));
            let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
            else { panic!("expected the completed callable") };
            assert_eq!(object.structured.signatures.as_deref(), Some(signatures.as_slice()));
            assert_eq!(context.get_return_type_of_signature(signatures[2]), Ok(expected));
            assert_providers_unchecked(&context);
            let before = (snapshot(&context, &declarations), context.store().relation_state_snapshot());
            for _ in 0..2 {
                context.recheck_source_file(SOURCE).unwrap();
                assert_eq!(context.get_type_from_type_node(query), Ok(callable));
                assert_eq!(context.get_type_from_type_node(actual), Ok(expected));
                assert_providers_unchecked(&context);
                assert_eq!((snapshot(&context, &declarations), context.store().relation_state_snapshot()), before);
            }
        }
    }
}

#[test]
fn qualified_signature_type_query_reuses_the_pending_callable() {
    let body = concat!(
        "function parseInt(value: string, radix: number): typeof parseInt.label;\n",
        "export function parseInt(value: boolean): boolean;\n",
        "namespace parseInt { const label: string; const radix: number; }\n",
    );
    for nested in [false, true] {
        let mut inputs = Inputs::with_augmentation_body(nested, body);
        inputs.source = parse_source_file(&format!("type Parser = typeof parseInt;\n{CONSUMER}"));
        let declarations = Declarations::new(&inputs);
        let queries = inputs
            .augmentation
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::TypeQueryNode(query) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(inputs.augmentation.arena.id(), AUGMENTATION, node),
                    record.parent,
                    query.expr_name,
                ))
            })
            .collect::<Vec<_>>();
        let [(return_query, parent, name)] = queries.as_slice() else {
            panic!("one qualified return query is required");
        };
        assert_eq!(*parent, Some(declarations.functions[1].node));
        assert_eq!(
            inputs.augmentation.arena.get(*name).unwrap().kind,
            SyntaxKind::QualifiedName,
        );
        // Keep the return query cold until source demand resolves the overload.
        check_augmented_callable_type_query_inputs(inputs, Some(*return_query));
    }
}
