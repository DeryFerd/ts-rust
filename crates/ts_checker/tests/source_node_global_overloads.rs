use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SignatureLinks, TypeData, TypeId, TypeNodeLinks,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const DOM: FileId = FileId::new(301_090);
const DOM_ITERABLE: FileId = FileId::new(301_091);
const NODE_GLOBALS: FileId = FileId::new(301_100);
const NODE_EVENTS: FileId = FileId::new(301_101);
const NODE_PROMISES: FileId = FileId::new(301_102);
const NODE_TIMERS: FileId = FileId::new(301_103);
const SOURCE: FileId = FileId::new(301_104);

macro_rules! library {
    ($name:literal) => {
        (
            concat!("/lib.", $name, ".d.ts"),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")),
        )
    };
}

const LIBRARIES: &[(&str, &str)] = &[
    library!("es5"),
    library!("es2015"),
    library!("es2016"),
    library!("es2017"),
    library!("es2018"),
    library!("es2019"),
    library!("es2020"),
    library!("es2021"),
    library!("es2022"),
    library!("es2015.core"),
    library!("es2015.collection"),
    library!("es2015.generator"),
    library!("es2015.iterable"),
    library!("es2015.promise"),
    library!("es2015.proxy"),
    library!("es2015.reflect"),
    library!("es2015.symbol"),
    library!("es2015.symbol.wellknown"),
    library!("es2016.array.include"),
    library!("es2016.intl"),
    library!("es2017.arraybuffer"),
    library!("es2017.date"),
    library!("es2017.object"),
    library!("es2017.sharedmemory"),
    library!("es2017.string"),
    library!("es2017.intl"),
    library!("es2017.typedarrays"),
    library!("es2018.asyncgenerator"),
    library!("es2018.asynciterable"),
    library!("es2018.intl"),
    library!("es2018.promise"),
    library!("es2018.regexp"),
    library!("es2019.array"),
    library!("es2019.object"),
    library!("es2019.string"),
    library!("es2019.symbol"),
    library!("es2019.intl"),
    library!("es2020.bigint"),
    library!("es2020.date"),
    library!("es2020.promise"),
    library!("es2020.sharedmemory"),
    library!("es2020.string"),
    library!("es2020.symbol.wellknown"),
    library!("es2020.intl"),
    library!("es2020.number"),
    library!("es2021.promise"),
    library!("es2021.string"),
    library!("es2021.weakref"),
    library!("es2021.intl"),
    library!("es2022.array"),
    library!("es2022.error"),
    library!("es2022.intl"),
    library!("es2022.object"),
    library!("es2022.string"),
    library!("es2022.regexp"),
    library!("esnext.disposable"),
    library!("decorators"),
    library!("decorators.legacy"),
];

// Declaration excerpts from @types/node 22.19.15 keep the timer's real type closure.
// The setTimeout overloads and namespace come from timers.d.ts, including 11822..11992.
const GLOBAL_DECLARATIONS: &str = r"
declare namespace NodeJS {
    interface RefCounted {
        ref(): this;
        unref(): this;
    }
}
";

const EVENT_DECLARATIONS: &str = r#"
declare module "events" {
    namespace EventEmitter {
        export interface Abortable {
            signal?: AbortSignal | undefined;
        }
    }
    export = EventEmitter;
}
declare module "node:events" {
    import events = require("events");
    export = events;
}
"#;

const PROMISE_DECLARATIONS: &str = r#"
declare module "timers/promises" {
    import { TimerOptions } from "node:timers";
    function setTimeout<T = void>(delay?: number, value?: T, options?: TimerOptions): Promise<T>;
}
declare module "node:timers/promises" {
    export * from "timers/promises";
}
"#;

const TIMER_DECLARATIONS: &str = r#"
declare module "timers" {
    import { Abortable } from "node:events";
    import * as promises from "node:timers/promises";
    export interface TimerOptions extends Abortable {
        ref?: boolean | undefined;
    }
    global {
        namespace NodeJS {
            interface Timer extends RefCounted {
                hasRef(): boolean;
                refresh(): this;
                [Symbol.toPrimitive](): number;
            }
            interface Timeout extends RefCounted, Disposable, Timer {
                close(): this;
                hasRef(): boolean;
                ref(): this;
                refresh(): this;
                unref(): this;
                [Symbol.toPrimitive](): number;
                [Symbol.dispose](): void;
                _onTimeout(...args: any[]): void;
            }
        }
        function setTimeout<TArgs extends any[]>(
            callback: (...args: TArgs) => void,
            delay?: number,
            ...args: TArgs
        ): NodeJS.Timeout;
        function setTimeout(callback: (_: void) => void, delay?: number): NodeJS.Timeout;
        namespace setTimeout {
            import __promisify__ = promises.setTimeout;
            export { __promisify__ };
        }
    }
    import setTimeout = globalThis.setTimeout;
    export { promises, setTimeout };
}
declare module "node:timers" {
    export * from "timers";
}
"#;

struct Input {
    file: FileId,
    name: &'static str,
    parsed: ParseResult,
    default_library: bool,
}

struct Inputs(Vec<Input>);

impl Inputs {
    fn new(source: &str) -> Self {
        let mut files = LIBRARIES
            .iter()
            .enumerate()
            .map(|(index, &(name, source))| Input {
                file: FileId::new(301_000 + u32::try_from(index).unwrap()),
                name,
                parsed: parse_source_file(source),
                default_library: true,
            })
            .collect::<Vec<_>>();
        for (file, name, source, default_library) in [
            (
                DOM,
                "/lib.dom.d.ts",
                include_str!("../../ts_bundled/libs/lib.dom.d.ts"),
                true,
            ),
            (
                DOM_ITERABLE,
                "/lib.dom.iterable.d.ts",
                include_str!("../../ts_bundled/libs/lib.dom.iterable.d.ts"),
                true,
            ),
            (
                NODE_GLOBALS,
                "/node/globals.d.ts",
                GLOBAL_DECLARATIONS,
                false,
            ),
            (NODE_EVENTS, "/node/events.d.ts", EVENT_DECLARATIONS, false),
            (
                NODE_PROMISES,
                "/node/timers/promises.d.ts",
                PROMISE_DECLARATIONS,
                false,
            ),
            (NODE_TIMERS, "/node/timers.d.ts", TIMER_DECLARATIONS, false),
            (SOURCE, "/consumer.ts", source, false),
        ] {
            files.push(Input {
                file,
                name,
                parsed: parse_source_file(source),
                default_library,
            });
        }
        Self(files)
    }

    fn parsed(&self, file: FileId) -> &ParseResult {
        &self
            .0
            .iter()
            .find(|input| input.file == file)
            .unwrap()
            .parsed
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        for input in &self.0 {
            assert!(
                input.parsed.diagnostics.is_empty(),
                "{}: {:?}",
                input.name,
                input.parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &input.parsed.arena,
                    input.parsed.source_file,
                    input.file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(input.name),
                        CanonicalSourceLanguage::TypeScript,
                        input.file != SOURCE,
                        input.default_library,
                        if input.file == SOURCE {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
        }
        for input in &self.0 {
            binder
                .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
                .unwrap();
        }
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            self.0
                .iter()
                .map(|input| (input.file, &input.parsed.arena))
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
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        context
    }
}

#[derive(Clone)]
struct Function {
    declaration: NodeRef,
    name: NodeRef,
    formals: Vec<NodeRef>,
    parameters: Vec<NodeRef>,
    returned: NodeRef,
}

fn functions(inputs: &Inputs, file: FileId) -> Vec<Function> {
    let parsed = inputs.parsed(file);
    let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
    let mut result = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == "setTimeout").then(|| Function {
                declaration: node_ref(node),
                name: node_ref(name),
                formals: function
                    .type_parameters
                    .as_ref()
                    .map_or_else(Vec::new, |list| {
                        list.nodes.iter().copied().map(node_ref).collect()
                    }),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .copied()
                    .map(node_ref)
                    .collect(),
                returned: node_ref(function.type_.unwrap()),
            })
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|function| {
        parsed
            .arena
            .get(function.declaration.node)
            .unwrap()
            .range
            .start
    });
    result
}

fn calls(inputs: &Inputs) -> Vec<NodeRef> {
    let parsed = inputs.parsed(SOURCE);
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                SOURCE,
                node,
            ))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    calls
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

fn parameter_types(context: &CanonicalCheckerContext<'_>, id: SignatureId) -> Vec<TypeId> {
    let store = context.store();
    store
        .signature(id)
        .unwrap()
        .parameters()
        .iter()
        .map(|&parameter| {
            store
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type
                .unwrap()
        })
        .collect()
}

fn only_signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let structured = match context.store().type_payload(type_).unwrap().data() {
        TypeData::Object(object) => &object.structured,
        TypeData::TypeReference(reference) => &reference.object.structured,
        _ => panic!("the callback must retain its callable object"),
    };
    assert_eq!(structured.call_signature_count, 1);
    let [signature] = structured.signatures.as_deref().unwrap() else {
        panic!("the callback must have one call signature")
    };
    *signature
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Group {
    owner: SemanticSymbolId,
    callable: TypeId,
    signatures: [SignatureId; 3],
    formal: TypeId,
    constraint: TypeId,
    callback: SignatureId,
    returned: TypeId,
}

#[allow(clippy::too_many_lines)] // Check the original formal and both of its parameter edges together.
fn assert_group(context: &mut CanonicalCheckerContext<'_>, inputs: &Inputs) -> Group {
    let dom = functions(inputs, DOM);
    let node = functions(inputs, NODE_TIMERS);
    assert_eq!(dom.len(), 1);
    assert_eq!(node.len(), 2);
    let declarations = [&dom[0], &node[0], &node[1]];
    let owner = symbol(context, dom[0].declaration);
    let callable = context.get_type_at_location(dom[0].name).unwrap();
    let signatures = declarations.map(|function| signature(context, function.declaration));
    let store = context.store();
    let record = store.symbol(owner).unwrap();
    assert!(record.flags().contains(SymbolFlags::FUNCTION));
    assert!(record.flags().contains(SymbolFlags::VALUE_MODULE));
    let ordered = record
        .declarations()
        .unwrap()
        .iter()
        .copied()
        .filter(|node| {
            context
                .file(node.file)
                .unwrap()
                .0
                .get(node.node)
                .unwrap()
                .kind
                == SyntaxKind::FunctionDeclaration
        })
        .collect::<Vec<_>>();
    assert_eq!(ordered, declarations.map(|function| function.declaration));
    let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
        panic!("the full global function and namespace must share a callable object")
    };
    assert_eq!(object.structured.call_signature_count, 3);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&signatures[..])
    );
    assert_eq!(object.structured.members, record.exports());
    let promisify = store
        .symbol_table(record.exports().unwrap())
        .unwrap()
        .get_source("__promisify__")
        .unwrap();
    assert!(
        store
            .symbol(promisify)
            .unwrap()
            .flags()
            .contains(SymbolFlags::ALIAS)
    );
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let undefined = bootstrap.undefined_type;
    let any = bootstrap.any_type;
    let void = bootstrap.void_type;
    for (index, function) in declarations.iter().enumerate() {
        assert_eq!(symbol(context, function.declaration), owner);
        let signature = store.signature(signatures[index]).unwrap();
        assert_eq!(signature.declaration(), Some(function.declaration));
        assert_eq!(signature.min_argument_count(), 1);
        assert_eq!(signature.has_rest_parameter(), index != 2);
        assert_eq!(signature.parameters().len(), [3, 3, 2][index]);
        assert_eq!(signature.type_parameters().len(), usize::from(index == 1));
        assert!(signature.target().is_none());
        assert!(signature.mapper().is_none());
        assert_eq!(
            signature.parameters(),
            function
                .parameters
                .iter()
                .map(|&node| symbol(context, node))
                .collect::<Vec<_>>()
        );
        let types = parameter_types(context, signatures[index]);
        let TypeData::Union(optional) = store.type_payload(types[1]).unwrap().data() else {
            panic!("each written optional delay must retain number and undefined")
        };
        assert_eq!(optional.union.types.len(), 2);
        assert!(optional.union.types.contains(&number));
        assert!(optional.union.types.contains(&undefined));
    }
    assert_eq!(
        store
            .signature(signatures[0])
            .unwrap()
            .resolved_return_type(),
        Some(number)
    );
    let [formal_node] = node[0].formals.as_slice() else {
        panic!("the real Node overload must retain TArgs")
    };
    let parsed = inputs.parsed(NODE_TIMERS);
    let NodeData::TypeParameterDeclaration(formal_data) =
        &parsed.arena.get(formal_node.node).unwrap().data
    else {
        panic!("expected TArgs declaration")
    };
    let constraint_node = NodeRef::new(
        parsed.arena.id(),
        NODE_TIMERS,
        formal_data.constraint.unwrap(),
    );
    let formal = context
        .get_declared_type_of_symbol(symbol(context, *formal_node))
        .unwrap();
    let constraint = context.get_type_from_type_node(constraint_node).unwrap();
    let store = context.store();
    assert_eq!(
        store.signature(signatures[1]).unwrap().type_parameters(),
        [formal]
    );
    let TypeData::TypeParameter(parameter) = store.type_payload(formal).unwrap().data() else {
        panic!("TArgs must keep its real type parameter")
    };
    assert_eq!(parameter.constraint, Some(constraint));
    assert!(parameter.target.is_none());
    assert!(parameter.mapper.is_none());
    let TypeData::TypeReference(array) = store.type_payload(constraint).unwrap().data() else {
        panic!("the written constraint must remain the canonical any array")
    };
    assert_eq!(array.resolved_type_arguments.as_deref(), Some(&[any][..]));
    let array_owner = store
        .type_payload(array.object.target.unwrap())
        .unwrap()
        .symbol()
        .unwrap();
    assert_eq!(
        store.symbol(array_owner).unwrap().name().as_utf8(),
        Some("Array")
    );
    let types = parameter_types(context, signatures[1]);
    assert_eq!(types[2], formal);
    let callback = only_signature(context, types[0]);
    let callback_record = store.signature(callback).unwrap();
    let NodeData::ParameterDeclaration(callback_parameter) =
        &parsed.arena.get(node[0].parameters[0].node).unwrap().data
    else {
        panic!("expected the real callback parameter")
    };
    assert_eq!(
        callback_record.declaration(),
        Some(NodeRef::new(
            parsed.arena.id(),
            NODE_TIMERS,
            callback_parameter.type_.unwrap(),
        )),
    );
    assert!(callback_record.type_parameters().is_empty());
    assert!(callback_record.has_rest_parameter());
    assert_eq!(callback_record.min_argument_count(), 0);
    assert_eq!(parameter_types(context, callback), [formal]);
    assert_eq!(callback_record.resolved_return_type(), Some(void));
    let legacy_callback = only_signature(context, parameter_types(context, signatures[2])[0]);
    assert_eq!(parameter_types(context, legacy_callback), [void]);
    assert!(
        !store
            .signature(legacy_callback)
            .unwrap()
            .has_rest_parameter()
    );
    let returned = context.get_type_from_type_node(node[0].returned).unwrap();
    assert_eq!(
        context.get_type_from_type_node(node[1].returned),
        Ok(returned)
    );
    for signature in &signatures[1..] {
        assert_eq!(
            context.get_return_type_of_signature(*signature),
            Ok(returned)
        );
    }
    let returned_owner = context
        .store()
        .type_payload(returned)
        .unwrap()
        .symbol()
        .unwrap();
    let returned_symbol = context.store().symbol(returned_owner).unwrap();
    assert_eq!(returned_symbol.name().as_utf8(), Some("Timeout"));
    let timeout_declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                return None;
            };
            (name.text == "Timeout").then_some(NodeRef::new(parsed.arena.id(), NODE_TIMERS, node))
        })
        .unwrap();
    assert_eq!(returned_owner, symbol(context, timeout_declaration));
    assert!(
        returned_symbol
            .declarations()
            .unwrap()
            .iter()
            .all(|node| node.file == NODE_TIMERS)
    );
    assert_ne!(returned, any);
    assert_ne!(returned, number);
    assert_ne!(returned, void);
    Group {
        owner,
        callable,
        signatures,
        formal,
        constraint,
        callback,
        returned,
    }
}

fn assert_instantiation(
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
    group: &Group,
    expected_elements: &[TypeId],
) {
    assert_eq!(context.get_type_at_location(call), Ok(group.returned));
    let selected = signature(context, call);
    let store = context.store();
    let record = store.signature(selected).unwrap();
    assert_eq!(record.target(), Some(group.signatures[1]));
    assert!(record.type_parameters().is_empty());
    assert!(record.has_rest_parameter());
    assert_eq!(record.parameters().len(), 3);
    assert_eq!(record.resolved_return_type(), Some(group.returned));
    let mapper = record.mapper().unwrap();
    let original = store.signature(group.signatures[1]).unwrap();
    for index in [0, 2] {
        let parameter = record.parameters()[index];
        let source = original.parameters()[index];
        assert_ne!(parameter, source);
        let links = store.value_symbol_links(parameter).unwrap();
        assert_eq!(links.target, Some(source));
        assert_eq!(links.mapper, Some(mapper));
    }
    let tuple = store.map_type(mapper, group.formal).unwrap();
    if expected_elements.is_empty() {
        let TypeData::Tuple(empty) = store.type_payload(tuple).unwrap().data() else {
            panic!("empty TArgs must retain the canonical empty tuple")
        };
        let reference = &empty.interface.reference;
        assert_eq!(reference.object.target, Some(tuple));
        assert!(reference.object.mapper.is_none());
        assert_eq!(reference.resolved_type_arguments.as_deref(), Some(&[][..]));
        assert!(empty.metadata.element_infos().is_empty());
        assert_eq!(empty.metadata.min_length(), 0);
        assert_eq!(empty.metadata.fixed_length(), 0);
        assert_eq!(
            empty.metadata.combined_flags(),
            ts_checker::semantic::signatures::ElementFlags::NONE,
        );
        assert!(!empty.metadata.is_readonly());
    } else {
        let TypeData::TypeReference(reference) = store.type_payload(tuple).unwrap().data() else {
            panic!("the instantiated TArgs must retain a tuple")
        };
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(expected_elements)
        );
        assert!(matches!(
            store
                .type_payload(reference.object.target.unwrap())
                .unwrap()
                .data(),
            TypeData::Tuple(_)
        ));
    }
    let rest_links = store.value_symbol_links(record.parameters()[2]).unwrap();
    if expected_elements.is_empty() {
        assert!(rest_links.resolved_type.is_none());
    } else {
        assert_eq!(rest_links.resolved_type, Some(tuple));
    }
    let callback_type = store
        .value_symbol_links(record.parameters()[0])
        .unwrap()
        .resolved_type
        .unwrap();
    let callback = only_signature(context, callback_type);
    assert_ne!(callback, group.callback);
    let callback_record = store.signature(callback).unwrap();
    assert_eq!(callback_record.target(), Some(group.callback));
    assert!(callback_record.has_rest_parameter());
    assert!(callback_record.type_parameters().is_empty());
    assert_eq!(callback_record.parameters().len(), 1);
    let callback_mapper = callback_record.mapper().unwrap();
    assert_eq!(store.map_type(callback_mapper, group.formal), Some(tuple));
    let callback_parameter = store
        .value_symbol_links(callback_record.parameters()[0])
        .unwrap();
    assert_eq!(
        callback_parameter.target,
        Some(store.signature(group.callback).unwrap().parameters()[0]),
    );
    assert_eq!(callback_parameter.mapper, Some(callback_mapper));
    if let Some(cached) = callback_parameter.resolved_type {
        assert_eq!(cached, tuple);
    }
    assert_eq!(
        store.signature(callback).unwrap().resolved_return_type(),
        Some(store.intrinsic_bootstrap().unwrap().void_type),
    );
    assert_eq!(parameter_types(context, group.callback), [group.formal]);
    assert_eq!(
        parameter_types(context, group.signatures[1])[2],
        group.formal
    );
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 4],
    declarations: [SignatureId; 3],
    calls: Vec<(Option<TypeNodeLinks>, Option<SignatureLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(context: &CanonicalCheckerContext<'_>, calls: &[NodeRef], group: &Group) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
        ],
        declarations: group.signatures,
        calls: calls
            .iter()
            .map(|&call| {
                (
                    store.type_node_links(call).cloned(),
                    store.signature_links(call).cloned(),
                )
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

#[test]
fn node_global_overloads_keep_real_tuple_callbacks_and_all_three_signatures() {
    let inputs = Inputs::new(
        r"
export {};
declare function textCallback(value: string): void;
declare function pairCallback(value: string, code: number): void;
declare function flagCallback(enabled: boolean): void;
declare function emptyCallback(): void;
const text = setTimeout<[string]>(textCallback, 5, 'ready');
const pair = setTimeout<[string, number]>(pairCallback, undefined, 'ready', 2);
const flag = setTimeout(flagCallback, 1, true);
const empty = setTimeout(emptyCallback, 2);
const browser = setTimeout('tick', 1, 1, 'payload');
",
    );
    let calls = calls(&inputs);
    assert_eq!(calls.len(), 5);
    for call_first in [false, true] {
        let mut context = inputs.context();
        let cold = call_first.then(|| context.get_type_at_location(calls[1]).unwrap());
        context.check_source_file(SOURCE).unwrap();
        let group = assert_group(&mut context, &inputs);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let boolean = bootstrap.boolean_type;
        assert_instantiation(&mut context, calls[0], &group, &[string]);
        assert_instantiation(&mut context, calls[1], &group, &[string, number]);
        assert_instantiation(&mut context, calls[2], &group, &[boolean]);
        assert_instantiation(&mut context, calls[3], &group, &[]);
        assert_eq!(context.get_type_at_location(calls[4]), Ok(number));
        assert_eq!(signature(&context, calls[4]), group.signatures[0]);
        if let Some(cold) = cold {
            assert_eq!(cold, group.returned);
        }
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let before = snapshot(&context, &calls, &group);
        for _ in 0..2 {
            context.check_source_file(SOURCE).unwrap();
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(assert_group(&mut context, &inputs), group);
            assert_instantiation(&mut context, calls[0], &group, &[string]);
            assert_instantiation(&mut context, calls[1], &group, &[string, number]);
            assert_instantiation(&mut context, calls[2], &group, &[boolean]);
            assert_instantiation(&mut context, calls[3], &group, &[]);
            assert_eq!(snapshot(&context, &calls, &group), before);
        }
    }
}

#[test]
fn node_global_overloads_keep_native_rest_and_constraint_errors() {
    let inputs = Inputs::new(
        r"
export {};
declare function textCallback(value: string): void;
setTimeout<[string]>(textCallback, 5, 123);
setTimeout<number>(textCallback, 5, 123);
",
    );
    let calls = calls(&inputs);
    assert_eq!(calls.len(), 2);
    let mut context = inputs.context();
    context.check_source_file(SOURCE).unwrap();
    let group = assert_group(&mut context, &inputs);
    let parsed = inputs.parsed(SOURCE);
    let NodeData::CallExpression(rest_call) = &parsed.arena.get(calls[0].node).unwrap().data else {
        panic!("expected the fresh tuple-rest call")
    };
    let NodeData::CallExpression(constraint_call) = &parsed.arena.get(calls[1].node).unwrap().data
    else {
        panic!("expected the fresh constraint call")
    };
    let expected = [
        (
            2345,
            NodeRef::new(parsed.arena.id(), SOURCE, rest_call.arguments.nodes[2]),
            ["number", "string"],
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        ),
        (
            2344,
            NodeRef::new(
                parsed.arena.id(),
                SOURCE,
                constraint_call.type_arguments.as_ref().unwrap().nodes[0],
            ),
            ["number", "any[]"],
            "Type 'number' does not satisfy the constraint 'any[]'.",
        ),
    ];
    assert_eq!(context.diagnostics().len(), expected.len());
    for (diagnostic, (code, node, arguments, message)) in
        context.diagnostics().as_slice().iter().zip(expected)
    {
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
    }
    let before = snapshot(&context, &calls, &group);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(assert_group(&mut context, &inputs), group);
        assert_eq!(snapshot(&context, &calls, &group), before);
    }
}
