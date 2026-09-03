use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::{InterfaceTypeData, TypeCacheState},
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const ES5: FileId = FileId::new(0);
const DOM: FileId = FileId::new(1);
const SOURCE: FileId = FileId::new(2);
const NODE_EVENTS: FileId = FileId::new(3);

// Complete web-globals/events.d.ts from @types/node 22.19.15.
const NODE_EVENT_DECLARATIONS: &str = r#"export {};

interface AddEventListenerOptions extends EventListenerOptions {
    once?: boolean;
    passive?: boolean;
    signal?: AbortSignal;
}

type _CustomEvent<T = any> = typeof globalThis extends { onmessage: any } ? {} : CustomEvent<T>;
interface CustomEvent<T = any> extends Event {
    readonly detail: T;
}

interface CustomEventInit<T = any> extends EventInit {
    detail?: T;
}

type _Event = typeof globalThis extends { onmessage: any } ? {} : Event;
interface Event {
    readonly bubbles: boolean;
    cancelBubble: boolean;
    readonly cancelable: boolean;
    readonly composed: boolean;
    readonly currentTarget: EventTarget | null;
    readonly defaultPrevented: boolean;
    readonly eventPhase: 0 | 2;
    readonly isTrusted: boolean;
    returnValue: boolean;
    readonly srcElement: EventTarget | null;
    readonly target: EventTarget | null;
    readonly timeStamp: number;
    readonly type: string;
    composedPath(): [EventTarget?];
    initEvent(type: string, bubbles?: boolean, cancelable?: boolean): void;
    preventDefault(): void;
    stopImmediatePropagation(): void;
    stopPropagation(): void;
}

interface EventInit {
    bubbles?: boolean;
    cancelable?: boolean;
    composed?: boolean;
}

interface EventListener {
    (evt: Event): void;
}

interface EventListenerObject {
    handleEvent(object: Event): void;
}

type _EventListenerOptions = typeof globalThis extends { onmessage: any } ? {} : EventListenerOptions;
interface EventListenerOptions {
    capture?: boolean;
}

type _EventTarget = typeof globalThis extends { onmessage: any } ? {} : EventTarget;
interface EventTarget {
    addEventListener(
        type: string,
        listener: EventListener | EventListenerObject,
        options?: AddEventListenerOptions | boolean,
    ): void;
    dispatchEvent(event: Event): boolean;
    removeEventListener(
        type: string,
        listener: EventListener | EventListenerObject,
        options?: EventListenerOptions | boolean,
    ): void;
}

declare global {
    interface CustomEvent<T = any> extends _CustomEvent<T> {}
    var CustomEvent: typeof globalThis extends { onmessage: any; CustomEvent: infer T } ? T
        : {
            prototype: CustomEvent;
            new<T>(type: string, eventInitDict?: CustomEventInit<T>): CustomEvent<T>;
        };

    interface Event extends _Event {}
    var Event: typeof globalThis extends { onmessage: any; Event: infer T } ? T
        : {
            prototype: Event;
            new(type: string, eventInitDict?: EventInit): Event;
        };

    interface EventListenerOptions extends _EventListenerOptions {}

    interface EventTarget extends _EventTarget {}
    var EventTarget: typeof globalThis extends { onmessage: any; EventTarget: infer T } ? T
        : {
            prototype: EventTarget;
            new(): EventTarget;
        };
}
"#;

struct Inputs {
    es5: ParseResult,
    dom: ParseResult,
    node_events: ParseResult,
    source: ParseResult,
}

impl Inputs {
    fn new(source: &str) -> Self {
        Self {
            es5: parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
            dom: parse_source_file(include_str!("../../ts_bundled/libs/lib.dom.d.ts")),
            node_events: parse_source_file(NODE_EVENT_DECLARATIONS),
            source: parse_source_file(source),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = [
            (ES5, &self.es5, "/lib.es5.d.ts"),
            (DOM, &self.dom, "/lib.dom.d.ts"),
            (
                NODE_EVENTS,
                &self.node_events,
                "/node/web-globals/events.d.ts",
            ),
            (SOURCE, &self.source, "/consumer.ts"),
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
                        file != SOURCE,
                        file == ES5 || file == DOM,
                        if file == SOURCE || file == NODE_EVENTS {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
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
                    exact_optional_property_types: false,
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        assert!(context.global_type_diagnostics().next().is_none());
        context
    }

    fn interface(&self, expected: &str) -> NodeRef {
        self.dom
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(data) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.dom.arena.get(data.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(self.dom.arena.id(), DOM, node))
            })
            .unwrap_or_else(|| panic!("missing DOM interface {expected}"))
    }

    fn variable(&self, expected: &str) -> (NodeRef, Option<NodeRef>, Option<NodeRef>) {
        self.source
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(data) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &self.source.arena.get(data.name)?.data else {
                    return None;
                };
                let reference = |node| NodeRef::new(self.source.arena.id(), SOURCE, node);
                (name.text == expected).then(|| {
                    (
                        reference(node),
                        data.type_.map(reference),
                        data.initializer.map(reference),
                    )
                })
            })
            .unwrap_or_else(|| panic!("missing source variable {expected}"))
    }

    fn annotation(&self, name: &str) -> NodeRef {
        self.variable(name).1.unwrap()
    }

    fn read(&self, name: &str) -> NodeRef {
        let node = self.variable(name).2.unwrap();
        assert_eq!(
            self.source.arena.get(node.node).unwrap().kind,
            SyntaxKind::PropertyAccessExpression
        );
        node
    }

    fn progress_parameter(&self) -> NodeRef {
        let owner = self.interface("GlobalEventHandlers");
        let NodeData::InterfaceDeclaration(interface) =
            &self.dom.arena.get(owner.node).unwrap().data
        else {
            unreachable!();
        };
        let property = interface
            .members
            .nodes
            .iter()
            .copied()
            .find(|node| {
                let NodeData::PropertyDeclaration(property) =
                    &self.dom.arena.get(*node).unwrap().data
                else {
                    return false;
                };
                matches!(&self.dom.arena.get(property.name).unwrap().data,
                NodeData::Identifier(name) if name.text == "onprogress")
            })
            .expect("GlobalEventHandlers.onprogress");
        let references = self
            .dom
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::TypeReferenceNode(reference) = &record.data else {
                    return None;
                };
                if reference.type_arguments.is_some()
                    || !matches!(&self.dom.arena.get(reference.type_name)?.data,
                    NodeData::Identifier(name) if name.text == "ProgressEvent")
                {
                    return None;
                }
                let mut parent = record.parent;
                while let Some(current) = parent {
                    if current == property {
                        return Some(NodeRef::new(self.dom.arena.id(), DOM, node));
                    }
                    parent = self.dom.arena.get(current)?.parent;
                }
                None
            })
            .collect::<Vec<_>>();
        let [reference] = references.as_slice() else {
            panic!("the real onprogress callback must have one bare ProgressEvent reference");
        };
        let parent = self.dom.arena.get(reference.node).unwrap().parent.unwrap();
        let NodeData::ParameterDeclaration(parameter) = &self.dom.arena.get(parent).unwrap().data
        else {
            panic!("ProgressEvent must annotate the real callback parameter");
        };
        assert!(matches!(&self.dom.arena.get(parameter.name).unwrap().data,
            NodeData::Identifier(name) if name.text == "ev"));
        *reference
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn interface_data(context: &CanonicalCheckerContext<'_>, target: TypeId) -> InterfaceTypeData {
    let TypeData::Interface(interface) = context.store().type_payload(target).unwrap().data()
    else {
        panic!("the declared generic owner must retain its interface payload");
    };
    interface.clone()
}

fn assert_merged_event_target(inputs: &Inputs, context: &CanonicalCheckerContext<'_>) {
    let owner = symbol(context, inputs.interface("EventTarget"));
    let declarations = context
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap();
    assert_eq!(declarations.len(), 4);
    assert_eq!(
        declarations.iter().filter(|node| node.file == DOM).count(),
        2
    );
    let augmented = declarations
        .iter()
        .filter(|node| node.file == NODE_EVENTS)
        .collect::<Vec<_>>();
    assert_eq!(augmented.len(), 2);
    let kinds = augmented
        .iter()
        .map(|node| inputs.node_events.arena.get(node.node).unwrap().kind)
        .collect::<Vec<_>>();
    assert!(kinds.contains(&SyntaxKind::InterfaceDeclaration));
    assert!(kinds.contains(&SyntaxKind::VariableDeclaration));
    for declaration in augmented {
        assert_eq!(symbol(context, *declaration), owner);
    }
    let local = inputs
        .node_events
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::InterfaceDeclaration(interface) = &record.data else {
                return None;
            };
            (record.parent == Some(inputs.node_events.source_file)
                && matches!(&inputs.node_events.arena.get(interface.name)?.data,
                NodeData::Identifier(name) if name.text == "EventTarget"))
            .then_some(NodeRef::new(
                inputs.node_events.arena.id(),
                NODE_EVENTS,
                node,
            ))
        })
        .expect("the complete Node declaration retains its module-local EventTarget");
    assert_ne!(symbol(context, local), owner);
    assert_eq!(context.store().get_parent_of_symbol(owner), None);
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    reference: TypeId,
    target: TypeId,
    argument: TypeId,
) {
    let record = context.store().type_payload(reference).unwrap();
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE)
    );
    let TypeData::TypeReference(reference) = record.data() else {
        panic!("ProgressEvent must use a real generic interface reference");
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some([argument].as_slice())
    );
    let TypeCacheState::Allocated(cache) = interface_data(context, target)
        .reference
        .object
        .instantiations
    else {
        panic!("the canonical interface must own its instantiation cache");
    };
    assert!(cache.values().any(|cached| *cached == record.id()));
}

fn assert_nullable(context: &CanonicalCheckerContext<'_>, type_: TypeId, member: TypeId) {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("ProgressEvent.target must retain its written null union");
    };
    let null = context.store().intrinsic_bootstrap().unwrap().null_type;
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&member));
    assert!(union.union.types.contains(&null));
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    target: TypeId,
    annotations: &[(NodeRef, TypeId)],
    reads: &[(NodeRef, TypeId)],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.type_alias_len(),
            ],
            interface_data(context, target),
            annotations
                .iter()
                .map(|(node, _)| {
                    (
                        store.type_node_links(*node).cloned(),
                        store.symbol_node_links(*node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            context.diagnostics().clone(),
        )
    };
    let warm = snapshot(context);
    for _ in 0..2 {
        for &(node, expected) in annotations {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &(node, expected) in reads {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(snapshot(context), warm);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn dom_progress_event_defaults_and_concrete_arguments_keep_identity_and_replay() {
    let inputs = Inputs::new(concat!(
        "export {};\n",
        "declare const eventTarget: EventTarget;\n",
        "declare const reader: FileReader;\n",
        "declare const implicit: ProgressEvent;\n",
        "declare const explicit: ProgressEvent<EventTarget>;\n",
        "declare const concrete: ProgressEvent<FileReader>;\n",
        "const defaultTarget = implicit.target;\n",
        "const concreteTarget = concrete.target;\n",
        "const loaded = concrete.loaded;\n",
        "const eventType = concrete.type;\n",
    ));
    let mut context = inputs.context();
    let callback = inputs.progress_parameter();
    assert!(
        context
            .store()
            .type_node_links(callback)
            .and_then(|links| links.resolved_type)
            .is_none()
    );
    // Start with the unchanged DOM callback annotation recorded by the census.
    let callback_type = context.get_type_from_type_node(callback).unwrap();
    let names = ["eventTarget", "reader", "implicit", "explicit", "concrete"];
    let annotations = names.map(|name| inputs.annotation(name));
    let types = annotations.map(|node| context.get_type_from_type_node(node).unwrap());
    let [event_target, reader, implicit, explicit, concrete] = types;
    assert_eq!(callback_type, implicit);
    assert_eq!(implicit, explicit);
    assert_ne!(concrete, implicit);
    assert_merged_event_target(&inputs, &context);
    let declaration = inputs.interface("ProgressEvent");
    let owner = symbol(&context, declaration);
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(
        context.store().type_payload(target).unwrap().symbol(),
        Some(owner)
    );
    let declarations = context
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap();
    assert_eq!(declarations.len(), 2);
    assert!(declarations.contains(&declaration));
    let value = context
        .store()
        .symbol(owner)
        .unwrap()
        .value_declaration()
        .unwrap();
    assert!(declarations.contains(&value));
    assert_eq!(
        inputs.dom.arena.get(value.node).unwrap().kind,
        SyntaxKind::VariableDeclaration
    );
    assert_eq!(symbol(&context, value), owner);
    assert_reference(&context, implicit, target, event_target);
    assert_reference(&context, concrete, target, reader);
    let interface = interface_data(&context, target);
    let [formal] = interface
        .reference
        .resolved_type_arguments
        .as_deref()
        .unwrap()
    else {
        panic!("ProgressEvent must retain its one interface formal");
    };
    let NodeData::InterfaceDeclaration(written) =
        &inputs.dom.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let [written_formal] = written.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the bundled interface must declare exactly one formal");
    };
    let formal_owner = symbol(
        &context,
        NodeRef::new(declaration.arena, DOM, *written_formal),
    );
    assert_eq!(
        context.store().get_parent_of_symbol(formal_owner),
        Some(owner)
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(formal_owner)
            .and_then(|links| links.declared_type),
        Some(*formal)
    );
    let TypeData::TypeParameter(parameter) = context.store().type_payload(*formal).unwrap().data()
    else {
        panic!("the interface formal must be a real type parameter");
    };
    assert_eq!(parameter.constraint, Some(event_target));
    assert_eq!(parameter.resolved_default_type, Some(event_target));
    assert_eq!(
        context.store().type_payload(event_target).unwrap().symbol(),
        Some(symbol(&context, inputs.interface("EventTarget")))
    );
    assert_eq!(
        context.store().type_payload(reader).unwrap().symbol(),
        Some(symbol(&context, inputs.interface("FileReader")))
    );

    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let read_nodes =
        ["defaultTarget", "concreteTarget", "loaded", "eventType"].map(|name| inputs.read(name));
    let read_types = read_nodes.map(|node| context.get_type_at_location(node).unwrap());
    assert_nullable(&context, read_types[0], event_target);
    assert_nullable(&context, read_types[1], reader);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(read_types[2], bootstrap.number_type);
    assert_eq!(read_types[3], bootstrap.string_type);
    for node in [callback]
        .into_iter()
        .chain(annotations.into_iter().skip(2))
    {
        assert_eq!(
            context
                .store()
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol),
            Some(owner)
        );
    }
    let queries = [(callback, callback_type)]
        .into_iter()
        .chain(annotations.into_iter().zip(types))
        .collect::<Vec<_>>();
    let reads = read_nodes.into_iter().zip(read_types).collect::<Vec<_>>();
    assert_replay(&mut context, target, &queries, &reads);
}

#[test]
fn dom_progress_event_references_keep_native_constraint_and_arity_errors() {
    let inputs = Inputs::new(concat!(
        "export {};\n",
        "declare const invalid: ProgressEvent<string>;\n",
        "declare const extra: ProgressEvent<EventTarget, EventTarget>;\n",
    ));
    let mut context = inputs.context();
    assert_merged_event_target(&inputs, &context);
    let invalid_node = inputs.annotation("invalid");
    let extra_node = inputs.annotation("extra");
    let invalid = context.get_type_from_type_node(invalid_node).unwrap();
    let extra = context.get_type_from_type_node(extra_node).unwrap();
    let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
    assert_ne!(invalid, error_type);
    assert_eq!(extra, error_type);
    let target = context
        .get_declared_type_of_symbol(symbol(&context, inputs.interface("ProgressEvent")))
        .unwrap();
    assert_reference(
        &context,
        invalid,
        target,
        context.store().intrinsic_bootstrap().unwrap().string_type,
    );
    context.check_source_file(SOURCE).unwrap();
    let NodeData::TypeReferenceNode(reference) =
        &inputs.source.arena.get(invalid_node.node).unwrap().data
    else {
        unreachable!();
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the invalid reference must have one written argument");
    };
    let argument = NodeRef::new(invalid_node.arena, invalid_node.file, *argument);
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    assert_eq!(diagnostics[0].node, Some(argument));
    assert_eq!(diagnostics[0].diagnostic.code(), 2344);
    assert_eq!(
        diagnostics[0].diagnostic.arguments,
        ["string", "EventTarget"]
    );
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "Type 'string' does not satisfy the constraint 'EventTarget'."
    );
    assert_eq!(diagnostics[1].node, Some(extra_node));
    assert_eq!(diagnostics[1].diagnostic.code(), 2707);
    assert_eq!(
        diagnostics[1].diagnostic.arguments,
        ["ProgressEvent<T>", "0", "1"]
    );
    assert_eq!(
        diagnostics[1].diagnostic.render().unwrap(),
        "Generic type 'ProgressEvent<T>' requires between 0 and 1 type arguments."
    );
    for diagnostic in diagnostics {
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }
    assert_replay(
        &mut context,
        target,
        &[(invalid_node, invalid), (extra_node, extra)],
        &[],
    );
}
