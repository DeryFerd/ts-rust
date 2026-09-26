use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(300_470);

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

const SUBSCRIBABLE: &str = r"export class Subscribable<TListener extends Function> {
  protected listeners = new Set<TListener>()

  constructor() {
    this.subscribe = this.subscribe.bind(this)
  }

  subscribe(listener: TListener): () => void {
    this.listeners.add(listener)

    this.onSubscribe()

    return () => {
      this.listeners.delete(listener)
      this.onUnsubscribe()
    }
  }

  hasListeners(): boolean {
    return this.listeners.size > 0
  }

  protected onSubscribe(): void {
    // Do nothing
  }

  protected onUnsubscribe(): void {
    // Do nothing
  }
}
";

struct Fixture {
    libraries: Vec<ParseResult>,
    source: ParseResult,
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            libraries: LIBRARIES
                .iter()
                .map(|(_, source)| parse_source_file(source))
                .collect(),
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
            .chain([(
                FILE,
                &self.source,
                "\"/project/class-returned-arrows.ts\"".to_owned(),
                false,
            )])
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
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_bind_call_apply: true,
                strict_function_types: true,
                strict_property_initialization: true,
                strict_builtin_iterator_return: true,
                no_implicit_any: true,
                no_implicit_this: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn named(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        if record.kind != kind {
            return None;
        }
        let name = match &record.data {
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::MethodDeclaration(data) => data.name,
            NodeData::PropertyDeclaration(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, id))
    });
    let found = matches.next().unwrap_or_else(|| panic!("missing {expected}"));
    assert!(matches.next().is_none(), "more than one {expected}");
    found
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
        panic!("expected a canonical callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature")
    };
    *signature
}

fn resolved_signature(checker: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn property(parsed: &ParseResult, location: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let NodeData::PropertyAccessExpression(access) = &parsed.arena.get(location.node).unwrap().data
    else {
        panic!("expected the actual property access")
    };
    let NodeData::Identifier(name) = &parsed.arena.get(access.name).unwrap().data else {
        panic!("expected the written property name")
    };
    assert_eq!(name.text, expected);
    (node(parsed, access.expression), node(parsed, access.name))
}

struct BodyNodes {
    class: NodeRef,
    method: NodeRef,
    parameter: NodeRef,
    annotation: NodeRef,
    returned: NodeRef,
    arrow: NodeRef,
    calls: [NodeRef; 2],
    listeners: NodeRef,
    argument: NodeRef,
    receivers: [NodeRef; 2],
}

fn body_nodes(parsed: &ParseResult) -> BodyNodes {
    let class = named(parsed, SyntaxKind::ClassDeclaration, "Subscribable");
    let method = named(parsed, SyntaxKind::MethodDeclaration, "subscribe");
    assert_eq!(parsed.arena.get(method.node).unwrap().parent, Some(class.node));
    let NodeData::MethodDeclaration(method_data) = &parsed.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = method_data.parameters.nodes.as_slice() else {
        panic!("the method must keep its listener parameter")
    };
    let NodeData::Block(body) = &parsed.arena.get(method_data.body.unwrap()).unwrap().data else {
        panic!("the method must keep its block")
    };
    assert_eq!(body.statements.nodes.len(), 3);
    let returned = node(parsed, body.statements.nodes[2]);
    let NodeData::ReturnStatement(return_data) = &parsed.arena.get(returned.node).unwrap().data
    else {
        panic!("the arrow must be returned by the method")
    };
    let arrow = node(parsed, return_data.expression.unwrap());
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        panic!("the returned expression must remain an arrow")
    };
    assert!(arrow_data.parameters.nodes.is_empty());
    let NodeData::Block(arrow_body) = &parsed.arena.get(arrow_data.body).unwrap().data else {
        panic!("the arrow must keep its block")
    };
    let [delete, unsubscribe] = arrow_body.statements.nodes.as_slice() else {
        panic!("both arrow body statements must remain")
    };
    let calls = [*delete, *unsubscribe].map(|statement| {
        let NodeData::ExpressionStatement(data) = &parsed.arena.get(statement).unwrap().data else {
            panic!("expected an ordinary expression statement")
        };
        node(parsed, data.expression)
    });
    let NodeData::CallExpression(delete) = &parsed.arena.get(calls[0].node).unwrap().data else {
        panic!("expected the actual delete call")
    };
    let (listeners, _) = property(parsed, node(parsed, delete.expression), "delete");
    let (first_this, _) = property(parsed, listeners, "listeners");
    let [argument] = delete.arguments.nodes.as_slice() else {
        panic!("delete must keep its argument")
    };
    let NodeData::CallExpression(unsubscribe) = &parsed.arena.get(calls[1].node).unwrap().data
    else {
        panic!("expected the actual onUnsubscribe call")
    };
    assert!(unsubscribe.arguments.nodes.is_empty());
    let (second_this, _) = property(parsed, node(parsed, unsubscribe.expression), "onUnsubscribe");
    let receivers = [first_this, second_this];
    for receiver in receivers {
        assert_eq!(
            parsed.arena.get(receiver.node).unwrap().kind,
            SyntaxKind::ThisKeyword
        );
    }
    BodyNodes {
        class,
        method,
        parameter: node(parsed, *parameter),
        annotation: node(parsed, method_data.type_.unwrap()),
        returned,
        arrow,
        calls,
        listeners,
        argument: node(parsed, *argument),
        receivers,
    }
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
            .all(|node| node.file != FILE)
    );
    checker.get_declared_type_of_symbol(owner).unwrap()
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
                    checker.store().declared_type_links(symbol).cloned(),
                    checker.store().value_symbol_links(symbol).cloned(),
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
#[allow(clippy::too_many_lines)] // Keep the actual method, capture, receiver, and replay together.
fn returned_class_arrow_keeps_generic_capture_lexical_this_and_void() {
    let fixture = Fixture::new(SUBSCRIBABLE);
    let parsed = &fixture.source;
    let nodes = body_nodes(parsed);
    for query_first in [false, true] {
        let mut checker = fixture.context();
        let early = query_first.then(|| checker.get_type_at_location(nodes.arrow).unwrap());
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().as_slice().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let arrow_type = checker.get_type_at_location(nodes.arrow).unwrap();
        if let Some(early) = early {
            assert_eq!(arrow_type, early);
        }
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let void = bootstrap.void_type;
        let boolean = bootstrap.boolean_type;
        let class_owner = symbol(&checker, nodes.class);
        let method_owner = symbol(&checker, nodes.method);
        let listener_owner = symbol(&checker, nodes.parameter);
        let arrow_owner = symbol(&checker, nodes.arrow);
        let instance = checker.get_declared_type_of_symbol(class_owner).unwrap();
        let NodeData::ClassDeclaration(class) = &parsed.arena.get(nodes.class.node).unwrap().data
        else {
            unreachable!()
        };
        let [formal] = class.type_parameters.as_ref().unwrap().nodes.as_slice() else {
            panic!("the class must keep TListener")
        };
        let formal = node(parsed, *formal);
        let formal_owner = symbol(&checker, formal);
        let formal_type = checker.get_declared_type_of_symbol(formal_owner).unwrap();
        let TypeData::Interface(class_type) = checker.store().type_payload(instance).unwrap().data()
        else {
            panic!("expected the real generic class instance")
        };
        let this_type = class_type.this_type.unwrap();
        assert_eq!(
            class_type.reference.resolved_type_arguments.as_deref(),
            Some(&[formal_type][..])
        );
        assert_eq!(
            class_type.all_type_parameters.as_deref(),
            Some(&[formal_type, this_type][..])
        );
        let TypeData::TypeParameter(this) = checker.store().type_payload(this_type).unwrap().data()
        else {
            panic!("expected the class's own polymorphic this type")
        };
        assert!(this.is_this_type);
        assert_eq!(this.constraint, Some(instance));
        assert_eq!(
            checker.store().symbol(formal_owner).unwrap().parent(),
            Some(class_owner)
        );
        assert_eq!(
            checker.store().symbol(method_owner).unwrap().parent(),
            Some(class_owner)
        );
        assert_eq!(
            checker.store().symbol(listener_owner).unwrap().parent(),
            None
        );
        assert_ne!(arrow_owner, method_owner);
        assert_eq!(checker.get_symbol_at_location(nodes.argument), Ok(Some(listener_owner)));
        assert_eq!(checker.get_type_at_location(nodes.argument), Ok(formal_type));
        assert_eq!(
            checker.store().value_symbol_links(listener_owner).unwrap().resolved_type,
            Some(formal_type)
        );
        let bound = checker.file(FILE).unwrap().1;
        assert_eq!(bound.container(nodes.parameter), Some(nodes.method));
        assert_eq!(bound.container(nodes.argument), Some(nodes.arrow));
        for receiver in nodes.receivers {
            assert_eq!(bound.container(receiver), Some(nodes.arrow));
        }
        let NodeData::TypeParameterDeclaration(parameter) =
            &parsed.arena.get(formal.node).unwrap().data
        else {
            panic!("expected the written class type parameter")
        };
        let constraint = checker
            .get_type_from_type_node(node(parsed, parameter.constraint.unwrap()))
            .unwrap();
        assert_eq!(constraint, global_type(&mut checker, "Function"));
        let listeners = checker.get_type_at_location(nodes.listeners).unwrap();
        let set = global_type(&mut checker, "Set");
        let TypeData::TypeReference(reference) =
            checker.store().type_payload(listeners).unwrap().data()
        else {
            panic!("expected the real Set<TListener> reference")
        };
        assert_eq!(reference.object.target, Some(set));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[formal_type][..])
        );
        let annotation = checker.get_type_from_type_node(nodes.annotation).unwrap();
        let annotation_signature = signature(&checker, annotation);
        assert_eq!(checker.get_return_type_of_signature(annotation_signature), Ok(void));
        let method_type = checker.get_type_at_location(nodes.method).unwrap();
        let method_signature = resolved_signature(&checker, nodes.method);
        assert_eq!(checker.get_return_type_of_signature(method_signature), Ok(annotation));
        let method_record = checker.store().signature(method_signature).unwrap();
        assert_eq!(method_record.declaration(), Some(nodes.method));
        assert_eq!(method_record.parameters(), [listener_owner]);
        assert!(method_record.type_parameters().is_empty());
        let arrow_signature = signature(&checker, arrow_type);
        assert_eq!(checker.get_return_type_of_signature(arrow_signature), Ok(void));
        let arrow_record = checker.store().signature(arrow_signature).unwrap();
        assert_eq!(arrow_record.declaration(), Some(nodes.arrow));
        assert!(arrow_record.parameters().is_empty());
        assert!(arrow_record.type_parameters().is_empty());
        assert_eq!(arrow_record.min_argument_count(), 0);
        assert_ne!(arrow_type, annotation);
        assert_ne!(arrow_signature, annotation_signature);
        assert_eq!(
            checker.store().type_payload(arrow_type).unwrap().symbol(),
            Some(arrow_owner)
        );
        let delete_signature = resolved_signature(&checker, nodes.calls[0]);
        let delete_record = checker.store().signature(delete_signature).unwrap();
        assert_ne!(delete_record.declaration().unwrap().file, FILE);
        assert_eq!(delete_record.parameters().len(), 1);
        assert_eq!(delete_record.resolved_return_type(), Some(boolean));
        assert_eq!(
            checker
                .store()
                .value_symbol_links(delete_record.parameters()[0])
                .unwrap()
                .resolved_type,
            Some(formal_type)
        );
        let unsubscribe_signature = resolved_signature(&checker, nodes.calls[1]);
        let unsubscribe_record = checker.store().signature(unsubscribe_signature).unwrap();
        assert_eq!(
            unsubscribe_record.declaration(),
            Some(named(parsed, SyntaxKind::MethodDeclaration, "onUnsubscribe"))
        );
        assert!(unsubscribe_record.parameters().is_empty());
        assert_eq!(unsubscribe_record.resolved_return_type(), Some(void));
        let locations = [
            (nodes.method, method_type),
            (nodes.arrow, arrow_type),
            (nodes.argument, formal_type),
            (nodes.listeners, listeners),
            (nodes.receivers[0], this_type),
            (nodes.receivers[1], this_type),
            (nodes.calls[0], boolean),
            (nodes.calls[1], void),
        ];
        for &(location, expected) in &locations {
            assert_eq!(checker.get_type_at_location(location), Ok(expected));
        }
        replay(
            &mut checker,
            &locations,
            &[(nodes.argument, listener_owner)],
            &[
                (arrow_signature, void),
                (annotation_signature, void),
                (method_signature, annotation),
                (delete_signature, boolean),
                (unsubscribe_signature, void),
            ],
        );
    }
}

#[test]
fn returned_class_arrow_keeps_native_argument_return_and_scope_errors() {
    let source = SUBSCRIBABLE
        .replacen("this.listeners.delete(listener)", "this.listeners.delete(1)", 1)
        .replacen(
            "subscribe(listener: TListener): () => void",
            "subscribe(listener: TListener): () => number",
            1,
        )
        + "const escaped = listener;\n";
    let fixture = Fixture::new(&source);
    let parsed = &fixture.source;
    let nodes = body_nodes(parsed);
    let escaped = named(parsed, SyntaxKind::VariableDeclaration, "escaped");
    let NodeData::VariableDeclaration(escaped) = &parsed.arena.get(escaped.node).unwrap().data
    else {
        unreachable!()
    };
    let escaped_read = node(parsed, escaped.initializer.unwrap());
    for query_first in [false, true] {
        let mut checker = fixture.context();
        let early = query_first.then(|| checker.get_type_at_location(nodes.arrow).unwrap());
        checker.check_source_file(FILE).unwrap();
        let arrow_type = checker.get_type_at_location(nodes.arrow).unwrap();
        if let Some(early) = early {
            assert_eq!(arrow_type, early);
        }
        assert_eq!(
            checker.diagnostics().as_slice().len(),
            3,
            "{:?}",
            checker.diagnostics()
        );
        assert_diagnostic(&checker, 2345, nodes.argument);
        assert_diagnostic(&checker, 2322, nodes.returned);
        assert_diagnostic(&checker, 2304, escaped_read);
        let void = checker.store().intrinsic_bootstrap().unwrap().void_type;
        let boolean = checker.store().intrinsic_bootstrap().unwrap().boolean_type;
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let annotation = checker.get_type_from_type_node(nodes.annotation).unwrap();
        let annotation_signature = signature(&checker, annotation);
        assert_eq!(checker.get_return_type_of_signature(annotation_signature), Ok(number));
        let arrow_signature = signature(&checker, arrow_type);
        assert_eq!(checker.get_return_type_of_signature(arrow_signature), Ok(void));
        assert_eq!(checker.get_type_at_location(nodes.calls[0]), Ok(boolean));
        assert_eq!(checker.get_type_at_location(nodes.calls[1]), Ok(void));
        assert_eq!(checker.get_symbol_at_location(escaped_read), Ok(None));
        replay(
            &mut checker,
            &[
                (nodes.arrow, arrow_type),
                (nodes.calls[0], boolean),
                (nodes.calls[1], void),
            ],
            &[],
            &[(arrow_signature, void), (annotation_signature, number)],
        );
        assert_eq!(checker.get_symbol_at_location(escaped_read), Ok(None));
    }
}
