use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SignatureLinks, SourceCheckError, SourceFileLinks, SourceFunctionUnsupported, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(286_200);
const FILE: FileId = FileId::new(286_201);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'a>(library: &'a ParseResult, parsed: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, parsed, "\"/captured-methods.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, source, path, library) in &files {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for &(file, source, _, _) in &files {
        binder
            .bind_typescript_declaration_slice(&source.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, source, _, _)| (file, &source.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn variable(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut declarations = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, id))
    });
    let result = declarations.next().expect("the actual local must exist");
    assert!(declarations.next().is_none(), "duplicate local {expected}");
    result
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    let declaration = variable(parsed, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    node(parsed, variable.initializer.unwrap())
}

fn method(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut methods = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::MethodDeclaration(method) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data else {
            return None;
        };
        if name.text != expected {
            return None;
        }
        assert_eq!(record.kind, SyntaxKind::MethodDeclaration);
        assert_eq!(
            parsed.arena.get(record.parent.unwrap()).unwrap().kind,
            SyntaxKind::ObjectLiteralExpression
        );
        Some(node(parsed, id))
    });
    let result = methods.next().expect("the actual object method must exist");
    assert!(methods.next().is_none(), "duplicate method {expected}");
    result
}

fn method_body(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    node(parsed, method.body.unwrap())
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_read(
    checker: &mut CanonicalCheckerContext<'_>,
    location: NodeRef,
    expected: TypeId,
    owner: SemanticSymbolId,
) {
    assert_eq!(
        checker
            .store()
            .type_node_links(location)
            .and_then(|links| links.resolved_type),
        Some(expected)
    );
    assert_eq!(checker.get_type_at_location(location), Ok(expected));
    assert_eq!(checker.get_symbol_at_location(location), Ok(Some(owner)));
}

fn assert_method(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
    returned: TypeId,
) -> (TypeId, SignatureId, Vec<SemanticSymbolId>) {
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let owner = symbol(checker, declaration);
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::METHOD);
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));
    let callable = value_type(checker, owner);
    assert_eq!(checker.get_type_at_location(declaration), Ok(callable));
    assert_eq!(
        checker.get_type_at_location(node(parsed, method.name)),
        Ok(callable)
    );
    assert_eq!(
        checker.get_symbol_at_location(node(parsed, method.name)),
        Ok(Some(owner))
    );
    let signature = checker
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = checker.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the source method must have its own callable object")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    let parameters = method
        .parameters
        .nodes
        .iter()
        .map(|&parameter| symbol(checker, node(parsed, parameter)))
        .collect::<Vec<_>>();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), parameters);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(
        checker.get_return_type_of_signature(signature),
        Ok(returned)
    );
    (callable, signature, parameters)
}

#[derive(Clone, Copy)]
struct Assignment {
    statement: NodeRef,
    expression: NodeRef,
    target: NodeRef,
    value: NodeRef,
}

fn assignment(parsed: &ParseResult, declaration: NodeRef) -> Assignment {
    let body = method_body(parsed, declaration);
    let NodeData::Block(body) = &parsed.arena.get(body.node).unwrap().data else {
        unreachable!()
    };
    let mut assignments = body.statements.nodes.iter().filter_map(|&statement| {
        let NodeData::ExpressionStatement(expression) = &parsed.arena.get(statement)?.data else {
            return None;
        };
        let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.expression)?.data
        else {
            return None;
        };
        assert_eq!(
            parsed.arena.get(binary.operator_token).unwrap().kind,
            SyntaxKind::EqualsToken
        );
        Some(Assignment {
            statement: node(parsed, statement),
            expression: node(parsed, expression.expression),
            target: node(parsed, binary.left),
            value: node(parsed, binary.right),
        })
    });
    let result = assignments
        .next()
        .expect("the real method write must exist");
    assert!(assignments.next().is_none());
    result
}

fn assert_capture_flow(
    checker: &CanonicalCheckerContext<'_>,
    local: NodeRef,
    method: NodeRef,
    assignment: Assignment,
) {
    let bound = checker.file(FILE).unwrap().1;
    let outer = bound.container(local).unwrap();
    assert_ne!(outer, method);
    assert_eq!(bound.container(assignment.target), Some(method));
    assert_eq!(bound.flow_container(assignment.target), Some(method));
    assert_eq!(bound.flow_container(assignment.statement), Some(method));
    let graph = bound.flow_graph();
    assert!(graph.container_start(method).is_some());
    assert!(graph.container_end(method).is_some());
    assert_ne!(graph.container_start(method), graph.container_start(outer));
    assert_eq!(
        graph
            .nodes()
            .iter()
            .filter(|row| {
                row.flags.contains(FlowFlags::ASSIGNMENT)
                    && row.payload == Some(FlowNodePayload::Ast(assignment.target))
            })
            .count(),
        1
    );
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    source: Option<SourceFileLinks>,
}

fn publication(checker: &CanonicalCheckerContext<'_>) -> Publication {
    let store = checker.store();
    let arena = checker.file(FILE).unwrap().0;
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(arena.id(), FILE, id);
                NodeState {
                    node,
                    type_: store.type_node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
            })
            .collect(),
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        source: store
            .source_file_links(checker.source_file(FILE).unwrap())
            .cloned(),
    }
}

fn assert_replay(checker: &mut CanonicalCheckerContext<'_>, locations: &[NodeRef]) {
    let expected = locations
        .iter()
        .map(|&location| {
            (
                checker.get_type_at_location(location).unwrap(),
                checker.get_symbol_at_location(location).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let before = publication(checker);
    let diagnostics = checker.diagnostics().clone();
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for (&location, &(type_, symbol)) in locations.iter().zip(&expected) {
            assert_eq!(checker.get_type_at_location(location), Ok(type_));
            assert_eq!(checker.get_symbol_at_location(location), Ok(symbol));
        }
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(publication(checker), before);
    }
}

#[test]
fn returned_object_methods_capture_the_real_iife_callable_local() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "declare const isServer: boolean;\n",
        "export type IsServerValue = () => boolean;\n",
        "export const environmentManager = (() => {\n",
        "  let isServerFn: IsServerValue = () => isServer;\n",
        "  return {\n",
        "    isServer(): boolean { return isServerFn(); },\n",
        "    setIsServer(isServerValue: IsServerValue): void { isServerFn = isServerValue; }\n",
        "  };\n",
        "})();\n",
    ));
    let setter = method(&parsed, "setIsServer");
    let getter = method(&parsed, "isServer");
    let local = variable(&parsed, "isServerFn");
    let write = assignment(&parsed, setter);
    for source_first in [false, true] {
        let mut checker = context(&library, &parsed);
        assert!(checker.store().signature_links(setter).is_none());
        if source_first {
            checker.check_source_file(FILE).unwrap();
        } else {
            checker.get_type_at_location(setter).unwrap();
        }
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let (boolean, void) = (bootstrap.boolean_type, bootstrap.void_type);
        let local_owner = symbol(&checker, local);
        let declared = value_type(&checker, local_owner);
        let (_, _, parameters) = assert_method(&mut checker, &parsed, setter, void);
        let [parameter] = parameters.as_slice() else {
            panic!("the setter keeps its parameter")
        };
        assert_ne!(*parameter, local_owner);
        assert_eq!(value_type(&checker, *parameter), declared);
        assert_read(&mut checker, write.target, declared, local_owner);
        assert_read(&mut checker, write.value, declared, *parameter);
        assert_eq!(checker.get_type_at_location(write.expression), Ok(declared));
        assert_method(&mut checker, &parsed, getter, boolean);
        assert_capture_flow(&checker, local, setter, write);
        let outer = checker.file(FILE).unwrap().1.container(local).unwrap();
        assert_eq!(
            parsed.arena.get(outer.node).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
        assert_replay(
            &mut checker,
            &[setter, getter, write.target, write.value, write.expression],
        );
    }
}

#[test]
fn method_capture_uses_declared_entry_type_without_running_the_outer_write() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "export function make(seed: number): number {\n",
        "  let current: number | string = seed;\n",
        "  const before = current;\n",
        "  const object = {\n",
        "    write(next: string): void {\n",
        "      const entry = current;\n",
        "      current = next;\n",
        "      const written = current;\n",
        "    },\n",
        "    shadow(current: string): void { current = 'shadow'; }\n",
        "  };\n",
        "  const after = current;\n",
        "  return after;\n",
        "}\n",
    ));
    let mut checker = context(&library, &parsed);
    checker.check_source_file(FILE).unwrap();
    assert!(
        checker.diagnostics().is_empty(),
        "{:?}",
        checker.diagnostics()
    );
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, string, void) = (
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.void_type,
    );
    let local = variable(&parsed, "current");
    let owner = symbol(&checker, local);
    let declared = value_type(&checker, owner);
    let TypeData::Union(union) = checker.store().type_payload(declared).unwrap().data() else {
        panic!("the captured declaration must keep its real union")
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&number));
    assert!(union.union.types.contains(&string));
    let before = initializer(&parsed, "before");
    let after = initializer(&parsed, "after");
    let entry = initializer(&parsed, "entry");
    let written = initializer(&parsed, "written");
    assert_read(&mut checker, before, number, owner);
    assert_read(&mut checker, after, number, owner);
    assert_read(&mut checker, entry, declared, owner);
    assert_read(&mut checker, written, string, owner);
    let writer = method(&parsed, "write");
    let write = assignment(&parsed, writer);
    let (_, _, parameters) = assert_method(&mut checker, &parsed, writer, void);
    assert_eq!(parameters.len(), 1);
    assert_read(&mut checker, write.target, declared, owner);
    assert_read(&mut checker, write.value, string, parameters[0]);
    assert_capture_flow(&checker, local, writer, write);
    let shadow = method(&parsed, "shadow");
    let shadow_write = assignment(&parsed, shadow);
    let (_, _, parameters) = assert_method(&mut checker, &parsed, shadow, void);
    assert_eq!(parameters.len(), 1);
    assert_ne!(parameters[0], owner);
    assert_read(&mut checker, shadow_write.target, string, parameters[0]);
    assert_eq!(
        checker.file(FILE).unwrap().1.container(shadow_write.target),
        Some(shadow)
    );
    assert_eq!(value_type(&checker, owner), declared);
    assert_replay(
        &mut checker,
        &[
            writer,
            shadow,
            before,
            after,
            entry,
            written,
            write.target,
            write.value,
            write.expression,
            shadow_write.target,
        ],
    );
}

#[test]
fn incompatible_captured_method_assignment_keeps_the_actual_diagnostic_and_types() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "export function make(seed: number): number {\n",
        "  let current: number = seed;\n",
        "  const object = { write(next: string): void { current = next; } };\n",
        "  return current;\n",
        "}\n",
    ));
    let mut checker = context(&library, &parsed);
    checker.check_source_file(FILE).unwrap();
    let writer = method(&parsed, "write");
    let write = assignment(&parsed, writer);
    let diagnostics = checker.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(write.target));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(diagnostic.related_information.is_empty());
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, string, void) = (
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.void_type,
    );
    let local = variable(&parsed, "current");
    let owner = symbol(&checker, local);
    let (_, _, parameters) = assert_method(&mut checker, &parsed, writer, void);
    assert_eq!(parameters.len(), 1);
    assert_read(&mut checker, write.target, number, owner);
    assert_read(&mut checker, write.value, string, parameters[0]);
    assert_eq!(checker.get_type_at_location(write.expression), Ok(string));
    assert_eq!(value_type(&checker, owner), number);
    assert_capture_flow(&checker, local, writer, write);
    assert_replay(
        &mut checker,
        &[writer, write.target, write.value, write.expression],
    );
}

#[test]
fn const_outer_binding_stays_outside_the_mutable_capture_path() {
    let library = parse_source_file(ES5);
    let parsed = parse_source_file(concat!(
        "export function make(seed: number): number {\n",
        "  const current: number = seed;\n",
        "  const object = { write(next: number): void { current = next; } };\n",
        "  return current;\n",
        "}\n",
    ));
    let writer = method(&parsed, "write");
    let body = method_body(&parsed, writer);
    let mut checker = context(&library, &parsed);
    for _ in 0..2 {
        assert!(matches!(checker.check_source_file(FILE),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                SourceFunctionUnsupported::FunctionBody(node)
            ))) if node == body));
        assert!(checker.diagnostics().is_empty());
        assert!(checker.store().signature_links(writer).is_none());
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
}
