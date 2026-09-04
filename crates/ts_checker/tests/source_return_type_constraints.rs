use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(3);

struct Fixture {
    files: [ParseResult; 4],
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            files: [
                parse_source_file(include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
                parse_source_file(include_str!("../../ts_bundled/libs/lib.decorators.d.ts")),
                parse_source_file(include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts")),
                parse_source_file(source),
            ],
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let paths = [
            "/lib.es5.d.ts", "/lib.decorators.d.ts",
            "/lib.decorators.legacy.d.ts", "/return-type-controls.ts",
        ];
        let mut binder = CanonicalBinder::new();
        for (index, parsed) in self.files.iter().enumerate() {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder.bind_source_file_with_facts(
                &parsed.arena, parsed.source_file, FileId::new(index as u32),
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(paths[index]),
                    CanonicalSourceLanguage::TypeScript, index != 3, index != 3,
                    if index == 3 { CanonicalModuleState::External }
                    else { CanonicalModuleState::Script },
                ),
            ).unwrap();
        }
        for (index, parsed) in self.files.iter().enumerate() {
            binder.bind_typescript_declaration_slice(
                &parsed.arena, FileId::new(index as u32),
            ).unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            self.files.iter().enumerate()
                .map(|(index, parsed)| (FileId::new(index as u32), &parsed.arena))
                .collect::<Vec<_>>(),
            CanonicalCheckerOptions {
                strict_function_types: true,
                no_implicit_any: true,
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        ).unwrap()
    }

    fn nodes(&self, kind: SyntaxKind) -> Vec<NodeRef> {
        let parsed = &self.files[3];
        let mut nodes = parsed.arena.iter().filter_map(|(id, node)| {
            (node.kind == kind).then_some(NodeRef::new(parsed.arena.id(), SOURCE, id))
        }).collect::<Vec<_>>();
        nodes.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
        nodes
    }

    fn alias(&self, name: &str) -> (NodeRef, NodeRef) {
        let parsed = &self.files[3];
        self.nodes(SyntaxKind::TypeAliasDeclaration).into_iter().find_map(|node| {
            let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(node.node)?.data
            else { return None };
            let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data
            else { return None };
            (identifier.text == name).then_some((
                node, NodeRef::new(node.arena, node.file, alias.type_),
            ))
        }).unwrap_or_else(|| panic!("missing alias {name}"))
    }

    fn state(&self, context: &CanonicalCheckerContext<'_>)
        -> impl std::fmt::Debug + PartialEq + use<>
    {
        let store = context.store();
        (
            [store.type_len(), store.symbol_len(), store.signature_len(), store.mapper_len()],
            context.diagnostics().clone(), store.relation_state_snapshot(),
            self.files[3].arena.iter().map(|(id, _)| {
                let node = NodeRef::new(self.files[3].arena.id(), SOURCE, id);
                (store.type_node_links(node).cloned(),
                 store.signature_links(node).cloned(),
                 store.symbol_node_links(node).cloned())
            }).collect::<Vec<_>>(),
        )
    }
}

fn owner(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signatures(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<SignatureId> {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data()
    else { panic!("expected a callable object") };
    object.structured.signatures.as_deref().unwrap().to_vec()
}

fn assert_function(context: &mut CanonicalCheckerContext<'_>, type_: TypeId,
                   first: TypeId, second: TypeId, returned: TypeId) {
    let ids = signatures(context, type_);
    assert_eq!(ids.len(), 1);
    let signature = context.store().signature(ids[0]).unwrap();
    assert_eq!(signature.min_argument_count(), 2);
    assert!(!signature.has_rest_parameter());
    let parameters = signature.parameters().to_vec();
    assert_eq!(parameters.len(), 2);
    let values = parameters.iter().map(|&parameter| {
        context.store().value_symbol_links(parameter).unwrap().resolved_type.unwrap()
    }).collect::<Vec<_>>();
    assert_eq!(values, [first, second]);
    assert_eq!(context.get_return_type_of_signature(ids[0]), Ok(returned));
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>) {
    for index in 0..4 {
        let file = context.source_file(FileId::new(index)).unwrap();
        assert!(!context.store().source_file_links(file).is_some_and(|links| links.type_checked));
    }
}

#[test]
fn ordinary_function_constraints_capture_formals_and_report_invalid_arguments() {
    let fixture = Fixture::new(concat!(
        "export {};\n",
        "type Keep<F extends (value: number, flag: boolean) => string> = F;\n",
        "type Capture<A, F extends (value: A, flag: boolean) => A> = F;\n",
        "type Plain = Keep<(value: number, flag: boolean) => string>;\n",
        "type Captured = Capture<string, (value: string, flag: boolean) => string>;\n",
        "type Bad = Keep<number>;\n",
    ));
    let parsed = &fixture.files[3];
    let (capture, _) = fixture.alias("Capture");
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(capture.node).unwrap().data
    else { panic!("expected Capture") };
    let parameters = &alias.type_parameters.as_ref().unwrap().nodes;
    assert_eq!(parameters.len(), 2);
    let a_node = NodeRef::new(capture.arena, SOURCE, parameters[0]);
    let f_node = NodeRef::new(capture.arena, SOURCE, parameters[1]);
    let NodeData::TypeParameterDeclaration(f) = &parsed.arena.get(f_node.node).unwrap().data
    else { panic!("expected F") };
    let constraint = NodeRef::new(capture.arena, SOURCE, f.constraint.unwrap());
    assert_eq!(parsed.arena.get(constraint.node).unwrap().kind, SyntaxKind::FunctionType);
    let plain = fixture.alias("Plain").1;
    let captured = fixture.alias("Captured").1;
    let bad = fixture.alias("Bad").1;
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(bad.node).unwrap().data
    else { panic!("expected Keep<number>") };
    let bad_argument = NodeRef::new(bad.arena, SOURCE,
        reference.type_arguments.as_ref().unwrap().nodes[0]);

    for query_first in [false, true] {
        let mut context = fixture.context();
        let early = query_first.then(|| {
            let result = context.get_type_from_type_node(constraint).unwrap();
            assert_unchecked(&context);
            assert!(context.diagnostics().is_empty());
            result
        });
        context.check_source_file(SOURCE).unwrap();
        let a_owner = owner(&context, a_node);
        let f_owner = owner(&context, f_node);
        let a = context.get_declared_type_of_symbol(a_owner).unwrap();
        let f = context.get_declared_type_of_symbol(f_owner).unwrap();
        let constraint_type = context.get_type_from_type_node(constraint).unwrap();
        assert!(early.is_none_or(|early| early == constraint_type));
        let TypeData::TypeParameter(formal) = context.store().type_payload(f).unwrap().data()
        else { panic!("F must remain a declared parameter") };
        assert_eq!(formal.constraint, Some(constraint_type));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, boolean, string) =
            (bootstrap.number_type, bootstrap.boolean_type, bootstrap.string_type);
        assert_function(&mut context, constraint_type, a, boolean, a);
        let plain_type = context.get_type_from_type_node(plain).unwrap();
        let captured_type = context.get_type_from_type_node(captured).unwrap();
        assert_function(&mut context, plain_type, number, boolean, string);
        assert_function(&mut context, captured_type, string, boolean, string);
        // Instantiating Capture<string, ...> must not overwrite the stored A constraint.
        assert_function(&mut context, constraint_type, a, boolean, a);
        let [diagnostic] = context.diagnostics().as_slice() else { panic!("one TS2344 required") };
        assert_eq!(diagnostic.node, Some(bad_argument));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.code(), 2344);
        assert_eq!(diagnostic.diagnostic.arguments,
            ["number", "(value: number, flag: boolean) => string"]);
        assert_eq!(diagnostic.diagnostic.render().unwrap(),
            "Type 'number' does not satisfy the constraint '(value: number, flag: boolean) => string'.");
        let before = fixture.state(&context);
        for _ in 0..2 {
            context.recheck_source_file(SOURCE).unwrap();
            for (node, expected) in [(constraint, constraint_type), (plain, plain_type), (captured, captured_type)] {
                assert_eq!(context.get_type_from_type_node(node), Ok(expected));
            }
            assert_function(&mut context, constraint_type, a, boolean, a);
            assert_eq!(fixture.state(&context), before);
        }
    }
}

fn check_return_type(source: &str, implementation: bool) {
    let fixture = Fixture::new(source);
    let actual = fixture.alias("Actual").1;
    let queries = fixture.nodes(SyntaxKind::TypeQuery);
    assert_eq!(queries.len(), 1);
    let query = queries[0];
    let declarations = fixture.nodes(SyntaxKind::FunctionDeclaration);
    assert_eq!(declarations.len(), if implementation { 3 } else { 2 });
    for query_first in [false, true] {
        let mut context = fixture.context();
        let value_owner = owner(&context, declarations[0]);
        let early = query_first.then(|| {
            let callable = context.get_type_from_type_node(query).unwrap();
            let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
            else { panic!("expected the pending callable") };
            assert!(object.structured.signatures.is_none());
            assert_unchecked(&context);
            let returned = context.get_type_from_type_node(actual).unwrap();
            assert_unchecked(&context);
            assert!(context.diagnostics().is_empty());
            assert_eq!(context.get_type_from_type_node(query), Ok(callable));
            let before = fixture.state(&context);
            assert_eq!(context.get_type_from_type_node(actual), Ok(returned));
            assert_eq!(fixture.state(&context), before);
            (callable, returned)
        });
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string) = (bootstrap.number_type, bootstrap.string_type);
        let callable = context.get_type_from_type_node(query).unwrap();
        let returned = context.get_type_from_type_node(actual).unwrap();
        assert_eq!(returned, string);
        assert!(early.is_none_or(|early| early == (callable, returned)));
        assert_eq!(context.store().type_payload(callable).unwrap().symbol(), Some(value_owner));
        assert_eq!(context.store().value_symbol_links(value_owner).unwrap().resolved_type, Some(callable));
        let visible = signatures(&context, callable);
        assert_eq!(visible.len(), 2);
        for (index, &signature) in visible.iter().enumerate() {
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(declarations[index]));
            assert_eq!(record.min_argument_count(), [1, 2][index]);
            assert_eq!(record.parameters().len(), [1, 2][index]);
            assert_eq!(context.get_return_type_of_signature(signature), Ok([number, string][index]));
        }
        if implementation {
            let signature = context.store().signature_links(declarations[2]).unwrap()
                .resolved_signature.signature().unwrap();
            assert!(!visible.contains(&signature));
            let implementation_return = context.get_return_type_of_signature(signature).unwrap();
            assert_ne!(implementation_return, returned);
            let TypeData::Union(union) = context.store().type_payload(implementation_return).unwrap().data()
            else { panic!("implementation retains its broader union return") };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&number) && union.union.types.contains(&string));
        }
        let before = fixture.state(&context);
        for _ in 0..2 {
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(context.get_type_from_type_node(actual), Ok(returned));
            assert_eq!(context.get_type_from_type_node(query), Ok(callable));
            assert_eq!(signatures(&context, callable), visible);
            assert_eq!(fixture.state(&context), before);
        }
    }
}

#[test]
fn return_type_demands_the_last_two_required_parameter_overload() {
    check_return_type(concat!(
        "export declare function pick(value: string): number;\n",
        "export declare function pick(value: number, flag: boolean): string;\n",
        "type Actual = ReturnType<typeof pick>;\n",
    ), false);
}

#[test]
fn return_type_accepts_required_parameters_and_preserves_the_return() {
    let fixture = Fixture::new(concat!(
        "export {};\n",
        "type Actual = ReturnType<(value: number, flag: boolean) => string>;\n",
        "type Scalar = ReturnType<(...args: any) => number>;\n",
    ));
    let actual = fixture.alias("Actual").1;
    let scalar = fixture.alias("Scalar").1;
    for query_first in [false, true] {
        let mut context = fixture.context();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        if query_first {
            assert_eq!(context.get_type_from_type_node(actual), Ok(string));
            assert_eq!(context.get_type_from_type_node(scalar), Ok(number));
            assert_unchecked(&context);
        }
        context.check_source_file(SOURCE).unwrap();
        assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
        assert_eq!(context.get_type_from_type_node(actual), Ok(string));
        assert_eq!(context.get_type_from_type_node(scalar), Ok(number));
        let before = fixture.state(&context);
        for _ in 0..2 {
            context.recheck_source_file(SOURCE).unwrap();
            assert_eq!(context.get_type_from_type_node(actual), Ok(string));
            assert_eq!(context.get_type_from_type_node(scalar), Ok(number));
            assert_eq!(fixture.state(&context), before);
        }
    }
}

#[test]
fn return_type_excludes_the_implementation_signature() {
    check_return_type(concat!(
        "export function pick(value: string): number;\n",
        "export function pick(value: number, flag: boolean): string;\n",
        "export function pick(value: string | number, flag?: boolean): string | number { return 0; }\n",
        "type Actual = ReturnType<typeof pick>;\n",
    ), true);
}
