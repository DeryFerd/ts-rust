use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_914);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/signature-trailing-commas.ts\""),
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
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), FILE, node),
            ))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

#[allow(clippy::too_many_lines)] // Check source identities, calls and replay for the same signature.
fn check_signature(method: bool) {
    for comma in ["", ","] {
        let member = if method { "run" } else { "" };
        let callee = if method { "call.run" } else { "call" };
        let source = format!(
            "interface Callable<A> {{ {member}<T extends A = A{comma}>(value: T): T; }}\n\
             declare const call: Callable<string>;\n\
             const explicit = {callee}<string>('ok');\n\
             const inferred = {callee}('ok');\n\
             const wrong = {callee}<string>(123);\n"
        );
        let parsed = parse_source_file(&source);
        let kind = if method {
            SyntaxKind::MethodSignature
        } else {
            SyntaxKind::CallSignature
        };
        let declarations = nodes(&parsed, kind);
        assert_eq!(declarations.len(), 1);
        let declaration = declarations[0];
        let (type_parameters, parameters, return_type) =
            match &parsed.arena.get(declaration.node).unwrap().data {
                NodeData::CallSignatureDeclaration(data) => {
                    (&data.type_parameters, &data.parameters, data.type_.unwrap())
                }
                NodeData::MethodSignatureDeclaration(data) => {
                    (&data.type_parameters, &data.parameters, data.type_.unwrap())
                }
                _ => panic!("expected a source signature"),
            };
        let type_parameters = type_parameters.as_ref().unwrap();
        assert_eq!(type_parameters.has_trailing_comma, !comma.is_empty());
        assert_eq!(type_parameters.nodes.len(), 1);
        assert_eq!(parameters.nodes.len(), 1);
        let formals = nodes(&parsed, SyntaxKind::TypeParameter);
        assert_eq!(formals.len(), 2);
        assert_eq!(type_parameters.nodes, [formals[1].node]);
        assert_eq!(
            parsed.arena.get(formals[1].node).unwrap().parent,
            Some(declaration.node)
        );
        let parameter = NodeRef::new(parsed.arena.id(), FILE, parameters.nodes[0]);
        assert_eq!(
            parsed.arena.get(parameter.node).unwrap().parent,
            Some(declaration.node)
        );
        let return_type = NodeRef::new(parsed.arena.id(), FILE, return_type);
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 3);

        for query_first in [false, true] {
            let mut context = context(&parsed);
            if query_first {
                context.get_type_from_type_node(return_type).unwrap();
            }
            context.check_source_file(FILE).unwrap();
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("expected only the invalid argument diagnostic")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Argument of type 'number' is not assignable to parameter of type 'string'."
            );
            let owners = formals
                .iter()
                .map(|&node| symbol(&context, node))
                .collect::<Vec<_>>();
            assert_ne!(owners[0], owners[1]);
            let types = owners
                .iter()
                .map(|&owner| {
                    context
                        .store()
                        .declared_type_links(owner)
                        .unwrap()
                        .declared_type
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert_ne!(types[0], types[1]);
            let record = context.store().type_payload(types[1]).unwrap();
            assert_eq!(record.symbol(), Some(owners[1]));
            let TypeData::TypeParameter(data) = record.data() else {
                panic!("expected the signature's own formal")
            };
            assert_eq!(data.constraint, Some(types[0]));
            assert_eq!(data.resolved_default_type, Some(types[0]));
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            let signature = context
                .store()
                .signature_links(declaration)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(record.type_parameters(), [types[1]]);
            assert_eq!(record.parameters(), [symbol(&context, parameter)]);
            assert_eq!(record.resolved_return_type(), Some(types[1]));
            assert_eq!(context.get_type_from_type_node(return_type), Ok(types[1]));
            let results = calls
                .iter()
                .map(|&call| context.get_type_at_location(call).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(context.type_to_string(results[0]).unwrap(), "string");
            assert_eq!(context.type_to_string(results[1]).unwrap(), "\"ok\"");
            assert_eq!(context.type_to_string(results[2]).unwrap(), "string");
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.diagnostics().clone(),
            );
            for _ in 0..2 {
                context.recheck_source_file(FILE).unwrap();
                for (&call, &expected) in calls.iter().zip(&results) {
                    assert_eq!(context.get_type_at_location(call), Ok(expected));
                }
                assert_eq!(context.get_type_from_type_node(return_type), Ok(types[1]));
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().mapper_len(),
                        context.diagnostics().clone()
                    ),
                    warm
                );
                assert!(context.store().type_resolution_is_empty());
            }
        }
    }
}

#[test]
fn call_signature_trailing_comma_preserves_formals_calls_and_replay() {
    check_signature(false);
}

#[test]
fn method_signature_trailing_comma_preserves_formals_calls_and_replay() {
    check_signature(true);
}

#[test]
fn trailing_comma_keeps_invalid_default_diagnostics() {
    for comma in ["", ","] {
        let source = format!(
            "interface Calls<A> {{ <T extends string = number{comma}>(value: T): T; }}\n\
             interface Methods<A> {{ run<T extends string = number{comma}>(value: T): T; }}"
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let defaults = nodes(&parsed, SyntaxKind::NumberKeyword);
        assert_eq!(defaults.len(), 2);
        assert_eq!(context.diagnostics().as_slice().len(), 2);
        for (diagnostic, &default) in context.diagnostics().as_slice().iter().zip(&defaults) {
            assert_eq!(diagnostic.diagnostic.code(), 2344);
            assert_eq!(diagnostic.node, Some(default));
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' does not satisfy the constraint 'string'."
            );
        }
        let diagnostics = context.diagnostics().clone();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.diagnostics(), &diagnostics);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn trailing_comma_keeps_class_interface_function_and_alias_queries() {
    for comma in ["", ","] {
        let source = format!(
            "declare class Ambient<T{comma}> {{}}\n\
             class Plain<T{comma}> {{}}\n\
             interface Holder<T{comma}> {{ run(value: T): T; }}\n\
             interface Merged<T = string{comma}> {{ first: T; }}\n\
             interface Merged<T = string{comma}> {{ second: T; }}\n\
             type Maybe<T{comma}> = T | undefined;\n\
             type AmbientString = Ambient<string>;\n\
             type PlainString = Plain<string>;\n\
             type MergedDefault = Merged;\n\
             type MaybeString = Maybe<string>;\n\
             function identity<T{comma}>(value: T): T {{ return value; }}\n\
             declare const holder: Holder<string>;\n\
             const method = holder.run('ok');\n\
             const functionResult = identity<string>('ok');\n"
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 2);
        let results = calls
            .iter()
            .map(|&call| context.get_type_at_location(call).unwrap())
            .collect::<Vec<_>>();
        for &result in &results {
            assert_eq!(context.type_to_string(result).unwrap(), "string");
        }
        let aliases = nodes(&parsed, SyntaxKind::TypeAliasDeclaration);
        let declared = aliases
            .iter()
            .map(|&alias| {
                let owner = symbol(&context, alias);
                (owner, context.get_declared_type_of_symbol(owner).unwrap())
            })
            .collect::<Vec<_>>();
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.diagnostics().clone(),
        );
        context.recheck_source_file(FILE).unwrap();
        for (owner, expected) in declared {
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(expected));
        }
        for (&call, expected) in calls.iter().zip(results) {
            assert_eq!(context.get_type_at_location(call), Ok(expected));
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.diagnostics().clone()
            ),
            warm
        );
        assert!(context.store().type_resolution_is_empty());
    }
}
