use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_813);
const SOURCE: &str = r#"
interface InvalidDefault<A> {
  <B extends string = number>(value: B): B;
}
interface ValidDefault<A> {
  <B extends A = A>(value: B): B;
}
"#;

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-interface-call-defaults.ts\""),
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

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

#[test]
#[allow(clippy::too_many_lines)] // Compare real default diagnostics, formal owners, and both entry orders.
fn generic_interface_call_defaults_use_written_constraints_and_replay() {
    let parsed = parse_source_file(SOURCE);
    let interfaces = nodes(&parsed, SyntaxKind::InterfaceDeclaration);
    let calls = nodes(&parsed, SyntaxKind::CallSignature);
    let formals = nodes(&parsed, SyntaxKind::TypeParameter);
    let parameters = nodes(&parsed, SyntaxKind::Parameter);
    assert_eq!(interfaces.len(), 2);
    assert_eq!(calls.len(), 2);
    assert_eq!(formals.len(), 4);
    assert_eq!(parameters.len(), 2);
    let annotations = calls
        .iter()
        .enumerate()
        .map(|(index, call)| {
            let NodeData::CallSignatureDeclaration(call) =
                &parsed.arena.get(call.node).unwrap().data
            else {
                panic!("expected a source call signature")
            };
            let NodeData::TypeParameterDeclaration(formal) =
                &parsed.arena.get(formals[index * 2 + 1].node).unwrap().data
            else {
                panic!("expected the call's own type parameter")
            };
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(parameters[index].node).unwrap().data
            else {
                panic!("expected the call's value parameter")
            };
            [
                formal.constraint.unwrap(),
                formal.default_type.unwrap(),
                parameter.type_.unwrap(),
                call.type_.unwrap(),
            ]
            .map(|node| NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .collect::<Vec<_>>();

    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            for (index, annotation) in annotations.iter().enumerate() {
                let result = context.get_type_from_type_node(annotation[3]).unwrap();
                assert_eq!(
                    context.store().type_payload(result).unwrap().symbol(),
                    Some(symbol(&context, formals[index * 2 + 1])),
                );
                assert!(context.diagnostics().is_empty());
            }
        }
        context.check_source_file(FILE).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected only the invalid written default diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2344);
        assert_eq!(diagnostic.node, Some(annotations[0][1]));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' does not satisfy the constraint 'string'.",
        );
        assert_eq!(
            parsed.arena.get(annotations[0][1].node).unwrap().kind,
            SyntaxKind::NumberKeyword,
        );

        let mut declared = Vec::new();
        let mut signatures = Vec::new();
        let mut queries = Vec::new();
        for index in 0..2 {
            for (child, parent) in [
                (calls[index], interfaces[index]),
                (formals[index * 2], interfaces[index]),
                (formals[index * 2 + 1], calls[index]),
                (parameters[index], calls[index]),
            ] {
                assert_eq!(
                    parsed.arena.get(child.node).unwrap().parent,
                    Some(parent.node)
                );
            }
            let owners = [
                interfaces[index],
                formals[index * 2],
                formals[index * 2 + 1],
            ]
            .map(|node| symbol(&context, node));
            let [interface, outer, inner] = owners.map(|owner| {
                context
                    .store()
                    .declared_type_links(owner)
                    .unwrap()
                    .declared_type
                    .unwrap()
            });
            assert_ne!(owners[1], owners[2]);
            assert_ne!(outer, inner);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let [constraint, default_type] = if index == 0 {
                [bootstrap.string_type, bootstrap.number_type]
            } else {
                [outer, outer]
            };
            let inner_record = context.store().type_payload(inner).unwrap();
            let TypeData::TypeParameter(inner_data) = inner_record.data() else {
                panic!("the call formal must retain its own canonical type")
            };
            assert_eq!(inner_record.symbol(), Some(owners[2]));
            assert_eq!(inner_data.constraint, Some(constraint));
            assert_eq!(inner_data.resolved_default_type, Some(default_type));
            assert!(!inner_data.is_this_type);
            assert_eq!(inner_data.target, None);
            assert_eq!(inner_data.mapper, None);
            let signature = context
                .store()
                .signature_links(calls[index])
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            let record = context.store().signature(signature).unwrap();
            let parameter_owner = symbol(&context, parameters[index]);
            assert_eq!(record.declaration(), Some(calls[index]));
            assert_eq!(record.type_parameters(), [inner]);
            assert_eq!(record.parameters(), [parameter_owner]);
            assert_eq!(record.resolved_return_type(), Some(inner));
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter_owner)
                    .unwrap()
                    .resolved_type,
                Some(inner),
            );
            let TypeData::Interface(interface_data) =
                context.store().type_payload(interface).unwrap().data()
            else {
                panic!("expected the source interface's canonical type")
            };
            assert!(interface_data.declared_members_resolved);
            assert_eq!(
                interface_data.declared_call_signatures.as_deref(),
                Some(&[signature][..])
            );
            declared.extend(owners.into_iter().zip([interface, outer, inner]));
            signatures.push((calls[index], signature, inner));
            queries.extend(annotations[index].into_iter().zip([
                constraint,
                default_type,
                inner,
                inner,
            ]));
        }
        assert_ne!(declared[1].1, declared[4].1);
        assert_ne!(declared[2].1, declared[5].1);
        assert_ne!(signatures[0].1, signatures[1].1);

        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                context.diagnostics().clone(),
                store
                    .types()
                    .filter_map(|(id, record)| match record.data() {
                        TypeData::TypeParameter(data) => Some((id, record.symbol(), data.clone())),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
                store
                    .signatures()
                    .map(|(id, record)| {
                        (
                            id,
                            record.declaration(),
                            record.type_parameters().to_vec(),
                            record.parameters().to_vec(),
                            record.resolved_return_type(),
                            record.target(),
                            record.mapper(),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        };
        let warm = snapshot(&context);
        for _ in 0..2 {
            for &(node, expected) in &queries {
                assert_eq!(context.get_type_from_type_node(node), Ok(expected));
            }
            for &(owner, expected) in &declared {
                assert_eq!(context.get_declared_type_of_symbol(owner), Ok(expected));
            }
            for &(node, signature, inner) in &signatures {
                assert_eq!(context.get_return_type_of_signature(signature), Ok(inner));
                assert_eq!(
                    context
                        .store()
                        .signature_links(node)
                        .unwrap()
                        .resolved_signature
                        .signature(),
                    Some(signature),
                );
            }
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(snapshot(&context), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}
