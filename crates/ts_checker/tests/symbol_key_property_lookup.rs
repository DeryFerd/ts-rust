use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/property-keys.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

#[test]
fn source_reads_keep_inherited_property_and_type_identity() {
    for (index, source) in [
        concat!(
            "interface Base { value: number }\n",
            "interface Item extends Base { readonly own: string }\n",
            "declare const item: Item;\n",
            "const result = item.value;\n",
        ),
        concat!(
            "interface Base<T> { value: T }\n",
            "interface Item<T> extends Base<T> { readonly own: string }\n",
            "declare const item: Item<number>;\n",
            "const result = item.value;\n",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(4_160 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let (access, receiver) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::PropertyAccessExpression(access) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, access.expression),
                ))
            })
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_at_location(access).unwrap(), number);
        let selected = context.get_symbol_at_location(access).unwrap().unwrap();
        let receiver_type = context.get_type_at_location(receiver).unwrap();
        let members = context
            .store()
            .type_payload(receiver_type)
            .and_then(|record| match record.data() {
                TypeData::Interface(interface) => Some(&interface.reference.object.structured),
                TypeData::TypeReference(reference) => Some(&reference.object.structured),
                _ => None,
            })
            .and_then(|members| members.members)
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(members)
                .unwrap()
                .get_source("value"),
            Some(selected),
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(selected)
                .and_then(|links| links.resolved_type),
            Some(number),
        );
        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().mapper_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        );
        assert_eq!(context.get_type_at_location(access).unwrap(), number);
        assert_eq!(
            context.get_symbol_at_location(access).unwrap(),
            Some(selected)
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().mapper_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
            ),
            warm,
        );
    }
}
