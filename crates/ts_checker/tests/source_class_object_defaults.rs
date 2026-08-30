use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(8_320);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-object-defaults.ts\""),
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
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn class_owner(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> (SemanticSymbolId, Vec<NodeRef>) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(class.name?)?.data else {
                return None;
            };
            if identifier.text != name {
                return None;
            }
            let declaration = NodeRef::new(parsed.arena.id(), FILE, node);
            let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
            let owner = context.store().get_merged_symbol(raw).unwrap();
            let parameters = class
                .type_parameters
                .as_ref()
                .unwrap()
                .nodes
                .iter()
                .map(|node| NodeRef::new(parsed.arena.id(), FILE, *node))
                .collect();
            Some((owner, parameters))
        })
        .unwrap_or_else(|| panic!("missing class {name}"))
}

fn variable_annotation(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name)
                .then(|| NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing variable {name}"))
}

fn reference_arguments(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    owner: SemanticSymbolId,
) -> Vec<TypeId> {
    let TypeData::TypeReference(reference) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected the instantiated class reference")
    };
    assert_eq!(
        reference.object.target,
        context
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type
    );
    reference.resolved_type_arguments.as_ref().unwrap().clone()
}

#[test]
#[allow(clippy::too_many_lines)] // Source-first, query-first, and replay checks share the same class identities.
fn class_object_defaults_resolve_and_forward_the_actual_type_arguments() {
    let parsed = parse_source_file(concat!(
        "class Store<T = object> {}\n",
        "class Bound<T extends {} = object> {}\n",
        "class Pair<A = object, B = A> {}\n",
        "interface Payload { value: string; }\n",
        "let store: Store; let bound: Bound; let pair: Pair;\n",
        "let explicit: Pair<Payload>;\n",
    ));
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early_references = query_first.then(|| {
            ["store", "bound", "pair", "explicit"].map(|name| {
                let annotation = variable_annotation(&parsed, name);
                let type_ = context.get_type_from_type_node(annotation).unwrap();
                (annotation, type_)
            })
        });
        let early = early_references.as_ref().map(|references| references[0].1);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let object = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .non_primitive_type;
        let mut checked = Vec::new();
        for (name, class, count) in [
            ("store", "Store", 1),
            ("bound", "Bound", 1),
            ("pair", "Pair", 2),
        ] {
            let (owner, parameters) = class_owner(&context, &parsed, class);
            assert_eq!(parameters.len(), count);
            let annotation = variable_annotation(&parsed, name);
            let type_ = context.get_type_from_type_node(annotation).unwrap();
            assert_eq!(
                reference_arguments(&context, type_, owner),
                vec![object; count]
            );
            if name == "store" {
                assert!(early.is_none_or(|early| early == type_));
            }
            for (index, parameter) in parameters.iter().enumerate() {
                let symbol = context.file(FILE).unwrap().1.symbol(*parameter).unwrap();
                let parameter_type = context
                    .store()
                    .declared_type_links(symbol)
                    .unwrap()
                    .declared_type
                    .unwrap();
                let record = context.store().type_payload(parameter_type).unwrap();
                assert_eq!(record.symbol(), Some(symbol));
                let TypeData::TypeParameter(data) = record.data() else {
                    panic!("expected the class's declaration-owned parameter")
                };
                let expected = if index == 0 {
                    object
                } else {
                    let first = context.file(FILE).unwrap().1.symbol(parameters[0]).unwrap();
                    context
                        .store()
                        .declared_type_links(first)
                        .unwrap()
                        .declared_type
                        .unwrap()
                };
                assert_eq!(data.resolved_default_type, Some(expected));
            }
            checked.push((annotation, type_));
        }
        let explicit = variable_annotation(&parsed, "explicit");
        let explicit_type = context.get_type_from_type_node(explicit).unwrap();
        let owner = class_owner(&context, &parsed, "Pair").0;
        let arguments = reference_arguments(&context, explicit_type, owner);
        assert_eq!(arguments.len(), 2);
        assert_eq!(arguments[0], arguments[1]);
        assert_ne!(arguments[0], object);
        let payload = context
            .store()
            .type_payload(arguments[0])
            .unwrap()
            .symbol()
            .unwrap();
        assert_eq!(
            context.store().symbol(payload).unwrap().name().as_utf8(),
            Some("Payload")
        );
        checked.push((explicit, explicit_type));
        if let Some(references) = &early_references {
            assert_eq!(checked.as_slice(), references.as_slice());
        }
        let counts = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
        );
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for (annotation, type_) in &checked {
                assert_eq!(context.get_type_from_type_node(*annotation), Ok(*type_));
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().mapper_len()
                ),
                counts
            );
            assert!(context.diagnostics().is_empty());
        }
    }
}
