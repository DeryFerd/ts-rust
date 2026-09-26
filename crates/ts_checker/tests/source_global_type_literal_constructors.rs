use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(284_000);
const AUGMENTATION: FileId = FileId::new(284_001);
const SOURCE: FileId = FileId::new(284_002);

// This authored provider tests the supported path, not the full DOM/Node Response declarations.
const LIBRARY_TEXT: &str = "interface Array<T> {}\n\
interface ReadonlyArray<T> {}\n\
interface NumberResult { value: number; }\n\
interface TextResult { value: string; }\n\
declare var Creator: {\n\
  prototype: NumberResult;\n\
  values: number[];\n\
  new(value?: number): NumberResult;\n\
  new(value?: string): TextResult;\n\
  make(value?: number): NumberResult;\n\
};\n";
const AUGMENTATION_TEXT: &str = "export {};\n\
declare global {\n\
  var Creator: typeof globalThis extends {\n\
    onmessage: any;\n\
    Creator: infer T;\n\
  } ? T : never;\n\
}\n";
const SOURCE_TEXT: &str = "const numeric = new Creator(1);\n\
const textual = new Creator('x');\n\
const omitted = new Creator();\n";

struct Input {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
    library: bool,
    external: bool,
}

fn inputs(augmentation_first: bool) -> Vec<Input> {
    let library = Input {
        file: LIBRARY,
        path: "\"/lib/creator.d.ts\"",
        parsed: parse_source_file(LIBRARY_TEXT),
        library: true,
        external: false,
    };
    let augmentation = Input {
        file: AUGMENTATION,
        path: "\"/types/creator.d.ts\"",
        parsed: parse_source_file(AUGMENTATION_TEXT),
        library: false,
        external: true,
    };
    let mut inputs = if augmentation_first {
        vec![augmentation, library]
    } else {
        vec![library, augmentation]
    };
    inputs.push(Input {
        file: SOURCE,
        path: "\"/project/creator.ts\"",
        parsed: parse_source_file(SOURCE_TEXT),
        library: false,
        external: false,
    });
    inputs
}

fn context(inputs: &[Input]) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in inputs {
        assert!(input.parsed.diagnostics.is_empty());
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.file != SOURCE,
                    input.library,
                    if input.external {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                ),
            )
            .unwrap();
    }
    for input in inputs {
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        inputs
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(context: &CanonicalCheckerContext<'_>, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(context.file(file).unwrap().0.id(), file, node)
}

fn named(context: &CanonicalCheckerContext<'_>, file: FileId, name: &str) -> NodeRef {
    let arena = context.file(file).unwrap().0;
    arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(reference(context, file, node))
        })
        .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn annotation(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(data) = &context
        .file(declaration.file)
        .unwrap()
        .0
        .get(declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    reference(context, declaration.file, data.type_.unwrap())
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn assert_owner(context: &CanonicalCheckerContext<'_>) -> (SemanticSymbolId, NodeRef, NodeRef) {
    let library = named(context, LIBRARY, "Creator");
    let augmentation = named(context, AUGMENTATION, "Creator");
    let owner = symbol(context, library);
    assert_eq!(symbol(context, augmentation), owner);
    let global = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source("Creator")
        .unwrap();
    assert_eq!(context.store().get_merged_symbol(global).unwrap(), owner);
    let record = context.store().symbol(owner).unwrap();
    assert_eq!(
        record.declarations(),
        Some([library, augmentation].as_slice())
    );
    assert_eq!(record.value_declaration(), Some(library));
    assert!(context.store().export_type_links(owner).is_none());
    let conditional = annotation(context, augmentation);
    assert_eq!(
        context
            .file(AUGMENTATION)
            .unwrap()
            .0
            .get(conditional.node)
            .unwrap()
            .kind,
        SyntaxKind::ConditionalType
    );
    assert!(
        context
            .store()
            .type_node_links(conditional)
            .is_none_or(|links| links.resolved_type.is_none())
    );
    (owner, annotation(context, library), conditional)
}

fn assert_optional_parameter(
    context: &CanonicalCheckerContext<'_>,
    signature: SignatureId,
    parameter: NodeRef,
    primitive: TypeId,
) {
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters(), &[symbol(context, parameter)]);
    assert_eq!(record.min_argument_count(), 0);
    let parameter_type = value_type(context, record.parameters()[0]);
    let TypeData::Union(union) = context.store().type_payload(parameter_type).unwrap().data()
    else {
        panic!("an optional parameter keeps its declared type and undefined");
    };
    assert_eq!(union.union.types.len(), 2);
    assert!(union.union.types.contains(&primitive));
    assert!(
        union.union.types.contains(
            &context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type
        )
    );
}

#[allow(clippy::too_many_lines)]
fn assert_provider(context: &mut CanonicalCheckerContext<'_>) -> (TypeId, Vec<SignatureId>) {
    let (owner, annotation, _) = assert_owner(context);
    let value = value_type(context, owner);
    assert_eq!(context.get_type_from_type_node(annotation).unwrap(), value);
    let literal_owner = symbol(context, annotation);
    assert_ne!(literal_owner, owner);
    assert_eq!(
        context.store().symbol(literal_owner).unwrap().flags(),
        SymbolFlags::TYPE_LITERAL
    );
    assert_eq!(
        context.store().type_payload(value).unwrap().symbol(),
        Some(literal_owner)
    );
    let number_owner = symbol(context, named(context, LIBRARY, "NumberResult"));
    let text_owner = symbol(context, named(context, LIBRARY, "TextResult"));
    assert_ne!(number_owner, owner);
    assert_ne!(text_owner, owner);
    let number_result = context.get_declared_type_of_symbol(number_owner).unwrap();
    let text_result = context.get_declared_type_of_symbol(text_owner).unwrap();
    assert_ne!(number_result, text_result);

    let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
        panic!("the global value retains the complete TypeLiteral object");
    };
    assert_eq!(object.structured.call_signature_count, 0);
    let signatures = object.structured.signatures.clone().unwrap();
    assert_eq!(signatures.len(), 2);
    let members = context
        .store()
        .symbol_table(object.structured.members.unwrap())
        .unwrap();
    let properties = object.structured.properties.as_ref().unwrap();
    assert_eq!(members.len(), 4);
    assert_eq!(properties.len(), 3);
    let construct_owner = members.get(InternalSymbolName::New.as_ref()).unwrap();
    assert!(!properties.contains(&construct_owner));
    let prototype = members.get_source("prototype").unwrap();
    let values = members.get_source("values").unwrap();
    let make = members.get_source("make").unwrap();
    for property in [prototype, values, make] {
        assert!(properties.contains(&property));
        assert_eq!(
            context.store().symbol(property).unwrap().parent(),
            Some(literal_owner)
        );
    }
    assert_eq!(value_type(context, prototype), number_result);
    let array_value = value_type(context, values);
    let TypeData::TypeReference(array) = context.store().type_payload(array_value).unwrap().data()
    else {
        panic!("values retains the canonical Array<number> reference");
    };
    let intrinsics = context.store().intrinsic_bootstrap().unwrap();
    let number = intrinsics.number_type;
    let string = intrinsics.string_type;
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some([number].as_slice())
    );

    let NodeData::TypeLiteralNode(literal) = &context
        .file(LIBRARY)
        .unwrap()
        .0
        .get(annotation.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    let declarations = literal
        .members
        .nodes
        .iter()
        .copied()
        .filter(|&node| {
            context.file(LIBRARY).unwrap().0.get(node).unwrap().kind
                == SyntaxKind::ConstructSignature
        })
        .map(|node| reference(context, LIBRARY, node))
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2);
    let construct_record = context.store().symbol(construct_owner).unwrap();
    assert_eq!(construct_record.flags(), SymbolFlags::SIGNATURE);
    assert_eq!(construct_record.parent(), Some(literal_owner));
    assert_eq!(
        construct_record.declarations(),
        Some(declarations.as_slice())
    );
    for &declaration in &declarations {
        assert_eq!(symbol(context, declaration), construct_owner);
    }
    for ((&signature, declaration), (primitive, result)) in signatures
        .iter()
        .zip(declarations)
        .zip([(number, number_result), (string, text_result)])
    {
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(declaration));
        assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
        assert!(record.type_parameters().is_empty());
        assert!(record.this_parameter().is_none());
        assert!(record.target().is_none());
        assert!(record.mapper().is_none());
        assert_eq!(record.resolved_return_type(), Some(result));
        assert_eq!(
            context
                .store()
                .signature_links(declaration)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(signature)
        );
        let NodeData::ConstructSignatureDeclaration(data) = &context
            .file(LIBRARY)
            .unwrap()
            .0
            .get(declaration.node)
            .unwrap()
            .data
        else {
            unreachable!()
        };
        let parameter = reference(context, LIBRARY, data.parameters.nodes[0]);
        let return_node = reference(context, LIBRARY, data.type_.unwrap());
        assert_optional_parameter(context, signature, parameter, primitive);
        assert_eq!(
            context.get_type_from_type_node(return_node).unwrap(),
            result
        );
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            result
        );
    }
    let TypeData::Object(method) = context
        .store()
        .type_payload(value_type(context, make))
        .unwrap()
        .data()
    else {
        panic!("the static method retains its callable value");
    };
    assert_eq!(method.structured.call_signature_count, 1);
    let method_signature = method.structured.signatures.as_ref().unwrap()[0];
    let method_record = context.store().signature(method_signature).unwrap();
    assert_eq!(method_record.resolved_return_type(), Some(number_result));
    let method_declaration = method_record.declaration().unwrap();
    assert_eq!(symbol(context, method_declaration), make);
    let NodeData::MethodSignatureDeclaration(data) = &context
        .file(LIBRARY)
        .unwrap()
        .0
        .get(method_declaration.node)
        .unwrap()
        .data
    else {
        unreachable!()
    };
    assert_optional_parameter(
        context,
        method_signature,
        reference(context, LIBRARY, data.parameters.nodes[0]),
        number,
    );

    for (name, expected_signature, result) in [
        ("numeric", signatures[0], number_result),
        ("textual", signatures[1], text_result),
        ("omitted", signatures[0], number_result),
    ] {
        let declaration = named(context, SOURCE, name);
        assert_eq!(value_type(context, symbol(context, declaration)), result);
        let NodeData::VariableDeclaration(data) = &context
            .file(SOURCE)
            .unwrap()
            .0
            .get(declaration.node)
            .unwrap()
            .data
        else {
            unreachable!()
        };
        let call = reference(context, SOURCE, data.initializer.unwrap());
        assert_eq!(
            context.file(SOURCE).unwrap().0.get(call.node).unwrap().kind,
            SyntaxKind::NewExpression
        );
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(expected_signature)
        );
        assert_eq!(context.get_type_at_location(call).unwrap(), result);
    }
    (value, signatures)
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_predicate_len(),
            store.type_alias_len(),
            store.type_resolution_len(),
            store.conditional_root_len(),
        ],
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
        context
            .file_order()
            .iter()
            .map(|&file| {
                (
                    file,
                    store
                        .source_file_links(context.source_file(file).unwrap())
                        .cloned(),
                )
            })
            .collect::<Vec<_>>(),
        context
            .file_order()
            .iter()
            .flat_map(|&file| {
                context.file(file).unwrap().0.iter().map(move |(node, _)| {
                    let node = reference(context, file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .signatures()
            .map(|(id, record)| {
                (
                    id,
                    record.flags(),
                    record.declaration(),
                    record.parameters().to_vec(),
                    record.min_argument_count(),
                    record.resolved_return_type(),
                    record.type_parameters().to_vec(),
                    record.this_parameter(),
                    record.target(),
                    record.mapper(),
                )
            })
            .collect::<Vec<_>>(),
    )
}

#[test]
fn global_type_literal_construction_keeps_ordered_owners_signatures_and_cold_augmentation() {
    for augmentation_first in [false, true] {
        for query_first in [false, true] {
            let inputs = inputs(augmentation_first);
            let mut context = context(&inputs);
            let (owner, annotation, _) = assert_owner(&context);
            assert!(
                context
                    .store()
                    .value_symbol_links(owner)
                    .is_none_or(|links| links.resolved_type.is_none())
            );
            let early = query_first.then(|| context.get_type_from_type_node(annotation).unwrap());
            assert_owner(&context);
            context.check_source_file(SOURCE).unwrap();
            assert!(context.diagnostics().is_empty());
            let expected = assert_provider(&mut context);
            if let Some(early) = early {
                assert_eq!(early, expected.0);
            }
            let warm = snapshot(&context);
            for _ in 0..2 {
                context.recheck_source_file(SOURCE).unwrap();
                assert_eq!(assert_provider(&mut context), expected);
                assert_eq!(snapshot(&context), warm);
            }
        }
    }
}
