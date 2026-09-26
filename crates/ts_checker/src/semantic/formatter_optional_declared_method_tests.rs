use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

use super::*;
use crate::semantic::{CanonicalCheckerContext, IntrinsicBootstrapOptions};

const SEARCH_SOURCE: &str = concat!(
    "interface Service { search(query: string, position?: number): boolean; } ",
    "declare const service: Service; const search = service.search;",
);

fn method_context<'a>(
    files: &[(FileId, &'a ParseResult, bool)],
    options: IntrinsicBootstrapOptions,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, library) in files.iter().copied() {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(format!("\"/optional-method/{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files.iter().copied() {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        options,
    )
    .unwrap()
}

fn method_access(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MethodIdentity {
    callable: TypeId,
    signature: SignatureId,
    declaration: NodeRef,
    parameter: NodeRef,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
    annotation_type: TypeId,
    value_type: TypeId,
    return_type: TypeId,
}

fn method_identity(
    context: &mut CanonicalCheckerContext<'_>,
    access: NodeRef,
    index: usize,
) -> MethodIdentity {
    let callable = context.get_type_at_location(access).unwrap();
    let signatures = context
        .store()
        .type_payload(callable)
        .unwrap()
        .data()
        .structured()
        .unwrap()
        .signatures
        .as_ref()
        .unwrap();
    let [signature] = signatures.as_slice() else {
        panic!("one source method signature")
    };
    let signature = *signature;
    let record = context.store().signature(signature).unwrap();
    assert!(record.type_parameters().is_empty());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    let declaration = record.declaration().unwrap();
    let symbol = record.parameters()[index];
    let (arena, bound) = context.file(declaration.file).unwrap();
    let NodeData::MethodSignatureDeclaration(method) = &arena.get(declaration.node).unwrap().data
    else {
        panic!("the callable retains its actual method declaration")
    };
    let parameter = NodeRef::new(arena.id(), declaration.file, method.parameters.nodes[index]);
    assert_eq!(bound.symbol(parameter), Some(symbol));
    let NodeData::ParameterDeclaration(data) = &arena.get(parameter.node).unwrap().data else {
        panic!("the signature retains a real parameter")
    };
    let annotation = NodeRef::new(arena.id(), declaration.file, data.type_.unwrap());
    let annotation_type = context.get_type_from_type_node(annotation).unwrap();
    let value_type = context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        context
            .store()
            .callable_signature_parameter_types(signature)
            .unwrap()[index],
        value_type
    );
    let return_type = context.get_return_type_of_signature(signature).unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(return_type)
    );
    MethodIdentity {
        callable,
        signature,
        declaration,
        parameter,
        annotation,
        symbol,
        annotation_type,
        value_type,
        return_type,
    }
}

fn assert_display_read_only(
    context: &mut CanonicalCheckerContext<'_>,
    identity: &MethodIdentity,
    location: NodeRef,
    located: &str,
    context_free: &str,
) {
    let before = format!("{:?}", context.store());
    let diagnostics = context.diagnostics().as_slice().to_vec();
    for _ in 0..2 {
        assert_eq!(
            context.type_to_string(identity.callable).unwrap(),
            context_free
        );
        assert_eq!(
            context
                .type_to_string_at_location_with_flags(
                    identity.callable,
                    location,
                    CanonicalTypeFormatFlags::NO_TRUNCATION,
                )
                .unwrap(),
            located,
        );
        assert_eq!(format!("{:?}", context.store()), before);
        assert_eq!(context.diagnostics().as_slice(), diagnostics.as_slice());
    }
}

fn assert_optional_number(
    context: &CanonicalCheckerContext<'_>,
    identity: &MethodIdentity,
    strict: bool,
) {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(identity.annotation_type, bootstrap.number_type);
    assert_eq!(identity.return_type, bootstrap.boolean_type);
    let signature = context.store().signature(identity.signature).unwrap();
    assert_eq!(signature.parameters().len(), 2);
    assert_eq!(signature.parameters()[1], identity.symbol);
    assert_eq!(signature.min_argument_count(), 1);
    let (arena, _) = context.file(identity.parameter.file).unwrap();
    let NodeData::ParameterDeclaration(parameter) =
        &arena.get(identity.parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter.question_token.is_some());
    assert!(parameter.dot_dot_dot_token.is_none());
    assert!(parameter.initializer.is_none());
    if strict {
        let TypeData::Union(union) = context
            .store()
            .type_payload(identity.value_type)
            .unwrap()
            .data()
        else {
            panic!("strict optional parameters keep a semantic union")
        };
        let mut expected = vec![bootstrap.number_type, bootstrap.undefined_type];
        expected.sort_unstable();
        assert_eq!(union.union.types, expected);
        context
            .store()
            .validate_optional_parameter_type_metadata(
                identity.annotation_type,
                identity.value_type,
            )
            .unwrap();
    } else {
        assert_eq!(identity.value_type, identity.annotation_type);
    }
}

#[test]
fn optional_declared_method_display_uses_real_library_annotation_without_semantic_changes() {
    let libraries = [
        include_str!("../../../ts_bundled/libs/lib.es5.d.ts"),
        include_str!("../../../ts_bundled/libs/lib.es2015.core.d.ts"),
        include_str!("../../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
        include_str!("../../../ts_bundled/libs/lib.es2015.symbol.wellknown.d.ts"),
        include_str!("../../../ts_bundled/libs/lib.scripthost.d.ts"),
    ]
    .map(parse_source_file);
    let parsed = parse_source_file("declare const text: string; const includes = text.includes;");
    let file = FileId::new(3_005);
    for source_first in [false, true] {
        let mut files = libraries
            .iter()
            .enumerate()
            .map(|(index, library)| {
                (
                    FileId::new(3_000 + u32::try_from(index).unwrap()),
                    library,
                    true,
                )
            })
            .collect::<Vec<_>>();
        files.push((file, &parsed, false));
        let mut context = method_context(
            &files,
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
        );
        if source_first {
            context.check_source_file(file).unwrap();
        }
        let access = method_access(&parsed, file, "includes");
        let identity = method_identity(&mut context, access, 1);
        assert_eq!(identity.declaration.file, files[1].0);
        assert_optional_number(&context, &identity, true);
        assert_display_read_only(
            &mut context,
            &identity,
            access,
            "(searchString: string, position?: number) => boolean",
            "(searchString: string, position?: number | undefined) => boolean",
        );
        context.check_source_file(file).unwrap();
        assert_eq!(method_identity(&mut context, access, 1), identity);
        assert_optional_number(&context, &identity, true);
        assert_display_read_only(
            &mut context,
            &identity,
            access,
            "(searchString: string, position?: number) => boolean",
            "(searchString: string, position?: number | undefined) => boolean",
        );
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn optional_declared_method_display_keeps_source_order_options_and_warm_identity() {
    for source in [
        SEARCH_SOURCE,
        concat!(
            "declare const service: { search(query: string, position?: number): boolean; }; ",
            "const search = service.search;",
        ),
    ] {
        let parsed = parse_source_file(source);
        let file = FileId::new(3_010);
        for (strict, exact) in [(true, false), (true, true), (false, false), (false, true)] {
            for source_first in [false, true] {
                let mut context = method_context(
                    &[(file, &parsed, false)],
                    IntrinsicBootstrapOptions {
                        strict_null_checks: strict,
                        exact_optional_property_types: exact,
                    },
                );
                if source_first {
                    context.check_source_file(file).unwrap();
                }
                let access = method_access(&parsed, file, "search");
                let identity = method_identity(&mut context, access, 1);
                let semantic = if strict {
                    "number | undefined"
                } else {
                    "number"
                };
                for _ in 0..2 {
                    assert_optional_number(&context, &identity, strict);
                    assert_eq!(
                        context.type_to_string(identity.value_type).unwrap(),
                        semantic
                    );
                    let annotation_links = context
                        .store()
                        .type_node_links(identity.annotation)
                        .cloned();
                    assert_display_read_only(
                        &mut context,
                        &identity,
                        access,
                        "(query: string, position?: number) => boolean",
                        &format!("(query: string, position?: {semantic}) => boolean"),
                    );
                    assert_eq!(
                        context.store().type_node_links(identity.annotation),
                        annotation_links.as_ref()
                    );
                    context.check_source_file(file).unwrap();
                    assert_eq!(method_identity(&mut context, access, 1), identity);
                }
                assert!(context.diagnostics().is_empty());
            }
        }
    }
}

#[test]
fn optional_declared_method_display_keeps_written_undefined_and_return_unions() {
    for (member, expected, strict) in [
        (
            "read(value?: number | undefined): boolean",
            "(value?: number | undefined) => boolean",
            true,
        ),
        (
            "read(value: number | undefined): boolean",
            "(value: number | undefined) => boolean",
            true,
        ),
        (
            "read(value?: undefined): undefined",
            "(value?: undefined) => undefined",
            true,
        ),
        (
            "read(value: number): number | undefined",
            "(value: number) => number | undefined",
            true,
        ),
        (
            "read(value?: number | undefined): boolean",
            "(value?: number) => boolean",
            false,
        ),
    ] {
        for exact in [false, true] {
            let parsed = parse_source_file(&format!(
                "interface Reader {{ {member}; }} declare const reader: Reader; const read = reader.read;"
            ));
            let file = FileId::new(3_011);
            let mut context = method_context(
                &[(file, &parsed, false)],
                IntrinsicBootstrapOptions {
                    strict_null_checks: strict,
                    exact_optional_property_types: exact,
                },
            );
            context.check_source_file(file).unwrap();
            let access = method_access(&parsed, file, "read");
            let identity = method_identity(&mut context, access, 0);
            assert_display_read_only(&mut context, &identity, access, expected, expected);
            assert_eq!(method_identity(&mut context, access, 0), identity);
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
fn optional_declared_method_display_reuses_other_intrinsic_annotations() {
    for (annotation, semantic) in [
        ("string", "string | undefined"),
        ("boolean", "boolean | undefined"),
        ("object", "object | undefined"),
    ] {
        let parsed = parse_source_file(&format!(
            "declare const service: {{ choose(value?: {annotation}): boolean; }}; \
             const choose = service.choose;"
        ));
        let file = FileId::new(3_014);
        let mut context = method_context(
            &[(file, &parsed, false)],
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
        );
        let access = method_access(&parsed, file, "choose");
        let identity = method_identity(&mut context, access, 0);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = match annotation {
            "string" => bootstrap.string_type,
            "boolean" => bootstrap.boolean_type,
            "object" => bootstrap.non_primitive_type,
            _ => unreachable!(),
        };
        assert_eq!(identity.annotation_type, expected);
        assert_eq!(
            context
                .store()
                .signature(identity.signature)
                .unwrap()
                .min_argument_count(),
            0
        );
        context
            .store()
            .validate_optional_parameter_type_metadata(expected, identity.value_type)
            .unwrap();
        assert_eq!(
            context.type_to_string(identity.value_type).unwrap(),
            semantic
        );
        assert_display_read_only(
            &mut context,
            &identity,
            access,
            &format!("(value?: {annotation}) => boolean"),
            &format!("(value?: {semantic}) => boolean"),
        );
        context.check_source_file(file).unwrap();
        assert_eq!(method_identity(&mut context, access, 0), identity);
        assert!(context.diagnostics().is_empty());
    }
}

fn assert_located_rejects_without_writes(
    context: &mut CanonicalCheckerContext<'_>,
    identity: &MethodIdentity,
    access: NodeRef,
) {
    let before = format!("{:?}", context.store());
    let diagnostics = context.diagnostics().as_slice().to_vec();
    for _ in 0..2 {
        assert_eq!(
            context.type_to_string_at_location_with_flags(
                identity.callable,
                access,
                CanonicalTypeFormatFlags::NO_TRUNCATION,
            ),
            Err(TypeDisplayUnavailable::MalformedType(identity.callable))
        );
        assert_eq!(format!("{:?}", context.store()), before);
        assert_eq!(context.diagnostics().as_slice(), diagnostics.as_slice());
    }
}

#[test]
fn optional_declared_method_display_rejects_changed_annotation_and_symbol_links() {
    let parsed = parse_source_file(SEARCH_SOURCE);
    let file = FileId::new(3_012);
    let mut context = method_context(
        &[(file, &parsed, false)],
        IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
    );
    context.check_source_file(file).unwrap();
    let access = method_access(&parsed, file, "search");
    let identity = method_identity(&mut context, access, 1);
    assert_display_read_only(
        &mut context,
        &identity,
        access,
        "(query: string, position?: number) => boolean",
        "(query: string, position?: number | undefined) => boolean",
    );
    // A keyword can have no cache row. Add only its already-proved identity before
    // damage. Restoration below restores these rows, not their former absence.
    let annotation_links = context
        .store()
        .type_node_links(identity.annotation)
        .cloned()
        .unwrap_or(TypeNodeLinks {
            resolved_type: Some(identity.annotation_type),
            ..TypeNodeLinks::default()
        });
    assert!(
        context
            .store_mut_for_test()
            .set_type_node_links(identity.annotation, annotation_links.clone())
    );
    assert!(
        context
            .store_mut_for_test()
            .ensure_symbol_node_links(identity.annotation)
    );
    let symbol_links = context
        .store()
        .symbol_node_links(identity.annotation)
        .unwrap()
        .clone();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let mut wrong_type = annotation_links.clone();
    wrong_type.resolved_type = Some(string);
    assert!(
        context
            .store_mut_for_test()
            .set_type_node_links(identity.annotation, wrong_type)
    );
    assert_located_rejects_without_writes(&mut context, &identity, access);
    assert!(
        context
            .store_mut_for_test()
            .set_type_node_links(identity.annotation, annotation_links.clone())
    );
    let mut wrong_symbol = symbol_links.clone();
    wrong_symbol.resolved_symbol = Some(identity.symbol);
    assert!(
        context
            .store_mut_for_test()
            .set_symbol_node_links(identity.annotation, wrong_symbol)
    );
    assert_located_rejects_without_writes(&mut context, &identity, access);
    assert!(
        context
            .store_mut_for_test()
            .set_symbol_node_links(identity.annotation, symbol_links.clone())
    );
    assert_eq!(
        context.store().type_node_links(identity.annotation),
        Some(&annotation_links)
    );
    assert_eq!(
        context.store().symbol_node_links(identity.annotation),
        Some(&symbol_links)
    );
    assert_display_read_only(
        &mut context,
        &identity,
        access,
        "(query: string, position?: number) => boolean",
        "(query: string, position?: number | undefined) => boolean",
    );
    assert_eq!(method_identity(&mut context, access, 1), identity);
}

#[test]
fn optional_declared_method_display_rejects_changed_value_and_optional_union_metadata() {
    let parsed = parse_source_file(SEARCH_SOURCE);
    let file = FileId::new(3_013);
    let mut context = method_context(
        &[(file, &parsed, false)],
        IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        },
    );
    context.check_source_file(file).unwrap();
    let access = method_access(&parsed, file, "search");
    let identity = method_identity(&mut context, access, 1);
    assert_optional_number(&context, &identity, true);
    let original = context
        .store()
        .value_symbol_links(identity.symbol)
        .unwrap()
        .clone();
    let mut missing_optional = original.clone();
    missing_optional.resolved_type = Some(identity.annotation_type);
    assert!(
        context
            .store_mut_for_test()
            .set_value_symbol_links(identity.symbol, missing_optional)
    );
    assert_located_rejects_without_writes(&mut context, &identity, access);
    assert!(
        context
            .store_mut_for_test()
            .set_value_symbol_links(identity.symbol, original.clone())
    );
    let TypeData::Union(union) = context
        .store()
        .type_payload(identity.value_type)
        .unwrap()
        .data()
    else {
        unreachable!()
    };
    let union = union.clone();
    assert!(context.store_mut_for_test().set_union_caches(
        identity.value_type,
        union.resolved_reduced_type,
        union.regular_type,
        Some(identity.value_type),
        union.key_property_name.clone(),
        union.constituent_map.clone()
    ));
    assert_located_rejects_without_writes(&mut context, &identity, access);
    assert!(context.store_mut_for_test().set_union_caches(
        identity.value_type,
        union.resolved_reduced_type,
        union.regular_type,
        union.origin,
        union.key_property_name.clone(),
        union.constituent_map.clone()
    ));
    assert_eq!(
        context.store().value_symbol_links(identity.symbol),
        Some(&original)
    );
    assert_eq!(
        context
            .store()
            .type_payload(identity.value_type)
            .unwrap()
            .data(),
        &TypeData::Union(union)
    );
    assert_optional_number(&context, &identity, true);
    assert_display_read_only(
        &mut context,
        &identity,
        access,
        "(query: string, position?: number) => boolean",
        "(query: string, position?: number | undefined) => boolean",
    );
    assert_eq!(method_identity(&mut context, access, 1), identity);
}

#[test]
fn optional_declared_method_display_rejects_a_different_real_signature_owner() {
    let parsed = parse_source_file(concat!(
        "interface Service { search(query: string, position?: number): boolean; ",
        "other(query: string, position?: number): boolean; } ",
        "declare const service: Service; const search = service.search; const other = service.other;",
    ));
    let file = FileId::new(3_015);
    let mut context = method_context(
        &[(file, &parsed, false)],
        IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
    );
    context.check_source_file(file).unwrap();
    let access = method_access(&parsed, file, "search");
    let identity = method_identity(&mut context, access, 1);
    let other = method_identity(&mut context, method_access(&parsed, file, "other"), 1);
    assert_ne!(identity.signature, other.signature);
    assert_ne!(identity.symbol, other.symbol);
    assert_ne!(identity.annotation, other.annotation);
    assert_eq!(identity.value_type, other.value_type);
    let original = context
        .store()
        .signature_links(identity.declaration)
        .unwrap()
        .clone();
    let foreign = context
        .store()
        .signature_links(other.declaration)
        .unwrap()
        .clone();
    assert!(
        context
            .store_mut_for_test()
            .set_signature_links(identity.declaration, foreign)
    );
    assert_located_rejects_without_writes(&mut context, &identity, access);
    assert!(
        context
            .store_mut_for_test()
            .set_signature_links(identity.declaration, original.clone())
    );
    assert_eq!(
        context.store().signature_links(identity.declaration),
        Some(&original)
    );
    assert_display_read_only(
        &mut context,
        &identity,
        access,
        "(query: string, position?: number) => boolean",
        "(query: string, position?: number | undefined) => boolean",
    );
    assert_eq!(method_identity(&mut context, access, 1), identity);
    assert_eq!(
        method_identity(&mut context, method_access(&parsed, file, "other"), 1),
        other
    );
    assert!(context.diagnostics().is_empty());
}
