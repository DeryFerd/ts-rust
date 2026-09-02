use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, DeclaredTypeError,
    IntrinsicBootstrapOptions, SignatureId, SourceCheckError, TypeData, TypeId,
    TypeNodeUnavailable, UnsupportedSourceSyntax,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(204_180);
const PROVIDER: FileId = FileId::new(204_181);
const SOURCE_TEXT: &str = concat!(
    "import type { Handler as ImportedHandler } from './handler';\n",
    "const handle: ImportedHandler = (value) => { return value; };\n",
    "handle('found');\n",
);

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().expect("the source contains this node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn context<'a>(source: &'a ParseResult, provider: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (SOURCE, source, "\"/project/consumer.ts\""),
        (PROVIDER, provider, "\"/project/handler.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let import = only_node(source, SOURCE, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &source.arena.get(import.node).unwrap().data else {
        unreachable!();
    };
    CanonicalCheckerContext::new_with_module_resolutions(
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
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(source.arena.id(), SOURCE, import.module_specifier),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

struct Arrow {
    declaration: NodeRef,
    variable: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    returned: NodeRef,
}

fn arrow(source: &ParseResult) -> Arrow {
    let node = |node| NodeRef::new(source.arena.id(), SOURCE, node);
    let declaration = only_node(source, SOURCE, SyntaxKind::ArrowFunction);
    let record = source.arena.get(declaration.node).unwrap();
    let NodeData::ArrowFunction(arrow) = &record.data else {
        unreachable!();
    };
    assert!(arrow.type_parameters.is_none());
    assert!(arrow.type_.is_none());
    let variable = node(record.parent.unwrap());
    let NodeData::VariableDeclaration(binding) = &source.arena.get(variable.node).unwrap().data
    else {
        panic!("the arrow must remain the variable initializer");
    };
    assert_eq!(binding.initializer, Some(declaration.node));
    let [parameter] = arrow.parameters.nodes.as_slice() else {
        panic!("the arrow has one parameter");
    };
    let NodeData::ParameterDeclaration(parameter_data) =
        &source.arena.get(*parameter).unwrap().data
    else {
        unreachable!();
    };
    assert!(parameter_data.type_.is_none());
    let returned = only_node(source, SOURCE, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(returned) = &source.arena.get(returned.node).unwrap().data
    else {
        unreachable!();
    };
    Arrow {
        declaration,
        variable,
        name: node(binding.name),
        annotation: node(binding.type_.unwrap()),
        parameter: node(*parameter),
        parameter_name: node(parameter_data.name),
        returned: node(returned.expression.unwrap()),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("the type must retain its callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the callable has one signature");
    };
    *signature
}

fn checked(checker: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn snapshot(checker: &CanonicalCheckerContext<'_>) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.type_alias_len(),
            store.mapper_len(),
        ],
        [SOURCE, PROVIDER].map(|file| {
            store
                .source_file_links(checker.source_file(file).unwrap())
                .cloned()
        }),
        checker.diagnostics().clone(),
    )
}

fn assert_raw_annotation_is_scoped(
    checker: &mut CanonicalCheckerContext<'_>,
    arrow: &Arrow,
    imported: SemanticSymbolId,
) {
    let before = snapshot(checker);
    assert_eq!(
        checker.get_type_from_type_node(arrow.annotation),
        Err(DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::ImportAliasTypeReference {
                node: arrow.annotation,
                alias: imported,
            },
        )),
    );
    assert_eq!(snapshot(checker), before);
}

#[derive(Debug, Eq, PartialEq)]
struct ArrowTypes {
    callable: TypeId,
    target: TypeId,
    source_signature: SignatureId,
    target_signature: SignatureId,
    parameter: TypeId,
    returned: TypeId,
    target_return: TypeId,
}

fn arrow_types(checker: &mut CanonicalCheckerContext<'_>, arrow: &Arrow) -> ArrowTypes {
    let callable = checker.get_type_at_location(arrow.declaration).unwrap();
    let target = checker.get_type_at_location(arrow.name).unwrap();
    assert_ne!(callable, target);
    let owner = symbol(checker, arrow.declaration);
    let variable = symbol(checker, arrow.variable);
    let parameter_owner = symbol(checker, arrow.parameter);
    assert_ne!(owner, variable);
    assert_eq!(checker.store().type_payload(callable).unwrap().symbol(), Some(owner));
    let parameter = checker.get_type_at_location(arrow.parameter_name).unwrap();
    assert_eq!(checker.get_type_at_location(arrow.returned), Ok(parameter));
    for (symbol, type_) in [(owner, callable), (variable, target), (parameter_owner, parameter)] {
        assert_eq!(
            checker.store().value_symbol_links(symbol).unwrap().resolved_type,
            Some(type_),
        );
    }
    let source_signature = signature(checker, callable);
    let target_signature = signature(checker, target);
    assert_ne!(source_signature, target_signature);
    let source = checker.store().signature(source_signature).unwrap();
    assert_eq!(source.declaration(), Some(arrow.declaration));
    assert_eq!(source.parameters(), &[parameter_owner]);
    assert!(source.type_parameters().is_empty());
    assert_eq!(source.target(), None);
    assert_eq!(source.mapper(), None);
    ArrowTypes {
        callable,
        target,
        source_signature,
        target_signature,
        parameter,
        returned: checker.get_return_type_of_signature(source_signature).unwrap(),
        target_return: checker.get_return_type_of_signature(target_signature).unwrap(),
    }
}

fn check_callable_alias(provider_text: &str, invalid_return: bool) {
    let source = parse_source_file(SOURCE_TEXT);
    let provider = parse_source_file(provider_text);
    let arrow = arrow(&source);
    let import = only_node(&source, SOURCE, SyntaxKind::ImportSpecifier);
    let alias = only_node(&provider, PROVIDER, SyntaxKind::TypeAliasDeclaration);
    let call = only_node(&source, SOURCE, SyntaxKind::CallExpression);
    for source_first in [false, true] {
        let mut checker = context(&source, &provider);
        let imported = symbol(&checker, import);
        let alias_owner = symbol(&checker, alias);
        assert_ne!(imported, alias_owner);
        assert!(checker.store().signature_links(arrow.declaration).is_none());
        if source_first {
            checker.check_source_file(SOURCE).unwrap();
        }
        let cold_callable = checker.get_type_at_location(arrow.declaration).unwrap();
        checker.check_source_file(SOURCE).unwrap();
        let types = arrow_types(&mut checker, &arrow);
        assert_eq!(types.callable, cold_callable);
        let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
        assert_eq!(types.parameter, intrinsic.string_type);
        assert_eq!(types.returned, intrinsic.string_type);
        assert_eq!(
            types.target_return,
            if invalid_return { intrinsic.number_type } else { intrinsic.string_type },
        );
        assert_eq!(checker.get_type_at_location(call), Ok(types.target_return));
        assert_eq!(
            checker.store().signature_links(call).unwrap().resolved_signature.signature(),
            Some(types.target_signature),
        );
        assert_eq!(
            checker.store().alias_symbol_links(imported).unwrap().alias_target,
            AliasTargetState::Resolved(alias_owner),
        );
        assert!(checked(&checker, SOURCE));
        assert!(!checked(&checker, PROVIDER));
        if invalid_return {
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("the inferred return must produce one assignment error");
            };
            assert_eq!(diagnostic.node, Some(arrow.declaration));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type '(value: string) => string' is not assignable to type 'Handler'.",
            );
            assert!(diagnostic.related_information.is_empty());
        } else {
            assert!(checker.diagnostics().is_empty());
        }
        assert_raw_annotation_is_scoped(&mut checker, &arrow, imported);
        let warm = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(SOURCE).unwrap();
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(arrow_types(&mut checker, &arrow), types);
            assert_eq!(checker.get_type_at_location(call), Ok(types.target_return));
            assert_raw_annotation_is_scoped(&mut checker, &arrow, imported);
            assert_eq!(snapshot(&checker), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn imported_callable_annotation_contextualizes_the_arrow_and_keeps_query_scope() {
    check_callable_alias("export type Handler = (value: string) => string;", false);
}

#[test]
fn imported_callable_annotation_does_not_replace_an_invalid_inferred_return() {
    check_callable_alias("export type Handler = (value: string) => number;", true);
}

#[test]
fn imported_non_callable_and_generic_annotations_remain_typed_boundaries() {
    for (provider_text, generic) in [
        ("export type Handler = { value: string };", false),
        ("export type Handler<T = string> = (value: T) => T;", true),
    ] {
        let source = parse_source_file(SOURCE_TEXT);
        let provider = parse_source_file(provider_text);
        let arrow = arrow(&source);
        let mut checker = context(&source, &provider);
        let boundary = if generic {
            arrow.annotation
        } else {
            only_node(&provider, PROVIDER, SyntaxKind::TypeLiteral)
        };
        let error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Arrow(boundary));
        assert_eq!(checker.check_source_file(SOURCE), Err(error));
        assert!(!checked(&checker, SOURCE));
        assert!(!checked(&checker, PROVIDER));
        assert!(checker.diagnostics().is_empty());
        for declaration in [arrow.variable, arrow.declaration, arrow.parameter] {
            assert!(checker.store().value_symbol_links(symbol(&checker, declaration)).is_none());
        }
        assert!(checker.store().signature_links(arrow.declaration).is_none());
        let warm = snapshot(&checker);
        for _ in 0..2 {
            assert_eq!(checker.recheck_source_file(SOURCE), Err(error));
            assert_eq!(snapshot(&checker), warm);
            assert!(checker.store().type_resolution_is_empty());
        }
    }
}
