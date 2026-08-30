use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalAliasQueryError, CanonicalCheckerContext,
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionLookup, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, SignatureLinks, SourceCheckError,
    SourceFileLinks, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    alias::CanonicalAliasResolutionError,
};
use ts_options::ModuleKind;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(46_500);
const DECLARATIONS: FileId = FileId::new(46_501);
const CONSUMER: FileId = FileId::new(46_502);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const AMBIENT: &str = concat!(
    "declare module 'route-tools' { ",
    "namespace toolkit { interface Paths { ",
    "parent(input: string): string; ",
    "combine(...inputs: string[]): string; ",
    "ignored(input: boolean): boolean; ",
    "readonly alternate: Paths; ",
    "} } ",
    "const toolkit: toolkit.Paths; export = toolkit; ",
    "} ",
    "declare module 'portable:routes' { ",
    "import toolkit = require('route-tools'); export = toolkit; ",
    "}",
);

fn module_specifiers(parsed: &ParseResult, file: FileId) -> Vec<(NodeRef, bool)> {
    parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let (specifier, require) = match &record.data {
                NodeData::ImportDeclaration(import) => (import.module_specifier, false),
                NodeData::ImportEqualsDeclaration(import) => {
                    let NodeData::ExternalModuleReference(reference) =
                        &parsed.arena.get(import.module_reference)?.data
                    else {
                        return None;
                    };
                    (reference.expression, true)
                }
                _ => return None,
            };
            let NodeData::StringLiteral(_) = &parsed.arena.get(specifier)?.data else {
                return None;
            };
            Some((NodeRef::new(parsed.arena.id(), file, specifier), require))
        })
        .collect()
}

fn context<'arena>(
    library: &'arena ParseResult,
    declarations: &'arena ParseResult,
    consumer: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib/lib.es5.d.ts\"", true),
        (
            DECLARATIONS,
            declarations,
            "\"/project/node_modules/@types/route-tools/index.d.ts\"",
            false,
        ),
        (CONSUMER, consumer, "\"/project/main.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, default_library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != CONSUMER,
                    default_library,
                    if file == CONSUMER {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_implied_node_format(if file == CONSUMER {
                    ModuleKind::EsNext
                } else {
                    ModuleKind::CommonJs
                }),
            )
            .unwrap();
    }
    for (file, parsed, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let entries = [(CONSUMER, consumer), (DECLARATIONS, declarations)]
        .into_iter()
        .flat_map(|(file, parsed)| module_specifiers(parsed, file))
        .map(|(specifier, require)| {
            CanonicalModuleResolutionEntry::resolved(
                specifier,
                CanonicalResolvedModuleInput::new(
                    DECLARATIONS,
                    if require {
                        CanonicalModuleResolutionMode::CommonJs
                    } else {
                        CanonicalModuleResolutionMode::Esm
                    },
                    CanonicalModuleResolutionMode::CommonJs,
                ),
            )
        });
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            module_kind: ModuleKind::NodeNext,
            no_emit: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(entries),
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::ImportSpecifier(import) => import.name,
                NodeData::ImportEqualsDeclaration(import) => import.name,
                NodeData::MethodSignatureDeclaration(method) => method.name,
                NodeData::PropertyDeclaration(property) => property.name,
                NodeData::InterfaceDeclaration(interface) => interface.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {name}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn imported(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> SemanticSymbolId {
    symbol(
        context,
        declaration(parsed, CONSUMER, SyntaxKind::ImportSpecifier, name),
    )
}

fn method(parsed: &ParseResult, name: &str) -> NodeRef {
    declaration(parsed, DECLARATIONS, SyntaxKind::MethodSignature, name)
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 6],
    sources: Vec<Option<SourceFileLinks>>,
    types: Vec<Option<TypeNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    aliases: Vec<Option<AliasSymbolLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    consumer: &ParseResult,
) -> Snapshot {
    let store = context.store();
    let nodes = [(DECLARATIONS, declarations), (CONSUMER, consumer)]
        .into_iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    let symbols = nodes
        .iter()
        .filter_map(|&node| context.file(node.file).unwrap().1.symbol(node))
        .map(|symbol| store.get_merged_symbol(symbol).unwrap())
        .collect::<Vec<_>>();
    Snapshot {
        counts: counts(context),
        sources: [LIBRARY, DECLARATIONS, CONSUMER]
            .map(|file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .to_vec(),
        types: nodes
            .iter()
            .map(|&node| store.type_node_links(node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|&node| store.signature_links(node).cloned())
            .collect(),
        aliases: symbols
            .iter()
            .map(|&symbol| store.alias_symbol_links(symbol).cloned())
            .collect(),
        values: symbols
            .iter()
            .map(|&symbol| store.value_symbol_links(symbol).cloned())
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    consumer: &ParseResult,
) {
    let checked = snapshot(context, declarations, consumer);
    context.check_source_file(CONSUMER).unwrap();
    assert_eq!(snapshot(context, declarations, consumer), checked);
    context.recheck_source_file(CONSUMER).unwrap();
    assert_eq!(snapshot(context, declarations, consumer), checked);
    assert!(context.store().type_resolution_is_empty());
}

fn assert_cold_members(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    for node in [
        method(parsed, "ignored"),
        declaration(
            parsed,
            DECLARATIONS,
            SyntaxKind::PropertyDeclaration,
            "alternate",
        ),
    ] {
        assert!(
            context
                .store()
                .value_symbol_links(symbol(context, node))
                .is_none()
        );
        assert!(context.store().signature_links(node).is_none());
    }
    assert!(
        !context
            .store()
            .source_file_links(context.source_file(DECLARATIONS).unwrap())
            .is_some_and(|links| links.type_checked),
        "an imported method must not check its declaration source",
    );
}

fn assert_method_value(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
    rest: bool,
) -> TypeId {
    let store = context.store();
    let method = symbol(context, declaration);
    assert_eq!(store.symbol(method).unwrap().flags(), SymbolFlags::METHOD);
    assert_eq!(
        store.symbol(method).unwrap().declarations(),
        Some(&[declaration][..])
    );
    let value = store
        .value_symbol_links(method)
        .unwrap()
        .resolved_type
        .unwrap();
    let record = store.type_payload(value).unwrap();
    assert_eq!(record.symbol(), Some(method));
    let TypeData::Object(object) = record.data() else {
        panic!("an imported method must retain its callable object");
    };
    let signatures = object.structured.signatures.as_ref().unwrap();
    assert_eq!(signatures.len(), 1);
    let signature = store.signature(signatures[0]).unwrap();
    assert_eq!(signature.declaration(), Some(declaration));
    assert!(signature.type_parameters().is_empty());
    assert_eq!(signature.parameters().len(), 1);
    assert_eq!(signature.has_rest_parameter(), rest);
    assert_eq!(signature.min_argument_count(), i32::from(!rest));
    assert_eq!(
        signature.resolved_return_type(),
        Some(store.intrinsic_bootstrap().unwrap().string_type)
    );
    assert!(signature.target().is_none());
    assert!(signature.mapper().is_none());
    value
}

#[test]
fn forwarded_ambient_methods_keep_source_symbols_real_calls_and_replay() {
    let library = parse_source_file(ES5);
    let declarations = parse_source_file(AMBIENT);
    let consumer = parse_source_file(concat!(
        "import { parent as forwardedParent, combine as forwardedCombine } from 'portable:routes'; ",
        "import { parent as directParent, combine as directCombine } from 'route-tools'; ",
        "const parentValue = forwardedParent('part/file'); ",
        "const combinedValue = forwardedCombine('part', 'file'); ",
        "const emptyValue = forwardedCombine(); ",
        "const directValue = directParent('part/file'); ",
        "const directCombined = directCombine('part', 'file'); ",
        "const wrongArgument = forwardedParent(1); ",
        "const wrongRest = forwardedCombine('part', 1); ",
        "const wrongResult: number = forwardedParent('part/file');",
    ));
    let mut context = context(&library, &declarations, &consumer);
    let forward = symbol(
        &context,
        declaration(
            &declarations,
            DECLARATIONS,
            SyntaxKind::ImportEqualsDeclaration,
            "toolkit",
        ),
    );
    assert!(context.store().alias_symbol_links(forward).is_none());
    for name in ["parent", "combine"] {
        assert!(
            context
                .store()
                .value_symbol_links(symbol(&context, method(&declarations, name)))
                .is_none()
        );
    }

    context.check_source_file(CONSUMER).unwrap();
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2345, 2345, 2322],
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    for (name, aliases, rest) in [
        ("parent", ["forwardedParent", "directParent"], false),
        ("combine", ["forwardedCombine", "directCombine"], true),
    ] {
        let declaration = method(&declarations, name);
        let target = symbol(&context, declaration);
        let value = assert_method_value(&context, declaration, rest);
        for name in aliases {
            let alias = imported(&context, &consumer, name);
            assert_eq!(
                context.resolve_alias(alias).unwrap().target,
                AliasTargetState::Resolved(target)
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(alias)
                    .unwrap()
                    .resolved_type,
                Some(value)
            );
        }
    }
    for (node, record) in consumer.arena.iter() {
        if record.kind == SyntaxKind::CallExpression {
            let call = NodeRef::new(consumer.arena.id(), CONSUMER, node);
            assert_eq!(context.get_type_at_location(call), Ok(string));
        }
    }
    assert_cold_members(&context, &declarations);
    assert_replay(&mut context, &declarations, &consumer);
}

#[test]
fn unused_forwarded_method_imports_resolve_without_typing_members() {
    let library = parse_source_file(ES5);
    let declarations = parse_source_file(AMBIENT);
    let consumer = parse_source_file("import { parent, combine } from 'portable:routes';");
    let mut context = context(&library, &declarations, &consumer);
    let cold = counts(&context);
    for name in ["parent", "combine"] {
        let alias = imported(&context, &consumer, name);
        let target = symbol(&context, method(&declarations, name));
        assert_eq!(
            context.resolve_alias(alias).unwrap().target,
            AliasTargetState::Resolved(target)
        );
        assert_eq!(counts(&context), cold);
        assert!(context.store().value_symbol_links(alias).is_none());
        assert!(context.store().value_symbol_links(target).is_none());
    }
    for (specifier, require) in module_specifiers(&consumer, CONSUMER)
        .into_iter()
        .chain(module_specifiers(&declarations, DECLARATIONS))
    {
        let CanonicalModuleResolutionLookup::Resolved(resolved) =
            context.module_resolution(specifier)
        else {
            panic!("the fixture retains every ambient import resolution");
        };
        assert_eq!(resolved.target_file(), DECLARATIONS);
        assert!(resolved.is_ambient_module());
        assert_eq!(
            resolved.target_mode(),
            CanonicalModuleResolutionMode::CommonJs
        );
        assert_eq!(
            resolved.usage_mode(),
            if require {
                CanonicalModuleResolutionMode::CommonJs
            } else {
                CanonicalModuleResolutionMode::Esm
            }
        );
    }
    context.check_source_file(CONSUMER).unwrap();
    assert!(context.diagnostics().is_empty());
    for name in ["parent", "combine"] {
        assert!(
            context
                .store()
                .value_symbol_links(imported(&context, &consumer, name))
                .is_none()
        );
        assert!(
            context
                .store()
                .value_symbol_links(symbol(&context, method(&declarations, name)))
                .is_none()
        );
    }
    assert_cold_members(&context, &declarations);
    assert_replay(&mut context, &declarations, &consumer);
}

#[test]
fn type_only_forwarding_retains_its_marker_and_rejects_a_value_read() {
    let library = parse_source_file(ES5);
    let declarations =
        parse_source_file(&AMBIENT.replace("import toolkit =", "import type toolkit ="));
    let consumer = parse_source_file(
        "import { parent } from 'portable:routes'; const result = parent('part/file');",
    );
    let marker = declaration(
        &declarations,
        DECLARATIONS,
        SyntaxKind::ImportEqualsDeclaration,
        "toolkit",
    );
    for resolve_first in [false, true] {
        let mut context = context(&library, &declarations, &consumer);
        let alias = imported(&context, &consumer, "parent");
        let target = symbol(&context, method(&declarations, "parent"));
        if resolve_first {
            assert_eq!(
                context.resolve_alias(alias).unwrap().target,
                AliasTargetState::Resolved(target)
            );
        }
        assert!(matches!(
            context.check_source_file(CONSUMER),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(_)
            ))
        ));
        for _ in 0..2 {
            assert_eq!(
                context.resolve_alias(alias).unwrap().target,
                AliasTargetState::Resolved(target)
            );
            assert_eq!(
                context
                    .store()
                    .alias_symbol_links(alias)
                    .unwrap()
                    .type_only_declaration,
                Some(marker)
            );
        }
        assert!(context.store().value_symbol_links(alias).is_none());
        assert!(context.store().value_symbol_links(target).is_none());
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn unsupported_ambient_member_shapes_do_not_publish_import_values() {
    let library = parse_source_file(ES5);
    let consumer = parse_source_file(
        "import { parent } from 'portable:routes'; const result = parent('part/file');",
    );
    let cases = [
        ("missing member", AMBIENT.replace("parent(input: string): string;", "")),
        ("generic owner", AMBIENT.replace("interface Paths {", "interface Paths<T> {").replace("alternate: Paths;", "alternate: Paths<T>;").replace("toolkit.Paths;", "toolkit.Paths<string>;")),
        ("inherited member", AMBIENT.replace("interface Paths { parent(input: string): string;", "interface Base { parent(input: string): string; } interface Paths extends Base {")),
        ("own method with heritage", AMBIENT.replace("interface Paths {", "interface Base {} interface Paths extends Base {")),
        ("optional method", AMBIENT.replace("parent(input:", "parent?(input:")),
        ("property callable", AMBIENT.replace("parent(input: string): string;", "parent: (input: string) => string;")),
        ("conflicting export", AMBIENT.replace("const toolkit: toolkit.Paths;", "export const parent: number; const toolkit: toolkit.Paths;")),
        ("forwarding cycle", concat!(
            "declare module 'route-tools' { import toolkit = require('portable:routes'); export = toolkit; } ",
            "declare module 'portable:routes' { import toolkit = require('route-tools'); export = toolkit; }",
        ).to_owned()),
    ];
    for (name, text) in cases {
        let declarations = parse_source_file(&text);
        let mut context = context(&library, &declarations, &consumer);
        let alias = imported(&context, &consumer, "parent");
        for _ in 0..2 {
            assert!(
                matches!(
                    context.resolve_alias(alias),
                    Err(CanonicalAliasQueryError::AliasResolution(
                        CanonicalAliasResolutionError::TargetUnavailable { .. }
                    )),
                ),
                "{name}"
            );
            assert!(
                context.store().value_symbol_links(alias).is_none(),
                "{name}"
            );
            assert!(context.store().type_resolution_is_empty(), "{name}");
        }
        assert!(
            matches!(
                context.check_source_file(CONSUMER),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(_)
                ))
            ),
            "{name}"
        );
        assert!(
            context.store().value_symbol_links(alias).is_none(),
            "{name}"
        );
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(CONSUMER).unwrap())
                .is_some_and(|links| links.type_checked),
            "{name}"
        );
        assert!(context.diagnostics().is_empty(), "{name}");
    }
}

#[test]
fn a_later_unsupported_member_keeps_earlier_import_values_unpublished() {
    let library = parse_source_file(ES5);
    let declarations = parse_source_file(AMBIENT);
    let consumer = parse_source_file(concat!(
        "import { parent, alternate } from 'portable:routes'; ",
        "const selected = parent('part/file'); const unsupported = alternate;",
    ));
    let mut context = context(&library, &declarations, &consumer);
    assert!(matches!(
        context.check_source_file(CONSUMER),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(_)
        ))
    ));
    for name in ["parent", "alternate"] {
        assert!(
            context
                .store()
                .value_symbol_links(imported(&context, &consumer, name))
                .is_none()
        );
    }
    assert!(
        !context
            .store()
            .source_file_links(context.source_file(CONSUMER).unwrap())
            .is_some_and(|links| links.type_checked)
    );
    assert!(context.diagnostics().is_empty());
    assert!(context.store().type_resolution_is_empty());
}
