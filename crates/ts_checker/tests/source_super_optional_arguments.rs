use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData,
    signatures::SignatureFlags,
};
use ts_diagnostics::Category;
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(204_280);
const ES5_FILE: FileId = FileId::new(204_281);
const ERROR_FILE: FileId = FileId::new(204_282);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");
const ERROR: &str = include_str!("../../ts_bundled/libs/lib.es2022.error.d.ts");

fn context<'a>(
    source: &'a ParseResult,
    es5: &'a ParseResult,
    error: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (ES5_FILE, es5, "\"/lib/lib.es5.d.ts\""),
        (ERROR_FILE, error, "\"/lib/lib.es2022.error.d.ts\""),
        (SOURCE, source, "\"/project/super-optional-arguments.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file != SOURCE,
                    file != SOURCE,
                    if file == SOURCE {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn only(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(id, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), SOURCE, id))
    });
    let node = nodes.next().unwrap();
    assert!(nodes.next().is_none());
    node
}

fn error_constructor(parsed: &ParseResult, file: FileId) -> NodeRef {
    let mut declarations = parsed.arena.iter().filter_map(|(_, record)| {
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
            return None;
        };
        (name.text == "ErrorConstructor").then_some(interface)
    });
    let interface = declarations.next().unwrap();
    assert!(declarations.next().is_none());
    let mut constructors = interface.members.nodes.iter().filter_map(|&id| {
        (parsed.arena.get(id).unwrap().kind == SyntaxKind::ConstructSignature)
            .then_some(NodeRef::new(parsed.arena.id(), file, id))
    });
    let constructor = constructors.next().unwrap();
    assert!(constructors.next().is_none());
    constructor
}

fn check_case(message_type: &str, invalid: bool) {
    let source = format!(
        "type Options = {{ message?: {message_type}; cause?: unknown }};\n\
         export class RequestError extends Error {{\n\
         constructor(options?: Options) {{\n\
         super(options?.message, {{ cause: options?.cause }});\n\
         }}\n}}\n"
    );
    let parsed = parse_source_file(&source);
    let es5 = parse_source_file(ES5);
    let error = parse_source_file(ERROR);
    let class = only(&parsed, SyntaxKind::ClassDeclaration);
    let call = only(&parsed, SyntaxKind::CallExpression);
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(data.expression).unwrap().kind,
        SyntaxKind::SuperKeyword
    );
    let [message, options] = data.arguments.nodes.as_slice() else {
        panic!("the super call must retain both actual arguments")
    };
    let message = NodeRef::new(parsed.arena.id(), SOURCE, *message);
    let options = NodeRef::new(parsed.arena.id(), SOURCE, *options);
    let cause = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(access.name)?.data else {
                return None;
            };
            (name.text == "cause").then_some(NodeRef::new(parsed.arena.id(), SOURCE, id))
        })
        .unwrap();
    for (node, text) in [(message, "options?.message"), (cause, "options?.cause")] {
        let record = parsed.arena.get(node.node).unwrap();
        let NodeData::PropertyAccessExpression(access) = &record.data else {
            unreachable!()
        };
        assert!(access.question_dot_token.is_some());
        assert_eq!(
            &source[record.range.start.get() as usize..record.range.end.get() as usize],
            text
        );
    }
    let declarations = [
        error_constructor(&es5, ES5_FILE),
        error_constructor(&error, ERROR_FILE),
    ];

    for members_first in [false, true] {
        let mut checker = context(&parsed, &es5, &error);
        assert!(checker.global_types().diagnostics().is_empty());
        let raw = checker.file(SOURCE).unwrap().1.symbol(class).unwrap();
        let owner = checker.store().get_merged_symbol(raw).unwrap();
        let early = members_first.then(|| checker.get_nongeneric_class_members(owner).unwrap());
        checker.check_source_file(SOURCE).unwrap();
        let members = checker.get_nongeneric_class_members(owner).unwrap();
        if let Some(early) = early {
            assert_eq!(early, members);
        }
        let base = members.base().unwrap();
        let selected = checker
            .store()
            .signature_links(call)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let signature = checker.store().signature(selected).unwrap();
        assert_eq!(signature.declaration(), Some(declarations[1]));
        assert_eq!(signature.flags(), SignatureFlags::CONSTRUCT);
        assert_eq!(signature.parameters().len(), 2);
        assert_eq!(signature.min_argument_count(), 0);
        assert_eq!(signature.resolved_return_type(), Some(base.instance_type()));
        for (declaration, count) in declarations.iter().zip([1, 2]) {
            let id = checker
                .store()
                .signature_links(*declaration)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            let record = checker.store().signature(id).unwrap();
            assert_eq!(record.declaration(), Some(*declaration));
            assert_eq!(record.parameters().len(), count);
            assert_eq!(record.resolved_return_type(), Some(base.instance_type()));
        }

        let message_type = checker.get_type_at_location(message).unwrap();
        let cause_type = checker.get_type_at_location(cause).unwrap();
        let options_type = checker.get_type_at_location(options).unwrap();
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let scalar = if invalid {
            bootstrap.number_type
        } else {
            bootstrap.string_type
        };
        let TypeData::Union(union) = checker.store().type_payload(message_type).unwrap().data()
        else {
            panic!("optional message access must preserve undefined")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&scalar));
        assert!(union.union.types.contains(&bootstrap.undefined_type));
        assert_eq!(cause_type, bootstrap.unknown_type);
        assert_ne!(options_type, bootstrap.any_type);
        let void = bootstrap.void_type;
        assert_eq!(checker.get_type_at_location(call).unwrap(), void);
        if invalid {
            let [diagnostic] = checker.diagnostics().as_slice() else {
                panic!("expected one native optional-message argument error")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2345);
            assert_eq!(diagnostic.diagnostic.category(), Category::Error);
            assert_eq!(diagnostic.node, Some(message));
            assert!(diagnostic.range_override.is_none());
        } else {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.type_alias_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                ],
                parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let node = NodeRef::new(parsed.arena.id(), SOURCE, id);
                        (
                            store.type_node_links(node).cloned(),
                            store.signature_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                store
                    .symbol_store()
                    .symbols()
                    .map(|(id, _)| (id, store.value_symbol_links(id).cloned()))
                    .collect::<Vec<_>>(),
                checker.diagnostics().clone(),
            )
        };
        let before = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(SOURCE).unwrap();
            checker.recheck_source_file(SOURCE).unwrap();
            assert_eq!(
                checker.get_nongeneric_class_members(owner).unwrap(),
                members
            );
            assert_eq!(checker.get_type_at_location(message).unwrap(), message_type);
            assert_eq!(checker.get_type_at_location(cause).unwrap(), cause_type);
            assert_eq!(checker.get_type_at_location(options).unwrap(), options_type);
            assert_eq!(checker.get_type_at_location(call).unwrap(), void);
            assert_eq!(
                checker
                    .store()
                    .signature_links(call)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(selected)
            );
            assert_eq!(snapshot(&checker), before);
        }
    }
}

#[test]
fn super_optional_properties_keep_real_error_overloads_and_types() {
    check_case("string", false);
}

#[test]
fn super_optional_numeric_message_reports_native_argument_error() {
    check_case("number", true);
}
