use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, ResolvedSignatureState,
    SignatureLinks, SourceCheckError, SymbolNodeLinks, TypeData, TypeNodeLinks,
    UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "class Model { value!: string; }\n",
    "const model = new Model();\n",
    "const value = model.value;\n",
);

fn checker_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-default-new.ts\""),
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

fn class_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = class.name.and_then(|name| parsed.arena.get(name))?;
            let NodeData::Identifier(name) = &name.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing class {expected}"))
}

fn class_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = class_declaration(parsed, file, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declaration = variable_declaration(parsed, file, expected);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!("the helper selected a variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable
            .initializer
            .expect("fixture variable is initialized"),
    )
}

fn variable_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = variable_declaration(parsed, file, expected);
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn constructor(parsed: &ParseResult, new_expression: NodeRef) -> NodeRef {
    let NodeData::NewExpression(new_expression_data) =
        &parsed.arena.get(new_expression.node).unwrap().data
    else {
        panic!("expected a new expression")
    };
    NodeRef::new(
        new_expression.arena,
        new_expression.file,
        new_expression_data.expression,
    )
}

fn first_new_expression(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::NewExpression(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("fixture contains a new expression")
}

fn package_class_context<'arena>(
    importer: &'arena ParseResult,
    declaration: &'arena ParseResult,
    importer_file: FileId,
    declaration_file: FileId,
) -> (CanonicalCheckerContext<'arena>, NodeRef) {
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );
    assert!(
        declaration.diagnostics.is_empty(),
        "{:?}",
        declaration.diagnostics
    );
    let (specifier, binding) = importer
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            let clause_node = import.import_clause?;
            let NodeData::ImportClause(clause) = &importer.arena.get(clause_node)?.data else {
                return None;
            };
            let binding = if clause.name.is_some() {
                clause_node
            } else {
                let NodeData::NamedImports(named) =
                    &importer.arena.get(clause.named_bindings?)?.data
                else {
                    return None;
                };
                *named.elements.nodes.first()?
            };
            Some((
                NodeRef::new(importer.arena.id(), importer_file, import.module_specifier),
                NodeRef::new(importer.arena.id(), importer_file, binding),
            ))
        })
        .expect("fixture has one package class import");

    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, ambient) in [
        (importer_file, importer, "\"/makeC.ts\"", false),
        (
            declaration_file,
            declaration,
            "\"/node_modules/pkg/index.d.ts\"",
            true,
        ),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    ambient,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed) in [(importer_file, importer), (declaration_file, declaration)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }

    let context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [
            (importer_file, &importer.arena),
            (declaration_file, &declaration.arena),
        ]
        .into_iter()
        .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                declaration_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap();
    (context, binding)
}

#[test]
#[allow(clippy::too_many_lines)] // The exact multi-file fixture proves alias and class identity.
fn imported_ambient_default_new_preserves_private_fields_and_inferred_returns() {
    let declaration = parse_source_file("export declare class C {\n  private p;\n}\n");
    let importer = parse_source_file(concat!(
        "import { C } from \"pkg\";\n",
        "\n",
        "export function makeC() {\n",
        "  return new C();\n",
        "}\n",
    ));
    assert!(
        declaration.diagnostics.is_empty(),
        "{:?}",
        declaration.diagnostics
    );
    assert!(
        importer.diagnostics.is_empty(),
        "{:?}",
        importer.diagnostics
    );

    let declaration_file = FileId::new(1_820);
    let importer_file = FileId::new(1_821);
    let (module_specifier, binding) = importer
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ImportDeclaration(import) = &record.data else {
                return None;
            };
            let clause = importer.arena.get(import.import_clause?)?;
            let NodeData::ImportClause(clause) = &clause.data else {
                return None;
            };
            let named = importer.arena.get(clause.named_bindings?)?;
            let NodeData::NamedImports(named) = &named.data else {
                return None;
            };
            Some((
                NodeRef::new(importer.arena.id(), importer_file, import.module_specifier),
                NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    *named.elements.nodes.first()?,
                ),
            ))
        })
        .expect("fixture has one named package import");

    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &importer.arena,
            importer.source_file,
            importer_file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/makeC.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    binder
        .bind_source_file_with_facts(
            &declaration.arena,
            declaration.source_file,
            declaration_file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/node_modules/pkg/index.d.ts\""),
                CanonicalSourceLanguage::TypeScript,
                true,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    for (file, parsed) in [(importer_file, &importer), (declaration_file, &declaration)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let mut context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [
            (importer_file, &importer.arena),
            (declaration_file, &declaration.arena),
        ]
        .into_iter()
        .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            module_specifier,
            CanonicalResolvedModuleInput::new(
                declaration_file,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap();

    let target = class_symbol(&declaration, declaration_file, &context, "C");
    let alias = context
        .file(importer_file)
        .unwrap()
        .1
        .symbol(binding)
        .unwrap();
    assert_ne!(alias, target);
    let construction = first_new_expression(&importer, importer_file);
    let constructor = constructor(&importer, construction);
    let function = importer
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(record.data, NodeData::FunctionDeclaration(_)).then_some(NodeRef::new(
                importer.arena.id(),
                importer_file,
                node,
            ))
        })
        .expect("fixture has one exported function");
    let target_source = context.source_file(declaration_file).unwrap();

    context.check_source_file(importer_file).unwrap();

    let members = context.get_nongeneric_class_members(target).unwrap();
    let shells = members.shells();
    let alias_links = context.store().alias_symbol_links(alias).unwrap();
    assert_eq!(alias_links.immediate_target, Some(target));
    assert_eq!(alias_links.alias_target, AliasTargetState::Resolved(target));
    assert!(alias_links.type_only_declaration.is_none());
    assert_eq!(
        context.store().symbol_node_links(constructor),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(alias),
        }),
    );
    assert_eq!(
        context.store().type_node_links(constructor),
        Some(&TypeNodeLinks {
            resolved_type: Some(shells.value_type()),
            ..TypeNodeLinks::default()
        }),
    );
    assert_eq!(
        context.store().signature_links(construction),
        Some(&SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(
                members.default_construct_signature(),
            ),
            ..SignatureLinks::default()
        }),
    );
    assert_eq!(
        context.store().type_node_links(construction),
        Some(&TypeNodeLinks {
            resolved_type: Some(shells.instance_type()),
            ..TypeNodeLinks::default()
        }),
    );
    for symbol in [target, alias] {
        assert_eq!(
            context.store().value_symbol_links(symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(shells.value_type()),
                ..ValueSymbolLinks::default()
            }),
        );
    }
    let function_signature = context
        .store()
        .signature_links(function)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the exported function has an inferred signature");
    assert_eq!(
        context
            .store()
            .signature(function_signature)
            .unwrap()
            .resolved_return_type(),
        Some(shells.instance_type()),
    );

    let &[private_field] = members.declared_instance_properties() else {
        panic!("the imported class retains exactly one private field")
    };
    assert_eq!(
        context
            .store()
            .symbol(private_field)
            .unwrap()
            .name()
            .as_utf8(),
        Some("p"),
    );
    assert_eq!(
        context.store().value_symbol_links(private_field),
        Some(&ValueSymbolLinks {
            resolved_type: Some(context.store().intrinsic_bootstrap().unwrap().any_type),
            ..ValueSymbolLinks::default()
        }),
    );
    assert!(context.diagnostics().is_empty());
    assert!(
        !context
            .store()
            .source_file_links(target_source)
            .is_some_and(|links| links.type_checked),
        "imported declaration files remain unchecked",
    );

    let warm = (
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        context.store().alias_symbol_links(alias).cloned(),
        context.store().symbol_node_links(constructor).cloned(),
        context.store().type_node_links(constructor).cloned(),
        context.store().signature_links(construction).cloned(),
        context.store().type_node_links(construction).cloned(),
        context.store().value_symbol_links(alias).cloned(),
        context.store().value_symbol_links(private_field).cloned(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(importer_file).unwrap();
    assert_eq!(
        (
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().relation_state_snapshot(),
            ),
            context.store().alias_symbol_links(alias).cloned(),
            context.store().symbol_node_links(constructor).cloned(),
            context.store().type_node_links(constructor).cloned(),
            context.store().signature_links(construction).cloned(),
            context.store().type_node_links(construction).cloned(),
            context.store().value_symbol_links(alias).cloned(),
            context.store().value_symbol_links(private_field).cloned(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
#[allow(clippy::too_many_lines)] // The upstream fixture retains two package targets and two users.
fn package_exports_false_fixture_preserves_the_resolved_package_class_through_reexported_calls() {
    let package = parse_source_file("export declare class C {\n  private p;\n}\n");
    let exported_package = parse_source_file("export declare class C {\n  private p;\n}\n");
    let factory = parse_source_file(concat!(
        "import { C } from \"pkg\";\n",
        "export function makeC() {\n",
        "  return new C();\n",
        "}\n",
    ));
    let consumer = parse_source_file(concat!(
        "import { makeC } from \"./makeC\";\n",
        "export const c = makeC();\n",
    ));
    let package_file = FileId::new(1_850);
    let exported_package_file = FileId::new(1_851);
    let factory_file = FileId::new(1_852);
    let consumer_file = FileId::new(1_853);

    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, ambient) in [
        (
            &package,
            package_file,
            "\"/node_modules/pkg/index.d.ts\"",
            true,
        ),
        (
            &exported_package,
            exported_package_file,
            "\"/node_modules/pkg/dist/index.d.ts\"",
            true,
        ),
        (&factory, factory_file, "\"/makeC.ts\"", false),
        (&consumer, consumer_file, "\"/index.ts\"", false),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    ambient,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (parsed, file) in [
        (&package, package_file),
        (&exported_package, exported_package_file),
        (&factory, factory_file),
        (&consumer, consumer_file),
    ] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let import_specifier = |parsed: &ParseResult, file| {
        parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    import.module_specifier,
                ))
            })
            .expect("the user source retains its module import")
    };
    let resolutions = [
        (import_specifier(&factory, factory_file), package_file),
        (import_specifier(&consumer, consumer_file), factory_file),
    ]
    .map(|(specifier, target)| {
        CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                target,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )
    });
    let mut context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        [
            (package_file, &package.arena),
            (exported_package_file, &exported_package.arena),
            (factory_file, &factory.arena),
            (consumer_file, &consumer.arena),
        ]
        .into_iter()
        .collect(),
        CanonicalCheckerOptions::default(),
        CanonicalModuleResolutionManifestInput::new(resolutions),
    )
    .unwrap();
    let resolved_class = class_symbol(&package, package_file, &context, "C");
    let exported_class = class_symbol(&exported_package, exported_package_file, &context, "C");
    assert_ne!(resolved_class, exported_class);

    for file in [
        package_file,
        exported_package_file,
        factory_file,
        consumer_file,
    ] {
        context.check_source_file(file).unwrap();
    }

    let resolved_members = context
        .get_nongeneric_class_members(resolved_class)
        .unwrap();
    let exported_members = context
        .get_nongeneric_class_members(exported_class)
        .unwrap();
    assert_ne!(
        resolved_members.declared_instance_properties(),
        exported_members.declared_instance_properties(),
    );
    let value = variable_symbol(&consumer, consumer_file, &context, "c");
    assert_eq!(
        context
            .store()
            .value_symbol_links(value)
            .and_then(|links| links.resolved_type),
        Some(resolved_members.shells().instance_type()),
    );
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().relation_state_snapshot(),
    );
    context.recheck_source_file(factory_file).unwrap();
    context.recheck_source_file(consumer_file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().relation_state_snapshot(),
        ),
        warm,
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Alias, argument, and warm identities share one source graph.
fn imported_ambient_constructor_arguments_preserve_named_and_default_aliases() {
    for (index, (declaration_text, importer_text, expected)) in [
        (
            concat!(
                "export declare class C {\n",
                "  constructor(value: string);\n",
                "  private p;\n",
                "}\n",
            ),
            concat!(
                "import { C as Renamed } from \"pkg\";\n",
                "export function makeC() { return new Renamed(\"ready\"); }\n",
            ),
            "string",
        ),
        (
            concat!(
                "export default class C {\n",
                "  constructor(value: number);\n",
                "  private p;\n",
                "}\n",
            ),
            concat!(
                "import Selected from \"pkg\";\n",
                "export function makeC() { return new Selected(1); }\n",
            ),
            "number",
        ),
        (
            concat!(
                "export declare class C {\n",
                "  constructor(value: number);\n",
                "  private p;\n",
                "}\n",
                "export { C as default };\n",
            ),
            concat!(
                "import Selected from \"pkg\";\n",
                "export function makeC() { return new Selected(1); }\n",
            ),
            "number",
        ),
        (
            concat!(
                "export declare class C {\n",
                "  constructor(value: string);\n",
                "  private p;\n",
                "}\n",
                "export default C;\n",
            ),
            concat!(
                "import Selected from \"pkg\";\n",
                "export function makeC() { return new Selected(\"ready\"); }\n",
            ),
            "string",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let declaration = parse_source_file(declaration_text);
        let importer = parse_source_file(importer_text);
        let importer_file = FileId::new(1_830 + u32::try_from(index).unwrap() * 2);
        let declaration_file = FileId::new(1_831 + u32::try_from(index).unwrap() * 2);
        let (mut context, binding) =
            package_class_context(&importer, &declaration, importer_file, declaration_file);
        let target = class_symbol(&declaration, declaration_file, &context, "C");
        let alias = context
            .file(importer_file)
            .unwrap()
            .1
            .symbol(binding)
            .unwrap();
        let construction = first_new_expression(&importer, importer_file);
        let NodeData::NewExpression(expression) =
            &importer.arena.get(construction.node).unwrap().data
        else {
            panic!("the constructor fixture must retain its argument")
        };
        let argument = NodeRef::new(
            construction.arena,
            construction.file,
            expression.arguments.as_ref().unwrap().nodes[0],
        );

        if index != 0 {
            context.check_source_file(declaration_file).unwrap();
        }
        context.check_source_file(importer_file).unwrap();

        let members = context.get_nongeneric_class_members(target).unwrap();
        let signature = context
            .store()
            .signature_links(construction)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        assert_eq!(signature, members.default_construct_signature());
        let [parameter] = context.store().signature(signature).unwrap().parameters() else {
            panic!("the imported constructor retains exactly one parameter")
        };
        let parameter_type = context
            .store()
            .value_symbol_links(*parameter)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(parameter_type).unwrap(), expected);
        assert_eq!(
            context
                .store()
                .symbol_node_links(constructor(&importer, construction))
                .and_then(|links| links.resolved_symbol),
            Some(alias),
        );
        assert!(
            context
                .store()
                .type_node_links(argument)
                .and_then(|links| links.resolved_type)
                .is_some(),
        );
        assert_eq!(
            context
                .store()
                .alias_symbol_links(alias)
                .unwrap()
                .alias_target,
            AliasTargetState::Resolved(target),
        );
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
        );
        context.recheck_source_file(importer_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
            ),
            warm,
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Explicit and inferred references require one retained graph.
fn imported_ambient_generic_constructors_preserve_instantiated_class_identity() {
    const GENERIC_PACKAGE: &str = concat!(
        "export declare class Box<T> { private p; }\n",
        "export { Box as default };\n",
    );
    for (index, (declaration_text, importer_text, expected)) in [
        (
            GENERIC_PACKAGE,
            concat!(
                "import { Box } from \"pkg\";\n",
                "export function makeBox() { return new Box<string>(); }\n",
            ),
            "Box<string>",
        ),
        (
            GENERIC_PACKAGE,
            concat!(
                "import { Box } from \"pkg\";\n",
                "export function makeBox() { return new Box(); }\n",
            ),
            "Box<unknown>",
        ),
        (
            GENERIC_PACKAGE,
            concat!(
                "import Selected from \"pkg\";\n",
                "export function makeBox() { return new Selected<number>(); }\n",
            ),
            "Box<number>",
        ),
        (
            concat!(
                "export declare class Box<T> {\n",
                "  constructor(value: number);\n",
                "  private p;\n",
                "}\n",
                "export { Box as default };\n",
            ),
            concat!(
                "import Selected from \"pkg\";\n",
                "export function makeBox() { return new Selected<string>(1); }\n",
            ),
            "Box<string>",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let declaration = parse_source_file(declaration_text);
        let importer = parse_source_file(importer_text);
        let importer_file = FileId::new(1_840 + u32::try_from(index).unwrap() * 2);
        let declaration_file = FileId::new(1_841 + u32::try_from(index).unwrap() * 2);
        let (mut context, binding) =
            package_class_context(&importer, &declaration, importer_file, declaration_file);
        let target = class_symbol(&declaration, declaration_file, &context, "Box");
        let alias = context
            .file(importer_file)
            .unwrap()
            .1
            .symbol(binding)
            .unwrap();
        let construction = first_new_expression(&importer, importer_file);

        if index != 0 {
            context.check_source_file(declaration_file).unwrap();
        }
        context.check_source_file(importer_file).unwrap();

        let members = context.get_nongeneric_class_members(target).unwrap();
        let &[private_field] = members.declared_instance_properties() else {
            panic!("the generic package class must preserve its private field")
        };
        assert_eq!(
            context
                .store()
                .value_symbol_links(private_field)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().any_type),
        );
        let instance = context
            .store()
            .type_node_links(construction)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(instance).unwrap(), expected);
        let TypeData::TypeReference(reference) =
            context.store().type_payload(instance).unwrap().data()
        else {
            panic!("generic construction must preserve its canonical class reference")
        };
        assert_eq!(
            reference.object.target,
            context
                .store()
                .declared_type_links(target)
                .and_then(|links| links.declared_type),
        );
        assert_eq!(reference.resolved_type_arguments.as_ref().unwrap().len(), 1);
        assert_eq!(
            context
                .store()
                .symbol_node_links(constructor(&importer, construction))
                .and_then(|links| links.resolved_symbol),
            Some(alias),
        );
        let signature = context
            .store()
            .signature_links(construction)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let base_signature = members.default_construct_signature();
        assert_ne!(signature, base_signature);
        assert_eq!(
            context
                .store()
                .signature(base_signature)
                .unwrap()
                .type_parameters()
                .len(),
            1,
        );
        assert_eq!(
            context.store().signature(signature).unwrap().target(),
            Some(base_signature),
        );
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(instance),
        );
        assert!(context.diagnostics().is_empty());

        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
        );
        context.recheck_source_file(importer_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
            ),
            warm,
        );
    }
}

#[test]
fn invalid_imported_ambient_constructor_arguments_leave_class_state_cold() {
    let declaration = parse_source_file(concat!(
        "export declare class C {\n",
        "  constructor(value: number);\n",
        "  private p;\n",
        "}\n",
    ));
    for (index, expression) in ["new C()", "new C(\"wrong\")", "new C<string>(1)"]
        .into_iter()
        .enumerate()
    {
        let importer = parse_source_file(&format!(
            "import {{ C }} from \"pkg\"; export function makeC() {{ return {expression}; }}",
        ));
        let importer_file = FileId::new(1_860 + u32::try_from(index).unwrap() * 2);
        let declaration_file = FileId::new(1_861 + u32::try_from(index).unwrap() * 2);
        let (mut context, _) =
            package_class_context(&importer, &declaration, importer_file, declaration_file);
        let target = class_symbol(&declaration, declaration_file, &context, "C");
        let construction = first_new_expression(&importer, importer_file);

        assert_eq!(
            context.check_source_file(importer_file),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                construction,
            ))),
            "{expression}",
        );
        assert!(context.store().declared_type_links(target).is_none());
        assert!(context.store().value_symbol_links(target).is_none());
        assert!(context.store().type_node_links(construction).is_none());
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn default_exported_private_constructor_diagnostics_use_the_declared_class_name() {
    let declaration = parse_source_file(concat!(
        "export default class Hidden {\n",
        "  private constructor();\n",
        "  private p;\n",
        "}\n",
    ));
    let importer = parse_source_file(concat!(
        "import Selected from \"pkg\";\n",
        "export function makeHidden() { return new Selected(); }\n",
    ));
    let importer_file = FileId::new(1_870);
    let declaration_file = FileId::new(1_871);
    let (mut context, _) =
        package_class_context(&importer, &declaration, importer_file, declaration_file);

    context.check_source_file(importer_file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("a private imported constructor must report one accessibility diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2673);
    assert_eq!(diagnostic.diagnostic.arguments, ["Hidden".to_owned()]);
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(importer_file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Constructor identity and warm caches require one source graph.
fn direct_default_new_publishes_exact_instance_signature_and_warm_caches() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_801);
    let mut context = checker_context(&parsed, file);
    let class = class_symbol(&parsed, file, &context, "Model");
    let model = variable_symbol(&parsed, file, &context, "model");
    let value = variable_symbol(&parsed, file, &context, "value");
    let construction = variable_initializer(&parsed, file, "model");
    let constructor = constructor(&parsed, construction);
    let access = variable_initializer(&parsed, file, "value");

    context.check_source_file(file).unwrap();

    let members = context.get_nongeneric_class_members(class).unwrap();
    let shells = members.shells();
    let signature = members.default_construct_signature();
    assert_eq!(
        context.store().symbol_node_links(constructor),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(class),
        })
    );
    assert_eq!(
        context.store().type_node_links(constructor),
        Some(&TypeNodeLinks {
            resolved_type: Some(shells.value_type()),
            ..TypeNodeLinks::default()
        })
    );
    assert_eq!(
        context.store().signature_links(construction),
        Some(&SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        })
    );
    assert_eq!(
        context.store().type_node_links(construction),
        Some(&TypeNodeLinks {
            resolved_type: Some(shells.instance_type()),
            ..TypeNodeLinks::default()
        })
    );
    assert_eq!(
        context.store().value_symbol_links(model),
        Some(&ValueSymbolLinks {
            resolved_type: Some(shells.instance_type()),
            ..ValueSymbolLinks::default()
        })
    );

    let signature_record = context.store().signature(signature).unwrap();
    assert_eq!(signature_record.flags(), SignatureFlags::CONSTRUCT);
    assert!(
        !signature_record
            .flags()
            .intersects(SignatureFlags::ABSTRACT)
    );
    assert!(signature_record.declaration().is_none());
    assert!(signature_record.type_parameters().is_empty());
    assert!(signature_record.parameters().is_empty());
    assert_eq!(signature_record.min_argument_count(), 0);
    assert_eq!(
        signature_record.resolved_return_type(),
        Some(shells.instance_type())
    );

    let value_record = context.store().type_payload(shells.value_type()).unwrap();
    assert_eq!(value_record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        value_record.object_flags(),
        ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
    );
    let TypeData::Object(value_type) = value_record.data() else {
        panic!("class value must use object storage")
    };
    assert_eq!(value_type.structured.call_signature_count, 0);
    assert_eq!(
        value_type.structured.signatures.as_deref(),
        Some(&[signature][..])
    );

    let instance_record = context
        .store()
        .type_payload(shells.instance_type())
        .unwrap();
    let TypeData::Interface(instance) = instance_record.data() else {
        panic!("class instance must use interface storage")
    };
    assert_eq!(
        instance.reference.object.target,
        Some(shells.instance_type())
    );

    let property = members.instance_properties()[0];
    let string_type = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        context.store().symbol_node_links(access),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(property),
        })
    );
    assert_eq!(
        context.store().type_node_links(access),
        Some(&TypeNodeLinks {
            resolved_type: Some(string_type),
            ..TypeNodeLinks::default()
        })
    );
    assert_eq!(
        context.store().value_symbol_links(value),
        Some(&ValueSymbolLinks {
            resolved_type: Some(string_type),
            ..ValueSymbolLinks::default()
        })
    );
    assert!(context.diagnostics().is_empty());

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context.store().symbol_node_links(constructor).cloned(),
        context.store().type_node_links(constructor).cloned(),
        context.store().signature_links(construction).cloned(),
        context.store().type_node_links(construction).cloned(),
        context.store().type_node_links(access).cloned(),
        context.diagnostics().len(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        context.get_nongeneric_class_members(class).unwrap(),
        members
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
            context.store().symbol_node_links(constructor).cloned(),
            context.store().type_node_links(constructor).cloned(),
            context.store().signature_links(construction).cloned(),
            context.store().type_node_links(construction).cloned(),
            context.store().type_node_links(access).cloned(),
            context.diagnostics().len(),
        ),
        warm
    );
}

#[test]
fn derived_default_new_accepts_optional_parentheses_and_reuses_inherited_members() {
    let parsed = parse_source_file(concat!(
        "class Base { base!: string; static count: number; }\n",
        "class Derived extends Base { own!: number; }\n",
        "const explicit = new Derived();\n",
        "const implicit = new Derived;\n",
        "const inherited = implicit.base;\n",
        "const own = explicit.own;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_807);
    let mut context = checker_context(&parsed, file);
    let base_symbol = class_symbol(&parsed, file, &context, "Base");
    let derived_symbol = class_symbol(&parsed, file, &context, "Derived");
    let explicit = variable_initializer(&parsed, file, "explicit");
    let implicit = variable_initializer(&parsed, file, "implicit");
    let inherited = variable_symbol(&parsed, file, &context, "inherited");
    let own = variable_symbol(&parsed, file, &context, "own");

    context.check_source_file(file).unwrap();

    let base = context.get_nongeneric_class_members(base_symbol).unwrap();
    let derived = context
        .get_nongeneric_class_members(derived_symbol)
        .unwrap();
    assert_eq!(
        derived
            .base()
            .map(ts_checker::semantic::ClassBaseIdentities::instance_type),
        Some(base.shells().instance_type())
    );
    for construction in [explicit, implicit] {
        assert_eq!(
            context
                .store()
                .symbol_node_links(constructor(&parsed, construction)),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(derived_symbol),
            })
        );
        assert_eq!(
            context.store().type_node_links(construction),
            Some(&TypeNodeLinks {
                resolved_type: Some(derived.shells().instance_type()),
                ..TypeNodeLinks::default()
            })
        );
        assert_eq!(
            context.store().signature_links(construction),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(
                    derived.default_construct_signature(),
                ),
                ..SignatureLinks::default()
            })
        );
    }
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(inherited)
            .and_then(|links| links.resolved_type),
        Some(bootstrap.string_type)
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(own)
            .and_then(|links| links.resolved_type),
        Some(bootstrap.number_type)
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        warm
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn later_invalid_new_preflights_before_earlier_class_or_new_publication() {
    let parsed = parse_source_file(concat!(
        "class Early { value!: string; }\n",
        "const early = new Early();\n",
        "class Later { value!: string; }\n",
        "const bad = new Later(1);\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_802);
    let mut context = checker_context(&parsed, file);
    let early_class = class_symbol(&parsed, file, &context, "Early");
    let early_new = variable_initializer(&parsed, file, "early");
    let early_constructor = constructor(&parsed, early_new);
    let bad_new = variable_initializer(&parsed, file, "bad");
    let before = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
    );

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
            bad_new
        )))
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().relation_state_snapshot(),
        ),
        before
    );
    assert!(context.store().declared_type_links(early_class).is_none());
    assert!(context.store().value_symbol_links(early_class).is_none());
    assert!(
        context
            .store()
            .symbol_node_links(early_constructor)
            .is_none()
    );
    assert!(context.store().type_node_links(early_constructor).is_none());
    assert!(context.store().signature_links(early_new).is_none());
    assert!(context.store().type_node_links(early_new).is_none());
    assert!(context.diagnostics().is_empty());
}

#[test]
fn unsupported_new_forms_stop_at_typed_boundaries() {
    for (source, expected_node) in [
        (
            "class Model { value!: string; } const model = new Model(1);",
            "new",
        ),
        (
            "class Model { value!: string; } const model = new Model<string>();",
            "new",
        ),
        (
            "const factory = 1; const model = new factory();",
            "constructor",
        ),
        (
            "const model = new Model(); class Model { value!: string; }",
            "constructor",
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_803);
        let construction = first_new_expression(&parsed, file);
        let boundary = if expected_node == "constructor" {
            constructor(&parsed, construction)
        } else {
            construction
        };
        let mut context = checker_context(&parsed, file);
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                boundary
            ))),
            "{source}"
        );
        assert!(context.diagnostics().is_empty());
    }

    let source = "abstract class Model { value!: string; } const model = new Model();";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1_804);
    let mut context = checker_context(&parsed, file);
    assert!(
        matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Class(_)
            ))
        ),
        "{source}"
    );
    assert!(context.diagnostics().is_empty());

    let source = "class Model { value!: string; } const model = new Model?.();";
    let parsed = parse_source_file(source);
    assert!(!parsed.diagnostics.is_empty());
    let file = FileId::new(1_805);
    let mut context = checker_context(&parsed, file);
    assert!(matches!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(_)
        ))
    ));
    assert!(context.diagnostics().is_empty());
}
