use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId, types::TypeFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(495_600);
const PROVIDER: FileId = FileId::new(495_601);
const ROUTER: &str = concat!(
    "export interface Router<T> {\n",
    "  name: string;\n",
    "  add(method: string, path: string, handler: T): void;\n",
    "  match(method: string, path: string): T;\n",
    "}\n",
);

fn context<'a>(source: &'a ParseResult, provider: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (SOURCE, source, "\"/project/source.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
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
    let specifier = source
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::ImportDeclaration(import) => {
                Some(node(source, SOURCE, import.module_specifier))
            }
            _ => None,
        })
        .unwrap();
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            module_kind: ModuleKind::EsNext,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn name_node(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::ClassDeclaration(data) => data.name.unwrap(),
        NodeData::InterfaceDeclaration(data) => data.name,
        NodeData::VariableDeclaration(data) => data.name,
        NodeData::PropertyDeclaration(data) => data.name,
        NodeData::PropertySignatureDeclaration(data) => data.name,
        NodeData::MethodDeclaration(data) => data.name,
        NodeData::MethodSignatureDeclaration(data) => data.name,
        _ => panic!("expected a named declaration"),
    };
    node(parsed, declaration.file, name)
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .filter(|(_, record)| record.kind == kind)
        .map(|(id, _)| node(parsed, file, id))
        .find(|&declaration| {
            let name = name_node(parsed, declaration);
            matches!(&parsed.arena.get(name.node).unwrap().data,
                NodeData::Identifier(name) if name.text == expected)
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn member(parsed: &ParseResult, owner: NodeRef, expected: &str) -> NodeRef {
    let members = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::ClassDeclaration(data) => &data.members.nodes,
        NodeData::InterfaceDeclaration(data) => &data.members.nodes,
        _ => panic!("expected a class or interface"),
    };
    members
        .iter()
        .filter(|&&id| parsed.arena.get(id).unwrap().kind != SyntaxKind::Constructor)
        .map(|&id| node(parsed, owner.file, id))
        .find(|&declaration| {
            let name = name_node(parsed, declaration);
            matches!(&parsed.arena.get(name.node).unwrap().data,
                NodeData::Identifier(name) if name.text == expected)
        })
        .unwrap_or_else(|| panic!("missing member {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn variable_part(parsed: &ParseResult, name: &str, annotation: bool) -> NodeRef {
    let declaration = named(parsed, SOURCE, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let part = if annotation { data.type_ } else { data.initializer };
    node(parsed, SOURCE, part.unwrap())
}

fn heritage(parsed: &ParseResult, class: NodeRef) -> NodeRef {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    let [clause] = data.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one implements clause")
    };
    let NodeData::HeritageClause(data) = &parsed.arena.get(*clause).unwrap().data else {
        unreachable!()
    };
    assert_eq!(data.token, SyntaxKind::ImplementsKeyword);
    let [implementation] = data.types.nodes.as_slice() else {
        panic!("expected one written implementation")
    };
    let record = parsed.arena.get(*implementation).unwrap();
    assert_eq!(record.parent, Some(*clause));
    let NodeData::ExpressionWithTypeArguments(data) = &record.data else {
        panic!("the original generic heritage must remain in the source")
    };
    let [argument] = data.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one written type argument")
    };
    assert_eq!(
        parsed.arena.get(*argument).unwrap().parent,
        Some(*implementation)
    );
    node(parsed, class.file, *implementation)
}

fn formal(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    owner: NodeRef,
) -> TypeId {
    let parameters = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::ClassDeclaration(data) => data.type_parameters.as_ref().unwrap(),
        NodeData::InterfaceDeclaration(data) => data.type_parameters.as_ref().unwrap(),
        _ => panic!("expected the original generic declaration"),
    };
    let [parameter] = parameters.nodes.as_slice() else {
        panic!("expected one declared type parameter")
    };
    let parameter = node(parsed, owner.file, *parameter);
    let owner_symbol = symbol(context, owner);
    let parameter_symbol = symbol(context, parameter);
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(owner.node)
    );
    assert_eq!(
        context.store().symbol(parameter_symbol).unwrap().parent(),
        Some(owner_symbol)
    );
    let type_ = context.get_declared_type_of_symbol(parameter_symbol).unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(record.symbol(), Some(parameter_symbol));
    let TypeData::TypeParameter(data) = record.data() else {
        panic!("the source formal must keep its actual type")
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    type_
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    target: TypeId,
    argument: TypeId,
) {
    let TypeData::TypeReference(data) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected the canonical instantiated reference")
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(
        data.resolved_type_arguments.as_deref(),
        Some([argument].as_slice())
    );
}

fn assert_import(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    target: SemanticSymbolId,
) {
    let bindings = source
        .arena
        .iter()
        .filter(|(_, record)| record.kind == SyntaxKind::ImportSpecifier)
        .map(|(id, _)| symbol(context, node(source, SOURCE, id)))
        .collect::<Vec<_>>();
    let [binding] = bindings.as_slice() else {
        panic!("expected the actual imported type binding")
    };
    assert_ne!(*binding, target);
    assert_eq!(
        context
            .store()
            .alias_symbol_links(*binding)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(target),
    );
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn assert_mapped_read(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    name: &str,
    original: NodeRef,
    source_formal: TypeId,
    expected: TypeId,
) {
    let expression = variable_part(source, name, false);
    let call = match &source.arena.get(expression.node).unwrap().data {
        NodeData::CallExpression(data) => Some(node(source, SOURCE, data.expression)),
        NodeData::PropertyAccessExpression(_) => None,
        _ => panic!("expected a real member read or call"),
    };
    let access = call.unwrap_or(expression);
    let NodeData::PropertyAccessExpression(data) = &source.arena.get(access.node).unwrap().data
    else {
        unreachable!()
    };
    assert_eq!(context.get_type_at_location(expression), Ok(expected));
    let copied = context
        .get_symbol_at_location(node(source, SOURCE, data.name))
        .unwrap()
        .unwrap();
    let original_symbol = symbol(context, original);
    assert_ne!(copied, original_symbol);
    let links = context.store().value_symbol_links(copied).unwrap();
    assert_eq!(links.target, Some(original_symbol));
    let mapper = links.mapper.unwrap();
    assert_eq!(
        context.store().map_type(mapper, source_formal),
        Some(expected)
    );
    let copied_symbol = context.store().symbol(copied).unwrap();
    assert!(copied_symbol.check_flags().contains(CheckFlags::INSTANTIATED));
    assert_eq!(
        copied_symbol.declarations(),
        context.store().symbol(original_symbol).unwrap().declarations()
    );
    if call.is_some() {
        let original_signature = signature(context, original);
        let selected = signature(context, expression);
        assert_eq!(context.get_return_type_of_signature(selected), Ok(expected));
        let record = context.store().signature(selected).unwrap();
        assert_eq!(record.target(), Some(original_signature));
        assert_eq!(record.declaration(), Some(original));
        assert_eq!(record.mapper(), Some(mapper));
        assert!(record.type_parameters().is_empty());
    } else {
        assert_eq!(links.resolved_type, Some(expected));
    }
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let nodes = [(SOURCE, source), (PROVIDER, provider)]
        .into_iter()
        .flat_map(|(file, parsed)| {
            parsed.arena.iter().map(move |(id, _)| {
                let node = node(parsed, file, id);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
        })
        .collect::<Vec<_>>();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
        nodes,
    )
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) {
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(PROVIDER).unwrap();
    assert_eq!(context.diagnostics(), &diagnostics);
    let before = snapshot(context, source, provider);
    for _ in 0..2 {
        for file in [SOURCE, PROVIDER] {
            context.check_source_file(file).unwrap();
            context.recheck_source_file(file).unwrap();
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .unwrap()
                    .type_checked
            );
        }
        assert_eq!(snapshot(context, source, provider), before);
    }
}

fn assert_diagnostic(
    diagnostic: &CanonicalCheckerDiagnostic,
    node: NodeRef,
    code: u32,
    arguments: &[&str],
    text: &str,
) {
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.arguments, arguments);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), text);
}

fn assert_missing_note(
    diagnostic: &CanonicalCheckerDiagnostic,
    provider: &ParseResult,
    member: NodeRef,
    name: &str,
) {
    let [note] = diagnostic.related_information.as_slice() else {
        panic!("expected the missing member's source declaration")
    };
    assert_eq!(note.node, Some(name_node(provider, member)));
    assert_eq!(note.diagnostic.code(), 2728);
    assert_eq!(note.diagnostic.arguments, [name]);
    assert_eq!(
        note.diagnostic.render().unwrap(),
        format!("'{name}' is declared here.")
    );
}

#[test]
#[allow(clippy::too_many_lines)] // The source class and imported interface share mapped call checks.
fn imported_generic_router_keeps_formals_mapped_members_and_replay() {
    let provider = parse_source_file(ROUTER);
    let source = parse_source_file(concat!(
        "import type { Router } from './provider';\n",
        "export class TrieRouter<T> implements Router<T> {\n",
        "  name: string = 'TrieRouter';\n",
        "  value: T;\n",
        "  constructor(value: T) { this.value = value; }\n",
        "  add(method: string, path: string, handler: T): void { this.value = handler; }\n",
        "  match(method: string, path: string): T { return this.value; }\n",
        "}\n",
        "declare const strings: TrieRouter<string>;\n",
        "declare const numbers: TrieRouter<number>;\n",
        "declare const contract: Router<string>;\n",
        "strings.add('GET', '/', 'handler');\n",
        "numbers.add('GET', '/', 1);\n",
        "const stringResult = strings.match('GET', '/');\n",
        "const numberResult = numbers.match('GET', '/');\n",
        "const contractResult = contract.match('GET', '/');\n",
        "const stringField = strings.value;\n",
        "const numberField = numbers.value;\n",
        "const accepted: Router<string> = strings;\n",
    ));
    for (provider_first, query_first) in [(false, false), (true, false), (false, true)] {
        let mut context = context(&source, &provider);
        let class = named(&source, SOURCE, SyntaxKind::ClassDeclaration, "TrieRouter");
        let target = named(&provider, PROVIDER, SyntaxKind::InterfaceDeclaration, "Router");
        let owner = symbol(&context, class);
        let target_owner = symbol(&context, target);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        let early = query_first.then(|| context.get_declared_type_of_symbol(owner).unwrap());
        context.check_source_file(SOURCE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_import(&context, &source, target_owner);
        let instance = context.get_declared_type_of_symbol(owner).unwrap();
        if let Some(early) = early {
            assert_eq!(early, instance);
        }
        let target_type = context.get_declared_type_of_symbol(target_owner).unwrap();
        let class_formal = formal(&mut context, &source, class);
        let target_formal = formal(&mut context, &provider, target);
        assert_ne!(class_formal, target_formal);
        let implemented = context
            .get_type_from_type_node(heritage(&source, class))
            .unwrap();
        assert_reference(&context, implemented, target_type, class_formal);
        assert!(
            context
                .get_nongeneric_class_members(owner)
                .unwrap()
                .base()
                .is_none()
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let strings = context
            .get_type_from_type_node(variable_part(&source, "strings", true))
            .unwrap();
        let numbers = context
            .get_type_from_type_node(variable_part(&source, "numbers", true))
            .unwrap();
        let contract = context
            .get_type_from_type_node(variable_part(&source, "contract", true))
            .unwrap();
        assert_ne!(strings, numbers);
        assert_reference(&context, strings, instance, string);
        assert_reference(&context, numbers, instance, number);
        assert_reference(&context, contract, target_type, string);
        assert_eq!(
            context.get_type_from_type_node(variable_part(&source, "accepted", true)),
            Ok(contract)
        );
        assert_eq!(context.is_type_assignable_to(strings, contract), Ok(true));
        assert_eq!(context.is_type_assignable_to(numbers, contract), Ok(false));
        for (name, type_) in [("stringResult", string), ("numberResult", number)] {
            assert_mapped_read(
                &mut context,
                &source,
                name,
                member(&source, class, "match"),
                class_formal,
                type_,
            );
        }
        for (name, type_) in [("stringField", string), ("numberField", number)] {
            assert_mapped_read(
                &mut context,
                &source,
                name,
                member(&source, class, "value"),
                class_formal,
                type_,
            );
        }
        assert_mapped_read(
            &mut context,
            &source,
            "contractResult",
            member(&provider, target, "match"),
            target_formal,
            string,
        );
        assert_replay(&mut context, &source, &provider);
        assert_eq!(
            context.get_type_from_type_node(heritage(&source, class)),
            Ok(implemented)
        );
        assert_eq!(context.get_declared_type_of_symbol(owner), Ok(instance));
        assert_eq!(
            context.get_declared_type_of_symbol(target_owner),
            Ok(target_type)
        );
    }
}

#[test]
fn imported_generic_router_reports_missing_and_incompatible_members() {
    let provider = parse_source_file(ROUTER);
    let source = parse_source_file(concat!(
        "import type { Router } from './provider';\n",
        "class MissingRouter<T> implements Router<T> {\n",
        "  name: string = 'MissingRouter';\n",
        "  add(method: string, path: string, handler: T): void {}\n",
        "}\n",
        "class NumberRouter implements Router<string> {\n",
        "  name: string = 'NumberRouter';\n",
        "  add(method: string, path: string, handler: string): void {}\n",
        "  match(method: string, path: string): number { return 1; }\n",
        "}\n",
    ));
    for provider_first in [false, true] {
        let mut context = context(&source, &provider);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(SOURCE).unwrap();
        let missing = named(&source, SOURCE, SyntaxKind::ClassDeclaration, "MissingRouter");
        let wrong = named(&source, SOURCE, SyntaxKind::ClassDeclaration, "NumberRouter");
        let target = named(&provider, PROVIDER, SyntaxKind::InterfaceDeclaration, "Router");
        let [missing_diagnostic, wrong_diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected the two native implements diagnostics: {:?}",
                context.diagnostics()
            )
        };
        assert_diagnostic(
            missing_diagnostic,
            name_node(&source, missing),
            2420,
            &["MissingRouter<T>", "Router<T>"],
            concat!(
                "Class 'MissingRouter<T>' incorrectly implements interface 'Router<T>'.\n",
                "  Property 'match' is missing in type 'MissingRouter<T>' but required in type 'Router<T>'.",
            ),
        );
        assert_missing_note(
            missing_diagnostic,
            &provider,
            member(&provider, target, "match"),
            "match",
        );
        assert_diagnostic(
            wrong_diagnostic,
            name_node(&source, member(&source, wrong, "match")),
            2416,
            &["match", "NumberRouter", "Router<string>"],
            concat!(
                "Property 'match' in type 'NumberRouter' is not assignable to the same property in base type 'Router<string>'.\n",
                "  Type '(method: string, path: string) => number' is not assignable to type '(method: string, path: string) => string'.\n",
                "    Type 'number' is not assignable to type 'string'.",
            ),
        );
        assert!(wrong_diagnostic.related_information.is_empty());
        let wrong_owner = symbol(&context, wrong);
        let wrong_type = context.get_declared_type_of_symbol(wrong_owner).unwrap();
        let implemented = context
            .get_type_from_type_node(heritage(&source, wrong))
            .unwrap();
        let target_owner = symbol(&context, target);
        let target_type = context.get_declared_type_of_symbol(target_owner).unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_reference(&context, implemented, target_type, string);
        assert_eq!(
            context.is_type_assignable_to(wrong_type, implemented),
            Ok(false)
        );
        assert_import(&context, &source, target_owner);
        assert_replay(&mut context, &source, &provider);
    }
}

#[test]
fn imported_generic_class_target_keeps_own_members_and_missing_diagnostic() {
    let provider = parse_source_file(concat!(
        "export class Box<T> {\n",
        "  value: T;\n",
        "  constructor(value: T) { this.value = value; }\n",
        "}\n",
    ));
    let source = parse_source_file(concat!(
        "import type { Box } from './provider';\n",
        "export class ValueBox<T> implements Box<T> {\n",
        "  value: T;\n",
        "  constructor(value: T) { this.value = value; }\n",
        "}\n",
        "class MissingBox<T> implements Box<T> {}\n",
        "declare const values: ValueBox<number>;\n",
        "const value = values.value;\n",
        "const accepted: Box<number> = values;\n",
    ));
    for provider_first in [false, true] {
        let mut context = context(&source, &provider);
        if provider_first {
            context.check_source_file(PROVIDER).unwrap();
        }
        context.check_source_file(SOURCE).unwrap();
        let class = named(&source, SOURCE, SyntaxKind::ClassDeclaration, "ValueBox");
        let missing = named(&source, SOURCE, SyntaxKind::ClassDeclaration, "MissingBox");
        let target = named(&provider, PROVIDER, SyntaxKind::ClassDeclaration, "Box");
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected one missing class member diagnostic: {:?}",
                context.diagnostics()
            )
        };
        assert_diagnostic(
            diagnostic,
            name_node(&source, missing),
            2720,
            &["MissingBox<T>", "Box<T>"],
            concat!(
                "Class 'MissingBox<T>' incorrectly implements class 'Box<T>'. Did you mean to extend 'Box<T>' and inherit its members as a subclass?\n",
                "  Property 'value' is missing in type 'MissingBox<T>' but required in type 'Box<T>'.",
            ),
        );
        assert_missing_note(
            diagnostic,
            &provider,
            member(&provider, target, "value"),
            "value",
        );
        let owner = symbol(&context, class);
        let target_owner = symbol(&context, target);
        let instance = context.get_declared_type_of_symbol(owner).unwrap();
        let target_type = context.get_declared_type_of_symbol(target_owner).unwrap();
        let class_formal = formal(&mut context, &source, class);
        let target_formal = formal(&mut context, &provider, target);
        assert_ne!(class_formal, target_formal);
        let implemented = context
            .get_type_from_type_node(heritage(&source, class))
            .unwrap();
        assert_reference(&context, implemented, target_type, class_formal);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let values = context
            .get_type_from_type_node(variable_part(&source, "values", true))
            .unwrap();
        let accepted = context
            .get_type_from_type_node(variable_part(&source, "accepted", true))
            .unwrap();
        assert_reference(&context, values, instance, number);
        assert_reference(&context, accepted, target_type, number);
        assert_eq!(context.is_type_assignable_to(values, accepted), Ok(true));
        let members = context.get_nongeneric_class_members(owner).unwrap();
        assert!(members.base().is_none());
        let own_value = symbol(&context, member(&source, class, "value"));
        let target_value = symbol(&context, member(&provider, target, "value"));
        assert_ne!(own_value, target_value);
        assert!(members.declared_instance_properties().contains(&own_value));
        assert!(!members.instance_properties().contains(&target_value));
        assert_mapped_read(
            &mut context,
            &source,
            "value",
            member(&source, class, "value"),
            class_formal,
            number,
        );
        assert_import(&context, &source, target_owner);
        assert_replay(&mut context, &source, &provider);
        assert_eq!(
            context.get_type_from_type_node(heritage(&source, class)),
            Ok(implemented)
        );
    }
}
