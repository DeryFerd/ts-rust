use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

use super::{AstScope, SemanticStore, SourceNodeFacts};
use crate::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifest, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, CanonicalTypeMapperStore,
    DeclaredTypeHost,
    module_resolution::validate_module_resolution_manifest,
    production::GlobalMergeCompletion,
    source_imports::{
        SourceImportError, SourceImportInvariant, plan_source_class_annotation_type_import,
        prepare_source_class_annotation_type_import,
    },
};

type RoleStore = SemanticStore<(), ()>;

#[derive(Clone, Copy, Debug)]
struct AnnotationHolder {
    declaration: NodeRef,
    name: NodeRef,
    annotation: Option<NodeRef>,
    initializer: Option<NodeRef>,
}

fn annotation_holders(parsed: &ParseResult, file: FileId) -> Vec<AnnotationHolder> {
    parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let (name, annotation, initializer) = match &record.data {
                NodeData::ParameterDeclaration(parameter) => {
                    (parameter.name, parameter.type_, parameter.initializer)
                }
                NodeData::PropertyDeclaration(property) => {
                    (property.name, property.type_, property.initializer)
                }
                _ => return None,
            };
            let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
            Some(AnnotationHolder {
                declaration: reference(id),
                name: reference(name),
                annotation: annotation.map(reference),
                initializer: initializer.map(reference),
            })
        })
        .collect()
}

fn facts_mut<TypePayload, MapperPayload>(
    store: &mut SemanticStore<TypePayload, MapperPayload>,
    node: NodeRef,
) -> &mut SourceNodeFacts {
    store.source_node_facts.get_mut(&node.arena).unwrap()[node.node.index()]
        .as_mut()
        .unwrap()
}

#[test]
fn class_annotation_roles_keep_written_types_with_initializers_and_absence() {
    let parsed = parse_source_file(concat!(
        "class Roles { typed: number; initialized: string = 'value'; absent; inferred = 1; ",
        "constructor(required: number, defaulted: number = 500, missing?, guessed = 2) {} } ",
        "let outside: number = 0; interface Other { field: number; }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(98_350);
    let holders = annotation_holders(&parsed, file);
    assert_eq!(holders.len(), 8);
    assert_eq!(
        holders
            .iter()
            .filter(|role| role.annotation.is_some())
            .count(),
        4
    );
    assert_eq!(
        holders
            .iter()
            .filter(|role| role.annotation.is_some() && role.initializer.is_some())
            .count(),
        2
    );
    let mut store = RoleStore::new();
    assert!(store.register_ast_scope(AstScope::new(file, &parsed.arena)));
    for role in &holders {
        assert_eq!(store.source_class_annotation_role(role.declaration), None);
    }
    store
        .register_source_file(&parsed.arena, parsed.source_file, file)
        .unwrap();
    let facts = store.source_node_facts.clone();
    let children = store.source_node_children.clone();
    for _ in 0..2 {
        for role in &holders {
            assert_eq!(
                store.source_class_annotation_role(role.declaration),
                role.annotation,
                "{role:?}"
            );
            assert_ne!(role.annotation, Some(role.name));
            if let Some(initializer) = role.initializer {
                assert_ne!(role.annotation, Some(initializer));
            }
        }
        for (id, record) in parsed.arena.iter() {
            if !matches!(
                record.kind,
                SyntaxKind::Parameter | SyntaxKind::PropertyDeclaration
            ) {
                assert_eq!(
                    store.source_class_annotation_role(NodeRef::new(parsed.arena.id(), file, id)),
                    None
                );
            }
        }
        assert_eq!(store.source_node_facts, facts);
        assert_eq!(store.source_node_children, children);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep each damaged role and its restoration in the same source fixture.
fn class_annotation_roles_reject_wrong_identity_and_damaged_edges() {
    let source = "class Roles { field: number = 1; constructor(value: string = 'value') {} }";
    let parsed = parse_source_file(source);
    let foreign = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty());
    assert!(foreign.diagnostics.is_empty());
    let file = FileId::new(98_351);
    let foreign_file = FileId::new(98_352);
    let holders = annotation_holders(&parsed, file);
    let [field, parameter] = holders.as_slice() else {
        panic!("the source has one field and one constructor parameter")
    };
    let mut store = RoleStore::new();
    store
        .register_source_file(&parsed.arena, parsed.source_file, file)
        .unwrap();
    store
        .register_source_file(&foreign.arena, foreign.source_file, foreign_file)
        .unwrap();
    let facts = store.source_node_facts.clone();
    let children = store.source_node_children.clone();
    for (role, other) in [(field, parameter), (parameter, field)] {
        let holder = role.declaration;
        let annotation = role.annotation.unwrap();
        for wrong in [
            NodeRef::new(holder.arena, foreign_file, holder.node),
            NodeRef::new(foreign.arena.id(), file, holder.node),
            NodeRef::new(holder.arena, file, NodeId::new(u32::MAX)),
            annotation,
            role.name,
        ] {
            assert_eq!(store.source_class_annotation_role(wrong), None);
        }

        for wrong_role in [
            None,
            Some(role.name.node),
            role.initializer.map(|node| node.node),
            other.annotation.map(|node| node.node),
        ] {
            facts_mut(&mut store, holder).class_annotation_role = wrong_role;
            for _ in 0..2 {
                assert_eq!(store.source_class_annotation_role(holder), None);
                assert_eq!(
                    facts_mut(&mut store, holder).class_annotation_role,
                    wrong_role
                );
            }
            facts_mut(&mut store, holder).class_annotation_role = Some(annotation.node);
            assert_eq!(store.source_class_annotation_role(holder), Some(annotation));
        }

        let holder_kind = facts_mut(&mut store, holder).kind;
        facts_mut(&mut store, holder).kind = SyntaxKind::VariableDeclaration;
        assert_eq!(store.source_class_annotation_role(holder), None);
        facts_mut(&mut store, holder).kind = holder_kind;

        let annotation_kind = facts_mut(&mut store, annotation).kind;
        facts_mut(&mut store, annotation).kind = SyntaxKind::NumericLiteral;
        assert_eq!(store.source_class_annotation_role(holder), None);
        facts_mut(&mut store, annotation).kind = annotation_kind;

        let parent = facts_mut(&mut store, annotation).parent;
        for wrong_parent in [None, Some(other.declaration.node)] {
            facts_mut(&mut store, annotation).parent = wrong_parent;
            assert_eq!(store.source_class_annotation_role(holder), None);
        }
        facts_mut(&mut store, annotation).parent = parent;

        let original = store.source_node_children[&holder.arena][holder.node.index()].clone();
        let missing = original
            .iter()
            .copied()
            .filter(|node| *node != annotation.node)
            .collect::<Vec<_>>();
        let mut duplicate = original.to_vec();
        duplicate.push(annotation.node);
        for changed in [missing, duplicate] {
            store.source_node_children.get_mut(&holder.arena).unwrap()[holder.node.index()] =
                changed.into_boxed_slice();
            assert_eq!(store.source_class_annotation_role(holder), None);
        }
        store.source_node_children.get_mut(&holder.arena).unwrap()[holder.node.index()] = original;
        assert_eq!(store.source_class_annotation_role(holder), Some(annotation));
        assert_eq!(store.source_node_facts, facts);
        assert_eq!(store.source_node_children, children);
    }
}

#[test]
fn class_annotation_roles_reject_changed_source_registration_and_restore() {
    let mut parsed = parse_source_file(
        "class Roles { field: number = 1; constructor(value: string = 'value') {} }",
    );
    assert!(parsed.diagnostics.is_empty());
    let file = FileId::new(98_353);
    let holders = annotation_holders(&parsed, file);
    assert_eq!(holders.len(), 2);
    let mut store = RoleStore::new();
    let source = store
        .register_source_file(&parsed.arena, parsed.source_file, file)
        .unwrap();
    let facts = store.source_node_facts.clone();
    let children = store.source_node_children.clone();
    for role in holders {
        let original = parsed.arena.get(role.declaration.node).unwrap().clone();
        let record = parsed.arena.get_mut(role.declaration.node).unwrap();
        match &mut record.data {
            NodeData::ParameterDeclaration(parameter) => {
                std::mem::swap(&mut parameter.type_, &mut parameter.initializer);
            }
            NodeData::PropertyDeclaration(property) => {
                std::mem::swap(&mut property.type_, &mut property.initializer);
            }
            _ => panic!("the selected holder is a parameter or field"),
        }
        for _ in 0..2 {
            assert_eq!(
                store.register_source_file(&parsed.arena, parsed.source_file, file),
                None
            );
            assert_eq!(
                store.source_class_annotation_role(role.declaration),
                role.annotation
            );
            assert_eq!(store.source_node_facts, facts);
            assert_eq!(store.source_node_children, children);
            assert_eq!(store.source_files.get(&file), Some(&source));
        }
        *parsed.arena.get_mut(role.declaration.node).unwrap() = original;
        assert_eq!(
            store.register_source_file(&parsed.arena, parsed.source_file, file),
            Some(source)
        );
        assert_eq!(
            store.source_class_annotation_role(role.declaration),
            role.annotation
        );
        assert_eq!(store.source_node_facts, facts);
        assert_eq!(store.source_node_children, children);
    }
}

fn import_context(
    sources: [&ParseResult; 2],
    files: [FileId; 2],
) -> (
    CanonicalCheckerContext<'_>,
    [BoundFile; 2],
    CanonicalModuleResolutionManifest,
) {
    let mut binder = CanonicalBinder::new();
    for (parsed, file) in sources.into_iter().zip(files) {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/class-role-{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let specifier = sources[0]
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::ImportDeclaration(import) => Some(NodeRef::new(
                sources[0].arena.id(),
                files[0],
                import.module_specifier,
            )),
            _ => None,
        })
        .unwrap();
    let input = || {
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                files[1],
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )])
    };
    let context = CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        sources
            .into_iter()
            .zip(files)
            .map(|(parsed, file)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
        input(),
    )
    .unwrap();
    let bounds = files.map(|file| context.file(file).unwrap().1.clone());
    let manifest = validate_module_resolution_manifest(
        input(),
        context.store().symbol_store(),
        sources
            .into_iter()
            .zip(&bounds)
            .map(|(parsed, bound)| (bound.file_id(), &parsed.arena, bound)),
    )
    .unwrap();
    (context, bounds, manifest)
}

#[test]
#[allow(clippy::too_many_lines)] // Cold and warm plans must reject the same role damage without publishing state.
fn class_annotation_import_plans_reject_changed_roles_before_and_after_alias_preparation() {
    let source = parse_source_file(concat!(
        "import type { Status } from './status'; ",
        "export class Reply { field: Status = 500; constructor(value: Status = 500) {} }",
    ));
    let provider = parse_source_file("export type Status = number;");
    let sources = [&source, &provider];
    let files = [FileId::new(98_354), FileId::new(98_355)];
    let (mut context, bounds, manifest) = import_context(sources, files);
    let host = DeclaredTypeHost::new_after_global_merge(
        sources
            .into_iter()
            .zip(&bounds)
            .map(|(parsed, bound)| (&parsed.arena, bound)),
        GlobalMergeCompletion::for_test(context.options().name_resolution),
    )
    .unwrap()
    .with_module_resolutions(&manifest);
    let holders = annotation_holders(&source, files[0]);
    assert_eq!(holders.len(), 2);
    let plans = holders
        .iter()
        .map(|role| {
            plan_source_class_annotation_type_import(
                context.store(),
                &host,
                role.annotation.unwrap(),
            )
            .unwrap()
            .unwrap()
        })
        .collect::<Vec<_>>();
    let alias = plans[0].alias_symbol();
    let target = plans[0].target_symbol();
    let bound_symbol = |source: &ParseResult, bound: &BoundFile, kind| {
        let declaration = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == kind).then_some(NodeRef::new(
                    source.arena.id(),
                    bound.file_id(),
                    node,
                ))
            })
            .unwrap();
        context
            .store()
            .get_merged_symbol(bound.symbol(declaration).unwrap())
            .unwrap()
    };
    assert_eq!(
        alias,
        bound_symbol(&source, &bounds[0], SyntaxKind::ImportSpecifier)
    );
    assert_eq!(
        target,
        bound_symbol(&provider, &bounds[1], SyntaxKind::TypeAliasDeclaration)
    );
    let owner = bound_symbol(&source, &bounds[0], SyntaxKind::ClassDeclaration);
    assert_eq!(plans[1].alias_symbol(), alias);
    assert_eq!(plans[1].target_symbol(), target);
    assert_ne!(plans[0].root(), plans[1].root());
    for (role, plan) in holders.iter().zip(&plans) {
        assert_eq!(plan.owner(), owner);
        assert_eq!(plan.root(), role.annotation.unwrap());
        assert_eq!(plan.reference(), role.annotation.unwrap());
        assert_eq!(plan.validate_current(context.store()), Ok(false));
        assert!(
            context
                .store()
                .type_node_links(role.initializer.unwrap())
                .is_none()
        );
    }
    assert!(context.store().alias_symbol_links(alias).is_none());
    let snapshot = |store: &CanonicalTypeMapperStore| {
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.type_alias_len_internal(),
                store.symbol_store().symbol_table_len(),
            ],
            store.alias_symbol_links(alias).cloned(),
            holders
                .iter()
                .map(|role| {
                    (
                        store.symbol_node_links(role.annotation.unwrap()).cloned(),
                        store.type_node_links(role.annotation.unwrap()).cloned(),
                        store.type_node_links(role.initializer.unwrap()).cloned(),
                        store
                            .value_symbol_links(bounds[0].symbol(role.declaration).unwrap())
                            .cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store.type_alias_links(target).cloned(),
            store.declared_type_links(target).cloned(),
            store.value_symbol_links(alias).cloned(),
            store.value_symbol_links(target).cloned(),
        )
    };
    let retained = context.store().source_node_facts.clone();
    for warm in [false, true] {
        if warm {
            prepare_source_class_annotation_type_import(
                context.store_mut_for_test(),
                &host,
                &plans[0],
            )
            .unwrap();
        }
        let before = snapshot(context.store());
        for (index, (role, plan)) in holders.iter().zip(&plans).enumerate() {
            let annotation = role.annotation.unwrap();
            let other_annotation = holders[1 - index].annotation.unwrap();
            assert_eq!(plan.validate_current(context.store()), Ok(warm));
            for wrong in [
                None,
                role.initializer.map(|node| node.node),
                Some(other_annotation.node),
            ] {
                facts_mut(context.store_mut_for_test(), role.declaration).class_annotation_role =
                    wrong;
                for _ in 0..2 {
                    let error = SourceImportError::Invariant(SourceImportInvariant::InvalidNode(
                        annotation,
                    ));
                    assert_eq!(plan.validate_current(context.store()), Err(error.clone()));
                    assert_eq!(
                        prepare_source_class_annotation_type_import(
                            context.store_mut_for_test(),
                            &host,
                            plan
                        ),
                        Err(error)
                    );
                    assert_eq!(snapshot(context.store()), before);
                }
                facts_mut(context.store_mut_for_test(), role.declaration).class_annotation_role =
                    Some(annotation.node);
                assert_eq!(plan.validate_current(context.store()), Ok(warm));
                assert_eq!(
                    plan_source_class_annotation_type_import(context.store(), &host, annotation),
                    Ok(Some(plan.clone()))
                );
                assert_eq!(snapshot(context.store()), before);
                assert_eq!(context.store().source_node_facts, retained);
            }
        }
        assert!(context.diagnostics().is_empty());
    }
}
