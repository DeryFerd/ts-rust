use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, TypeData,
    TypeId, ValueSymbolLinks,
    type_records::StructuredTypeData,
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

const DECLARATIONS: FileId = FileId::new(206_300);
const MAIN: FileId = FileId::new(206_301);

// Complete pinned Go input at dc37b5249ab60e2bbce936f71b883e6c8136167e.
const ORIGINAL_CASE: &str = r"// @allowJs: true
// @checkJs: true
// @noEmit: true

// @filename: react.d.ts
declare namespace React {
    class Component {}
    class PureComponent {}
}

// @filename: main.js
/**
 * @extends {React.Component}
 */
class C extends React.PureComponent {}

/**
 * @extends {React.Component}
 */
class D extends React.Component {}
";

fn original_units() -> (&'static str, &'static str) {
    let (options, units) = ORIGINAL_CASE
        .split_once("// @filename: react.d.ts\n")
        .unwrap();
    assert_eq!(
        options,
        "// @allowJs: true\n// @checkJs: true\n// @noEmit: true\n\n"
    );
    units.split_once("// @filename: main.js\n").unwrap()
}

fn context<'arena>(
    declarations: &'arena ParseResult,
    main: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, name, language, declaration_file) in [
        (
            DECLARATIONS,
            declarations,
            "\"/.src/react.d.ts\"",
            CanonicalSourceLanguage::TypeScript,
            true,
        ),
        (
            MAIN,
            main,
            "\"/.src/main.js\"",
            CanonicalSourceLanguage::JavaScript,
            false,
        ),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    language,
                    declaration_file,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    binder
        .bind_typescript_declaration_slice(&declarations.arena, DECLARATIONS)
        .unwrap();
    binder
        .bind_javascript_declaration_slice(&main.arena, MAIN)
        .unwrap();
    // The public checker admits JS through these source facts and checks it on demand.
    // The fixture test also retains the frontend allowJs and checkJs options.
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(DECLARATIONS, &declarations.arena), (MAIN, &main.arena)],
        CanonicalCheckerOptions {
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, node)
}

fn identifier(parsed: &ParseResult, node: NodeRef) -> &str {
    let record = parsed.arena.get(node.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::Identifier);
    let NodeData::Identifier(name) = &record.data else {
        panic!("the original name must remain an identifier")
    };
    &name.text
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Heritage {
    class: NodeRef,
    class_name: NodeRef,
    wrapper: NodeRef,
    whole: NodeRef,
    qualifier: NodeRef,
    leaf: NodeRef,
}

fn heritages(parsed: &ParseResult) -> Vec<Heritage> {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("the original JavaScript must retain its source file")
    };
    source
        .statements
        .nodes
        .iter()
        .map(|&node| {
            let class_node = reference(parsed, MAIN, node);
            let record = parsed.arena.get(node).unwrap();
            let NodeData::ClassDeclaration(class) = &record.data else {
                panic!("the original statements must remain classes")
            };
            assert_eq!(record.parent, Some(parsed.source_file));
            assert!(class.type_parameters.is_none());
            assert!(class.members.nodes.is_empty());
            let [clause] = class.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
                panic!("each original class has one heritage clause")
            };
            let clause_record = parsed.arena.get(*clause).unwrap();
            assert_eq!(clause_record.parent, Some(node));
            let NodeData::HeritageClause(heritage) = &clause_record.data else {
                panic!("the class must own its actual heritage clause")
            };
            assert_eq!(heritage.token, SyntaxKind::ExtendsKeyword);
            let [wrapper] = heritage.types.nodes.as_slice() else {
                panic!("the clause must contain one original base")
            };
            let wrapper_record = parsed.arena.get(*wrapper).unwrap();
            assert_eq!(wrapper_record.parent, Some(*clause));
            let NodeData::ExpressionWithTypeArguments(expression) = &wrapper_record.data else {
                panic!("the clause must retain its original expression wrapper")
            };
            assert!(expression.type_arguments.is_none());
            let whole = parsed.arena.get(expression.expression).unwrap();
            assert_eq!(whole.parent, Some(*wrapper));
            let NodeData::QualifiedName(name) = &whole.data else {
                panic!("the parser retains this heritage expression as a qualified name")
            };
            for child in [name.left, name.right] {
                assert_eq!(
                    parsed.arena.get(child).unwrap().parent,
                    Some(expression.expression)
                );
            }
            Heritage {
                class: class_node,
                class_name: reference(parsed, MAIN, class.name.unwrap()),
                wrapper: reference(parsed, MAIN, *wrapper),
                whole: reference(parsed, MAIN, expression.expression),
                qualifier: reference(parsed, MAIN, name.left),
                leaf: reference(parsed, MAIN, name.right),
            }
        })
        .collect()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassIdentity {
    declaration: NodeRef,
    name: NodeRef,
    owner: SemanticSymbolId,
    local: SemanticSymbolId,
    prototype: SemanticSymbolId,
    namespace: SemanticSymbolId,
    namespace_name: NodeRef,
}

#[allow(clippy::too_many_lines)] // One source path proves the namespace, export, local and prototype owners.
fn class_identity(
    context: &CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    main: &ParseResult,
    heritage: Heritage,
) -> ClassIdentity {
    let namespace_text = identifier(main, heritage.qualifier);
    let class_text = identifier(main, heritage.leaf);
    let NodeData::SourceFile(source) = &declarations
        .arena
        .get(declarations.source_file)
        .unwrap()
        .data
    else {
        panic!("the declaration input must retain its source file")
    };
    let (namespace_node, module) = source
        .statements
        .nodes
        .iter()
        .find_map(|&node| {
            let record = declarations.arena.get(node)?;
            let NodeData::ModuleDeclaration(module) = &record.data else {
                return None;
            };
            let name = reference(declarations, DECLARATIONS, module.name);
            (identifier(declarations, name) == namespace_text).then_some((node, module))
        })
        .unwrap();
    let namespace_node = reference(declarations, DECLARATIONS, namespace_node);
    let block_node = module.body.unwrap();
    let block_record = declarations.arena.get(block_node).unwrap();
    assert_eq!(block_record.parent, Some(namespace_node.node));
    let NodeData::ModuleBlock(block) = &block_record.data else {
        panic!("the namespace must retain its written body")
    };
    let (declaration, name) = block
        .statements
        .nodes
        .iter()
        .find_map(|&node| {
            let record = declarations.arena.get(node)?;
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let name = reference(declarations, DECLARATIONS, class.name?);
            (identifier(declarations, name) == class_text)
                .then_some((reference(declarations, DECLARATIONS, node), name))
        })
        .unwrap();
    assert_eq!(
        declarations.arena.get(declaration.node).unwrap().parent,
        Some(block_node)
    );
    assert_eq!(
        declarations.arena.get(name.node).unwrap().parent,
        Some(declaration.node)
    );
    let bound = context.file(DECLARATIONS).unwrap().1;
    let namespace = bound.symbol(namespace_node).unwrap();
    let owner = bound.symbol(declaration).unwrap();
    let local = bound.local_symbol(declaration).unwrap();
    assert_ne!(owner, local);
    let store = context.store();
    let namespace_record = store.symbol(namespace).unwrap();
    assert_eq!(namespace_record.flags(), SymbolFlags::VALUE_MODULE);
    assert_eq!(namespace_record.declarations(), Some(&[namespace_node][..]));
    assert_eq!(namespace_record.value_declaration(), Some(namespace_node));
    let class = store.symbol(owner).unwrap();
    assert_eq!(class.flags(), SymbolFlags::CLASS);
    assert_eq!(class.check_flags(), CheckFlags::NONE);
    assert_eq!(class.name().as_utf8(), Some(class_text));
    assert_eq!(class.declarations(), Some(&[declaration][..]));
    assert_eq!(class.value_declaration(), Some(declaration));
    assert_eq!(class.parent(), Some(namespace));
    assert_eq!(class.export_symbol(), None);
    assert_eq!(store.get_merged_symbol(owner), Some(owner));
    assert_eq!(
        store
            .symbol_table(namespace_record.exports().unwrap())
            .unwrap()
            .get_source(class_text),
        Some(owner)
    );
    assert_eq!(
        store
            .symbol_table(bound.locals(namespace_node).unwrap())
            .unwrap()
            .get_source(class_text),
        Some(local)
    );
    let proxy = store.symbol(local).unwrap();
    assert_eq!(proxy.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(proxy.declarations(), Some(&[declaration][..]));
    assert_eq!(proxy.export_symbol(), Some(owner));
    assert_eq!(proxy.value_declaration(), None);
    let exports = store.symbol_table(class.exports().unwrap()).unwrap();
    assert_eq!(exports.len(), 1);
    let prototype = exports.get_source("prototype").unwrap();
    let prototype_record = store.symbol(prototype).unwrap();
    assert_eq!(
        prototype_record.flags(),
        SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
    );
    assert_eq!(prototype_record.parent(), Some(owner));
    assert_eq!(prototype_record.declarations(), None);
    ClassIdentity {
        declaration,
        name,
        owner,
        local,
        prototype,
        namespace,
        namespace_name: reference(declarations, DECLARATIONS, module.name),
    }
}

fn checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .store()
        .source_file_links(context.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> (String, CanonicalCheckerDiagnostics) {
    (
        format!("{:?}", context.store()),
        context.diagnostics().clone(),
    )
}

#[allow(clippy::too_many_lines)] // Keep the actual instance and value identities with their public queries.
fn query_roles(
    context: &mut CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    main: &ParseResult,
    heritage: Heritage,
    class: ClassIdentity,
    leaf_first: bool,
) -> (TypeId, TypeId) {
    let (instance, value) = if leaf_first {
        let value = context.get_type_at_location(heritage.leaf).unwrap();
        let instance = context.get_type_at_location(heritage.whole).unwrap();
        (instance, value)
    } else {
        let before = context.store().value_symbol_links(class.owner).cloned();
        let instance = context.get_type_at_location(heritage.whole).unwrap();
        assert_eq!(
            context.store().value_symbol_links(class.owner),
            before.as_ref()
        );
        let value = context.get_type_at_location(heritage.leaf).unwrap();
        (instance, value)
    };
    assert_ne!(instance, value);
    assert_eq!(
        context.get_declared_type_of_symbol(class.owner),
        Ok(instance)
    );
    assert_eq!(
        context.get_type_at_location(class.declaration),
        Ok(instance)
    );
    assert_eq!(context.get_type_at_location(class.name), Ok(instance));
    assert_eq!(context.get_type_at_location(heritage.whole), Ok(instance));
    assert_eq!(context.get_type_at_location(heritage.leaf), Ok(value));
    for node in [class.declaration, class.name, heritage.whole, heritage.leaf] {
        assert_eq!(context.get_symbol_at_location(node), Ok(Some(class.owner)));
    }
    let shells = context.get_class_query_shells(class.owner).unwrap();
    assert_eq!(shells.symbol(), class.owner);
    assert_eq!(shells.declaration(), class.declaration);
    assert_eq!(shells.instance_type(), instance);
    assert_eq!(shells.value_type(), value);

    let namespace = context.get_type_at_location(heritage.qualifier).unwrap();
    assert_eq!(
        context.get_type_at_location(class.namespace_name),
        Ok(namespace)
    );
    for node in [heritage.qualifier, class.namespace_name] {
        assert_eq!(
            context.get_symbol_at_location(node),
            Ok(Some(class.namespace))
        );
    }
    assert_eq!(
        context.store().type_payload(namespace).unwrap().symbol(),
        Some(class.namespace)
    );

    let source_owner = context
        .file(MAIN)
        .unwrap()
        .1
        .symbol(heritage.class)
        .unwrap();
    let source_instance = context.get_type_at_location(heritage.class_name).unwrap();
    assert_eq!(
        context.get_type_at_location(heritage.class),
        Ok(source_instance)
    );
    assert_eq!(
        context.get_declared_type_of_symbol(source_owner),
        Ok(source_instance)
    );
    assert_eq!(
        context.get_symbol_at_location(heritage.class_name),
        Ok(Some(source_owner))
    );
    assert_ne!(source_instance, instance);
    assert!(context.store().value_symbol_links(source_owner).is_none());

    let qualified = format!(
        "{}.{}",
        identifier(main, heritage.qualifier),
        identifier(main, heritage.leaf)
    );
    assert_eq!(
        context
            .type_to_string_at_location(instance, heritage.wrapper)
            .unwrap(),
        qualified
    );
    assert_eq!(
        context
            .type_to_string_at_location(value, heritage.whole)
            .unwrap(),
        format!("typeof {qualified}")
    );
    assert_eq!(
        context
            .type_to_string_at_location(namespace, heritage.whole)
            .unwrap(),
        format!("typeof {}", identifier(main, heritage.qualifier))
    );
    assert_eq!(
        context
            .type_to_string_at_location(instance, class.name)
            .unwrap(),
        identifier(declarations, class.name)
    );
    assert_eq!(
        context
            .type_to_string_at_location(source_instance, heritage.class)
            .unwrap(),
        identifier(main, heritage.class_name)
    );

    let store = context.store();
    assert_eq!(
        store
            .declared_type_links(class.owner)
            .unwrap()
            .declared_type,
        Some(instance)
    );
    assert_eq!(
        store.value_symbol_links(class.owner),
        Some(&ValueSymbolLinks {
            resolved_type: Some(value),
            ..ValueSymbolLinks::default()
        })
    );
    for symbol in [class.local, class.prototype] {
        assert!(
            store
                .value_symbol_links(symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
    }
    let instance_record = store.type_payload(instance).unwrap();
    assert_eq!(instance_record.flags(), TypeFlags::OBJECT);
    assert_eq!(
        instance_record.object_flags(),
        ObjectFlags::CLASS | ObjectFlags::REFERENCE
    );
    assert_eq!(instance_record.symbol(), Some(class.owner));
    let TypeData::Interface(instance_data) = instance_record.data() else {
        panic!("the base must keep its canonical declared instance")
    };
    assert_eq!(instance_data.reference.object.target, Some(instance));
    assert_eq!(
        instance_data.resolved_base_constructor_type,
        Some(store.intrinsic_bootstrap().unwrap().undefined_type)
    );
    assert_eq!(instance_data.resolved_base_types, None);
    assert!(!instance_data.declared_members_resolved);
    assert_eq!(
        instance_data.reference.object.structured,
        StructuredTypeData::default()
    );
    let this = store
        .type_payload(instance_data.this_type.unwrap())
        .unwrap();
    assert_eq!(this.symbol(), Some(class.owner));
    assert!(
        matches!(this.data(), TypeData::TypeParameter(parameter) if parameter.is_this_type && parameter.constraint == Some(instance))
    );
    let value_record = store.type_payload(value).unwrap();
    assert_eq!(value_record.flags(), TypeFlags::OBJECT);
    assert_eq!(value_record.object_flags(), ObjectFlags::ANONYMOUS);
    assert_eq!(value_record.symbol(), Some(class.owner));
    let TypeData::Object(object) = value_record.data() else {
        panic!("the constructor must be the real anonymous static side")
    };
    assert_eq!(object.structured, StructuredTypeData::default());
    assert_eq!(class_identity(context, declarations, main, heritage), class);
    (instance, value)
}

fn assert_original_diagnostic(context: &CanonicalCheckerContext<'_>) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the complete original fixture must retain exactly TS8023")
    };
    assert_eq!(diagnostic.diagnostic.code(), 8023);
    assert_eq!(diagnostic.node.unwrap().file, MAIN);
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["extends", "Component", "PureComponent"]
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "JSDoc '@extends Component' does not match the 'extends PureComponent' clause."
    );
    let range = diagnostic.range_override.unwrap().range();
    assert_eq!(range.start.get(), 23);
    assert_eq!(range.len(), 9);
    assert!(diagnostic.related_information.is_empty());
}

#[test]
fn original_jsdoc_heritage_keeps_instance_and_constructor_query_roles() {
    let (declaration_text, main_text) = original_units();
    let declarations = parse_source_file(declaration_text);
    let main = parse_javascript_source_file(main_text);
    let rows = heritages(&main);
    assert_eq!(rows.len(), 2);
    for source_first in [false, true] {
        for leaf_first in [false, true] {
            let mut context = context(&declarations, &main);
            assert_eq!(context.file_order(), &[DECLARATIONS, MAIN]);
            assert!(context.options().no_emit);
            assert!(
                context
                    .file(DECLARATIONS)
                    .unwrap()
                    .1
                    .source_facts()
                    .unwrap()
                    .is_declaration_file()
            );
            assert!(
                context
                    .file(MAIN)
                    .unwrap()
                    .1
                    .source_facts()
                    .unwrap()
                    .is_javascript_file()
            );
            let identities = rows
                .iter()
                .map(|&row| class_identity(&context, &declarations, &main, row))
                .collect::<Vec<_>>();
            if source_first {
                context.check_source_file(DECLARATIONS).unwrap();
                context.check_source_file(MAIN).unwrap();
                assert_original_diagnostic(&context);
            } else {
                assert!(!checked(&context, MAIN));
                assert!(context.diagnostics().is_empty());
            }
            for row in &rows {
                let owner = context.file(MAIN).unwrap().1.symbol(row.class).unwrap();
                assert!(context.store().declared_type_links(owner).is_none());
                assert!(context.store().value_symbol_links(owner).is_none());
            }
            let mut types = Vec::new();
            for (&row, &class) in rows.iter().zip(&identities) {
                assert!(context.store().value_symbol_links(class.owner).is_none());
                types.push(query_roles(
                    &mut context,
                    &declarations,
                    &main,
                    row,
                    class,
                    leaf_first,
                ));
                assert!(checked(&context, MAIN));
                assert_original_diagnostic(&context);
            }
            assert_eq!(identities[0].namespace, identities[1].namespace);
            assert_ne!(identities[0].owner, identities[1].owner);
            assert_ne!(types[0].0, types[1].0);
            assert_ne!(types[0].1, types[1].1);
            context.check_source_file(DECLARATIONS).unwrap();
            let warm = snapshot(&context);
            for _ in 0..2 {
                context.recheck_source_file(DECLARATIONS).unwrap();
                context.recheck_source_file(MAIN).unwrap();
                for index in (0..rows.len()).rev() {
                    assert_eq!(
                        query_roles(
                            &mut context,
                            &declarations,
                            &main,
                            rows[index],
                            identities[index],
                            !leaf_first
                        ),
                        types[index]
                    );
                }
                assert_original_diagnostic(&context);
                assert_eq!(snapshot(&context), warm);
            }
        }
    }
}

#[test]
fn renamed_namespace_class_values_keep_distinct_same_named_owners() {
    let declarations = parse_source_file(concat!(
        "declare namespace Archive { class Entry {} }\n",
        "declare namespace Ledger { class Entry {} }\n",
    ));
    let main = parse_javascript_source_file(concat!(
        "/** @extends {Archive.Entry} */\nclass Left extends Archive.Entry {}\n",
        "/** @extends {Ledger.Entry} */\nclass Right extends Ledger.Entry {}\n",
    ));
    let rows = heritages(&main);
    assert_eq!(rows.len(), 2);
    for leaf_first in [false, true] {
        let mut context = context(&declarations, &main);
        let first = class_identity(&context, &declarations, &main, rows[0]);
        let second = class_identity(&context, &declarations, &main, rows[1]);
        assert_eq!(identifier(&declarations, first.name), "Entry");
        assert_eq!(identifier(&declarations, second.name), "Entry");
        assert_ne!(first.namespace, second.namespace);
        assert_ne!(first.owner, second.owner);
        assert_ne!(first.local, second.local);
        assert_ne!(first.prototype, second.prototype);
        let first_types = query_roles(
            &mut context,
            &declarations,
            &main,
            rows[0],
            first,
            leaf_first,
        );
        assert!(context.store().value_symbol_links(second.owner).is_none());
        let second_types = query_roles(
            &mut context,
            &declarations,
            &main,
            rows[1],
            second,
            !leaf_first,
        );
        assert_ne!(first_types.0, second_types.0);
        assert_ne!(first_types.1, second_types.1);
        assert!(context.diagnostics().is_empty());
        context.check_source_file(DECLARATIONS).unwrap();
        let warm = snapshot(&context);
        for _ in 0..2 {
            context.recheck_source_file(MAIN).unwrap();
            context.recheck_source_file(DECLARATIONS).unwrap();
            assert_eq!(
                query_roles(
                    &mut context,
                    &declarations,
                    &main,
                    rows[1],
                    second,
                    leaf_first
                ),
                second_types
            );
            assert_eq!(
                query_roles(
                    &mut context,
                    &declarations,
                    &main,
                    rows[0],
                    first,
                    !leaf_first
                ),
                first_types
            );
            assert!(context.diagnostics().is_empty());
            assert_eq!(snapshot(&context), warm);
        }
    }
}
