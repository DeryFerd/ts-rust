use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolutionError,
    CanonicalProgramBindings, CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerContextError, CanonicalCheckerOptions,
    CanonicalGlobalInitializationError, CanonicalGlobalTypeInitializationError,
    DeclaredTypeError, TypeData, TypeId, TypeNodeUnavailable,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(470_120);

fn bindings(parsed: &ParseResult) -> CanonicalProgramBindings {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/types/entries.d.ts\""),
                CanonicalSourceLanguage::TypeScript,
                true,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    binder.finish()
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    CanonicalCheckerContext::new(
        bindings(parsed),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::ImportSpecifier(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn declared(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap()
}

fn assert_this_type(
    checker: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    expected: bool,
) -> Option<TypeId> {
    let type_ = declared(checker, owner);
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Interface(data) = record.data() else {
        panic!("the declared identity must remain an interface")
    };
    assert!(!data.declared_members_resolved);
    assert!(!data.base_types_resolved);
    assert_eq!(data.this_type.is_some(), expected);
    if let Some(this) = data.this_type {
        assert_eq!(data.all_type_parameters.as_deref(), Some([this].as_slice()));
        assert_eq!(data.reference.object.target, Some(type_));
        let record = checker.store().type_payload(this).unwrap();
        assert_eq!(record.symbol(), Some(owner));
        let TypeData::TypeParameter(parameter) = record.data() else {
            panic!("synthetic this must keep its type-parameter identity")
        };
        assert!(parameter.is_this_type);
        assert_eq!(parameter.constraint, Some(type_));
        assert!(parameter.target.is_none());
        assert!(parameter.mapper.is_none());
    }
    data.this_type
}

fn alias_body(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = declaration(parsed, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(declaration.arena, declaration.file, data.type_)
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.merged_symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[test]
fn ambient_class_and_interface_imports_keep_their_this_identity() {
    let parsed = parse_source_file(concat!(
        "declare module 'entries' {\n",
        "  export class Entry { readonly value: number; }\n",
        "  export interface Shape { label: string; }\n",
        "  import { Entry as ImportedClass, Shape as ImportedShape } from 'entries';\n",
        "  global {\n",
        "    interface ClassView extends ImportedClass {}\n",
        "    interface ShapeView extends ImportedShape {}\n",
        "  }\n",
        "}\n",
        "interface Object extends ShapeView, ClassView {}\n",
        "interface Function extends ClassView {}\n",
    ));
    // Global initialization asks only for declared identities. Function repeats ClassView.
    let checker = context(&parsed);
    let interface = |name| {
        symbol(
            &checker,
            declaration(&parsed, SyntaxKind::InterfaceDeclaration, name),
        )
    };
    let class_view = interface("ClassView");
    let shape_view = interface("ShapeView");
    let object = interface("Object");
    let function = interface("Function");
    assert_this_type(&checker, interface("Shape"), false);
    assert_this_type(&checker, shape_view, false);
    let class_this = assert_this_type(&checker, class_view, true).unwrap();
    let object_this = assert_this_type(&checker, object, true).unwrap();
    let function_this = assert_this_type(&checker, function, true).unwrap();
    assert_ne!(class_this, object_this);
    assert_ne!(class_this, function_this);
    assert_eq!(checker.global_types().object_type, declared(&checker, object));
    assert_eq!(
        checker.global_types().function_type,
        declared(&checker, function)
    );

    let class = symbol(
        &checker,
        declaration(&parsed, SyntaxKind::ClassDeclaration, "Entry"),
    );
    assert_eq!(
        checker.store().symbol(class).unwrap().flags(),
        SymbolFlags::CLASS
    );
    assert!(checker.store().declared_type_links(class).is_none());
    for name in ["ImportedClass", "ImportedShape"] {
        let alias = symbol(
            &checker,
            declaration(&parsed, SyntaxKind::ImportSpecifier, name),
        );
        assert!(checker.store().alias_symbol_links(alias).is_none());
    }
    assert!(checker.diagnostics().is_empty());
}

#[test]
fn ambient_type_references_keep_the_existing_class_boundary() {
    let parsed = parse_source_file(concat!(
        "declare module 'entries' {\n",
        "  export class Entry { value: number; }\n",
        "  export interface Shape { value: number; }\n",
        "  import { Entry as ImportedClass, Shape as ImportedShape } from 'entries';\n",
        "  type ClassUse = ImportedClass;\n",
        "  type ShapeUse = ImportedShape;\n",
        "}\n",
    ));
    let mut checker = context(&parsed);
    let shape_node = alias_body(&parsed, "ShapeUse");
    let class_node = alias_body(&parsed, "ClassUse");
    let shape = symbol(
        &checker,
        declaration(&parsed, SyntaxKind::InterfaceDeclaration, "Shape"),
    );
    let imported_class = symbol(
        &checker,
        declaration(&parsed, SyntaxKind::ImportSpecifier, "ImportedClass"),
    );
    let expected_error = DeclaredTypeError::TypeNodeUnavailable(
        TypeNodeUnavailable::ImportAliasTypeReference {
            node: class_node,
            alias: imported_class,
        },
    );
    let shape_type = checker.get_type_from_type_node(shape_node).unwrap();
    assert_eq!(
        checker.store().type_payload(shape_type).unwrap().symbol(),
        Some(shape)
    );
    assert_eq!(
        checker.get_type_from_type_node(class_node),
        Err(expected_error)
    );
    let stable = counts(&checker);
    let diagnostics = checker.diagnostics().clone();
    for _ in 0..2 {
        assert_eq!(checker.get_type_from_type_node(shape_node), Ok(shape_type));
        assert_eq!(
            checker.get_type_from_type_node(class_node),
            Err(expected_error)
        );
        assert_eq!(counts(&checker), stable);
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert!(checker.store().alias_symbol_links(imported_class).is_none());
    }
}

#[test]
fn ambient_unproved_heritage_keeps_the_name_error() {
    for (export, imported, heritage) in [
        ("export { Entry as Forwarded };", "Forwarded", "Imported"),
        ("", "Forwarded", "Imported"),
        ("", "Entry", "Imported.Missing"),
    ] {
        let parsed = parse_source_file(&format!(
            "declare module 'entries' {{\n\
               export class Entry {{ value: number; }}\n\
               {export}\n\
               import {{ {imported} as Imported }} from 'entries';\n\
               global {{ interface Derived extends {heritage} {{}} }}\n\
             }}\n\
             interface Object extends Derived {{}}\n"
        ));
        let bindings = bindings(&parsed);
        let import = declaration(&parsed, SyntaxKind::ImportSpecifier, "Imported");
        let alias = bindings.file(FILE).unwrap().symbol(import).unwrap();
        let record = bindings.symbol_store().symbol(alias).unwrap();
        assert_eq!(record.name().as_utf8(), Some("Imported"));
        assert_eq!(record.flags(), SymbolFlags::ALIAS);
        assert_eq!(record.declarations(), Some([import].as_slice()));
        let expected = CanonicalCheckerContextError::GlobalInitialization(
            CanonicalGlobalInitializationError::GlobalTypes(
                CanonicalGlobalTypeInitializationError::DeclaredType(
                    DeclaredTypeError::NameResolution(
                        CanonicalNameResolutionError::AliasResolutionUnavailable(alias),
                    ),
                ),
            ),
        );
        let result = CanonicalCheckerContext::new(
            bindings,
            vec![(FILE, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        );
        assert_eq!(result.err(), Some(expected));
    }
}
