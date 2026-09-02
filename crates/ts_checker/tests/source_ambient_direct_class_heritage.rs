use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, DeclaredTypeUnavailable,
    TypeData, TypeNodeUnavailable,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(470_121);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
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
    CanonicalCheckerContext::new(
        binder.finish(),
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
fn ambient_class_heritage_reaches_the_class_member_boundary() {
    let parsed = parse_source_file(concat!(
        "declare module 'entries' {\n",
        "  class Entry { value: number; }\n",
        "  import { Entry as Imported } from 'entries';\n",
        "  global { interface Derived extends Imported {} }\n",
        "}\n",
        "interface Object extends Derived {}\n",
    ));
    let mut checker = context(&parsed);
    let derived_node = declaration(&parsed, SyntaxKind::InterfaceDeclaration, "Derived");
    let derived = symbol(&checker, derived_node);
    let imported = symbol(
        &checker,
        declaration(&parsed, SyntaxKind::ImportSpecifier, "Imported"),
    );
    let class = symbol(
        &checker,
        declaration(&parsed, SyntaxKind::ClassDeclaration, "Entry"),
    );
    assert_eq!(
        checker.store().symbol(class).unwrap().flags(),
        SymbolFlags::CLASS
    );
    assert_eq!(
        checker.store().symbol(imported).unwrap().flags(),
        SymbolFlags::ALIAS
    );

    let NodeData::InterfaceDeclaration(interface) =
        &parsed.arena.get(derived_node.node).unwrap().data
    else {
        unreachable!()
    };
    let clause = interface.heritage_clauses.as_ref().unwrap().nodes[0];
    let NodeData::HeritageClause(clause) = &parsed.arena.get(clause).unwrap().data else {
        unreachable!()
    };
    let NodeData::ExpressionWithTypeArguments(base) =
        &parsed.arena.get(clause.types.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    let expression = NodeRef::new(derived_node.arena, FILE, base.expression);
    let declared = checker
        .store()
        .declared_type_links(derived)
        .unwrap()
        .declared_type
        .unwrap();
    let TypeData::Interface(identity) = checker.store().type_payload(declared).unwrap().data()
    else {
        panic!("global initialization must retain the interface identity")
    };
    let this = identity.this_type.unwrap();
    let expected = DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::UnsupportedSyntax {
        node: expression,
        kind: SyntaxKind::Identifier,
    });

    // The identity is valid. Full member checking still rejects the class base.
    assert_eq!(checker.get_declared_type_of_symbol(derived), Err(expected));
    let stable = counts(&checker);
    let diagnostics = checker.diagnostics().clone();
    for _ in 0..2 {
        assert_eq!(checker.get_declared_type_of_symbol(derived), Err(expected));
        assert_eq!(counts(&checker), stable);
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(
            checker
                .store()
                .declared_type_links(derived)
                .unwrap()
                .declared_type,
            Some(declared)
        );
        let TypeData::Interface(identity) = checker.store().type_payload(declared).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(identity.this_type, Some(this));
        assert!(!identity.declared_members_resolved);
        assert!(!identity.base_types_resolved);
        let this_record = checker.store().type_payload(this).unwrap();
        assert_eq!(this_record.symbol(), Some(derived));
        let TypeData::TypeParameter(parameter) = this_record.data() else {
            unreachable!()
        };
        assert!(parameter.is_this_type);
        assert_eq!(parameter.constraint, Some(declared));
        assert!(checker.store().declared_type_links(class).is_none());
        assert!(checker.store().alias_symbol_links(imported).is_none());
    }
}

#[test]
fn unproved_ambient_class_imports_keep_the_declaration_error() {
    for source in [
        concat!(
            "declare module 'entries' {\n",
            "  export class Entry {}\n",
            "  export { Entry as Forwarded };\n",
            "  import { Forwarded as Imported } from 'entries';\n",
            "  global { interface Derived extends Imported {} }\n",
            "}\n",
        ),
        concat!(
            "declare module 'other' { export class Other {} }\n",
            "declare module 'entries' {\n",
            "  export class Entry {}\n",
            "  import { Entry as Imported } from 'other';\n",
            "  global { interface Derived extends Imported {} }\n",
            "}\n",
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&parsed);
        let derived_node = declaration(&parsed, SyntaxKind::InterfaceDeclaration, "Derived");
        let derived = symbol(&checker, derived_node);
        let import_node = declaration(&parsed, SyntaxKind::ImportSpecifier, "Imported");
        let imported = symbol(&checker, import_node);
        let record = checker.store().symbol(imported).unwrap();
        assert_eq!(record.flags(), SymbolFlags::ALIAS);
        assert_eq!(record.declarations(), Some([import_node].as_slice()));
        let expected = DeclaredTypeError::Unavailable(
            DeclaredTypeUnavailable::DeclarationSymbolMismatch(derived_node),
        );
        assert_eq!(checker.get_declared_type_of_symbol(derived), Err(expected));
        let stable = counts(&checker);
        let diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            assert_eq!(checker.get_declared_type_of_symbol(derived), Err(expected));
            assert_eq!(counts(&checker), stable);
            assert_eq!(checker.diagnostics(), &diagnostics);
            assert!(checker.store().declared_type_links(derived).is_none());
            assert!(checker.store().alias_symbol_links(imported).is_none());
        }
    }
}
