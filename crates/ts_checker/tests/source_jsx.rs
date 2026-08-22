use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalTypeMapperStore, DeclaredTypeHost, IntrinsicBootstrapOptions, JsxFlags,
    SourceCheckError, SymbolNodeLinks, TypeData, TypeNodeLinks, UnsupportedSourceSyntax,
    ValueSymbolLinks, types::ObjectFlags,
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_jsx_source_file};

struct Fixture {
    parsed: ParseResult,
    file: FileId,
    bound: BoundFile,
    store: CanonicalTypeMapperStore,
}

impl Fixture {
    fn new(source: &str, file: FileId) -> Self {
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/view.tsx\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let bound = files.remove(&file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let namespace = bound
            .locals(bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"));
        if let Some(namespace) = namespace {
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            assert_eq!(
                store.insert_symbol(globals, EscapedName::source("JSX"), namespace),
                Some(None),
            );
        }
        Self {
            parsed,
            file,
            bound,
            store,
        }
    }

    fn expression(&self, name: &str) -> NodeRef {
        self.parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &self.parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(
                    self.parsed.arena.id(),
                    self.file,
                    variable.initializer?,
                ))
            })
            .unwrap_or_else(|| panic!("missing JSX initializer {name}"))
    }

    fn namespace_export(&self, name: &str) -> SemanticSymbolId {
        let namespace = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("JSX"))
            .unwrap();
        let exports = self.store.symbol(namespace).unwrap().exports().unwrap();
        self.store
            .symbol_table(exports)
            .unwrap()
            .get_source(name)
            .unwrap()
    }

    fn local(&self, name: &str) -> SemanticSymbolId {
        self.bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(name))
            .unwrap()
    }

    fn check(
        &mut self,
        node: NodeRef,
        options: CanonicalCheckerOptions,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<ts_checker::semantic::TypeId, SourceCheckError> {
        let host = DeclaredTypeHost::new([(&self.parsed.arena, &self.bound)]).unwrap();
        self.store
            .check_jsx_element(&host, node, options, diagnostics)
    }
}

const NAMESPACE: &str = concat!(
    "declare namespace JSX {\n",
    "  interface Element {}\n",
    "  interface IntrinsicElements {\n",
    "    div: { label: string; enabled?: boolean };\n",
    "    span: {};\n",
    "    'my-widget': { label: number };\n",
    "  }\n",
    "}\n",
);

#[test]
fn intrinsic_jsx_reuses_namespace_property_signature_and_attribute_links() {
    let source = format!("{NAMESPACE}const view = <div label=\"ok\" enabled />;\n");
    let mut fixture = Fixture::new(&source, FileId::new(3_700));
    let expression = fixture.expression("view");
    let element_symbol = fixture.namespace_export("Element");
    let intrinsic_symbol = fixture.namespace_export("IntrinsicElements");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    let element_type = fixture
        .check(
            expression,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

    assert!(diagnostics.is_empty());
    assert_eq!(
        fixture
            .store
            .declared_type_links(element_symbol)
            .and_then(|links| links.declared_type),
        Some(element_type),
    );
    let intrinsic_type = fixture
        .store
        .declared_type_links(intrinsic_symbol)
        .and_then(|links| links.declared_type)
        .unwrap();
    let TypeData::Interface(intrinsics) =
        fixture.store.type_payload(intrinsic_type).unwrap().data()
    else {
        panic!("JSX.IntrinsicElements must resolve to its declared interface")
    };
    let div = intrinsics
        .reference
        .object
        .structured
        .members
        .and_then(|members| fixture.store.symbol_table(members))
        .and_then(|members| members.get_source("div"))
        .unwrap();
    let props_type = fixture
        .store
        .value_symbol_links(div)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let links = fixture.store.jsx_element_links(expression).unwrap();
    assert_eq!(links.jsx_flags, JsxFlags::INTRINSIC_NAMED_ELEMENT);
    assert_eq!(links.resolved_jsx_element_attributes_type, Some(props_type));
    assert_eq!(
        links.jsx_namespace,
        Some(fixture.store.intrinsic_bootstrap().unwrap().unknown_symbol),
    );
    assert_eq!(
        fixture.store.symbol_node_links(expression),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(div),
        }),
    );
    assert_eq!(
        fixture.store.type_node_links(expression),
        Some(&TypeNodeLinks {
            resolved_type: Some(element_type),
            ..TypeNodeLinks::default()
        }),
    );
    let signature = fixture
        .store
        .signature_links(expression)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let signature_record = fixture.store.signature(signature).unwrap();
    assert_eq!(signature_record.min_argument_count(), 1);
    assert_eq!(signature_record.resolved_return_type(), Some(element_type));
    let [parameter] = signature_record.parameters() else {
        panic!("intrinsic JSX must synthesize its single props parameter")
    };
    assert_eq!(
        fixture
            .store
            .value_symbol_links(*parameter)
            .and_then(|links| links.resolved_type),
        Some(props_type),
    );

    let NodeData::JsxSelfClosingElement(element) =
        &fixture.parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("expected a self-closing JSX expression")
    };
    let attributes = NodeRef::new(expression.arena, expression.file, element.attributes);
    let attributes_type = fixture
        .store
        .type_node_links(attributes)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let attributes_record = fixture.store.type_payload(attributes_type).unwrap();
    assert!(attributes_record.object_flags().contains(
        ObjectFlags::ANONYMOUS
            | ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::FRESH_LITERAL
            | ObjectFlags::JSX_ATTRIBUTES
            | ObjectFlags::MEMBERS_RESOLVED,
    ));
    let TypeData::Object(attributes_object) = attributes_record.data() else {
        panic!("JSX attributes must use the existing anonymous object graph")
    };
    assert_eq!(
        attributes_object
            .structured
            .properties
            .as_ref()
            .map(Vec::len),
        Some(2),
    );

    let cold = (
        fixture.store.type_len(),
        fixture.store.symbol_len(),
        fixture.store.signature_len(),
        fixture.store.symbol_store().symbol_table_len(),
        diagnostics.as_slice().to_vec(),
    );
    assert_eq!(
        fixture
            .check(
                expression,
                CanonicalCheckerOptions::default(),
                &mut diagnostics
            )
            .unwrap(),
        element_type,
    );
    assert_eq!(
        (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            diagnostics.as_slice().to_vec(),
        ),
        cold,
    );
}

#[test]
fn missing_intrinsic_interface_emits_exact_ts7026_for_each_opening() {
    let mut fixture = Fixture::new(
        "const first = <div label=\"ok\" />;\nconst second = <my-widget />;\n",
        FileId::new(3_701),
    );
    let first = fixture.expression("first");
    let second = fixture.expression("second");
    let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
    let options = CanonicalCheckerOptions {
        no_implicit_any: true,
        ..CanonicalCheckerOptions::default()
    };
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    assert_eq!(
        fixture.check(first, options, &mut diagnostics).unwrap(),
        error_type
    );
    assert_eq!(
        fixture.check(second, options, &mut diagnostics).unwrap(),
        error_type
    );

    let entries = diagnostics.as_slice();
    assert_eq!(entries.len(), 2);
    for (entry, opening) in entries.iter().zip([first, second]) {
        assert_eq!(entry.node, Some(opening));
        assert_eq!(entry.diagnostic.code(), 7026);
        assert_eq!(
            entry.diagnostic.render().unwrap(),
            "JSX element implicitly has type 'any' because no interface 'JSX.IntrinsicElements' exists.",
        );
        assert_eq!(
            fixture.store.jsx_element_links(opening).unwrap().jsx_flags,
            JsxFlags::NONE,
        );
    }

    fixture.check(first, options, &mut diagnostics).unwrap();
    assert_eq!(diagnostics.len(), 2);
}

#[test]
fn upstream_multiline_jsx_attributes_keep_all_four_ts7026_ranges() {
    let source = concat!(
        "const a = <div className= \"foo\n\n bar\" />;\n\n",
        "const b = <div className=\t\"foo\n\n bar\" />;\n\n",
        "const c = <div className=\n\"foo\n\n bar\" />;\n\n",
        "const d = <div className=   \"foo\n\n bar\" />;\n",
    );
    let mut fixture = Fixture::new(source, FileId::new(3_709));
    let options = CanonicalCheckerOptions {
        no_implicit_any: true,
        ..CanonicalCheckerOptions::default()
    };
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let openings = ["a", "b", "c", "d"].map(|name| fixture.expression(name));

    for opening in openings {
        fixture.check(opening, options, &mut diagnostics).unwrap();
    }

    assert_eq!(diagnostics.len(), 4);
    for (diagnostic, opening) in diagnostics.as_slice().iter().zip(openings) {
        assert_eq!(diagnostic.diagnostic.code(), 7026);
        assert_eq!(diagnostic.node, Some(opening));
        let range = fixture.parsed.arena.get(opening.node).unwrap().range;
        let text = &source[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()];
        assert!(text.starts_with("<div className="));
        assert!(text.ends_with(" />"));
    }
}

#[test]
fn production_source_checker_matches_upstream_multiline_jsx_diagnostics() {
    let source = concat!(
        "const a = <div className= \"foo\n\n bar\" />;\n\n",
        "const b = <div className=\t\"foo\n\n bar\" />;\n\n",
        "const c = <div className=\n\"foo\n\n bar\" />;\n\n",
        "const d = <div className=   \"foo\n\n bar\" />;\n",
    );
    let parsed = parse_jsx_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3_710);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/multiline.tsx\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();

    context.check_source_file(file).unwrap();

    assert_eq!(context.diagnostics().len(), 4);
    for diagnostic in context.diagnostics().as_slice() {
        assert_eq!(diagnostic.diagnostic.code(), 7026);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "JSX element implicitly has type 'any' because no interface 'JSX.IntrinsicElements' exists.",
        );
    }
    let snapshot = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.diagnostics().as_slice().to_vec(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.diagnostics().as_slice().to_vec(),
        ),
        snapshot,
    );
}

#[test]
fn missing_intrinsic_property_emits_ts2339_on_the_full_opening() {
    let source = format!("{NAMESPACE}const view = <section />;\n");
    let mut fixture = Fixture::new(&source, FileId::new(3_702));
    let opening = fixture.expression("view");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    fixture
        .check(
            opening,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

    let [diagnostic] = diagnostics.as_slice() else {
        panic!("one missing intrinsic tag must produce exactly one diagnostic")
    };
    assert_eq!(diagnostic.node, Some(opening));
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Property 'section' does not exist on type 'JSX.IntrinsicElements'.",
    );
    assert_eq!(
        fixture
            .store
            .symbol_node_links(opening)
            .and_then(|links| links.resolved_symbol),
        Some(fixture.store.intrinsic_bootstrap().unwrap().unknown_symbol),
    );
}

#[test]
fn intrinsic_type_argument_diagnostics_skip_spaces_and_newlines() {
    let source = format!(
        "{NAMESPACE}const first = <span<   number> />;\nconst second = <span<\n    number> />;\n"
    );
    let mut fixture = Fixture::new(&source, FileId::new(3_703));
    let first = fixture.expression("first");
    let second = fixture.expression("second");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    fixture
        .check(first, CanonicalCheckerOptions::default(), &mut diagnostics)
        .unwrap();
    fixture
        .check(second, CanonicalCheckerOptions::default(), &mut diagnostics)
        .unwrap();

    let ranges = [first, second]
        .into_iter()
        .map(|node| {
            let range = fixture.parsed.arena.get(node.node).unwrap().range;
            let start = usize::try_from(range.start.get()).unwrap();
            let end = usize::try_from(range.end.get()).unwrap();
            let offset = source[start..end].find("number").unwrap();
            (start + offset, "number")
        })
        .collect::<Vec<_>>();
    assert_eq!(diagnostics.len(), 2);
    for (entry, (start, text)) in diagnostics.as_slice().iter().zip(ranges) {
        assert_eq!(entry.diagnostic.code(), 2558);
        assert_eq!(
            entry.diagnostic.render().unwrap(),
            "Expected 0 type arguments, but got 1.",
        );
        assert_eq!(
            entry.range_override.unwrap().range(),
            TextRange::new(
                TextPos::new(u32::try_from(start).unwrap()),
                TextPos::new(u32::try_from(start + text.len()).unwrap()),
            ),
        );
    }
}

#[test]
fn scalar_attribute_mismatch_keeps_exact_ts2322_arguments() {
    let source = format!("{NAMESPACE}const view = <div label={{1}} />;\n");
    let mut fixture = Fixture::new(&source, FileId::new(3_704));
    let opening = fixture.expression("view");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    fixture
        .check(
            opening,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

    let [diagnostic] = diagnostics.as_slice() else {
        panic!("the mismatched attribute must produce one TS2322 diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'.",
    );
    let anchor = diagnostic.node.unwrap();
    let NodeData::Identifier(name) = &fixture.parsed.arena.get(anchor.node).unwrap().data else {
        panic!("the attribute name must own its assignment diagnostic")
    };
    assert_eq!(name.text, "label");
}

#[test]
fn indexed_intrinsic_tags_create_one_pinned_index_symbol() {
    let source = concat!(
        "declare namespace JSX {\n",
        "  interface Element {}\n",
        "  interface IntrinsicElements { [tag: string]: { label: string }; }\n",
        "}\n",
        "const first = <custom-element label=\"one\" />;\n",
        "const second = <other-element label=\"two\" />;\n",
    );
    let mut fixture = Fixture::new(source, FileId::new(3_705));
    let first = fixture.expression("first");
    let second = fixture.expression("second");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    fixture
        .check(first, CanonicalCheckerOptions::default(), &mut diagnostics)
        .unwrap();
    let first_index = fixture
        .store
        .symbol_node_links(first)
        .and_then(|links| links.resolved_symbol)
        .unwrap();
    fixture
        .check(second, CanonicalCheckerOptions::default(), &mut diagnostics)
        .unwrap();

    assert!(diagnostics.is_empty());
    assert_eq!(
        fixture
            .store
            .symbol_node_links(second)
            .and_then(|links| links.resolved_symbol),
        Some(first_index),
    );
    for opening in [first, second] {
        assert_eq!(
            fixture.store.jsx_element_links(opening).unwrap().jsx_flags,
            JsxFlags::INTRINSIC_INDEXED_ELEMENT,
        );
    }
    assert!(
        fixture
            .store
            .symbol(first_index)
            .unwrap()
            .check_flags()
            .contains(ts_binder::CheckFlags::INDEX_SYMBOL)
    );
}

#[test]
fn fixed_function_components_reuse_their_declared_call_signature() {
    let source = concat!(
        "declare namespace JSX {\n",
        "  interface Element {}\n",
        "  interface IntrinsicElements {\n",
        "    div: {};\n",
        "    component: { (props: { label: string }): any };\n",
        "  }\n",
        "}\n",
        "declare const Box: any;\n",
        "const initialize = <div />;\n",
        "const view = <Box label=\"ready\" />;\n",
    );
    let mut fixture = Fixture::new(source, FileId::new(3_706));
    let initialize = fixture.expression("initialize");
    let opening = fixture.expression("view");
    let component_owner = fixture.local("Box");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    fixture
        .check(
            initialize,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

    let intrinsics = fixture.namespace_export("IntrinsicElements");
    let intrinsic_type = fixture
        .store
        .declared_type_links(intrinsics)
        .and_then(|links| links.declared_type)
        .unwrap();
    let TypeData::Interface(interface) = fixture.store.type_payload(intrinsic_type).unwrap().data()
    else {
        panic!("expected the resolved JSX.IntrinsicElements interface")
    };
    let component_member = interface
        .reference
        .object
        .structured
        .members
        .and_then(|members| fixture.store.symbol_table(members))
        .and_then(|members| members.get_source("component"))
        .unwrap();
    let component_type = fixture
        .store
        .value_symbol_links(component_member)
        .and_then(|links| links.resolved_type)
        .unwrap();
    assert!(fixture.store.set_value_symbol_links(
        component_owner,
        ValueSymbolLinks {
            resolved_type: Some(component_type),
            ..ValueSymbolLinks::default()
        },
    ));
    let TypeData::Object(component) = fixture.store.type_payload(component_type).unwrap().data()
    else {
        panic!("the test component must be a source-declared call-signature object")
    };
    let [signature] = component.structured.signatures.as_deref().unwrap() else {
        panic!("the test component must have exactly one call signature")
    };
    let signature = *signature;
    let before_signatures = fixture.store.signature_len();

    fixture
        .check(
            opening,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

    assert!(diagnostics.is_empty());
    assert_eq!(fixture.store.signature_len(), before_signatures);
    assert_eq!(
        fixture
            .store
            .signature_links(opening)
            .and_then(|links| links.resolved_signature.signature()),
        Some(signature),
    );
    let NodeData::JsxSelfClosingElement(element) =
        &fixture.parsed.arena.get(opening.node).unwrap().data
    else {
        panic!("expected a self-closing JSX component")
    };
    let name = NodeRef::new(opening.arena, opening.file, element.tag_name);
    assert_eq!(
        fixture.store.symbol_node_links(name),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(component_owner),
        }),
    );
    assert_eq!(
        fixture.store.type_node_links(name),
        Some(&TypeNodeLinks {
            resolved_type: Some(component_type),
            ..TypeNodeLinks::default()
        }),
    );
}

#[test]
fn nested_elements_and_fragments_keep_closing_tag_identity() {
    let source = format!(
        "{NAMESPACE}const view = <div label=\"ok\">text<span />{{1}}</div>;\nconst fragment = <><span /></>;\n"
    );
    let mut fixture = Fixture::new(&source, FileId::new(3_707));
    let view = fixture.expression("view");
    let fragment = fixture.expression("fragment");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    fixture
        .check(view, CanonicalCheckerOptions::default(), &mut diagnostics)
        .unwrap();
    fixture
        .check(
            fragment,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap();

    assert!(diagnostics.is_empty());
    let NodeData::JsxElement(element) = &fixture.parsed.arena.get(view.node).unwrap().data else {
        panic!("expected an opening/closing JSX element")
    };
    let opening = NodeRef::new(view.arena, view.file, element.opening_element);
    let closing = NodeRef::new(view.arena, view.file, element.closing_element);
    assert_eq!(
        fixture.store.symbol_node_links(opening),
        fixture.store.symbol_node_links(closing),
    );
    assert_eq!(
        fixture.store.jsx_element_links(closing).unwrap().jsx_flags,
        JsxFlags::INTRINSIC_NAMED_ELEMENT,
    );
    let nested_count = fixture
        .parsed
        .arena
        .iter()
        .filter(|(_, node)| node.kind == SyntaxKind::JsxSelfClosingElement)
        .count();
    assert_eq!(nested_count, 2);
    for (node, record) in fixture.parsed.arena.iter() {
        if record.kind == SyntaxKind::JsxSelfClosingElement {
            let node = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
            assert!(fixture.store.type_node_links(node).is_some());
        }
    }
}

#[test]
fn spread_attributes_fail_before_jsx_semantic_publication() {
    let source =
        format!("{NAMESPACE}declare const props: any;\nconst view = <div {{...props}} />;\n");
    let mut fixture = Fixture::new(&source, FileId::new(3_708));
    let opening = fixture.expression("view");
    let counts = (
        fixture.store.type_len(),
        fixture.store.symbol_len(),
        fixture.store.signature_len(),
    );
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    let error = fixture
        .check(
            opening,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap_err();

    assert!(matches!(
        error,
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
            kind: SyntaxKind::JsxSpreadAttribute,
            ..
        })
    ));
    assert_eq!(
        (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.signature_len(),
        ),
        counts,
    );
    assert!(fixture.store.jsx_element_links(opening).is_none());
    assert!(diagnostics.is_empty());
}
