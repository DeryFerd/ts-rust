use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    jsdoc::{
        JsDocCommentError, JsDocIntrinsicType, JsDocTagKind, JsDocType, JsDocTypeResolutionError,
        leading_jsdoc_comment, parse_jsdoc_comment_at, plan_javascript_source_jsdoc,
        resolve_intrinsic_jsdoc_type,
    },
};
use ts_core::{TextPos, TextRange};
use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

fn comment_range(source: &str) -> TextRange {
    let start = source.find("/**").unwrap();
    let end = source[start..].find("*/").unwrap() + start + 2;
    TextRange::new(
        TextPos::new(u32::try_from(start).unwrap()),
        TextPos::new(u32::try_from(end).unwrap()),
    )
}

fn context(parsed: &ParseResult, options: CanonicalCheckerOptions) -> CanonicalCheckerContext<'_> {
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/input.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
}

#[test]
fn leading_jsdoc_type_preserves_intrinsic_identity_and_source_ranges() {
    let source = "/** @type {Number} */\nconst value = 1;";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file")
    };
    let statement = NodeRef::new(parsed.arena.id(), FileId::new(0), file.statements.nodes[0]);
    let comment = leading_jsdoc_comment(&parsed.arena, statement)
        .unwrap()
        .unwrap();
    assert!(comment.diagnostics().is_empty());
    assert_eq!(comment.range(), comment_range(source));
    let tag = comment.type_tag().unwrap();
    assert_eq!(tag.kind(), JsDocTagKind::Type);
    let annotation = tag.type_expression().unwrap();
    assert_eq!(annotation.text(), "Number");
    assert_eq!(
        annotation.type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::Number)
    );
    let start = source.find("Number").unwrap();
    assert_eq!(annotation.range().start.get() as usize, start);
    assert_eq!(
        annotation.range().end.get() as usize,
        start + "Number".len()
    );

    let context = context(&parsed, CanonicalCheckerOptions::default());
    assert_eq!(
        resolve_intrinsic_jsdoc_type(
            context.store(),
            CanonicalCheckerOptions::default(),
            annotation,
        )
        .unwrap(),
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
}

#[test]
fn parameter_aliases_optional_names_and_returns_match_go_jsdoc_tags() {
    let source = concat!(
        "/**\n",
        " * @arg {String} [name = 'guest']\n",
        " * @argument {number=} count\n",
        " * @param active {Boolean}\n",
        " * @returns {Void}\n",
        " */",
    );
    let comment = parse_jsdoc_comment_at(source, comment_range(source)).unwrap();
    assert!(
        comment.diagnostics().is_empty(),
        "{:?}",
        comment.diagnostics()
    );
    assert_eq!(comment.tags().len(), 4);

    let name = comment.parameter_tag("name").unwrap();
    assert!(name.is_optional());
    assert!(!name.is_name_first());
    assert_eq!(
        name.type_expression().unwrap().type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::String)
    );

    let count = comment.parameter_tag("count").unwrap();
    assert!(count.is_optional());
    assert_eq!(
        count.type_expression().unwrap().type_(),
        &JsDocType::Optional(Box::new(JsDocType::Intrinsic(JsDocIntrinsicType::Number)))
    );

    let active = comment.parameter_tag("active").unwrap();
    assert!(!active.is_optional());
    assert!(active.is_name_first());
    assert_eq!(
        active.type_expression().unwrap().type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::Boolean)
    );

    assert_eq!(
        comment
            .return_tag()
            .unwrap()
            .type_expression()
            .unwrap()
            .type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::Void)
    );
}

#[test]
fn invalid_jsdoc_import_type_reports_the_exact_upstream_ts1110_range() {
    let source = "/** @type {@import(\"a\").Type} */\nlet x;";
    let comment = parse_jsdoc_comment_at(source, comment_range(source)).unwrap();
    assert_eq!(comment.tags().len(), 1);
    assert!(comment.type_tag().unwrap().type_expression().is_none());
    assert_eq!(comment.diagnostics().len(), 1);
    let diagnostic = &comment.diagnostics()[0];
    assert_eq!(diagnostic.code, Some(1110));
    assert_eq!(diagnostic.message, "Type expected.");
    let start = source.find("@import").unwrap();
    assert_eq!(diagnostic.range.start.get() as usize, start);
    assert_eq!(diagnostic.range.end.get() as usize, start + 1);
}

#[test]
fn strict_nullable_intrinsics_fail_without_union_allocation() {
    let source = "/** @type {?string} */";
    let comment = parse_jsdoc_comment_at(source, comment_range(source)).unwrap();
    let annotation = comment.type_tag().unwrap().type_expression().unwrap();
    let options = CanonicalCheckerOptions {
        intrinsic: IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        },
        ..CanonicalCheckerOptions::default()
    };
    let parsed = parse_source_file("const marker = 1;");
    let context = context(&parsed, options);
    assert_eq!(
        resolve_intrinsic_jsdoc_type(context.store(), options, annotation),
        Err(JsDocTypeResolutionError::UnsupportedType {
            kind: SyntaxKind::JsDocNullableType,
            range: annotation.range(),
        })
    );
}

#[test]
fn variadic_jsdoc_types_do_not_change_parameter_optionality() {
    let source = "/** @param {...number} values */";
    let comment = parse_jsdoc_comment_at(source, comment_range(source)).unwrap();
    assert!(
        comment.diagnostics().is_empty(),
        "{:?}",
        comment.diagnostics()
    );
    let parameter = comment.parameter_tag("values").unwrap();
    assert!(!parameter.is_optional());
    assert_eq!(
        parameter.type_expression().unwrap().type_(),
        &JsDocType::Variadic(Box::new(JsDocType::Intrinsic(JsDocIntrinsicType::Number)))
    );
}

#[test]
fn unsupported_type_names_do_not_silently_become_any() {
    let source = "/** @type {Missing} */";
    let comment = parse_jsdoc_comment_at(source, comment_range(source)).unwrap();
    let annotation = comment.type_tag().unwrap().type_expression().unwrap();
    let parsed = parse_source_file("const marker = 1;");
    let context = context(&parsed, CanonicalCheckerOptions::default());
    assert_eq!(
        resolve_intrinsic_jsdoc_type(
            context.store(),
            CanonicalCheckerOptions::default(),
            annotation,
        ),
        Err(JsDocTypeResolutionError::UnresolvedTypeReference {
            name: "Missing".to_owned(),
            range: annotation.range(),
        })
    );
}

#[test]
fn foreign_source_nodes_are_rejected_before_reading_comments() {
    let source = parse_source_file("/** @type {number} */ const value = 1;");
    let foreign = parse_source_file("const other = 1;");
    let foreign_node = NodeRef::new(foreign.arena.id(), FileId::new(0), foreign.source_file);
    assert_eq!(
        leading_jsdoc_comment(&source.arena, foreign_node),
        Err(JsDocCommentError::InvalidSourceNode(foreign_node))
    );
}

#[test]
fn javascript_source_plan_retains_adjacent_typedefs_and_function_annotations() {
    let source = concat!(
        "/** @typedef {number} NS.Count */\n",
        "/** @type {NS.Count} */\n",
        "const value = 1;\n",
        "/**\n",
        " * @param {Number} [count=1]\n",
        " * @returns {string}\n",
        " */\n",
        "function format(count) { return 'ok'; }",
    );
    let parsed = parse_javascript_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(30);
    let source_node = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
    let plan = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
    assert!(plan.diagnostics().is_empty(), "{:?}", plan.diagnostics());
    assert_eq!(plan.declarations().len(), 2);

    let variable = &plan.declarations()[0];
    assert_eq!(
        variable.type_().unwrap().type_(),
        &JsDocType::Named("NS.Count".to_owned())
    );
    assert_eq!(variable.typedefs().len(), 1);
    assert_eq!(variable.typedefs()[0].name(), "NS.Count");
    assert_eq!(
        variable.typedefs()[0].type_().unwrap().type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::Number)
    );

    let function = &plan.declarations()[1];
    let parameter = function.parameter("count").unwrap();
    assert!(parameter.is_optional());
    assert_eq!(
        parameter.type_().unwrap().type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::Number)
    );
    assert_eq!(
        function.return_type().unwrap().type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::String)
    );
}

#[test]
fn source_wide_invalid_jsdoc_types_use_canonical_root_anchored_diagnostics() {
    let source = "/** @type {@import(\"a\").Type} */\nlet x;";
    let parsed = parse_javascript_source_file(source);
    let source_node = NodeRef::new(parsed.arena.id(), FileId::new(31), parsed.source_file);
    let plan = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
    let [diagnostic] = plan.diagnostics() else {
        panic!("expected exactly one canonical JSDoc diagnostic")
    };
    assert_eq!(diagnostic.node, Some(source_node));
    assert_eq!(diagnostic.diagnostic.code(), 1110);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), "Type expected.");
    let range = diagnostic.range_override.unwrap().range();
    let start = source.find("@import").unwrap();
    assert_eq!(range.start.get() as usize, start);
    assert_eq!(range.end.get() as usize, start + 1);
}

#[test]
fn unmatched_jsdoc_parameters_use_the_exact_name_and_ts8024_message() {
    let source = concat!(
        "/** @param {number} missing */\n",
        "function first(value) {}\n",
        "/** @param missing {number} */\n",
        "function second(value) {}",
    );
    let parsed = parse_javascript_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let source_node = NodeRef::new(parsed.arena.id(), FileId::new(32), parsed.source_file);
    let plan = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
    let [diagnostic] = plan.diagnostics() else {
        panic!("only the type-first unmatched parameter should report TS8024")
    };
    assert_eq!(diagnostic.diagnostic.code(), 8024);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "JSDoc '@param' tag has name 'missing', but there is no parameter with that name.",
    );
    let start = source.find("missing").unwrap();
    let range = diagnostic.range_override.unwrap().range();
    assert_eq!(range.start.get() as usize, start);
    assert_eq!(range.end.get() as usize, start + "missing".len());
}

#[test]
fn jsdoc_class_heritage_mismatch_matches_pinned_ts8023_range_and_arguments() {
    let source = concat!(
        "/**\n",
        " * @extends {React.Component}\n",
        " */\n",
        "class C extends React.PureComponent {}\n",
        "/**\n",
        " * @extends {React.Component}\n",
        " */\n",
        "class D extends React.Component {}",
    );
    let parsed = parse_javascript_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let source_node = NodeRef::new(parsed.arena.id(), FileId::new(33), parsed.source_file);
    let plan = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
    assert_eq!(plan.declarations().len(), 2);
    let [diagnostic] = plan.diagnostics() else {
        panic!(
            "only the mismatched class should report TS8023: {:?}; declarations: {:?}",
            plan.diagnostics(),
            plan.declarations()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 8023);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "JSDoc '@extends Component' does not match the 'extends PureComponent' clause.",
    );
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["extends", "Component", "PureComponent"]
    );
    let start = source.find("React.Component").unwrap() + "React.".len();
    let range = diagnostic.range_override.unwrap().range();
    assert_eq!(range.start.get() as usize, start);
    assert_eq!(range.end.get() as usize, start + "Component".len());
}

#[test]
fn javascript_binder_and_owned_jsdoc_plan_share_canonical_declaration_identity() {
    let source = "/** @type {number} */ const value = 1;";
    let parsed = parse_javascript_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(34);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/input.js\""),
                CanonicalSourceLanguage::JavaScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_javascript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let source_node = context.source_file(file).unwrap().node_ref();
    let plan = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
    let [declaration] = plan.declarations() else {
        panic!("expected one JavaScript variable annotation")
    };
    let bound = context.file(file).unwrap().1;
    assert!(bound.symbol(declaration.node()).is_some());
    assert_eq!(
        declaration.type_().unwrap().type_(),
        &JsDocType::Intrinsic(JsDocIntrinsicType::Number)
    );
}
