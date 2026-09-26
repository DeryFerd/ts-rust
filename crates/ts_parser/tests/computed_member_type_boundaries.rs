use ts_ast::{NodeData, NodeId, PropertyDeclarationData, SyntaxKind};
use ts_core::{Diagnostic, DiagnosticCategory, TextPos, TextRange};
use ts_parser::{ParseResult, parse_source_file};

#[test]
fn computed_interface_properties_start_after_line_breaks_and_comments() {
    for separator in ["\n", "\r\n", " // next member\n", " /* line\n break */ "] {
        let source = format!(
            "interface CssClassName {{\n  [SELECTOR]: string{separator}  [CLASS_NAME]: string{separator}  [SELECTORS]: CssClassName[]{separator}  [EXTERNAL_CLASS_NAMES]: string[]\n}}\n"
        );
        let parsed = parse_source_file(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        assert_eq!(statements(&parsed).len(), 1);
        let (owner, members) = first_interface(&parsed);
        assert_eq!(members.len(), 4);

        for (member, (name, annotation, kind)) in members.iter().copied().zip([
            ("SELECTOR", "string", SyntaxKind::StringKeyword),
            ("CLASS_NAME", "string", SyntaxKind::StringKeyword),
            ("SELECTORS", "CssClassName[]", SyntaxKind::ArrayType),
            ("EXTERNAL_CLASS_NAMES", "string[]", SyntaxKind::ArrayType),
        ]) {
            let member_text = format!("[{name}]: {annotation}");
            let type_node = property_type(
                &parsed,
                &source,
                owner,
                member,
                &member_text,
                kind,
                annotation,
            );
            let property = property(&parsed, member);
            assert!(property.postfix_token.is_none());
            assert!(property.modifiers.is_none());
            assert_computed_name(&parsed, &source, member, property.name, name);
            if let NodeData::ArrayTypeNode(array) = &parsed.arena.get(type_node).unwrap().data {
                let (element, element_kind) = if name == "SELECTORS" {
                    ("CssClassName", SyntaxKind::TypeReference)
                } else {
                    ("string", SyntaxKind::StringKeyword)
                };
                assert_child(
                    &parsed,
                    &source,
                    type_node,
                    array.element_type,
                    element_kind,
                    element,
                );
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn computed_type_literal_property_keeps_its_union_and_nested_arrays() {
    let annotation = concat!(
        "| [number, any[][], LocalJSXContexts, [Context, Function, NodeObject]]\n",
        "    | [number, any[][]]",
    );
    let member_text = format!("[DOM_STASH]:\n    {annotation}");
    let source = format!(
        "type NodeObject = {{\n  o?: NodeObject // original node\n  {member_text}\n}} & JSXNode\n"
    );
    let parsed = parse_source_file(&source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(statements(&parsed).len(), 1);
    let alias_node = statements(&parsed)[0];
    let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(alias_node).unwrap().data else {
        panic!("expected NodeObject alias");
    };
    let intersection_node = alias.type_;
    let NodeData::IntersectionTypeNode(intersection) =
        &parsed.arena.get(intersection_node).unwrap().data
    else {
        panic!("expected the written JSXNode intersection");
    };
    assert_eq!(
        parsed.arena.get(intersection_node).unwrap().parent,
        Some(alias_node)
    );
    assert_eq!(intersection.types.nodes.len(), 2);
    let owner = intersection.types.nodes[0];
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(owner).unwrap().data else {
        panic!("expected the complete NodeObject type literal");
    };
    assert_eq!(
        parsed.arena.get(owner).unwrap().parent,
        Some(intersection_node)
    );
    assert_eq!(literal.members.nodes.len(), 2);
    assert_child(
        &parsed,
        &source,
        intersection_node,
        intersection.types.nodes[1],
        SyntaxKind::TypeReference,
        "JSXNode",
    );

    let original = literal.members.nodes[0];
    property_type(
        &parsed,
        &source,
        owner,
        original,
        "o?: NodeObject",
        SyntaxKind::TypeReference,
        "NodeObject",
    );
    let original = property(&parsed, original);
    assert_child(
        &parsed,
        &source,
        literal.members.nodes[0],
        original.name,
        SyntaxKind::Identifier,
        "o",
    );
    assert_child(
        &parsed,
        &source,
        literal.members.nodes[0],
        original.postfix_token.expect("written optional marker"),
        SyntaxKind::QuestionToken,
        "?",
    );

    let member = literal.members.nodes[1];
    let union_node = property_type(
        &parsed,
        &source,
        owner,
        member,
        &member_text,
        SyntaxKind::UnionType,
        annotation,
    );
    assert_computed_name(
        &parsed,
        &source,
        member,
        property(&parsed, member).name,
        "DOM_STASH",
    );
    let NodeData::UnionTypeNode(union) = &parsed.arena.get(union_node).unwrap().data else {
        panic!("expected the two stash tuple alternatives");
    };
    assert_eq!(union.types.nodes.len(), 2);
    for (tuple_node, length) in union.types.nodes.iter().copied().zip([4, 2]) {
        let NodeData::TupleTypeNode(tuple) = &parsed.arena.get(tuple_node).unwrap().data else {
            panic!("expected stash tuple");
        };
        assert_eq!(
            parsed.arena.get(tuple_node).unwrap().parent,
            Some(union_node)
        );
        assert_eq!(tuple.elements.nodes.len(), length);
        assert_child(
            &parsed,
            &source,
            tuple_node,
            tuple.elements.nodes[0],
            SyntaxKind::NumberKeyword,
            "number",
        );
        let outer = tuple.elements.nodes[1];
        assert_child(
            &parsed,
            &source,
            tuple_node,
            outer,
            SyntaxKind::ArrayType,
            "any[][]",
        );
        let NodeData::ArrayTypeNode(outer_data) = &parsed.arena.get(outer).unwrap().data else {
            panic!("expected outer stash array");
        };
        let inner = outer_data.element_type;
        assert_child(
            &parsed,
            &source,
            outer,
            inner,
            SyntaxKind::ArrayType,
            "any[]",
        );
        let NodeData::ArrayTypeNode(inner_data) = &parsed.arena.get(inner).unwrap().data else {
            panic!("expected inner stash array");
        };
        assert_child(
            &parsed,
            &source,
            inner,
            inner_data.element_type,
            SyntaxKind::AnyKeyword,
            "any",
        );
        if length == 4 {
            assert_child(
                &parsed,
                &source,
                tuple_node,
                tuple.elements.nodes[2],
                SyntaxKind::TypeReference,
                "LocalJSXContexts",
            );
            let boundary = tuple.elements.nodes[3];
            assert_child(
                &parsed,
                &source,
                tuple_node,
                boundary,
                SyntaxKind::TupleType,
                "[Context, Function, NodeObject]",
            );
            let NodeData::TupleTypeNode(boundary_data) = &parsed.arena.get(boundary).unwrap().data
            else {
                panic!("expected error-boundary tuple");
            };
            assert_eq!(boundary_data.elements.nodes.len(), 3);
            for (element, name) in boundary_data.elements.nodes.iter().copied().zip([
                "Context",
                "Function",
                "NodeObject",
            ]) {
                assert_child(
                    &parsed,
                    &source,
                    boundary,
                    element,
                    SyntaxKind::TypeReference,
                    name,
                );
            }
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn ambient_method_return_stops_before_an_iterator_property() {
    let source = concat!(
        "declare class MockCallHistory {\n",
        "  clear (): void\n",
        "  /** use it with for..of loop or spread operator */\n",
        "  [Symbol.iterator]: () => Generator<MockCallHistoryLog>\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(statements(&parsed).len(), 1);
    let owner = statements(&parsed)[0];
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(owner).unwrap().data else {
        panic!("expected ambient class");
    };
    assert_eq!(class.members.nodes.len(), 2);
    let method_node = class.members.nodes[0];
    let method = parsed.arena.get(method_node).unwrap();
    assert_eq!(method.kind, SyntaxKind::MethodDeclaration);
    assert_eq!(method.parent, Some(owner));
    assert_written_span(&parsed, source, method_node, "clear (): void");
    let NodeData::MethodDeclaration(method) = &method.data else {
        panic!("expected clear method");
    };
    assert!(method.body.is_none());
    assert!(method.parameters.nodes.is_empty());
    assert!(method.type_parameters.is_none());
    assert_child(
        &parsed,
        source,
        method_node,
        method.name,
        SyntaxKind::Identifier,
        "clear",
    );
    assert_child(
        &parsed,
        source,
        method_node,
        method.type_.expect("written return"),
        SyntaxKind::VoidKeyword,
        "void",
    );

    let member = class.members.nodes[1];
    let function_node = property_type(
        &parsed,
        source,
        owner,
        member,
        "[Symbol.iterator]: () => Generator<MockCallHistoryLog>",
        SyntaxKind::FunctionType,
        "() => Generator<MockCallHistoryLog>",
    );
    assert_computed_name(
        &parsed,
        source,
        member,
        property(&parsed, member).name,
        "Symbol.iterator",
    );
    let NodeData::FunctionTypeNode(function) = &parsed.arena.get(function_node).unwrap().data
    else {
        panic!("expected the iterator property's function type");
    };
    assert!(function.parameters.nodes.is_empty());
    assert!(function.type_parameters.is_none());
    let return_type = function.type_.expect("written generator return");
    assert_child(
        &parsed,
        source,
        function_node,
        return_type,
        SyntaxKind::TypeReference,
        "Generator<MockCallHistoryLog>",
    );
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(return_type).unwrap().data
    else {
        panic!("expected Generator reference");
    };
    assert_child(
        &parsed,
        source,
        return_type,
        reference.type_name,
        SyntaxKind::Identifier,
        "Generator",
    );
    let arguments = reference
        .type_arguments
        .as_ref()
        .expect("written type argument");
    assert_eq!(arguments.nodes.len(), 1);
    assert_child(
        &parsed,
        source,
        return_type,
        arguments.nodes[0],
        SyntaxKind::TypeReference,
        "MockCallHistoryLog",
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn function_property_return_stops_before_dotted_computed_members() {
    let source = concat!(
        "interface FormData {\n",
        "  entries: () => SpecIterableIterator<[string, FormDataEntryValue]>\n",
        "\n",
        "  /**\n   * An alias for FormData#entries()\n   */\n",
        "  [Symbol.iterator]: () => SpecIterableIterator<[string, FormDataEntryValue]>\n",
        "  readonly [Symbol.toStringTag]: string\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(statements(&parsed).len(), 1);
    let (owner, members) = first_interface(&parsed);
    assert_eq!(members.len(), 3);
    for (member, name) in members[..2]
        .iter()
        .copied()
        .zip(["entries", "[Symbol.iterator]"])
    {
        let annotation = "() => SpecIterableIterator<[string, FormDataEntryValue]>";
        let function_node = property_type(
            &parsed,
            source,
            owner,
            member,
            &format!("{name}: {annotation}"),
            SyntaxKind::FunctionType,
            annotation,
        );
        let property = property(&parsed, member);
        if name == "entries" {
            assert_child(
                &parsed,
                source,
                member,
                property.name,
                SyntaxKind::Identifier,
                "entries",
            );
        } else {
            assert_computed_name(&parsed, source, member, property.name, "Symbol.iterator");
        }
        let NodeData::FunctionTypeNode(function) = &parsed.arena.get(function_node).unwrap().data
        else {
            panic!("expected iterator function type");
        };
        assert!(function.parameters.nodes.is_empty());
        let return_type = function.type_.expect("written iterator return");
        assert_child(
            &parsed,
            source,
            function_node,
            return_type,
            SyntaxKind::TypeReference,
            "SpecIterableIterator<[string, FormDataEntryValue]>",
        );
        let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(return_type).unwrap().data
        else {
            panic!("expected iterator reference");
        };
        assert_child(
            &parsed,
            source,
            return_type,
            reference.type_name,
            SyntaxKind::Identifier,
            "SpecIterableIterator",
        );
        let arguments = reference
            .type_arguments
            .as_ref()
            .expect("written tuple argument");
        assert_eq!(arguments.nodes.len(), 1);
        let tuple_node = arguments.nodes[0];
        assert_child(
            &parsed,
            source,
            return_type,
            tuple_node,
            SyntaxKind::TupleType,
            "[string, FormDataEntryValue]",
        );
        let NodeData::TupleTypeNode(tuple) = &parsed.arena.get(tuple_node).unwrap().data else {
            panic!("expected entry tuple");
        };
        assert_eq!(tuple.elements.nodes.len(), 2);
        assert_child(
            &parsed,
            source,
            tuple_node,
            tuple.elements.nodes[0],
            SyntaxKind::StringKeyword,
            "string",
        );
        assert_child(
            &parsed,
            source,
            tuple_node,
            tuple.elements.nodes[1],
            SyntaxKind::TypeReference,
            "FormDataEntryValue",
        );
    }
    let member = members[2];
    property_type(
        &parsed,
        source,
        owner,
        member,
        "readonly [Symbol.toStringTag]: string",
        SyntaxKind::StringKeyword,
        "string",
    );
    let property = property(&parsed, member);
    assert_computed_name(&parsed, source, member, property.name, "Symbol.toStringTag");
    let modifiers = property
        .modifiers
        .as_ref()
        .expect("written readonly modifier");
    assert_eq!(modifiers.list.nodes.len(), 1);
    assert_child(
        &parsed,
        source,
        member,
        modifiers.list.nodes[0],
        SyntaxKind::ReadonlyKeyword,
        "readonly",
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn same_line_postfix_types_and_bracket_members_keep_their_roles() {
    let source = concat!(
        "interface Members {\n",
        "  indexed: Value[Key];\n",
        "  array: Value[];\n",
        "  grouped: (Value | Other)[];\n",
        "  nonnull: Value!;\n",
        "  nullable: Value?;\n",
        "  [key: string]: Value;\n",
        "  [method]?(): Value;\n",
        "  [Symbol.iterator](): Value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (owner, members) = first_interface(&parsed);
    assert_eq!(statements(&parsed).len(), 1);
    assert_eq!(members.len(), 8);
    let mut types = Vec::new();
    for (member, (name, annotation, kind)) in members[..5].iter().copied().zip([
        ("indexed", "Value[Key]", SyntaxKind::IndexedAccessType),
        ("array", "Value[]", SyntaxKind::ArrayType),
        ("grouped", "(Value | Other)[]", SyntaxKind::ArrayType),
        ("nonnull", "Value!", SyntaxKind::JsDocNonNullableType),
        ("nullable", "Value?", SyntaxKind::JsDocNullableType),
    ]) {
        types.push(property_type(
            &parsed,
            source,
            owner,
            member,
            &format!("{name}: {annotation};"),
            kind,
            annotation,
        ));
    }
    let NodeData::IndexedAccessTypeNode(indexed) = &parsed.arena.get(types[0]).unwrap().data else {
        panic!("expected same-line indexed access");
    };
    assert_child(
        &parsed,
        source,
        types[0],
        indexed.object_type,
        SyntaxKind::TypeReference,
        "Value",
    );
    assert_child(
        &parsed,
        source,
        types[0],
        indexed.index_type,
        SyntaxKind::TypeReference,
        "Key",
    );
    for (array_node, element_kind, element_text) in [
        (types[1], SyntaxKind::TypeReference, "Value"),
        (types[2], SyntaxKind::ParenthesizedType, "(Value | Other)"),
    ] {
        let NodeData::ArrayTypeNode(array) = &parsed.arena.get(array_node).unwrap().data else {
            panic!("expected same-line array");
        };
        assert_child(
            &parsed,
            source,
            array_node,
            array.element_type,
            element_kind,
            element_text,
        );
    }
    let NodeData::JsDocNonNullableType(nonnull) = &parsed.arena.get(types[3]).unwrap().data else {
        panic!("expected retained non-nullable postfix");
    };
    assert_child(
        &parsed,
        source,
        types[3],
        nonnull.type_,
        SyntaxKind::TypeReference,
        "Value",
    );
    let NodeData::JsDocNullableType(nullable) = &parsed.arena.get(types[4]).unwrap().data else {
        panic!("expected retained nullable postfix");
    };
    assert_child(
        &parsed,
        source,
        types[4],
        nullable.type_,
        SyntaxKind::TypeReference,
        "Value",
    );

    let index_node = members[5];
    assert_child(
        &parsed,
        source,
        owner,
        index_node,
        SyntaxKind::IndexSignature,
        "[key: string]: Value;",
    );
    let NodeData::IndexSignatureDeclaration(index) = &parsed.arena.get(index_node).unwrap().data
    else {
        panic!("expected an index signature, not a computed property");
    };
    assert_eq!(index.parameters.nodes.len(), 1);
    let parameter_node = index.parameters.nodes[0];
    assert_child(
        &parsed,
        source,
        index_node,
        parameter_node,
        SyntaxKind::Parameter,
        "key: string",
    );
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter_node).unwrap().data
    else {
        panic!("expected index parameter");
    };
    assert_child(
        &parsed,
        source,
        parameter_node,
        parameter.name,
        SyntaxKind::Identifier,
        "key",
    );
    assert_child(
        &parsed,
        source,
        parameter_node,
        parameter.type_.expect("written parameter type"),
        SyntaxKind::StringKeyword,
        "string",
    );
    assert_child(
        &parsed,
        source,
        index_node,
        index.type_,
        SyntaxKind::TypeReference,
        "Value",
    );
    for (member, name, optional) in [
        (members[6], "method", true),
        (members[7], "Symbol.iterator", false),
    ] {
        let method_node = parsed.arena.get(member).unwrap();
        assert_eq!(method_node.kind, SyntaxKind::MethodSignature);
        assert_eq!(method_node.parent, Some(owner));
        let NodeData::MethodSignatureDeclaration(method) = &method_node.data else {
            panic!("expected computed method signature");
        };
        assert_computed_name(&parsed, source, member, method.name, name);
        assert!(method.parameters.nodes.is_empty());
        assert_eq!(method.postfix_token.is_some(), optional);
        if let Some(question) = method.postfix_token {
            assert_child(
                &parsed,
                source,
                member,
                question,
                SyntaxKind::QuestionToken,
                "?",
            );
        }
        assert_child(
            &parsed,
            source,
            member,
            method.type_.expect("written method return"),
            SyntaxKind::TypeReference,
            "Value",
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn conditional_property_ends_before_the_next_computed_member() {
    let source = concat!(
        "interface Combined<T> {\n",
        "  value: T extends string ? | number | boolean : object\n",
        "  [NEXT]: T[]\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (owner, members) = first_interface(&parsed);
    assert_eq!(statements(&parsed).len(), 1);
    assert_eq!(members.len(), 2);
    let conditional_node = property_type(
        &parsed,
        source,
        owner,
        members[0],
        "value: T extends string ? | number | boolean : object",
        SyntaxKind::ConditionalType,
        "T extends string ? | number | boolean : object",
    );
    let NodeData::ConditionalTypeNode(conditional) =
        &parsed.arena.get(conditional_node).unwrap().data
    else {
        panic!("expected conditional annotation");
    };
    assert_child(
        &parsed,
        source,
        conditional_node,
        conditional.check_type,
        SyntaxKind::TypeReference,
        "T",
    );
    assert_child(
        &parsed,
        source,
        conditional_node,
        conditional.extends_type,
        SyntaxKind::StringKeyword,
        "string",
    );
    assert_child(
        &parsed,
        source,
        conditional_node,
        conditional.true_type,
        SyntaxKind::UnionType,
        "| number | boolean",
    );
    assert_child(
        &parsed,
        source,
        conditional_node,
        conditional.false_type,
        SyntaxKind::ObjectKeyword,
        "object",
    );
    let NodeData::UnionTypeNode(union) = &parsed.arena.get(conditional.true_type).unwrap().data
    else {
        panic!("expected leading-bar true branch");
    };
    assert_eq!(union.types.nodes.len(), 2);
    assert_child(
        &parsed,
        source,
        conditional.true_type,
        union.types.nodes[0],
        SyntaxKind::NumberKeyword,
        "number",
    );
    assert_child(
        &parsed,
        source,
        conditional.true_type,
        union.types.nodes[1],
        SyntaxKind::BooleanKeyword,
        "boolean",
    );
    let member = members[1];
    let array_node = property_type(
        &parsed,
        source,
        owner,
        member,
        "[NEXT]: T[]",
        SyntaxKind::ArrayType,
        "T[]",
    );
    assert_computed_name(
        &parsed,
        source,
        member,
        property(&parsed, member).name,
        "NEXT",
    );
    let NodeData::ArrayTypeNode(array) = &parsed.arena.get(array_node).unwrap().data else {
        panic!("expected the next property's array annotation");
    };
    assert_child(
        &parsed,
        source,
        array_node,
        array.element_type,
        SyntaxKind::TypeReference,
        "T",
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn malformed_computed_names_keep_exact_errors_and_later_members() {
    for (name, code, message, anchor) in [
        ("[Symbol.iterator", 1005, "']' expected.", ": number"),
        ("[]", 1109, "Expression expected.", "]: number"),
    ] {
        let member_text = format!("{name}: number;");
        let source = format!(
            "interface Broken {{\n  first: string\n  {member_text}\n  next: boolean\n}}\nconst after = 1;\n"
        );
        let parsed = parse_source_file(&source);
        let start = u32::try_from(source.find(anchor).unwrap()).unwrap();
        assert_eq!(
            parsed.diagnostics,
            [Diagnostic {
                range: TextRange::new(TextPos::new(start), TextPos::new(start + 1)),
                code: Some(code),
                category: DiagnosticCategory::Error,
                message: message.to_owned(),
            }],
            "{source}",
        );
        assert_eq!(statements(&parsed).len(), 2);
        let (owner, members) = first_interface(&parsed);
        assert_eq!(members.len(), 3);
        property_type(
            &parsed,
            &source,
            owner,
            members[0],
            "first: string",
            SyntaxKind::StringKeyword,
            "string",
        );
        property_type(
            &parsed,
            &source,
            owner,
            members[1],
            &member_text,
            SyntaxKind::NumberKeyword,
            "number",
        );
        property_type(
            &parsed,
            &source,
            owner,
            members[2],
            "next: boolean",
            SyntaxKind::BooleanKeyword,
            "boolean",
        );
        let computed_node = property(&parsed, members[1]).name;
        let computed = parsed.arena.get(computed_node).unwrap();
        assert_eq!(computed.kind, SyntaxKind::ComputedPropertyName);
        assert_eq!(computed.parent, Some(members[1]));
        assert_written_span(&parsed, &source, computed_node, name);
        let NodeData::ComputedPropertyName(computed) = &computed.data else {
            panic!("expected the recovered computed name");
        };
        if name == "[]" {
            let missing = parsed.arena.get(computed.expression).unwrap();
            assert_eq!(missing.kind, SyntaxKind::Identifier);
            assert_eq!(missing.parent, Some(computed_node));
            assert_eq!(
                missing.range,
                TextRange::new(TextPos::new(start), TextPos::new(start))
            );
            let NodeData::Identifier(identifier) = &missing.data else {
                panic!("expected missing expression identifier");
            };
            assert!(identifier.text.is_empty());
        } else {
            assert_child(
                &parsed,
                &source,
                computed_node,
                computed.expression,
                SyntaxKind::PropertyAccessExpression,
                "Symbol.iterator",
            );
        }
        let after = statements(&parsed)[1];
        assert_written_span(&parsed, &source, after, "const after = 1;");
        let NodeData::VariableStatement(after) = &parsed.arena.get(after).unwrap().data else {
            panic!("expected the later source declaration");
        };
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(after.declaration_list).unwrap().data
        else {
            panic!("expected the later declaration list");
        };
        assert_eq!(list.declarations.nodes.len(), 1);
        let declaration_node = list.declarations.nodes[0];
        let NodeData::VariableDeclaration(declaration) =
            &parsed.arena.get(declaration_node).unwrap().data
        else {
            panic!("expected after declaration");
        };
        assert_child(
            &parsed,
            &source,
            declaration_node,
            declaration.name,
            SyntaxKind::Identifier,
            "after",
        );
        assert_child(
            &parsed,
            &source,
            declaration_node,
            declaration.initializer.expect("written initializer"),
            SyntaxKind::NumericLiteral,
            "1",
        );
    }
}

fn statements(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    for statement in &source.statements.nodes {
        assert_eq!(
            parsed.arena.get(*statement).unwrap().parent,
            Some(parsed.source_file)
        );
    }
    &source.statements.nodes
}

fn first_interface(parsed: &ParseResult) -> (NodeId, &[NodeId]) {
    let owner = statements(parsed)[0];
    let node = parsed.arena.get(owner).unwrap();
    assert_eq!(node.kind, SyntaxKind::InterfaceDeclaration);
    let NodeData::InterfaceDeclaration(interface) = &node.data else {
        panic!("expected interface");
    };
    (owner, &interface.members.nodes)
}

fn property(parsed: &ParseResult, member: NodeId) -> &PropertyDeclarationData {
    let node = parsed.arena.get(member).unwrap();
    assert_eq!(node.kind, SyntaxKind::PropertyDeclaration);
    let NodeData::PropertyDeclaration(property) = &node.data else {
        panic!("expected property data");
    };
    assert!(property.initializer.is_none());
    property
}

fn property_type(
    parsed: &ParseResult,
    source: &str,
    owner: NodeId,
    member: NodeId,
    member_text: &str,
    type_kind: SyntaxKind,
    annotation: &str,
) -> NodeId {
    assert_eq!(parsed.arena.get(member).unwrap().parent, Some(owner));
    assert_written_span(parsed, source, member, member_text);
    let property = property(parsed, member);
    let type_node = property.type_.expect("written property annotation");
    assert_child(parsed, source, member, type_node, type_kind, annotation);
    let member_start = source.find(member_text).unwrap();
    let type_start = member_start + member_text.find(annotation).unwrap();
    let range = parsed.arena.get(type_node).unwrap().range;
    assert_eq!(range.start.get() as usize, type_start);
    assert_eq!(range.end.get() as usize, type_start + annotation.len());
    type_node
}

fn assert_computed_name(
    parsed: &ParseResult,
    source: &str,
    owner: NodeId,
    name: NodeId,
    expression: &str,
) {
    let text = format!("[{expression}]");
    assert_child(
        parsed,
        source,
        owner,
        name,
        SyntaxKind::ComputedPropertyName,
        &text,
    );
    let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(name).unwrap().data else {
        panic!("expected computed name");
    };
    if let Some((left, right)) = expression.split_once('.') {
        assert_child(
            parsed,
            source,
            name,
            computed.expression,
            SyntaxKind::PropertyAccessExpression,
            expression,
        );
        let NodeData::PropertyAccessExpression(access) =
            &parsed.arena.get(computed.expression).unwrap().data
        else {
            panic!("expected dotted computed-name expression");
        };
        assert_child(
            parsed,
            source,
            computed.expression,
            access.expression,
            SyntaxKind::Identifier,
            left,
        );
        assert_child(
            parsed,
            source,
            computed.expression,
            access.name,
            SyntaxKind::Identifier,
            right,
        );
    } else {
        assert_child(
            parsed,
            source,
            name,
            computed.expression,
            SyntaxKind::Identifier,
            expression,
        );
    }
    let name_range = parsed.arena.get(name).unwrap().range;
    let expression_range = parsed.arena.get(computed.expression).unwrap().range;
    assert_eq!(expression_range.start.get(), name_range.start.get() + 1);
    assert_eq!(expression_range.end.get() + 1, name_range.end.get());
}

fn assert_child(
    parsed: &ParseResult,
    source: &str,
    parent: NodeId,
    child: NodeId,
    kind: SyntaxKind,
    text: &str,
) {
    let parent_range = parsed.arena.get(parent).unwrap().range;
    let node = parsed.arena.get(child).unwrap();
    assert_eq!(node.kind, kind);
    assert_eq!(node.parent, Some(parent));
    if kind == SyntaxKind::Identifier {
        let NodeData::Identifier(identifier) = &node.data else {
            panic!("expected identifier data");
        };
        assert_eq!(identifier.text, text);
    }
    assert!(node.range.start >= parent_range.start);
    assert!(node.range.end <= parent_range.end);
    assert_eq!(
        &source[node.range.start.get() as usize..node.range.end.get() as usize],
        text
    );
}

fn assert_written_span(parsed: &ParseResult, source: &str, node: NodeId, text: &str) {
    assert_eq!(
        source.matches(text).count(),
        1,
        "expected one written occurrence of {text:?}"
    );
    let start = source.find(text).unwrap();
    let range = parsed.arena.get(node).unwrap().range;
    assert_eq!(range.start.get() as usize, start, "{text}");
    assert_eq!(range.end.get() as usize, start + text.len(), "{text}");
}
