use std::collections::HashSet;

use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_core::DiagnosticCategory;
use ts_parser::{ParseResult, parse_source_file};

fn statements(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected the parsed source file")
    };
    &file.statements.nodes
}

fn text<'a>(parsed: &ParseResult, source: &'a str, node: NodeId) -> &'a str {
    let range = parsed.arena.get(node).unwrap().range;
    &source[range.start.get() as usize..range.end.get() as usize]
}

fn class_members(parsed: &ParseResult, class: NodeId) -> &[NodeId] {
    match &parsed.arena.get(class).unwrap().data {
        NodeData::ClassDeclaration(data) => &data.members.nodes,
        NodeData::ClassExpression(data) => &data.members.nodes,
        _ => panic!("expected a class"),
    }
}

fn initializer(parsed: &ParseResult, statement: NodeId, name: &str) -> NodeId {
    let NodeData::VariableStatement(statement) = &parsed.arena.get(statement).unwrap().data else {
        panic!("expected a variable statement")
    };
    let NodeData::VariableDeclarationList(list) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected a variable declaration list")
    };
    let [declaration] = list.declarations.nodes.as_slice() else {
        panic!("expected one variable")
    };
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(*declaration).unwrap().data
    else {
        panic!("expected a variable declaration")
    };
    let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name).unwrap().data else {
        panic!("expected a variable name")
    };
    assert_eq!(identifier.text, name);
    variable.initializer.unwrap()
}

fn assert_tree(parsed: &ParseResult, source: &str) {
    let mut pending = vec![parsed.source_file];
    let mut seen = HashSet::new();
    while let Some(id) = pending.pop() {
        assert!(seen.insert(id), "a parsed child must have one owner");
        let node = parsed.arena.get(id).unwrap();
        let start = node.range.start.get() as usize;
        let end = node.range.end.get() as usize;
        assert!(start <= end && end <= source.len());
        assert!(source.is_char_boundary(start) && source.is_char_boundary(end));
        node.for_each_child(|child| {
            let record = parsed.arena.get(child).unwrap();
            assert_eq!(record.parent, Some(id));
            assert!(record.range.start >= node.range.start);
            assert!(record.range.end <= node.range.end);
            pending.push(child);
        });
    }
}

fn diagnostics(parsed: &ParseResult) -> Vec<(Option<u32>, u32, u32, &str)> {
    parsed
        .diagnostics
        .iter()
        .map(|diagnostic| {
            assert_eq!(diagnostic.category, DiagnosticCategory::Error);
            (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
                diagnostic.message.as_str(),
            )
        })
        .collect()
}

#[test]
fn function_overloads_keep_the_ambient_class_and_module_boundaries() {
    let source = concat!(
        "declare module \"database\" {\n",
        "    class Database {\n",
        "        function(\n",
        "            name: string,\n",
        "            options: FunctionOptions,\n",
        "            func: (...args: SQLOutputValue[]) => SQLInputValue,\n",
        "        ): void;\n",
        "        function(name: string, func: (...args: SQLOutputValue[]) => SQLInputValue): void;\n",
        "        readonly isOpen: boolean;\n",
        "        open(): void;\n",
        "        prepare(sql: string): Statement;\n",
        "        createSession(options?: SessionOptions): Session;\n",
        "        [Symbol.dispose](): void;\n",
        "    }\n",
        "    interface Session { close(): void; }\n",
        "    const inside: number;\n",
        "}\n",
        "const after = 1;\n",
    );
    let parsed = parse_source_file(source);
    assert!(diagnostics(&parsed).is_empty(), "{:?}", parsed.diagnostics);
    let [module, after] = statements(&parsed) else {
        panic!("the module must keep its full body")
    };
    let NodeData::ModuleDeclaration(module_data) = &parsed.arena.get(*module).unwrap().data else {
        panic!("expected the ambient module")
    };
    assert_eq!(text(&parsed, source, module_data.name), "\"database\"");
    let block = module_data.body.unwrap();
    let NodeData::ModuleBlock(body) = &parsed.arena.get(block).unwrap().data else {
        panic!("expected the module block")
    };
    let [class, session, inside] = body.statements.nodes.as_slice() else {
        panic!("class members must not become module statements")
    };
    let members = class_members(&parsed, *class);
    assert_eq!(members.len(), 7);
    for (index, parameter_names) in [vec!["name", "options", "func"], vec!["name", "func"]]
        .into_iter()
        .enumerate()
    {
        let method = members[index];
        let NodeData::MethodDeclaration(data) = &parsed.arena.get(method).unwrap().data else {
            panic!("function must be a method, not a declaration")
        };
        assert_eq!(parsed.arena.get(method).unwrap().parent, Some(*class));
        assert_eq!(
            parsed.arena.get(data.name).unwrap().kind,
            SyntaxKind::Identifier
        );
        assert_eq!(text(&parsed, source, data.name), "function");
        assert_eq!(text(&parsed, source, data.type_.unwrap()), "void");
        assert!(data.body.is_none() && data.type_parameters.is_none());
        assert_eq!(data.parameters.nodes.len(), parameter_names.len());
        for (&parameter, expected) in data.parameters.nodes.iter().zip(parameter_names) {
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(parameter).unwrap().data
            else {
                panic!("expected a real method parameter")
            };
            assert_eq!(text(&parsed, source, parameter.name), expected);
            assert!(parameter.type_.is_some());
        }
        let callback = *data.parameters.nodes.last().unwrap();
        let NodeData::ParameterDeclaration(callback) = &parsed.arena.get(callback).unwrap().data
        else {
            unreachable!()
        };
        let NodeData::FunctionTypeNode(callback) =
            &parsed.arena.get(callback.type_.unwrap()).unwrap().data
        else {
            panic!("expected the callback type")
        };
        assert_eq!(
            text(&parsed, source, callback.type_.unwrap()),
            "SQLInputValue"
        );
        let NodeData::ParameterDeclaration(rest) =
            &parsed.arena.get(callback.parameters.nodes[0]).unwrap().data
        else {
            panic!("expected the callback rest parameter")
        };
        assert!(rest.dot_dot_dot_token.is_some());
        assert_eq!(
            text(&parsed, source, rest.type_.unwrap()),
            "SQLOutputValue[]"
        );
    }
    for (&member, expected) in members[2..].iter().zip([
        "readonly isOpen: boolean;",
        "open(): void",
        "prepare(sql: string): Statement",
        "createSession(options?: SessionOptions): Session",
        "[Symbol.dispose](): void",
    ]) {
        assert_eq!(text(&parsed, source, member), expected);
        assert_eq!(parsed.arena.get(member).unwrap().parent, Some(*class));
    }
    assert_eq!(
        parsed.arena.get(members[2]).unwrap().kind,
        SyntaxKind::PropertyDeclaration
    );
    let NodeData::MethodDeclaration(dispose) = &parsed.arena.get(members[6]).unwrap().data else {
        panic!("expected the computed method")
    };
    assert_eq!(
        parsed.arena.get(dispose.name).unwrap().kind,
        SyntaxKind::ComputedPropertyName
    );
    assert_eq!(
        text(&parsed, source, *session),
        "interface Session { close(): void; }"
    );
    assert_eq!(text(&parsed, source, *inside), "const inside: number;");
    let module_end = u32::try_from(source.find("\nconst after").unwrap()).unwrap();
    assert_eq!(
        parsed.arena.get(*module).unwrap().range.end.get(),
        module_end
    );
    assert_eq!(parsed.arena.get(block).unwrap().range.end.get(), module_end);
    assert_eq!(
        text(&parsed, source, initializer(&parsed, *after, "after")),
        "1"
    );
    assert_tree(&parsed, source);
}

#[test]
fn function_keyword_methods_and_fields_keep_their_real_member_shapes() {
    for expression in [false, true] {
        let prefix = if expression {
            "const value = class Named"
        } else {
            "class Named"
        };
        let source = format!(
            "{prefix} {{ function<T>(value: T): T {{ return value; }} \"function\"(): void; function?: number; function!: number; function = 1; }}{}\nconst after = 1;",
            if expression { ";" } else { "" },
        );
        let parsed = parse_source_file(&source);
        assert!(diagnostics(&parsed).is_empty(), "{:?}", parsed.diagnostics);
        let [first, after] = statements(&parsed) else {
            panic!("expected the class and sentinel")
        };
        let class = if expression {
            initializer(&parsed, *first, "value")
        } else {
            *first
        };
        assert_eq!(
            parsed.arena.get(class).unwrap().kind,
            if expression {
                SyntaxKind::ClassExpression
            } else {
                SyntaxKind::ClassDeclaration
            }
        );
        let members = class_members(&parsed, class);
        let [generic, quoted, optional, definite, initialized] = members else {
            panic!("expected five members")
        };
        let NodeData::MethodDeclaration(method) = &parsed.arena.get(*generic).unwrap().data else {
            panic!("expected the generic method")
        };
        assert_eq!(
            text(&parsed, &source, *generic),
            "function<T>(value: T): T { return value; }"
        );
        assert_eq!(text(&parsed, &source, method.name), "function");
        assert_eq!(method.type_parameters.as_ref().unwrap().nodes.len(), 1);
        assert_eq!(
            text(
                &parsed,
                &source,
                method.type_parameters.as_ref().unwrap().nodes[0]
            ),
            "T"
        );
        assert_eq!(
            text(&parsed, &source, method.parameters.nodes[0]),
            "value: T"
        );
        assert_eq!(text(&parsed, &source, method.type_.unwrap()), "T");
        assert_eq!(
            parsed.arena.get(method.body.unwrap()).unwrap().kind,
            SyntaxKind::Block
        );
        let NodeData::MethodDeclaration(method) = &parsed.arena.get(*quoted).unwrap().data else {
            panic!("expected the quoted method")
        };
        assert_eq!(
            parsed.arena.get(method.name).unwrap().kind,
            SyntaxKind::StringLiteral
        );
        for (&member, expected) in [optional, definite]
            .into_iter()
            .zip([SyntaxKind::QuestionToken, SyntaxKind::ExclamationToken])
        {
            let NodeData::PropertyDeclaration(property) = &parsed.arena.get(member).unwrap().data
            else {
                panic!("expected a keyword property")
            };
            assert_eq!(text(&parsed, &source, property.name), "function");
            assert_eq!(
                parsed
                    .arena
                    .get(property.postfix_token.unwrap())
                    .unwrap()
                    .kind,
                expected
            );
            assert_eq!(text(&parsed, &source, property.type_.unwrap()), "number");
        }
        let NodeData::PropertyDeclaration(property) = &parsed.arena.get(*initialized).unwrap().data
        else {
            panic!("expected the initialized property")
        };
        assert_eq!(text(&parsed, &source, property.initializer.unwrap()), "1");
        assert_eq!(
            text(&parsed, &source, initializer(&parsed, *after, "after")),
            "1"
        );
        assert_tree(&parsed, &source);
    }
}

#[test]
fn function_keyword_asi_and_terminators_preserve_following_members() {
    for separator in ["; ", "\n", " /*\n*/ "] {
        let source = format!(
            "class C {{ function{separator}next(): void; }}\ninterface I {{ function(): void; }}"
        );
        let parsed = parse_source_file(&source);
        assert!(diagnostics(&parsed).is_empty(), "{:?}", parsed.diagnostics);
        let [class, interface] = statements(&parsed) else {
            panic!("expected class and interface")
        };
        let [property, method] = class_members(&parsed, *class) else {
            panic!("expected two class members")
        };
        assert_eq!(
            parsed.arena.get(*property).unwrap().kind,
            SyntaxKind::PropertyDeclaration
        );
        assert_eq!(
            text(&parsed, &source, *property),
            if separator.starts_with(';') {
                "function;"
            } else {
                "function"
            }
        );
        assert_eq!(text(&parsed, &source, *method), "next(): void");
        let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(*interface).unwrap().data
        else {
            panic!("expected an interface")
        };
        let [method] = interface.members.nodes.as_slice() else {
            panic!("expected one interface method")
        };
        let NodeData::MethodSignatureDeclaration(method) = &parsed.arena.get(*method).unwrap().data
        else {
            panic!("expected a method signature")
        };
        assert_eq!(text(&parsed, &source, method.name), "function");
        assert_tree(&parsed, &source);
    }
    let source = "class C { function }";
    let parsed = parse_source_file(source);
    assert!(diagnostics(&parsed).is_empty());
    let [class] = statements(&parsed) else {
        panic!("expected one class")
    };
    let [property] = class_members(&parsed, *class) else {
        panic!("expected one property")
    };
    assert_eq!(text(&parsed, source, *property), "function");
    assert_eq!(text(&parsed, source, *class), source);
    assert_tree(&parsed, source);
}

#[test]
fn invalid_nested_function_declarations_keep_the_old_statement_recovery() {
    for declaration in ["function named() {}", "function* named() {}"] {
        let source = format!("class Broken {{ {declaration} }}\nconst after = 1;");
        let parsed = parse_source_file(&source);
        let start = u32::try_from(source.find("function").unwrap()).unwrap();
        let closing = u32::try_from(source.find("}\n").unwrap()).unwrap();
        assert_eq!(
            diagnostics(&parsed),
            [
                (None, start, start + 8, "Declaration expected."),
                (
                    Some(1128),
                    closing,
                    closing + 1,
                    "Declaration or statement expected."
                ),
            ]
        );
        let [class, function, after] = statements(&parsed) else {
            panic!("expected recovered outer declarations")
        };
        assert!(class_members(&parsed, *class).is_empty());
        assert_eq!(text(&parsed, &source, *class), "class Broken {");
        let NodeData::FunctionDeclaration(function_data) =
            &parsed.arena.get(*function).unwrap().data
        else {
            panic!("expected a recovered function declaration")
        };
        assert_eq!(text(&parsed, &source, *function), declaration);
        assert_eq!(text(&parsed, &source, function_data.name.unwrap()), "named");
        assert_eq!(
            function_data.asterisk_token.is_some(),
            declaration.starts_with("function*")
        );
        assert_eq!(
            parsed.arena.get(*function).unwrap().parent,
            Some(parsed.source_file)
        );
        assert_eq!(
            text(&parsed, &source, initializer(&parsed, *after, "after")),
            "1"
        );
        assert_tree(&parsed, &source);
    }
}

#[test]
fn malformed_keyword_members_keep_progress_and_exact_error_spans() {
    for (member, error_token, message, expected_members) in [
        ("function<T>;", ";", "'(' expected.", 2),
        ("function [key](): void;", "[", "';' expected.", 3),
    ] {
        let source = format!("class Broken {{ {member} after(): void; }}\nconst sentinel = 1;");
        let parsed = parse_source_file(&source);
        let start = u32::try_from(source.find(error_token).unwrap()).unwrap();
        assert_eq!(
            diagnostics(&parsed),
            [(Some(1005), start, start + 1, message)]
        );
        let [class, sentinel] = statements(&parsed) else {
            panic!("expected class and sentinel")
        };
        let members = class_members(&parsed, *class);
        assert_eq!(members.len(), expected_members);
        assert_eq!(
            text(&parsed, &source, *members.last().unwrap()),
            "after(): void"
        );
        assert_eq!(
            text(
                &parsed,
                &source,
                initializer(&parsed, *sentinel, "sentinel")
            ),
            "1"
        );
        assert_tree(&parsed, &source);
    }
    let source = "class C { function";
    let parsed = parse_source_file(source);
    let end = u32::try_from(source.len()).unwrap();
    assert_eq!(
        diagnostics(&parsed),
        [(Some(1005), end, end, "'}' expected.")]
    );
    let [class] = statements(&parsed) else {
        panic!("expected a recovered class")
    };
    let [property] = class_members(&parsed, *class) else {
        panic!("expected the keyword property")
    };
    assert_eq!(text(&parsed, source, *property), "function");
    assert_eq!(text(&parsed, source, *class), source);
    assert_tree(&parsed, source);
}
