use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::SymbolFlags;
use ts_compiler::{CanonicalProgramCheckFailureClass, CanonicalProgramQueries, Program};
use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use ts_vfs::{FileSystem, MemoryFileSystem};

fn canonical_options() -> CompilerOptions {
    CompilerOptions {
        module: ModuleKind::EsNext,
        module_specified: true,
        module_resolution: ModuleResolutionKind::Bundler,
        lib: Some(vec!["es5".to_owned()]),
        strict: true,
        ..CompilerOptions::default()
    }
}

#[test]
fn canonical_program_checks_primitive_class_members() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "class Model {\n",
            "  readonly value?: string;\n",
            "  definite!: number;\n",
            "  static readonly count: number;\n",
            "}\n",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    assert!(program.diagnostics().is_empty());
}

#[test]
fn canonical_program_checks_default_class_construction() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "class Model { value!: string; }\n",
            "const model = new Model();\n",
            "const value = model.value;\n",
        ),
    )
    .unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    assert!(program.diagnostics().is_empty());
}

#[test]
fn canonical_program_rejects_unsupported_class_construction_as_a_typed_boundary() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        "class Model { value!: string; }\nconst model = new Model(1);\n",
    )
    .unwrap();

    let error = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap_err();

    assert_eq!(
        error.failure_class(),
        CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "E00.SOURCE_SYNTAX",
        }
    );
}

#[test]
fn canonical_program_reports_uninitialized_instance_field() {
    let fs = MemoryFileSystem::new(true);
    let source = concat!(
        "class Unsafe {\n",
        "  value: string;\n",
        "  static count: number;\n",
        "}\n",
    );
    fs.write_file("/project/main.ts", source).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    let [diagnostic] = program.diagnostics() else {
        panic!(
            "expected one field initialization diagnostic: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(diagnostic.code, Some(2564));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/main.ts"));
    assert_eq!(
        diagnostic.message,
        "Property 'value' has no initializer and is not definitely assigned in the constructor."
    );
    let start = u32::try_from(source.find("value").unwrap()).unwrap();
    let range = diagnostic.range.expect("field name range");
    assert_eq!((range.start.get(), range.end.get()), (start, start + 5));
}

fn assert_exported_class_program_queries(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
) -> (NodeRef, NodeRef) {
    let source = program
        .source_file("/project/main.ts")
        .expect("the canonical program retains its exported class source");
    assert_eq!(source.file_name, "/project/main.ts");
    assert_eq!(source.binding.file_id(), Some(source.id));
    assert!(!source.is_default_library);

    let NodeData::SourceFile(root) = &source
        .parse
        .arena
        .get(source.parse.source_file)
        .unwrap()
        .data
    else {
        panic!("the exported class belongs to the original program source")
    };
    let [declaration] = root.statements.nodes.as_slice() else {
        panic!("the source retains exactly one exported class")
    };
    let declaration = source.node_ref(*declaration).unwrap();
    let NodeData::ClassDeclaration(class) = &source.parse.arena.get(declaration.node).unwrap().data
    else {
        panic!("the program statement remains a class declaration")
    };
    let class_name = source.node_ref(class.name.unwrap()).unwrap();
    let [field] = class.members.nodes.as_slice() else {
        panic!("the exported class retains one optional member")
    };
    let field = source.node_ref(*field).unwrap();
    let NodeData::PropertyDeclaration(property) = &source.parse.arena.get(field.node).unwrap().data
    else {
        panic!("the class member remains its original property declaration")
    };
    let field_name = source.node_ref(property.name).unwrap();
    let annotation = source.node_ref(property.type_.unwrap()).unwrap();
    assert_eq!(
        source
            .parse
            .arena
            .get(property.postfix_token.unwrap())
            .unwrap()
            .kind,
        SyntaxKind::QuestionToken,
    );

    let bound_owner = source.binding.exports.get("Exported").unwrap();
    let bound_class = source.binding.symbols.get(bound_owner).unwrap();
    assert!(bound_class.flags.contains(SymbolFlags::CLASS));
    assert_eq!(bound_class.value_declaration, Some(declaration.node));
    let bound_field = bound_class.members.get("value").unwrap();
    let bound_property = source.binding.symbols.get(bound_field).unwrap();
    assert!(bound_property.flags.contains(SymbolFlags::PROPERTY));

    let owner = queries
        .get_symbol_at_location(declaration)
        .unwrap()
        .expect("the exported class retains its canonical declaration symbol");
    assert_eq!(
        queries.get_symbol_at_location(class_name).unwrap(),
        Some(owner)
    );
    assert_eq!(queries.symbol_to_string(owner).unwrap(), "Exported");
    assert_eq!(
        queries.get_symbol_declarations(owner).unwrap(),
        &[declaration]
    );
    let member = queries
        .get_symbol_at_location(field)
        .unwrap()
        .expect("the optional property retains its canonical member symbol");
    assert_eq!(
        queries.get_symbol_at_location(field_name).unwrap(),
        Some(member)
    );
    assert_eq!(queries.symbol_to_string(member).unwrap(), "value");
    assert_eq!(queries.get_symbol_declarations(member).unwrap(), &[field]);
    let member_type = queries.get_type_at_location(annotation).unwrap();
    assert_eq!(queries.type_to_string(member_type).unwrap(), "string");
    assert_eq!(
        queries.get_symbol_at_location(declaration).unwrap(),
        Some(owner)
    );
    assert_eq!(queries.get_symbol_at_location(field).unwrap(), Some(member));
    assert_eq!(
        queries.get_type_at_location(annotation).unwrap(),
        member_type
    );

    (declaration, field)
}

#[test]
fn canonical_program_publishes_exported_class_and_member_symbols() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        "export class Exported { value?: string; }\n",
    )
    .unwrap();

    let (program, nodes) = Program::try_new_with_canonical_checker_and_queries(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
        assert_exported_class_program_queries,
    )
    .expect("authenticated exported classes check successfully");

    let (declaration, field) = nodes.expect("the canonical checker runs the symbol queries");
    assert!(program.diagnostics().is_empty());
    assert_eq!(
        program
            .source_file_by_id(declaration.file)
            .unwrap()
            .file_name,
        "/project/main.ts",
    );
    assert_eq!(
        program.node(declaration).unwrap().kind,
        SyntaxKind::ClassDeclaration
    );
    assert_eq!(
        program.node(field).unwrap().kind,
        SyntaxKind::PropertyDeclaration
    );
}

#[test]
fn canonical_program_reports_anonymous_decorated_class_diagnostics() {
    let fs = MemoryFileSystem::new(true);
    let source = "class {\n  @x\n  m() {}\n};\n";
    fs.write_file("/project/main.ts", source).unwrap();

    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/project",
        &["main.ts".to_owned()],
        canonical_options(),
    )
    .unwrap();

    let [class, decorator] = program.diagnostics() else {
        panic!(
            "expected anonymous class and missing decorator diagnostics: {:?}",
            program.diagnostics()
        );
    };
    assert_eq!(class.code, Some(1211));
    assert_eq!(class.file_name.as_deref(), Some("/project/main.ts"));
    assert_eq!(
        class.message,
        "A class declaration without the 'default' modifier must have a name."
    );
    let class_range = class.range.expect("class keyword range");
    assert_eq!((class_range.start.get(), class_range.end.get()), (0, 5));

    assert_eq!(decorator.code, Some(2304));
    assert_eq!(decorator.file_name.as_deref(), Some("/project/main.ts"));
    assert_eq!(decorator.message, "Cannot find name 'x'.");
    let decorator_start = u32::try_from(source.find("@x").unwrap() + 1).unwrap();
    let decorator_range = decorator.range.expect("decorator identifier range");
    assert_eq!(
        (decorator_range.start.get(), decorator_range.end.get()),
        (decorator_start, decorator_start + 1)
    );
}
