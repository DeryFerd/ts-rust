use ts_compiler::{CanonicalProgramCheckFailureClass, Program};
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

#[test]
fn canonical_program_rejects_exported_class_as_a_typed_boundary() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        "export class Exported { value?: string; }\n",
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
