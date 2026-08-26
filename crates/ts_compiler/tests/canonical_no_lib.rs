use ts_ast::FileId;
use ts_compiler::Program;
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

fn assert_file_ids(program: &Program) {
    for (index, source) in program.source_files().iter().enumerate() {
        let id = FileId::new(u32::try_from(index).unwrap());
        assert_eq!(source.id, id);
        assert_eq!(source.binding.file_id(), Some(id));
        assert!(
            source
                .binding
                .is_for_source(&source.parse.arena, source.parse.source_file)
        );
        assert!(std::ptr::eq(program.source_file_by_id(id).unwrap(), source));
    }
}

fn assert_missing_global_types(program: &Program) {
    let expected = [
        "Array",
        "Boolean",
        "CallableFunction",
        "Function",
        "IArguments",
        "NewableFunction",
        "Number",
        "Object",
        "RegExp",
        "String",
    ]
    .map(|name| format!("Cannot find global type '{name}'."));
    assert_eq!(
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| &diagnostic.message)
            .collect::<Vec<_>>(),
        expected.iter().collect::<Vec<_>>(),
    );
    assert!(
        program
            .diagnostics()
            .iter()
            .all(|diagnostic| { diagnostic.code == Some(2318) && diagnostic.file_name.is_none() })
    );
}

#[test]
fn canonical_no_lib_skips_default_explicit_and_reference_libraries() {
    let fs = MemoryFileSystem::new(true);
    for (file, source) in [
        (
            "/project/main.ts",
            concat!(
                "/// <reference lib='es2015.promise' />\n",
                "/// <reference path='./globals.d.ts' />\n",
                "/// <reference types='pkg' />\n",
                "export {};\n",
            ),
        ),
        (
            "/project/custom-lib.d.ts",
            "/// <reference lib='es2015.symbol' />\ninterface ExplicitLibrary {}",
        ),
        (
            "/project/globals.d.ts",
            concat!(
                "/// <reference lib='es2015.iterable' />\n",
                "/// <reference path='./nested.d.ts' />\n",
                "declare const pathValue: string;\n",
            ),
        ),
        ("/project/nested.d.ts", "declare const nestedValue: number;"),
        (
            "/project/node_modules/@types/pkg/index.d.ts",
            "declare const packageValue: boolean;",
        ),
    ] {
        fs.write_file(file, source).unwrap();
    }

    for lib in [None, Some(vec![String::from("es5")])] {
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &[String::from("main.ts"), String::from("custom-lib.d.ts")],
            CompilerOptions {
                no_lib: true,
                lib,
                types: Some(Vec::new()),
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        assert!(program.options().no_lib);
        assert_eq!(
            program
                .source_files()
                .iter()
                .map(|source| source.file_name.as_str())
                .collect::<Vec<_>>(),
            [
                "/project/main.ts",
                "/project/custom-lib.d.ts",
                "/project/globals.d.ts",
                "/project/node_modules/@types/pkg/index.d.ts",
                "/project/nested.d.ts",
            ],
        );
        assert!(
            program
                .source_files()
                .iter()
                .all(|source| !source.is_default_library)
        );
        assert_file_ids(&program);
    }
}

#[test]
fn canonical_no_resolve_preserves_reference_libraries() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "/// <reference path='./globals.d.ts' />\n",
            "/// <reference lib='es2015.promise' />\n",
            "export {};\n",
        ),
    )
    .unwrap();
    fs.write_file("/project/globals.d.ts", "declare const pathValue: string;")
        .unwrap();

    for no_resolve in [false, true] {
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &[String::from("main.ts")],
            CompilerOptions {
                lib: Some(Vec::new()),
                no_resolve,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        let mut expected = vec!["/project/main.ts"];
        if !no_resolve {
            expected.push("/project/globals.d.ts");
        }
        expected.push("/__typescript/lib/lib.es2015.promise.d.ts");
        assert_eq!(
            program
                .source_files()
                .iter()
                .map(|source| source.file_name.as_str())
                .collect::<Vec<_>>(),
            expected,
            "noResolve={no_resolve}",
        );
        assert_missing_global_types(&program);
        assert_file_ids(&program);
    }
}

#[test]
fn canonical_no_default_lib_directive_keeps_library_selection() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(
        "/project/main.ts",
        concat!(
            "/// <reference no-default-lib='true' />\n",
            "/// <reference lib='es2015.promise' />\n",
            "export {};\n",
        ),
    )
    .unwrap();

    for lib in [None, Some(Vec::new()), Some(vec![String::from("es5")])] {
        let has_default_root = lib.is_none();
        let has_es5 = lib.as_ref().is_none_or(|libraries| !libraries.is_empty());
        let program = Program::try_new_with_canonical_checker(
            &fs,
            "/project",
            &[String::from("main.ts")],
            CompilerOptions {
                lib,
                ..CompilerOptions::default()
            },
        )
        .unwrap();

        assert!(!program.options().no_lib);
        assert!(program.source_files()[0].file_name.ends_with("/main.ts"));
        assert_eq!(
            program.source_file("/__typescript/lib/lib.d.ts").is_some(),
            has_default_root,
        );
        assert_eq!(
            program
                .source_file("/__typescript/lib/lib.es5.d.ts")
                .is_some(),
            has_es5,
        );
        assert!(
            program
                .source_file("/__typescript/lib/lib.es2015.promise.d.ts")
                .is_some()
        );
        if has_es5 {
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
        } else {
            assert_missing_global_types(&program);
        }
        assert_file_ids(&program);
    }
}
