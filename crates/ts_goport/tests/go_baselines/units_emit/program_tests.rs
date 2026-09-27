//! Ports of internal/compiler/program_test.go (TestProgram,
//! TestIncludeProcessorDiagnosticsWithMissingFileCasing),
//! internal/checker/checker_test.go (TestGetSymbolAtLocation) and
//! internal/checker/tracer_test.go (TestTracerPushPreservesEndArgMutations).
//! The Go benchmarks are not ported.
//!
//! Each test builds a program or starts the process tracing session, so it
//! runs in a child process of its own (see `childprog`).

use super::Subtests;
use super::childprog::{
    in_child, install_map_fs, new_program, new_program_with_config, source_file,
};
use crate::support::vfstest::{MapFile, MapFs};
use ts_goport::frontend::bundled;
use ts_goport::frontend::compiler::{CompilerHost, new_compiler_host};
use ts_goport::frontend::json::json_unmarshal;
use ts_goport::frontend::json_ext::LspAny;
use ts_goport::frontend::tsoptions::{ParseConfigHost, get_parsed_command_line_of_config_file};
use ts_goport::frontend::vfs::{FileMode, Fs};
use ts_goport::gostd::context;
use ts_goport::prelude::*;
use ts_goport::program::ls_program;
use ts_goport::tracing::{Arg, Phase, new_tracer, start_tracing};

// Go: compiler/program_test.go:33 esnextLibs
#[rustfmt::skip]
const ESNEXT_LIBS: &[&str] = &[
    "lib.es5.d.ts",
    "lib.es2015.d.ts",
    "lib.es2016.d.ts",
    "lib.es2017.d.ts",
    "lib.es2018.d.ts",
    "lib.es2019.d.ts",
    "lib.es2020.d.ts",
    "lib.es2021.d.ts",
    "lib.es2022.d.ts",
    "lib.es2023.d.ts",
    "lib.es2024.d.ts",
    "lib.es2025.d.ts",
    "lib.esnext.d.ts",
    "lib.dom.d.ts",
    "lib.dom.iterable.d.ts",
    "lib.dom.asynciterable.d.ts",
    "lib.webworker.importscripts.d.ts",
    "lib.scripthost.d.ts",
    "lib.es2015.core.d.ts",
    "lib.es2015.collection.d.ts",
    "lib.es2015.generator.d.ts",
    "lib.es2015.iterable.d.ts",
    "lib.es2015.promise.d.ts",
    "lib.es2015.proxy.d.ts",
    "lib.es2015.reflect.d.ts",
    "lib.es2015.symbol.d.ts",
    "lib.es2015.symbol.wellknown.d.ts",
    "lib.es2016.array.include.d.ts",
    "lib.es2016.intl.d.ts",
    "lib.es2017.arraybuffer.d.ts",
    "lib.es2017.date.d.ts",
    "lib.es2017.object.d.ts",
    "lib.es2017.sharedmemory.d.ts",
    "lib.es2017.string.d.ts",
    "lib.es2017.intl.d.ts",
    "lib.es2017.typedarrays.d.ts",
    "lib.es2018.asyncgenerator.d.ts",
    "lib.es2018.asynciterable.d.ts",
    "lib.es2018.intl.d.ts",
    "lib.es2018.promise.d.ts",
    "lib.es2018.regexp.d.ts",
    "lib.es2019.array.d.ts",
    "lib.es2019.object.d.ts",
    "lib.es2019.string.d.ts",
    "lib.es2019.symbol.d.ts",
    "lib.es2019.intl.d.ts",
    "lib.es2020.bigint.d.ts",
    "lib.es2020.date.d.ts",
    "lib.es2020.promise.d.ts",
    "lib.es2020.sharedmemory.d.ts",
    "lib.es2020.string.d.ts",
    "lib.es2020.symbol.wellknown.d.ts",
    "lib.es2020.intl.d.ts",
    "lib.es2020.number.d.ts",
    "lib.es2021.promise.d.ts",
    "lib.es2021.string.d.ts",
    "lib.es2021.weakref.d.ts",
    "lib.es2021.intl.d.ts",
    "lib.es2022.array.d.ts",
    "lib.es2022.error.d.ts",
    "lib.es2022.intl.d.ts",
    "lib.es2022.object.d.ts",
    "lib.es2022.string.d.ts",
    "lib.es2022.regexp.d.ts",
    "lib.es2023.array.d.ts",
    "lib.es2023.collection.d.ts",
    "lib.es2023.intl.d.ts",
    "lib.es2024.arraybuffer.d.ts",
    "lib.es2024.collection.d.ts",
    "lib.es2024.object.d.ts",
    "lib.es2024.promise.d.ts",
    "lib.es2024.regexp.d.ts",
    "lib.es2024.sharedmemory.d.ts",
    "lib.es2024.string.d.ts",
    "lib.es2025.collection.d.ts",
    "lib.es2025.float16.d.ts",
    "lib.es2025.intl.d.ts",
    "lib.es2025.iterator.d.ts",
    "lib.es2025.promise.d.ts",
    "lib.es2025.regexp.d.ts",
    "lib.esnext.array.d.ts",
    "lib.esnext.collection.d.ts",
    "lib.esnext.date.d.ts",
    "lib.esnext.decorators.d.ts",
    "lib.esnext.disposable.d.ts",
    "lib.esnext.error.d.ts",
    "lib.esnext.intl.d.ts",
    "lib.esnext.sharedmemory.d.ts",
    "lib.esnext.temporal.d.ts",
    "lib.esnext.typedarrays.d.ts",
    "lib.decorators.d.ts",
    "lib.decorators.legacy.d.ts",
    "lib.esnext.full.d.ts",
];

/// The source files of each Go test case after the libs, in order.
#[rustfmt::skip]
const ORDERED_FILES: &[&str] = &[
    "c:/dev/src2/a/b/c/1.ts",
    "c:/dev/src2/a/b/2.ts",
    "c:/dev/src2/a/b/3.ts",
    "c:/dev/src2/a/4.ts",
    "c:/dev/src2/a/5.ts",
    "c:/dev/src2/a/b/c/d/e/f/6.ts",
    "c:/dev/src2/a/b/c/d/e/7.ts",
    "c:/dev/src2/a/b/c/d/e/8.ts",
    "c:/dev/src2/a/b/c/d/9.ts",
    "c:/dev/src2/a/10.ts",
    "c:/dev/src/index.ts",
];

/// Go `programTest`: (testName, files, target). Every Go case expects
/// `esnextLibs` then `ORDERED_FILES`.
type ProgramTest = (
    &'static str,
    &'static [(&'static str, &'static str)],
    ScriptTarget,
);

// Go: compiler/program_test.go:129 programTestCases
#[rustfmt::skip]
const PROGRAM_TEST_CASES: &[ProgramTest] = &[
    (
        "BasicFileOrdering",
        &[
            ("c:/dev/src/index.ts", "/// <reference path='c:/dev/src2/a/5.ts' />\n/// <reference path='c:/dev/src2/a/10.ts' />"),
            ("c:/dev/src2/a/5.ts", "/// <reference path='4.ts' />"),
            ("c:/dev/src2/a/4.ts", "/// <reference path='b/3.ts' />"),
            ("c:/dev/src2/a/b/3.ts", "/// <reference path='2.ts' />"),
            ("c:/dev/src2/a/b/2.ts", "/// <reference path='c/1.ts' />"),
            ("c:/dev/src2/a/b/c/1.ts", "console.log('hello');"),
            ("c:/dev/src2/a/10.ts", "/// <reference path='b/c/d/9.ts' />"),
            ("c:/dev/src2/a/b/c/d/9.ts", "/// <reference path='e/8.ts' />"),
            ("c:/dev/src2/a/b/c/d/e/8.ts", "/// <reference path='7.ts' />"),
            ("c:/dev/src2/a/b/c/d/e/7.ts", "/// <reference path='f/6.ts' />"),
            ("c:/dev/src2/a/b/c/d/e/f/6.ts", "console.log('world!');"),
        ],
        ScriptTarget::ES_NEXT,
    ),
    (
        "FileOrderingImports",
        &[
            ("c:/dev/src/index.ts", "import * as five from '../src2/a/5.ts';\nimport * as ten from '../src2/a/10.ts';"),
            ("c:/dev/src2/a/5.ts", "import * as four from './4.ts';"),
            ("c:/dev/src2/a/4.ts", "import * as three from './b/3.ts';"),
            ("c:/dev/src2/a/b/3.ts", "import * as two from './2.ts';"),
            ("c:/dev/src2/a/b/2.ts", "import * as one from './c/1.ts';"),
            ("c:/dev/src2/a/b/c/1.ts", "console.log('hello');"),
            ("c:/dev/src2/a/10.ts", "import * as nine from './b/c/d/9.ts';"),
            ("c:/dev/src2/a/b/c/d/9.ts", "import * as eight from './e/8.ts';"),
            ("c:/dev/src2/a/b/c/d/e/8.ts", "import * as seven from './7.ts';"),
            ("c:/dev/src2/a/b/c/d/e/7.ts", "import * as six from './f/6.ts';"),
            ("c:/dev/src2/a/b/c/d/e/f/6.ts", "console.log('world!');"),
        ],
        ScriptTarget::ES_NEXT,
    ),
    (
        "FileOrderingCycles",
        &[
            ("c:/dev/src/index.ts", "import * as five from '../src2/a/5.ts';\nimport * as ten from '../src2/a/10.ts';"),
            ("c:/dev/src2/a/5.ts", "import * as four from './4.ts';"),
            ("c:/dev/src2/a/4.ts", "import * as three from './b/3.ts';"),
            ("c:/dev/src2/a/b/3.ts", "import * as two from './2.ts';\nimport * as cycle from 'c:/dev/src/index.ts'; "),
            ("c:/dev/src2/a/b/2.ts", "import * as one from './c/1.ts';"),
            ("c:/dev/src2/a/b/c/1.ts", "console.log('hello');"),
            ("c:/dev/src2/a/10.ts", "import * as nine from './b/c/d/9.ts';"),
            ("c:/dev/src2/a/b/c/d/9.ts", "import * as eight from './e/8.ts';\nimport * as cycle from 'c:/dev/src/index.ts';"),
            ("c:/dev/src2/a/b/c/d/e/8.ts", "import * as seven from './7.ts';"),
            ("c:/dev/src2/a/b/c/d/e/7.ts", "import * as six from './f/6.ts';"),
            ("c:/dev/src2/a/b/c/d/e/f/6.ts", "console.log('world!');"),
        ],
        ScriptTarget::ES_NEXT,
    ),
];

// Go: compiler/program_test.go:225 TestProgram
// PORT: the Go subtests run on one map file system each. Here they run in
// one child process with one map file system (the OS override is set once
// per process); each subtest writes its files over the previous ones, and
// every case writes the same eleven file names.
#[test]
fn test_program() {
    in_child(module_path!(), "test_program", || {
        let map_fs = MapFs::from_map(
            Vec::<(String, MapFile)>::new(),
            false, /*useCaseSensitiveFileNames*/
        );
        install_map_fs(&map_fs, "c:/dev/src");
        let lib_prefix = format!("{}/", bundled::lib_path());
        let mut t = Subtests::new("TestProgram");
        for &(test_name, files, target) in PROGRAM_TEST_CASES {
            t.run(test_name, || {
                let fs = map_fs.fs();
                for &(file_name, contents) in files {
                    let _ = fs.write_file(file_name, contents);
                }

                let program = new_program(
                    map_fs.fs(),
                    "c:/dev/src",
                    &["c:/dev/src/index.ts"],
                    CompilerOptions {
                        target,
                        ..Default::default()
                    },
                );

                let actual_files: Vec<String> = program
                    .get_source_files()
                    .iter()
                    .map(|file| {
                        let name = file.parse_options.file_name.as_str();
                        name.strip_prefix(&lib_prefix).unwrap_or(name).to_string()
                    })
                    .collect();

                let expected_files: Vec<String> = ESNEXT_LIBS
                    .iter()
                    .chain(ORDERED_FILES)
                    .map(|s| s.to_string())
                    .collect();
                if expected_files != actual_files {
                    return Err(format!(
                        "assert.DeepEqual(expectedFiles, actualFiles) failed\n  expected: {expected_files:?}\n  actual:   {actual_files:?}"
                    ));
                }
                Ok(())
            });
        }
        t.finish();
    });
}

// Go: compiler/program_test.go:267 TestIncludeProcessorDiagnosticsWithMissingFileCasing
#[test]
fn test_include_processor_diagnostics_with_missing_file_casing() {
    in_child(
        module_path!(),
        "test_include_processor_diagnostics_with_missing_file_casing",
        || {
            // Use case-sensitive file names so that /src/MyFile.ts and /src/myFile.ts
            // have different canonical paths but the same lower-case path, triggering
            // file casing diagnostics in the include processor.
            let map_fs = MapFs::from_map(
                Vec::<(String, MapFile)>::new(),
                true, /*useCaseSensitiveFileNames*/
            );
            install_map_fs(&map_fs, "/");

            // Only create the lowercase version; /src/MyFile.ts does not exist.
            let _ = map_fs
                .fs()
                .write_file("/src/myFile.ts", "export const y = 2;");

            // List both casings as root files. The first one (/src/MyFile.ts) will fail
            // to load because it does not exist on the case-sensitive filesystem.
            let program = new_program(
                map_fs.fs(),
                "/",
                &["/src/MyFile.ts", "/src/myFile.ts"],
                CompilerOptions {
                    skip_default_lib_check: Tristate::True,
                    ..Default::default()
                },
            );

            // GetProgramDiagnostics triggers getDiagnostics which processes all
            // include processor diagnostics including the casing diagnostic whose
            // file path points to the missing /src/MyFile.ts. Before the fix this
            // panicked with a nil pointer dereference.
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                ls_program::get_program_diagnostics(program)
            }));
            if let Err(payload) = result {
                panic!(
                    "assertion failed: error is not nil: panic: {}",
                    crate::astnav_api::panic_message(payload.as_ref())
                );
            }
        },
    );
}

// Go: checker/checker_test.go:19 TestGetSymbolAtLocation
#[test]
fn test_get_symbol_at_location() {
    in_child(module_path!(), "test_get_symbol_at_location", || {
        let content = "interface Foo {
  bar: string;
}
declare const foo: Foo;
foo.bar;";
        let map_fs = MapFs::from_map(
            [
                ("/foo.ts", content),
                (
                    "/tsconfig.json",
                    r#"
				{
					"compilerOptions": {},
					"files": ["foo.ts"]
				}
			"#,
                ),
            ],
            false, /*useCaseSensitiveFileNames*/
        );
        install_map_fs(&map_fs, "/");
        let fs = bundled::wrap_fs(map_fs.fs());

        let cd = "/";
        let host = new_compiler_host(cd, fs, &bundled::lib_path(), None, None);

        // PORT: Go passes the compiler host, which is also a
        // `tsoptions.ParseConfigHost`; `HostAsParseConfigHost` forwards the
        // two methods.
        let (parsed, errors) = get_parsed_command_line_of_config_file(
            "/tsconfig.json",
            Some(&CompilerOptions::default()),
            None,
            &HostAsParseConfigHost(host),
            None,
        );
        assert_eq!(errors.len(), 0, "Expected no errors in parsed command line");

        let p = new_program_with_config(map_fs.fs(), cd, Rc::new(parsed.expect("parsed config")));
        let _current = ls_program::enter(p);
        ls_program::bind_source_files(p);
        let (c, done) = ls_program::get_type_checker(p, &context::background());
        let file = source_file(p, "/foo.ts").root;
        let statements = file.statements();
        let interface_id = statements.get(0).name();
        let var_id = statements
            .get(1)
            .declaration_list()
            .declarations()
            .nodes()
            .get(0)
            .name();
        let prop_access = statements.get(2).expression();
        let nodes = [interface_id, var_id, prop_access];
        for node in nodes {
            let symbol = c.borrow_mut().get_symbol_at_location_exported(node);
            assert!(symbol.is_some(), "Expected symbol to be non-nil");
        }
        done.call();
    });
}

/// A compiler host used as a `tsoptions.ParseConfigHost`.
struct HostAsParseConfigHost(Rc<dyn CompilerHost>);

impl ParseConfigHost for HostAsParseConfigHost {
    fn fs(&self) -> Rc<dyn Fs> {
        self.0.fs()
    }
    fn get_current_directory(&self) -> String {
        self.0.get_current_directory()
    }
}

/// Go `testTraceEvent`: (ph, name, args).
type TestTraceEvent = (String, String, IndexMap<String, LspAny>);

// Go: checker/tracer_test.go:60 findTestTraceEvent
fn find_test_trace_event(events: &[TestTraceEvent], phase: &str, name: &str) -> TestTraceEvent {
    for event in events {
        if event.0 == phase && event.1 == name {
            return event.clone();
        }
    }
    panic!("failed to find {phase} event {name:?}");
}

// Go: checker/tracer_test.go:14 TestTracerPushPreservesEndArgMutations
// PORT: Go passes the args map to `Push` and mutates it before `pop()`;
// the end event shows the change and the caller's map never gets
// "checkerId". The Rust `Push` takes the args by value, so the caller has no
// map to check, and the change goes through `Pop::args_mut` (what
// `getVariancesWorker` uses). The trace session is the process global and
// writes through the OS override, so the test runs in a child process.
#[test]
fn test_tracer_push_preserves_end_arg_mutations() {
    in_child(
        module_path!(),
        "test_tracer_push_preserves_end_arg_mutations",
        || {
            let map_fs = MapFs::from_map(
                [(
                    "/trace",
                    MapFile {
                        mode: FileMode::DIR,
                        ..MapFile::default()
                    },
                )],
                true,
            );
            install_map_fs(&map_fs, "/");

            let tr = start_tracing("/trace", "", true /*deterministic*/).expect("StartTracing");

            let args = vec![("id", Arg::Int(1))];
            let tracer = new_tracer(tr, 7);
            let mut pop = tracer.push(Phase::CheckTypes, "getVariancesWorker", args, true);

            pop.args_mut()
                .expect("recorded event")
                .push(("variances", Arg::Strs(vec!["out".to_string()])));
            drop(pop);

            tr.stop_tracing().expect("StopTracing");

            let (trace_text, ok) = map_fs.fs().read_file("/trace/trace.json");
            assert!(ok, "trace.json exists");

            let mut raw_events = LspAny::Null;
            json_unmarshal(trace_text.as_bytes(), &mut raw_events, &[]).expect("json.Unmarshal");
            let LspAny::Array(raw_events) = raw_events else {
                panic!("trace.json is not an array");
            };
            let events: Vec<TestTraceEvent> = raw_events
                .into_iter()
                .map(|event| {
                    let LspAny::Object(fields) = event else {
                        panic!("trace event is not an object");
                    };
                    let text = |key: &str| match fields.get(key) {
                        Some(LspAny::String(s)) => s.clone(),
                        _ => String::new(),
                    };
                    let args = match fields.get("args") {
                        Some(LspAny::Object(args)) => args.clone(),
                        _ => IndexMap::new(),
                    };
                    (text("ph"), text("name"), args)
                })
                .collect();

            let begin_event = find_test_trace_event(&events, "B", "getVariancesWorker");
            assert_eq!(begin_event.2.get("checkerId"), Some(&LspAny::Number(7.0)));
            assert_eq!(begin_event.2.get("variances"), None);

            let end_event = find_test_trace_event(&events, "E", "getVariancesWorker");
            assert_eq!(end_event.2.get("checkerId"), Some(&LspAny::Number(7.0)));
            let Some(LspAny::Array(variances)) = end_event.2.get("variances") else {
                panic!("end event has no variances array: {:?}", end_event.2);
            };
            assert_eq!(variances, &vec![LspAny::String("out".to_string())]);
        },
    );
}
