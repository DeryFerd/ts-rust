//! Ports of internal/execute/build/graph_test.go and
//! internal/execute/tsc/extendedconfigcache_test.go.

use super::Subtests;
use crate::support::runner::FileMap;
use crate::support::test_sys::new_tsc_system;
use crate::support::vfstest;
use std::rc::Rc;
use ts_goport::execute::build::command_line::parse_build_command_line;
use ts_goport::execute::build::host::TscExtendedConfigCache;
use ts_goport::execute::build::orchestrator::{Options, new_orchestrator};
use ts_goport::execute::tsc::compile::{System, SystemParseConfigHost};
use ts_goport::frontend::tsoptions::{
    ParseConfigHost, ParsedCommandLine, get_parsed_command_line_of_config_file,
};
use ts_goport::frontend::vfs::Fs;

// ---------------------------------------------------------------------------
// execute/build/graph_test.go
// ---------------------------------------------------------------------------

/// Go `buildOrderTestCase`.
struct BuildOrderTestCase {
    name: &'static str,
    projects: &'static [&'static str],
    expected: &'static [&'static str],
    // ts#64220
    expected_schedule: &'static [&'static str],
    circular: bool,
}

// Go: execute/build/graph_test.go:16 TestBuildOrderGenerator
#[test]
fn test_build_order_generator() {
    #[rustfmt::skip]
    let test_cases = [
        BuildOrderTestCase { name: "specify two roots", projects: &["A", "G"], expected: &["D", "E", "C", "B", "A", "G"], expected_schedule: &["D", "E", "G", "C", "B", "A"], circular: false },
        BuildOrderTestCase { name: "multiple parts of the same graph in various orders", projects: &["A"], expected: &["D", "E", "C", "B", "A"], expected_schedule: &["D", "E", "C", "B", "A"], circular: false },
        BuildOrderTestCase { name: "multiple parts of the same graph in various orders", projects: &["A", "C", "D"], expected: &["D", "E", "C", "B", "A"], expected_schedule: &["D", "E", "C", "B", "A"], circular: false },
        BuildOrderTestCase { name: "multiple parts of the same graph in various orders", projects: &["D", "C", "A"], expected: &["D", "E", "C", "B", "A"], expected_schedule: &["D", "E", "C", "B", "A"], circular: false },
        BuildOrderTestCase { name: "other orderings", projects: &["F"], expected: &["E", "F"], expected_schedule: &["E", "F"], circular: false },
        BuildOrderTestCase { name: "other orderings", projects: &["E"], expected: &["E"], expected_schedule: &["E"], circular: false },
        BuildOrderTestCase { name: "other orderings", projects: &["F", "C", "A"], expected: &["E", "F", "D", "C", "B", "A"], expected_schedule: &["E", "D", "F", "C", "B", "A"], circular: false },
        BuildOrderTestCase { name: "returns circular order", projects: &["H"], expected: &["E", "J", "I", "H"], expected_schedule: &["E", "J", "I", "H"], circular: true },
        BuildOrderTestCase { name: "returns circular order", projects: &["A", "H"], expected: &["D", "E", "C", "B", "A", "J", "I", "H"], expected_schedule: &["D", "E", "C", "J", "B", "I", "A", "H"], circular: true },
    ];
    let mut t = Subtests::new("TestBuildOrderGenerator");
    for testcase in &test_cases {
        testcase.run(&mut t);
    }
    t.finish();
}

impl BuildOrderTestCase {
    // Go: execute/build/graph_test.go:41 configName
    fn config_name(project: &str) -> String {
        format!("/home/src/workspaces/project/{project}/tsconfig.json")
    }

    // Go: execute/build/graph_test.go:45 projectName
    fn project_name(config: &str) -> String {
        let s = config
            .strip_prefix("/home/src/workspaces/project/")
            .unwrap_or(config);
        s.strip_suffix("/tsconfig.json").unwrap_or(s).to_string()
    }

    // Go: execute/build/graph_test.go:51 run
    fn run(&self, t: &mut Subtests) {
        t.run(
            &format!("{} - {}", self.name, self.projects.join(",")),
            || self.run_case(),
        );
    }

    fn run_case(&self) -> Result<(), String> {
        // PORT: Go ranges over the `deps` map; the order does not matter.
        let deps: &[(&str, &[&str])] = &[
            ("A", &["B", "C"]),
            ("B", &["C", "D"]),
            ("C", &["D", "E"]),
            ("F", &["E"]),
            ("H", &["I"]),
            ("I", &["J"]),
            ("J", &["H", "E"]),
        ];
        let deps_of = |project: &str| -> Vec<String> {
            deps.iter()
                .find(|(p, _)| *p == project)
                .map(|(_, d)| d.iter().map(|s| s.to_string()).collect())
                .unwrap_or_default()
        };
        let reverse_deps_of = |project: &str| -> Vec<String> {
            let mut out = Vec::new();
            for (p, ds) in deps {
                if ds.contains(&project) {
                    out.push(p.to_string());
                }
            }
            out
        };
        let verify_deps = |orchestrator: &ts_goport::execute::build::orchestrator::Orchestrator,
                           build_order: &[String],
                           has_down_stream: bool|
         -> Result<(), String> {
            for (index, project) in build_order.iter().enumerate() {
                let upstream: Vec<String> = orchestrator
                    .upstream(&Self::config_name(project))
                    .iter()
                    .map(|c| Self::project_name(c))
                    .collect();
                let expected_upstream = deps_of(project);
                if upstream.len() > expected_upstream.len() {
                    return Err(format!(
                        "Expected upstream for {project} to be at most {}, got {}",
                        expected_upstream.len(),
                        upstream.len()
                    ));
                }
                for expected in &expected_upstream {
                    if build_order[..index].contains(expected) {
                        if !upstream.contains(expected) {
                            return Err(format!(
                                "Expected upstream for {project} to contain {expected}"
                            ));
                        }
                    } else if upstream.contains(expected) {
                        return Err(format!(
                            "Expected upstream for {project} to not contain {expected}"
                        ));
                    }
                }

                let downstream: Vec<String> = orchestrator
                    .downstream(&Self::config_name(project))
                    .iter()
                    .map(|c| Self::project_name(c))
                    .collect();
                let expected_downstream = if has_down_stream {
                    reverse_deps_of(project)
                } else {
                    Vec::new()
                };
                if downstream.len() > expected_downstream.len() {
                    return Err(format!(
                        "Expected downstream for {project} to be at most {}, got {}",
                        expected_downstream.len(),
                        downstream.len()
                    ));
                }
                for expected in &expected_downstream {
                    if build_order[index + 1..].contains(expected) {
                        if !downstream.contains(expected) {
                            return Err(format!(
                                "Expected downstream for {project} to contain {expected}"
                            ));
                        }
                    } else if downstream.contains(expected) {
                        return Err(format!(
                            "Expected downstream for {project} to not contain {expected}"
                        ));
                    }
                }
            }
            Ok(())
        };

        let mut files = FileMap::new();
        for project in ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J"] {
            files.insert(
                format!("/home/src/workspaces/project/{project}/{project}.ts"),
                "export {}".into(),
            );
            let mut references_str = String::new();
            let project_deps = deps_of(project);
            if !project_deps.is_empty() {
                references_str = format!(
                    r#", "references": [{}]"#,
                    project_deps
                        .iter()
                        .map(|dep| format!(r#"{{ "path": "../{dep}" }}"#))
                        .collect::<Vec<_>>()
                        .join(",")
                );
            }
            files.insert(
                Self::config_name(project),
                format!(
                    r#"{{
                "compilerOptions": {{ "composite": true }},
                "files": ["./{project}.ts"],
                {references_str}
            }}"#
                )
                .into(),
            );
        }

        let sys: Rc<dyn System> =
            Rc::new(new_tsc_system(files, true, "/home/src/workspaces/project"));
        let build = |flag: &str| -> ts_goport::execute::build::orchestrator::Orchestrator {
            let mut args: Vec<String> = vec!["--build".to_string(), flag.to_string()];
            args.extend(self.projects.iter().map(|p| p.to_string()));
            let build_command = parse_build_command_line(&args, &SystemParseConfigHost(&*sys));
            new_orchestrator(Options {
                sys: Rc::clone(&sys),
                command: Rc::new(build_command),
                testing: None,
            })
        };
        let mut orchestrator = build("--dry");
        orchestrator.generate_graph(None);
        let build_order: Vec<String> = orchestrator
            .order()
            .iter()
            .map(|c| Self::project_name(c))
            .collect();
        if build_order != self.expected {
            return Err(format!(
                "assert.DeepEqual(buildOrder, b.expected) failed: got {build_order:?}, want {:?}",
                self.expected
            ));
        }
        verify_deps(&orchestrator, &build_order, false)?;
        // Go: graph_test.go:123-125 (ts#64220)
        let schedule_order: Vec<String> = orchestrator
            .schedule_order()
            .iter()
            .map(|c| Self::project_name(c))
            .collect();
        if schedule_order != self.expected_schedule {
            return Err(format!(
                "assert.DeepEqual(scheduleOrder, b.expectedSchedule) failed: got {schedule_order:?}, want {:?}",
                self.expected_schedule
            ));
        }
        verify_deps(&orchestrator, &schedule_order, false)?;

        if !self.circular {
            for (project, project_deps) in deps {
                let child = Self::config_name(project);
                // PORT: Go looks up config names in the project-name order,
                // so the index is always -1 and the loop always continues.
                let Some(child_index) = build_order.iter().position(|p| *p == child) else {
                    continue;
                };
                for dep in *project_deps {
                    let parent = Self::config_name(dep);
                    let parent_index = build_order
                        .iter()
                        .position(|p| *p == parent)
                        .map_or(-1, |i| i as i64);
                    if child_index as i64 <= parent_index {
                        return Err(format!(
                            "Expecting child {project} to be built after parent {dep}"
                        ));
                    }
                }
            }
        }

        orchestrator.generate_graph_reusing_old_tasks();
        let build_order2: Vec<String> = orchestrator
            .order()
            .iter()
            .map(|c| Self::project_name(c))
            .collect();
        if build_order2 != self.expected {
            return Err(format!(
                "assert.DeepEqual(buildOrder2, b.expected) failed: got {build_order2:?}, want {:?}",
                self.expected
            ));
        }

        let mut orchestrator = build("--watch");
        orchestrator.generate_graph(None);
        let build_order3: Vec<String> = orchestrator
            .order()
            .iter()
            .map(|c| Self::project_name(c))
            .collect();
        verify_deps(&orchestrator, &build_order3, true)
    }
}

// ---------------------------------------------------------------------------
// execute/tsc/extendedconfigcache_test.go
// ---------------------------------------------------------------------------

// Go: execute/tsc/extendedconfigcache_test.go:12 testParseConfigHost
struct TestParseConfigHost {
    fs: Rc<dyn Fs>,
    cwd: String,
}

impl ParseConfigHost for TestParseConfigHost {
    fn fs(&self) -> Rc<dyn Fs> {
        Rc::clone(&self.fs)
    }
    fn get_current_directory(&self) -> String {
        self.cwd.clone()
    }
}

/// Go `tsoptions.GetParsedCommandLineOfConfigFile("/project/tsconfig.json",
/// nil, nil, host, &tsc.ExtendedConfigCache{})` over a map file system with
/// `files`.
// PORT: Go `tsc.ExtendedConfigCache` is `TscExtendedConfigCache` in
// execute/build/host.rs.
fn parse_with_cache(files: &[(&str, &str)]) -> Option<ParsedCommandLine> {
    let fs = vfstest::from_map(
        files.iter().copied(),
        false, /*useCaseSensitiveFileNames*/
    );
    let host = TestParseConfigHost {
        fs,
        cwd: "/project".to_string(),
    };
    let cache = TscExtendedConfigCache::default();

    let (cmd, _) = get_parsed_command_line_of_config_file(
        "/project/tsconfig.json",
        None,
        None,
        &host,
        Some(&cache),
    );
    cmd
}

// Go: execute/tsc/extendedconfigcache_test.go:110 assertHasCircularityDiagnostic
fn assert_has_circularity_diagnostic(cmd: &ParsedCommandLine) -> Result<(), String> {
    if cmd.errors.iter().any(|d| d.code == 18000) {
        return Ok(());
    }
    Err(format!(
        "expected circularity diagnostic (code 18000), but none was found; errors: {:?}",
        cmd.errors.iter().map(|d| d.code).collect::<Vec<_>>()
    ))
}

// Go: execute/tsc/extendedconfigcache_test.go:20 TestExtendedConfigCacheExtendsCircularity
#[test]
fn test_extended_config_cache_extends_circularity() {
    let mut t = Subtests::new("TestExtendedConfigCacheExtendsCircularity");

    t.run("self-referencing extends", || {
        // Regression test: a tsconfig extends cycle should produce an error,
        // not a deadlock when using the tsc ExtendedConfigCache.
        let cmd = parse_with_cache(&[
            ("/project/tsconfig.json", r#"{"extends": "./base.json"}"#),
            ("/project/base.json", r#"{"extends": "./base.json"}"#),
            ("/project/main.ts", "// Hello World!"),
        ])
        .ok_or("expected non-nil ParsedCommandLine")?;
        assert_has_circularity_diagnostic(&cmd)
    });

    t.run("mutual extends cycle", || {
        // Two config files that extend each other.
        let cmd = parse_with_cache(&[
            ("/project/tsconfig.json", r#"{"extends": "./other.json"}"#),
            ("/project/other.json", r#"{"extends": "./tsconfig.json"}"#),
            ("/project/main.ts", "// Hello World!"),
        ])
        .ok_or("expected non-nil ParsedCommandLine")?;
        assert_has_circularity_diagnostic(&cmd)
    });

    t.run("case-insensitive self-referencing extends", || {
        // On a case-insensitive FS, ./Base.json and ./base.json resolve to the same
        // cache entry. The cycle check must use canonical paths to avoid deadlock.
        let cmd = parse_with_cache(&[
            ("/project/tsconfig.json", r#"{"extends": "./Base.json"}"#),
            ("/project/base.json", r#"{"extends": "./base.json"}"#),
            ("/project/main.ts", "// Hello World!"),
        ])
        .ok_or("expected non-nil ParsedCommandLine")?;
        assert_has_circularity_diagnostic(&cmd)
    });

    t.finish();
}

// Go: execute/tsc/extendedconfigcache_test.go:89 TestExtendedConfigCacheNullExtendsDoesNotPanic
#[test]
fn test_extended_config_cache_null_extends_does_not_panic() {
    let cmd = parse_with_cache(&[
        ("/project/tsconfig.json", r#"{"extends": null}"#),
        ("/project/main.ts", "// Hello World!"),
    ])
    .expect("expected non-nil ParsedCommandLine");
    assert!(
        !cmd.errors.is_empty(),
        "expected diagnostics for invalid null extends"
    );
}
