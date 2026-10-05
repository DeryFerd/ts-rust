//! Port-only test of the downstream lists of `tsc -b --watch` after config
//! changes (watchcfg1).
//!
//! PORT: Go appends to the `downStream` of a reused task in each new graph
//! (build/orchestrator.go:247 `setupBuildTask`), so the list keeps the
//! downstream tasks of every older graph. In the port those old tasks were
//! an `Rc` cycle with their upstream tasks, and each config change of a
//! downstream project kept its old task for the rest of the session. The
//! port clears the lists before it makes a new graph
//! (`Orchestrator::generate_graph_reusing_old_tasks`), so the list of a
//! reused task holds the tasks of the current graph only. The output does
//! not change (see that function).

use ts_goport::execute::build::orchestrator::Orchestrator;
use ts_goport::fswatch::{Event, EventKind};
use ts_goport::gostd::context;

use crate::support::child::{command_line_in_process, new_in_process_test_sys, run_test_in_child};
use crate::support::runner::TscInput;

const PROJECT: &str = "/home/src/workspaces/project";

#[test]
fn config_changes_leave_one_downstream_task() {
    run_test_in_child(
        "tsctests::watch_build_downstream::config_changes_leave_one_downstream_task",
        || {
            let file = |name: &str, text: &str| (format!("{PROJECT}/{name}"), text.into());
            let app_config = |extra: &str| {
                format!(
                    r#"{{"compilerOptions":{{"composite":true{extra}}},"files":["b.ts"],"references":[{{"path":"../core"}}]}}"#
                )
            };
            let input = TscInput {
                files: [
                    file(
                        "core/tsconfig.json",
                        r#"{"compilerOptions":{"composite":true},"files":["a.ts"]}"#,
                    ),
                    file("core/a.ts", "export const a = 1;\n"),
                    file("app/tsconfig.json", &app_config("")),
                    file(
                        "app/b.ts",
                        "import { a } from \"../core/a\";\nexport const b = a;\n",
                    ),
                ]
                .into_iter()
                .collect(),
                ..Default::default()
            };
            let sys = new_in_process_test_sys(&input);
            let args = ["--build", "--watch", "app"].map(String::from);
            let result = command_line_in_process(&context::background(), &sys, &args);
            let mut w = result
                .watcher
                .expect("expected Watcher to be non-nil in watch mode");
            let fs = sys.fs_from_file_map();
            for (i, extra) in [r#","newLine":"lf""#, "", r#","newLine":"lf""#]
                .into_iter()
                .enumerate()
            {
                sys.set_output_bytes(Vec::new());
                let _ = fs.write_file(&format!("{PROJECT}/app/tsconfig.json"), &app_config(extra));
                sys.mock_watch_backend().send_events(vec![Event {
                    kind: EventKind::Update,
                    path: format!("{PROJECT}/app/tsconfig.json"),
                }]);
                w.do_cycle();
                let out = sys.output_text();
                assert!(
                    out.contains("Found 0 errors. Watching for file changes."),
                    "config change {i} builds again: {out}"
                );
            }
            let orchestrator = w
                .as_any()
                .downcast_ref::<Orchestrator>()
                .expect("the -b watcher is an Orchestrator");
            let downstream = orchestrator.downstream(&format!("{PROJECT}/core/tsconfig.json"));
            assert_eq!(
                downstream.len(),
                1,
                "core lists the app task of the current graph only: {downstream:?}"
            );
        },
    );
}
