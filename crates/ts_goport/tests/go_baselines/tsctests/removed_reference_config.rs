//! Port-only test of `tsc -b` after the config file of a reference is gone
//! (followups18 item 3).
//!
//! PORT: no Go counterpart. The upstream task has no config, so its check
//! never loads a build info, and the downstream check reads
//! `upstream.buildInfoEntry.dtsTime` with a nil entry
//! (build/buildtask.go:889 `getLatestChangedDtsMTime`). Go N panics with a
//! nil dereference and exits 2. The port panicked with a port assert and
//! exited 70.

use std::panic::AssertUnwindSafe;

use ts_goport::execute::tsc::ExitStatus;
use ts_goport::gostd::context;

use crate::support::child::{command_line_in_process, new_in_process_test_sys, run_test_in_child};
use crate::support::runner::TscInput;

const PROJECT: &str = "/home/src/workspaces/project";

#[test]
fn a_removed_reference_config_is_a_go_nil_dereference() {
    run_test_in_child(
        "tsctests::removed_reference_config::a_removed_reference_config_is_a_go_nil_dereference",
        || {
            let file = |name: &str, text: &str| (format!("{PROJECT}/{name}"), text.into());
            let input = TscInput {
                files: [
                    file(
                        "a/tsconfig.json",
                        r#"{"compilerOptions":{"composite":true},"files":["a.ts"],"references":[{"path":"../b"}]}"#,
                    ),
                    file("a/a.ts", "import { b } from \"../b/b\";\nexport const a = b;\n"),
                    file(
                        "b/tsconfig.json",
                        r#"{"compilerOptions":{"composite":true},"files":["b.ts"]}"#,
                    ),
                    file("b/b.ts", "export const b = 1;\n"),
                ]
                .into_iter()
                .collect(),
                ..Default::default()
            };
            let sys = new_in_process_test_sys(&input);
            let args = |builders: &str| -> Vec<String> {
                ["-b", "a", "--builders", builders]
                    .map(String::from)
                    .to_vec()
            };
            let result = command_line_in_process(&context::background(), &sys, &args("4"));
            assert_eq!(result.status, ExitStatus::Success);
            sys.remove_no_error(&format!("{PROJECT}/b/tsconfig.json"));
            for builders in ["4", "1"] {
                let payload = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    command_line_in_process(&context::background(), &sys, &args(builders))
                }))
                .err()
                .unwrap_or_else(|| panic!("--builders {builders}: no panic"));
                assert_eq!(
                    ts_goport::ipc::conn::recovered_value(payload.as_ref()),
                    "runtime error: invalid memory address or nil pointer dereference",
                    "--builders {builders}"
                );
            }
        },
    );
}
