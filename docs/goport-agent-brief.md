# Workflow agent brief

Root pastes this text at the start of every workflow agent prompt. It replaces about 30 setup calls per agent.

- Edit only the files your prompt gives you. Do not edit `docs/typechecker-state/*`. Do not commit unless your prompt says so. Project inputs under `target/project-inputs*` are read-only.
- Build in your worktree with `scripts/run-cargo-capped.sh build --release -p ts_goport --bins`. Do not set `CARGO_TARGET_DIR`. Use `--profile goport` (fat LTO, 7 to 20 minutes) only when your prompt asks for timing or a release binary.
- Before you report, run `rustfmt --edition 2024` on every `.rs` file you changed. Unformatted code costs a whole new revision.
- You are a subagent. When you end your turn, you stop, and your background jobs stop with you. To wait for a build or a job, block in the foreground with a Bash timeout up to 600000 ms, for example `timeout 590 bash -c 'until grep -qE "^(DONE|FAIL)" LOG; do sleep 10; done'`. Do not poll in 2-minute steps.
- A job that runs longer than 10 minutes goes under `systemd-run --user --collect --unit=<name>`, writes a log, and ends the log with one line: `DONE` or `FAIL rc=<N>`.
- Timing: use `scripts/goport/perf.sh <label> <bin>...` on a quiet host. It refuses above load 1.5. Compare numbers only within one run.
- Remote hosts: use `scripts/goport/remote.sh run auto <command>`. It picks a free, quiet host and holds its lock.
- Go reference: `~/.explore/repos/microsoft__typescript-go` at the pin in `UPSTREAM.json`. `main` is at a newer accepted pin (saved state `batch.upstreamPin.to`, now `52168999f3dc`): for `main`-based work run every Go comparison with `GOPORT_PIN=52168999f3dc` through `scripts/upstream/pin.py exec`, until the default pin is switched. Port notes: `crates/ts_goport/PORTING.md`. Read only the sections you need.
- Remote jobs always hold the host lock: `scripts/goport/remote.sh run auto <command>`. Raw `ssh` is only for a quick look, never for a run.
- Tools in `/tmp` can vanish. Use scripts under `scripts/`.
- Return your findings as text in your final answer. Root saves them.
- If you need a decision, choose the safe option, say which one in your answer and continue.
