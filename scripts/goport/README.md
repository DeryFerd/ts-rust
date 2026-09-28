# goport measurement scripts

Moved from `/tmp/port`, where a reboot would erase them. They measure the `ts_goport`
candidate in `target/worktrees/checker-port` against the pinned `tsgo-oracle`.

- `gate.sh <label>`: full regression gate. Run it before any goport merge.
- `bound2.sh <round>`: bound parity run with a manifest (Query, Hono, error copies, sweeps, emit).
- `measure.sh`, `measure-extra.sh`, `sweep.sh`: the project comparisons that `bound2.sh` and `gate.sh` use.
- `perf.sh <label> <bin>...`: median of 3 wall time and peak RSS on Query, Hono, zod and effect,
  runs interleaved across the binaries. It refuses to start above load 1.5 (`PERF_WAIT=1` waits
  for a quiet host). zbook is rarely quiet: run it on dbook-lan or mini-abf9.
- `roster_fp.py <checkout>`: fingerprint of every file outside `crates/ts_goport`. Equal values
  allow the goport-only roster carry-forward (docs/typechecker-accountability.md).
- `facts [section...]`: in one call, the paths and versions agents look up before their first edit: main
  against origin, the accepted revision (commit, bins checked against the gate manifest, gate, evidence),
  the Go pins with checkouts and oracles, the project tsconfigs, the newest lane bins, active `goport-*`
  worktrees and the last gates. Local reads only, about 2 s.
- `wfstatus [--all]`: one line per workflow of the newest ts-rust session (state, agents done,
  running labels, age). `wfstatus <run-id>` prints that run's agent results. Use it instead of
  parsing `journal.jsonl` by hand.
- `prune-worktrees.py`: lists stale worktrees and merged branches. `--apply` removes them.
- `fp.py <checkout>`: the source fingerprint recorded in the saved state.
- `gate.sh` also runs an editor stage (memory and answers limits of `ls_edit_bench.py` on Query
  core and Hono), so `--bins` must hold `tsgo` too. Build the bins with `--release --bins`.
- `ls_edit_bench.py --rust BIN`: editor sessions (typing, error then fix, VS Code request mix, imports,
  200-edit session, and typing and error then fix with a 150 ms pause between edits) on Query core,
  Hono and effect against Go. RSS, edit latency and answers; exit 1 when Rust is over the limits in
  its docstring.

- `buildbench.sh`, `buildbench-plan.sh`, `buildbench-remote.sh`: timed `ts_goport` builds on a quiet
  host under its lock (see "Build toolchain" below). `bin-identity.sh <out> <bins-a> <bins-b>`:
  byte-for-byte output of two bin dirs (`tsgo -p` with emit and `goport -p`) on Query core, Hono,
  zod and effect.

Revision bindings made before this move pin `/tmp/port/fp.py`. That copy is identical.
`tmp-port.sh restore` puts back the legacy `/tmp/port` files and the cargo pool runner after a
reboot or a tmpfiles cleanup (a login does it too). Put new tools here, never in `/tmp`.

## Build toolchain

`scripts/run-cargo-capped.sh` runs edit-loop commands (`build`, `check`, `test`, `run`, `bench`)
with the pinned `nightly-2026-06-17` and `-Zthreads=8` (the job count, at most 8), and builds
`ts_goport` incrementally. Release `-p ts_goport --bins` on dbook-lan, 16 jobs, sccache off
(`target/continuation-r97-goport/buildspeed/bench.md`):

| build | 1.93.0 (before) | nightly -Zthreads=8 | + incremental ts_goport (default) |
|---|---|---|---|
| clean | 215 s | 84 s | 84 s |
| touch one file | 75 s | 43 s | 7 s |
| one-line edit | 75 s | 43 s | 32 s |

- Incremental is the edit-loop gain: a one-line edit also takes 32 s on 1.93.0 with it. The nightly
  gains are in clean builds, large edits (merges, rebases, branch switches), `check` and `test`.
- Output does not change. `tsgo -p` with emit and `goport -p` on Query core, Hono, zod and effect
  are byte-equal to 1.93.0 bins, the quick gate is equal item for item, and `perf.sh` run time is
  equal within 1%.
- 1.93.0 stays for `--profile goport` (shipped and timing bins: `build-release.sh`, `build-pgo.sh`),
  `fmt`, `clippy`, any command with `RUSTUP_TOOLCHAIN` or a `+toolchain` argument, and the protected
  cargo roster (its pool runner calls cargo directly). For timing, build every side with the same
  toolchain.
- `TS_CARGO_NIGHTLY=0` uses the default toolchain. `TS_CARGO_INCREMENTAL=0` turns incremental off;
  `1` turns it on for every workspace crate. After an internal compiler error, build again with both
  set to 0 and report the error.
- A host without the toolchain uses the default one and prints a note. Install it with
  `rustup toolchain install nightly-2026-06-17 --profile minimal`.
- The first build in each target dir after the switch rebuilds every crate once. The incremental
  cache of ts_goport takes about 1.7 GB per target dir. sccache does not cache an incremental crate, so only
  `ts_goport` is incremental: sccache still caches every other crate.
- To measure a build change, run the `buildbench-plan.sh` session `defaults` before and after it on
  one host: `buildbench-remote.sh dbook-lan defaults` from the worktree under test (the `setup`
  session copies its source to the host first). `buildbench-report.py <runs-dir>...` makes the table.

Revision evidence is the exception: `candidate.sh side` builds its release bins with `TS_CARGO_NIGHTLY=0 TS_CARGO_INCREMENTAL=0`, so the gate, bound runs and oracles test bins from the shipped toolchain with no incremental cache (the evidence key records the toolchain).

## Editor sessions: `ls_edit_bench.py`

Our other checks measure startup and watch mode. This one measures a language server during edits,
against Go, with the same messages on both sides.

Run it on zbook:

- for every integration candidate, before it merges
- for every change to `crates/ts_goport/src/{ls,lsp,project,api}/`, `program.rs` or the allocator
  (jemalloc features, `set_malloc_tunables` in `src/bin/tsgo.rs`)

```
flock /tmp/goport-lsguard.lock scripts/goport/ls_edit_bench.py \
    --rust cand=/abs/path/to/candidate/tsgo --rust base=/abs/path/to/main/tsgo \
    --out target/continuation-r97-goport/lsguard/<label>
```

- Use absolute binary paths. Each server starts in its project directory.
- Put the main build in the same run (`--rust base=...`). Then load from other agents affects both
  Rust sides equally.
- Other upstream pin: `GOPORT_PIN=<key> scripts/upstream/pin.py exec -- scripts/goport/ls_edit_bench.py ...`.
- One pass is 3 projects (Query core, Hono, effect) x 5 scenarios (typing, errfix, mix, imports, and a
  200-edit long session), plus typing-paced and errfix-paced on Query core and Hono. With Go and two
  Rust builds it takes about 4 to 5 minutes, plus the wait for the lock.
- One session again: `--projects hono --scenarios long`. New limits on an old run: `--recheck --out DIR`.
- Paced scenarios on effect: `--projects effect --scenarios typing-paced,errfix-paced` (not in the
  default pass, to keep it short).

Think time (pace): the pause after each edit's answers, before the next edit. The client sends
nothing then, except answers to server requests. The Rust server runs idle work (the auto-import
warm) only after 50 ms with no message (`IDLE_QUIET_PERIOD` in `lsp/server.rs`). Editors pause
between keystrokes, so an edit can arrive while that work runs.

- typing-paced and errfix-paced: typing and errfix with a 150 ms pause. They catch the leak that
  editors hit: R123 on Query core goes to 6.4 GiB after 40 edits, with a 185 ms median edit (Go 266
  MiB, 17 ms).
- `--pace-ms N`: the same pause for the other scenarios (default 0).
- `--sweep [MS,...]`: for diagnosis. It runs each scenario once per pause (default 0, 30, 80, 150 and
  300 ms). Defaults: Query core, typing and errfix, 20 edits. `--projects`, `--scenarios` and
  `--edits` change them. R123: 0 and 30 ms pass, 80 and 150 ms add about 155 MiB per edit, 300 ms
  passes (the warm finishes before the next edit).

How to read the result:

- Exit 0: every limit passes. Exit 1: a limit failed. Exit 2: usage error, or a Go session failed.
- `report.md` has one row per project, scenario, pace and side, then "Failed limits" with the value
  and the limit for each failure. `result.json` has every edit.
- Limits (Rust against the Go of the same run):

  | limit | Rust must be at or below |
  |---|---|
  | rss | RSS added by the edits: 2 x Go + 256 MiB |
  | growth | RSS slope over the second half, long session only: 2 x Go + 1 MiB per edit |
  | editMedian | median didChange-to-diagnostics time: 1.5 x Go + 5 ms |
  | editP95 | p95 of the same: 2 x Go + 20 ms |
  | roundMedian | median time until the last answer of the burst: 2 x Go + 10 ms |
  | answers | no error, crash, timeout or RSS-cap kill where Go answered |

- rss and growth do not change much with load. The latency limits do. If only a latency limit fails,
  run that session again before you trust it.
- Answer differences are listed but not judged. Hono completion `autoImport/moduleSpecifier`
  (Go `"."`, Rust `"./adapter/bun"`) also differs between two Go runs. Look at any other difference.
- Known state on 2026-09-27: R122, R123 and the branches on R123 fail 5 unpaced sessions on memory:
  imports on Query core and effect (rss), and long on all three projects (growth and rss).
  Go against Go passes all 15. R123 also fails typing-paced and errfix-paced on Query core (rss and
  all latency limits); it passes them on Hono. Go against Go passes all 4 paced sessions.

## Remote runners

`remote.sh` copies binaries and scripts to a remote host, runs a command there in the repo root and
fetches the results. zbook builds. Each host keeps a mirror at zbook's absolute paths (manifests and
setup notes in `target/continuation-r97-goport/remote/`). The header of `remote.sh` has the usage.

| command | use | lock |
|---|---|---|
| `status [host...]` | per host: load, free RAM, busiest process, and the zbook lock (holder, age, waiters) | none |
| `look <host> <cmd>` | a quick look: logs, files, hashes, tools. Same route and paths as `run`, 120 s limit | none |
| `run <host\|auto> <cmd>` | a job in the repo root. stdin passes through: `run <host> bash -s <<'EOF'` | holds it |
| `job <host\|auto> <cmd>` | a zbook script that does several steps on `$REMOTE_HOST` (sync, run, fetch) | holds it for the whole script |
| `sync-bins`, `sync-scripts`, `sync-pin`, `push` | copy to the host (`all`: every host at once) | none |
| `fetch <host> <dir>` | copy results back; never replaces a file | none |

Locks:

- `run` and `job` take the zbook lock `/tmp/goport-remote-<host>.lock` (dbook-lan: `goport-remote-dbook.lock`)
  and wait for it. While one waits, it prints the holder.
- A caller that holds the lock passes the open lock file on to its children. `run` finds it in
  `/proc/$$/fd` and does not lock again. So `flock /tmp/goport-remote-<host>.lock remote.sh run <host> ...`
  and scripts that do `exec 9>LOCK; flock 9` still work. The flock wrapper is optional now.
- A script under `job` must not take the lock itself: it would wait for its own lock (`status` then shows
  the job as holder with 1 waiting).
- The lock does not pass through `systemd-run`. Take it inside the unit, not around `systemd-run`.
- `auto` takes the first host in order whose lock is free, whose load is under half its cores and whose
  mirror paths are right. When no host is free, it checks again every 30 s.
- Until 2026-09-28, `run auto` released its lock when the command started (ssh closes inherited file
  descriptors), and `run <host>` took no lock. `run` now keeps its shell alive as the lock holder.

Do not use raw `ssh` or `rsync`. `look` reaches the host over the right route (the minis by their LAN
names) with zbook's paths (alvin through its `zbook-paths` wrapper, dbook with `HOME=/home/theo`).
`pin.py sync <host>` uses the ssh config route, which is Tailscale for the minis: use `remote.sh sync-pin`.

Root: name a host in an agent prompt only for timing that needs zbook-class hardware (dbook-lan). Other
jobs use `auto`. Record each package install or other host change in
`target/continuation-r97-goport/remote/<host>-setup.md`.

- alvin, cup2: cloud hosts for gates, corpus suites, sweeps and oracle checks. alvin has no sudo. cup2
  has `sudo -n` and `/usr/local/sbin/fleet-pkg-install`.
- dbook (ssh host `dbook-lan`): LAN host with zbook's CPU (Ryzen AI Max+ 395, 32 threads) but
  only 26 GB RAM. It runs gates and checks, and quiet timing on zbook-class hardware when no gate
  runs. Every dbook job takes the same lock, timing included, so the two never overlap.
  dbook is on the same LAN as zbook: always use `dbook-lan` (dbook.local), never the Tailscale
  name `dbook`. `remote.sh` maps `dbook` to `dbook-lan`.
- mini-743d (Ryzen 7 8845HS) and mini-abf9 (ssh alias `mini-abf9-1`, Ryzen 7 255): LAN minis with
  16 threads and 28 GB RAM each. They run gates and checks. Both are wired since 2026-09-28
  (mini-743d about 215 MB/s over ssh), so both are also good for quiet timing and the editor
  benchmark (`ls_edit_bench.py`, every side on the same host). Every job takes the host's own lock,
  timing included. `remote.sh` always reaches them by the LAN names mini-743d.local and
  mini-abf9.local, never Tailscale. It maps `mini-abf9-1` and the `-ts` names to `mini-abf9` and
  `mini-743d`.
- dbook-lan and the minis: `sudo -n`, perf_event_paranoid 4 (use `sudo perf`), THP madvise, and
  perf, bpftrace and strace installed.
