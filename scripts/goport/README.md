# goport measurement scripts

Moved from `/tmp/port`, where a reboot would erase them. They measure the `ts_goport`
candidate in `target/worktrees/checker-port` against the pinned `tsgo-oracle`.

- `gate.sh <label>`: full regression gate. Run it before any goport merge.
- `bound2.sh <round>`: bound parity run with a manifest (Query, Hono, error copies, sweeps, emit).
- `measure.sh`, `measure-extra.sh`, `sweep.sh`: the project comparisons that `bound2.sh` and `gate.sh` use.
- `perf.sh <label> <bin>...`: median of 3 wall time and peak RSS on Query, Hono, zod and effect,
  runs interleaved across the binaries. It refuses to start above load 1.5 (`PERF_WAIT=1` waits
  for a quiet host). zbook is rarely quiet: run it on dbook-lan or mini-abf9.
- `facts [section...]`: in one call, the paths and versions agents look up before their first edit: main
  against origin, the accepted revision (commit, bins checked against the gate manifest, gate, evidence),
  the Go pins with checkouts and oracles, the project tsconfigs, the newest lane bins, active `goport-*`
  worktrees and the last gates. Local reads only, about 2 s.
- `wfstatus [--all]`: one line per workflow of the newest ts-rust session (state, agents done,
  running labels, age). `wfstatus <run-id>` prints that run's agent results. Use it instead of
  parsing `journal.jsonl` by hand.
- `prune-worktrees.py`: lists stale worktrees and merged branches. `--apply` removes them.
- `fp.py <checkout>`: the source fingerprint recorded in the saved state. `fpcommit.py <checkout> <commit>`
  gives the same value for the checkout as it was at a commit.
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
`tmp-port.sh restore` puts back the legacy `/tmp/port` files after a reboot or a tmpfiles cleanup
(a login does it too). It stays after the legacy roster: the sweep step of `scripts/upstream/rerecord.sh`
runs it first (the oracle sweeps write their build info under `/tmp/port`), and the runners in
`compat/p5-corpus` and `typesyms/scale` call `/tmp/port/treehash.py`. Put new tools here, never in `/tmp`.

## Revision pipeline

The protected set is goport's own tests and the gate items (`docs/typechecker-accountability.md`,
"Protected set"). The base of a candidate is the last accepted revision: its goport test results
(after a legacy batch, `docs/goport-protected/tests-r131.json.gz`), its gate manifest and its LSP
and API oracle results (after a legacy batch, its LSP run and the rule's `apiBaseline` `api-r131`,
an API run of the R131 bins). `open_revision.py --base` prints it. The legacy roster drive is
retired. R132 is the last legacy revision.

1. `candidate.sh check <branch>`: scope and rustfmt of the branch against the checkout
   `target/worktrees/checker-port`. A goport batch may change every path except
   `docs/typechecker-state`, `docs/typechecker-batches`, `target/` and the protected paths
   (`open_revision.py --protected`: the tools, runners, oracles, baseline and rules that judge the
   protected set, `remote.sh`, `UPSTREAM.json` (the oracle and Go checkout of each pin),
   `scripts/run-cargo-capped.sh` (it builds the test and release bins and runs clippy), and every
   script that `gate.sh` and `bound2.sh` run from the repository, which it reads from their text).
   The check fails when the branch changes a protected path since its merge base with `main`,
   unless the batch lists that exact path (with Theo's approval).
2. `candidate.sh open <rev> <branch> --hypothesis TEXT --change TEXT --new-batch <id> --origin TEXT`:
   applies the branch to the checkout in one commit and records the revision (`open_revision.py`,
   the only state write). Leave out `--new-batch` for a later revision of an open batch. Then commit
   the state.
3. `candidate.sh side <rev> [--gate-host HOST] [--name-map TSV]`: in a systemd unit, the release
   bins, the goport tests (`build-goport-tests.sh`, `goport-tests.sh`, then `compare-tests.py`
   against the base results), two bound runs, the full gate and `gate-compare.py` against the base
   gate manifest, the LSP oracle (`lsp_oracle.py`) and the API oracle (`api_oracle.py`, 10
   batteries) each compared per request with the base results (`oracle-compare.py`), and rustfmt
   and clippy on `ts_goport` and the kept crates. Wait for `SIDE DONE`. A pin bump that
   renames Go tests, or a moved test, needs `--name-map` (old suite, old name, new suite, new name,
   then the evidence). A gate run that fails its compare stays in the evidence cache for good, as
   `gate-fail-<gate label>.json` and `gate-compare-fail-<gate label>.json`, and the next `side` runs a
   new gate with a new label (repeat-run rule). Before the verdicts, root records a flake note
   `flake-r<rev>-<name>` for each item of a failed run, naming the item id and the run label, with
   the evidence that the flake rule asks for.
4. `candidate.sh verdict-request <rev>`: the texts for the auditor and the reviewer, with every
   failed gate run of the source and its flake notes, then the accept command. The texts ask for a
   verdict that names the goport tests, gate manifest, name map and gate id map sha256.
5. After two PASS verdicts: `accept_revision.py --revision <rev> --evidence <cache dir> --scope TEXT
   --outcome TEXT`. It refuses a failed gate run that has no flake note for an item. It records the
   evidence and the verdicts (the history row and both verdicts carry `goportTestsSha256`,
   `gateSha256`, `nameMapSha256` and `gateIdMapSha256`), and every gate run of the source in `gateRuns` (each failed
   run with its regressions and flake notes, then the batch gate). It runs
   `check-typechecker-batch.mjs`, and records the acceptance only when the check passes. The check
   also finds each kept `gate-compare-fail-<label>.json`, runs `gate-compare.py` on that run again
   and needs a flake note for each regressed item, so skipping the refusal does not pass.

`gate-compare.py <base manifest> <new manifest>` compares the gate item by item: a base MATCH stays
MATCH, or becomes ALLOWED only by an allow entry (same id, condition and case path) that the base
allow list has too (the single-threaded-equal items change between MATCH and ALLOWED on the same bins).
An ALLOWED item needs a verified allow condition, and a removed id or a new FAIL is a regression. A
corpus id names another case at another Go pin, so each `corpus-diag`, `corpus-emit` and `f1` entry of
`gate-allow.txt` names its case path, and the gate applies it only to the item of that id with that
case path. The open editor
long-growth items (`editor/*/long`) may FAIL only while the batch has the open defect
`editor-long-growth`, only on growth, and only up to a fixed cap per project: query-core 1.58 and
hono 1.28 MiB/edit (`LONG_CAP` in `gate-compare.py`, the one place of the caps; the output lists them
in `longCaps`). Each cap is the highest growth of a good build + 0.15, and it does not follow the base,
so growth cannot add up over revisions. Caps only go down. A batch that fixes some growth can lower
`LONG_CAP` (a protected path the batch lists; the reviewer checks the value). A cap also goes down by
itself to 1.00, the lowest value of the gate's own limit (2 x Go + 1), once the base Rust growth of that
project is at or under 1.00: from then on its item must be MATCH with growth at or under 1.00. A MATCH
at a higher growth does not lower it, because the gate's limit follows Go's slope and the same bins
can then FAIL. A pin bump that renumbers the corpus cases names a gate id map in `batch.gateIdMap`
(`path`, `sha256`; lines of old id, new id and case path). It applies only when the two manifests are
at different upstream pins: a mapped id is the same item, and a base allow entry moves only with its
own case. A line's case path must equal the case path of the base item and of the new item. The map
cannot remove a case. An unmapped base id of a mapped family, or a line that names another case, is a
removed id (format and rules in the `gate-compare.py` docstring). The corpus-emit stage runs the case
paths of `gate-emit-sample.txt`, so a pin that adds cases keeps the same sample under new ids.

`oracle-compare.py <base results dir> <new results dir>` compares two LSP or API oracle results per
request: a base request that was `same` or `oracle_error_same` must stay so. It exits 1 on a lost,
unrun or absent request.

`candidate.sh` runs its local helpers from its own checkout, so a worktree copy can be tried with
`--dry-run` before its merge. The state, `target/` and the host commands (`gate.sh` and the oracles,
which `remote.sh sync-scripts` copies from the main checkout) always use the main checkout.

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
  `fmt`, `clippy`, any command with `RUSTUP_TOOLCHAIN` or a `+toolchain` argument, and the candidate
  evidence builds (see below). For timing, build every side with the same
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

Revision evidence is the exception: `candidate.sh side` builds its release bins and its test bins with `TS_CARGO_NIGHTLY=0 TS_CARGO_INCREMENTAL=0`, so the goport tests, gate, bound runs and oracles test bins from the shipped toolchain with no incremental cache (the evidence key records the toolchain).

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
