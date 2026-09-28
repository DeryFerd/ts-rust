# goport measurement scripts

Moved from `/tmp/port`, where a reboot would erase them. They measure the `ts_goport`
candidate in `target/worktrees/checker-port` against the pinned `tsgo-oracle`.

- `gate.sh <label>`: full regression gate. Run it before any goport merge.
- `bound2.sh <round>`: bound parity run with a manifest (Query, Hono, error copies, sweeps, emit).
- `measure.sh`, `measure-extra.sh`, `sweep.sh`: the project comparisons that `bound2.sh` and `gate.sh` use.
- `perf.sh <bin> <label>`: median wall time and peak RSS on Query, Hono, zod and effect.
- `fp.py <checkout>`: the source fingerprint recorded in the saved state.
- `ls_edit_bench.py --rust BIN`: editor sessions (typing, error then fix, VS Code request mix, imports,
  200-edit session) on Query core, Hono and effect against Go. RSS, edit latency and answers; exit 1
  when Rust is over the limits in its docstring.

Revision bindings made before this move pin `/tmp/port/fp.py`. That copy is identical.

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
  200-edit long session). With Go and two Rust builds it takes about 3 minutes, plus the wait for the lock.
- One session again: `--projects hono --scenarios long`. New limits on an old run: `--recheck --out DIR`.

How to read the result:

- Exit 0: every limit passes. Exit 1: a limit failed. Exit 2: usage error, or a Go session failed.
- `report.md` has one row per project, scenario and side, then "Failed limits" with the value and the
  limit for each failure. `result.json` has every edit.
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
- Known state on 2026-09-27: R122, R123 and the branches on R123 fail 5 sessions on memory:
  imports on Query core and effect (rss), and long on all three projects (growth and rss).
  Go against Go passes all 15.

Not covered: think time. The Rust server runs idle work (the auto-import warm) only after 50 ms
with no message (`IDLE_QUIET_PERIOD` in `lsp/server.rs`). This tool sends the next edit at once, so
that work never runs. The leak that editors saw (R122 and R123 add about 155 MiB per edit with 60
to 250 ms between edits, 6.3 to 6.5 GiB after 40 Query edits) does not show here. Until this tool
has a pause between edits, also run the lsmem repro with the build added to its `CONFIGS`:
`target/continuation-r97-goport/lsmem/repro/builds-allocator/repro.py --scenario append --pause-ms 150`.

## Remote runners

`remote.sh` copies binaries and scripts to a remote host, runs a command there in the repo root
and fetches the results. zbook builds. Each host keeps a mirror at zbook's absolute paths
(manifests and setup notes in `target/continuation-r97-goport/remote/`).

- alvin, cup2: cloud hosts for gates, corpus suites, sweeps and oracle checks.
- dbook (ssh host `dbook-lan`): LAN host with zbook's CPU (Ryzen AI Max+ 395, 32 threads) but
  only 26 GB RAM. It runs gates and checks, and quiet timing on zbook-class hardware when no gate
  runs. Every dbook job takes the same lock on zbook, timing included, so the two never overlap:
  `flock /tmp/goport-remote-dbook.lock scripts/goport/remote.sh run dbook-lan <command>`.
  dbook is on the same LAN as zbook: always use `dbook-lan` (dbook.local), never the Tailscale
  name `dbook`. `remote.sh` maps `dbook` to `dbook-lan`.
