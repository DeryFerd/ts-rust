# goport measurement scripts

Moved from `/tmp/port`, where a reboot would erase them. They measure the `ts_goport`
candidate in `target/worktrees/checker-port` against the pinned `tsgo-oracle`.

- `gate.sh <label>`: full regression gate. Run it before any goport merge.
- `bound2.sh <round>`: bound parity run with a manifest (Query, Hono, error copies, sweeps, emit).
- `measure.sh`, `measure-extra.sh`, `sweep.sh`: the project comparisons that `bound2.sh` and `gate.sh` use.
- `perf.sh <bin> <label>`: median wall time and peak RSS on Query, Hono, zod and effect.
- `fp.py <checkout>`: the source fingerprint recorded in the saved state.

Revision bindings made before this move pin `/tmp/port/fp.py`. That copy is identical.

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
