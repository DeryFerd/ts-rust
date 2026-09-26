# goport measurement scripts

Moved from `/tmp/port`, where a reboot would erase them. They measure the `ts_goport`
candidate in `target/worktrees/checker-port` against the pinned `tsgo-oracle`.

- `gate.sh <label>`: full regression gate. Run it before any goport merge.
- `bound2.sh <round>`: bound parity run with a manifest (Query, Hono, error copies, sweeps, emit).
- `measure.sh`, `measure-extra.sh`, `sweep.sh`: the project comparisons that `bound2.sh` and `gate.sh` use.
- `perf.sh <bin> <label>`: median wall time and peak RSS on Query, Hono, zod and effect.
- `fp.py <checkout>`: the source fingerprint recorded in the saved state.

Revision bindings made before this move pin `/tmp/port/fp.py`. That copy is identical.
