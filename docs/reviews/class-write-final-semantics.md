# Class-write final semantic review

Verdict: scoped approval for `4305d16d` and `32ad57ab` on the preserved
`3d5f0d0a` composition with the original review probes. No new finding remains
within this scope. The repaired cold-planning and diagnostic contracts match
the pinned Go cases checked here.

## Reviewed composition

- Preserved base: `3d5f0d0a6a11674b50e79b53dac322c102b06e17`.
- Original review: `aacec767b970002bbf1a4e61fdc5f366143aa6ed`.
- Exact review import: `79180480ecb804eb53b0b234d0907fefbfe4a5d5`.
- Cold-parameter repair: `4305d16d7f3bd9b4c9a896db3b864aa11722c118`.
- Diagnostic repair: `32ad57abd3db382ffe90b52cfa4ee794ac0c7b98`.
- Go reference: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

This review owns only new tests and this report. Production code is unchanged.
Relative to the preserved base, the repairs change only `source.rs` in
production. The class provider, kernel, context, source properties, source flow,
relater, object diagnostics, and super selection have no diff from that base.

The imported probe file and historical report exactly match `aacec767` at the
import commit. The repair changes only the old cold-history control. Its
TypeScript inputs are unchanged. The other 13 probes, their expected Go
diagnostics, the historical report, and all 23 public class/super tests remain
unchanged. The historical hold report describes the old candidate, not these
repairs.

## Saved-control replay

The author's worktree is clean at `32ad57ab`. Its combined log records 3,731
unit passes, 14 focused passes, and 23 public class/super passes. The saved
binaries match the logged paths and postdate the final `source.rs` edit.

This review replayed the unchanged binaries under a 16 GiB memory cap and a
16 MiB Rust stack. Strict SHA256 checks ran before and after the replay. The
three selected unit controls, all 14 review probes, and all 23 public tests
passed. No Cargo build or broad unit rerun was needed for this replay.

The selected units are the original property-flow control, the new poisoned
optional-parameter control, and the preserved cold-super-receiver no-write
control. The public replay includes the exact base-target and derived-this
checks and the write/super composition control.

Saved binary SHA256 values:

| Binary | SHA256 |
| --- | --- |
| `ts_checker-b21086c70c0cfd32` | `1c7edc6613a068a99bfec1c0c8f79a69ea1af3601586d70e00776ecb529d57cd` |
| `review_constructor_writes-710134db922d9943` | `50434c12ecc313e4e6b14c94939ecd2f5798a2d76e679c8cd77b7b7544c804c5` |
| `source_class_bodies-bc287ad3e02fd49b` | `dad41f693439f910cdd453a4ccd1ee6bb39d35b5fce260ff04adcad286b19b21` |
| `source_class_polymorphic_super-31eca02557d0e998` | `224995083828586c139923c91f1d94774fd9a4acbeadfc983d45f15214e146c5` |
| `source_class_writes-1f711a904396d470` | `abf06c67cdf9c9aa09426f72703f7eaa19d26817ab7440a4231b1df4a7f53093` |

Source SHA256 values at the reviewed composition:

| File | SHA256 |
| --- | --- |
| `source.rs` | `c4c36f2ae76bebff086c4ff87a5f5f7db0df014e2aba855194b8fd69e201ef8d` |
| Original `review_constructor_writes.rs` at `aacec767` | `fda5c5aefd081690cc028d01619b2e858200e1c9a29374a21c7313d12d848ed1` |
| Repaired `review_constructor_writes.rs` | `16d49348ffbe23b2c2f9db12be960c6883dbba0c2ee3ece99055d6196fef1eee` |
| `source_class_bodies.rs` | `5dade3f9085a658ec48e1f13555d52590e79f8e96512bde954692c3c3bca4928` |
| `source_class_polymorphic_super.rs` | `7dbe6802f49716c7de8bb7ef179dcb1d451d7ec06c290f8620a62cb29f7edb43` |
| `source_class_writes.rs` | `f7f640190f92f7c5aa702bc4745b175a8d25dccfc7de451efe7a57a7f074539d` |

## New Go checks

All 12 new Go cases pass against the clean pinned checkout and cached Go 1.26.5.
The program uses the same pinned `es5.d.ts` as the original review, strict
checking, ES2015, no default library, skipped library checks, and both exact
optional settings. Source files, compiler code, and the checkout are unchanged.

The cold-history cases use a string optional parameter and an unrelated
`number | undefined` annotation. They cover a cold check, an earlier unrelated
query, no property write, an undefined property write, and both optional modes.
All have zero diagnostics. The local parameter stays `string | undefined`.
The member read is `string | undefined` without the write and `undefined` after
the write.

The diagnostic cases retain exact start and end positions, message chains,
related-information counts, API order, and repeated results. For a boolean
optional source written to a number optional field, Go reports `boolean` in
the rejected-member detail under ordinary optional checking. With exact
optional checking, the first rejected member is `undefined`. An unrelated
earlier assignment diagnostic remains first in both modes.

For a scalar string source, Go displays target `number` while the actual write
target remains `number | undefined` in ordinary mode. In exact optional mode,
the actual target is `number`. Invalid writes leave the later member read at
`number | undefined` in both modes.

Relevant pinned code is `internal/checker/relater.go:2645` for nullable-target
reduction and `reportRelationError` at line 4744 for literal display
generalization. Rust's shared formatter already has that literal rule. The new
probe checks the class reporter's use of it. The review does not replace
assignment relations or the actual field target with display types.

## New Rust gate

The new tests are in `crates/ts_checker/tests/review_class_write_final_semantics.rs`.
Session 75156 exited zero after a 37.87-second build. Both tests passed in
0.09 seconds, with no ignored or filtered tests. All four diagnostic cases and
all eight cold-history cases executed and matched Go.

The checks cover actual assignment source and target types, declared primitive
field types, codes, full ranges, complete messages and details, absent related
information, raw order, and local parameter identity. Two forced warm checks
per case preserved diagnostics, allocation counts, node links, symbol links,
watched value links, and check flags. No test or production source edit followed
the run.

New review artifact SHA256 values:

| Artifact | SHA256 |
| --- | --- |
| `review_class_write_final_semantics.rs` | `79a77a2fd2d36e2f5b6bc3ad0a399a3eed8c81dd21957fafb4ef5b1381dcebf5` |
| `class_write_final_semantics_go_test.go` | `1301b02e3c60602c13f6f724f61f9493cf08774064ce563d110fca240aa872f2` |
| `review_class_write_final_semantics-2698aec1ee4465e6` | `4d4f84095ef30a6f855228848a5cbb6eb7e8c42ca84e1f42f4029c37cded43c4` |

The gate uses `scripts/run-cargo-capped.sh`, locked offline Cargo, an absolute
manifest, 16 GiB memory, a 16 MiB Rust stack, and the private target
`target/worktrees/wave146-class-write-final-semantics`. TMPDIR and the shared
lock were unchanged. The source stayed fixed during the gate, and its hashes
were verified after completion.

Logs use the `/tmp/ts-rust-wave146-class-write-final-semantics-` prefix:

- `replay-final.log`: strict hash verification and 40 passing saved controls.
- `go.log`: 12 passing new Go cases.
- `new-probes.log`: both new Rust tests passed across all 12 cases.

## Limits

The original unsupported declaration and write cases remain separate, including
optional private identifiers and the independent receiver-alias limitation.
This review does not approve root composition, the separate JSDoc diagnostic
API, or constructor positional-index work. Those remain with their assigned
owners. No full workspace or strict Clippy result is claimed.

All owned sessions are collected. Rustfmt, gofmt, and diff checks pass. The
author worktree and frozen Go checkout remain clean.
