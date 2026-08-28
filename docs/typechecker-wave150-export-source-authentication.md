# Export source authentication

Tested source: `e896cbf8`.
Base: `4327f7f3`.
Status: held for two existing class/namespace source failures and the remaining
independent review. No primary promotion or full parity claim.

## Changes

`c91e42d3` checks original binder flags and declarations before selecting a
class or enum export cache. It requires the complete class graph check and
rejects missing caches on checked sources. Untouched declaration files retain
their cold result.

`34b12ce7` moves the class/enum source check before live flags can filter a
name lookup. Only direct `export =` identifier queries enable this check in
the existing name resolver. Ordinary lookup behavior stays unchanged. The
new positive control keeps a local type-only name from hiding a global value.

The imported flag probe is unchanged from `ad02b560`, applied as `e4de7ef3`.
The original invariant imports are `91319c42`, `39dbbdb7`, and `3653e25d`.
`f77dc388` corrects the enum corruption probe to change the actual exports
table. It retains the rejection and restoration checks.

The first new class test used private fields. `a0fda737` and `e896cbf8` correct
its two expressions to `members.shells().instance_type()`. Both public methods
were checked in `classes.rs`. No test expectation changed for those fixes.

## Combined run

Session `29460` completed with exit 101. All 20 requested binaries ran with
`--no-fail-fast`. Compilation took 2 minutes 3 seconds after the shared lock.

| Group | Passed | Failed |
| --- | ---: | ---: |
| Checker units | 3,953 | 2 |
| Compiler units | 258 | 0 |
| Fixture units | 164 | 0 |
| Public controls | 54 | 0 |
| Total | 4,429 | 2 |

No test was ignored or filtered. A binary-qualified test-name comparison
retains all 4,415 prior root tests, and every one still passes. There are
16 added tests: 14 pass and two fail during source checking.

All class and enum cache corruption controls pass. The changed function,
type-alias, interface, and empty flags cannot bypass the class checks. Cold
declarations, lexical scope, declared/value identities, restoration, and
no-write assertions pass. The legitimate type-only shadowing control passes.

## Remaining source failures

The unchanged global class/namespace input fails before artifact queries with
`Variable(NonVariableSymbol)`. The unchanged local class/namespace input fails
with `Variable(NonUniqueDeclaration)`, with two owner declarations. These are
the two source limits already found in the earlier invariant review.

Both positive tests remain enabled. The separate class/namespace source owner
must supply real source support. Their earlier failure does not validate the
later export query path for those sources.

The imported-enum alias repair and its proposed ALIAS guard extension are not
part of this tested source. The independent reviewer still owns final source
authentication review. The semantic smoke, full corpus, modern projects,
Clippy, and all-component composition were not run by this command.

## Evidence

Worktree: `target/agent-worktrees/wave150/root-export-lexical-source-authentication`.
Target: `target/worktrees/wave150-root-export-lexical-source-authentication`.

The target started empty. No workspace artifacts or fingerprints were copied
from another physical source. The source stayed clean and fixed until the
session was collected. Cargo used the root capped runner, absolute manifest,
locked offline dependencies, 16 GiB memory, a 16 MiB Rust stack, the common
lock, and unchanged TMPDIR.

| File | SHA-256 |
| --- | --- |
| `target/wave150-export-lexical-source-combined-tests-2.log` | `7f6bca8a7a50f9de2c0205a02c81d6772c3a860298eead8ea76b73f0473768ac` |
| `artifact_queries.rs` | `66ebd9cf577b07e49cfa177edb6458567f73a4e20444a305dcb5cdf417d1b9be` |
| `name_resolution.rs` | `480e8cceb609671488a7cddab6069ae220b79203665e91bc6bd27461b17e4dbc` |
| `export_equals_final_invariant_tests.rs` | `b2f62877bbb36c77dab1583ca30154a593bc8331c298f56867b504d61a446efa` |

Sessions `78420` and `73351` stopped at the test accessor compile errors. They
ran no tests, and their logs remain preserved. Session `50695` was stopped
while its verified root-owned wrapper still waited in flock, before Cargo
started. Its empty log remains. It supplies no compile or test evidence.
No other worker was stopped. All four root sessions are collected.

Changed-file formatting and the committed-range whitespace check pass. This
report is the only change after the completed run.
