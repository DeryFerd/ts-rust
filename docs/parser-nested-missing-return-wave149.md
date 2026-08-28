# Nested missing return range repair

Status: ready for review. All 324 parser tests and strict Clippy passed.

Reviewed stack: `57e8fd65585bf566c092397980da10d465ec0e36`.
Original repair: `8035fe5b5eecf0651cf153cc2588a1db1c1ef711`.
Worktree: `target/agent-worktrees/wave149/parser-nested-missing-return`.
Branch: `agent/wave149-parser-nested-missing-return`.
Go pin: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

## Change

The review found 12 cases where a nested function or constructor type ended
before its missing type parameter. The return type used the arrow's
before-trivia position. The missing type-parameter name still used the next
token's start.

The repair keeps the existing arrow-return context and gives missing signature
headers the same recovery position:

- A missing type-parameter name uses `current.full_start` only in the existing
  arrow-return context. Its diagnostic and token consumption stay unchanged.
- A type parameter without modifiers starts at its name. A modifier list ends
  at the name's position. Real names keep their original token ranges.
- A missing parameter list uses that same before-trivia position in this
  context. Real parameter lists are unchanged.
- Function and constructor type ends include their own type-parameter list,
  parameter list, and return type. No descendant range is clamped.

The general identifier helpers, outer arrow constructors, and arrow-body
recovery are unchanged. The context still restores before an arrow body.
Ordinary declarations outside arrow-return parsing keep their original ranges.

The first implementation idea reset the context inside nested returns. It was
discarded before compilation. That would move an unparenthesized missing return
past the arrow's existing end. The final source instead keeps the context and
creates missing header nodes at the correct position.

## Exact review probe

The review probe remains unchanged at
`docs/review-probes/parser-missing-return-final-review.rs`, with SHA-256
`178b1ca57a808cd981020e2ca05b00de6e66ec4300c79424f8dca7f67d42c3a6`.
It includes the unchanged original invariant probe, whose SHA-256 remains
`2153a53cfc6820e1aa2bac5a35233dc61a0052b10d0c0b1fa35dbcf0f15ad9aa`.

The new integration test includes those exact files. Their inputs, containment,
UTF-8, parent-link, repeated-child, and following-declaration assertions are
unchanged. The saved failing review log still has SHA-256
`48e0d78e389096399e239b258101949d324760b2c830fb1c46e948184cfedd3c`.
That recorded failure is reused as the baseline. No duplicate baseline build
was started.

Three added tests check exact missing-node and empty-list positions, `const`
modifiers, multibyte comments, enclosing arrow context, and unparenthesized
signatures. The latter cover both missing generic names and missing returns
after valid headers. All original 315 parser controls remain unchanged.

## Preserved ends

The following UTF-8 byte offsets passed for all 12 review cases.
Parenthesized-arrow rows each cover TS and TSX. The generic forms cover TSX.

| Arrow form | Nested signature | Missing header and return position | Outer arrow end | After end |
| --- | --- | ---: | ---: | ---: |
| Parenthesized | `<` | 31 | 46 | 63 |
| Parenthesized | `new <` | 35 | 50 | 67 |
| Parenthesized | `abstract new <` | 44 | 59 | 76 |
| Generic | `<` | 29 | 44 | 61 |
| Generic | `new <` | 33 | 48 | 65 |
| Generic | `abstract new <` | 42 | 57 | 74 |
| Async generic | `<` | 35 | 50 | 67 |
| Async generic | `new <` | 39 | 54 | 71 |
| Async generic | `abstract new <` | 48 | 63 | 80 |

The original bare missing-return arrow ends stay at 28, 26, and 32. The scoped
header change does not widen those arrows.

## Go and sealed evidence

All 44 preserved Go rows and all eight review neighbor rows replayed on their
original files. Their outputs match the saved results byte for byte. The old
helpers were run read-only, with outputs written only to this new worktree.

Two new inputs, in TS and TSX, contain six unparenthesized signature cases each.
The existing Go executable confirms that every arrow ends before its comment
and that the following declaration remains intact. The read-only helper checks
those exact ends. No Go executable was rebuilt.

The Go executable still has SHA-256
`bf6385d18a6579c69b9da6e3dab910135236f82c88d575dc0df633c55fc626a8`.
The checkout is clean at the pin. These checks compare diagnostics and
initializer kinds and ends. They do not compare complete nested AST shapes.
The existing Rust TS1003/TS1005 versus Go TS1139 differences remain outside this
range repair.

All 55 sealed files verified before editing and after the final gates. Their
manifest still has SHA-256
`c7529d4a277f580a9042676817fd4bab2cf1aadd06196f6fd290e228abf986a6`.
No reviewed source, original input, saved log, or sealed file was rewritten.

## Verification

| Check | Session | Result |
| --- | --- | --- |
| Exact review probe and three added controls | `72793` | 9 passed, 0 failed, exit 0 |
| Full parser suite | `83923` | 324 passed, 0 failed, exit 0 |
| Strict all-target parser Clippy | `67148` | Passed with warnings denied, exit 0 |
| Rustfmt on changed source and the new test file | None | Passed |
| Post-gate source and seal checks | None | All recorded hashes and 55 sealed files matched |

The focused run retained all diagnostic codes and ranges printed by the original
12-case review. It also passed the exact missing-name, modifier-list, empty-list,
and return positions in the new controls. The unparenthesized controls passed
for all selected arrow forms. Compilation took 3.22 seconds, and the tests took
0.02 seconds. The session exited and was collected before the final gates were
queued.

The full suite passed 245 unit tests and 79 integration tests. Its 19 result
records contain no failures, ignores, or filters. The total includes all 315
original controls and the nine tests in the new integration target. That target
includes the six unchanged review tests and three additional tests. Three of
the included review tests also run in the original invariant target.

All Cargo uses the root capped runner, an absolute manifest, `--locked --offline`,
16 GiB memory, 16 MiB Rust and process stacks, and unique target
`target/worktrees/wave149-parser-nested-missing-return`. TMPDIR and the common
lock are unchanged. No job was cancelled or bypassed.
This physical worktree started with an empty Cargo target. No workspace
artifacts, fingerprints, reflinks, or hardlinks were copied from another source
tree. The final gates reuse only this worktree's own focused-build target.
No run in this repair used copied artifacts, and no affected run requires
replacement under the empty-target rule.

The final source record is `target/review/final-sources.sha256`. It was recorded
after the context correction, while the queued focused log was still empty.
The earlier uncompiled source record is retained as `preflight-sources.sha256`.
All 11 final source hashes matched after the gates. No Rust source or test changed
after that final record, and both full gates were queued only after the focused
run had completed. All three sessions exited and were collected. No verification
session remains running or queued.

All new outputs and replay helpers are under this worktree's `target/review`.
All five Go replays ran again after the Rust gates. Their 54 final rows match the
fresh results byte for byte. The original 44 rows and eight review rows still
match the reviewed worktree's saved outputs. That worktree is clean at
`57e8fd65585bf566c092397980da10d465ec0e36`, and the Go checkout remains clean at
the pin.

## Final hashes

| File | SHA-256 |
| --- | --- |
| Parser source | `ea44589e9fcb6404185c6590c27d1d42421a77ddd017401fbd08370b70270a73` |
| New integration target | `79f8fd9279e42381b39acbb3783b71b98ee8c791afe6a474895e51cc8cc2a254` |
| Focused log | `b782c8c1e0dde1d725b2c973c17a98e4a022dd90c7bd25c2e128a51b1f6bcf8a` |
| Full parser log | `7adfcb0130bf708109fc6edfc7f32b36367e07b17d947b97e154ccd8a1d84fb5` |
| Strict Clippy log | `4b8ca3a34a0f2bde7565602025af956483d9c343e65859c1e366eb4684efb9c3` |
| Final source record | `43beb85109a0b4f3d81285f2efeacbf2cf452950333d22ddec346a9c014e4038` |
| Original parenthesized Go rows | `6e7695724ea5a046570f7463bf09935a42b9a6f9642c2a9092bc934a9c2c9ee7` |
| Original predicate and comment Go rows | `e77087367aa92f62c924a8ad95c54f2bd2caf9873cb418e4d752d6d04cf61ec8` |
| Original missing-return Go rows | `4be0d97ee2826552e000618e5cdbcbcabce38518547ee700b6255928105ed41c` |
| Eight review neighbor Go rows | `bc4a71a4bc76b7de5ffa97962a3d39c7ddcf0d4d5734c01c38307b21c6b008e8` |
| New unparenthesized Go rows | `0487071976096ac4357b719a5c9dff88dd89c07362f79aaf4d8242e33517e541` |
| Post-gate 55-file verification log | `1909e03a024a1020fa1d5d7bf0ae5c3fbebeaa80318a7c3feda09e896963200f` |

## Limits

No complete parser parity, full AST differential, semantic artifact, checker,
binder, emit, full-project, or performance result is claimed. The existing EOF
and malformed-input diagnostic differences remain separate. The full log still
records five Rust diagnostics for the old missing-outer-arrow TS control and
nine for the old missing-inner-return TS control. These are not relabeled as Go
diagnostic matches.
