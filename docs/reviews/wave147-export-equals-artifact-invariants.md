# Export-equals artifact invariant review

Candidate: `f265222b60340c2a4de8ab8e62512b9398dc86db`.
Base: `0358fa7a9a2b5e886eddb9896af5f423a8167793`.

## Findings

No finding within the reviewed export-equals fallback.

At `artifact_queries.rs:2365`, the fallback requires an immediate
`ExportAssignment` parent, `is_export_equals`, and an exact expression node.
The unchanged lexical helper then requires an identifier. The new branch does
not admit default exports, parenthesized references, property-access receivers,
or call-expression callees. Other existing artifact paths are not changed.

The branch uses the existing source-bound lexical resolver with `VALUE`,
`EXPORT_VALUE`, and `ALIAS`. It requires the selected symbol's existing resolved
value type and calls the existing type validator before returning that symbol.
It does not invoke a declaration-type producer, resolve a cold alias target,
create an error type, replace a symbol with its alias target, or publish links.

The narrow limit is intentional: an alias with only a ready target value, but
no value type on the alias itself, remains unavailable through this fallback.
This review does not approve cold export-value resolution or broader artifact
parity.

## Focused checks

Three added tests use real parsed and bound declarations. They stage existing
value-cache entries where needed to isolate the fallback.

- Direct scope: a cold `export = value` returns no symbol and a missing-type
  error without checking the declaration file or changing caches. With an
  existing number type, both public queries return the bound value identity.
  The four excluded expression forms remain outside the new fallback even
  when the referenced value has a cached type.
- Lexical scope: an ambient module's local value shadows an outer value. A
  ready outer value does not replace the cold inner binding. Once the inner
  value has its existing string type, both queries use that inner symbol.
- Aliases: a ready namespace target does not cause cold alias resolution.
  Once the alias has the existing target type, the symbol query retains the
  alias and the type query reuses the value identity. Repeated reads leave alias
  links unchanged. The existing validator and store setter reject a foreign
  type without changing the ready cache.

Every case checks repeated reads and unchanged type, symbol, signature, mapper,
table, link-allocation, source-file, relation, and diagnostic snapshots.

The unchanged invocation-recovery test also passed in the new build. Its
original TS2349 and related TS7038 assertions remain intact. The author's
extended body checks the exported function, namespace-import alias, namespace
value, and canonical call-error type before and after source replay. This
review did not change that test body.

## Verification

All 4,198 preservation tests were replayed from the saved candidate binaries.
Each run used a 4 GiB memory scope, one test thread, and a 16 MiB stack. No build
was started for these replays. No test was ignored or filtered out.

- Session `23388`: 3,927 checker tests passed in 48.70 seconds.
- Session `62172`: 258 compiler tests passed in 43.30 seconds.
- Session `24788`: 12 artifact query tests passed in 1.24 seconds.
- Session `72702`: one duplicate-member artifact test passed in 19.57 seconds.

Session `10124` compiled only the needed checker test target in the review
worktree. All three new tests and the unchanged invocation-recovery test passed.
There were no failures or ignored tests and 3,926 filtered tests. The build took
1 minute 7 seconds. Tests took 0.01 seconds. The existing unused
`allows_string_fallback` warning remains.

The new run used the shared capped Cargo runner, an absolute manifest, locked
offline dependencies, 16 GiB memory, a 16 MiB process and Rust stack, the unique
`target/worktrees/wave147-export-equals-artifact-invariants` target, and unchanged
TMPDIR. Source files stayed fixed while queued and compiling.

The logs share `/tmp/ts-rust-wave147-export-equals-artifact-invariants` with
suffixes `-checker.log`, `-compiler.log`, `-artifacts.log`, `-duplicates.log`, and
`-probes.log`. Probe log SHA-256:
`33b4951ba53e04c34cd8a1a09a36e5b3973ab3049414ca02a31f37f620dcb7c2`.

## Fixture evidence

The saved before and after scorecards identify clean Rust revisions
`0358fa7a` and `f265222b`, and the same clean pinned Go revision
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. Their manifest digest and capability
registry digest are unchanged.

Both runs selected exactly one `invocationErrorRecovery.ts` case and variant.
The after result is an exact full-artifact match, including the complete TS2349
diagnostic with related TS7038, all five type nodes, and all six symbol nodes.
There are no header-only matches, unsupported details, mismatches, or fatal
invariants. The before result has the recorded missing export reference.

The scorecards are in the author's `target/evidence/invocation-before.json`
and `invocation-after.json`. This review audited those saved results. It did
not rerun the fixture or update the pinned checkout. Root owns the unchanged
smoke run on the separate composition.

## Scope

The production prefix of `artifact_queries.rs` is byte-identical to the
candidate. `source_calls.rs` and both original artifact integration test files
are unchanged. The review adds only three tests, their fixture helper, and this
report. Rustfmt and diff checks pass. All five command sessions have ended.

No source binding, global or export table, general source checking, constructor
error-alias branch, formatter, fixture, or manifest was changed. No root
promotion or broader artifact-parity approval is part of this review.
