# Phase-correct Go evidence

This separate schema 3 producer starts from `7b912dc5`. It does not modify
that producer, its gates, project configs, or earlier reports.

## Programs

Each process creates two independent Programs and keeps their checker
identities separate. Both use the real config, normal host, pinned bundled
libraries, and the existing pre-emit Program diagnostic policy.

The source-only Program runs first, before any artifact query. It records
initial diagnostics, diagnostics before reset, and diagnostics after the
existing source completion reset and normal Program re-entry. These remain
retained snapshots, not fresh diagnostic production.

The query Program records initial source diagnostics, then snapshots before
types, after types, and after symbols. It records another snapshot before
reset and after re-entry, then repeats the same artifact phases. The pinned
walker's `hadErrorBaseline` input is frozen from the initial source snapshot
for both walks. A later query-added diagnostic cannot change this input.

Every snapshot has its own `.errors.txt` state and ordered inputs. Query-phase
snapshot differences are labeled retained snapshot differences. They are not
silently added to the initial source-check result or called fresh production.
Type and symbol artifacts refer back to the initial source snapshot token.

## Sequence

`sequence.jsonl` records monotonically ordered operation tokens. Program and
checker tokens are assigned to actual object identities and scoped to the
process. A checker cannot bind to two Programs. The initial checker binding
is obtained after normal diagnostic collection, not by forcing early setup.

Every direct baseline `GetTypeAtLocation` and `GetSymbolAtLocation` call has
a query token, the actual Program and checker tokens, phase, and exact queried
and rendered node path, byte range, and kind. Query events record return
boundaries. Diagnostic collection and source reset operations are also
recorded. Internal compiler queries are not claimed as baseline queries.

The trace is streamed and hashed. The report records its byte count, event
count, query count, and checksum. Tokens are not cross-process object IDs.

## Gates

Pointer equality remains strict for all retained direct query results,
rendered type results, and symbols. Equal artifact text cannot bypass a
pointer failure. Source-only retained diagnostic changes and artifact byte
or visit changes also remain failures.

Without a reviewed fresh-diagnostic producer verifier, a stable result is
`incomplete_evidence`, not complete or parity. Failures remain
`invariant_error`, and real oracle runs return nonzero. Missing eligible
project sources remain explicit. No broad cache reset is implemented.

## Commands

All paths must be absolute. The output must be new. The launcher preserves
the shared build lock, 16 GiB scope, one Go worker, copied module inputs,
Go 1.26.5, and offline dependency policy.

Set `GOMODCACHE` to a copied, verified module cache beneath the output's
parent directory. The launcher does not download dependencies. For an
archive project inside another Git repository, set
`GIT_CEILING_DIRECTORIES` to the archive's parent so the helper does not
attribute the input to that other repository.

```sh
bash tools/ts_fixture/go_project_oracle/phase_correct/run.sh GO UPSTREAM CONFIG OUT controls
bash tools/ts_fixture/go_project_oracle/phase_correct/run.sh GO UPSTREAM CONFIG OUT run
```

Controls cover the five query-added diagnostic reduction, frozen false and
true renderer flags, independent Programs/checkers, exact sequence tokens,
and strict pointer failure for an object literal with equal printed text.
