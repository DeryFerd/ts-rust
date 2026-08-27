# Object witnesses in artifact phases

This adapter composes the approved provider at `b650cedf` with the reviewed
phase producer at `c0c72945`. Provider source files remain unchanged.
The Hono display probes and proposed formatting fixes are not included.

## API and order

Every direct type query in the pinned artifact walker is replaced one for
one by `ProjectOracleObjectQuery`. The adapter returns that call's actual
type pointer to the walker. The existing raw-pointer and sequence hooks
observe the same return. No extra type query or pre-warming call is made.

The source-only Program never opens an object pass. Each query Program pass
opens after its before-types diagnostic snapshot. It closes after types,
symbols, and the after-symbols diagnostic snapshot. Provider calls and
adapted walker calls hold the Program's exclusive checker lock.

The provider handles are opaque. Report tokens bind the actual returned
handles and type pointers inside this process. They are adapter tokens,
not copies or claims about the provider's private token fields.

After both passes close and the original phase comparisons finish, the
adapter checks that cold and warm query slots have the same rendered and
queried nodes. It verifies object-literal and parenthesized-object query
pairs in their original warm-query order. A slot mismatch stops verification.
Non-object queries remain recorded but are outside this provider's scope.

Verification runs once per selected pair. Its relation result and side
effects are preserved. There is no retry to hide a changed witness or a
cached relation result. The original phase report and artifact bytes are
checked for changes after verification.

This adds proof data only. Raw pointer failures, differing artifacts,
unavailable fresh diagnostics, and nonzero oracle results remain unchanged.
The proof report does not grant project parity or replace any current gate.

## Commands

```sh
bash tools/ts_fixture/go_project_oracle/object_witness_phase/run.sh GO UPSTREAM CONFIG OUT controls
bash tools/ts_fixture/go_project_oracle/object_witness_phase/run.sh GO UPSTREAM CONFIG OUT run
```

All paths must be absolute, and `OUT` must be new. Set `GOMODCACHE` to a
copied verified cache under the output parent. The launcher preserves the
16 GiB default, shared build lock, one Go worker, copied module inputs,
Go 1.26.5 pin, and offline dependency policy. A verified prior build cache
may seed the isolated cache through `TS_OBJECT_PHASE_BUILD_CACHE`.

Controls write persistent inputs and both plain and adapted reports. They
compare every direct query event, artifact, diagnostic phase, and original
failure result. They test open-pass refusal, exact return binding, class-base
fallback calls, unsupported objects, and both renderer-flag values.
Real-project runs remain nonzero under the existing phase gates.
