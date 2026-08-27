# Declared class type-parameter cache witnesses

## Approved phase base

The phase worktree remains clean at `6dafae9b`. Root recorded the two
delivered review messages in `/tmp/ts-rust-wave134-object-witness-reviews.md`.
The runner review and replay review both give bounded approval without
blocking findings. They did not run a new build or project run. This is a
record of those delivered reviews, not a claim of new reviewer files.

The approved series after `c0c729459fe2e6cc4c3b991dd7581aaa4bd33f23` is:

1. `a1bed56a4f3f450958de7b6eaa247393f42c40ec`
2. `8216be0b00c3e5946dab4d7eddb3ef3e5463260c`
3. `4460f38649189d7b33b5d132b9a83d0fc6cf4df7`
4. `419f43e051d526c6b4c0a1c508b04d1bd53934ce`
5. `6dafae9b9f39614b68e18f9b02c843ce96531fd9`

Both reviews retained 18,962 original events, 18,890 artifact queries,
6,202 receipts, 16 unchanged artifact files, and all 44 raw pointer failures.
Each saved process has 17 verified and 52 incomplete pairs and exit 1.
Fresh diagnostic equality is null. Parity is false. This new provider change
is separate from that approval and needs its own review.

## Bounded change

The first saved incomplete pair is `query-00000238` / `query-00009683` in
ts-pattern `src/match.ts`, bytes 2682 through 2778. The saved type artifact
prints `value: handler(...)` as the class type parameter `output`. Its
reported reason is `property type has no proved cache owner at creation`.
The saved reports are unchanged. No new ts-pattern result is claimed.

The new cache edge covers only an unconstrained, unmodified type parameter
declared by one named class. It reads `declaredTypeLinks.TryGet` and requires
the exact existing type, symbol, declaration, class owner, parameter list,
and source file. It does not call a resolving getter or create a cache entry.

Creation captures the type header, the whole type-parameter record, the
declared-type links, and declaration ownership. Closure and verification
must retain those values. No lazy changes are normalized for this edge.
The initial memo flags may be zero or the exact computed/contains pair set
by the pinned `couldContainTypeVariablesWorker`. Later flag changes fail.
Missing creation evidence remains incomplete even if the cache is repaired
before closure. Changed captured data is rejected before the relation runs.

Constraints, defaults, modifiers, function parameters, `this` parameters,
instantiation targets, and mappers are outside this addition. Existing
intrinsic and function-cache checks are unchanged. The adapter, renderer,
source inputs, saved artifacts, and strict raw-pointer gate are not changed.

## Controls and method

The positive controls cover a call result and two separate declared parameter
owners. The shorthand control retains its cached raw pointer and stays
incomplete because no actual object producer was observed. Further controls
cover empty cache lookup without resolution, missing creation evidence
restored before closure, cache and declaration mutations in three timing
windows, and the
unsupported declaration forms listed above. Positive controls require
different cold and warm raw pointers and equal printed text.
Memo flags are mutated before cold closure and after both closures. A later
query can restore these flags, so the control does not claim to detect an
unobserved change that was repaired between snapshots.

The standalone checker-test launcher is
`target/worktrees/wave134-object-witness-type-parameter/run-provider.sh`
in the shared workspace at `/home/theo/Code/sandbox/ts-rust`.
It uses Go 1.26.5 at SHA-256
`8da5fd321795754b994c64e3eb8a5a14ff47bd285559a7e876f3c79abafc67f9`
and TypeScript-Go at `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

The launcher copies verified caches and module inputs into a new output
directory. It holds `/tmp/ts-rust-cargo-3253601520.lock`, uses one Go worker,
sets a 16 GiB cgroup cap with no swap, and disables dependency downloads.
It compiles `./internal/checker` with the unchanged checker and relation
patches plus the three provider overlays. The test filter is
`^TestObjectQueryWitness`, with count 1 and a 600-second timeout.

The complete provider suite passed in `attempt-3`. Its result audit checked
all 42 new control cases and confirmed the current source is byte-identical
to the compiled provider and test overlays. The build took 111.374 seconds
with peak RSS 2,400,804 KiB. Tests took 3.737 seconds with peak RSS 95,924 KiB.
Both exited 0. The cgroup recorded no OOM events.

Both positive cases retain different cold and warm object pointers and equal
text. Each verifies one fresh object and two cache edges. Each relation adds
one identity-cache entry and allocates no types, symbols, or signatures.
Neither reports diagnostics, suggestions, overflow, panic, or changed witness
data. All 32 mutation-window cases reject before a relation call. The empty
lookup creates no cache entry and no checker types, symbols, or signatures.
The repaired cache and cached shorthand cases remain incomplete.

The earlier attempts remain available. Attempt 1 compiled but stopped after
a test mutation set a declaration parent to nil and broke the renderer's
source-file path. The corrected mutation points at another valid class,
which retains printable source text but violates declaration ownership.
Attempt 2 failed only because shorthand was incorrectly expected to produce
fresh objects. It returned equal raw pointers and equal text, with no actual
producer observation. The final control keeps that result incomplete.
No renderer or provider acceptance rule was changed to clear that failure.

The recorded final invocation was:

```sh
ROOT=/home/theo/Code/sandbox/ts-rust
SOURCE="$ROOT/target/agent-worktrees/wave134/object-witness-type-parameter"
OUT="$ROOT/target/project-evidence/object-witness-type-parameter/attempt-3"
env TS_OBJECT_PARAMETER_BUILD_CACHE="$ROOT/target/project-evidence/object-witness-type-parameter/attempt-2/go-cache" \
  bash "$ROOT/target/worktrees/wave134-object-witness-type-parameter/run-provider.sh" "$SOURCE" "$OUT"
```

The compiler and test commands inside that capped scope were:

```sh
"$ROOT/target/toolchains/go1.26.5/bin/go" -C /home/theo/.explore/repos/microsoft__typescript-go \
  test -mod=readonly -modfile "$OUT/go.mod" -c -p 1 \
  -overlay "$OUT/overlay.json" -o "$OUT/object-witness.test" ./internal/checker
"$OUT/object-witness.test" -test.run '^TestObjectQueryWitness' -test.count=1 -test.v -test.timeout=600s
```

Their exact environment is recorded in `build.json`. It uses
`GOTOOLCHAIN=local`, `GOPROXY=off`, `GOSUMDB=off`, `GOWORK=off`, empty
`GOFLAGS`, `GOMAXPROCS=1`, and `GOMEMLIMIT=12582912KiB`. `GOCACHE`,
`GOMODCACHE`, `GOTMPDIR`, and `TMPDIR` all point inside the new output.

Evidence is under
`target/project-evidence/object-witness-type-parameter/attempt-3`.
`build.json` records the source hashes, overlays, commands, binary, and
resources. `tests.stdout.log` records the controls and provider results.
`cgroup-before.json` and `cgroup-after.json` record the actual limits.
`audit.json` records the source and control checks and the unchanged hashes
of the approved phase reports and input-verifier records.

The audit SHA-256 is
`4a16b2b2fe5275193c5ded0205f53e2668505a0c5e2b03f3ea8006ede2bd3b59`.
The test binary SHA-256 is
`35a2e420e678ce85c0cc560a43de10c0bebe196eff50523ea53b15dc15b4ef04`.

The phase launcher remains pinned to `b650cedf` and does not load this new
provider. No real project was rerun. The saved 17 verified / 52 incomplete
results, all 44 raw pointer failures, null fresh-diagnostic equality, and
false parity claim remain unchanged. Root can take this provider commit
separately after its own review.
