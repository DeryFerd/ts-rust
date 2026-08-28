# Constructor property write semantic review

Candidate: `6b93562f5a91af2d4ceda8b816845fa538274c8a`.
Base: `9b1f0c304a72002e246c5f65b06e3bf68327d4d6`.
Decision: hold semantic approval for the two findings below.

This review changes tests and this report only. The write provider, class
metadata, source executor, flow provider, super selection, and existing tests
are unchanged. The separately reviewed super repair `e765a682` is not included.

## P1. Optional constructors depend on an unrelated union cache

The following valid constructor returns `SourceCheckError::Class` at its
parameter on a cold check. Pinned Go accepts it with no diagnostics.

```typescript
declare let cachedOptional: number | undefined;
class OptionalParameterControl {
    constructor(public readonly value?: number) {
        this.value = 1;
        const parameter = value;
    }
}
```

`review_constructor_optional_parameter_failure_precedes_writes` proves that
the error also occurs without the write. The parameter value cache and the
write expression cache are still empty after the failure. Querying the unrelated
`number | undefined` annotation through `get_type_from_type_node` then makes
the same source check succeed. The probe changes no AST or option and uses no
cache mutation test hook.

The source constructor planner calls `optional_constructor_parameter_type`
at `classes.rs:445`. That helper only looks up the optional union and returns
`None` while it is cold, at `classes.rs:4241`. The new early constructor dispatch
at `source.rs:3295` then falls through because `try_plan_source_class` turns the
unsupported source plan into `None` at `source.rs:7704`. The legacy reader rejects
the extra local at `classes.rs:4474` and reports a class invariant.

This is a constructor-dispatch and class-provider integration gap. It occurs
before the new write target executes. The class-provider cache lookup and the
legacy locals guard are unchanged in this patch. This review does not claim a
regression from a previously passing base case. It does prove that the newly
available constructor path still depends on prior query history.

Prepare optional parameter types through the class provider before this dispatch
can require their identities. Do not change declared member types or replace the
missing union with a scalar type to pass the frame checks.

Three focused positive probes retain the cold failure for ordinary optional
parameters and optional parameter properties. A separate prepared-cache probe
passes under both exact-optional settings, accepts an undefined write, and
completes two forced warm checks.

## P2. Accepted write diagnostics do not match pinned Go

The write executor uses the shared assignment reporter at `source.rs:29094`.
Its exact-optional rewrite at `source.rs:29244` changes the primary message but
cannot restore the missing union detail lines. The shared reporter at
`source.rs:31670` also retains a nullable target name that Go omits for a plain
string mismatch.

For this supported write, Rust and Go select TS2412 at the same position, but
Rust omits the final line shown below.

```typescript
class OptionalUnionSource {
    value?: number;
    source?: number;
    constructor() {
        this.value = this.source;
        const after: number = this.value;
    }
}
```

```text
Type 'number | undefined' is not assignable to type 'number' with 'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the type of the target.
  Type 'undefined' is not assignable to type 'number'.
```

The same missing detail occurs for a `string | undefined` source and for the
following `const after: number` assignment under both optional-type settings.
Five message probes fail at their final diagnostic comparison. Before that
comparison, they pass the expected read-type checks, declared primitive field
checks, and two forced warm checks with stable node links and allocation counts.

A second message difference occurs without exact optional types:

```typescript
class PlainParameter {
    value?: number;
    constructor(input: string) {
        this.value = input;
    }
}
```

Go reports `Type 'string' is not assignable to type 'number'.` Rust reports
`Type 'string' is not assignable to type 'number | undefined'.` Both use TS2322
at the write target. This is an error-display difference. Narrowing the actual
write target to `number` would incorrectly reject valid undefined writes.

The shared reporter predates this patch. The finding is a remaining diagnostic
parity gap in the newly accepted write path, not a claim that this patch changed
the shared reporter's existing behavior.

## Passing checks

- All 12 existing public class-body tests and all 7 public class-write tests pass.
- The unchanged original `optional_class_property_assignment_keeps_the_real_flow_type`
  unit test passes.
- Distinct public `value` and private `#value` fields preserve TS2565, field
  identity, read types, and forced warm state.
- A write with `this` on both sides before `super()` preserves both TS17009
  diagnostics and the ES2015 TS2376 diagnostic. The later read has number type.
- A second write that reads the first write's result keeps number flow under
  both exact-optional settings and on forced warm checks.
- Once the optional union is prepared, an optional parameter property accepts
  undefined under both settings and remains stable on two forced warm checks.

## Boundaries and attribution

The broad probe batch also tried union-typed field declarations, a write after a
constructor return, and a receiver alias. The first two forms returned typed
unsupported errors. They did not reach diagnostic or warm comparisons. The
receiver alias returned `RelationUnavailable(UnsupportedStructuredType)` even
without a property write. That control remains in the focused file to keep the
failure separate from write flow.

Four broad positive probes were removed from the focused file after this
classification. Their complete executed snapshot is saved at
`/tmp/ts-rust-wave141-class-writes-all-probes.patch`, and their output is in
`/tmp/ts-rust-wave141-class-writes-followup.log`. No retained assertion was
changed, and no existing test was changed or ignored.

Optional private identifiers remain the documented unsupported declaration
case. Their Go result is not counted as a passing Rust oracle control. No new
claim covers inherited, static, accessor, computed, compound, guard, loop, or
nested-function writes.

## Execution evidence

- Session `3919`: 3 of the initial 11 review probes passed. All 19 existing public
  tests passed. Build time was 38.22 seconds. The three test binaries took 0.06,
  0.08, and 0.10 seconds. Exit 101.
- Session `58847`: the original property-flow unit test passed, with 3,723 tests
  filtered out. Build time was 55.95 seconds. Execution took 0.01 seconds. Exit 0.
- Session `19207`: 6 of the expanded 18 review probes passed. Five failures were
  accepted-write diagnostic differences, three were cold optional-parameter
  failures, and four were the separately classified broad probes. Build time
  was 0.63 seconds. Execution took 0.11 seconds. Exit 101.
- Session `17870`: the final focused file had 6 passes and 8 failures. The five
  message differences and three cold optional-parameter failures remain.
  Build time was 0.71 seconds. Execution took 0.10 seconds. Exit 101. Output is
  saved at `/tmp/ts-rust-wave141-class-writes-focused.log`.

Two of those six passing probes are failure-location controls. They establish
the cache dependency and the independent alias limitation, not Go parity.

The final file contains 14 tests with unchanged retained assertions. No test or
production source edit followed the final run. All command sessions are
collected. All Cargo commands use the shared capped runner, an absolute
manifest, `--locked --offline`, 16 GiB memory, a 16 MiB Rust stack, and the unique
target `target/worktrees/wave141-class-writes-semantics`. TMPDIR is unchanged.
No outer lock or queue bypass was added.

The focused test file passes Rustfmt. The staged diff has no whitespace errors.
The existing tests and production source still match the reviewed candidate.

The author's 3,724-test unit pass was read from the handoff. It was not repeated
by this reviewer. No full workspace, strict Clippy, or combined-super pass is
claimed.

## Pinned Go evidence

The compiler binary and matching clean checkout both identify
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. The binary embeds
`vcs.modified=false`. Fresh ordinary and exact-optional runs are saved under
`/tmp/ts-rust-wave141-class-writes-oracle`.

Both runs use strict checking, ES2015, `--noLib`, `--skipLibCheck`, `--noEmit`,
and the pinned checkout's `es5.d.ts`. The optional-cache fixture passes with
zero diagnostics under both settings. The error fixture's full output is saved
as `ordinary.log` and `exact.log`.

Relevant Go code is `checker.go:12717` for assignment errors,
`checker.go:13074` for exact-optional mismatches, `checker.go:27139` for readonly
writes, and `flow.go:220`, `flow.go:1576`, and `flow.go:2374` for assignment flow,
receiver matching, and assignment type reduction. The tests compare Go's sorted
diagnostic presentation and separately retain raw diagnostic order for warm
checks. No production diagnostic sort was added.
