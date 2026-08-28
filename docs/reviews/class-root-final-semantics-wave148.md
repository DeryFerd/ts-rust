# Class root semantic review

Reviewed production: `f8636a5004458b27cbaf9aa401c5ff9fdb6054c6` on
`0358fa7a9a2b5e886eddb9896af5f423a8167793`.

Decision: two diagnostic repairs remain. Do not restore the old unsupported
expectations for the newly admitted constructors or method body.

This review changes tests, Go probes, and documentation only. The production
diff from `f8636a50` is empty. The separate query-only class, constructor
position, and JSDoc work is not included.

## Findings

### P2: exported class bodies lose TS2662

```typescript
export class C { static foo: string; bar() { let k = foo; } }
```

Go reports TS2662 at `53..56`:

```text
Cannot find name 'foo'. Did you mean the static member 'C.foo'?
```

Rust admits and checks the class, but reports TS2304 at the same range:

```text
Cannot find name 'foo'.
```

The script form without `export` matches Go. The mismatch remains through
two forced Rust source replays. The new
`root_static_name_priority_is_consistent_for_exported_classes` test fails on
the exported form.

In `source.rs`, the export branch attempts source-class planning at lines
3185 and 3223. Only the ordinary class branch runs the TS2300/TS2662 grammar
check at line 3325. The grammar helper in `classes.rs:19186` also rejects
exported owners and modifiers. Calling that bare-class matcher alone would
not cover the exported form.

The repair must retain unresolved-name error recovery. A static-member
suggestion must not resolve the invalid reference as if the source said
`C.foo`.

### P2: TS2377 covers the whole constructor

```typescript
class Base {} class Model extends Base { constructor() {} }
```

Both checkers report TS2377 with this message:

```text
Constructors for derived classes must contain a 'super' call.
```

Go uses `41..52`, the constructor keyword. Rust uses `41..57`, the whole
constructor declaration. Offsets are zero-based and end-exclusive. The
fixture is ASCII.

`source.rs:29427` calls `issue_node_diagnostic` on the constructor declaration
without a range override. The Program then uses the full node range. Retain
the constructor node and class identities, but use its authenticated keyword
span for this diagnostic.

The constructor probe checks codes and forced replay and prints the complete
record. Its code assertion passes. The range mismatch was found by comparing
that record with the new Go output. It is not a second failing assertion in
the recorded Rust run.

## Expectation update

I independently inspected `41bc7f774670c8269c2563861bb1376ed904bbf4`, whose
parent is the reviewed composition. It preserves all three original
constructor strings, both compiler source strings, and their default options.

The independent Go results support the new admission choices:

| Original input | Go result | Composed Rust result |
| --- | --- | --- |
| Primitive parameter forwarded to a parameter-property base | No diagnostics | Same |
| Constructor with one local variable | No diagnostics | Same |
| Empty derived constructor | TS2377 | Same code and message, wrong span |
| Later method beside an earlier invalid assignment | Earlier TS2322 only | Same file, `6..11`, and message |

The new constructor assertions preserve cold state before checking, distinct
instance and value identities, owner symbols, and forced warm replay. The
compiler assertion retains the earlier file's complete TS2322 record and
checks that the canonical checker was used.

The new `range_override == None` assertion for TS2377 in `41bc7f77` preserves
the wrong full-constructor span. Update it with the diagnostic repair.
Do not change the expected TS2377 code or make these supported inputs fail
source checking again.

I did not import the author's expectation update. The new independent probes
use the exact original inputs against `f8636a50`.

## Root adaptations

- `SourcePlanner` still builds `ClassTypeQueryContext` and array targets from
  the real globals and options. Both legacy class-planning branches retain
  that context. `plan_class_declaration` passes it to constructor planning.
  All seven root constructor-annotation tests pass, including local names,
  namespace references, aliases, optional unions, Date defaults, and cold
  rejection of invalid initializers. Source-body constructors retain their
  documented primitive-parameter limit.
- `source_properties.rs:2130` accepts the caller's instantiation session.
  Its non-class path forwards that same session to the ordinary property
  reader. Only the test compatibility wrapper creates a default session.
  `source.rs:27650` forwards the caller session and real globals. Generic
  property retries retain array targets and the same session at line 33013.
  The property, interface-heritage, and instantiation-limit controls pass.
- The ordinary TS2300/TS2662 grammar priority remains ahead of source-class
  admission. Duplicate fields retain their initializer diagnostics, ranges,
  and order. The full existing duplicate-member artifact control passes.
  The exported TS2662 gap is described above.
- The visibility guard runs before source-class preparation and reads the
  authenticated class and base member/export tables. The original private
  and protected rejection rule remains. All four invalid visibility forms
  are errors in Go, TS2415 for instances and TS2417 for static members.
  Rust retains its explicit unsupported result before any class allocation.
  This is preservation of the existing boundary, not TS2415/TS2417 parity.
- All 23 original class-body, write, and polymorphic-super controls pass.
  Their files and the 14 original review probes remain byte-identical to the
  repaired leaf. Base targets, derived `this`, write flow, and warm identities
  remain covered by those unchanged assertions.

## Reused evidence

The semantic review `05f9c623` is imported unchanged as
`c341b61bcd367cc84327beb8ed1b2d22a52f7d7e`. I also read the invariant review
`e650fb6d`. The imported Rust and Go probe hashes match the saved review.

The 12 leaf Go cases were not rerun. Their source strings, strict-null and
exact-optional settings, ES2015 target, pinned Go source, and library input
remain the same. Both unchanged Rust test functions ran on the root
composition. All four diagnostic cases and eight cold-history cases pass.
Actual write types, complete diagnostics, field/local distinctions, cache
counts, and two forced warm checks remain equal to the retained expectations.

Go pin: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
TypeScript submodule: `c3bd12d888b86f676718b16e64d7d2abcb423514`.
Toolchain: Go 1.26.5, linux/amd64. Both source checkouts remain clean.

## Executed checks

Rust session `30605` exited 101. All 17 selected integration targets ran:
98 test functions passed and one failed. None was ignored or filtered within
those targets. Compilation took one minute. The one assertion failure is
the exported TS2662 control. The additional TS2377 span mismatch is visible
in the constructor record described above.

The run includes the original 23 controls and 14 probes, the 12 leaf cases,
root constructor annotations/parameters/union results, class and interface
heritage, property reads/calls, instantiation limits, both existing compiler
composition/artifact controls, and the four new compiler review tests.
It does not repeat the 4,617-test gate or claim a full workspace pass.

Go session `13200` exited 0. All 12 new subtests passed their expected codes,
repeated diagnostic queries, and class-type pointer checks. The output keeps
the full message, span, detail chain, and related-information count. Repeated
Go queries use the public cached API. They are not fresh source replay.
The new Rust checks force source replay twice.

Cargo used the root capped runner, an absolute manifest, locked offline
resolution, a 16 GiB cap, a 16 MiB Rust stack, the common Git-derived lock,
and `target/worktrees/wave148-class-root-final-semantics`. TMPDIR was unchanged.
Go used an overlay, the same lock, a 16 GiB scope, a 16 MiB stack, one worker,
and an 8 GiB Go memory target. The Go checkout was not edited. Both sessions
are collected.

Logs are `/tmp/ts-rust-wave148-class-root-final-semantics-go.log` and
`/tmp/ts-rust-wave148-class-root-final-semantics-rust.log`. The overlay and
Go wrapper are under this worktree's `target/review/` directory.

| Artifact | SHA-256 |
| --- | --- |
| New Go log | `7518825fb39b1a8ee74ab4967e8dc45d96db960f57b1927f82487a23f1b71d6c` |
| New Rust log | `3ee2c0f1c54161ec400aa9e74fdd878e6dd41ce988e0f3c23b2cbc492aa3ca44` |
| New Rust probe | `3c4e525fd87978c451dbe9ed6f2ae41ca01057cb072d5f0e7afa5ff0a8d07a0e` |
| New Go probe | `64bdf8943c4ce89411256feae855346c1da05a9a3766be234d3d6ef9918f44c5` |
| Reused leaf Go log | `1ed77d957b7f7e38c44fb41f09a5e695f330b7828c3ac3fafd5fb477d614c9f8` |
| Reused Rust probe | `79a77a2fd2d36e2f5b6bc3ad0a399a3eed8c81dd21957fafb4ef5b1381dcebf5` |
| Reused Go probe | `1301b02e3c60602c13f6f724f61f9493cf08774064ce563d110fca240aa872f2` |
| Pinned `es5.d.ts` | `d3527ec5aa76f79514f3ec02c72055761042bd34d272d4dc439fab01d8089235` |

No production or probe source changed after the recorded runs. Rustfmt,
gofmt, and diff checks pass. No strict Clippy result is claimed.
