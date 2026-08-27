# Namespace wrapper semantic review

Decision: hold `7cadc15287af26cd19998a440e00c48fee10519f` for one confirmed
formatter finding. The producer and property-reader comparison found no
blocking semantic issue in the tested source family.

## Blocking finding

`crates/ts_checker/src/semantic/formatter.rs:1811` formats a wrapper through
`wrapper.source.alias` whenever a location is present. Valid import origin
does not mean that this alias is visible at the requested location.

This valid NodeNext input reproduces the problem:

```typescript
// producer.cts
export const value: number = 1;

// consumer.mts
import * as ns from './producer.cjs';
export const copied = ns;
function shadow(ns: number): number { copied; return ns; }
```

For `copied` inside `shadow`, Rust returns `typeof ns`. Pinned Go returns
`typeof import("./producer.cjs")`. The local `ns` is a number parameter.
The Rust probe confirms that it has type `number` and a different TypeId from
the namespace. The returned text therefore names the wrong value binding.

The formatter validates the wrapper's origin, then asks the ordinary symbol
writer to name the original alias. That writer can fall back to the alias's
plain name when no accessible chain exists. It cannot recover the correct
module reference from this request. Go's node builder starts from the module
symbol and can use an import type when the import alias is hidden.

The repair must choose a name valid at the actual display location. Do not
reject this supported source, collapse wrapper and bare identities, invent
compiler mode facts, or add the generated default to source exports.

The committed review probe is
`crates/ts_compiler/tests/canonical_namespace_wrapper_display_scope_review.rs`.
Its expected string comes from the pinned Go cold artifact. It currently fails
on its first display assertion. Its forced-replay branch has not yet run.
No production change or weakened assertion is included in this review.

## Exact composition

Root base: `9b6eb86bf548202e621f9470f5a73a0c089291a5`.
Production checkpoint: `8a941701d5bbe742130475e1a77729ae712e1f7c`.
Verification checkpoint: `7cadc15287af26cd19998a440e00c48fee10519f`.

| Original | Root import |
| --- | --- |
| `d326cf791b596780ae3df08a8799fe697630bc0b` | `7cdda5ec01f7e37f369420d0603565f7aaede4f3` |
| `190e4aef50319bea306ceeb0056ff7759c57ecbc` | `6607b5ad3412779f9622befd6d99792b924d99a8` |
| `f9b62d4b4b927782173beda8f2b8e2d51ebf9978` | `8a941701d5bbe742130475e1a77729ae712e1f7c` |

I reviewed the committed diffs and the combined source. Range comparisons
show no semantic import change. Root already had the equivalent JavaScript
predicate method reference. Both consumer patches otherwise match their
originals. `7cadc152` adds combined property/display/replay assertions only.

## Matching behavior

Pinned Go is `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
The comparison used the actual cached Go source and saved artifacts.

- `checker.go::resolveESModuleSymbol` uses the ESM-import/CommonJS-target pair
  for this wrapper. The Rust producer uses the existing resolved manifest
  modes. Real NodeNext compiler tests derive them from `.mts` and `.cts` files.
  No compiler production or mode-classifier change is part of the stack.
- Go's `cloneTypeAsModuleType` retains a separate module symbol, source target,
  and originating import. Rust retains the corresponding import-owned view
  separately from the bare source namespace. Two ESM imports keep distinct
  namespace identities and the same generated default alias.
- Go's generated default is an alias to the original module. The Rust wrapper
  keeps that alias in the type's member view. Raw source exports remain source
  exports. The source module does not gain a fabricated default export.
- The property consumer reads validated wrapper members before raw exports.
  `ns.value` and `ns.default.value` retain the source export symbol and number
  type. `ns.default` retains the generated alias and bare namespace type.
  Non-wrapped views do not gain a default. Their missing-default controls still
  report TS2339 for the tested producer.
- Query-first and value-first controls retain their TypeIds through later
  value publication. Forced source replay retains property and alias identity.
  Incomplete cold wrapper display remains unavailable without writes. That
  negative control is not evidence of complete cold-display parity.
- At a location where the import alias is visible, wrapper display as
  `typeof ns` matches the saved Go artifact. The bare default value displays
  as `typeof import("./producer.cjs")`. The blocking finding is the hidden
  alias case, which the prior tests did not cover.

Relevant Go code is in `internal/checker/checker.go`, including
`resolveESModuleSymbol`, `createDefaultPropertyWrapperForModule`, and
`cloneTypeAsModuleType`. Scope-aware type naming is in
`internal/checker/nodebuilderimpl.go::symbolToTypeNode` and `getSymbolChain`.

## Executed probe

Evidence paths below are relative to this review worktree's `target/review`.

- Rust session `44151` exited 101 and is collected. The test compiled and
  reached the display comparison. One test failed, with no ignored tests.
  Log: `namespace-display-scope-rust.log`.
- Go session `17081` exited 1 and is collected. It produced cold and warm type
  and symbol artifacts with empty diagnostics. Its overall outcome is
  `incomplete_evidence`, solely because fresh diagnostic replay is unavailable.
  This exit is not a successful full oracle result.
- The Go cold artifact contains `copied : typeof import("./producer.cjs")`
  inside the function and `ns : number` for the local parameter and return.
  Cold and warm artifact files are byte-identical. Fresh diagnostic replay
  remains unavailable and is not claimed.
- The run reused the unchanged pinned executable with SHA-256
  `fae09af2f812b27e2e8dfd568ffcb7a193096d2a531a05b7e0b2472f297f46ad`.
  No Go build or upstream edit occurred. Input hashes and reused-build
  provenance are in `namespace-display-scope-build-provenance.json`.
- Both runs used the shared queue and a 16 GiB memory scope. Rust used the
  capped runner, an absolute manifest, a 16 MiB stack, locked offline
  dependencies, and the new target
  `target/worktrees/wave142-namespace-wrapper-semantics`. TMPDIR was unchanged.

Full Go evidence is in `namespace-display-scope-go/`. Its cold artifact is
sufficient to establish this display mismatch. Its partial replay record is
not a full fresh-diagnostic or project-parity result.

## Other verification

The saved composition log
`/tmp/ts-rust-wave142-namespace-wrapper-composition-tests.log` records 4,345
selected passes: 3,911 checker units, 258 compiler units, 164 fixture units,
and 12 public tests. There are zero failures or ignored tests in that run.
Those results remain valid for the original controls, but do not cover the
new shadowing case. The original producer and consumer evidence was also read.

The new route remains limited to its admitted TypeScript source-file namespace
imports. It does not add support for JavaScript/CommonJS-assignment targets,
type-only namespace typeof queries, ambient resolution targets, dynamic
imports, or broader export-equals wrappers. Existing separate paths are not
claimed fixed by these commits.

No full workspace, strict Clippy, complete artifact parity, or fresh Go replay
pass is claimed. Root's namespace semantic hold should remain until the scope
finding is repaired and the unchanged failing probe passes.

## Evidence hashes

SHA-256:

- Rust probe: `ec792bc8c60d318e82bddf05f206dd376f61ff75156554743a9b4673e0b5962f`.
- Rust log: `bf2bd1954deb95e1da2f1b0c494e1921b9862cd5bf6f28118e8a15fc4b495931`.
- Go cold types: `ac15801babcac5002e3d0012f912975dbbad3355e86ba0434a9daebec1453514`.
- Go report: `ff3523d8e62a7af3ba73d8974b3d8240ce6b158738f27f9957330de8ea4cecc7`.

All review command sessions are collected. Production source remains identical
to `7cadc152`. The probe and this report are the only tracked review changes.
