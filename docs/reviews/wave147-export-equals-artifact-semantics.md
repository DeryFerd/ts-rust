# Export-equals artifact semantic review

Decision: hold `f265222b60340c2a4de8ab8e62512b9398dc86db` for the P2 below.
Base: `0358fa7a9a2b5e886eddb9896af5f423a8167793`.
Date: August 27, 2026.

The original invocation fixture passes its complete artifact comparison.
However, the new fallback also accepts class and enum references and returns
the wrong type for them. This review changes only reports and probes.

## P2: class and enum exports select their value type

The new branch at `artifact_queries.rs:2370` admits every value symbol with a
published value type. `get_type_at_location` then reaches
`type_of_artifact_symbol` at line 2672, which prefers that value type. Export
assignments need a different selection when the symbol has a declared type.

Both of these checked programs reproduce the problem:

```typescript
class Value { value: number = 1; }
const observed = Value;
export = Value;
```

```typescript
enum Value { One = 0, Two = 1 }
const observed = Value;
export = Value;
```

| Location | Pinned Go | Rust candidate |
| --- | --- | --- |
| Class export identifier | `Value` | `typeof Value` |
| Enum export identifier | `Value` | `typeof Value` |
| Ordinary class or enum read | `typeof Value` | `typeof Value` |

Both programs have no diagnostic. The symbol and declaration kinds agree.
The wrong export type remains stable after full Rust source replay. This is
type selection, not class, enum, or namespace formatting.

The focused cache-state probe starts after normal source checking and before
any export artifact query. Both export identifiers have no cached node type,
no cached node symbol, and no binder-attached reference symbol. Their real
declared type already exists and displays as `Value`. Their separate value
type displays as `typeof Value`. The artifact query selects the value identity.

Those observations locate the newly admitted path. Before the added branch,
this uncached reference reaches neither the import-equals case nor an enum
initializer ancestor and returns no reference symbol. The candidate changes
that unavailable route into a successful wrong type. This route comparison is
from the source diff and measured cache state, not a fresh base compiler build.

Pinned Go's `internal/ast/utilities.go:1929` does not treat a direct export
assignment identifier as an ordinary expression. Its
`internal/checker/checker.go:31768` first asks for the symbol's declared type.
Only an error result falls back to the symbol's value type. The runtime probe
checks that exact identity selection, not just a rendered label.

Use the existing declared identity when this export-assignment query requires
it, or keep those symbols unsupported until that identity can be proved.
Do not change the class or enum formatter to hide the wrong selection.

## Mutable variables are correct

Go uses the variable's declared value type at `export = value`, not the
flow-specific type of a nearby ordinary read. The candidate agrees in all
three controls:

| Source state | Export type in both compilers | Ordinary read in both |
| --- | --- | --- |
| `string | number` initialized with `1` | `string | number` | `number` |
| Same variable assigned `'ok'` | `string | number` | `string` |
| `number | undefined` initialized with `1` | `number | undefined` | `number` |

No mutable-variable flow finding is raised. Both type identity and symbol
identity remain stable on the warm queries and Rust source replay.

## Original fixture and aliases

The exact pinned `invocationErrorRecovery.ts`, `.errors.txt`, `.types`, and
`.symbols` files remain unchanged. The reused full-artifact runner reports one
variant, one exact match, five type nodes, and six symbol nodes. There are no
header-only matches, unsupported details, artifact mismatches, or fatal
invariants. Its scorecard records clean Rust `f265222b` and clean pinned Go.

TS2349 and related TS7038 retain their complete messages and spans. The export
reference has `() => void` and the real merged function/namespace symbol. The
namespace-import alias remains distinct. The failed call keeps the canonical
error type displayed as `any`. The new Go control also checks TS2349, TS7038,
and the error-type identity directly.

The direct function control and all three imported-alias controls match Go.
Named imports retain `ImportSpecifier`, import-require retains
`ImportEqualsDeclaration`, and namespace imports retain `NamespaceImport`.
The export and ordinary read use the same local alias symbol. No target symbol
or invented `any` replaces the alias.

## Existing unsupported routes

Five controls remain unavailable and are not counted as exact matches:

- A function merged with a nonempty namespace reaches `MalformedType` during
  display. The cache-state control gets that same display failure from the
  published callable before querying the export reference. The formatter and
  source production are unchanged by this repair.
- An ambient namespace without an existing value identity returns
  `MissingType`. The new branch deliberately does not create its cold value.
- A type-only alias returns `MissingType` and no reference symbol. The new
  lookup has value and alias meanings, not a general type-only export path.
- A type-only interface stops in the unchanged source planner.
- A qualified export assignment stops in the unchanged source planner at the
  `ExportAssignment` node. The new branch handles direct identifiers only.

These are separate from the two successful wrong class and enum answers.
The type-only work, broader namespace support, and root composition remain
with their existing owners.

## Execution and evidence

Pinned Go: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
TypeScript submodule: `c3bd12d888b86f676718b16e64d7d2abcb423514`.
Both checkouts remain clean. The author worktree remains clean at `f265222b`.

Fifteen shared JSON cases feed both compilers. All 15 Go controls pass their
source diagnostics, declared-or-value selection, and warm identity assertions.
The Rust observer completes its supported queries and source replay without
altering the inputs. The comparison reports eight exact export-query matches,
five unsupported cases, and two mismatches. Its exit code is 1 because of the
class and enum findings. Go's `Kind` enum display prefix is the only spelling
normalization in the declaration comparison. Type and symbol strings are not
rewritten.

Fourteen original controls pass using checked existing binaries: the extended
invocation test, 12 canonical artifact tests, and the duplicate-member artifact
test. The author's 4,198-test result was read, not rerun. No broad Cargo build
ran. The small Rust observer links the author's checked libraries into a new
private executable. The Go probe uses a private overlay and copied caches.

The final run is session 27359, exit 0. Session 56259 completed the first matrix
at exit 0. Session 59054 completed the revised Rust probe but stopped while
recopying read-only Go module files. The runner now seeds each private cache
only when it is absent and verifies the modules on reuse. No permission was
changed and no cache was cleared. The final run repeated all checks and passed
every input hash and clean-source check. All owned sessions are closed.

The runs use a 4 GiB systemd limit, no swap, one worker, a 16 MiB stack, disabled
downloads, and unchanged TMPDIR. No production, formatter, source-checking,
fixture, manifest, or dependency file changed.

Worktree: `target/agent-worktrees/wave147/export-equals-artifact-semantics`.
Run these commands there:

```sh
bash docs/probes/run_export_equals_artifact_semantics.sh
node docs/probes/compare_export_equals_artifacts.mjs target/review
```

The second command reports the two mismatches and exits 1. The observations,
comparison, original-fixture scorecard, build logs, input checksums, and binary
checksums are under `target/review`.

| Evidence | SHA-256 |
| --- | --- |
| Shared cases | `576fac3610f4908d642a970782b5eff67af0eb3787fcfd8e3de63a7ab9f36338` |
| Go observations | `7cef0ff18c55e475a63701ff8aafa50e18e6cfc778daf167ba5cdd0de692f435` |
| Rust observations | `d40dff66c333555bb682ff6afddfe2c2175ecacab5cdc782f625c2032eeb66cf` |
| Comparison | `3dd9c8acdbf23a59d2de86914c83bf59c7f393d01d8e0d92dd324073358439f5` |
| Original invocation source | `b54ea576526657470159e298b1709873a0b07cd5da9f8c87df991cd28c25a105` |

This is a semantic hold on the candidate. It is not an approval of the combined
root smoke or general artifact parity. Invariant review remains separate.
