# Namespace constructor value merge

The unchanged pinned `declarationEmitConstructorType.ts` fixture now passes
the public canonical runner. It has no diagnostics and matches the complete
`.types` and `.symbols` baselines. The old fatal result remains in the saved
partial corpus attempt. This repair does not rewrite that evidence.

Repair commit: `8c32f20d45b76eaa126329bc40151217a747c65f`.
Final test commit: `995556d39836293dc10fd3f5af50ee6277cd7e80`.
Checker base: `0358fa7a9a2b5e886eddb9896af5f423a8167793`.
Branch: `agent/wave148-namespace-constructor-type-fatal`.

## Cause and repair

The source has `interface Foo {}` and `var Foo: new () => number` inside an
ambient namespace. The binder puts both declarations on one export symbol
with `INTERFACE | FUNCTION_SCOPED_VARIABLE`. Its value declaration is the
variable. Both declarations also share a local `EXPORT_VALUE` placeholder.
That placeholder has no value declaration and points to the export symbol.
This matches the pinned Go binder's `declareModuleMember`.

The source-check path enters namespace member execution, the canonical
declared-type query, interface property planning, and finally
`object_members::declared_namespace_type_parent`. The last helper required
a `NONE` flag on the local placeholder. It rejected the correct
`EXPORT_VALUE` flag and returned `InvalidInterfaceDeclaration`, which the
compiler maps to `INV.SOURCE.DECLARED_TYPE`.

`preflight_interface_identity` already skips the ordinary value declaration.
The repair does not change that function or the binder. Only the namespace
owner helper changes production behavior. It derives the required local flag
from the authenticated declaration set. It keeps the exact declaration,
name, export-target, empty local value-slot, and namespace-parent checks.
An exported declaration with a missing parent can no longer use the private
declaration path.

No type becomes `any`. No fatal error is relabeled as unsupported. Method,
recovery, union, and formatter producers stay unchanged. The fixture,
capability registry, lockfile, and fixed manifests also stay unchanged.

## Verification

The base reproduction ran before production source changed. Its type-only
namespace control passed. Its merged interface/value test failed with
`Unavailable(InvalidInterfaceDeclaration(... NodeId(3)))` after the binder
identity assertions passed. The test command exited 101, with one passing
test and one failing test.

| Check | Result |
| --- | --- |
| Checker namespace unit tests | 350 passed |
| Final cold and warm identity tests | 2 passed |
| Public CLI full-artifact control | 1 passed |
| Real pinned fixture | 1 exact variant, zero diagnostics |

The identity tests use both declaration orders and both query orders. They
check queries before source checking and source checking before queries.
The interface type and constructor value type remain distinct. Rechecking
keeps the same type and symbol identities without new type, symbol,
signature, or mapper allocations. Diagnostics remain empty.

The unit tests also check seven invalid owner states, both cold and warm.
Wrong flags, missing declarations, a local value declaration, a missing
export target, a local parent, or a missing namespace parent all fail without
new semantic writes. Restoring valid data permits the query again. A separate
control rejects `EXPORT_VALUE` on a type-only namespace interface.

The real pinned run records clean Rust commit `8c32f20d` and clean Go commit
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. It retains variant key
`v1:d067cacc28224de1ec0a98ba7dbc5e69` and the raw `declaration: true` option.
It reports zero unsupported details and zero fatal invariants. Types visit
two nodes and symbols visit three. Both complete artifacts match.

The final test commit changes only the identity test. Production sources
are byte-identical to the passing pinned run. The TypeScript submodule stays
clean at `c3bd12d888b86f676718b16e64d7d2abcb423514`.

## Remaining boundary

The first identity test also requested context-free display of the merged
interface type itself. That query returns
`TypeDisplayUnavailable::MalformedType`.
`formatter::validate_merged_interface_display_owner` currently accepts only
global merged owners and rejects the namespace parent.

The pinned `.types` output does not print the interface declaration's type.
It prints `typeof NS` and `new () => number`, which both match. The final
identity test checks the authoritative declared-type cache instead of
requiring this separate formatter extension. It still requires the exact
constructor display. The failed first-after-run log is retained, and the
formatter remains unchanged. No broader merged-interface display support
is claimed.

## Evidence and limits

`docs/typechecker-wave148-namespace-constructor.json` records complete
commands, observed exit codes, test summaries, source and baseline hashes,
the runner and binary hashes, and the full pinned scorecard.

Large artifacts remain under
`target/agent-worktrees/wave148/namespace-constructor-type-fatal/target/namespace-constructor-evidence`.
The source worktree uses private Cargo target
`target/worktrees/wave148-namespace-constructor-type-fatal`.

Every Cargo command uses the root capped runner, an absolute manifest,
16 GiB memory, 16 MiB process and Rust stacks, the common lock, and unchanged
`TMPDIR`. All owned command sessions finished. Formatting and whitespace
checks passed. The existing 18 checker warnings remain.

This work runs one real pinned Rust variant and one synthetic CLI control.
The checker unit and identity tests are separate from corpus execution.
No Go compiler or observer runs, duplicate full-corpus execution, fixed-shard
promotion, actual-project run, or benchmark is part of this repair.
