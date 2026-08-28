# Artifact identity composition

Status: prepared. Formatting and 29 source checks pass. No test has run on this
combined source, and no change has been promoted to the primary branch.

Base: `e3ce5f70d704dac9d4a175e09781ebfebd947421`.
Combined code: `41edaf0b6f2fbb0312fb22cc5b92036751dc74ac`.
Source tree: `378b0d40c17bb4be895718d2707bf17aacc80a1d`.
Branch: `root/wave155-artifact-identity-composition`.
Worktree: `target/agent-worktrees/wave155/root-artifact-identity-composition`.
Reserved target: `target/worktrees/wave155-root-artifact-identity-composition`.

The worktree and target did not exist before setup. No build output was copied.
The separate root commands `72404` and `90172` still use their unchanged
`e3ce5f70` worktree. Their pending result is not credited to this composition.

## Imports

| Original | Import | Change |
| --- | --- | --- |
| `582221c3` | `b919b557` | Original merged-class observer and inputs |
| `d187aeb4` | `5bef3141` | Observer declaration-kind comparison |
| `040336dd` | `f9cc8565` | Cold namespace value identity |
| `9e4d3c4d` | `2476b1d0` | Separate namespace verification report |
| `a47b0327` | `2f2bd332` | Symbol-only type-name queries |
| `e6d48861` | `2ed37640` | Required import-equals namespace repair |
| `448e345f` | `41edaf0b` | Separate type-name verification report |

The type-name pair is kept together. The first commit alone has two known
import-equals regressions. The second fixes them without changing their
expectations. The two conflicts here were additive imports and test-module
declarations in `artifact_queries.rs`. Both sides remain.

## Source checks

The standalone ambient-class source repair, alias provider, class planner,
name resolver, bootstrap, formatter, and both root export-review files match
the base byte for byte. The store and production-context changes are additions
only. All namespace observer files and the new test files match their measured
source commits exactly.

The original artifact-query tests have three recorded changes from the measured
type-name leaf:

- `qualified_namespace_names_resolve_nested_exports_without_cached_links`
  now requires the exact unresolved symbol for a missing nested type name.
- `qualified_namespace_imports_keep_alias_roots_and_resolve_exported_members`
  now requires the unresolved symbol with no declarations for a missing import
  member used as a type. The bound alias and real exported member checks remain.
- `module_aliases_preserve_immediate_targets_and_resolved_exports` uses
  `typeof Types.Exposed` for its value query. Its alias-cache and export-table
  checks remain. The added
  `root_type_name_symbols_keep_original_value_export_as_type_negative_control`
  retains the original source and its planted resolved-export table, and
  requires an unresolved symbol distinct from that value.

The audit compares each changed test with `e6d48861`, then verifies every other
byte in the original test module. No original test name was removed. The
standalone negative test also matches `e6d48861` exactly. The retained Go report
distinguishes the original missing export, a real value export used as a type,
and the valid `typeof` form. It is separate evidence, not a new Go run.

Audit command:

```sh
node target/wave155-audit-artifact-identity.mjs
```

Audit output: `target/wave155-artifact-identity-static-audit-v3.json` in the
primary checkout. SHA-256:
`29660279213176307498e05f7c716911c929e2d9cbff8fe25ecb8f2295eb63f9`.
The audit runs no compiler tests. Earlier audit attempts stopped at sandbox
process access, Node's output limit, and the unaccounted test changes above.
The final check keeps the three explicit changes in its output.

Changed-file rustfmt and `git diff --check` pass. No Cargo command is queued for
this worktree yet. It remains open for the separate parser integration after
that worker collects its fixed test runs. The later combined workspace run
must start with this worktree's empty target and retain every root test.

## Remaining checks

The root ambient-class test result, independent class and symbol-cache reviews,
and parser integration are still pending. Namespace display and local
namespace-before-class support are separate tasks. Neither the namespace
observer nor the full artifact comparison has run on this combined source.

The full corpus, modern projects, replay, performance, strict and generated-code
checks, and the controlled upstream update remain required. This composition
does not establish completion of the port.

## Export-alias name check

The next source is `7d6d539a`. Test commit `000f8783` was imported unchanged as
`51379dd9`. The production commit adds only a requested-name comparison in
`global_ambient_class_export_target` before its existing class proof.

The reviewer identified the path by reading the source. If the global `Value`
entry points to the real class `Other`, the old helper can prove `Other` under
its unchanged `Other` entry without checking the requested name. The new check
rejects that mismatch. Local lookup and the class proof stay unchanged.

The original test checks healthy aliases, two rejected lookups, unchanged
state, restoration, and a local class while the unused global entry is damaged.
It is still queued on the original `e3ce5f70` review source in session `13003`.
No runtime defect or successful repair is claimed before those tests complete.
The root `72404` and `90172` sources are also unchanged.

The earlier 29-check audit remains evidence for `41edaf0b`, not for this later
alias-provider change. The new audit script is
`target/wave156-audit-export-alias-name.mjs` in the primary checkout. It checks
the exact three-line guard, both unchanged review files, and that no other
file changed after `c6a47813`. Formatting and whitespace checks pass. The new
worktree still has no queued Cargo job and no runtime result.
