# Namespace and export-equals composition

Tested source: `ac91c1df7f04b622894aedd8b3299d39d9b977e1`.
The combined test selection passes all 4,415 tests. The fixed semantic smoke
retains all 53 previous exact results. No primary promotion is claimed.

## Imported changes

The worktree starts from namespace report `c3cd3b50`, whose tested source is
`3a336ec7`. These imports completed without conflicts:

| Original | Import | Change |
| --- | --- | --- |
| `768242ba` | `5354dee2` | Namespace alias scope probe |
| `7cac087f` | `d576bf5b` | Namespace semantic review |
| `537ec1b1` | `ec663bc9` | Namespace invariant review |
| `51ce71a1` | `4589c500` | Original export-equals review and input data |
| `9ca7dffb` | `ac91c1df` | Existing declared types for class and enum exports |

The export repair has the same stable patch ID before and after import:
`8db44174fcb1c534656401a9e23c91b56d240491`.
The unchanged review JSON has Git blob
`d4e18b3e7943cd6edb32b0de4861aedd7080f3f1` in both source and composition.
The import range passes `git diff --check`.

## Combined tests

Session `27180` exited 0. All 20 requested binaries ran with no failed,
ignored, or filtered tests.

| Group | Passed |
| --- | ---: |
| Checker units | 3,939 |
| Compiler units | 258 |
| Fixture units | 164 |
| Public controls | 54 |
| Total | 4,415 |

The test-name comparison retains all 4,412 controls from the preceding root
run. The only added tests are the export declared/value identity unit, the
public export-equals control, and the namespace alias scope control.

## Semantic smoke

Session `79401` exited 1 because known unsupported and mismatching cases remain.
It used the unchanged 96-entry `checker-smoke-v1` selection. There are 95
executions and one upstream-skipped configuration.

| Primary result | Count |
| --- | ---: |
| Exact | 53 |
| Unsupported | 41 |
| Artifact mismatch | 1 |
| Fatal invariant | 0 |

The complete summary and semantic-artifact totals match `ba41ed3a`. All 53
previous exact rows are deeply equal. No selected row was added or removed.
The only changed row is the already unsupported
`nodeModulesDeclarationEmitWithPackageExportsNoOutDir.ts`. Its import node
number changes from 29 to 23 in the reported error. This is not new support.

The scorecard records clean Rust source `ac91c1df` and clean pinned Go source
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. The selection digest stays
`60dbd52bce2c3f9f94971819ad0d9cda`.

## Execution and evidence

Both commands used the root capped runner, absolute manifests, locked offline
dependencies, 16 GiB memory, a 16 MiB Rust stack, the common lock, and unchanged
`TMPDIR`. Both used the target assigned only to this physical worktree:

```text
target/agent-worktrees/wave148/root-namespace-export-composition
target/worktrees/wave148-root-namespace-export-composition
```

The source stayed fixed and clean until both commands were collected.

| File | SHA-256 |
| --- | --- |
| `target/wave148-namespace-export-combined-tests.log` | `4a489e74b8c1b610e2e6573e423bf0983356bcd2bc055b1fd565f59a2d8c1891` |
| `target/wave148-namespace-export-semantic-smoke.log` | `488dca5dcf948e5a6829aac3c0d130bedbfdb5c3630f0cca287f61156a1e36b2` |
| `target/wave148-namespace-export-semantic-smoke.json` | `13f3db5bf8501921798093aafce02505183cbaff44125090387d5a26009d9072` |

## Remaining work

Final independent export-equals reviews remain separate from this combined
result. The compiler relative-specifier repair, heritage and method proof
composition, class composition, JSDoc repairs, and other active changes are
not imported by this report.

The full corpus runs separately on checker base `0358fa7a` with runner source
`95114a7d`. Its results must not be attributed to this candidate. Full corpus
parity, modern projects, fresh replay, performance, upstream roll-forward, and
cutover remain incomplete. The full port goal stays active.
