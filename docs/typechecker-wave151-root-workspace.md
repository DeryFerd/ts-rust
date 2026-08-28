# Root workspace verification

Tested source: `31f61095d65ab3dbbf4cb6e8fffa8e0f8eb1655f`.
Source tree: `55c2b94f313907ab82d9112ef6ce371897f5dc99`.
Result: 6,676 passed and two failed. This is a held result, not a completed port.

The full workspace ran 154 test binaries and 32 documentation-test groups.
No test was ignored, measured, or filtered. The read-only workspace format
check passed. Both command sessions are collected.

## Imported changes

This source starts at `258c214a` and combines the verified interface-heritage
recovery changes with the private-class artifact provider.

| Source | Root import |
| --- | --- |
| `311820a0` | `bd49b8a1` |
| `08cf6458` | `d0e2fc11` |
| `d941bab7` | `48b10427` |
| `d7a6dfbb` | `e1a0ea1a` |
| `0efdd881` | `31f61095` |

All five imports retain equivalent patches. Root's direct export source checks
and lexical name resolver remain present. No broad parent history was merged.

## Results and retained controls

Session `52676` ran `test --locked --offline --workspace --no-fail-fast` and
exited 101. Session `21688` ran `fmt --all -- --check` and exited 0.

The checker library passed 3,980 tests and failed these two original controls:

- `export_equals_final_invariant_global_class_namespace_merge_keeps_identity`
- `export_equals_final_invariant_local_class_namespace_merge_keeps_identity`

Both fail during source checking, before artifact queries. The global case
returns `NonVariableSymbol` for `Value`. The local case returns
`NonUniqueDeclaration` for the class and namespace declaration pair. These are
the same failures reported by the previous root selection at `e896cbf8`.

All 4,431 test names from that prior selection are present in this full run.
Its 4,429 passing tests still pass. No additional workspace test failed.
The adjacent JSON report checks each binary's named test count against its
reported result and includes all failed names, documentation groups, totals,
and the complete prior-name comparison.

## Build evidence

The physical worktree stayed fixed and clean during both commands:
`target/agent-worktrees/wave151/root-heritage-artifact-composition`.

The target did not exist before launch:
`target/worktrees/wave151-root-heritage-artifact-composition`.
No artifact or fingerprint was copied, reflinked, hardlinked, or seeded from
another worktree. Both commands used the absolute root capped runner and
absolute manifest, a 16 GiB memory cap, a 16 MiB Rust stack, the common lock,
and unchanged `TMPDIR`.

The test command used the clean pinned Go checkout at
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. No upstream update was performed.

| Evidence | SHA-256 |
| --- | --- |
| `target/wave151-root-workspace-tests.log` | `35f2c5696b59039f434fa6a69e7ac7d93ac2c6fb1f8b3e6af4f500fa49c0f222` |
| `target/wave151-root-workspace-format.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `docs/typechecker-wave151-root-workspace.json` | `cad702d397b1f8b0c80ba0128c9b9f01160fce055b6bca1ac34bc95b8f676da6` |
| Root capped runner | `2175054c4a3f2bfaf5d441e3671db766fa9bc064180755678ffe0a13da547803` |

## Next source and limits

Separate candidate `ebe995e1` contains the class/namespace source changes and
merged-owner checks. Its full-workspace test and format commands are still
queued. This report does not give that candidate pass credit.

No primary promotion, new full-corpus result, modern-project success, benchmark,
strict Clippy pass, or upstream roll-forward is claimed. The complete port
goal and the two independent merged-export reviews remain active.
