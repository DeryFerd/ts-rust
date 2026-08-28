# Combined root workspace result

Tested source: `ebe995e1cd7c342ebb7c89fc8ca66600f7ef9715`.
Source tree: `7e2e67f2661ac28156cbaf127853c6aef9af4710`.
All 6,811 workspace tests pass. Formatting passes. The full port remains open.

## Scope

This source combines namespace constructor identity, typed artifact errors,
class source and private-artifact support, class/namespace source dependencies,
and the root merged-owner export check. It retains the earlier direct-export
checks and interface-heritage recovery.

| Change | Root checkpoint |
| --- | --- |
| Namespace constructor and preserved display limit | `c734437d`, `837c6207` |
| Typed artifact error classes | `91c16a21` |
| Complete tested class delta from `0efdd881..e07fc2f8` | `33081c24` |
| Class/namespace source and alias dependencies | `46cc9aef`, `ecb15a12`, `0af54f63` |
| Merged-owner export validation and seven-case control | `ebe995e1` |

The class delta retains zero-context patch ID
`182b307679de22c1bc8019eb38115a3bb6b13352`. At the class import checkpoint,
35 of its 37 files matched the tested class source. The two shared files also
retained the root's newer callable recovery and store changes.
The later class/namespace imports retain both the class
assignment planner and the incoming value planners. Only an import list needed
adaptation. No broad parent history was merged.

## Measured checks

Session `96705` ran the complete workspace with `--locked --offline --workspace
--no-fail-fast`. It exited 0. All 164 test binaries and 32 documentation groups
completed. There are no failed, ignored, measured, or filtered tests.
Session `21361` ran `fmt --all -- --check` and exited 0 with an empty log.
Both sessions are collected. Source stayed fixed and clean throughout them.

Both original class/namespace cases now pass through source checking and their
unchanged type/symbol identity assertions. The new seven-case control rejects
changed merged flags, value declaration, declaration order and missing namespace
state before returning a planted type cache. Repeated rejection leaves query
state unchanged, and every restoration returns the healthy identities.

The adjacent JSON verifies each section's named-test count against its summary.
It compares this run with all 6,678 previous workspace names and the earlier
4,431-name root selection. Every missing name has an explicit passing
replacement. There is no unaccounted missing test.

## Changed test names

Five names changed in the imported feature work. This is not a claim that all
old bodies and inputs are identical.

- The constructor-body test keeps all three original sources. It now checks
  their supported results, exact TS2377 diagnostic and stable replay identities.
- The binder static-block test keeps its original source. It now requires an
  incomplete block with no start node and `CrossContainerFlowEffects` after
  the unsupported outer flow, rather than reporting a generic static-block gap.
- The JavaScript class-expando negative test changes its inputs to unsupported
  array and arrow values. Numeric expandos and static `super` have separate
  positive coverage in `source_class_bodies.rs`.
- The compiler class-method test keeps its original files and checks supported
  methods without losing earlier diagnostics. Its separate unsupported
  construction control remains.
- The artifact-error test keeps both original symbol-display cases and adds
  typed missing, unsupported and fatal query/display cases.

The JSON records each exact old and new name and its reason. All replacements
ran and passed. The 6,673 unchanged prior names also ran and passed.

## Build evidence

Worktree: `target/agent-worktrees/wave151/root-namespace-artifact-composition`.
Target: `target/worktrees/wave151-root-namespace-artifact-composition`.
The target was absent at setup and immediately before the first command.
No build artifact or fingerprint was copied, reflinked, hardlinked or seeded.

Both commands used the absolute root capped runner and absolute manifest,
16 GiB memory, a 16 MiB Rust stack, the common lock and unchanged `TMPDIR`.
Tests used the pinned Go checkout at
`dc37b5249ab60e2bbce936f71b883e6c8136167e`. No upstream update occurred.

| Evidence | SHA-256 |
| --- | --- |
| `target/wave152-root-workspace-tests.log` | `49c5474bfc8c4a281f229ab67acce04810548006fa014be2831dc31958721a5f` |
| `target/wave152-root-workspace-format.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `docs/typechecker-wave152-root-workspace.json` | `a58e41e250c39874371deff5d087050b2a619ecea26f02e8a0a5ce1548e58865` |

## Remaining work

The separate merged-export invariant and Go/source reviews remain pending.
This workspace pass does not resolve a later finding from those reviews.
The idle successor `69e6d9c4` also contains the independently verified constructor
span and property/index changes. It has no combined runtime result yet.

No primary promotion, strict Clippy pass, full corpus parity, modern-project
success, performance result or controlled upstream roll-forward is claimed.
The full port goal stays active.
