# JavaScript JSX type-argument recovery

The unchanged `jsFileCompilationTypeArgumentSyntaxOfCall.ts` fixture now matches
its complete pinned `.errors.txt` artifact. The base produced seven diagnostics.
The repair produces all ten expected diagnostics with no comparison mismatch.

Base: `0daa6583e8b28213704c95f1c80ebfe6dbaf418e`.
Pinned Go: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
Pinned TypeScript: `c3bd12d888b86f676718b16e64d7d2abcb423514`.

## Change

JavaScript expression parsing now keeps `<` and `>` as relational operators
instead of consuming TypeScript type arguments. An unexpected `<` in JSX
attributes reports TS1003 and remains available for recovery. JavaScript binary
expression parsing reuses the existing adjacent-element recovery loop.
The existing JSX attribute initializer uses the same extracted loop.

TypeScript and TSX type-argument parsing remain unchanged. No scanner code,
byte API, compiler diagnostic filter, fixture, baseline, or comparator changed.

## Verification

The original case is under `_submodules/TypeScript/tests/cases/compiler`.
Its variant key, options, baseline path, and input hashes are unchanged.
The comparison selects one case and executes one variant with
`status: exact_match` and `comparisonScope: full_artifact`. All header-only,
code, span, message, order, header, artifact, and fatal mismatch counts are zero.

| Session | Result |
| --- | --- |
| `6393` | Five focused parser tests pass, exit 0 |
| `96813` | 22 existing JSX parser tests pass, 223 filtered, exit 0 |
| `62291` | Fresh own-target fixture runner builds, exit 0 |
| `74798` | Complete original error artifact matches, exit 0 |

The focused tests check JavaScript relational AST nodes, TypeScript generic
calls and tagged templates, TSX generic elements, all ten original error spans,
valid JSX and unary expressions, and unchanged JavaScript and TypeScript
signature ranges with semicolons and automatic semicolon insertion.

## Evidence

Worktree: `target/agent-worktrees/wave167/javascript-jsx-type-arguments`.
Evidence: `target/review-jsx-type-arguments` within that worktree.
`validation.json` records the exact result and unchanged variant identity.
`progress.json` records the completed commands with no pending runs.

The worktree's physical Cargo target started absent. No build artifacts or
fingerprints were copied or seeded. Only the root's baseline JSON was copied.
Cargo used the absolute root capped runner, absolute manifest, locked offline
dependencies, shared build lock, 16 GiB memory, and 16 MiB stacks. Direct fixture
execution used the shared diagnostics lock.

| Evidence | SHA256 |
| --- | --- |
| `before.json` | `4acd37785567ea09b88e5d4702e40aae5dc3fb4e5b755adb545d0f11a6f1706a` |
| `after.json` | `b3c0b12e489773271706f458156c9083a8ea75066e473c056b5217ff88ecd1de` |
| `tests-1.log` | `49e174970a61e31d02d98a44faf3c03dcbfd95a61f418e86095da28562103041` |
| `jsx-controls-1.log` | `099192fd63d961723958367422e0ec5db8b00340bb2cc7fc8a86b97817d298d4` |
| Repaired fixture binary | `454936ce238e1ef9548d55f55cfdda53808ca6c8650b582ed982f8b32c09d0b0` |

Formatting, whitespace, and frozen source-input checks pass. Both pinned upstream
checkouts are clean. No root merge or broad parser compatibility claim is included.
