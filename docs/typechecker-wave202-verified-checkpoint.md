# Typechecker checkpoint after core and source integration

Code checkpoint: `028ae027dd5f03aee750d30cd8e9151986b8a34b`.
Pinned Go: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

This code is on `july-ultra`. The retained upstream selections improved without
losing any previously exact result. No full modern-project pass is claimed.

## Verified results

The groups overlap. Do not add them to get a unique test count.

| Check | Tested commit | Result |
| --- | --- | --- |
| Full workspace | `1e7e140b` | 8,014 passed, zero failed or ignored, 281 target summaries |
| All checker unit tests | `028ae027` | 4,737 passed, zero failed, ignored, or filtered |
| Fixed diagnostic selection | `028ae027` | 419 exact, 92 unsupported, zero supported mismatches, zero fatal in 511 executed variants |
| Semantic selection | `028ae027` | 57 exact, 33 unsupported, zero supported mismatches, five retained fatals in 95 executed variants |

Both selections retain the same one upstream skip. The full workspace was not
rerun after the final mapped-type and formatter additions. The final checkpoint
passed formatting and strict workspace Clippy with all targets and `-D warnings`.

The full workspace check also passed both generated AST checks and built both
fixture executables. It included 4,721 checker units and 285 compiler units.

## Exact results gained

Against the retained wave201 reports:

- `bindingPatternContextualTypeDoesNotCauseWidening.ts` changed from a fatal
  diagnostic check to an exact match.
- `functionExpandoPropertyDeclaration.ts` now matches its full semantic baseline.
- `accessOverriddenBaseClassMember1.ts` now matches its full semantic baseline.

The diagnostic exact count increased from 418 to 419. The semantic exact count
increased from 55 to 57. Exact type artifacts increased from 50 to 52. Exact
symbol artifacts increased from 59 to 60.

All 418 prior exact diagnostic records and all 55 prior exact semantic records
remain exact. Each previously exact type or symbol artifact also remains exact.
The comparison reports no new fatal or unknown outcome. The five retained
semantic fatal results remain open defects.

## Modern projects

The original React Hook Form app still stops during source construction.
The measured failure is `E00.SOURCE_SYNTAX` in React's `global.d.ts`, at
`FileId(146) NodeId(70)`, an interface declaration. The program graph, checker
results, and forced replay are unavailable. This is not a diagnostic match or
a successful project check.

This app run used the original config and 45 source roots, including 44 TSX
files. It had no compiler-option override. Queue, build, and execution took
76 seconds under the unchanged 300-second deadline. The oracle used 17,908 ms
and reached 582,096 KiB peak RSS.

The separate React Hook Form library run on `e262c08d` remains blocked by its
unannotated filter callback in `createSubject.ts`. Source inspection proved
that the reported Node131 is the callback parameter `o`. The callback is the
right-hand side of a captured-local assignment. A separate fix is in progress.

Neither run proves parity with Go. No complete Zod pass is claimed.

## Work that is not included

The following separate candidates do not contribute to the counts above:

- Ordinary interface properties without type annotations. Its focused tests
  and strict checker Clippy pass at `6eda9f69`.
- Callback inference inside captured-local array assignments.
- Generic remapping of still-deferred conditional types.
- Lazy type-only imports of declared functions.

The next independent work covers React's merged interface declarations, mapped
declarations nested under indexed access, and the retained fatal test results.
Concrete conditional evaluation and broader mapped member checking remain open.

## Parallel execution

Each implementation worker has a separate worktree and a fixed file list.
One integrator combines reviewed changes. A test run freezes its whole source
worktree until the run and its service close.

Up to three capped Cargo jobs can run at once. Each job keeps a 16 GiB memory
limit, no swap, one Cargo worker, one test worker, and the existing target locks.
Source analysis and review can proceed while those jobs run. No test deadline
or resource cap was raised to accept this checkpoint.

## Evidence

The companion [JSON record](typechecker-wave202-verified-checkpoint.json)
contains the exact commits, source fingerprint, selection identities, and
report hashes.

Full logs remain in the local workspace:

- `target/wave202-combined-core-source-full-1-*`
- `target/wave202-combined-features-1-*`
- `target/wave202-combined-corpus-1/`
- `target/wave202-rhf-app-combined-features-1*`

All original test sources, options, library files, baselines, and selected
variant keys stayed unchanged. Source and input identities matched before and
after each accepted run. Each service closed with no remaining control group.
