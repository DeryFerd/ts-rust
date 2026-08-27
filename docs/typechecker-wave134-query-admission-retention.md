# Admitted module target integrity

Follow-up to `933cf8b6f002b57ed27d38eda9025b61cbe4e3f2`.
Runtime guard: `22d9dea4`. Test correction: `162c6565`.

## Problem

The module manifest could classify a damaged file index as an intentional
JavaScript omission. An import can exceed the dependency depth limit even when
its target was admitted as an explicit root or through a later relative import.
Removing that target's index entry then returned `M00.OMITTED_MODULE_TARGET`.
The correct result is the fatal `INV.PROGRAM.MISSING_MODULE_TARGET` error.

## Change

Before using the omission path, the manifest now checks the retained
`source_files` list. It uses the same path canonicalization and case-sensitivity
setting as the file index. A retained target proves actual admission, regardless
of the current import's depth policy.

The check is read-only. It does not reconstruct an index entry, repeat module
resolution, change raw resolver results, or add a second admission cache.
Targets that were not admitted still require the exact saved resolver edge and
a supported omission reason. Ambient target selection is unchanged.

## Controls

The existing missing-target test now includes a JavaScript target that is both
an explicit root and a package import with depth limit zero. It confirms that
the source was retained at depth zero before removing its index entry.

A second test first omits a package import at depth two with limit one. A later
relative import admits the same target at depth one. The original source's
edge still exceeds the depth limit. Removing the target index must remain
fatal in this case too.

Both controls confirm that validation leaves raw resolutions unchanged. They
also check that validation does not restore the missing index entry.

## Validation

The final run for `162c6565` passed 297 selected compiler tests, including 230
unit tests and 67 integration tests. Both corruption controls passed. The
workspace formatting check and strict compiler Clippy with all targets passed.
The Rust source remained unchanged during these final checks.

The first compiler run passed 229 unit tests, including the requested root
corruption control. The added later-route fixture failed because a direct
path under `node_modules` is still an external dependency. Its initial
depth-zero setup could not admit the target. The test-only correction uses
the two routes described above. It also applies the formatter's requested
layout. The runtime guard is unchanged.

The first strict Clippy run also passed. Both sets of logs remain available.

## Input evidence

The read-only prepared-input verifier checked 134,010 files and 10,348 links
before and after the compiler checks. Both new reports are byte-identical to
the prior final report. All have SHA-256
`c81ef4fbf7e328f5ebad36fc07bc5b05a845134fd6852d4530833424d78525de`.

New evidence is in `target/project-evidence/query-admission-retention-wave134`.
The final test log is `compiler-tests-2.log`, with SHA-256
`7efa2c9ef565ef1358228a11c58d751894f30f94281be9746c3aa6884475437d`.
The final Clippy log is `clippy-2.log`, with SHA-256
`0f6177427f94f07fb0bd6c5869c76f11f3c5fed6b419ef884ad8011af104985f`.
The successful formatting check produced an empty `fmt-2.log`.

The reviewed Query worktree, source-scope provider, and older evidence are
unchanged. The prior real-project result remains the arrow error in
`timeoutManager.ts`. This follow-up does not claim full project checking.
