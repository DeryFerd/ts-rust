# Typechecker checkpoint after core query work

Recorded on 2026-08-30. Primary merge: `6c9ad4f0`.
Measured source: `e0ede993`.

Every non-documentation file in the primary merge matches the measured source.
The measurements below did not run on the merge itself. The JSON record keeps
the full commit IDs, tree ID, and fingerprints separate.

## Verification scope

These groups overlap. Do not add them to get a unique test count.

| Check | Tested commit | Result |
| --- | --- | --- |
| Full checker unit suite | `b83d424b` | 4,825 passed |
| All 106 complete public test targets | `b83d424b` | 654 passed |
| Full compiler unit suite | `b83d424b` | 285 passed |
| Four focused union-display controls | `e0ede993` | 4 passed, 4,821 filtered |

The three full test groups had zero failed, ignored, or filtered tests.
The gate at `b83d424b` ended on one Clippy local-name error. The only change
in `e0ede993` renamed that binding and its sole use. Its delta gate passed
formatting, the four focused controls, strict workspace Clippy with all targets
and `-D warnings`, and both fixture executable builds.

The full checker, public, and compiler test groups were not rerun after the
rename or on the primary merge. The full workspace test suite was not rerun.

## Unchanged fixed corpus

Both selections ran on `e0ede993` with the original inputs, options, and expected
artifacts. The comparison used the accepted class-var checkpoint, `9941d93f`.

| Selection | Executed variants | Exact | Unsupported | Supported record mismatches | Fatal |
| --- | ---: | ---: | ---: | ---: | ---: |
| Diagnostics | 511 | 422 | 89 | 0 | 0 |
| Semantic artifacts | 95 | 59 | 33 | 0 | 3 |

Each selection retains one upstream skip outside its executed count.
All 422 prior exact diagnostic records, 58 prior exact semantic records,
53 exact type artifacts, and 60 exact symbol artifacts remain exact.
No new fatal record appeared, checked by case and variant identity.

Type-artifact exact matches increased to 54. Symbol-artifact exact matches
increased to 61. Seven existing symbol-artifact mismatches remain. Zero
supported record mismatches does not mean that every artifact matches.

Only two semantic records changed:

- `objectSubtypeReduction.ts` now matches diagnostics, types, and symbols.
  This clears the union-order mismatch in the earlier, unaccepted core run.
- `freshObjectLiteralSubtype.ts` now has an exact symbol artifact. Its existing
  prefix-unary type query remains unsupported. It is no longer fatal, but it
  is not a new exact semantic record.

Seven diagnostic cases stop at different checks but remain unsupported.
They add no exact diagnostic passes. The JSON lists those changes and the
three retained semantic fatal records.

## Limits and evidence

This checkpoint covers the two fixed selections, not the full upstream suite.
It establishes no full modern-project pass or Go project parity.
All measured services closed. Fresh checks confirmed `MainPID=0` and
empty control groups for both corpus services.

The [JSON record](typechecker-wave202-core-query-checkpoint.json) contains the
exact source relationship, scopes, paths, and evidence hashes. Local reports:

- [Full tests before the rename](../target/wave202-core-union-display-2-summary.txt)
- [Delta gate](../target/wave202-core-union-display-3-summary.txt)
- [Corpus comparison](../target/wave202-core-union-display-corpus-1/comparison.json)

The [class-var checkpoint](typechecker-wave202-class-var-checkpoint.md) and all
older checkpoint documents are unchanged.
