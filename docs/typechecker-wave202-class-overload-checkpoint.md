# Typechecker checkpoint after class overload work

Recorded on 2026-08-30. Primary merge: `8f4943ac`.
Measured source: `5c7c7bd2`.

The original `ambiguousCallsWhereReturnTypesAgree.ts` case now matches its
complete diagnostics, types and symbols. All prior exact results remain
unchanged. No new fatal record appeared.

## Original corpus results

Both fixed selections used the original sources, options, libraries and
expected artifacts. The comparison used accepted source `e0ede993`, not the
earlier rejected class overload run.

| Selection | Executed variants | Previous exact | Current exact | Unsupported | Fatal |
| --- | ---: | ---: | ---: | ---: | ---: |
| Diagnostics | 511 | 422 | 423 | 88 | 0 |
| Semantic artifacts | 95 | 59 | 60 | 32 | 3 |

Each selection also has one unchanged upstream skip. Both have zero supported
record mismatches and zero unknown results. The selections overlap. Do not add
their counts to get a unique case count.

Exact type artifacts increased from 54 to 55. Exact symbol artifacts increased
from 61 to 62. Seven existing symbol-artifact mismatches remain. The three
semantic fatal records retain their complete previous payloads.

Independent review compared complete raw records, not just success labels.
All 422 prior exact diagnostic records, 59 prior exact semantic records,
54 exact type artifacts and 61 exact symbol artifacts stayed unchanged.

The one new exact case uses the original `target=es2015` variant. It includes
both classes, their overload groups, hidden implementations and both calls.
The comparison covers the whole type and symbol files. `bases.ts` stops at a
different class check but remains unsupported. It adds no pass.

## Quality checks

These checks ran on measured source `5c7c7bd2` before the corpus replay.

| Complete test group | Passed | Harnesses |
| --- | ---: | ---: |
| Original class overload fixture | 1 | 1 |
| Checker units | 4,839 | 1 |
| All checker public targets | 677 | 110 |
| Compiler units | 285 | 1 |
| Fixture library | 188 | 1 |
| Fixture binaries | 4 | 2 |
| Retained fixture integration targets | 61 | 4 |
| Total | 6,055 | 120 |

All test groups had zero failed, ignored, measured or filtered tests.
Formatting, strict workspace Clippy with all targets and both fixture binary
builds passed. All ten quality services and both corpus services closed.
This is the listed quality check, not every workspace package's test suite.

## Primary source and limits

The primary merge preserves the measured candidate's complete source and test
bytes. Its only additional files are the two older core-query checkpoint
documents. Root verified the expected merged tree before committing it.
The tests ran on `5c7c7bd2`, not on the later merge or documentation commit.

This checkpoint covers two selected corpora, not the entire upstream suite.
It does not establish a full modern-project pass or Go project parity.
Other integration branches still have failures and are not part of this
accepted checkpoint. More workers have completed useful fixes, but the
available measurements do not prove a higher rate of accepted upstream passes.

The [JSON record](typechecker-wave202-class-overload-checkpoint.json) keeps
source, merge, input and evidence identities separate. Local evidence:

- [Quality review](../target/wave202-core-class-call-integration-2-review.md)
- [Independent corpus review](../target/wave202-core-class-call-corpus-2-review.md)
- [Full corpus comparison](../target/wave202-core-class-call-corpus-2/comparison.json)
- [Primary merge preflight](../target/wave202-core-class-call-primary-promotion-preflight.md)

The [previous checkpoint](typechecker-wave202-core-query-checkpoint.md) and
all older checkpoint documents remain unchanged.
