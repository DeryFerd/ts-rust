# Typechecker checkpoint after the next checker batch

Code checkpoint: `e7e6931b7565a295cb3bbf00832e852928365c0d`.
Branch: `july-ultra`.
Recorded on 2026-08-30.

The batch is on the current branch. All 4,782 checker unit tests pass. The
unchanged upstream selections gained one exact diagnostic result and one exact
semantic result. Every prior exact record and artifact remains exact.

These are fixed test selections, not the complete upstream suite. No full
modern-project pass or Go project parity is claimed.

## Changes included

- Generic remapping of deferred conditional types.
- Unannotated interface properties and their type display.
- Null conditional expressions.
- Merged auto-accessor class display.
- Ordered, nongeneric interface bases, including native interfaces.
- Captured array callback checking and contextual return queries.
- Local named type exports.
- Validation of source requests when a conditional type uses a cached result.

## Verified results

The groups overlap. Do not add them to get a unique test count.

| Check | Tested commit | Result |
| --- | --- | --- |
| Full workspace | `9a4adc50` | 8,073 passed, two failed, zero ignored, all 284 targets completed |
| All checker unit tests after repair | `e7e6931b` | 4,782 passed, zero failed, ignored, or filtered |
| Six complete public test targets | `e7e6931b` | 40 passed, zero failed, ignored, or filtered |
| Fixed diagnostic selection | `e7e6931b` | 420 exact, 91 unsupported, zero supported mismatches or fatals in 511 executed variants |
| Fixed semantic selection | `e7e6931b` | 58 exact, 33 unsupported, four retained fatals, zero supported record mismatches in 95 executed variants |

Both upstream selections retain the same one upstream skip. Seven existing
symbol-artifact mismatches remain. Zero supported record mismatches does not
mean that every artifact is correct.

The two full-workspace failures were conditional replay controls. The final
checker run includes both controls, and both now pass. The full workspace was
not rerun at `e7e6931b`. Its earlier failed result remains in the record.

The final checkpoint also passed formatting, built both fixture executables,
and passed strict workspace Clippy with all targets and `-D warnings`.

## Exact results gained

Compared with the previous code checkpoint, `028ae027`:

- `bestCommonTypeWithContextualTyping.ts` is now diagnostic-exact.
- `propertyAndAccessorMerging.ts` is now semantic-exact. Its type artifact now
  matches. Its symbol artifact was already exact and stays exact.

Diagnostic exact results increased from 419 to 420. Semantic exact results
increased from 57 to 58. Exact type artifacts increased from 52 to 53. Exact
symbol artifacts remain at 60. Semantic fatal results decreased from five to
four.

The comparison found no lost exact record, lost exact artifact, new fatal
record, or unknown outcome. `bases.ts` moved past its interface declaration,
but still stops at a class declaration. It is still unsupported, not a pass.

## Modern projects

The original React Hook Form app, React Hook Form library, and Zod runs remain
incomplete. Their latest separate measurements are not full runs of this
combined checkpoint.

The React Hook Form app stops during merged global interface construction.
The next repair must preserve the actual merge order and authenticate external
`declare global` contributions. The existing ordered-base change is included
here. The global augmentation repair is separate.

The React Hook Form library reaches a relation failure involving its
`Subscription` type. A focused three-file test proves that the direct imported
`Noop` return path works. The failing operation in the original project still
needs to be identified. Healthy type metadata alone does not identify it.

The latest clean Zod run stops at an import in the original `vitest.config.ts`.
Existing ambient export-star work has been recovered in a separate worktree.
Its type-only function-import dependency is paused after two automatic
permission-review timeouts. It is not part of this checkpoint.

No project source, config, compiler option, bundled library, or expected
baseline was changed to obtain these results.

## Next parallel work

The next batch has separate owners for:

- Conditional source captures and their relation checks.
- Cached mapped lookup validation.
- Source-backed index-signature type display.
- Union property symbol display.
- Native global interface augmentation.
- The actual React Hook Form relation failure.

Mapped member evaluation is the next shared dependency. The first control uses
the real `RequiredKeys`, `Validator`, and `IsOptional` declarations. It must
produce the key for a required property, `never` for an optional property, and
a deferred result for an unresolved input. It must use the existing conditional
evaluator and the actual source branches.

Implementation workers use separate worktrees and fixed file ownership.
Source analysis and review continue while up to three capped Cargo jobs run.
Each test run freezes its whole source worktree until all stages and services
close. No deadline or resource cap was raised for this checkpoint.

## Evidence

The [JSON record](typechecker-wave202-next-checker-checkpoint.json) contains the
commits, source fingerprint, input pins, counts, and report hashes.

Full local evidence remains at:

- `target/wave202-next-checker-integration-1-*`
- `target/wave202-next-checker-integration-2-*`
- `target/wave202-next-checker-corpus-1/`

The previous [checkpoint](typechecker-wave202-verified-checkpoint.md) remains
unchanged. The implementation goal is active.
