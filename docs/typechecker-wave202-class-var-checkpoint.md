# Typechecker checkpoint after class-local variable support

Code checkpoint: `9941d93f1c3c17e7da096d70d12d791ff610231f`.
Branch: `july-ultra`. Recorded on 2026-08-30.

The class-local variable batch passed its gate. Both original upstream collision
cases now match diagnostics, types, and symbols. The unchanged fixed diagnostic
selection gained those two passes. Every prior exact record and artifact remains
exact.

## Verified results

These groups overlap. Do not add them to get a unique test count.

| Check | Result |
| --- | --- |
| All checker unit tests | 4,782 passed, zero failed, ignored, or filtered |
| Four complete public test targets | 32 passed, zero failed, ignored, or filtered |
| Two original upstream cases | Both diagnostics, type artifacts, and symbol artifacts exact |
| Fixed diagnostic selection | 422 exact of 511 executed variants, 89 unsupported, zero supported mismatches or fatals |
| Fixed semantic selection | 58 exact of 95 executed variants, 33 unsupported, four retained fatals, zero supported record mismatches |

Formatting, both fixture executable builds, and strict workspace Clippy with
all targets and `-D warnings` passed. The public targets were
`source_class_bodies`, `source_class_polymorphic_super`,
`source_class_second_wave`, and `source_class_var_bindings`.

Compared with the retained `e7e6931b` corpus baseline, diagnostic exact results
increased from 420 to 422. Only these records changed:

- `collisionSuperAndLocalVarInConstructor.ts`
- `collisionSuperAndLocalVarInMethod.ts`

Both original cases were also checked separately with full diagnostic, type,
and symbol artifact comparison. Their original `target=es2015` inputs and
expected artifacts were unchanged. Emit comparison and a fresh Go diagnostic
replay were not run.

The semantic selection is unchanged: 53 exact type artifacts, 60 exact symbol
artifacts, and seven existing symbol-artifact mismatches. Each fixed selection
retains one upstream skip outside its executed count. No prior exact result was
lost, and no new fatal record appeared. Diagnostic and semantic stages took
676 and 126 seconds respectively.

## Scope and remaining work

This is a selected corpus, not the full upstream suite or a modern-project pass.
It does not establish Go project parity. The implementation goal remains active.
Unverified batches remain separate and are not covered by these results.

The full workspace was not rerun at this checkpoint. Its historical run at
`9a4adc50b2689390bbbbdcb748bbd55bf34f253c` remains recorded as 8,073 passed and
two failed across 284 completed targets. This successful checker gate does not
replace that historical result.

## Evidence and cleanup

The measured clean source fingerprint was
`b6369572e68db4f6811424139756088523a581bf9a7d862cd9a8374774cc352d`, before these
documentation files were added. Source, input, manifest, bundled-library, runner,
and binary identities remained unchanged throughout the measurements.

The first corpus launch was blocked by sandbox access to the user service bus
before Cargo started. Its absent service was confirmed and its output preserved.
One identical retry ran outside the sandbox. Both completed corpus services were
confirmed absent and inactive with empty control groups. The target lock was
released. Gate and original-case service cleanup also passed.

The [JSON record](typechecker-wave202-class-var-checkpoint.json) contains the
exact commits, pins, paths, report hashes, input hashes, binary hashes, and wrapper
hashes. Local evidence:

- [Gate summary](../target/wave202-class-var-bindings-1-summary.txt)
- [Original-case result](../target/wave202-class-var-original-1/result.txt)
- [Fixed-corpus comparison](../target/wave202-class-var-corpus-1/comparison.json)
- [Pre-execution cleanup record](../target/wave202-class-var-corpus-1-preexecution-blocked/cleanup-note.txt)

The [previous checkpoint](typechecker-wave202-next-checker-checkpoint.md) is unchanged.
