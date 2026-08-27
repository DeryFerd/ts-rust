# Namespace alias view repair

Tested source: `3a336ec7e033a4f0faef83715efbdf84e6908997`.
Root session `94249` finished with exit code 0. All 4,412 selected tests pass.
The worktree stayed clean at that source until the command was collected.

## Change

The original probe `03c26a34` uses a renamed import of the same namespace
wrapper. It checks separate wrapped and bare identities, diagnostics, and
replay before comparing the display. All four display checks fail on the
unchanged source. Callers without a direct producer import report
`MissingModuleSpecifier`. Callers with another direct import use an import
expression instead of `typeof routed`.

Commit `c05d045c` gives the existing symbol-chain query the genuine wrapper
identity. Only the final file-spelling step uses the wrapper's source module.
It does not use a bare module or a different wrapper to select an alias.

That first repair passes the public probe but fails its new ownership test.
A direct visible name can return before the late parent check. Commit
`3a336ec7` moves the same check into `validate_symbol`, before alias lookup.
The original test and assertions are unchanged. Source declarations cannot
acquire a namespace wrapper as their parent.

## Verification

The combined command uses the same libraries and public targets as the prior
namespace run, plus the unchanged renamed-alias probe. It has 18 test binaries.

| Group | Passed |
| --- | ---: |
| Checker units | 3,938 |
| Compiler units | 258 |
| Fixture units | 164 |
| Public controls | 52 |
| Total | 4,412 |

There are no failed, ignored, or filtered tests. A test-name comparison retains
all 4,410 names from the previous cross-source repair. It adds only the new
ownership unit and the renamed-alias public probe. All 4,412 names from the
first candidate run are present. Its one failure now passes.

The command uses the root `scripts/run-cargo-capped.sh`, an absolute manifest,
locked offline dependencies, a 16 GiB memory limit, a 16 MiB Rust stack, the
shared build lock, and unchanged `TMPDIR`. Its target belongs only to this
physical worktree:

```text
target/agent-worktrees/wave147/root-namespace-alias-view
target/worktrees/wave147-root-namespace-alias-view
```

The compiler build reports 1 minute 53 seconds. Queue wait is not build time.
The candidate range passes `git diff --check`.

## Independent reviews

Semantic review `7cac087f` reuses the pinned Go flag probe. It checks 19 values,
four flag combinations, cold and warm calls, and 12 identity relationships.
It approves only the measured alias naming and source behavior.

Invariant review `537ec1b1` checks `3a336ec7` and the early parent rejection.
Its separate scope probe `768242ba` passes all 48 formatting calls on
`c05d045c`. That probe was not rerun on `3a336ec7` in this command.
The full root command supplies runtime evidence for the unchanged ownership
test on `3a336ec7`.

## Evidence

| File | SHA-256 |
| --- | --- |
| `target/wave147-namespace-alias-parent-fixed.log` | `f8381e580f7ba4d854cf1967bad60b6e43f6d60c4c5924caddc1c66ab7618457` |
| `formatter.rs` | `8206de83ecfdae8fa852bfc47413612f1052a5c2e2b91cc6f1f5e74b76dc20c4` |
| `symbol_display.rs` | `716816ac578702dc1752b40856fced36b6c92e5bc2feb3c5359159a5aa2eed67` |
| `canonical_namespace_wrapper_alias_view.rs` | `a0a1223c9bf8d06c0fefaa78185649f9c8726b90d1858d1f268532b5f050a0e3` |

## Remaining work

This result does not clear the separate export-equals class and enum finding
in `f265222b`. Its repair `9ca7dffb` still needs independent review and root
composition. Compiler relative-specifier generation remains separate work.

The latest completed semantic smoke is still `ba41ed3a`: 53 exact results,
41 unsupported results, one artifact mismatch, and no fatal result across
95 executions. This report does not relabel that smoke as a `3a336ec7` result.
Full corpus parity, fresh replay, and primary promotion remain incomplete.
