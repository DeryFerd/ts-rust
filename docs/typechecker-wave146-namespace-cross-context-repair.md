# Namespace display across source files

The original cross-source display failure is fixed. All 4,410 selected tests
pass on the combined source. Independent invariant review found no new scoped
issue. Final Go-semantic review remains pending. This is not primary promotion
or approval of the separate heritage recovery failure.

## Source

- Base: `9eb75a716d18d75f1c8cf8d1be9553ddbc4242af`.
- Original probe: `0049d7375277020fdd3879871a17d5d2b0fce008`.
- Unchanged probe import: `592b5b75`.
- Tested repair: `3b956761268210e9cfb2db45b76bf6ca73a49e8e`.
- Worktree: `target/agent-worktrees/wave146/root-namespace-cross-context`.
- Branch: `root/wave146-namespace-cross-context`.

The source stayed clean and fixed during the test run. Only `formatter.rs`
changes in the repair. The original public probe is byte-identical to its
review version. No original test, fixture, or baseline was changed.

## Fix

When the originating import alias is absent from the caller's value scope,
the old formatter asked the bare source module for a visible name. A caller's
bare import could then name the requested wrapped type. Those types have
different identities and different default members.

The wrapped fallback now uses the caller's checked module specifier directly.
It keeps the existing wrapper/source validation and uses the visible originating
alias when that alias is valid. Location-free display is unchanged.

The small import-spelling helper is shared with the existing symbol writer.
It keeps quote flags and display-length accounting. No type, symbol, source,
export, or cache producer changed. The added unit checks double and single
quotes before and after replay, while the bare view keeps its own alias name.

## Tests

Session `15814` exited 0. The build took 2 minutes 1 second. All 17 test
binaries passed, with no failures, ignored tests, or filtered tests.

| Group | Passed |
| --- | ---: |
| Checker units | 3,937 |
| Compiler units | 258 |
| Fixture units | 164 |
| Public controls across 14 targets | 51 |
| Total | 4,410 |

The test-name comparison retains all 4,408 prior controls. Its only additions
are the cross-source public probe and the quote-flags unit. The old owner-loss,
source-owner, alias-shadowing, namespace, heritage, and artifact controls pass.

The run used the root capped Cargo script, an absolute manifest, locked offline
dependencies, 16 GiB memory, 16 MiB process and Rust stacks, the common lock,
unchanged TMPDIR, and the unique target
`target/worktrees/wave146-root-namespace-cross-context`.

Log: `target/wave146-namespace-cross-context-tests.log`.
SHA-256: `8b4073199f7e7c5caa6e07dbeae3cde6b5dcc620ef01a21eba498cb8fa1eb347`.
Formatter SHA-256: `15052c52230048daf8826430ae2a41c865c7f50e6db71a28bf2ee6c5cf63bb5c`.
Public probe SHA-256: `e46f97198a28b3c0882d05327c822ef88d13f97ccc75e289967b265845a4d8d5`.

## Review and limits

Invariant review `aa7e56cca932df5784a3ab8b28f24aa31b5f4781` found no new scoped
blocker. The separate final Go review checks additional source contexts and
flags. Its result is not claimed here.

The earlier smoke on clean `9eb75a71` has 52 exact results, 42 unsupported
results, one artifact mismatch, and no fatal failures across 95 executions.
All 52 previous exact rows match. That smoke predates this fix and was not
relabeled. No new full-workspace, strict Clippy, or frozen-corpus result is
claimed. The heritage recovery P1, full port, and primary promotion remain open.
