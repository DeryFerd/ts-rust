# Namespace alias view invariant review

No further source-level invariant issue was found in follow-up `3a336ec7`.
It closes the parent check missed by `c05d045c`. Root's follow-up gate remains
pending. The added public scope probe passed on `c05d045c`. These results are
separate. No production code was authored in this review.

## Previous failure

P1: Reject wrapper parents before a direct symbol chain can return.

The guard in `symbol_display.rs:1353` is inside `validated_parent`. The caller
at `symbol_display.rs:249` reaches it only when no accessible chain exists or
qualification is needed. A direct chain returns at `symbol_display.rs:286`
without that check.

Root's unchanged new test,
`namespace_wrapper_symbol_chains_keep_source_ownership`, fails at
`formatter.rs:11703` in its combined run. The source trace identifies the
second mutation, which gives the source export `value` a wrapper parent. The
artifact helper passes `SymbolFlags::NONE`, so the local value parameter does
not force qualification. The source module's accessible export returns before
the guard. Giving the wrapper itself a parent is already rejected by the exact
wrapper proof.

Root's `3a336ec7e033a4f0faef83715efbdf84e6908997` moves the same rejection into
`validate_symbol`, before any accessible-chain lookup. The genuine-wrapper
branch still checks its exact no-parent record. All other source symbols now
receive the wrapper-parent check before they can return a direct chain.
`validated_parent` calls `validate_symbol`, so its removal of the later copy
does not remove the check. No test, formatter input, or producer changed.

This covers the failed case by source inspection. The root test is unchanged.
Wrapper exports retain raw source symbols, generated properties have no parent,
and the generated default alias has the raw module as its parent. The early
check does not reject any of those valid owners.

## Fixed source

- Candidate: `c05d045c4a5351d796da1be9951d1e76e62b9445`.
- Follow-up reviewed: `3a336ec7e033a4f0faef83715efbdf84e6908997`.
- Before-fix source and original probe: `03c26a34be2c0dad44140b5d424f975bd7d2639e`.
- Added probe: `768242ba787ae7b2710cd799bb15f489fce6ea30`.
- Branch: `agent/wave147-namespace-alias-view-invariants`.
- Worktree: `target/agent-worktrees/wave147/namespace-alias-view-invariants`.

The probe worktree kept `c05d045c` production code for the entire test run.
The follow-up was reviewed from its exact Git diff and root's fixed worktree.
The quote-flags test from `3b956761` is unchanged. Both original public probes
have the same Git blobs in their original commits and both candidates:

| Probe | Original commit | Git blob |
| --- | --- | --- |
| Cross-source wrapped and bare display | `0049d737`, imported as `592b5b75` | `a9d24b4afcc49653aad61bc7705728f945d9ed0f` |
| Renamed alias for the same wrapper | `03c26a34` | `fe8d3f8ebeda0c2cf2cbffe2d4784181fda0a704` |

## Identity and ownership

`symbol_display::validate_symbol` returns the wrapper symbol, not its raw
module. It rejects a merged wrapper and requires
`source_file_namespace_wrapper_is_exact`. That proof checks the retained raw
module, origin alias, import, wrapper, export entries, generated default, and
immediate and final alias links. It also checks the retained source declarations
and both wrapper lookup maps. Validation then checks the raw module and origin
alias against the source host.

`same_reference` still compares merged symbol IDs. It does not compare names,
source paths, declarations, or export tables. A bare module or another import's
wrapper therefore cannot name the requested wrapper. An alias to that exact
wrapper can name it. No type or symbol producer changed.

The formatter's visible-origin path still compares the resolved value symbol
with the exact origin alias. Its fallback passes the wrapper to `symbol_chain`.
Only the final external-module file-spelling step maps a wrapper to its raw
module. Alias selection, chain identity, and quote selection stay separate.

## Failed reads

The changed validators and formatter functions take immutable store references.
They do not allocate types, symbols, relations, or checker links. Scope creation
can still resolve alias links. Both public entry points,
`type_to_string_at_location_with_flags` and `symbol_to_string_at_location`, wrap
that work in `with_display_alias_transaction`, which restores the full alias
checkpoint after an error. Existing tests cover changed origins, aliases,
owners, cached types, and cold visible or nested aliases.

The private `artifact_symbol_chain` helper has no separate transaction. Its new
root test runs after alias warm-up. This review does not claim that a cold direct
call to that helper leaves alias caches unchanged. The public caller owns that
guarantee, and this commit does not change that boundary.

## Added probe

The added `canonical_namespace_wrapper_alias_scope_invariants.rs` test uses a
renamed alias, `routed`, to the requested wrapper and a distinct direct wrapper
named `ns`. That second import reuses the origin alias's spelling. All 48
location-aware calls pass, across four flag combinations and both replay states:

- The origin uses `typeof ns`.
- The same-owner renamed alias uses `typeof routed`.
- A type parameter named `routed` does not hide the value alias.
- A value parameter named `routed` forces checked import spelling.
- The distinct wrapper keeps `typeof ns` in both caller scopes.
- The two wrappers stay distinct from each other and from their shared bare
  default. All retained types, plain displays, store ID, and diagnostics survive
  replay unchanged.

The flags cover no truncation, single quotes, aliases outside the current scope,
and both optional flags together. The probe does not change either original
public test.

## Evidence

Root's saved baseline log, `target/wave147-namespace-alias-before.log`, shows the
unchanged `03c26a34` probe failing on the before-fix source. It reports missing
module specifiers in the caller without a direct import and import spelling
instead of `typeof routed` in the caller with a direct import.

Root collected combined session `81496` with 4,411 passes and one failure across
18 binaries. Only the new ownership unit failed. All 4,410 prior controls and
the new same-owner alias public test passed. The log is
`target/wave147-namespace-alias-fixed.log`. This review did not repeat the batch.

Root's follow-up session `94249` is queued on `3a336ec7`. Its log is
`target/wave147-namespace-alias-parent-fixed.log`. The result is not yet claimed.

The new probe passed in session `29338` on `c05d045c` plus test-only commit
`768242ba`. The session is collected with exit code 0. It ran one test, with no
failures, ignored tests, or filtered tests. After the queue wait, the build took
50.87 seconds and the test took 0.13 seconds. No owned command remains active.

The run used the root capped runner, an absolute manifest, locked offline
dependencies, 16 GiB memory, a 16 MiB Rust stack, the unchanged shared queue,
unchanged TMPDIR, and private target
`target/worktrees/wave147-namespace-alias-view-invariants-1`.

Log: `/tmp/ts-rust-wave147-namespace-alias-view-invariants-scope.log`.
Changed-file rustfmt and the candidate-range whitespace check pass.

SHA-256 values:

- `formatter.rs`: `8206de83ecfdae8fa852bfc47413612f1052a5c2e2b91cc6f1f5e74b76dc20c4`.
- `symbol_display.rs`: `ed0b3deac7171b4dc992f5a18e67495df88453296dfc1e5c054c4e64091ce4f1`.
- Follow-up `symbol_display.rs`: `716816ac578702dc1752b40856fced36b6c92e5bc2feb3c5359159a5aa2eed67`.
- New scope probe: `96dfe88a1353696e7ef872be2c030a457e5d6d6913d2cbbd4b70dfbfd4a76d3c`.
- Before-fix log: `2b5e91f4339f1ae860748d45b4016bc5b9c41387486a5afb727fdcaacf8fce66`.
- First candidate combined log: `12eed3191732c8d0327400ee67564436c2f9c9a7b2e4237a7c004ea67b0d6e62`.
- New scope probe log: `d16085f40546eadc4ebd759d89aae415574be2f3dcbdff9f083d1a7b0bf45b74`.

## Limits

This is a scoped invariant review. It does not claim a new Go oracle result,
full workspace coverage, strict Clippy, full parity, whole-root approval, or
primary promotion. The new 48-call probe was not rerun on `3a336ec7`. Root's
follow-up gate is still required. The separate f265 class/enum hold and the
missing-specifier naming limit remain open. No earlier evidence or baseline
was changed.
