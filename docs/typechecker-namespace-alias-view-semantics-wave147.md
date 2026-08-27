# Namespace alias view semantic review

Reviewed source: `3a336ec7e033a4f0faef83715efbdf84e6908997`, following
`c05d045c4a5351d796da1be9951d1e76e62b9445`.

No additional display-semantic issue was found in the measured namespace
cases. The source supports same-owner renamed imports without using a bare
module or another wrapper as the requested view. The follow-up also places
the source-parent check before direct-name lookup can return.

This is scoped source approval, not a passed-build claim for `3a336ec7`.
Root's combined gate `94249` is pending. The earlier gate on `c05d045c` had
4411 passing tests and one failing ownership unit. Its result is preserved
below, not relabeled as a pass.

## Ownership finding and follow-up

The `c05d045c` gate failed
`namespace_wrapper_symbol_chains_keep_source_ownership` at
`formatter.rs:11703`. The failed assertion requires a symbol chain with a
changed parent to reject. All prior 4410 controls and the new renamed-alias
public probe passed, as root confirmed.

The old parent check ran only in `validated_parent`. A visible unqualified name
could return from `chain_in_table` at `symbol_display.rs:515`, then from
`symbol_chain_worker` at line 286, without calling that function. Ordinary
source-symbol validation did not check for a wrapper parent. This left a
direct-name path around the new rejection.

The unit has two changed-parent controls. Source inspection identifies the
exported `value` queried inside `hidden` as the affected direct-name path. The
log prints the assertion but not the loop row. The wrapper-owner control is
already covered by the exact wrapper proof, which requires no parent.

Follow-up `3a336ec7` moves the same rejection to `validate_symbol` at
`symbol_display.rs:1250`. `symbol_chain` calls that validator before lookup,
including before its direct-name and type-parameter returns. A genuine wrapper
must still have exact source ownership and no parent. The follow-up changes
no alias-selection rule, formatter code, or test assertion.
The unchanged unit must pass in the new root gate before runtime approval.

## Measured Go behavior

No new Go build or run was started. This review reuses the completed four-flag
probe from `2e7bb2ea`, reported in `36f5fbe6`, on pinned Go
`dc37b5249ab60e2bbce936f71b883e6c8136167e`.

The evidence has 19 values, four actual flag combinations, and cold and warm
passes. All rows and identity fields match across replay. All 12 identity
relationships are true. Diagnostics are empty before and after formatting.
The flags are `NO_TRUNCATION`, that flag with single quotes, that flag with
`USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE`, and all three together. Their
recorded bit sets are `1`, `268435457`, `16385`, and `268451841`.

| Requested Go view | Base display | Single-quote display |
| --- | --- | --- |
| Original wrapper, bare import visible | `typeof import("../producer.cjs")` | `typeof import('../producer.cjs')` |
| Original wrapper, distinct wrapper visible | `typeof import("../producer.cjs")` | `typeof import('../producer.cjs')` |
| Original wrapper, only a copied value imported | `typeof import("../producer.cjs")` | `typeof import('../producer.cjs')` |
| Same-owner alias `routed`, no direct producer import | `typeof routed` | `typeof routed` |
| Same-owner alias `routed`, another direct wrapper visible | `typeof routed` | `typeof routed` |
| Distinct direct wrapper's own view | `typeof other` | `typeof other` |
| Bare/default view in the CommonJS caller | `typeof bare` | `typeof bare` |

Adding the outside-scope flag changes none of these results. Single quotes
change only import strings. Both renamed-alias cases retain Go type token
`type-0004` and owner `symbol-0005`. The bare/default view is `type-0003`, owner
`symbol-0003`. The direct wrappers are `type-0005`/`symbol-0010` and
`type-0006`/`symbol-0017`. They are not interchangeable names for one view.

The Go probe records both the copied value and the local `routed` expression.
They share the same type and owner. This supports the root public probe's use
of the original wrapped type at each renamed-import location.

The separate no-location controls are stable across replay. They are not a
second four-flag matrix. Fresh diagnostic equality remains null. Retained
diagnostic equality is not evidence that Go produced each diagnostic again.

## Exact source review

At `formatter.rs:1842`, the fallback now passes the wrapper's genuine owner to
the existing symbol-chain query. It no longer replaces that owner with the
bare module before selecting an alias.

`symbol_display.rs:1120` compares canonical symbol identity. Alias candidates
must name the requested owner. A bare import or a different wrapper therefore
does not become a matching alias merely because it shares the same producer
or exports. The normal value-scope qualification checks remain in use.

Only after chain selection, at `formatter.rs:5612`, an external-module root
that is a checked wrapper uses its actual source module for the import path.
This does not change the selected namespace view. The existing quoting and
length accounting remain in `display_module_import_name` and
`display_location_symbol_name`.

The outside-scope flag controls `yield_module`. The omission in
`symbol_display.rs:303` applies only to a non-final parent chain. A parentless
namespace fallback is final, so the flag does not erase its import spelling.
Named accessible aliases still use the same scope checks. This matches the
retained Go observations, not an assumption that a namespace is a type alias.

At `symbol_display.rs:1239`, genuine wrappers pass the existing exact proof
and source validation for both the real module and original import alias.
`alias_provider.rs:174` checks the retained declarations, module and alias
identities, exports, default, links, and originating import. The validator
returns the wrapper owner, not the bare module. These validation functions
take immutable store and host references.

The early parent rejection in `3a336ec7` protects direct-name lookup as well
as qualified lookup. Genuine wrappers share exports. They do not become the
source-declaration parents of those exports. The no-write and retry assertions
remain unchanged in the original unit and await the new root gate.

## Rust coverage

The preserved `03c26a34` baseline reaches the public probe's final assertion.
In both cold and warm passes, its no-direct-import case returns
`MissingModuleSpecifier`; its direct-import case prints an import instead of
`typeof routed`. Identity, diagnostics, replay, and the distinct-wrapper
checks complete before that assertion.

On `c05d045c`, the same unmodified public probe passes with all four expected
`typeof routed` results. The original cross-context wrapper/bare probe and the
existing quote controls also pass. The one new ownership rejection fails as
described above. The copied combined log contains 18 test-target summaries,
with 4411 passes and one failure.

The invariant worker already queued a separate four-flag scope probe in
session `29338`. It covers a hidden renamed alias, a type-only shadow, a
distinct wrapper using the original alias spelling, shared bare defaults,
and no-location replay. This worker did not duplicate that test or root's
combined gate. No new Rust runtime result is claimed here for `3a336ec7`.

## Remaining scope

A caller with a visible same-owner `routed` alias does not need a producer
specifier to name that wrapper. This fixes the renamed-alias failure without
claiming relative-path generation.

A caller that imports only a copied value has no such namespace alias. Go can
generate `../producer.cjs` there. The Rust module-specifier lookup still needs
a caller-valid string. Relative-specifier generation remains separately owned
by `project_graph_review`, including bare/default values in no-direct callers.
Do not reuse an origin file's relative path in a different caller directory.

This review does not approve all namespace naming, fresh Go diagnostic replay,
full project parity, or primary promotion. It contains no production edit.

## Evidence

Worktree:

```text
/home/theo/Code/sandbox/ts-rust/target/agent-worktrees/wave147/namespace-alias-view-semantics
```

Preserved local logs under this worktree:

| File | SHA-256 |
| --- | --- |
| `target/review/root-03c26a34-baseline.log` | `2b5e91f4339f1ae860748d45b4016bc5b9c41387486a5afb727fdcaacf8fce66` |
| `target/review/root-c05d045c-combined.log` | `12eed3191732c8d0327400ee67564436c2f9c9a7b2e4237a7c004ea67b0d6e62` |

Retained Go evidence is under the prior worktree's
`target/review/flags/attempt-1/`:

```text
/home/theo/Code/sandbox/ts-rust/target/agent-worktrees/wave146/namespace-cross-context-final-semantics
```

| File | SHA-256 |
| --- | --- |
| `output/flags.json` | `08221456d8e771c2498793a62fc2aa8d9cc4292d63cedc6ba39142212991a25c` |
| `build.json` | `e5f5449b396ea94dba361ad10dc3305b6f441d84b33a358f2442dc4b7c338b3f` |
| `namespace-flags.test` | `e4c3a38129b74245d09ffcd8625be9c0fff58f6d40f0b90080576e51a02b100c` |

Reviewed source and unchanged public probes:

| File | SHA-256 |
| --- | --- |
| `formatter.rs` | `8206de83ecfdae8fa852bfc47413612f1052a5c2e2b91cc6f1f5e74b76dc20c4` |
| `symbol_display.rs` | `716816ac578702dc1752b40856fced36b6c92e5bc2feb3c5359159a5aa2eed67` |
| `canonical_namespace_wrapper_alias_view.rs` | `a0a1223c9bf8d06c0fefaa78185649f9c8726b90d1858d1f268532b5f050a0e3` |
| `canonical_namespace_wrapper_cross_context_review.rs` | `e46f97198a28b3c0882d05327c822ef88d13f97ccc75e289967b265845a4d8d5` |
