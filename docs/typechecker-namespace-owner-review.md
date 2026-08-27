# Namespace owner display review

This repairs the semantic review finding against `b8bf583c`. Keep that commit
held until the separate repair passes re-review.

## Confirmed failure

The source contains a function merged with a runtime namespace:

```ts
declare function callable(): void;
declare namespace callable { export const value: string; }
```

The probe changes the cached owner flags to `FUNCTION | NAMESPACE_MODULE` and
removes its export table. On `b8bf583c`, the formatter returns `() => void`
instead of rejecting the malformed owner. The focused probe failed as expected.

## Repair

The formatter now checks the retained binder record before using callable
display. It requires complete declaration binding, the original function owner,
and matching binder ownership for every cached declaration.

The binder records instantiated namespaces in `not_const_enum_only_modules`.
A const-enum namespace merged with a function also sets this marker. Semantic
symbol setters cannot erase the retained record, so changing flags, deleting
exports, or pruning cached declarations cannot hide the namespace value meaning.

The object-payload check still runs first. Callable signature and cache
validation still run after the source-backed namespace check. The repair does
not change binder classification, query producers, or pinned fixtures.

## Verification

The final focused run passed all six formatter tests and all three existing
binder tests, with no ignored tests. The binder tests cover module instance
state, local export aliases, and const-enum classification. The formatter cases
cover the reviewer mutation, pruned declarations, unrelated declaration
ownership, valid type aliases, and const enums in both declaration orders.

Commands use `scripts/run-cargo-capped.sh`, the shared Cargo lock, an absolute
manifest, an exclusive target directory, `TS_CARGO_MEMORY_LIMIT_KIB=16777216`,
and `RUST_MIN_STACK=16777216`.

Logs in the writer worktree:

- `target/namespace-owner-repair-red.log`: confirmed original failure.
- `target/namespace-owner-repair-green.log`: eight checks passed, one extra
  test stopped in an existing unsupported source-checking path.
- `target/namespace-owner-repair-green-2.log`: eight checks passed, the alternate
  setup stopped at an existing missing-type query boundary.
- `target/namespace-owner-repair-green-3.log`: final run using supported source
  declarations for the pruned-declaration probe. All nine checks passed.

These checks do not establish full fixture parity. The separate identifier
type-query and export-assignment symbol gaps from the earlier handoff remain
outside this repair.
