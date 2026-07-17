# Fixture diagnostic scorecard schema

The canonical fixture runner writes schema version 5. Consumers must inspect
`schemaVersion` before reading a scorecard; version 5 is intentionally not
advertised as version-4-compatible because it adds a new terminal status and
changes what the runner can retain after a canonical checker failure.

## Version 5 provenance

The top-level `provenance` record contains:

- the upstream and Rust Git SHA plus dirty state (`null` when the path is not a
  Git worktree);
- an XXH3-128 digest of the complete deterministic upstream oracle manifest;
- the exact process invocation as an argument array; and
- the version and XXH3-128 digest of the capability registry compiled into the
  runner.

The manifest digest identifies discovery, ordering, disposition, and artifact
counts. It is not a digest of only the filtered or limited selection.

## Stable variant identity

Every variant has a `variantKey` in the form `v1:<32 lowercase hex digits>`.
The v1 identity hashes length-delimited fields for the repository-relative case
path, compiler-option names normalized to lowercase, canonical option values,
the expected baseline path, and the complete expected baseline contents.
Aliases such as `target=es6` and `target=es2015` therefore have the same
identity, while a changed oracle produces a new identity.

Fixed shard manifests must store these complete keys. A future identity
algorithm requires a new key prefix and an explicit manifest migration.

## Outcome and frontier fields

`outcomeClass` is one of:

- `exact`;
- `harness_config` for a fixture option or artifact fidelity boundary;
- `checker_capability` for a typed, intentionally unsupported compiler
  boundary;
- `supported_mismatch` when the checker ran but its artifact differs; or
- `fatal_invariant` for a typed compiler invariant failure.

Every non-exact result has a `frontierBlocker`. Checker-capability blockers have
a registry-backed code. Fatal blockers use the reserved `INV.*` namespace.
Harness and supported-mismatch blockers have no capability code. Human-readable
display text is detail only and is never parsed to choose an outcome or code.

The existing version-4 status strings remain unchanged for exact, mismatch, and
unsupported results. Version 5 additionally permits `fatal_invariant` and adds
`summary.fatalInvariants`.

Canonical checker capability and invariant results are retained per variant;
later variants continue to execute. Either outcome still makes the command exit
1. A fixture filesystem I/O failure remains a process-level harness error and
exits 2 because reliable scorecard persistence cannot be assumed.

## Capability registry

[`typechecker-capabilities.tsv`](typechecker-capabilities.tsv) is schema
version 1. Codes are unique, map to one primary port-map row, and carry explicit
lifecycle metadata. `INV.*` codes are forbidden in that registry. Retired
capability rows remain present and point at their replacement; active rows use
`-` in the replacement column.
