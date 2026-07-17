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

When `--variant-manifest` executes a fixed shard, provenance additionally
contains `fixedShard`:

- `name`;
- `schemaVersion` and `variantKeyVersion`;
- the ordered-key `digest` and `digestAlgorithm`; and
- `variantCount`.

This is additive schema-5 provenance. `manifestDigest` remains the digest of
the complete upstream oracle manifest, so selection identity never replaces or
changes the discovery identity.

## Stable variant identity

Every variant has a `variantKey` in the form `v1:<32 lowercase hex digits>`.
The v1 identity hashes length-delimited fields for the repository-relative case
path, compiler-option names normalized to lowercase, canonical option values,
the expected baseline path, and the complete expected baseline contents.
Aliases such as `target=es6` and `target=es2015` therefore have the same
identity, while a changed oracle produces a new identity.

Fixed shard manifests must store these complete keys. A future identity
algorithm requires a new key prefix and an explicit manifest migration.
The runner expands every runnable case before resolving fixed keys, requires
each key to resolve exactly once, checks redundant case/option/baseline/source
metadata against discovery, and executes the resolved variants in manifest
order. Fixed execution also requires a clean upstream checkout at the
manifest's exact Git SHA and oracle-manifest digest.

## Outcome and frontier fields

`outcomeClass` is one of:

- `exact`;
- `harness_config` for a fixture option or artifact fidelity boundary;
- `checker_capability` for a typed, intentionally unsupported compiler
  boundary;
- `supported_mismatch` when the checker ran but its artifact differs; or
- `fatal_invariant` for a typed compiler invariant failure or a caught canonical
  checker unwind.

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

The runner isolates only the call to the canonical checker program constructor;
fixture parsing, filesystem setup, baseline I/O, and legacy checking remain
outside the unwind boundary. A checker panic is retained as
`INV.CHECKER.PANIC`, with its string payload copied verbatim into the blocker
detail after a stable `canonical checker panicked:` prefix. Non-string payloads
use the deterministic `<non-string panic payload>` marker. Panic outcomes are
fatal invariants, never capabilities, and do not stop later variants or JSON
persistence. The normal panic hook is not replaced or suppressed.

This isolation contract requires a binary built with `panic="unwind"`. A
`panic="abort"` build rejects canonical diagnostic execution explicitly as a
process-level unsupported harness configuration before fixture discovery; it
does not claim it can retain an aborting process.

## Capability registry

[`typechecker-capabilities.tsv`](typechecker-capabilities.tsv) is schema
version 1. Codes are unique, map to one primary port-map row, and carry explicit
lifecycle metadata. `INV.*` codes are forbidden in that registry. Retired
capability rows remain present and point at their replacement; active rows use
`-` in the replacement column.
