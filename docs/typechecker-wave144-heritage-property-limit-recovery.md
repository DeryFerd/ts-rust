# Heritage property limit recovery

Status: held checkpoint. Direct and wrapped value recovery pass. Method recovery
still fails, so this is not integration approval.

Base: `5f57896b22576122a7579b58e2d26207500bd78d`.
Branch: `agent/wave144-heritage-property-limit-recovery`.

Before this repair, the unchanged probe at `b64a2de9` returned the canonical error
type after a real limit event, then reported malformed heritage. The preceding
probe at `18d9c18a` passed. Both probes and the public heritage assertions remain
unchanged. The before evidence is in the wave141 invariant report.

## Repair

The property producer records a recovery only after its caller's existing session
reports a new limit event. The record binds the exact proxy, source target, source
template, mapper, and result. It also retains type arguments, tuple metadata,
aliases, union members, and callable signature contents. Ordinary member caches,
source parameter defaults, and type-variable cache flags can become ready later
without changing those keys. Copied method parameter results remain checked.

Raw value-link writes to the proxy or source target revoke the record, including
identical writes. Revoked records remain present. Clearing or restoring a proxy
cannot turn an old recovery into a new cold query. Failed writes do not revoke a
record. The normal exact mapper validator remains unchanged for unproven caches.

The producer keeps canonical error results and wrapped recovery results cached.
It does not clear the cache, replace the session, or return ordinary `any` instead.
It rejects noncanonical recovery identities before instantiation.

## Verification

The original source-property probe and all public heritage assertions are unchanged.
New focused tests cover warm reuse, query reset, another caller, raw writes,
forged values, cross-proxy substitution, array capabilities, and changed results.
One method recovery test also checks the separate callable validator.

- Session `35185`: unchanged source-property probe passed. Exit 0, one pass,
  no failures or ignored tests, and 3,848 filtered tests. The repair compiled.
- Session `60163`: all checker units and `source_interface_heritage`, exit 101.
  The units have 3,847 passes and three failures. The 14 public tests all pass.
  All failures are in new recovery controls. All 3,840 existing units pass,
  including the unchanged source-property probe.
- Session `61275`: the focused retry found a test-only AST variant typo and exited
  101 before running tests. The fixture now uses `NodeData::TypeReferenceNode`.
- Session `26553`: the focused retry compiled and ran all ten controls. Nine
  passed and one failed, with no ignored tests and 3,840 filtered tests.
  The only failure is the recovered-method warm read. Exit 101.

All runs used locked offline dependencies, an absolute manifest, 16 GiB memory,
16 MiB Rust and process stacks, and the reserved
`target/worktrees/wave144-heritage-property-limit-recovery` build directory.
`TMPDIR` is unchanged. No shared lock was bypassed and no other worker was stopped.
Formatting and `git diff --check` pass. Session `60163` also passed the source
parameter default-resolution control added after the first compile. Two initial
failures needed test-only corrections. The wrapper fixture went through an unsupported
source-publication path, and the wrapper corruption control expected a narrower
error category than the earlier rejection returns. The corrected fixture uses
the existing declared-member publication helper for wrapped annotations. Direct
properties and methods still use source inheritance publication. The original
probe and public tests remain unchanged.

Passing value cases are `T`, `[T]`, `readonly [head: T, tail?: T]`, `[] | [T]`,
`Array<T>`, `ReadonlyArray<T>`, `Child<T>`, and `[Child<T>, T[]]`. The controls
also pass after query reset, another caller, nested member cache publication,
and source parameter default resolution. Raw writes, forged caches, foreign
array targets, and changed results reject without more instantiation or a new
limit event. A changed method signature rejects even when it matches the normal
mapper result.

All owned execution sessions have ended. No full workspace run was repeated.

Broad log: `/tmp/ts-rust-wave144-heritage-property-limit-recovery-checker.log`.
SHA256: `68ece274d1aefc8894813029984274ed2a21c6a8c26558ee9d1f4e1c8308a904`.
Focused log: `/tmp/ts-rust-wave144-heritage-property-limit-recovery-focused.log`.
Retry log: `/tmp/ts-rust-wave144-heritage-property-limit-recovery-focused-2.log`.
SHA256: `6e6c8c472481cd93a6cf027152878dbd0a83290a1cdc79b9af23498251f32633`.

## Remaining callable failure

The separate callable validator still checks method parameter and return types
against the normal mapper result. The new method control confirms the failure.
For `first(value: T): T` on `Box<number>`, a zero-count recovering caller returns a
callable from the cold read. Its next read returns `InvalidCachedProperty` for
the same proxy. Sessions `60163` and `26553` both fail at the warm-read assertion.

This repair has not changed `callable_sets.rs` or its normal mapper validators.
Accepting the method needs a checked callable provider for the producer's exact
recovery record. That work must keep parameter, signature, and source provenance
checks. Do not infer method approval from a passing direct-property test.
The callable provider must not call the full recovery matcher again. That matcher
enters cached graph validation, which calls the callable provider. The dispatch
needs a separate read-only identity check to avoid recursion.

## Scope

The pinned Go audit is in
`docs/typechecker-wave144-heritage-limit-recovery-semantics.md` on the audit branch.
It establishes the direct property cache behavior. It does not establish every
method, nested diagnostic, or direct-property TS2589 diagnostic owner.
This repair does not claim that the direct-property source diagnostic path is
complete. The earlier held index-reader changes are outside this work.
