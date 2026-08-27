# Heritage method recovery

The recovered-method failure from `f1582a54` is fixed. Its original warm-read
test passes unchanged, along with all existing checker units and the public
heritage and optional-method tests.

Base: `f1582a544eecb8c5f4b24a037c55f724fca85377`.
Branch: `agent/wave147-heritage-method-recovery`.

## Before and after

The wave144 control used `first(value: T): T` on `Box<number>` with a zero-count
recovering session. The cold read returned a callable with recovered signature
values. The next read returned `InvalidCachedProperty`. The callable validator
still required the normal mapped `number` result.

The wave147 run keeps that test and its assertions. The warm read now returns
the original callable. No new instantiation or limit event is needed. The
normal mapper and return checks have not been changed to accept error or any.

## Implementation

`InstantiatedPropertyRecovery::matches_identity` checks only the current producer
record and its exact source and result contents. It does not enter graph
validation. `checked_identity` returns a sealed borrowed view. The record also
retains the array targets supplied to the producer.

`InstantiatedPropertyRecoveryIdentity::receiver` checks the source target,
original mapper endpoints, live proxy metadata, and exact receiver member entry.
It uses the existing source-owner plan without asking the member graph to
validate itself.

`validate_stored_recovered_property_callable_set` is a separate early dispatch
in `validate_stored_callable_set`. A revoked or changed recovery result is
malformed. It cannot fall through to another callable family. The source type
is checked through `validate_stored_declared_method_callable_set`, and that
provider's projection and dependency edges are retained.

`recovered_property_signature_parameters` checks the stored signature pair,
mapper, type parameters, declaration, flags, arity, and parameter symbols and
links. Field values come from the exact producer result. No general exception
for error or any types exists.

The property producer checks the ordinary source provider before instantiation.
Raw writes to source or copied parameter links revoke the record, including
identical writes. Signature type parameter contents are also retained. Existing
proxy and source-target invalidation remains in place.

For recovered methods, member validation checks the callable projection without
starting another graph walk. Source and receiver dependencies go back to the
outer graph reader, which keeps its own visited set and array mode. The recursive
`Derived extends Box<Derived>` control verifies this path.

## Ownership

The following ordinary paths are unchanged:

- `validate_stored_declared_method_callable_set`.
- `validated_method_annotation_type` and `valid_declared_method_type_parameters`.
- `validated_instantiated_method_mapper` and normal parameter and return matchers.
- `authenticated_interface_method_owner` and `published_interface_method_source_matches`.

The new recovery dispatch reuses the ordinary source provider. The source-result
proof work owned by `method_publication` applies through that same call. This
change does not copy, replace, or weaken that proof. It does not claim to repair
the separate `292f335c` ordinary paired-cache or hidden-array finding.

The function-member source-result commits `d6e3c6a2` and `17bf11ca` were read,
but their later ordinary-owner code was not imported into this worktree. Only
the recovery path is added to `callable_sets.rs`.

## Verification

Session `19063` exited 0.

| Target | Passed | Failed | Ignored |
| --- | ---: | ---: | ---: |
| Checker units | 3,855 | 0 | 0 |
| `source_interface_heritage` | 14 | 0 | 0 |
| `source_optional_methods` | 3 | 0 | 0 |

The unit run includes the unchanged original source-property probe, the
unchanged formerly failing method test, and all 15 recovery controls. New
controls cover wrapped parameters and returns, rest parameters, generic
constraints and defaults, overloads, recursive receivers, source-cache changes,
raw writes, mapper and signature changes, cross-result and cross-proxy forgery,
and rejection of a malformed source before instantiation.

The original source-property and public test files are unchanged from the base.
Formatting and `git diff --check` pass. No source caller, cache reset, or new
instantiation session was added. No full workspace run was repeated.

The command used the shared capped runner and lock, an absolute manifest,
locked offline dependencies, 16 GiB memory, 16 MiB Rust and process stacks, and
`target/worktrees/wave147-heritage-method-recovery`. `TMPDIR` was unchanged.
No other worker was stopped. All owned execution sessions have ended.

Log: `/tmp/ts-rust-wave147-heritage-method-recovery-checker.log`.
SHA256: `1c2fd323400acb0864f660e82611853ec25eb2d0397c03c451a94f574713c70a`.

This closes the retained recovered-method cache failure. It does not claim a
complete direct-property TS2589 diagnostic owner or approve unrelated held
index-reader changes.
