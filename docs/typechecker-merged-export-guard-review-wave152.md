# Merged-export guard review

Status: two confirmed guard defects. Root owns the production repair.

Candidate: `ebe995e1cd7c342ebb7c89fc8ca66600f7ef9715`.
Original probes: `1bc9e76fea46c4556871b27ca8763976f4b67a9a`.
Fixture-only repair: `47eae0c98a6cf0054a03cd006c665015010b5235`.

## Measured result

Session `40156` completed with exit 101 against the fixed original probe commit.
It passed 75 tests, failed three, ignored none, and filtered 3,974. Compilation
took 1 minute 9 seconds. Tests took 0.25 seconds. All 75 original selected
controls passed, including the seven-case merged-owner test and both source
class/namespace controls.

Two failures reached the final negative assertions after unchanged snapshots
and healthy restoration. They confirm wrong public type results. The third
failure occurred during cold-fixture setup and is not a production finding.

## Redirect and flags

`review_merged_export_guard_rejects_redirect_and_flag_pairs_before_cache_reads`
changes the raw class redirect to the raw namespace, clears the canonical
owner's flags, and plants a number node cache. Each owner change alone is
rejected. The pair makes both repeated public queries return the planted number.
The export route returns `Ok(None)` and the remaining source flags lack CLASS.

`store.rs::source_symbol_flags` uses current redirects to select original binder
flags. The changed redirect removes the class from that set. The source guard
in `name_resolution.rs::lookup_name` then fails to recognize a class before
value filtering. The export route falls through to the node-type cache in
`artifact_queries.rs::get_type_at_location`.

## Foreign global target

`review_merged_export_guard_rejects_foreign_same_name_global_targets` changes
the global `Value` entry to a valid same-name class in another external file.
Its source and declared/value identities are valid for that other class.

Changing the global entry alone redirects both repeated public reads to the
foreign declared type. Changing the entry together with matching node caches
does the same. Changing only the node caches is rejected. All four wrong reads
preserve the snapshots, and restoration returns the healthy result.

The lookup verifies the substituted class's own source, but not its membership
in this lookup table. The direct-source path then accepts the foreign class
without using the merged-global proof.

## Cold fixture

The original cold program is `export = Value;`. Its binder does not create a
local table. The original fixture unwrapped that absent table at line 189,
before any cold-query assertion ran.

The separate fixture repair makes the local table optional. Existing mutation
fixtures still require their actual table where they use it. The cold control
asserts that no local table exists. It retains the exact original program and
all original assertions. No table is created or borrowed. Both negative probe
bodies remain byte-identical. Removing only the fixture edits and the new
absence assertion reproduces the original probe file exactly.

The fixture repair has source and whitespace checks only. Root owns its runtime
check with the separate production repair. No combined repair pass is claimed.

## Evidence and isolation

The first run used its own initially empty target in
`target/agent-targets/wave152/merged-export-guard-review`. All five frozen source
hashes still matched after collection. No artifact or fingerprint was copied.
The root capped runner used an absolute manifest, locked offline dependencies,
16 GiB memory, 16 MiB process and Rust stacks, the common lock, and unchanged
TMPDIR. The existing unused `allows_string_fallback` warning remains.

Log: `/tmp/ts-rust-wave152-merged-export-guard-review-tests-1.log`.
Log SHA-256: `c87354503b7e31f1dd648389e1d7f9a0230afbd7362cb9f0a4414c9f40900238`.
Binary SHA-256: `559d6f5d6e9b7f074c8f9c51eb80556791e98469d9b7b24c7bbc5f64c4566e9a`.
Corrected fixture file SHA-256:
`86bc5f27b2628e8fd46ddfbda896424dac4686360cea41dd253268bd01713cf8`.

The separate `wave153/merged-export-cold-fixture` handoff worktree has no Cargo
run and no target. The native-key composition remains separate. Root's earlier
full workspace pass does not clear these new findings.
