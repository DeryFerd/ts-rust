# Object-witness integration review handoff

## Commits and scope

The reviewed phase producer is the base at `c0c72945`.
The approved provider commits were applied in order.

| Approved provider commit | Commit in this branch |
| --- | --- |
| `ea7a8768` | `a1bed56a` |
| `6136c68c` | `8216be0b` |
| `b650cedf` | `4460f386` |

The adapter is `419f43e051d526c6b4c0a1c508b04d1bd53934ce`.
The tested binary was built from that clean commit. This handoff adds no
code and does not require another build.

All five provider files match `b650cedf` byte for byte. No file that existed
at `c0c72945` was changed or removed. The integration adds only the provider
files and the `object_witness_phase` directory. It does not include Hono
display probes, formatting changes, or cache experiments.

## Adapter contract

The adapter uses the public provider APIs. It does not inspect private
provider tokens. Its receipt tokens bind actual provider handles and actual
returned type pointers within one process.

1. Open each provider pass with `ProjectOracleBeginObjectPass` after the
   before-types snapshot.
2. Replace each direct artifact type query with one
   `ProjectOracleObjectQuery` call. Return its exact type pointer to the
   original walker. Keep both original observation hooks.
3. Close the pass with `ProjectOracleEndObjectPass` after types, symbols,
   and the after-symbols snapshot.
4. Wait for both passes and the original phase checks to finish. Require
   exact cold and warm query slots and nodes.
5. Call `ProjectOracleVerifyObjectsAfterArtifacts` once for each object
   literal or parenthesized-object query pair, in warm query order.

There is no duplicate query or prewarming call. The independent source-only
Program never opens a provider pass. Provider operations and adapted walker
calls hold the Program's exclusive checker lock. All type queries have
receipts, including queries outside the provider's object-root scope.

Verification records the provider result without changing it. Each result
includes relation identity, allocations, cache changes, diagnostics,
suggestions, overflow, panic, and witness changes. The adapter then checks
the frozen primary report and the artifact bytes for changes.

The primary snapshot hashes compare the same report state before and after
verification. They do not hash the final report file. The final report also
contains trace, checker-binding, and runtime fields added after that check.

## Controls

All eight adapter controls and all three original phase controls passed.
The controls compare plain and adapted runs, including every direct query,
the artifacts, the diagnostic phases, the input graphs, and the original
failure results. Verification is refused at all four open-pass boundaries.

| Control | Original outcome retained | Raw type changes | Verified pairs | Incomplete pairs | Relation calls |
| --- | --- | ---: | ---: | ---: | ---: |
| `empty` | `invariant_error` | 1 | 1 | 0 | 1 |
| `nested_parentheses` | `invariant_error` | 4 | 4 | 0 | 4 |
| `function_cache` | `invariant_error` | 1 | 1 | 0 | 1 |
| `computed_unproved` | `invariant_error` | 1 | 0 | 1 | 0 |
| `const_unproved` | `invariant_error` | 2 | 0 | 1 | 0 |
| `existing_source_error` | `incomplete_evidence` | 0 | 0 | 0 | 0 |
| `class_base_fallback` | `incomplete_evidence` | 0 | 0 | 0 | 0 |
| `query_added_diagnostics` | `incomplete_evidence` | 0 | 0 | 0 | 0 |

The class-base control exercises both actual fallback queries. The
query-added diagnostic control keeps source-only diagnostics empty and
records five diagnostics after the first type phase. Its renderer flags
remain false. The existing-source-error control keeps its flags true.

The build took 126.911 seconds with a peak RSS of 2,407,404 KiB.
The controls took 1.807 seconds with a peak RSS of 312,724 KiB and exit 0.

## Real-project evidence

Two fresh processes used the controls binary on unchanged ts-pattern at
`c92ca435c7e1827e0fd55c539080ef1bfd6fe3f0`. Both completed with exit 1 and
the original `invariant_error` outcome. Their independent audit passed.

Each process retained all 18,962 original events in the same order and all
18,890 artifact queries. Each pass has 3,101 type queries and 6,344 symbol
queries. The adapter added 6,202 type-query receipts and 144 boundary events.
It did not add a type query.

The audit compared every original event and every primary report field
except provenance, run ID, runtime, and trace metadata. It mapped operation
tokens by exact original event order. It also checked all 14 overlay hashes,
the saved source hashes, the Go executable, and the copied module files.

Each run had 16 artifact files. All were byte-identical to the preserved
phase baseline. The type artifact hash remains
`cdbfea306a05d990181a615833c8380b258caed4a87c1085b29e0922ab1c2af8`.
The symbol artifact hash remains
`230c91fcb2a599b71b6e1b17ff8d39a6051cbcc256003144a1363207c6cc8939`.

Both runs kept 44 changed raw type-query pointers and 44 changed rendered
type pointers. The source-only Program made no artifact queries. Every
diagnostic snapshot retained TS5011, and both renderer flags stayed true.
Fresh diagnostic equality remains null. Project parity remains false.

Each run recorded 69 object query pairs with the following provider results.

| Provider result | Pairs | Raw pointer changes | Relation calls |
| --- | ---: | ---: | ---: |
| `verified` | 17 | 17 | 17 |
| `incomplete` | 52 | 27 | 0 |
| `rejected` | 0 | 0 | 0 |

The 52 incomplete results remain unchanged. Their reasons are 26 property
types without a proved cache owner at creation, one unproved object member
producer, and 25 returned objects without a matching producer observation.
None were retried. No relation ran for an incomplete pair.

The 17 relation calls reported identity success. They added 17 identity-cache
entries and allocated no types, symbols, or signatures. They reported no
diagnostics, suggestions, overflow, panic, or witness changes. Each called
relation had overflow evidence. The full provider results remain in the
proof reports. These results did not reduce the 44 raw pointer failures.

Both passes closed before verification. The last pass closed at
`operation-00018966`, and verification began at `operation-00018967`.
The frozen primary report and artifact bytes stayed unchanged after
verification. The two proof reports match apart from the primary snapshot
hashes, which include different process run IDs.

Process A took 0.755 seconds with a peak RSS of 512,044 KiB. Process B took
0.747 seconds with a peak RSS of 510,556 KiB. Both returned the required
nonzero result without a runtime resource error.

The before and after input verifiers passed and produced byte-identical
reports. They checked 101 source files, 12,649 dependency files, 45 links,
and 367 preparation reader inputs. The preserved phase report bytes are
unchanged. No project input, wrapper, or provider file was changed.

## Local evidence and pins

All `target` paths below are relative to the shared workspace at
`/home/theo/Code/sandbox/ts-rust`, not this child worktree.

The evidence root is
`target/project-evidence/object-witness-phase-integration`.

- `controls-1/build.json` records the build, sources, overlays, and binary.
- `controls-1/controls.stdout.log` records the eleven passing controls.
- `controls-1/controls/` contains each plain and adapted control report.
- `controls-1-cgroup.json` records the actual build cgroup limit.
- `ts-pattern-inputs-before.json` records the unchanged prepared inputs.
- `ts-pattern-inputs-after.json` repeats the input checks after both runs.
- `ts-pattern-1-cgroup.json` records the project cgroup limit while queued.
- `ts-pattern-audit.json` records the independent report and artifact audit.
- `ts-pattern-1/process-a/` and `process-b/` contain the primary reports,
  proof reports, query receipts, traces, and artifacts.
- `ts-pattern-1/process-a-process.json` and `process-b-process.json` record
  the exact process arguments, environment, exit codes, and resources.

The preserved baseline is
`target/project-evidence/ts-pattern-go/phase-correct/attempt-1/process-a`.
Its report SHA-256 remains
`f45364345c819c5be97bc7ce1ac5d5608ea171380e4bb858e2c776fb2be0e757`.
The independent audit SHA-256 is
`8e09c1a01e096090fc6137351656ceaecdf7aceedd42c13e7d77940a64e375b0`.

The local evidence tools are `audit-project.mjs`, `run-project.sh`, and
`record-cgroups.mjs` under
`target/worktrees/wave132-object-witness-phase-integration`.
The reuse launcher runs the verified binary under the shared lock and
16 GiB cap. It does not rebuild or change the compiler inputs.

The Go executable is pinned to version `go1.26.5 linux/amd64` and SHA-256
`8da5fd321795754b994c64e3eb8a5a14ff47bd285559a7e876f3c79abafc67f9`.
TypeScript-Go is pinned to
`dc37b5249ab60e2bbce936f71b883e6c8136167e`.
The binary SHA-256 is
`0b4b888e000eb2dd62881ce97fa38db48b20601d2f1b18c02f1ff68f16dfb47f`.

The build and runs use a 16 GiB cgroup cap, no swap, one Go worker, the
shared lock at `/tmp/ts-rust-cargo-3253601520.lock`, copied module inputs,
`GOTOOLCHAIN=local`, `GOPROXY=off`, and `-mod=readonly`.
No dependency download or package installation was needed.

## Review checks

First review: check the API use and query order. Confirm exact return
binding, independent source-only checking, fixed renderer flags, exclusive
checker ownership, both pass closures, and no query before its actual
artifact phase. Compare the provider files with the approved commit.

Second review: check the evidence and gates. Confirm receipt and event
binding, query-pair order, unchanged primary artifacts, complete relation
side effects, retained unsupported results, and preserved raw pointer
failures. Confirm that fresh diagnostic equality remains null, parity
remains false, and the project command remains nonzero.

This adapter does not establish project parity. It does not provide fresh
diagnostic evidence or replace the existing pointer gate. Provider results
are bounded to the recorded object query pairs. Hono was not run for this
integration step.
