# Completion gate audit

Source checkpoint: `8357dac34c37b4a4f24b210a4ddafb76310bfaec`.
Upstream epoch: `dc37b5249ab60e2bbce936f71b883e6c8136167e`.
Audit date: August 27, 2026. No production edits, Cargo commands, or new parity runs.

`proved` applies only to the stated scope. `incomplete` means evidence exists but
does not close the gate. `contradicted` means a saved result fails the condition.
`missing` means no required result was found in the inspected evidence. It is not
a claim that no other work exists. The root status file was only an evidence index.

## Findings

1. **P1: no project ring or full-corpus completion is proved.** The frozen modern
   project manifest is absent. The completed semantic smoke at clean `8357dac3`
   has 51 exact, 43 unsupported, and one artifact mismatch in 95 executed variants.
   Discovery of 12,750 cases is not execution of all option configurations. [E1, E2]
2. **P1: project replay cannot pass on retained output equality.** Both saved
   phase-correct Go projects report `invariant_error`. Hono changes 221 direct
   type identities and its type artifact bytes. ts-pattern changes 44 identities
   despite equal printed artifacts. Fresh diagnostic equality is null. The saved
   Rust project runs have no completed graph/artifact/replay comparison. [E4, E5]
3. **P1: the accepted composition needs its own complete verification record.**
   The saved combined workspace log has 6,460 passes and two failures. Later
   focused tests pass. The wave137 check now finishes with warnings, and its
   semantic smoke is complete. Full tests, strict Clippy, rustdoc, and a semantic
   milestone still need a complete record for this composition. The 27 Go
   prepare-only path controls do not exercise a project check. [E6, E7]
4. **P2: status text is not synchronized.** The goal's lines 394-421 still call
   14/95 exact a current result. Port-map C01 still cites dirty `d97e5de` and says
   a completed milestone run is unverified. Saved evidence instead has a clean
   51/95 semantic smoke and a completed 397/511 *diagnostic-only* milestone.
   Correct the labels, not the old evidence. The milestone's `full_artifact`
   label must not be read as three-artifact parity: `semanticArtifacts` is null
   and its invocation lacks `--semantic-artifacts`. [E2, E3, E8]

The current goal explicitly remains active and says no modern-project ring is
claimed. That statement is accurate. Bounded leaf approvals are not a broader
completion claim. [S1:136, S1:147]

## Required gates

| Gate | Status | Evidence required and current gap |
| --- | --- | --- |
| Frozen oracle and fixed selections | proved | The 96 and 512 manifests have unique keys and the frozen SHA. The milestone contains all smoke keys. Smoke has eight families, each with six clean/six error entries. Recomputed digests match saved provenance. This proves the selections only. [S1:529, S1:555, E1-E3] |
| Stable outcome accounting | incomplete | The clean `8357dac3` report retains SHA, dirty state, digests, registry version, invocation, and keys. Its 43 unsupported results split into 28 capability and 15 harness outcomes. Zero fatal results cannot prove continuation and nonzero exit after `INV.*` failures. [S1:529-584, E2, E3] |
| Canonical semantic closure | incomplete | The map has 11 verified, 30 porting, and five blocked rows. Prove one owned semantic graph and ordinary library checking, without legacy fallback, fixture branches, placeholder success, or unexplained `any`/`unknown`. [S1:48-60, S2:2028-2042, E8] |
| Leaf proof and independent review | incomplete | Unverified rows and unassigned reviewers remain. Each row needs upstream inventory, ownership, public tests, forced cold/warm checks, atomic retry, cache identity tests, strict options, applicable cross-file tests, and separate fresh Go-semantic and Rust-invariant reviews. A `verified` label alone is not evidence. [S1:490-516, S1:1123-1162, E8] |
| Dependency composition | incomplete | Prove imported recursive generics, `T[K]`, callbacks/overloads/rest/spread/new, flow, classes, actual-library utilities, and staged JSX together. Wave 3 needs actual pinned declarations for conditional/mapped/template/NoInfer/intrinsic behavior. Advanced classes, generators, flow, packages, and JS/JSDoc remain later gates. [S1:662-666, S1:997-1048, E8] |
| Checkpoint quality | incomplete | The completed check has 18 library warnings and one library-test warning, but no source SHA. Retain accepted-SHA production/public checks, full tests, format/generated-source checks, strict checker/compiler Clippy, denied rustdoc warnings, and relevant debug/release results. The prior full test log has failures. [S1:1157-1196, S2:1657-1659, E6, E7] |
| Per-merge regression control | incomplete | Fixed-key comparison at `985ba5f5` and `8357dac3` gives one exact win, no exact losses, no new supported mismatches/fatals, and one additional exact type and symbol baseline. Two blocker details change. Serial per-merge scores, synchronized records, and the two-unreviewed-stacks-per-reviewer limit still need proof. [S1:605-619, S1:1164-1173, E2, E7, E8] |
| Exact semantic artifacts | contradicted | Require exact errors/types/symbols through production queries and pinned node order. At `8357dac3`, 46/89 types and 54/89 symbols are exact. One type and seven symbols mismatch. Another 27 of each are not reached. Secondary mismatches inside non-exact variants count. [S1:586-603, E2] |
| Full frozen-corpus ledger | missing | Account for every pinned compiler/conformance configuration, actual upstream skips, and explicit emit-only exclusions. No Rust-only skips, unexplained timeout/crash, unapproved mismatch, or unsupported checker variant may remain. An emit-only artifact is not semantic success. Neither fixed selection closes this gate. [S1:66-72, S1:1042-1048, S1:1261-1264, S2:1626-1630, E1-E3] |
| Frozen modern-project manifest | missing | Review and check in `tools/ts_fixture/manifests/modern-projects-v1.tsv` with repository/commit, license, lockfile digest, exact package-manager version, configs, ring, non-generated line counts, and pinned Go artifact digests. The saved inventory is not this manifest. [S1:1207-1221, E1, E9] |
| Unchanged project inputs | incomplete | Hono/ts-pattern snapshots are verified for their recorded runs only. Seal all selected dependencies, workspace links, generated declarations, libraries, and build records. No source patches, private exclusions, skipped files, or fallback. Runtime Git ancestry cannot replace archive input pins. [S1:1223-1227, E4, E5, E9] |
| Input and mode equality | incomplete | Paired Rust/Go comparison is unavailable. Compare loaded file bytes/order, libraries, effective options, config inputs, import/require modes, package identities, realpaths, and graphs. Preserve null versus false. `skipLibCheck` must still bind and consume `.d.ts`. Parser-text digests and retained paths cannot close documented NodeNext/realpath gaps. [S1:675-697, S1:1226, E5, E10] |
| Forced replay and two-run equality | contradicted | Go has strict identity failures and unavailable fresh diagnostics. Rust replay is unavailable after construction failures. Require two deterministic runs with real source re-entry, equal diagnostics/artifacts, and valid within-program identities. Retained output and the `type_checked` fast path do not pass. [S1:1148-1149, S1:1229-1231, E4, E5] |
| Zero project failures | contradicted | Hono/ts-pattern full-source runs stop at classes. Query core stops at the timeout-manager arrow. Require every project to finish with exact errors/types/symbols and no unsupported, mismatch, or fatal outcome. Reporter exit zero means a report was written, not a check passed. [S1:1228-1231, S2:1591-1601, E5] |
| Determinism and resource budgets | incomplete | Prove recursion/count limits, including 1,000 conditional tail steps, on adversarial inputs without panic, overflow, nondeterminism, or unexplained timeout. Future checker pooling needs ownership and no-cross-checker-mixing proof. Narrow limit tests do not establish the corpus/project gate. [S1:730-750, S1:891-906, S2:1642-1646, S2:2033-2034, E8] |
| Project performance | missing | Record machine/toolchain and equal complete workloads. Release Rust wall time must be at most 10x Go, peak RSS at most `max(2x Go, 4 GiB)`. Include cold/warm and pathological inputs. Saved dev-profile Rust failures before checking and Go-only metrics are not comparisons. [S1:1232-1237, S2:1644-1646, E4, E5] |
| Controlled roll-forward | missing | C02 is blocked. All inspected scorecards use `dc37b524`. After frozen parity, port a later semantic batch, update generated inputs, and prove its complete core delta plus frozen regression artifacts. Drift inventories and oracle-hook merges do not satisfy this. [S1:1266-1270, S2:1648-1656, E2-E4, E8] |
| Atomic cutover and cleanup | missing | Deferred until the corpus gate. Then switch the default checker atomically, remove reachable legacy selection/`TypeDescriptor` bridging, and retain only explicit output adapters backed by canonical IDs. Recheck parity. This audit does not authorize cutover. [S2:1598-1601, S2:1634-1659, E8] |

## Support rings

| Claim | Required scope | Current classification |
| --- | --- | --- |
| Modern TypeScript core, Wave 3 | At least four strict `.ts` projects and 100,000 non-generated lines, with utilities, classes, callbacks, multi-package Bundler/ESM, and consumed `.d.ts`. All project gates apply. | incomplete. The five-repository proposal has 224,500 lines but no passing ring. Without Effect it has 57,791. [S1:1217-1219, S1:1241-1251, E9] |
| NodeNext and TSX, Wave 4 | Package/mode facts, real TSX/function components, advanced classes/flow, and standard libraries. Basic intrinsic/function JSX is not managed/class JSX. | incomplete. Inputs are inventoried only. M01 is porting and M04 is blocked. [S1:952-968, S1:1030-1039, S1:1253-1257, E8-E10] |
| Complete ecosystem, Wave 5 | Core plus NodeNext, TSX, and mixed JavaScript/JSDoc projects on the same canonical path without private skips/fallback. | incomplete. Svelte and React Hook Form input preparation is not semantic equality. [S1:1220-1237, S1:1042-1048, E1, E9] |
| Frozen-epoch parity and maintainability | Complete configuration accounting, exact artifacts, semantic dependency closure, then controlled roll-forward. | missing completion evidence. Partial shards and reviewed providers do not prove this. [S1:1259-1270, E2, E3, E8] |

General JS emit, complete declaration emit, transforms, watch/build, fourslash,
and language-service parity are not additional gates here, except required
checker queries/artifacts. Keep emit-only cases visible without scoring them as
semantic success. [S1:62-72]

## Next actions

1. Finish the accepted composition, then seal its exact-SHA full verification,
   strict Clippy/rustdoc, semantic smoke, semantic milestone, and per-merge delta.
2. Repair project construction and the Go/Rust replay evidence. Close graph and
   mode gaps before comparing artifact bytes. Preserve failed evidence unchanged.
3. Review and freeze the project manifest, including dependency/library facts and
   Go hashes. Run every entry twice with forced replay. Do not replace hard inputs.
4. Close all corpus frontiers and the complete configuration ledger. Then collect
   matched release benchmarks, perform the later-epoch port, and gate cutover.
5. Replace the multiple stale "current" summaries with one checkpoint-bound table.

## Exact references

S1 is [the completion goal](typechecker-completion-goal.md) at `8357dac3`.
S2 is [the port goal](typechecker-port-goal.md) at the same commit.
Suffixes above are line numbers.
Evidence paths below are in the main workspace, not the audit worktree.

- E1: `tools/ts_fixture/manifests/{checker-smoke-v1,checker-milestone-v1}.json`,
  fields `.upstream`, `.policy`, `.coverage`, `.digest`, `.variants[].variantKey`.
  `git ls-tree 8357dac3 tools/ts_fixture/manifests` has no modern-project manifest.
- E2: `target/wave137-combined-semantic-smoke.json`, `.provenance.rust`
  at clean `8357dac3`, `.summary`, `.semanticArtifacts`, and variant
  `v1:7a479af7f8ada8b68cb4d2cc02ec5bbb` for the expando type mismatch.
  Report SHA-256: `927cf97cb834c87da2fb2b3290f7438eea9de87da3a7e8f7b81e739782499d7a`.
- E3: `target/wave131-combined-milestone.json`, `.provenance.rust.sha`
  is `74fd417a`. Fields `.provenance.invocation`, `.summary`, `.semanticArtifacts`.
- E4: `target/project-evidence/{hono-go,ts-pattern-go}/phase-correct/result.json`,
  `.parity_claimed`, `.fresh_diagnostic_equality`, `.processes[].outcome`,
  `.processes[].strict_pointer_checks`. Their `attempt-1/process-a/report.json`
  records `.fresh_diagnostics` and `.programs[].graph.missing_evidence`.
- E5: `target/project-evidence/wave132-binder-families/project-summary.json`,
  fields `.source.sha`, `.projects[].runs[]`, `.limitations`. Query's
  `target/project-evidence/query-core-module-target-wave132/after-154c696b.json`,
  field `.construction`. `target/project-evidence/{hono-rust,ts-pattern-rust,query-core-rust}/comparison.json`,
  `.claims`, `.comparisons`, `.limitations`. The original Rust `report-a.json`
  files record `.provenance.suppliedBuildRecord.profile` as dev, not release.
- E6: `target/wave136-combined-workspace.log` has 169 result summaries, 6,460
  passes and two failures at lines 4768 and 4949. Later logs are
  `target/wave136-alias-module-unit-tests.log` and
  `target/wave136-alias-property-tests.log`. Neither is a full workspace run.
- E7: `git diff --stat 8406fc34..8357dac3` changes 38 files, including runtime
  checker/module code. `target/wave136-go-composition-path-tests.log` records
  27 path controls. `tools/ts_fixture/go_project_oracle/README.md:10` defines
  prepare mode as no Go invocation. `target/wave137-combined-check.log` finishes
  its dev check in 1m 04s with warnings. The smoke log completes with E2's counts.
  Compared with `target/wave134-combined-semantic-smoke.json` at clean `985ba5f5`,
  E2 has identical ordered keys and one exact win, `exportAssignmentMerging1.ts`,
  key `v1:fbe66757fabb0773c39951e7d9f91819`. Other changed blocker details are
  `strictBestCommonSupertype.ts` and `invocationErrorRecovery.ts`.
- E8: `docs/typechecker-port-map.tsv:4` H02, `:20` T07, `:45` C00, `:46` C01,
  `:47` C02. Blocked rows are B04, A15, M03, M04, C02. S1:394-421 contains the
  stale current-count text. `docs/typechecker-wave131-status.md` limits its claims.
- E9: `/tmp/wave127-modern-input-audit/inventory.json`, `.projects[].groups` and
  `.projects[].configs`. SHA-256 verified as
  `8efa4241dbd49de8e0788add7bf4f3bf5291387cf74adad71c04a6d29803b1f3`.
  `docs/typechecker-modern-project-inputs.md:1` calls this an inventory, not a ring.
- E10: `docs/project-graph-limitations.md:34-110` records input-retention limits,
  package identity/realpath gaps, and the remaining NodeNext/Realpath differences.
  `tools/ts_fixture/go_project_oracle/README.md:147` records option and graph limits.
