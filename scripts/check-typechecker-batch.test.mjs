import assert from "node:assert/strict";
import test from "node:test";
import { BASELINE_SHA256, CHECKPOINT_SHA256, checkBatch, readPinnedJson } from "./check-typechecker-batch.mjs";

const SOURCE = "a".repeat(64);
const RESULT = "b".repeat(64);
const tally = rows => ({ tests: rows.length, PASS: rows.filter(row => row.status === "PASS").length,
  FAIL: rows.filter(row => row.status === "FAIL").length, harnesses: new Set(rows.map(row => row.harness)).size });

function fixture() {
  const rows = Array.from({ length: 6330 }, (_, index) => ({ harness: index < 6328 ? "checker" : index === 6328 ? "compiler" : "fixture",
    name: `case_${index}`, status: "PASS", logStage: index < 6328 ? "checker" : index === 6328 ? "compiler" : "fixture" }));
  rows.push({ harness: "checker", name: "older_unprotected_failure", status: "FAIL", logStage: "checker" });
  const accepted = rows.slice(0, 6055).map(row => ({ harness: row.harness, name: row.name, accepted: { status: "PASS" } }));
  const closure = { normalClosure: true, sourceUnchanged: true, sourceFingerprint: SOURCE };
  const baseline = { closure, summary: tally(rows), originalAccepted6055: { exactLedger: accepted },
    versusPreviousFullBaseline: { exactLedger: rows.filter(row => row.logStage === "checker").map(row => ({ ...row, current: { status: row.status } })) },
    closedStages: Object.fromEntries(["compiler", "fixture"].map(stage => [stage, { closure, outcomes: rows.filter(row => row.logStage === stage) }])) };
  const candidate = { schemaVersion: 1, status: "ALL_STAGES_CLOSED", sourceFingerprint: SOURCE,
    closure: { normalClosures: true, sourceUnchangedThroughAllStages: true, sourceFingerprint: SOURCE },
    expectationChangesApplied: false, waiversApplied: false, summary: tally(rows), current: { ...tally(rows), ABSENT: 0, UNRUN: 0 },
    versusFullBaseline: { exactLedger: rows.map(row => ({ harness: row.harness, name: row.name, current: { status: row.status, logStage: row.logStage } })) }, addedNames: [],
    stages: ["checker", "compiler", "fixture"].map(stage => ({ stage, path: `${stage}.log`, sourceFingerprint: SOURCE,
      normalClosure: true, closureReceipt: `closed-${stage}`, counts: tally(rows.filter(row => row.logStage === stage)), exitCode: stage === "checker" ? 101 : 0 })),
    originalAccepted6055: { exactLedger: accepted.map(row => ({ ...row, current: { status: "PASS" } })) } };
  const verdict = (role, agent) => ({ role, agent, batchId: "batch-1", verdict: "PASS", sourceFingerprint: SOURCE, fullResultSha256: RESULT });
  const state = { schemaVersion: 1, phase: "initial-recovery", status: "ready", decision: "REVIEW", goalAuthorization: "Theo authorized initial recovery.", preservedCandidateSourceFingerprint: SOURCE,
    acceptedBaseline: { path: "checkpoint.json", sha256: CHECKPOINT_SHA256 },
    originalAccepted: { path: "baseline.json", sha256: BASELINE_SHA256, expectedNames: 6055 },
    laterPassBaseline: { path: "baseline.json", sha256: BASELINE_SHA256, expectedPasses: 6330 },
    batch: { id: "batch-1", implementer: "writer", hypothesis: "hypothesis-1", sourceFingerprint: SOURCE,
      fullResult: { path: "candidate.json", sha256: RESULT }, recoveryRevision: 1,
      recoveryHistory: [{ revision: 1, hypothesis: "hypothesis-1", sourceFingerprint: SOURCE, fullResultSha256: RESULT }],
      auditor: verdict("audit_accepted_roster", "auditor"), reviewer: verdict("production-review", "reviewer") } };
  return { state, baseline, candidate, read: ref => {
    if (ref.path === "checkpoint.json") return {};
    if (ref.path === "baseline.json") return baseline;
    if (ref.path === "candidate.json") return candidate;
    throw new Error("Missing synthetic evidence.");
  } };
}

function refresh(candidate) {
  const rows = candidate.versusFullBaseline.exactLedger.map(row => ({ ...row, ...row.current }));
  candidate.summary = tally(rows);
  candidate.current = { ...tally(rows), ABSENT: 0, UNRUN: 0 };
  for (const stage of candidate.stages) {
    stage.counts = tally(rows.filter(row => row.logStage === stage.stage));
    stage.exitCode = stage.counts.FAIL ? 101 : 0;
  }
}

function stopped(f, pattern) {
  const result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "STOP");
  if (pattern) assert.match(result.reasons.join(" "), pattern);
  return result;
}

test("complete pinned prerequisite passes, without claiming corpus parity", () => {
  const f = fixture(), result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "PASS");
  assert.deepEqual(result.counts, { originalAccepted: 6055, originalRetained: 6055, laterPasses: 6330, laterRetained: 6330 });
  assert.match(result.scope, /corpus parity need independent review/);
});

test("paused state and absent batch fail closed before evidence reads", () => {
  const f = fixture(); f.state.status = "paused"; f.state.batch = null;
  assert.equal(checkBatch(f.state, () => assert.fail("No evidence read needed")).verdict, "STOP");
});

test("missing evidence and different same-size baseline identity stop", () => {
  const f = fixture();
  assert.equal(checkBatch(f.state, () => { throw new Error("Missing evidence"); }).verdict, "STOP");
  f.state.originalAccepted.sha256 = "c".repeat(64);
  stopped(f, /baseline identity/);
  f.state.originalAccepted.sha256 = BASELINE_SHA256;
  f.state.acceptedBaseline.sha256 = "c".repeat(64);
  stopped(f, /checkpoint identity/);
});

test("real evidence loader rejects missing files and hash mismatches", () => {
  assert.throws(() => readPinnedJson({ path: "scripts/does-not-exist-guard-fixture.json", sha256: RESULT }), /Missing evidence/);
  assert.throws(() => readPinnedJson({ path: "scripts/check-typechecker-batch.mjs", sha256: RESULT }), /hash mismatch/);
});

test("one exact accepted PASS loss is counted in both overlapping baselines", () => {
  const f = fixture();
  f.candidate.versusFullBaseline.exactLedger[0].current.status = "FAIL";
  f.candidate.originalAccepted6055.exactLedger[0].current.status = "FAIL";
  refresh(f.candidate);
  const result = stopped(f);
  assert.equal(result.losses.originalAccepted.length, 1);
  assert.equal(result.losses.laterPasses.length, 1);
  assert.equal(result.losses.originalAccepted[0].name, "case_0");
});

test("later nonaccepted PASS loss is protected independently", () => {
  const f = fixture(); f.candidate.versusFullBaseline.exactLedger[6100].current.status = "FAIL"; refresh(f.candidate);
  const result = stopped(f);
  assert.equal(result.losses.originalAccepted.length, 0);
  assert.equal(result.losses.laterPasses[0].name, "case_6100");
});

test("missing exact name is ABSENT, never a renamed-name waiver", () => {
  const f = fixture(); f.candidate.versusFullBaseline.exactLedger[0].name = "renamed_case_0";
  f.candidate.originalAccepted6055.exactLedger[0].current.status = "ABSENT";
  const result = stopped(f);
  assert.deepEqual(result.losses.originalAccepted[0], { harness: "checker", name: "case_0", status: "ABSENT" });
});

test("candidate accepted ledger cannot replace or hide an original name", () => {
  const f = fixture(); f.candidate.originalAccepted6055.exactLedger[0].name = "renamed";
  stopped(f, /renamed or omitted/);
});

test("source mismatch, partial stages, duplicate names and wrong totals stop", () => {
  for (const change of [
    f => { f.candidate.sourceFingerprint = RESULT; },
    f => { f.candidate.stages[0].sourceFingerprint = RESULT; },
    f => { f.candidate.stages.pop(); },
    f => { f.candidate.versusFullBaseline.exactLedger.push(f.candidate.versusFullBaseline.exactLedger[0]); },
    f => { f.candidate.summary.PASS++; },
    f => { f.candidate.current.UNRUN = 1; },
    f => { f.candidate.status = "CHECKER_CLOSED"; },
    f => { f.candidate.stages[0].normalClosure = false; },
  ]) { const f = fixture(); change(f); stopped(f); }
});

test("missing, STOP, stale, or non-independent verdicts stop", () => {
  for (const change of [
    f => { delete f.state.batch.reviewer; },
    f => { f.state.batch.reviewer.verdict = "STOP"; },
    f => { f.state.batch.reviewer.batchId = "older-batch"; },
    f => { f.state.batch.auditor.sourceFingerprint = RESULT; },
    f => { f.state.batch.auditor.fullResultSha256 = SOURCE; },
    f => { f.state.batch.reviewer.agent = "auditor"; },
    f => { f.state.batch.reviewer.role = "audit_accepted_roster"; },
    f => { f.state.batch.reviewer.agent = "writer"; },
  ]) { const f = fixture(); change(f); stopped(f); }
});

test("failed revisions remain counted and may have no full result", () => {
  const f = fixture(); f.state.batch.recoveryRevision = 2;
  f.state.batch.recoveryHistory.unshift({ revision: 1, hypothesis: "hypothesis-1", sourceFingerprint: RESULT, fullResultSha256: null });
  f.state.batch.recoveryHistory[1].revision = 2;
  assert.equal(checkBatch(f.state, f.read).verdict, "PASS");
  f.state.batch.recoveryHistory[1].fullResultSha256 = null;
  stopped(f, /Current history row/);
});

test("fixed limits reject extra revisions, hypotheses, and counter resets", () => {
  const base = fixture();
  for (const hypotheses of [["a", "a", "a"], ["a", "b", "c"], ["a", "a", "b", "b", "b"]]) {
    const f = fixture();
    f.state.batch.recoveryHistory = hypotheses.map((hypothesis, i) => ({ revision: i + 1, hypothesis, sourceFingerprint: SOURCE, fullResultSha256: RESULT }));
    f.state.batch.recoveryRevision = hypotheses.length;
    f.state.batch.hypothesis = hypotheses.at(-1);
    stopped(f, /[Ll]imit|1 to 4/);
  }
  base.state.batch.maxRecoveryRevisions = 99; stopped(base, /fixed at 4/);
  delete base.state.batch.maxRecoveryRevisions;
  base.state.batch.recoveryRevision = 0; stopped(base, /history length/);
  base.state.batch.recoveryRevision = 1;
  base.state.phase = "new-phase"; stopped(base, /initial-recovery only/);
});

test("waivers, expectation exceptions, and missing hypotheses stop", () => {
  for (const field of ["waiversApplied", "expectationChangesApplied"]) {
    const f = fixture(); f.candidate[field] = true; stopped(f, /human review/);
  }
  const f = fixture(); f.state.batch.hypothesis = ""; stopped(f, /hypothesis/);
});

test("ready state must remove STOP and include goal authorization", () => {
  const f = fixture(); f.state.decision = "STOP"; stopped(f, /decision/);
  f.state.decision = "REVIEW";
  for (const value of [null, undefined, "", {}]) {
    f.state.goalAuthorization = value; stopped(f, /authorization/);
  }
});
