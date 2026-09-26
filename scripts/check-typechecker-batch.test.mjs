import assert from "node:assert/strict";
import test from "node:test";
import { BASELINE_SHA256, CHECKPOINT_SHA256, INHERITED_PIN, checkBatch, readPinnedJson } from "./check-typechecker-batch.mjs";

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

function continuationFixture() {
  const f = fixture();
  f.state.phase = "recovery-continuation";
  f.state.continuationAuthorization = { authorized: true, date: "2026-09-08T03:26:02Z",
    instruction: "Theo authorized continued Query core and Hono recovery.",
    scope: "Preserve all revision history, protected passes and independent review." };
  const hypotheses = ["hypothesis-1", "hypothesis-1", "hypothesis-2", "hypothesis-2", "hypothesis-3", "hypothesis-3", "hypothesis-3"];
  f.state.batch.recoveryHistory = hypotheses.map((hypothesis, index) => ({ revision: index + 1, hypothesis,
    sourceFingerprint: String(index + 1).repeat(64), fullResultSha256: index === 3 ? "c".repeat(64) : null }));
  Object.assign(f.state.batch.recoveryHistory.at(-1), { sourceFingerprint: SOURCE, fullResultSha256: RESULT });
  f.state.batch.recoveryRevision = hypotheses.length;
  f.state.batch.hypothesis = hypotheses.at(-1);
  return f;
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
  assert.deepEqual(result.counts, { originalAccepted: 6055, originalRetained: 6055, laterPasses: 6330, laterRetained: 6330,
    inheritedOriginal: null, inheritedLater: null });
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
  base.state.phase = "new-phase"; stopped(base, /Unsupported recovery phase/);
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

test("authorized continuation retains the initial trial and permits later revisions", () => {
  const f = continuationFixture(), before = structuredClone(f.state);
  const result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "PASS");
  assert.deepEqual(result.counts, { originalAccepted: 6055, originalRetained: 6055, laterPasses: 6330, laterRetained: 6330,
    inheritedOriginal: null, inheritedLater: null });
  assert.match(result.scope, /Later added passes and corpus parity need independent review/);
  assert.deepEqual(f.state, before);
});

test("continuation requires explicit saved authorization before evidence reads", () => {
  for (const change of [
    f => { delete f.state.continuationAuthorization; },
    f => { f.state.continuationAuthorization = null; },
    f => { f.state.continuationAuthorization = "Theo said keep going"; },
    f => { f.state.continuationAuthorization = {}; },
    f => { f.state.continuationAuthorization.authorized = false; },
    f => { f.state.continuationAuthorization.authorized = "true"; },
    f => { f.state.continuationAuthorization.instruction = " "; },
    f => { f.state.continuationAuthorization.scope = ""; },
    f => { delete f.state.continuationAuthorization.date; },
    f => { f.state.continuationAuthorization.date = "invalid"; },
    f => { f.state.continuationAuthorization.date = "2026-99-99T00:00:00Z"; },
  ]) {
    const f = continuationFixture(); change(f);
    const result = checkBatch(f.state, () => assert.fail("Unauthorized continuation must not read evidence"));
    assert.equal(result.verdict, "STOP");
    assert.match(result.reasons.join(" "), /Continuation requires explicit saved authorization/);
  }
});

test("saved continuation authorization does not change initial recovery limits", () => {
  const f = continuationFixture(); f.state.phase = "initial-recovery";
  stopped(f, /1 to 4 measured revisions/);
  f.state.batch.recoveryHistory = f.state.batch.recoveryHistory.slice(0, 3);
  f.state.batch.recoveryRevision = 3;
  for (const row of f.state.batch.recoveryHistory) row.hypothesis = "hypothesis-1";
  stopped(f, /two revisions per hypothesis/);
  f.state.batch.recoveryHistory[2].hypothesis = "hypothesis-2";
  f.state.batch.maxRecoveryRevisions = 99;
  stopped(f, /fixed at 4/);
});

test("continuation rejects missing, reordered, duplicated and reset history", () => {
  for (const change of [
    f => { delete f.state.batch.recoveryHistory; },
    f => { f.state.batch.recoveryHistory = []; f.state.batch.recoveryRevision = 0; },
    f => { f.state.batch.recoveryHistory = f.state.batch.recoveryHistory.slice(0, 4); f.state.batch.recoveryRevision = 4; },
    f => { f.state.batch.recoveryRevision = 1; },
    f => { f.state.batch.recoveryHistory.shift(); f.state.batch.recoveryRevision--; },
    f => { [f.state.batch.recoveryHistory[0], f.state.batch.recoveryHistory[1]] = [f.state.batch.recoveryHistory[1], f.state.batch.recoveryHistory[0]]; },
    f => { f.state.batch.recoveryHistory[2] = { ...f.state.batch.recoveryHistory[1] }; },
    f => { f.state.batch.recoveryHistory[4].revision = 1; },
    f => { f.state.batch.recoveryHistory[5].revision = 7; },
    f => { f.state.batch.recoveryHistory[0].sourceFingerprint = "invalid"; },
    f => { delete f.state.batch.recoveryHistory[0].fullResultSha256; },
  ]) { const f = continuationFixture(); change(f); stopped(f, /history|History/); }
});

test("continuation cannot rewrite initial history to exceed its hypothesis limits", () => {
  for (const change of [
    f => { f.state.batch.recoveryHistory[2].hypothesis = "hypothesis-1"; },
    f => { f.state.batch.recoveryHistory[3].hypothesis = "hypothesis-3"; },
  ]) { const f = continuationFixture(); change(f); stopped(f, /two hypotheses, two revisions per hypothesis/); }
});

test("continuation binds the latest history row to the current source, hypothesis and full result", () => {
  for (const change of [
    row => { row.sourceFingerprint = "d".repeat(64); },
    row => { row.hypothesis = "older-hypothesis"; },
    row => { row.fullResultSha256 = "d".repeat(64); },
    row => { row.fullResultSha256 = null; },
  ]) {
    const f = continuationFixture(); change(f.state.batch.recoveryHistory.at(-1));
    stopped(f, /Current history row does not match/);
  }
});

test("continuation rejects protected lost passes even when another test recovers", () => {
  for (const index of [0, 6100]) {
    const f = continuationFixture();
    f.candidate.versusFullBaseline.exactLedger[index].current.status = "FAIL";
    if (index < 6055) f.candidate.originalAccepted6055.exactLedger[index].current.status = "FAIL";
    f.candidate.versusFullBaseline.exactLedger.at(-1).current.status = "PASS";
    refresh(f.candidate);
    const result = stopped(f, /PASS names are FAIL or ABSENT/);
    assert.equal(result.losses.originalAccepted.length, index < 6055 ? 1 : 0);
    assert.deepEqual(result.losses.laterPasses, [{ harness: "checker", name: `case_${index}`, status: "FAIL" }]);
  }
});

test("continuation rejects missing protected names, incomplete evidence and non-independent verdicts", () => {
  for (const change of [
    f => { f.candidate.versusFullBaseline.exactLedger[0].name = "renamed_case_0"; f.candidate.originalAccepted6055.exactLedger[0].current.status = "ABSENT"; },
    f => { f.candidate.closure.normalClosures = false; },
    f => { f.candidate.stages[1].sourceFingerprint = RESULT; },
    f => { f.state.batch.fullResult.path = "missing.json"; },
    f => { f.state.acceptedBaseline.sha256 = RESULT; },
    f => { f.candidate.versusFullBaseline.exactLedger[0].current.status = "UNRUN"; },
    f => { f.candidate.waiversApplied = true; },
    f => { f.candidate.expectationChangesApplied = true; },
    f => { delete f.state.batch.auditor; },
    f => { delete f.state.batch.reviewer; },
    f => { f.state.batch.auditor.verdict = "STOP"; },
    f => { f.state.batch.reviewer.verdict = "STOP"; },
    f => { f.state.batch.reviewer.sourceFingerprint = RESULT; },
    f => { f.state.batch.reviewer.batchId = "older-batch"; },
    f => { f.state.batch.reviewer.fullResultSha256 = SOURCE; },
    f => { f.state.batch.reviewer.agent = "writer"; },
    f => { f.state.batch.reviewer.agent = "auditor"; },
    f => { f.state.batch.reviewer.role = "audit_accepted_roster"; },
    f => { f.state.decision = "STOP"; },
    f => { f.state.status = "active"; },
  ]) { const f = continuationFixture(); change(f); stopped(f); }
});

// A candidate with inherited losses (case_0, and later-only case_6100) and an inherited
// result that already had them. PIN stands in for the real INHERITED_PIN.
const PIN = { sha256: "d".repeat(64), originalAccepted: 1, laterPasses: 2 };
function optInFixture() {
  const f = continuationFixture();
  f.candidate.versusFullBaseline.exactLedger[0].current.status = "FAIL";
  f.candidate.originalAccepted6055.exactLedger[0].current.status = "FAIL";
  f.candidate.versusFullBaseline.exactLedger[6100].current.status = "FAIL";
  refresh(f.candidate);
  const inherited = { versusFullBaseline: { exactLedger: f.candidate.versusFullBaseline.exactLedger.map(row => ({ ...row, current: { ...row.current } })) }, addedNames: [] };
  const read = f.read;
  f.read = ref => ref.path === "inherited.json" ? inherited : read(ref);
  f.state.acceptanceRuleChanges = [{ id: "opt-in-crate-no-new-loss", batchId: "batch-1", approvedBy: "Theo", date: "2026-09-25T06:00:00Z",
    instruction: "Opt-in crate rule", inheritedResult: { path: "inherited.json", sha256: PIN.sha256 },
    inheritedLosses: { originalAccepted: 1, laterPasses: 2 } }];
  return { ...f, inherited };
}

test("opt-in crate rule passes inherited losses but reports them", () => {
  const f = optInFixture(), result = checkBatch(f.state, f.read, PIN);
  assert.equal(result.verdict, "PASS");
  assert.equal(result.rule, "opt-in-crate-no-new-loss");
  assert.equal(result.counts.inheritedOriginal, 1);
  assert.equal(result.counts.inheritedLater, 2);
  assert.equal(result.losses.originalAccepted.length, 1);
  // The real pin (290/15, R96 hash) does not match this rule, so the CLI default stops.
  assert.equal(checkBatch(f.state, f.read).verdict, "STOP");
  assert.deepEqual(INHERITED_PIN, { sha256: "e7838ed863c42bc2271981c680d2fc46bb6a98f3171c8554b2d040ca9277d6b7", originalAccepted: 290, laterPasses: 15 });
});

test("opt-in crate rule still stops on a new loss, a count drift, or another batch", () => {
  let f = optInFixture();
  const stop = (g, pattern) => { const r = checkBatch(g.state, g.read, PIN); assert.equal(r.verdict, "STOP"); assert.match(r.reasons.join(" "), pattern); };
  f.candidate.versusFullBaseline.exactLedger[1].current.status = "FAIL";
  f.candidate.originalAccepted6055.exactLedger[1].current.status = "FAIL";
  refresh(f.candidate);
  stop(f, /not inherited/);
  f = optInFixture(); f.state.acceptanceRuleChanges[0].inheritedLosses.originalAccepted = 2;
  stop(f, /pinned constants/);
  f = optInFixture(); f.state.acceptanceRuleChanges[0].inheritedResult.sha256 = "e".repeat(64);
  stop(f, /pinned constants/);
  f = optInFixture(); f.inherited.versusFullBaseline.exactLedger[0].current.status = "PASS";
  stop(f, /Inherited loss counts/);
  f = optInFixture(); f.state.acceptanceRuleChanges[0].batchId = "other";
  stop(f, /original accepted PASS names/);
  f = optInFixture(); delete f.state.acceptanceRuleChanges[0].approvedBy;
  stop(f, /Theo's saved approval/);
});

test("approved unbound rows may keep a null source, never the current row", () => {
  const f = continuationFixture();
  Object.assign(f.state.batch.recoveryHistory[5], { sourceFingerprint: null, fullResultSha256: null });
  stopped(f, /Invalid or reset recovery history/);
  f.state.acceptanceRuleChanges = [{ id: "unbound-history-rows", batchId: "batch-1", approvedBy: "Theo", date: "2026-09-25T06:00:00Z",
    instruction: "Accept as recorded gaps", revisions: [6, 7] }];
  assert.equal(checkBatch(f.state, f.read).verdict, "PASS");
  Object.assign(f.state.batch.recoveryHistory[6], { sourceFingerprint: null });
  stopped(f, /Invalid or reset recovery history/);
});
