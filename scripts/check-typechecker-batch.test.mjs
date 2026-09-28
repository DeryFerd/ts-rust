import assert from "node:assert/strict";
import test from "node:test";
import { BASELINE_SHA256, CARRY_FORWARD_RULE, CHECKPOINT_SHA256, GOPORT_RULE, INHERITED_PIN, checkBatch, readEvidenceFile } from "./check-typechecker-batch.mjs";

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
  assert.throws(() => readEvidenceFile({ path: "scripts/does-not-exist-guard-fixture.json", sha256: RESULT }), /Missing evidence/);
  assert.throws(() => readEvidenceFile({ path: "scripts/check-typechecker-batch.mjs", sha256: RESULT }), /hash mismatch/);
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

// Revision 7 carries the full result of measured revision 6 (source FROM). Only
// crates/ts_goport changed, so both rows have the same roster fingerprint.
const FROM = "e".repeat(64), ROSTER = "f".repeat(64);
function carryFixture() {
  const f = continuationFixture();
  for (const item of [f.candidate, f.candidate.closure, ...f.candidate.stages]) item.sourceFingerprint = FROM;
  Object.assign(f.state.batch.recoveryHistory[5], { sourceFingerprint: FROM, fullResultSha256: RESULT, status: "full_measured", rosterFingerprint: ROSTER });
  f.state.batch.rosterFingerprint = ROSTER;
  f.state.batch.rosterCarryForward = { fromRevision: 6, fromSourceFingerprint: FROM, rosterFingerprint: ROSTER };
  f.state.acceptanceRuleChanges = [{ id: CARRY_FORWARD_RULE, batchId: "*", standing: true, approvedBy: "Theo", date: "2026-09-28T09:00:00Z",
    instruction: "Skip the roster run when only crates/ts_goport changed.", scope: "Every batch. Equal roster_fp.py hashes." }];
  return f;
}

test("roster carry-forward checks the earlier measured result and reports it", () => {
  const f = carryFixture(), result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "PASS");
  assert.deepEqual(result.rosterCarryForward, { rule: CARRY_FORWARD_RULE, fromRevision: 6, fromSourceFingerprint: FROM });
  const plain = fixture();
  assert.equal("rosterCarryForward" in checkBatch(plain.state, plain.read), false);
  delete f.state.batch.rosterCarryForward;
  stopped(f, /Full result source mismatch/);
});

test("roster carry-forward stops without the rule, equal fingerprints or an earlier measured row", () => {
  const from = f => f.state.batch.recoveryHistory[5];
  for (const [change, pattern] of [
    [f => { f.state.acceptanceRuleChanges = []; }, /standing goport-only-roster-carry-forward rule/],
    [f => { f.state.acceptanceRuleChanges[0].standing = false; }, /standing/],
    [f => { f.state.acceptanceRuleChanges[0].batchId = "batch-1"; }, /standing/],
    [f => { delete f.state.acceptanceRuleChanges[0].approvedBy; }, /standing/],
    [f => { f.state.batch.rosterFingerprint = "d".repeat(64); }, /differs from the batch roster fingerprint/],
    [f => { f.state.batch.rosterFingerprint = f.state.batch.rosterCarryForward.rosterFingerprint = "roster"; }, /SHA-256/],
    [f => { from(f).rosterFingerprint = "d".repeat(64); }, /differs from the carry-forward record/],
    [f => { from(f).fullResultSha256 = "d".repeat(64); }, /differs from the carry-forward record/],
    [f => { from(f).sourceFingerprint = "d".repeat(64); }, /differs from the carry-forward record/],
    [f => { from(f).status = "focused_only"; }, /not a full_measured revision/],
    [f => { from(f).rosterCarryForward = { fromRevision: 5 }; }, /not a full_measured revision/],
    [f => { f.state.batch.rosterCarryForward.fromRevision = 7; }, /earlier revision/],
    [f => { f.state.batch.auditor.sourceFingerprint = FROM; }, /Verdict is not bound/],
  ]) { const f = carryFixture(); change(f); stopped(f, pattern); }
});

test("only the carry-forward rule may use batchId *", () => {
  const f = optInFixture(); f.state.acceptanceRuleChanges[0].batchId = "*";
  assert.match(checkBatch(f.state, f.read, PIN).reasons.join(" "), /original accepted PASS names are FAIL or ABSENT\./);
});

// A goport batch (protectedSet "goport") after an accepted legacy batch-0. The test base is
// the rule baseline; the gate base is batch-0's gate. case_* roster evidence is not present.
const GO_PIN = "52168999f3dc", COMMIT = "0123456789abcdef0123456789abcdef01234567";
const NOTE = "legacy-removal-rule-approval-2026-09-28";
const BASELINE_PATH = "docs/goport-protected/tests-r131.json";
function goportFixture() {
  const f = continuationFixture();
  const { state } = f;
  for (const field of ["acceptedBaseline", "originalAccepted", "laterPassBaseline"]) delete state[field];
  state[NOTE] = { quote: "i approve any rule changes that allow removing the legacy code" };
  state.acceptanceRuleChanges = [{ id: GOPORT_RULE, batchId: "*", standing: true, approvedBy: "Theo", date: "2026-09-28T22:00:00Z",
    instruction: "i approve any rule changes that allow removing the legacy code", scope: "Every batch with protectedSet goport.",
    protectedSet: "goport", baseline: { path: BASELINE_PATH, sha256: "1".repeat(64) }, approvalNote: NOTE }];
  const batch = state.batch;
  delete batch.fullResult;
  const bound = { goportTestsSha256: "2".repeat(64), gateSha256: "7".repeat(64) };
  Object.assign(batch.recoveryHistory.at(-1), { fullResultSha256: null, status: "full_measured", ...bound });
  for (const verdict of [batch.auditor, batch.reviewer]) {
    delete verdict.fullResultSha256;
    Object.assign(verdict, bound);
  }
  const files = {};
  const put = (path, digit, value) => { files[path] = { sha256: digit.repeat(64), value }; return { path, sha256: digit.repeat(64) }; };
  const base = { source: { commit: "50b0593b5", tree: "a4aae8d62022", testbinSha256: "9".repeat(64) }, pin: GO_PIN, suites: {
    "ts_goport lib": { "api::t1": "ok", "api::t2": "ok", "api::slow": "ignored" },
    "go_baselines default": { "b::one": "ok", "b::two": "failed" },
    "ts_scanner lib": { "scan::a": "ok" } } };
  const results = structuredClone(base);
  results.source.commit = COMMIT.slice(0, 9);
  results.suites["go_baselines default"]["b::two"] = "ok";
  results.suites["ts_goport lib"]["api::t3"] = "ok";
  const gateItems = [["measure/query", "MATCH"], ["typesyms/effect", "ALLOWED"], ["editor/query-core/long", "FAIL"], ["corpus-diag/00001", "MATCH"]]
    .map(([id, status]) => ({ stage: id.split("/")[0], id, status }));
  const gateBase = { commit: "b2b7dca1fc694b34dcf2303c8b013d544b043374", upstreamPin: GO_PIN, results: gateItems };
  const gateNew = { commit: COMMIT, upstreamPin: GO_PIN, results: [...structuredClone(gateItems), { stage: "sweep", id: "sweep/new", status: "MATCH" }] };
  put(BASELINE_PATH, "1", base);
  const manifest = put("measure/r40/manifest.json", "4", { sourceFingerprint: SOURCE });
  put("quality.json", "5", { sourceFingerprint: SOURCE, rustfmtExit: 0, clippyExit: 0, tsGoportWarnings: 0, fingerprintUnchanged: true });
  put("lsp/summary.md", "6", "summary");
  const run = { complete: true, exitCode: 0, diagnostics: 0, matchesOracle: true, sourceFingerprint: SOURCE,
    runs: [{ manifest: manifest.path, sha256: manifest.sha256 }] };
  const tests = put("tests-new.json", "2", results);
  const gate = put("gate-new.json", "7", gateNew);
  const previousGate = put("gate-base.json", "8", gateBase);
  const archive = put("docs/typechecker-batches/batch-0.json", "3", { id: "batch-0", compilerAccepted: true,
    gate: { manifest: previousGate.path, sha256: previousGate.sha256 } });
  Object.assign(batch, { protectedSet: "goport", commit: COMMIT.slice(0, 9), upstreamPin: { from: GO_PIN, to: GO_PIN },
    previousBatch: { id: "batch-0", archive },
    protectedBase: { batch: "batch-0", revision: 6, tests: { path: BASELINE_PATH, sha256: "1".repeat(64) }, gate: previousGate },
    goportTests: { results: tests.path, sha256: tests.sha256, base: BASELINE_PATH, baseSha256: "1".repeat(64),
      compare: { lost: 0, absent: [], unrun: 0, retained: 4, recovered: 1 } },
    gate: { manifest: gate.path, sha256: gate.sha256 },
    gateCompare: { base: previousGate.path, baseSha256: previousGate.sha256, new: gate.path, sha256: gate.sha256, regressions: 0 },
    ordinaryQuery: run, latestHono: structuredClone(run),
    languageServerOracle: { summary: "lsp/summary.md", result: "257,129 requests: 0 diff, 0 crash, 0 timeout, 0 goport_error", host: "cup2" },
    quality: { record: "quality.json", result: "rustfmt 0, clippy 0" }, qualityEvidence: { sourceFingerprint: SOURCE },
    openDefects: [{ id: "editor-long-growth", status: "open; lsshells M2 running" }] });
  const read = (ref, { pinned = true } = {}) => {
    const file = files[ref?.path];
    if (!file) throw new Error(`Missing evidence: ${ref?.path}.`);
    if (pinned && ref.sha256 !== file.sha256) throw new Error(`Evidence hash mismatch: ${ref.path}.`);
    return file.value;
  };
  return { state, files, put, results, gateNew, read };
}

test("goport batch passes on its own tests and gate, without roster evidence", () => {
  const f = goportFixture(), result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "PASS", result.reasons.join(" "));
  assert.equal(result.protectedSet, "goport");
  assert.equal(result.rule, GOPORT_RULE);
  assert.deepEqual(result.counts, {
    goportTests: { baseOk: 4, retained: 4, recovered: 1, removedByMap: 0, newNames: 1, lost: 0, absent: 0, unrun: 0 },
    gate: { baseItems: 4, items: 5, regressions: 0, knownOpen: 1 } });
  assert.deepEqual(result.base, { batch: "batch-0", tests: BASELINE_PATH, gate: "gate-base.json" });
  assert.deepEqual(result.knownOpenGateItems, [{ id: "editor/query-core/long", base: "FAIL", now: "FAIL" }]);
  assert.match(result.scope, /goport protected set/);
});

test("a legacy batch ignores the goport rule and keeps the roster check", () => {
  const f = fixture(), g = goportFixture();
  f.state.acceptanceRuleChanges = g.state.acceptanceRuleChanges;
  const result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "PASS");
  assert.equal(result.counts.originalRetained, 6055);
  f.candidate.versusFullBaseline.exactLedger[0].current.status = "FAIL";
  f.candidate.originalAccepted6055.exactLedger[0].current.status = "FAIL";
  refresh(f.candidate);
  stopped(f, /original accepted PASS names/);
});

test("a planted lost goport name stops even when the saved compare shows none", () => {
  const f = goportFixture();
  f.results.suites["ts_goport lib"]["api::t1"] = "failed";
  const result = stopped(f, /1 base ok goport test names are lost/);
  assert.deepEqual(result.losses.goportTests, [{ suite: "ts_goport lib", name: "api::t1", status: "failed" }]);
  assert.equal(result.counts.goportTests.lost, 1);
});

test("an absent goport name stops", () => {
  const f = goportFixture();
  delete f.results.suites["go_baselines default"]["b::one"];
  const result = stopped(f, /are absent/);
  assert.deepEqual(result.losses.goportTests, [{ suite: "go_baselines default", name: "b::one", status: "absent" }]);
});

test("an unrun suite, an unrun name or an incomplete suite stops; ignored is lost", () => {
  let f = goportFixture();
  delete f.results.suites["ts_scanner lib"];
  assert.deepEqual(stopped(f, /are unrun/).losses.goportTests, [{ suite: "ts_scanner lib", name: "scan::a", status: "unrun" }]);
  f = goportFixture();
  f.results.suites["ts_goport lib"]["api::t2"] = "unrun";
  assert.deepEqual(stopped(f, /are unrun/).losses.goportTests, [{ suite: "ts_goport lib", name: "api::t2", status: "unrun" }]);
  f = goportFixture();
  delete f.results.suites["ts_scanner lib"]["scan::a"];
  f.results.incomplete = ["ts_scanner lib"];
  assert.deepEqual(stopped(f, /are unrun/).losses.goportTests, [{ suite: "ts_scanner lib", name: "scan::a", status: "unrun" }]);
  f = goportFixture();
  f.results.suites["ts_goport lib"]["api::t2"] = "ignored";
  assert.deepEqual(stopped(f, /are lost/).losses.goportTests, [{ suite: "ts_goport lib", name: "api::t2", status: "ignored" }]);
});

test("a saved compare that reports a loss stops", () => {
  for (const [field, value] of [["lost", 1], ["absent", ["b::one"]], ["unrun", 2]]) {
    const f = goportFixture();
    f.state.batch.goportTests.compare[field] = value;
    stopped(f, new RegExp(`goportTests.compare reports ${field}`));
  }
  const f = goportFixture(); delete f.state.batch.goportTests.compare.unrun;
  stopped(f, /compare.unrun needs a count/);
});

// Binds the current history row and both verdicts to the batch goport test and gate hashes again.
function rebind(f) {
  const { batch } = f.state;
  for (const item of [batch.recoveryHistory.at(-1), batch.auditor, batch.reviewer]) {
    Object.assign(item, { goportTestsSha256: batch.goportTests.sha256, gateSha256: batch.gate.sha256 });
  }
}

test("a wrong sha256 or a base that is not the pinned baseline stops", () => {
  for (const [change, pattern] of [
    [f => { f.state.batch.goportTests.sha256 = "e".repeat(64); }, /Current history row does not match/],
    [f => { f.state.batch.goportTests.sha256 = "e".repeat(64); rebind(f); }, /hash mismatch: tests-new.json/],
    [f => { f.state.batch.goportTests.baseSha256 = "e".repeat(64); }, /base must be the protected baseline/],
    [f => { f.state.batch.goportTests.base = "tests-new.json"; f.state.batch.goportTests.baseSha256 = "2".repeat(64); }, /base must be the protected baseline/],
    [f => { f.state.acceptanceRuleChanges[0].baseline.sha256 = "e".repeat(64); }, /protectedBase differs/],
    [f => { f.state.acceptanceRuleChanges[0].baseline.sha256 = f.state.batch.goportTests.baseSha256 = f.state.batch.protectedBase.tests.sha256 = "e".repeat(64); },
      /hash mismatch: docs\/goport-protected/],
    [f => { f.state.batch.gateCompare.sha256 = "e".repeat(64); }, /must be batch.gate/],
    [f => { f.state.batch.gate.sha256 = f.state.batch.gateCompare.sha256 = "e".repeat(64); rebind(f); }, /hash mismatch: gate-new.json/],
    [f => { f.state.batch.previousBatch.archive.sha256 = "e".repeat(64); }, /hash mismatch: docs\/typechecker-batches/],
    [f => { f.state.batch.ordinaryQuery.runs[0].sha256 = "e".repeat(64); }, /hash mismatch: measure/],
  ]) { const f = goportFixture(); change(f); stopped(f, pattern); }
});

test("a gate regression stops", () => {
  const item = (f, id) => f.gateNew.results.find(row => row.id === id);
  for (const [change, regression] of [
    [f => { item(f, "measure/query").status = "FAIL"; }, { id: "measure/query", base: "MATCH", now: "FAIL" }],
    [f => { item(f, "corpus-diag/00001").status = "ALLOWED"; }, { id: "corpus-diag/00001", base: "MATCH", now: "ALLOWED" }],
    [f => { item(f, "typesyms/effect").status = "FAIL"; }, { id: "typesyms/effect", base: "ALLOWED", now: "FAIL" }],
    [f => { f.gateNew.results = f.gateNew.results.filter(row => row.id !== "measure/query"); }, { id: "measure/query", base: "MATCH", now: "REMOVED" }],
    [f => { item(f, "sweep/new").status = "FAIL"; }, { id: "sweep/new", base: "NEW", now: "FAIL" }],
  ]) {
    const f = goportFixture(); change(f);
    assert.deepEqual(stopped(f, /1 gate items regressed/).losses.gate, [regression]);
  }
  const f = goportFixture(); f.state.batch.gateCompare.regressions = [{ id: "editor/query-core/long" }];
  stopped(f, /gateCompare reports gate regressions/);
});

test("the editor long-growth FAIL passes only while its open defect is recorded", () => {
  for (const defects of [[], [{ id: "editor-long-growth", status: "closed" }], undefined]) {
    const f = goportFixture(); f.state.batch.openDefects = defects;
    assert.deepEqual(stopped(f, /gate items regressed/).losses.gate, [{ id: "editor/query-core/long", base: "FAIL", now: "FAIL" }]);
  }
});

test("the base is the previous accepted batch: its goport results when it had them", () => {
  let f = goportFixture();
  f.files["docs/typechecker-batches/batch-0.json"].value.compilerAccepted = false;
  stopped(f, /accepted batch/);
  f = goportFixture();
  const archive = f.files["docs/typechecker-batches/batch-0.json"].value;
  archive.protectedSet = "goport";
  archive.goportTests = { results: "tests-prev.json", sha256: "a".repeat(64) };
  f.put("tests-prev.json", "a", structuredClone(f.files[BASELINE_PATH].value));
  stopped(f, /protectedBase differs from the base that accepted batch batch-0 gives/);
  f.state.batch.protectedBase.tests = { path: "tests-prev.json", sha256: "a".repeat(64) };
  stopped(f, /base must be the results of accepted batch batch-0/);
  Object.assign(f.state.batch.goportTests, { base: "tests-prev.json", baseSha256: "a".repeat(64) });
  assert.equal(checkBatch(f.state, f.read).verdict, "PASS");
  delete f.state.batch.protectedBase;
  assert.equal(checkBatch(f.state, f.read).verdict, "PASS");
  f.state.batch.gateCompare.base = "gate-new.json";
  stopped(f, /gateCompare base must be the gate manifest of accepted batch batch-0/);
});

test("a checked name map covers renamed and removed names, never two names in one", () => {
  const f = goportFixture();
  const suite = f.results.suites["go_baselines default"];
  suite["b::uno"] = suite["b::one"]; delete suite["b::one"];
  stopped(f, /are absent/);
  f.put("map.tsv", "c", "oldSuite\toldName\tnewSuite\tnewName\ngo_baselines default\tb::one\tgo_baselines default\tb::uno\n");
  f.state.batch.goportTests.nameMap = { path: "map.tsv", sha256: "c".repeat(64) };
  const result = checkBatch(f.state, f.read);
  assert.equal(result.verdict, "PASS", result.reasons.join(" "));
  assert.equal(result.counts.goportTests.newNames, 1);
  f.put("map.tsv", "c", "# pin bump\ngo_baselines default\tb::one\t-\t-\tremoved at N: evidence.txt\n");
  assert.equal(checkBatch(f.state, f.read).counts.goportTests.removedByMap, 1);
  f.put("map.tsv", "c", "go_baselines default\tb::one\tts_scanner lib\tscan::a\n");
  stopped(f, /Two base names map to ts_scanner lib scan::a/);
  f.put("map.tsv", "c", "go_baselines default\tb::one\n");
  stopped(f, /Name map line 1 needs/);
  f.state.batch.goportTests.nameMap.sha256 = "e".repeat(64);
  stopped(f, /hash mismatch: map.tsv/);
});

test("goport results and gate must come from the batch commit and Go pin", () => {
  for (const [change, pattern] of [
    [f => { f.results.source.commit = "fedcba987"; }, /goportTests results come from another commit/],
    [f => { f.results.pin = "dc37b5249ab6"; }, /goportTests results are not at the batch Go pin/],
    [f => { delete f.results.pin; }, /goportTests results are not at the batch Go pin/],
    [f => { f.gateNew.commit = "fedcba9876543210"; }, /Gate manifest comes from another commit/],
    [f => { f.gateNew.upstreamPin = "dc37b5249ab6"; }, /Gate manifest is not at the batch Go pin/],
    [f => { delete f.state.batch.commit; }, /needs its commit/],
    [f => { f.results.suites["ts_goport lib"]["api::t1"] = "FAILED"; }, /has status "FAILED"/],
  ]) { const f = goportFixture(); change(f); stopped(f, pattern); }
});

test("goport batch needs bound runs, the LSP oracle, quality and bound verdicts", () => {
  for (const [change, pattern] of [
    [f => { delete f.state.batch.ordinaryQuery; }, /ordinaryQuery: bound run/],
    [f => { f.state.batch.latestHono.matchesOracle = false; }, /latestHono: bound run/],
    [f => { f.state.batch.latestHono.sourceFingerprint = RESULT; }, /latestHono: bound run/],
    [f => { f.files["measure/r40/manifest.json"].value.sourceFingerprint = RESULT; }, /names another source/],
    [f => { f.state.batch.languageServerOracle.result = "257,129 requests: 3 diff, 0 crash"; }, /0 diff and 0 crash/],
    [f => { f.state.batch.languageServerOracle.result = "257,129 requests: 0 diff, 10 crash"; }, /0 diff and 0 crash/],
    [f => { f.state.batch.languageServerOracle.summary = "lsp/missing.md"; }, /Missing evidence: lsp\/missing.md/],
    [f => { f.state.batch.qualityEvidence.sourceFingerprint = RESULT; }, /Quality needs/],
    [f => { f.files["quality.json"].value.clippyExit = 1; }, /Quality record/],
    [f => { f.state.batch.reviewer.verdict = "STOP"; }, /Missing independent PASS verdict/],
    [f => { f.state.batch.reviewer.sourceFingerprint = RESULT; }, /Verdict is not bound/],
    [f => { f.state.batch.auditor.batchId = "batch-0"; }, /Verdict is not bound/],
    [f => { f.state.batch.reviewer.agent = "writer"; }, /implementer/],
    [f => { f.state.batch.recoveryHistory.at(-1).sourceFingerprint = RESULT; }, /Current history row does not match/],
    [f => { f.state.batch.recoveryHistory.at(-1).goportTestsSha256 = RESULT; }, /Current history row does not match .* goport test and gate hashes/],
    [f => { delete f.state.batch.recoveryHistory.at(-1).gateSha256; }, /Current history row does not match/],
    [f => { f.state.batch.auditor.gateSha256 = RESULT; }, /Verdict is not bound to this batch, source, and goport test and gate hashes/],
    [f => { delete f.state.batch.reviewer.goportTestsSha256; }, /Verdict is not bound/],
    [f => { f.state.batch.gateCompare.baseSha256 = RESULT; }, /gateCompare base must be/],
    [f => { f.state.batch.rosterCarryForward = { fromRevision: 6 }; }, /no roster carry-forward/],
  ]) { const f = goportFixture(); change(f); stopped(f, pattern); }
});

test("goport mode needs Theo's standing rule that cites a saved approval note", () => {
  for (const [change, pattern] of [
    [f => { f.state.acceptanceRuleChanges = []; }, /standing goport-protected-set rule/],
    [f => { f.state.acceptanceRuleChanges[0].batchId = "batch-1"; }, /standing goport-protected-set rule/],
    [f => { f.state.acceptanceRuleChanges[0].standing = false; }, /standing goport-protected-set rule/],
    [f => { delete f.state.acceptanceRuleChanges[0].approvedBy; }, /standing goport-protected-set rule/],
    [f => { delete f.state.acceptanceRuleChanges[0].baseline; }, /baseline path and SHA-256/],
    [f => { f.state.acceptanceRuleChanges[0].protectedSet = "roster"; }, /protectedSet "goport"/],
    [f => { delete f.state[NOTE]; }, /saved approval note/],
    [f => { f.state.batch.protectedSet = "goport2"; }, /Unknown protectedSet/],
  ]) { const f = goportFixture(); change(f); stopped(f, pattern); }
});

test("goport unbound history rows come from the standing rule list, never the current row", () => {
  const f = goportFixture();
  Object.assign(f.state.batch.recoveryHistory[5], { sourceFingerprint: null, fullResultSha256: null });
  stopped(f, /Invalid or reset recovery history. A goport batch lists unbound rows in goport-protected-set unboundRevisions/);
  f.state.acceptanceRuleChanges[0].unboundRevisions = [6, 7];
  assert.equal(checkBatch(f.state, f.read).verdict, "PASS");
  f.state.batch.recoveryHistory[6].sourceFingerprint = null;
  stopped(f, /Invalid or reset recovery history/);
});
