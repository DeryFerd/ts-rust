import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";

// This checks saved evidence. It does not run Cargo or authenticate agent identities.
export const CHECKPOINT_SHA256 = "60a372581586cb3c8d0046ba6e4ab0af65b515267485a0a01bdfe90695f7a538";
export const BASELINE_SHA256 = "f562cd3ca338de7203c6ae12693dfc4a726a6478b3da7f1393374c36194bdcba";
const ROOT = fileURLToPath(new URL("../", import.meta.url));
const HASH = /^[a-f0-9]{64}$/;
const STAGES = ["checker", "compiler", "fixture"];
const SCOPE = "Original 6055 and later 6330 PASS names only. Later added passes and corpus parity need independent review.";

function requireValue(condition, message) {
  if (!condition) throw new Error(message);
}

function text(value) {
  return typeof value === "string" && value.trim().length > 0;
}

function key(row) {
  requireValue(text(row?.harness) && text(row?.name), "Missing exact harness or test name.");
  return JSON.stringify([row.harness, row.name]);
}

function rowsByKey(rows, label) {
  requireValue(Array.isArray(rows), `${label}: missing exact ledger.`);
  const result = new Map();
  for (const row of rows) {
    const id = key(row);
    requireValue(!result.has(id), `${label}: duplicate ${row.harness}::${row.name}.`);
    result.set(id, row);
  }
  return result;
}

function counts(rows) {
  return {
    tests: rows.length,
    PASS: rows.filter(row => row.status === "PASS").length,
    FAIL: rows.filter(row => row.status === "FAIL").length,
    harnesses: new Set(rows.map(row => row.harness)).size,
  };
}

function matchCounts(actual, claimed, label) {
  for (const field of ["tests", "PASS", "FAIL", "harnesses"]) {
    requireValue(actual[field] === claimed?.[field], `${label}: ${field} count mismatch.`);
  }
}

export function readPinnedJson(reference) {
  requireValue(text(reference?.path) && HASH.test(reference?.sha256), "Missing evidence path or SHA-256.");
  let bytes;
  try {
    bytes = readFileSync(resolve(ROOT, reference.path));
  } catch {
    throw new Error(`Missing evidence: ${reference.path}. Do not regenerate a baseline.`);
  }
  requireValue(createHash("sha256").update(bytes).digest("hex") === reference.sha256,
    `Evidence hash mismatch: ${reference.path}.`);
  try {
    return JSON.parse(bytes.toString("utf8"));
  } catch {
    throw new Error(`Invalid evidence JSON: ${reference.path}.`);
  }
}

function validateBatch(state) {
  requireValue(state?.schemaVersion === 1, "Unsupported state schema.");
  requireValue(state.phase === "initial-recovery", "STOP: this guard supports initial-recovery only.");
  requireValue(state.status === "ready", "State is not ready. Paused or missing state means STOP.");
  requireValue(state.decision === "REVIEW" || state.decision === "PASS", "Ready state cannot keep a STOP or missing decision.");
  requireValue(text(state.goalAuthorization) || (state.goalAuthorization !== null && typeof state.goalAuthorization === "object"
    && !Array.isArray(state.goalAuthorization) && Object.keys(state.goalAuthorization).length > 0), "Missing goal authorization.");
  requireValue(HASH.test(state.preservedCandidateSourceFingerprint), "Missing preserved candidate fingerprint.");
  const batch = state.batch;
  requireValue(batch && text(batch.id) && text(batch.implementer) && text(batch.hypothesis), "Missing authorized batch, implementer, or hypothesis.");
  requireValue(HASH.test(batch.sourceFingerprint), "Missing batch source fingerprint.");
  requireValue(text(batch.fullResult?.path) && HASH.test(batch.fullResult?.sha256), "Missing completed full result.");
  const history = batch.recoveryHistory;
  requireValue(Array.isArray(history) && history.length >= 1 && history.length <= 4, "Recovery history must contain 1 to 4 measured revisions.");
  requireValue(batch.recoveryRevision === history.length, "Recovery revision must equal the retained history length.");
  requireValue(batch.maxRecoveryRevisions === undefined || batch.maxRecoveryRevisions === 4, "The recovery limit is fixed at 4.");
  const hypotheses = new Map();
  for (const [index, row] of history.entries()) {
    requireValue(row?.revision === index + 1 && text(row.hypothesis) && HASH.test(row.sourceFingerprint), "Invalid or reset recovery history.");
    requireValue(row.fullResultSha256 === null || HASH.test(row.fullResultSha256), "History needs a result hash or explicit null.");
    hypotheses.set(row.hypothesis, (hypotheses.get(row.hypothesis) ?? 0) + 1);
  }
  requireValue(hypotheses.size <= 2 && [...hypotheses.values()].every(value => value <= 2), "Limit: two hypotheses, two revisions per hypothesis.");
  const last = history.at(-1);
  requireValue(last.hypothesis === batch.hypothesis && last.sourceFingerprint === batch.sourceFingerprint && last.fullResultSha256 === batch.fullResult.sha256,
    "Current history row does not match the batch source, hypothesis, and full result.");
  const verdicts = [batch.auditor, batch.reviewer];
  requireValue(batch.auditor?.role === "audit_accepted_roster", "Missing audit_accepted_roster verdict.");
  for (const verdict of verdicts) {
    requireValue(text(verdict?.role) && text(verdict?.agent) && verdict.verdict === "PASS", "Missing independent PASS verdict. STOP is the default.");
    requireValue(verdict.batchId === batch.id && verdict.sourceFingerprint === batch.sourceFingerprint && verdict.fullResultSha256 === batch.fullResult.sha256,
      "Verdict is not bound to this batch, source, and full result.");
    requireValue(verdict.agent !== batch.implementer && verdict.role !== batch.implementer, "The implementer cannot supply an independent verdict.");
  }
  requireValue(batch.auditor.agent !== batch.reviewer.agent && batch.auditor.role !== batch.reviewer.role, "Auditor and reviewer must have distinct roles and agent identities.");
  return batch;
}

function laterPasses(report) {
  requireValue(report?.closure?.normalClosure === true && report.closure.sourceUnchanged === true, "Later baseline checker is not closed.");
  const rows = report.versusPreviousFullBaseline?.exactLedger?.map(row => ({ ...row, status: row.current?.status }));
  requireValue(Array.isArray(rows), "Later baseline checker ledger is missing.");
  for (const stage of ["compiler", "fixture"]) {
    const result = report.closedStages?.[stage];
    requireValue(result?.closure?.normalClosure === true && result.closure.sourceUnchanged === true && result.closure.sourceFingerprint === report.closure.sourceFingerprint,
      `Later baseline ${stage} is missing or has a different source.`);
    requireValue(Array.isArray(result.outcomes), `Later baseline ${stage} ledger is missing.`);
    rows.push(...result.outcomes);
  }
  rowsByKey(rows, "Later baseline");
  requireValue(rows.every(row => row.status === "PASS" || row.status === "FAIL"), "Later baseline has incomplete outcomes.");
  matchCounts(counts(rows), report.summary, "Later baseline");
  const passes = rows.filter(row => row.status === "PASS");
  requireValue(passes.length === 6330, "Later baseline must contain exactly 6330 PASS names.");
  return passes;
}

function currentResults(report, sourceFingerprint) {
  requireValue(report?.schemaVersion === 1 && report.status === "ALL_STAGES_CLOSED", "Missing full ALL_STAGES_CLOSED result.");
  requireValue(report.sourceFingerprint === sourceFingerprint && report.closure?.sourceFingerprint === sourceFingerprint,
    "Full result source mismatch.");
  requireValue(report.closure.normalClosures === true && report.closure.sourceUnchangedThroughAllStages === true,
    "Full result lacks unchanged-source normal closures.");
  requireValue(report.expectationChangesApplied === false && report.waiversApplied === false,
    "Expectation changes or waivers need human review and cannot pass this guard.");
  requireValue(Array.isArray(report.versusFullBaseline?.exactLedger) && Array.isArray(report.addedNames), "Full exact result ledger is missing.");
  const rows = report.versusFullBaseline.exactLedger.map(row => ({ ...row, ...row.current }));
  for (const row of report.addedNames) {
    const stage = report.stages?.find(item => item.path === row.path);
    rows.push({ ...row, logStage: stage?.stage });
  }
  const map = rowsByKey(rows, "Current result");
  requireValue(rows.every(row => row.status === "PASS" || row.status === "FAIL"), "Current ledger contains missing or unrun outcomes.");
  requireValue(Array.isArray(report.stages) && report.stages.length === 3 && new Set(report.stages.map(stage => stage.stage)).size === 3,
    "Need exactly one checker, compiler, and fixture stage.");
  for (const name of STAGES) {
    const stage = report.stages.find(item => item.stage === name);
    requireValue(stage?.normalClosure === true && text(stage.closureReceipt) && stage.sourceFingerprint === sourceFingerprint,
      `${name}: missing closure or source mismatch.`);
    const measured = counts(rows.filter(row => row.logStage === name));
    matchCounts(measured, stage.counts, name);
    requireValue(stage.exitCode === (measured.FAIL > 0 ? 101 : 0), `${name}: unexpected exit code.`);
  }
  requireValue(rows.every(row => STAGES.includes(row.logStage)), "Outcome has no closed stage.");
  matchCounts(counts(rows), report.summary, "Full summary");
  matchCounts(counts(rows), report.current, "Full current counts");
  requireValue(report.current.ABSENT === 0 && report.current.UNRUN === 0, "Full result reports absent or unrun selected outcomes.");
  return map;
}

function losses(baseline, current) {
  return baseline.flatMap(row => {
    const status = current.get(key(row))?.status ?? "ABSENT";
    return status === "PASS" ? [] : [{ harness: row.harness, name: row.name, status }];
  });
}

// Tests may supply parsed synthetic evidence. The CLI always uses readPinnedJson.
export function checkBatch(state, readEvidence = readPinnedJson) {
  try {
    const batch = validateBatch(state);
    requireValue(state.acceptedBaseline?.sha256 === CHECKPOINT_SHA256, "Accepted checkpoint identity changed.");
    requireValue(state.originalAccepted?.sha256 === BASELINE_SHA256 && state.originalAccepted.expectedNames === 6055,
      "Original accepted baseline identity or count changed.");
    requireValue(state.laterPassBaseline?.sha256 === BASELINE_SHA256 && state.laterPassBaseline.expectedPasses === 6330,
      "Later PASS baseline identity or count changed.");
    readEvidence(state.acceptedBaseline);
    const original = readEvidence(state.originalAccepted);
    const accepted = original.originalAccepted6055?.exactLedger;
    const acceptedMap = rowsByKey(accepted, "Original accepted baseline");
    requireValue(acceptedMap.size === 6055 && accepted.every(row => row.accepted?.status === "PASS"), "Original baseline must contain 6055 exact PASS names.");
    const later = laterPasses(readEvidence(state.laterPassBaseline));
    const candidate = readEvidence(batch.fullResult);
    const current = currentResults(candidate, batch.sourceFingerprint);
    const candidateAccepted = rowsByKey(candidate.originalAccepted6055?.exactLedger, "Candidate accepted ledger");
    requireValue(candidateAccepted.size === acceptedMap.size, "Candidate accepted ledger changed its name count.");
    for (const [id] of acceptedMap) {
      const row = candidateAccepted.get(id);
      requireValue(row && row.accepted?.status === "PASS", "Candidate accepted ledger renamed or omitted an original name.");
      requireValue(row.current?.status === (current.get(id)?.status ?? "ABSENT"), "Candidate accepted ledger disagrees with exact current outcomes.");
    }
    const originalLosses = losses(accepted, current), laterLosses = losses(later, current);
    const reasons = [];
    if (originalLosses.length) reasons.push(`${originalLosses.length} original accepted PASS names are FAIL or ABSENT.`);
    if (laterLosses.length) reasons.push(`${laterLosses.length} later baseline PASS names are FAIL or ABSENT.`);
    return { verdict: reasons.length ? "STOP" : "PASS", scope: SCOPE, reasons,
      counts: { originalAccepted: 6055, originalRetained: 6055 - originalLosses.length, laterPasses: 6330, laterRetained: 6330 - laterLosses.length },
      losses: { originalAccepted: originalLosses, laterPasses: laterLosses } };
  } catch (error) {
    return { verdict: "STOP", scope: SCOPE, reasons: [error.message], counts: null };
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  if (process.argv.length === 3 && process.argv[2] === "--help") {
    console.log(`Usage: node scripts/check-typechecker-batch.mjs <state.json>

Read-only pre-acceptance check. Exit 0 means the protected-name and review
prerequisites pass. Exit 1 means STOP. This is not a Cargo wrapper.

State requires schemaVersion 1, phase initial-recovery, status ready,
decision REVIEW or PASS, goalAuthorization, and a preserved candidate hash.
acceptedBaseline, originalAccepted, and laterPassBaseline need pinned path/SHA-256
references. Original expectedNames is 6055. Later expectedPasses is 6330.

batch needs id, implementer, hypothesis, sourceFingerprint, fullResult path/hash,
recoveryRevision, recoveryHistory, auditor, and reviewer. History retains all
measured revisions, including failures. Limits are 4 revisions, 2 hypotheses,
and 2 revisions per hypothesis. Each history row needs revision, hypothesis,
sourceFingerprint, and fullResultSha256. A past result hash may be null.
The final row must match this completed full result.

Both verdicts need distinct role/agent identities, batchId, PASS,
sourceFingerprint, and fullResultSha256. Neither may be the implementer.
The auditor role is audit_accepted_roster. Missing evidence, STOP, source
mismatch, renamed/missing protected names, or expectation exceptions stop.

${SCOPE}
This check cannot prevent arbitrary direct commands or edits to state history.`);
  } else {
  let result;
  try {
    requireValue(process.argv.length === 3, "Usage: node scripts/check-typechecker-batch.mjs <state.json>");
    const state = JSON.parse(readFileSync(resolve(process.argv[2]), "utf8"));
    result = checkBatch(state);
  } catch {
    result = { verdict: "STOP", scope: SCOPE, reasons: ["Missing or invalid state. Usage: node scripts/check-typechecker-batch.mjs <state.json>."] };
  }
  if (result.losses) {
    result.losses = Object.fromEntries(Object.entries(result.losses).map(([name, rows]) => [name, { total: rows.length, first20: rows.slice(0, 20) }]));
  }
  console.log(JSON.stringify(result, null, 2));
  process.exitCode = result.verdict === "PASS" ? 0 : 1;
  }
}
