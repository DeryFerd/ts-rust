import { createHash } from "node:crypto";
import { readFileSync, statSync } from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { loadState, verifyAppendOnly } from "./state.mjs";

// This checks saved evidence. It does not run Cargo or authenticate agent identities.
export const CHECKPOINT_SHA256 = "60a372581586cb3c8d0046ba6e4ab0af65b515267485a0a01bdfe90695f7a538";
export const BASELINE_SHA256 = "f562cd3ca338de7203c6ae12693dfc4a726a6478b3da7f1393374c36194bdcba";
// Theo's opt-in crate rule (2026-09-25) pins the inherited losses to the R96 full result.
export const INHERITED_PIN = { sha256: "e7838ed863c42bc2271981c680d2fc46bb6a98f3171c8554b2d040ca9277d6b7", originalAccepted: 290, laterPasses: 15 };
export const CARRY_FORWARD_RULE = "goport-only-roster-carry-forward";
// Theo's standing rule (2026-09-28) that makes goport's own tests the protected set for a
// batch with protectedSet "goport". See checkGoport.
export const GOPORT_RULE = "goport-protected-set";
const ROOT = fileURLToPath(new URL("../", import.meta.url));
const HASH = /^[a-f0-9]{64}$/;
const STAGES = ["checker", "compiler", "fixture"];
const SCOPE = "Original 6055 and later 6330 PASS names only. Later added passes and corpus parity need independent review.";
const GOPORT_SCOPE = "goport protected set: every base ok test name and every base gate item, plus bound runs, LSP oracle and quality. "
  + "Name maps, gate noise and allow-list conditions need independent review.";
const TEST_STATUSES = new Set(["ok", "failed", "ignored", "unrun"]);
const GATE_STATUSES = new Set(["MATCH", "ALLOWED", "FAIL"]);
// Gate items of the open editor-long-growth defect. They may stay FAIL while the batch keeps
// that open defect record. gate-compare.py applies the noise rule to them.
const LONG_GROWTH = /^editor\/[^/]+\/long$/;

function requireValue(condition, message) {
  if (!condition) throw new Error(message);
}

function text(value) {
  return typeof value === "string" && value.trim().length > 0;
}

function isoDate(value) {
  return text(value) && /^\d{4}-\d{2}-\d{2}T/.test(value) && Number.isFinite(Date.parse(value));
}

// Two abbreviated or full git hashes (commits, Go pins) name the same object.
function sameHash(a, b) {
  const hex = /^[0-9a-f]{7,64}$/;
  if (typeof a !== "string" || typeof b !== "string") return false;
  const [x, y] = [a.toLowerCase(), b.toLowerCase()];
  return hex.test(x) && hex.test(y) && (x.startsWith(y) || y.startsWith(x));
}

function samePath(a, b) {
  return text(a) && text(b) && resolve(ROOT, a) === resolve(ROOT, b);
}

// A count, or a list whose length is the count.
function size(value, label) {
  const result = Array.isArray(value) ? value.length : value;
  requireValue(Number.isInteger(result) && result >= 0, `${label} needs a count or a list.`);
  return result;
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

// Reads an evidence file {path, sha256} relative to the repository root. The hash must match
// unless the caller passes pinned false (for records the state saves without a hash, such as
// the quality record). json false returns the text.
export function readEvidenceFile(reference, { pinned = true, json = true } = {}) {
  requireValue(text(reference?.path) && (!pinned || HASH.test(reference?.sha256)), "Missing evidence path or SHA-256.");
  let bytes;
  try {
    bytes = readFileSync(resolve(ROOT, reference.path));
  } catch {
    throw new Error(`Missing evidence: ${reference.path}. Do not regenerate a baseline.`);
  }
  requireValue(!pinned || createHash("sha256").update(bytes).digest("hex") === reference.sha256,
    `Evidence hash mismatch: ${reference.path}.`);
  if (!json) return bytes.toString("utf8");
  try {
    return JSON.parse(bytes.toString("utf8"));
  } catch {
    throw new Error(`Invalid evidence JSON: ${reference.path}.`);
  }
}

// Theo-approved rule changes live in state.acceptanceRuleChanges. Each entry is bound
// to one batch id. Rules that do not name this batch have no effect. Only the standing
// rules (standingRule) use batchId "*", so "*" never matches here.
function approvedRule(state, id) {
  const rules = Array.isArray(state.acceptanceRuleChanges) ? state.acceptanceRuleChanges : [];
  const rule = rules.find(item => item?.id === id && item.batchId === state.batch?.id && item.batchId !== "*");
  if (!rule) return null;
  requireValue(rule.approvedBy === "Theo" && text(rule.instruction) && text(rule.date) && Number.isFinite(Date.parse(rule.date)),
    `Rule ${id} needs Theo's saved approval, instruction and date.`);
  return rule;
}

// A standing rule applies to every batch that asks for it: batchId "*", standing true,
// approvedBy Theo, instruction, scope and an ISO date. Used by the roster carry-forward
// and the goport protected set.
function standingRule(state, id, label) {
  const rules = Array.isArray(state.acceptanceRuleChanges) ? state.acceptanceRuleChanges : [];
  const rule = rules.find(item => item?.id === id && item.batchId === "*");
  requireValue(rule?.standing === true && rule.approvedBy === "Theo" && text(rule.instruction) && text(rule.scope) && isoDate(rule.date),
    `${label} needs Theo's standing ${id} rule with batchId "*", instruction, scope and ISO date.`);
  return rule;
}

// batch.protectedSet selects the protected set. Absent means the legacy cargo roster.
// "goport" needs the standing goport-protected-set rule, which pins the first goport
// baseline, cites Theo's saved approval note and may list unbound history revisions.
function goportRule(state) {
  const set = state?.batch?.protectedSet;
  if (set === undefined) return null;
  requireValue(set === "goport", `Unknown protectedSet ${JSON.stringify(set)}. Use "goport" or leave it out.`);
  const rule = standingRule(state, GOPORT_RULE, "The goport protected set");
  requireValue(rule.protectedSet === "goport" && text(rule.baseline?.path) && HASH.test(rule.baseline?.sha256),
    `${GOPORT_RULE} needs protectedSet "goport" and a baseline path and SHA-256.`);
  requireValue(text(rule.approvalNote) && state[rule.approvalNote] != null, `${GOPORT_RULE} must cite a saved approval note.`);
  requireValue(rule.unboundRevisions === undefined || (Array.isArray(rule.unboundRevisions) && rule.unboundRevisions.every(Number.isInteger)),
    `${GOPORT_RULE} unboundRevisions must be a list of revision numbers.`);
  return rule;
}

// goport is the goport-protected-set rule for a goport batch, else null. A goport batch has
// no full result: its current history row and verdicts carry goportTestsSha256 and gateSha256.
function validateBatch(state, goport = null) {
  requireValue(state?.schemaVersion === 1, "Unsupported state schema.");
  const continuation = state.phase === "recovery-continuation";
  requireValue(state.phase === "initial-recovery" || continuation, "Unsupported recovery phase.");
  requireValue(state.status === "ready", "State is not ready. Paused or missing state means STOP.");
  requireValue(state.decision === "REVIEW" || state.decision === "PASS", "Ready state cannot keep a STOP or missing decision.");
  requireValue(text(state.goalAuthorization) || (state.goalAuthorization !== null && typeof state.goalAuthorization === "object"
    && !Array.isArray(state.goalAuthorization) && Object.keys(state.goalAuthorization).length > 0), "Missing goal authorization.");
  if (continuation) {
    const authorization = state.continuationAuthorization;
    requireValue(authorization?.authorized === true && text(authorization.instruction) && text(authorization.scope) && isoDate(authorization.date),
      "Continuation requires explicit saved authorization, instruction, scope, and a valid date.");
  }
  requireValue(HASH.test(state.preservedCandidateSourceFingerprint), "Missing preserved candidate fingerprint.");
  const batch = state.batch;
  requireValue(batch && text(batch.id) && text(batch.implementer) && text(batch.hypothesis), "Missing authorized batch, implementer, or hypothesis.");
  requireValue(HASH.test(batch.sourceFingerprint), "Missing batch source fingerprint.");
  if (!goport) requireValue(text(batch.fullResult?.path) && HASH.test(batch.fullResult?.sha256), "Missing completed full result.");
  const history = batch.recoveryHistory;
  requireValue(Array.isArray(history) && (continuation ? history.length >= 5 : history.length >= 1 && history.length <= 4),
    continuation ? "Continuation history must retain all four initial revisions and each later measured revision."
      : "Recovery history must contain 1 to 4 measured revisions.");
  requireValue(batch.recoveryRevision === history.length, "Recovery revision must equal the retained history length.");
  if (!continuation) {
    requireValue(batch.maxRecoveryRevisions === undefined || batch.maxRecoveryRevisions === 4, "The recovery limit is fixed at 4.");
  }
  const unbound = approvedRule(state, "unbound-history-rows");
  const unboundRevisions = new Set([...(Array.isArray(unbound?.revisions) ? unbound.revisions : []), ...(goport?.unboundRevisions ?? [])]);
  const hypotheses = new Map();
  for (const [index, row] of history.entries()) {
    // An approved unbound row keeps a null source and a null result. It can never be the current row.
    const sourceOk = HASH.test(row?.sourceFingerprint)
      || (row?.sourceFingerprint === null && row.fullResultSha256 === null && unboundRevisions.has(row.revision) && index < history.length - 1);
    requireValue(row?.revision === index + 1 && text(row.hypothesis) && sourceOk,
      `Invalid or reset recovery history.${goport ? ` A goport batch lists unbound rows in ${GOPORT_RULE} unboundRevisions.` : ""}`);
    requireValue(row.fullResultSha256 === null || HASH.test(row.fullResultSha256), "History needs a result hash or explicit null.");
    // Later authorization does not change the initial four-revision trial.
    if (index < 4) hypotheses.set(row.hypothesis, (hypotheses.get(row.hypothesis) ?? 0) + 1);
  }
  requireValue(hypotheses.size <= 2 && [...hypotheses.values()].every(value => value <= 2), "Limit: two hypotheses, two revisions per hypothesis.");
  const last = history.at(-1);
  // A goport row and verdict bind to the goport test results and the gate manifest instead.
  const evidence = item => goport ? item.goportTestsSha256 === batch.goportTests?.sha256 && item.gateSha256 === batch.gate?.sha256
    : item.fullResultSha256 === batch.fullResult.sha256;
  requireValue(last.hypothesis === batch.hypothesis && last.sourceFingerprint === batch.sourceFingerprint && evidence(last),
    `Current history row does not match the batch source, hypothesis, and ${goport ? "goport test and gate hashes" : "full result"}.`);
  const verdicts = [batch.auditor, batch.reviewer];
  requireValue(batch.auditor?.role === "audit_accepted_roster", "Missing audit_accepted_roster verdict.");
  for (const verdict of verdicts) {
    requireValue(text(verdict?.role) && text(verdict?.agent) && verdict.verdict === "PASS", "Missing independent PASS verdict. STOP is the default.");
    requireValue(verdict.batchId === batch.id && verdict.sourceFingerprint === batch.sourceFingerprint && evidence(verdict),
      `Verdict is not bound to this batch, source, and ${goport ? "goport test and gate hashes" : "full result"}.`);
    requireValue(verdict.agent !== batch.implementer && verdict.role !== batch.implementer, "The implementer cannot supply an independent verdict.");
  }
  requireValue(batch.auditor.agent !== batch.reviewer.agent && batch.auditor.role !== batch.reviewer.role, "Auditor and reviewer must have distinct roles and agent identities.");
  return batch;
}

// Theo's standing goport-only roster carry-forward rule (2026-09-28). When no file outside
// crates/ts_goport changed (equal scripts/goport/roster_fp.py hashes), batch.fullResult may
// be the saved result of an earlier measured revision. Returns null without
// batch.rosterCarryForward, else the carry record, whose fromSourceFingerprint the full
// result must name. Verdicts and the current history row stay bound to this batch.
function rosterCarry(state, batch) {
  const carry = batch.rosterCarryForward;
  if (carry == null) return null;
  standingRule(state, CARRY_FORWARD_RULE, "Roster carry-forward");
  requireValue(HASH.test(batch.rosterFingerprint) && HASH.test(carry.rosterFingerprint) && HASH.test(carry.fromSourceFingerprint),
    "Roster carry-forward needs SHA-256 roster and source fingerprints.");
  requireValue(carry.rosterFingerprint === batch.rosterFingerprint, "Roster carry-forward fingerprint differs from the batch roster fingerprint.");
  requireValue(Number.isInteger(carry.fromRevision) && carry.fromRevision < batch.recoveryRevision, "Roster carry-forward must name an earlier revision.");
  const from = batch.recoveryHistory.find(row => row.revision === carry.fromRevision);
  // A carried row never ran the roster, so it cannot be a source for another carry.
  requireValue(typeof from?.status === "string" && from.status.startsWith("full_measured") && from.rosterCarryForward == null,
    `Roster carry-forward source R${carry.fromRevision} is not a full_measured revision.`);
  requireValue(from.sourceFingerprint === carry.fromSourceFingerprint && from.rosterFingerprint === batch.rosterFingerprint
    && from.fullResultSha256 === batch.fullResult.sha256,
  `R${carry.fromRevision} source, roster fingerprint or full result differs from the carry-forward record.`);
  return carry;
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

// Exact outcomes of a saved full result, for the inherited-loss comparison.
function ledgerStatuses(report) {
  requireValue(Array.isArray(report?.versusFullBaseline?.exactLedger) && Array.isArray(report.addedNames), "Inherited result ledger is missing.");
  const rows = [...report.versusFullBaseline.exactLedger.map(row => ({ harness: row.harness, name: row.name, status: row.current?.status })),
    ...report.addedNames.map(row => ({ harness: row.harness, name: row.name, status: row.status }))];
  return rowsByKey(rows, "Inherited result");
}

function losses(baseline, current) {
  return baseline.flatMap(row => {
    const status = current.get(key(row))?.status ?? "ABSENT";
    return status === "PASS" ? [] : [{ harness: row.harness, name: row.name, status }];
  });
}

// Name map TSV (compare-tests.py --name-map): oldSuite, oldName, newSuite, newName per line;
// more columns (the evidence) are ignored. "-" in both new columns marks a base name that the
// change removed. Blank lines, "#" lines and a header row that starts with "oldSuite" are
// skipped. Returns Map(old key -> [suite, name] | null).
function parseNameMap(source) {
  const map = new Map();
  for (const [index, line] of source.split("\n").entries()) {
    const cells = line.replace(/\r$/, "").split("\t").slice(0, 4);
    if (!line.trim() || line.startsWith("#") || (index === 0 && cells[0] === "oldSuite")) continue;
    requireValue(cells.length === 4 && cells.every(text), `Name map line ${index + 1} needs oldSuite, oldName, newSuite and newName.`);
    const id = JSON.stringify(cells.slice(0, 2));
    requireValue(!map.has(id), `Name map line ${index + 1} maps ${cells[0]} ${cells[1]} twice.`);
    map.set(id, cells[2] === "-" && cells[3] === "-" ? null : cells.slice(2));
  }
  return map;
}

// results.json of goport-tests.sh: {source, pin, suites: {suite: {name: status}}, incomplete: [suite]}.
function testSuites(results, label) {
  const suites = results?.suites;
  requireValue(suites && typeof suites === "object" && !Array.isArray(suites), `${label}: missing suites.`);
  for (const [suite, names] of Object.entries(suites)) {
    requireValue(names && typeof names === "object" && !Array.isArray(names), `${label}: suite ${suite} is not a name map.`);
    for (const [name, status] of Object.entries(names)) {
      requireValue(TEST_STATUSES.has(status), `${label}: ${suite} ${name} has status ${JSON.stringify(status)}.`);
    }
  }
  return suites;
}

// Every base "ok" name must be "ok" at its own name or its mapped name. As in
// compare-tests.py: failed or ignored is lost; unrun, or a name missing from a missing or
// incomplete suite, is unrun; a name missing from a complete suite is absent.
function compareTests(baseResults, newResults, map) {
  const before = testSuites(baseResults, "Base goport results"), after = testSuites(newResults, "goportTests results");
  requireValue(newResults.incomplete === undefined || (Array.isArray(newResults.incomplete) && newResults.incomplete.every(text)),
    "goportTests results: incomplete must be a list of suites.");
  const incomplete = new Set(newResults.incomplete ?? []);
  const result = { baseOk: 0, retained: 0, recovered: 0, removedByMap: 0, newNames: 0, lost: [], absent: [], unrun: [] };
  const targets = new Set();
  for (const [suite, names] of Object.entries(before)) {
    for (const [name, status] of Object.entries(names)) {
      const id = JSON.stringify([suite, name]);
      const target = map?.has(id) ? map.get(id) : [suite, name];
      if (status === "ok") result.baseOk++;
      if (target === null) {
        if (status === "ok") result.removedByMap++;
        continue;
      }
      const targetId = JSON.stringify(target);
      requireValue(!targets.has(targetId), `Two base names map to ${target[0]} ${target[1]}.`);
      targets.add(targetId);
      const [toSuite, toName] = target;
      const now = Object.hasOwn(after, toSuite) && Object.hasOwn(after[toSuite], toName) ? after[toSuite][toName]
        : !Object.hasOwn(after, toSuite) || incomplete.has(toSuite) ? "unrun" : "absent";
      if (status !== "ok") {
        if (now === "ok") result.recovered++;
      } else if (now === "ok") {
        result.retained++;
      } else {
        const row = { suite, name, status: now, ...(targetId !== id && { mappedTo: { suite: toSuite, name: toName } }) };
        result[now === "absent" || now === "unrun" ? now : "lost"].push(row);
      }
    }
  }
  for (const [suite, names] of Object.entries(after)) {
    for (const name of Object.keys(names)) if (!targets.has(JSON.stringify([suite, name]))) result.newNames++;
  }
  return result;
}

// Gate manifest items by id. Every base item must be in the new run; a base MATCH must stay
// MATCH; a new FAIL is a regression unless the base item already failed, it is an editor
// long-growth item, and the batch keeps the open editor-long-growth defect record.
function compareGate(baseManifest, newManifest, openDefects) {
  const items = (manifest, label) => {
    requireValue(Array.isArray(manifest?.results), `${label}: missing results.`);
    const byId = new Map();
    for (const item of manifest.results) {
      requireValue(text(item?.id) && GATE_STATUSES.has(item.status), `${label}: item without id or MATCH, ALLOWED or FAIL status.`);
      requireValue(!byId.has(item.id), `${label}: duplicate item ${item.id}.`);
      byId.set(item.id, item.status);
    }
    return byId;
  };
  const before = items(baseManifest, "Base gate manifest"), after = items(newManifest, "Gate manifest");
  const open = Array.isArray(openDefects) && openDefects.some(item => item?.id === "editor-long-growth" && /^open\b/.test(item.status ?? ""));
  const regressions = [], knownOpen = [];
  for (const [id, base] of before) {
    const now = after.get(id) ?? "REMOVED";
    if (now === "REMOVED" || (base === "MATCH" && now !== "MATCH")) regressions.push({ id, base, now });
    else if (now === "FAIL") (base === "FAIL" && LONG_GROWTH.test(id) && open ? knownOpen : regressions).push({ id, base, now });
  }
  for (const [id, now] of after) if (!before.has(id) && now === "FAIL") regressions.push({ id, base: "NEW", now });
  return { baseItems: before.size, items: after.size, regressions, knownOpen };
}

// The Query core and Hono bound runs, LSP oracle and quality record of the batch source.
function checkRunEvidence(batch, readEvidence) {
  for (const label of ["ordinaryQuery", "latestHono"]) {
    const run = batch[label];
    requireValue(run?.complete === true && run.exitCode === 0 && run.matchesOracle === true && run.sourceFingerprint === batch.sourceFingerprint
      && Array.isArray(run.runs) && run.runs.length > 0,
    `${label}: bound run is missing, incomplete, differs from the oracle or names another source.`);
    for (const ref of run.runs) {
      requireValue(readEvidence({ path: ref?.manifest, sha256: ref?.sha256 }).sourceFingerprint === batch.sourceFingerprint,
        `${label}: bound run ${ref.manifest} names another source.`);
    }
  }
  const lsp = batch.languageServerOracle;
  requireValue(text(lsp?.summary) && /\b0 diffs?\b/.test(lsp.result ?? "") && /\b0 crash(es)?\b/.test(lsp.result ?? ""),
    "languageServerOracle needs a summary and a result with 0 diff and 0 crash.");
  readEvidence({ path: lsp.summary }, { pinned: false, json: false });
  requireValue(text(batch.quality?.record) && batch.qualityEvidence?.sourceFingerprint === batch.sourceFingerprint,
    "Quality needs a record and qualityEvidence for the batch source.");
  const quality = readEvidence({ path: batch.quality.record }, { pinned: false });
  requireValue(quality.sourceFingerprint === batch.sourceFingerprint && quality.rustfmtExit === 0 && quality.clippyExit === 0
    && quality.fingerprintUnchanged === true, "Quality record is for another source or has rustfmt or clippy findings.");
}

// Theo's goport protected set (rule goport-protected-set, 2026-09-28). The base is the
// accepted previous batch: its goportTests results when it was a goport batch, else the
// rule's pinned baseline (docs/goport-protected/tests-r131.json); the gate base is always its
// gate manifest. The check recomputes the test and gate comparison from the pinned files and
// also requires the saved compare and gateCompare records to show no loss or regression.
function checkGoport(state, rule, readEvidence) {
  const batch = validateBatch(state, rule);
  requireValue(batch.rosterCarryForward == null, "A goport batch has no roster carry-forward.");
  requireValue(text(batch.commit), "A goport batch needs its commit.");
  const pin = batch.upstreamPin?.to;
  const previous = readEvidence(batch.previousBatch?.archive);
  requireValue(previous?.id === batch.previousBatch.id && previous.compilerAccepted === true,
    "previousBatch.archive is not the saved record of an accepted batch.");
  const previousGoport = previous.protectedSet === "goport";
  const baseRef = previousGoport ? { path: previous.goportTests?.results, sha256: previous.goportTests?.sha256 } : rule.baseline;
  // open_revision.py saves the same base as batch.protectedBase when it opens the batch.
  const saved = batch.protectedBase;
  requireValue(saved == null || (saved.batch === previous.id && samePath(saved.tests?.path, baseRef.path) && saved.tests.sha256 === baseRef.sha256
    && samePath(saved.gate?.path, previous.gate?.manifest) && saved.gate.sha256 === previous.gate.sha256),
  `batch.protectedBase differs from the base that accepted batch ${previous.id} gives.`);
  const tests = batch.goportTests;
  requireValue(samePath(tests?.base, baseRef.path) && tests.baseSha256 === baseRef.sha256,
    previousGoport ? `goportTests base must be the results of accepted batch ${previous.id}.`
      : `goportTests base must be the protected baseline ${rule.baseline.path}.`);
  const results = readEvidence({ path: tests.results, sha256: tests.sha256 });
  requireValue(sameHash(results.source?.commit, batch.commit), "goportTests results come from another commit than the batch.");
  requireValue(!pin || sameHash(results.pin, pin), `goportTests results are not at the batch Go pin ${pin}.`);
  const map = tests.nameMap == null ? null : parseNameMap(readEvidence(tests.nameMap, { json: false }));
  const compared = compareTests(readEvidence(baseRef), results, map);
  const reasons = [];
  const recorded = ["lost", "absent", "unrun"].filter(field => size(tests.compare?.[field], `goportTests.compare.${field}`) > 0);
  if (recorded.length) reasons.push(`goportTests.compare reports ${recorded.join(", ")} names.`);
  for (const field of ["lost", "absent", "unrun"]) {
    if (compared[field].length) reasons.push(`${compared[field].length} base ok goport test names are ${field}.`);
  }

  const gateCompare = batch.gateCompare;
  requireValue(text(previous.gate?.manifest) && samePath(gateCompare?.base, previous.gate.manifest)
    && (gateCompare.baseSha256 === undefined || gateCompare.baseSha256 === previous.gate.sha256),
  `gateCompare base must be the gate manifest of accepted batch ${previous.id}.`);
  requireValue(samePath(gateCompare.new, batch.gate?.manifest) && gateCompare.sha256 === batch.gate.sha256,
    "gateCompare new and sha256 must be batch.gate.");
  const newGate = readEvidence({ path: gateCompare.new, sha256: gateCompare.sha256 });
  requireValue(sameHash(newGate.commit, batch.commit), "Gate manifest comes from another commit than the batch.");
  requireValue(!pin || sameHash(newGate.upstreamPin, pin), `Gate manifest is not at the batch Go pin ${pin}.`);
  const gate = compareGate(readEvidence({ path: previous.gate.manifest, sha256: previous.gate.sha256 }), newGate, batch.openDefects);
  if (size(gateCompare.regressions, "gateCompare.regressions") > 0) reasons.push("gateCompare reports gate regressions.");
  if (gate.regressions.length) reasons.push(`${gate.regressions.length} gate items regressed against ${previous.gate.manifest}.`);

  checkRunEvidence(batch, readEvidence);
  const { lost, absent, unrun, ...counts } = compared;
  return { verdict: reasons.length ? "STOP" : "PASS", scope: GOPORT_SCOPE, protectedSet: "goport", rule: GOPORT_RULE, reasons,
    base: { batch: previous.id, tests: baseRef.path, gate: previous.gate.manifest },
    counts: { goportTests: { ...counts, lost: lost.length, absent: absent.length, unrun: unrun.length },
      gate: { baseItems: gate.baseItems, items: gate.items, regressions: gate.regressions.length, knownOpen: gate.knownOpen.length } },
    knownOpenGateItems: gate.knownOpen,
    losses: { goportTests: [...lost, ...absent, ...unrun], gate: gate.regressions } };
}

// Tests may supply parsed synthetic evidence and a synthetic pin. The CLI always uses
// readEvidence and INHERITED_PIN.
export function checkBatch(state, readEvidence = readEvidenceFile, inheritedPin = INHERITED_PIN) {
  try {
    const goport = goportRule(state);
    if (goport) return checkGoport(state, goport, readEvidence);
    const batch = validateBatch(state);
    const carry = rosterCarry(state, batch);
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
    const current = currentResults(candidate, carry?.fromSourceFingerprint ?? batch.sourceFingerprint);
    const candidateAccepted = rowsByKey(candidate.originalAccepted6055?.exactLedger, "Candidate accepted ledger");
    requireValue(candidateAccepted.size === acceptedMap.size, "Candidate accepted ledger changed its name count.");
    for (const [id] of acceptedMap) {
      const row = candidateAccepted.get(id);
      requireValue(row && row.accepted?.status === "PASS", "Candidate accepted ledger renamed or omitted an original name.");
      requireValue(row.current?.status === (current.get(id)?.status ?? "ABSENT"), "Candidate accepted ledger disagrees with exact current outcomes.");
    }
    const originalLosses = losses(accepted, current), laterLosses = losses(later, current);
    // Opt-in crate rule: losses already present in the pinned inherited result are reported,
    // not blocking. The inherited counts must equal the approved counts exactly.
    const optIn = approvedRule(state, "opt-in-crate-no-new-loss");
    let inherited = null;
    if (optIn) {
      requireValue(optIn.inheritedResult?.sha256 === inheritedPin.sha256
        && optIn.inheritedLosses?.originalAccepted === inheritedPin.originalAccepted
        && optIn.inheritedLosses?.laterPasses === inheritedPin.laterPasses, "Inherited loss rule differs from the pinned constants.");
      const statuses = ledgerStatuses(readEvidence(optIn.inheritedResult));
      inherited = { originalAccepted: losses(accepted, statuses), laterPasses: losses(later, statuses) };
      requireValue(inherited.originalAccepted.length === optIn.inheritedLosses?.originalAccepted
        && inherited.laterPasses.length === optIn.inheritedLosses?.laterPasses, "Inherited loss counts differ from the approved rule.");
    }
    const isNew = (loss, list) => !list || !list.some(row => key(row) === key(loss));
    const newOriginal = originalLosses.filter(loss => isNew(loss, inherited?.originalAccepted));
    const newLater = laterLosses.filter(loss => isNew(loss, inherited?.laterPasses));
    const reasons = [];
    if (newOriginal.length) reasons.push(`${newOriginal.length} original accepted PASS names are FAIL or ABSENT${inherited ? " and not inherited" : ""}.`);
    if (newLater.length) reasons.push(`${newLater.length} later baseline PASS names are FAIL or ABSENT${inherited ? " and not inherited" : ""}.`);
    return { verdict: reasons.length ? "STOP" : "PASS", scope: SCOPE, reasons, rule: optIn ? optIn.id : null,
      ...(carry && { rosterCarryForward: { rule: CARRY_FORWARD_RULE, fromRevision: carry.fromRevision, fromSourceFingerprint: carry.fromSourceFingerprint } }),
      counts: { originalAccepted: 6055, originalRetained: 6055 - originalLosses.length, laterPasses: 6330, laterRetained: 6330 - laterLosses.length,
        inheritedOriginal: inherited?.originalAccepted.length ?? null, inheritedLater: inherited?.laterPasses.length ?? null },
      losses: { originalAccepted: originalLosses, laterPasses: laterLosses } };
  } catch (error) {
    return { verdict: "STOP", scope: state?.batch?.protectedSet === "goport" ? GOPORT_SCOPE : SCOPE, reasons: [error.message], counts: null };
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  if (process.argv.length === 3 && process.argv[2] === "--help") {
    console.log(`Usage: node scripts/check-typechecker-batch.mjs <state-dir | legacy-state.json>

A state directory holds current.json and the append-only history.jsonl. The
check rebuilds the full state from both and stops if committed history lines
were changed or removed.

Read-only pre-acceptance check. Exit 0 means the protected-name and review
prerequisites pass. Exit 1 means STOP. This is not a Cargo wrapper.

batch.protectedSet selects the protected set. Without it the batch uses the
legacy cargo roster (below). protectedSet "goport" uses goport's own tests and
gate (see "Goport protected set" at the end).

State requires schemaVersion 1, phase initial-recovery or recovery-continuation, status ready,
decision REVIEW or PASS, goalAuthorization, and a preserved candidate hash.
Legacy roster: acceptedBaseline, originalAccepted, and laterPassBaseline need pinned path/SHA-256
references. Original expectedNames is 6055. Later expectedPasses is 6330.

batch needs id, implementer, hypothesis, sourceFingerprint, fullResult path/hash,
recoveryRevision, recoveryHistory, auditor, and reviewer. History retains all
measured revisions, including failures. Initial recovery limits are 4 revisions,
2 hypotheses, and 2 revisions per hypothesis. Continuation requires a saved
continuationAuthorization with authorized true, instruction, scope, and a valid
ISO date. Its history must keep all four initial revisions and each later
revision, numbered from 1 without gaps or resets. Initial limits still apply
to the first four rows. Later revisions have no fixed count or hypothesis limit.
Each history row needs revision, hypothesis,
sourceFingerprint, and fullResultSha256. A past result hash may be null.
The final row must match this completed full result.

Both verdicts need distinct role/agent identities, batchId, PASS,
sourceFingerprint, and fullResultSha256. Neither may be the implementer.
The auditor role is audit_accepted_roster. Missing evidence, STOP, source
mismatch, renamed/missing protected names, or expectation exceptions stop.

Theo-approved rules in acceptanceRuleChanges apply only to the named batch id:
- unbound-history-rows: listed past revisions may keep a null source and result.
- opt-in-crate-no-new-loss: losses already in the pinned inheritedResult are
  reported, not blocking. Inherited counts must equal the approved counts.
A rule with batchId "*" is ignored, except this standing rule:
- goport-only-roster-carry-forward (batchId "*", standing true, scope): used
  only when batch.rosterCarryForward {fromRevision, fromSourceFingerprint,
  rosterFingerprint} is present. batch.rosterFingerprint is the
  scripts/goport/roster_fp.py hash (all files except crates/ts_goport). The
  history row of the earlier fromRevision must be full_measured, not carried
  itself, with that sourceFingerprint, the same rosterFingerprint, and
  fullResultSha256 equal to batch.fullResult. The full result must then name
  fromSourceFingerprint. Protected names, inherited losses, the current history
  row and both verdicts stay bound to this batch source and full result. The
  output then has rosterCarryForward.

${SCOPE}

Goport protected set (batch.protectedSet "goport"):
The state needs Theo's standing rule ${GOPORT_RULE}: batchId "*", standing
true, approvedBy Theo, instruction, scope, ISO date, protectedSet "goport",
baseline {path, sha256} (the first goport test baseline,
docs/goport-protected/tests-r131.json), and approvalNote, the key of a saved
note that holds Theo's approval. Optional unboundRevisions lists history rows
that may keep a null source (as unbound-history-rows does, for every batch).
The batch has no fullResult, corpus, roster baselines or rosterCarryForward.
The history rules above still apply. The current history row and both verdicts
(PASS, batchId, sourceFingerprint) carry goportTestsSha256 = goportTests.sha256
and gateSha256 = gate.sha256 instead of fullResultSha256.

The base is batch.previousBatch.archive {path, sha256}, the saved record of the
accepted previous batch. When it is a goport batch, the test base is its
goportTests results; else it is the rule baseline. The gate base is its gate.
- goportTests {results, sha256, base, baseSha256, compare, nameMap?}: results
  is the results.json of scripts/goport/goport-tests.sh
  ({source {commit, tree, testbinSha256}, pin, suites {suite {name: ok |
  failed | ignored | unrun}}, incomplete [suite]}). Its source.commit must be
  batch.commit and its pin batch.upstreamPin.to. compare.lost, absent and
  unrun (counts or lists) must be 0. The check also compares the files itself,
  as compare-tests.py does: each base ok name must be ok. failed or ignored is
  lost; unrun, or missing from a missing or incomplete suite, is unrun; missing
  from a complete suite is absent. nameMap {path, sha256} is a TSV of
  oldSuite, oldName, newSuite, newName (more columns ignored; "-" "-" for a
  removed name) for pin bumps and moved tests.
- gateCompare {base, baseSha256?, new, sha256, regressions}: base is the
  previous gate manifest, new and sha256 equal batch.gate {manifest, sha256}, regressions
  (count or list) is 0. The new manifest must have batch.commit and the batch
  pin. The check compares items itself: a base item is removed, a base MATCH
  is not MATCH, or an item is FAIL. A base FAIL editor/<project>/long item may
  stay FAIL while batch.openDefects has an open editor-long-growth record
  (gate-compare.py applies the noise rule). Those items are in knownOpenGateItems.
- ordinaryQuery and latestHono: complete, exitCode 0, matchesOracle, the batch
  sourceFingerprint, and runs [{manifest, sha256}] whose manifests name it.
- languageServerOracle {summary, result}: the summary exists and result says
  0 diff and 0 crash.
- quality {record} and qualityEvidence {sourceFingerprint}: the record names
  the batch source, rustfmtExit 0, clippyExit 0, fingerprintUnchanged true.
${GOPORT_SCOPE}

Independent review must compare retained history against saved batchRecords.
This check cannot prevent arbitrary direct commands or edits to state history.`);
  } else {
  let result;
  try {
    requireValue(process.argv.length === 3, "Usage: node scripts/check-typechecker-batch.mjs <state-dir | legacy-state.json>");
    const path = resolve(process.argv[2]);
    let state;
    if (statSync(path).isDirectory()) {
      verifyAppendOnly(path);
      state = loadState(path);
    } else {
      state = JSON.parse(readFileSync(path, "utf8"));
    }
    result = checkBatch(state);
  } catch (error) {
    result = { verdict: "STOP", scope: SCOPE, reasons: [`Missing or invalid state: ${error.message}`] };
  }
  if (result.losses) {
    result.losses = Object.fromEntries(Object.entries(result.losses).map(([name, rows]) => [name, { total: rows.length, first20: rows.slice(0, 20) }]));
  }
  console.log(JSON.stringify(result, null, 2));
  process.exitCode = result.verdict === "PASS" ? 0 : 1;
  }
}
