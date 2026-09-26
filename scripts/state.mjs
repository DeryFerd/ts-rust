import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { appendFileSync, existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

// Typechecker accountability state, split into two files:
// - current.json: the small live state. Root reads it at every start or resume.
// - history.jsonl: append-only. Revisions, auditor passing results, archived notes
//   and every change to current.json. The last line for a revision or note wins.
// loadState() rebuilds the legacy single-object shape for the batch check and audits.

const ROOT = fileURLToPath(new URL("../", import.meta.url));
export const STATE_DIR = "docs/typechecker-state";
const HASH = /^[a-f0-9]{64}$/;
// These live in history.jsonl only. current.json must not carry a second copy.
const HISTORY_ONLY = ["additionalPassingResultsForAuditor"];
// Kept in current.json by `migrate`. Every other legacy key becomes a note.
const CURRENT_KEYS = [
  "schemaVersion", "status", "decision", "updated", "reason", "phase", "goalAuthorization",
  "continuationAuthorization", "executionPolicy", "instructions", "plan", "roles", "limits",
  "acceptedBaseline", "originalAccepted", "laterPassBaseline", "acceptedSource",
  "preservedCandidateSourceFingerprint", "candidate", "lastFullResult", "latestAcceptedHono",
  "periodicAcceptedProjectResults", "readRestrictions", "parallelModelPreference", "acceptanceRuleChanges",
  "batch", "batchRecords",
];

function fail(message) {
  throw new Error(message);
}

function paths(dir) {
  const base = resolve(ROOT, dir);
  return { base, current: resolve(base, "current.json"), history: resolve(base, "history.jsonl") };
}

function readJson(file) {
  return JSON.parse(readFileSync(file, "utf8"));
}

export function readHistory(dir = STATE_DIR) {
  const file = paths(dir).history;
  return readFileSync(file, "utf8").split("\n").filter(Boolean).map((line, index) => {
    try {
      return JSON.parse(line);
    } catch {
      return fail(`history.jsonl line ${index + 1} is not valid JSON.`);
    }
  });
}

// Rebuilds the legacy state object. Throws on a malformed or reset history.
export function loadState(dir = STATE_DIR) {
  const current = readJson(paths(dir).current);
  const lines = readHistory(dir);
  const revisions = new Map();
  const passing = [];
  const notes = {};
  for (const line of lines) {
    if (line.kind === "revision") revisions.set(line.value?.revision, line.value);
    else if (line.kind === "passing-result") passing.push(line.value);
    else if (line.kind === "note") notes[line.key] = line.value;
  }
  const history = [...revisions.keys()].sort((a, b) => a - b).map(revision => revisions.get(revision));
  history.forEach((row, index) => row?.revision === index + 1 || fail(`History revision ${index + 1} is missing or reset.`));
  for (const key of Object.keys(notes)) if (key in current) fail(`Note ${key} duplicates a current.json key.`);
  return {
    ...notes,
    ...current,
    additionalPassingResultsForAuditor: passing,
    batch: current.batch ? { ...current.batch, recoveryHistory: history } : current.batch,
  };
}

// Fails when history.jsonl no longer starts with the committed copy.
export function verifyAppendOnly(dir = STATE_DIR) {
  const file = paths(dir).history;
  let committed;
  try {
    committed = execFileSync("git", ["-C", ROOT, "show", `HEAD:${relative(ROOT, file)}`], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] });
  } catch {
    return "history.jsonl is not committed yet. No append-only baseline.";
  }
  if (!readFileSync(file, "utf8").startsWith(committed)) fail("history.jsonl changed committed lines. It is append-only.");
  return `history.jsonl keeps all ${committed.split("\n").filter(Boolean).length} committed lines.`;
}

function append(dir, line) {
  appendFileSync(paths(dir).history, `${JSON.stringify({ ...line, recordedUtc: new Date().toISOString() })}\n`);
}

function writeCurrent(dir, value) {
  const file = paths(dir).current;
  writeFileSync(`${file}.next`, `${JSON.stringify(value, null, 2)}\n`);
  renameSync(`${file}.next`, file);
}

function recordRevision(dir, row) {
  const history = loadState(dir).batch?.recoveryHistory ?? [];
  const last = history.length;
  Number.isInteger(row?.revision) || fail("A revision needs an integer revision number.");
  (row.revision === last || row.revision === last + 1)
    || fail(`Revision ${row.revision} is not the latest (${last}) or the next (${last + 1}). Do not skip or rewrite older revisions.`);
  typeof row.hypothesis === "string" && row.hypothesis.trim() || fail("A revision needs a hypothesis.");
  HASH.test(row.sourceFingerprint) || fail("A revision needs a SHA-256 sourceFingerprint.");
  row.fullResultSha256 === null || HASH.test(row.fullResultSha256) || fail("fullResultSha256 must be a SHA-256 or null.");
  append(dir, { kind: "revision", value: row });
  return `Recorded revision ${row.revision}.`;
}

function recordNote(dir, key, value) {
  typeof key === "string" && /^[A-Za-z][\w-]*$/.test(key) || fail("A note needs a key made of letters, digits, _ or -.");
  key in readJson(paths(dir).current) && fail(`${key} is a current.json key. Use record current.`);
  HISTORY_ONLY.includes(key) && fail(`${key} has its own record kind.`);
  append(dir, { kind: "note", key, value });
  return `Recorded note ${key}.`;
}

// Merges top-level keys into current.json and logs the patch to history.jsonl.
function recordCurrent(dir, patch) {
  patch && typeof patch === "object" && !Array.isArray(patch) || fail("record current needs a JSON object.");
  for (const key of HISTORY_ONLY) key in patch && fail(`${key} lives in history.jsonl. Use record passing-result.`);
  patch.batch && "recoveryHistory" in patch.batch && fail("batch.recoveryHistory lives in history.jsonl. Use record revision.");
  const current = readJson(paths(dir).current);
  const next = { ...current, ...patch };
  const oldId = current.batch?.id;
  if (patch.batch && oldId && patch.batch.id !== oldId) {
    const saved = `docs/typechecker-batches/${oldId}.json`;
    existsSync(resolve(ROOT, saved)) || fail(`Save the replaced batch first: ${saved} (scripts/state batch --with-history).`);
    (next.batchRecords ?? []).some(entry => (entry?.path ?? entry) === saved) || fail(`Add ${saved} to batchRecords before replacing the batch.`);
  }
  const notes = new Set(readHistory(dir).filter(line => line.kind === "note").map(line => line.key));
  for (const key of Object.keys(patch)) notes.has(key) && fail(`${key} is an archived note. Use record note ${key}.`);
  writeCurrent(dir, next);
  append(dir, { kind: "current", value: patch });
  return `Updated current.json: ${Object.keys(patch).join(", ")}.`;
}

// One-time split of the legacy single-file state. Refuses to overwrite.
export function migrate(legacyFile, dir = STATE_DIR) {
  const { current: currentFile, history: historyFile } = paths(dir);
  if (existsSync(currentFile) || existsSync(historyFile)) fail(`${dir} already exists. Migration runs once.`);
  const bytes = readFileSync(legacyFile);
  const legacy = JSON.parse(bytes.toString("utf8"));
  const current = {};
  const lines = [{ kind: "migration", value: { from: legacyFile, sha256: createHash("sha256").update(bytes).digest("hex"), bytes: bytes.length } }];
  for (const [key, value] of Object.entries(legacy)) {
    if (CURRENT_KEYS.includes(key)) current[key] = value;
    else if (!HISTORY_ONLY.includes(key)) lines.push({ kind: "note", key, value });
  }
  const { recoveryHistory = [], ...batch } = legacy.batch ?? {};
  if (legacy.batch) current.batch = batch;
  lines.push(...recoveryHistory.map(value => ({ kind: "revision", value })));
  lines.push(...(legacy.additionalPassingResultsForAuditor ?? []).map(value => ({ kind: "passing-result", value })));
  mkdirSync(paths(dir).base, { recursive: true });
  writeFileSync(historyFile, lines.map(line => `${JSON.stringify(line)}\n`).join(""));
  writeCurrent(dir, current);
  const rebuilt = loadState(dir);
  const canonical = value => JSON.stringify(value, (_, item) => item && typeof item === "object" && !Array.isArray(item)
    ? Object.fromEntries(Object.entries(item).sort(([a], [b]) => a.localeCompare(b))) : item);
  const legacyShape = { ...legacy, additionalPassingResultsForAuditor: legacy.additionalPassingResultsForAuditor ?? [] };
  canonical(rebuilt) === canonical(legacyShape) || fail("Rebuilt state differs from the legacy file. Remove the output and investigate.");
  return `Split ${legacyFile} into ${dir}: current.json ${readFileSync(currentFile).length} bytes, history.jsonl ${lines.length} lines. Rebuilt state matches.`;
}

function summary(dir) {
  const state = loadState(dir);
  const batch = state.batch ?? {};
  const history = batch.recoveryHistory ?? [];
  const last = history.at(-1);
  const measured = history.findLast(row => typeof row.outcome === "string" && row.outcome.length > 0);
  const label = row => row && `${row.revision} ${(row.hypothesisLabel ?? row.hypothesis).slice(0, 120)} [${row.status ?? "no status"}]`;
  const verdict = role => role ? `${role.verdict ?? "none"} by ${role.agent ?? "?"}` : "none";
  const hono = batch.latestHono ?? state.latestAcceptedHono;
  const rows = [
    ["state", `${state.phase} / ${state.status} / decision ${state.decision}`],
    ["updated", state.updated],
    ["reason", state.reason],
    ["batch", `${batch.id} (implementer ${batch.implementer})`],
    ["source", batch.sourceFingerprint],
    ["revisions", `${history.length} recorded, batch says ${batch.recoveryRevision}${history.length === batch.recoveryRevision ? "" : " (MISMATCH)"}`],
    ["last revision", label(last)],
    ["last measured", measured && `${label(measured)}: ${measured.outcome}`],
    ["batch Query", JSON.stringify(batch.ordinaryQuery ?? null)],
    ["batch Hono", hono && `${hono.startedUtc ?? "?"} complete=${hono.complete} source ${hono.sourceFingerprint ?? "?"}`],
    ["auditor", verdict(batch.auditor)],
    ["reviewer", verdict(batch.reviewer)],
    ["next action", batch.nextPermittedAction],
    ["history", `${readHistory(dir).length} lines. Use history --last N, --kind, --key, --revision.`],
  ];
  return rows.map(([label, value]) => `${label.padEnd(15)}${value ?? "none"}`).join("\n");
}

function readInput(arg) {
  arg || fail("Pass a JSON file path or - for stdin.");
  return JSON.parse(readFileSync(arg === "-" ? 0 : arg, "utf8"));
}

function option(args, name) {
  const index = args.indexOf(name);
  return index === -1 ? undefined : args[index + 1];
}

const USAGE = `Usage: scripts/state <command>

  summary                         Short live status. Start here.
  batch [--with-history]          Current batch JSON. --with-history adds recoveryHistory
                                  in the shape saved to docs/typechecker-batches/<id>.json.
  history [--last N] [--kind K] [--key NAME] [--revision N]
                                  Print history lines (default --last 5). Kinds: revision,
                                  passing-result, note, current, migration.
  record revision <file|->        Append a revision row. Only the latest or next number.
  record passing-result <file|->  Append an auditor passing-result reference.
  record note <key> <file|->      Archive a named record (diagnosis, measurement, plan).
  record current <file|->         Merge top-level keys into current.json and log the patch.
  export                          Full legacy-shaped state JSON (for audits).
  verify                          Rebuild the state and check history.jsonl is append-only.
  migrate <legacy.json>           One-time split of the old single-file state.

Directory: ${STATE_DIR} (override with TS_STATE_DIR).`;

export function main(args, dir = process.env.TS_STATE_DIR ?? STATE_DIR) {
  const [command, ...rest] = args;
  switch (command) {
    case "summary": return summary(dir);
    case "batch": {
      const batch = rest.includes("--with-history") ? loadState(dir).batch : readJson(paths(dir).current).batch;
      return JSON.stringify(batch, null, 2);
    }
    case "history": {
      const kind = option(rest, "--kind"), key = option(rest, "--key"), revision = option(rest, "--revision");
      const last = Number(option(rest, "--last") ?? 5);
      Number.isInteger(last) && last > 0 || fail("--last needs a positive integer.");
      const lines = readHistory(dir).filter(line => (!kind || line.kind === kind) && (!key || line.key === key)
        && (!revision || (line.kind === "revision" && line.value?.revision === Number(revision))));
      return lines.slice(-last).map(line => JSON.stringify(line)).join("\n");
    }
    case "record": {
      const [kind, ...input] = rest;
      if (kind === "revision") return recordRevision(dir, readInput(input[0]));
      if (kind === "passing-result") {
        append(dir, { kind, value: readInput(input[0]) });
        return "Recorded passing result.";
      }
      if (kind === "note") return recordNote(dir, input[0], readInput(input[1]));
      if (kind === "current") return recordCurrent(dir, readInput(input[0]));
      return fail(`Unknown record kind: ${kind ?? "(none)"}.\n\n${USAGE}`);
    }
    case "export": return JSON.stringify(loadState(dir), null, 2);
    case "verify": {
      const state = loadState(dir);
      return `State rebuilds with ${state.batch?.recoveryHistory?.length ?? 0} revisions. ${verifyAppendOnly(dir)}`;
    }
    case "migrate": return migrate(rest[0] ?? fail("Pass the legacy state file."), dir);
    case undefined: case "--help": case "-h": case "help": return USAGE;
    default: return fail(`Unknown command: ${command}.\n\n${USAGE}`);
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const output = main(process.argv.slice(2));
    if (output) console.log(output);
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}
