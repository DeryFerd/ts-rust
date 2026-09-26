import assert from "node:assert/strict";
import { appendFileSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { loadState, main, migrate } from "./state.mjs";

const hash = digit => digit.repeat(64);
const row = revision => ({ revision, hypothesis: "h", sourceFingerprint: hash("a"), fullResultSha256: null });

// A synthetic legacy state. Tests never touch the real state directory.
function legacyDir() {
  const dir = mkdtempSync(join(tmpdir(), "ts-state-"));
  const legacy = {
    schemaVersion: 1, status: "active", decision: "STOP", phase: "recovery-continuation",
    batch: { id: "b1", recoveryRevision: 2, recoveryHistory: [row(1), row(2)] },
    batchRecords: [],
    additionalPassingResultsForAuditor: [{ path: "p", sha256: hash("b") }],
    oldDiagnosis: { note: "kept" },
  };
  writeFileSync(join(dir, "legacy.json"), JSON.stringify(legacy));
  migrate(join(dir, "legacy.json"), join(dir, "state"));
  return { legacy, state: join(dir, "state"), dir };
}

test("migrate splits and rebuilds the legacy state exactly", () => {
  const { legacy, state } = legacyDir();
  assert.deepEqual(loadState(state), legacy);
  const current = JSON.parse(readFileSync(join(state, "current.json"), "utf8"));
  assert.equal(current.batch.recoveryHistory, undefined);
  assert.equal(current.oldDiagnosis, undefined);
  assert.throws(() => migrate(join(state, "..", "legacy.json"), state), /already exists/);
});

test("record revision appends only the latest or next revision", () => {
  const { state, dir } = legacyDir();
  const write = value => {
    const file = join(dir, "row.json");
    writeFileSync(file, JSON.stringify(value));
    return main(["record", "revision", file], state);
  };
  assert.throws(() => write(row(4)), /not the latest/);
  assert.throws(() => write(row(1)), /not the latest/);
  write({ ...row(2), status: "measured" });
  write(row(3));
  const history = loadState(state).batch.recoveryHistory;
  assert.deepEqual(history.map(item => item.revision), [1, 2, 3]);
  assert.equal(history[1].status, "measured");
});

test("a gap in revision history fails to load", () => {
  const { state } = legacyDir();
  appendFileSync(join(state, "history.jsonl"), `${JSON.stringify({ kind: "revision", value: row(5) })}\n`);
  assert.throws(() => loadState(state), /missing or reset/);
});

test("record current refuses to replace a batch without its saved record", () => {
  const { state, dir } = legacyDir();
  const file = join(dir, "patch.json");
  writeFileSync(file, JSON.stringify({ batch: { id: "b2" } }));
  assert.throws(() => main(["record", "current", file], state), /Save the replaced batch/);
  writeFileSync(file, JSON.stringify({ batch: { id: "b1", recoveryHistory: [] } }));
  assert.throws(() => main(["record", "current", file], state), /record revision/);
  writeFileSync(file, JSON.stringify({ oldDiagnosis: {} }));
  assert.throws(() => main(["record", "current", file], state), /archived note/);
  writeFileSync(file, JSON.stringify({ decision: "REVIEW" }));
  main(["record", "current", file], state);
  assert.equal(loadState(state).decision, "REVIEW");
  assert.match(main(["history", "--last", "1"], state), /"kind":"current"/);
});

test("import applies an edited full state as records", () => {
  const { state, dir } = legacyDir();
  const edited = loadState(state);
  edited.decision = "REVIEW";
  edited.batch.recoveryHistory.push(row(3));
  edited.batch.recoveryRevision = 3;
  edited.additionalPassingResultsForAuditor.push({ path: "q", sha256: hash("c") });
  edited.newDiagnosis = { note: "added" };
  const file = join(dir, "edited.json");
  writeFileSync(file, JSON.stringify(edited));
  main(["import", file], state);
  assert.deepEqual(loadState(state), edited);
  main(["import", file], state);
  assert.match(main(["import", file], state), /Imported 0 revision rows, 0 passing results, 0 notes, current keys: none/);
  edited.batch.recoveryHistory[0] = { ...row(1), hypothesis: "rewritten" };
  writeFileSync(file, JSON.stringify(edited));
  assert.throws(() => main(["import", file], state), /rewrites an older revision/);
});
