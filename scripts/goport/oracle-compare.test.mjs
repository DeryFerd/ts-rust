// Tests of scripts/goport/oracle-compare.py for bump C reviewer ruling 1: a new API run made with --wire is refused
// (item 1), and a masked answer set entry compares only after api_oracle.mask_ids (item 3).
// Run: node --test scripts/goport/oracle-compare.test.mjs
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { gzipSync } from "node:zlib";

const TOOL = join(dirname(fileURLToPath(import.meta.url)), "oracle-compare.py");
const ORACLE = "2991c6e91578b4765ef34de5de47734e167f409a17bda7f450bf3d2eac64389a";
const METHOD = "getTypeOfSymbol";
const GO = { id: 148, flags: 1048576, objectFlags: 6, symbol: "Navigator@71780.265.bundled:///libs/lib.dom.d.ts", value: null };
// The Go answer after mask_ids: every symbol and type id is "#" (the canon() text: sorted keys, no spaces).
const MASKED = { flags: 1048576, id: "#", objectFlags: 6, symbol: "#", value: null };
const canon = v => JSON.stringify(Object.fromEntries(Object.entries(v).sort(([a], [b]) => (a < b ? -1 : 1))));

// An API results dir with one trace qc/t whose event 1 has the class cls; goport's answer is result.
function results(root, label, cls, result, { wire } = {}) {
  const dir = join(root, label);
  mkdirSync(join(dir, "traces/qc"), { recursive: true });
  mkdirSync(join(dir, "responses/qc"), { recursive: true });
  writeFileSync(join(dir, "traces/qc/t.json"), JSON.stringify({ format: "goport-api-result/1", trace: "t", battery: "qc",
    meta: wire ? { wire } : {}, events: [{ event: 1, method: METHOD, class: cls }] }));
  const lines = [{ trace: "t" }, { event: 1, method: METHOD, status: "ok", response: { result } }];
  writeFileSync(join(dir, "responses/qc/t.jsonl.gz"), gzipSync(lines.map(l => JSON.stringify(l)).join("\n") + "\n"));
  writeFileSync(join(dir, "manifest.json"), JSON.stringify({ batteries: { qc: { oracleSha: ORACLE, ...(wire && { wire }) } } }));
  return dir;
}

// A goport-oracle-answers/1 set at pin N with one masked entry for qc/t#1. Returns FILE@SHA256.
function maskedSet(root, answer = MASKED) {
  const doc = { format: "goport-oracle-answers/1", kind: "api", pin: "673a5f17d713", oracleSha256: ORACLE, goldenSha12: ORACLE.slice(0, 12),
    requests: { "qc/t#1": { method: METHOD, multiset: [], mask: "ids", answers: [{ answer,
      sha256: createHash("sha256").update(canon(answer)).digest("hex"),
      sources: [`tests2/api/golden/${ORACLE.slice(0, 12)}/qc/t.golden.jsonl.gz`] }] } } };
  const data = gzipSync(JSON.stringify(doc));
  const path = join(root, "masked.json.gz");
  writeFileSync(path, data);
  return `${path}@${createHash("sha256").update(data).digest("hex")}`;
}

function run(args) {
  const r = spawnSync("python3", [TOOL, ...args, "--kind", "api"], { encoding: "utf8" });
  return { rc: r.status, out: r.status === 2 ? null : JSON.parse(r.stdout), stderr: r.stderr };
}

test("a new API run made with --wire is refused; a base run may have it", () => {
  const root = mkdtempSync(join(tmpdir(), "oracle-compare-"));
  try {
    const base = results(root, "base", "same", GO, { wire: 3 });
    assert.equal(run([base, results(root, "new", "same", GO)]).rc, 0);
    const wired = run([results(root, "base2", "same", GO), results(root, "new-wire", "same", GO, { wire: 3 })]);
    assert.equal(wired.rc, 2);
    assert.match(wired.stderr, /was made with --wire/);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("a masked entry keeps a flake request whose answer differs only in ids, and loses one that differs elsewhere", () => {
  const root = mkdtempSync(join(tmpdir(), "oracle-compare-"));
  try {
    const set = maskedSet(root);
    const base = results(root, "base", "flaky_oracle", GO);
    // Other ids than Go: retained through the masked entry, on its own count.
    const ids = run([base, results(root, "ids", "flaky_oracle", { ...GO, id: 136 }), "--answers", set]);
    assert.equal(ids.rc, 0, ids.stderr);
    assert.deepEqual([ids.out.total.retainedByMaskedAnswers, ids.out.total.retainedByAnswers, ids.out.total.lost], [1, 0, 0]);
    assert.equal(ids.out.answers[0].maskedRequests, 1);
    // A field that is not an id (flags): lost.
    const flags = run([base, results(root, "flags", "flaky_oracle", { ...GO, id: 136, flags: 1 }), "--answers", set]);
    assert.equal(flags.rc, 1);
    assert.equal(flags.out.total.lost, 1);
    assert.match(flags.out.lostFirst[0].answersWhy, /not in the answer set/);
    // Only an API entry with one answer can be masked.
    const two = maskedSet(root, MASKED).replace(/@.*/, "");
    const doc = { format: "goport-oracle-answers/1", kind: "api", pin: "673a5f17d713", oracleSha256: ORACLE, goldenSha12: ORACLE.slice(0, 12),
      requests: { "qc/t#1": { method: METHOD, multiset: [], mask: "names", answers: [{ answer: MASKED,
        sha256: createHash("sha256").update(canon(MASKED)).digest("hex"), sources: [`x/golden/${ORACLE.slice(0, 12)}/qc/t.golden.jsonl.gz`] }] } } };
    writeFileSync(two, gzipSync(JSON.stringify(doc)));
    const sha = createHash("sha256").update(gzipSync(JSON.stringify(doc))).digest("hex");
    const bad = run([base, results(root, "bad", "flaky_oracle", GO), "--answers", `${two}@${sha}`]);
    assert.equal(bad.rc, 2);
    assert.match(bad.stderr, /only an API entry with one answer can have mask "ids"/);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
