// Tests of scripts/goport/oracle-compare.py for bump C reviewer ruling 1: a new API run made with --wire is refused
// (item 1), a masked answer set entry compares only after its mask (item 3, request 2 item 1), and --parity prints
// each known diff with its class and pointer (item 4).
// Run: node --test scripts/goport/oracle-compare.test.mjs
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { gzipSync } from "node:zlib";

const HERE = dirname(fileURLToPath(import.meta.url));
const TOOL = join(HERE, "oracle-compare.py");
const ORACLE = "2991c6e91578b4765ef34de5de47734e167f409a17bda7f450bf3d2eac64389a";
const METHOD = "getTypeOfSymbol";
const GO = { id: 148, flags: 1048576, objectFlags: 6, symbol: "Navigator@71780.265.bundled:///libs/lib.dom.d.ts", value: null };
// The Go answer after each mask (the canon() text: sorted keys, no spaces). "ids" masks the symbol too, "strict" keeps it.
const MASKED = {
  ids: { flags: 1048576, id: "#", objectFlags: 6, symbol: "#", value: null },
  strict: { flags: 1048576, id: "#", objectFlags: 6, symbol: GO.symbol, value: null },
};
const canon = v => JSON.stringify(Object.fromEntries(Object.entries(v).sort(([a], [b]) => (a < b ? -1 : 1))));
const sha = data => createHash("sha256").update(data).digest("hex");
// maskTool of this checkout: the sha256 of the files whose code the masks run.
const MASK_TOOL = Object.fromEntries(["api_oracle.py", "oracle-compare.py"].map(f => [`scripts/goport/${f}`, sha(readFileSync(join(HERE, f)))]));

// An API results dir <root>/results/<label> with one trace qc/t whose event 1 has the class cls and the diff pointer;
// goport's answer is result.
function results(root, label, cls, result, { wire, pointer = null } = {}) {
  const dir = join(root, "results", label);
  mkdirSync(join(dir, "traces/qc"), { recursive: true });
  mkdirSync(join(dir, "responses/qc"), { recursive: true });
  writeFileSync(join(dir, "traces/qc/t.json"), JSON.stringify({ format: "goport-api-result/1", trace: "t", battery: "qc",
    meta: wire ? { wire } : {}, events: [{ event: 1, method: METHOD, class: cls, pointer, sub: null }] }));
  const lines = [{ trace: "t" }, { event: 1, method: METHOD, status: "ok", response: { result } }];
  writeFileSync(join(dir, "responses/qc/t.jsonl.gz"), gzipSync(lines.map(l => JSON.stringify(l)).join("\n") + "\n"));
  writeFileSync(join(dir, "manifest.json"), JSON.stringify({ batteries: { qc: { oracleSha: ORACLE, ...(wire && { wire }) } } }));
  return dir;
}

// A Go golden of qc/t at the oracle under <root>/<name>/golden/<sha12>, whose event 1 has the answer result (ok) or error.
function golden(root, name, { result, error } = {}) {
  const dir = join(root, name, "golden", ORACLE.slice(0, 12), "qc");
  mkdirSync(dir, { recursive: true });
  const rec = error ? { status: "error", response: { error: { code: -32603, message: error } } } : { status: "ok", response: { result } };
  const lines = [{ format: "goport-api-golden/1", trace: "t", battery: "qc" }, { event: 1, method: METHOD, ...rec }];
  const path = join(dir, "t.golden.jsonl.gz");
  writeFileSync(path, gzipSync(lines.map(l => JSON.stringify(l)).join("\n") + "\n"));
  return path;
}

// A goport-oracle-answers/1 set at pin N with one masked entry for qc/t#1. Returns FILE@SHA256.
function maskedSet(root, { mask = "ids", answer = MASKED[mask], header = { mask, maskTool: MASK_TOOL }, entryMask = mask,
  sources = [`tests2/api/golden/${ORACLE.slice(0, 12)}/qc/t.golden.jsonl.gz`] } = {}) {
  const doc = { format: "goport-oracle-answers/1", kind: "api", pin: "673a5f17d713", oracleSha256: ORACLE, goldenSha12: ORACLE.slice(0, 12),
    ...header, requests: { "qc/t#1": { method: METHOD, multiset: [], mask: entryMask, answers: [{ answer, sha256: sha(canon(answer)), sources }] } } };
  const data = gzipSync(JSON.stringify(doc));
  const path = join(root, `masked-${sha(data).slice(0, 8)}.json.gz`);
  writeFileSync(path, data);
  return `${path}@${sha(data)}`;
}

function run(args) {
  const r = spawnSync("python3", [TOOL, ...args, "--kind", "api"], { encoding: "utf8" });
  return { rc: r.status, out: r.status === 2 ? null : JSON.parse(r.stdout), stderr: r.stderr };
}

function inTemp(fn) {
  const root = mkdtempSync(join(tmpdir(), "oracle-compare-"));
  try {
    fn(root);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

test("a new API run made with --wire is refused; a base run may have it", () => inTemp(root => {
  const base = results(root, "base", "same", GO, { wire: 3 });
  assert.equal(run([base, results(root, "new", "same", GO)]).rc, 0);
  const wired = run([results(root, "base2", "same", GO), results(root, "new-wire", "same", GO, { wire: 3 })]);
  assert.equal(wired.rc, 2);
  assert.match(wired.stderr, /was made with --wire/);
}));

test("the ids mask keeps a flake request whose answer differs only in ids (the symbol too), and loses a flags change", () => inTemp(root => {
  const set = maskedSet(root);
  const base = results(root, "base", "flaky_oracle", GO);
  // Other ids than Go: retained through the masked entry, on its own count.
  const ids = run([base, results(root, "ids", "flaky_oracle", { ...GO, id: 136 }), "--answers", set]);
  assert.equal(ids.rc, 0, ids.stderr);
  assert.deepEqual([ids.out.total.retainedByMaskedAnswers, ids.out.total.retainedByAnswers, ids.out.total.lost], [1, 0, 0]);
  assert.deepEqual([ids.out.answers[0].maskedRequests, ids.out.answers[0].mask, ids.out.answers[0].maskTool], [1, "ids", { same: true, rechecked: 0 }]);
  // mask_ids masks the symbol of a type answer, so a symbol change passes with "ids".
  const symbol = run([base, results(root, "symbol", "flaky_oracle", { ...GO, id: 136, symbol: "Window@1.2.x" }), "--answers", set]);
  assert.equal(symbol.rc, 0, symbol.stderr);
  // A field that is not an id (flags): lost.
  const flags = run([base, results(root, "flags", "flaky_oracle", { ...GO, id: 136, flags: 1 }), "--answers", set]);
  assert.equal(flags.rc, 1);
  assert.equal(flags.out.total.lost, 1);
  assert.match(flags.out.lostFirst[0].answersWhy, /not in the answer set/);
}));

test("the strict mask keeps a type id change and loses a symbol or flags change", () => inTemp(root => {
  const set = maskedSet(root, { mask: "strict" });
  const base = results(root, "base", "flaky_oracle", GO);
  const ids = run([base, results(root, "ids", "flaky_oracle", { ...GO, id: 136 }), "--answers", set]);
  assert.equal(ids.rc, 0, ids.stderr);
  assert.deepEqual([ids.out.total.retainedByMaskedAnswers, ids.out.answers[0].mask], [1, "strict"]);
  for (const [label, change] of [["symbol", { symbol: "Window@1.2.x" }], ["flags", { flags: 1 }]]) {
    const lost = run([base, results(root, label, "flaky_oracle", { ...GO, id: 136, ...change }), "--answers", set]);
    assert.equal(lost.rc, 1, `${label}: ${lost.stderr}`);
    assert.deepEqual([lost.out.total.lost, lost.out.total.retainedByMaskedAnswers], [1, 0]);
    assert.match(lost.out.lostFirst[0].answersWhy, /not in the answer set/);
  }
}));

test("a masked set needs the header mask and maskTool, and each entry the header's mask", () => inTemp(root => {
  const base = results(root, "base", "flaky_oracle", GO), now = results(root, "new", "flaky_oracle", GO);
  for (const [options, pattern] of [
    [{ header: { maskTool: MASK_TOOL } }, /has masked entries: an API set needs the header mask \(one of ids, strict\) and maskTool/],
    [{ header: { mask: "names", maskTool: MASK_TOOL }, entryMask: "names" }, /needs the header mask/],
    [{ header: { mask: "ids" } }, /needs the header mask .* and maskTool/],
    [{ header: { mask: "ids", maskTool: { "scripts/goport/api_oracle.py": MASK_TOOL["scripts/goport/api_oracle.py"] } } }, /and maskTool/],
    [{ entryMask: "strict" }, /request qc\/t#1 has mask 'strict'; a masked entry has the mask of the set header \('ids'\)/]]) {
    const bad = run([base, now, "--answers", maskedSet(root, options)]);
    assert.equal(bad.rc, 2, JSON.stringify(options));
    assert.match(bad.stderr, pattern);
  }
}));

test("a changed mask tool masks every source golden again: the same answer passes, another is refused", () => inTemp(root => {
  const base = results(root, "base", "flaky_oracle", GO), now = results(root, "new", "flaky_oracle", { ...GO, id: 136 });
  const old = { mask: "strict", maskTool: { ...MASK_TOOL, "scripts/goport/oracle-compare.py": "0".repeat(64) } };
  const sources = [golden(root, "r1", { result: GO }), golden(root, "r2", { result: { ...GO, id: 990 } })];
  const ok = run([base, now, "--answers", maskedSet(root, { mask: "strict", header: old, sources })]);
  assert.equal(ok.rc, 0, ok.stderr);
  assert.deepEqual(ok.out.answers[0].maskTool, { same: false, rechecked: 2 });
  // A source whose Go answer the mask does not map to the entry's answer (another symbol).
  const other = [...sources, golden(root, "r3", { result: { ...GO, symbol: "Window@1.2.x" } })];
  const bad = run([base, now, "--answers", maskedSet(root, { mask: "strict", header: old, sources: other })]);
  assert.equal(bad.rc, 2);
  assert.match(bad.stderr, /the mask tool changed, and qc\/t#1 in the source golden .*r3.* does not give the masked answer/);
  // A source that is gone.
  const gone = run([base, now, "--answers", maskedSet(root, { mask: "strict", header: old, sources: [join(root, "r9/golden", ORACLE.slice(0, 12), "qc/t.golden.jsonl.gz")] })]);
  assert.equal(gone.rc, 2);
  assert.match(gone.stderr, /the source golden .* cannot be read/);
}));

test("--parity prints each known diff with its class, pointer and the Go golden error", () => inTemp(root => {
  golden(root, ".", { error: "panic: runtime error: invalid memory address or nil pointer dereference" });
  const base = results(root, "base", "same", GO);
  const diff = run([base, results(root, "diff", "diff", GO, { pointer: "/flags" }), "--parity", "--known-diff", "qc/t#1"]);
  assert.equal(diff.rc, 1);  // base same, new diff: lost, though a known diff for parity
  assert.deepEqual(diff.out.parity.knownDiffRows, [{ key: "qc/t#1", class: "diff", method: METHOD, pointer: "/flags", sub: null, goldenError: null }]);
  assert.equal(diff.out.parity.bad, 0);
  assert.match(diff.stderr, /known diff qc\/t#1: diff getTypeOfSymbol pointer \/flags\n/);
  const oed = run([results(root, "base2", "oracle_error_same", GO), results(root, "oed", "oracle_error_diff", GO), "--parity", "--known-diff", "qc/t#1"]);
  assert.equal(oed.out.parity.knownDiffRows[0].goldenError, "panic: runtime error: invalid memory address or nil pointer dereference");
  assert.match(oed.stderr, /known diff qc\/t#1: oracle_error_diff getTypeOfSymbol pointer None; Go golden error: panic: runtime error/);
  // An unused known diff is still printed, with its class in the new run.
  const same = run([base, results(root, "same", "same", GO), "--parity", "--known-diff", "qc/t#1"]);
  assert.deepEqual([same.out.parity.bad, same.out.parity.knownDiffRows[0].class], [1, "same"]);
}));
