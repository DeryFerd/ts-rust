// Tests of scripts/goport/oracle-compare.py for bump C reviewer rulings 1 and 2: a new API run made with --wire is
// refused (ruling 1 item 1), a masked answer set entry compares only after the "type-ids" mask (ruling 1 item 3,
// ruling 2 item 1), and --parity prints each known diff with its class and pointer (ruling 1 item 4, ruling 2 item 2).
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
const TYPE = "getTypeOfSymbol", SIG = "getResolvedSignature";
const GO = { id: 148, flags: 1048576, objectFlags: 6, symbol: "Navigator@71780.265.bundled:///libs/lib.dom.d.ts", value: null };
const GO_SIG = { id: 12, flags: 0, typeParameters: [148], parameters: ["x@1.2.@PROJECT_DIR@/a.ts"] };
// The Go answers after the type-ids mask: type and signature ids are "#", the symbol and the flags stay.
const MASKED = { [TYPE]: { ...GO, id: "#" }, [SIG]: { ...GO_SIG, id: "#", typeParameters: ["#"] } };
// canon(): sorted keys, no spaces.
const canon = v => JSON.stringify(v, (_, x) => x && typeof x === "object" && !Array.isArray(x)
  ? Object.fromEntries(Object.entries(x).sort(([a], [b]) => (a < b ? -1 : 1))) : x);
const sha = data => createHash("sha256").update(data).digest("hex");
// maskTool of this checkout: the sha256 of the files whose code the mask runs.
const MASK_TOOL = Object.fromEntries(["api_oracle.py", "oracle-compare.py"].map(f => [`scripts/goport/${f}`, sha(readFileSync(join(HERE, f)))]));

// An API results dir <root>/results/<label> with one trace qc/t. events: [{event, method, cls, result, pointer}];
// goport's answer to each is result. A plain (cls, result) gives one getTypeOfSymbol event 1.
function results(root, label, cls, result, { wire, pointer = null, events = [{ event: 1, method: TYPE, cls, result, pointer }] } = {}) {
  const dir = join(root, "results", label);
  mkdirSync(join(dir, "traces/qc"), { recursive: true });
  mkdirSync(join(dir, "responses/qc"), { recursive: true });
  writeFileSync(join(dir, "traces/qc/t.json"), JSON.stringify({ format: "goport-api-result/1", trace: "t", battery: "qc", meta: wire ? { wire } : {},
    events: events.map(e => ({ event: e.event, method: e.method, class: e.cls, pointer: e.pointer ?? null, sub: null })) }));
  const lines = [{ trace: "t" }, ...events.map(e => ({ event: e.event, method: e.method, status: "ok", response: { result: e.result } }))];
  writeFileSync(join(dir, "responses/qc/t.jsonl.gz"), gzipSync(lines.map(l => JSON.stringify(l)).join("\n") + "\n"));
  writeFileSync(join(dir, "manifest.json"), JSON.stringify({ batteries: { qc: { oracleSha: ORACLE, ...(wire && { wire }) } } }));
  return dir;
}

// A Go golden of qc/t at the oracle under <root>/<name>/golden/<sha12>, whose event 1 has the answer result (ok) or error.
function golden(root, name, { result, error } = {}) {
  const dir = join(root, name, "golden", ORACLE.slice(0, 12), "qc");
  mkdirSync(dir, { recursive: true });
  const rec = error ? { status: "error", response: { error: { code: -32603, message: error } } } : { status: "ok", response: { result } };
  const lines = [{ format: "goport-api-golden/1", trace: "t", battery: "qc" }, { event: 1, method: TYPE, ...rec }];
  const path = join(dir, "t.golden.jsonl.gz");
  writeFileSync(path, gzipSync(lines.map(l => JSON.stringify(l)).join("\n") + "\n"));
  return path;
}

// A goport-oracle-answers/1 set at pin N. entries: {"qc/t#<event>": {method, answer, mask}}; the default is one masked
// getTypeOfSymbol entry for qc/t#1. Returns FILE@SHA256.
function answerSet(root, { header = { mask: "type-ids", maskTool: MASK_TOOL }, sources = [`tests2/api/golden/${ORACLE.slice(0, 12)}/qc/t.golden.jsonl.gz`],
  entries = { "qc/t#1": { method: TYPE, answer: MASKED[TYPE], mask: "type-ids" } } } = {}) {
  const requests = Object.fromEntries(Object.entries(entries).map(([key, { method, answer, mask }]) =>
    [key, { method, multiset: [], ...(mask && { mask }), answers: [{ answer, sha256: sha(canon(answer)), sources }] }]));
  const doc = { format: "goport-oracle-answers/1", kind: "api", pin: "673a5f17d713", oracleSha256: ORACLE, goldenSha12: ORACLE.slice(0, 12), ...header, requests };
  const data = gzipSync(JSON.stringify(doc));
  const path = join(root, `set-${sha(data).slice(0, 8)}.json.gz`);
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

test("the type-ids mask keeps a type or signature id change and loses a symbol, flags or objectFlags change", () => inTemp(root => {
  const set = answerSet(root, { entries: { "qc/t#1": { method: TYPE, answer: MASKED[TYPE], mask: "type-ids" },
    "qc/t#2": { method: SIG, answer: MASKED[SIG], mask: "type-ids" } } });
  const both = (t, s) => [{ event: 1, method: TYPE, cls: "flaky_oracle", result: t }, { event: 2, method: SIG, cls: "flaky_oracle", result: s }];
  const base = results(root, "base", null, null, { events: both(GO, GO_SIG) });
  // Other type and signature ids than Go: retained through the masked entries, on their own count.
  const ids = run([base, results(root, "ids", null, null, { events: both({ ...GO, id: 136 }, { ...GO_SIG, id: 99, typeParameters: [136] }) }), "--answers", set]);
  assert.equal(ids.rc, 0, ids.stderr);
  assert.deepEqual([ids.out.total.retainedByMaskedAnswers, ids.out.total.retainedByAnswers, ids.out.total.lost], [2, 0, 0]);
  assert.deepEqual([ids.out.answers[0].maskedRequests, ids.out.answers[0].mask, ids.out.answers[0].maskTool], [2, "type-ids", { same: true, rechecked: 0 }]);
  // A field that is not a type or signature id: lost.
  for (const [label, t, s] of [["symbol", { ...GO, symbol: "Window@1.2.x" }, GO_SIG], ["flags", { ...GO, flags: 1 }, GO_SIG],
    ["objectFlags", { ...GO, objectFlags: 4 }, GO_SIG], ["parameter", GO, { ...GO_SIG, parameters: ["y@1.2.@PROJECT_DIR@/a.ts"] }]]) {
    const lost = run([base, results(root, label, null, null, { events: both({ ...t, id: 136 }, s) }), "--answers", set]);
    assert.equal(lost.rc, 1, `${label}: ${lost.stderr}`);
    assert.deepEqual([lost.out.total.lost, lost.out.total.retainedByMaskedAnswers], [1, 1], label);
    assert.match(lost.out.lostFirst[0].answersWhy, /not in the answer set/);
  }
}));

test("a masked entry covers only its own key", () => inTemp(root => {
  // qc/t#2 is in the same set without a mask: its answer is compared exactly, so another type id is lost.
  const set = answerSet(root, { entries: { "qc/t#1": { method: TYPE, answer: MASKED[TYPE], mask: "type-ids" }, "qc/t#2": { method: TYPE, answer: GO } } });
  const two = (a, b, cls = "flaky_oracle") => [{ event: 1, method: TYPE, cls, result: a }, { event: 2, method: TYPE, cls, result: b }];
  const base = results(root, "base", null, null, { events: two(GO, GO) });
  const out = run([base, results(root, "new", null, null, { events: two({ ...GO, id: 136 }, { ...GO, id: 136 }) }), "--answers", set]);
  assert.equal(out.rc, 1);
  assert.deepEqual([out.out.total.retainedByMaskedAnswers, out.out.total.lost, out.out.lostFirst[0].event], [1, 1, "2"]);
  // A same request of another key, in no set, is not masked either: an id change there is a loss.
  const same = results(root, "base-same", null, null, { events: [{ event: 1, method: TYPE, cls: "flaky_oracle", result: GO }, { event: 3, method: TYPE, cls: "same", result: GO }] });
  const other = run([same, results(root, "new-same", null, null, { events: [{ event: 1, method: TYPE, cls: "flaky_oracle", result: { ...GO, id: 136 } },
    { event: 3, method: TYPE, cls: "id_only", result: { ...GO, id: 136 } }] }), "--answers", answerSet(root)]);
  assert.deepEqual([other.rc, other.out.total.retainedByMaskedAnswers, other.out.total.lost], [1, 1, 1]);
}));

test("a masked set needs the header mask type-ids and maskTool, and each entry the header's mask", () => inTemp(root => {
  const base = results(root, "base", "flaky_oracle", GO), now = results(root, "new", "flaky_oracle", GO);
  const entry = mask => ({ entries: { "qc/t#1": { method: TYPE, answer: MASKED[TYPE], mask } } });
  for (const [options, pattern] of [
    [{ header: { maskTool: MASK_TOOL } }, /has masked entries: an API set needs the header mask 'type-ids' and maskTool/],
    // api_oracle.mask_ids ("ids") is not a mask kind of an answer set (ruling 2 item 1).
    [{ header: { mask: "ids", maskTool: MASK_TOOL }, ...entry("ids") }, /needs the header mask 'type-ids'/],
    [{ header: { mask: "type-ids" } }, /needs the header mask 'type-ids' and maskTool/],
    [{ header: { mask: "type-ids", maskTool: { "scripts/goport/api_oracle.py": MASK_TOOL["scripts/goport/api_oracle.py"] } } }, /and maskTool/],
    [{ ...entry("ids") }, /request qc\/t#1 has mask 'ids'; a masked entry has the mask of the set header \('type-ids'\)/]]) {
    const bad = run([base, now, "--answers", answerSet(root, options)]);
    assert.equal(bad.rc, 2, JSON.stringify(options));
    assert.match(bad.stderr, pattern);
  }
}));

test("a changed mask tool masks every source golden again: the same answer passes, another is refused", () => inTemp(root => {
  const base = results(root, "base", "flaky_oracle", GO), now = results(root, "new", "flaky_oracle", { ...GO, id: 136 });
  const header = { mask: "type-ids", maskTool: { ...MASK_TOOL, "scripts/goport/oracle-compare.py": "0".repeat(64) } };
  const sources = [golden(root, "r1", { result: GO }), golden(root, "r2", { result: { ...GO, id: 990 } })];
  const ok = run([base, now, "--answers", answerSet(root, { header, sources })]);
  assert.equal(ok.rc, 0, ok.stderr);
  assert.deepEqual(ok.out.answers[0].maskTool, { same: false, rechecked: 2 });
  // A source whose Go answer the mask does not map to the entry's answer (another symbol).
  const other = [...sources, golden(root, "r3", { result: { ...GO, symbol: "Window@1.2.x" } })];
  const bad = run([base, now, "--answers", answerSet(root, { header, sources: other })]);
  assert.equal(bad.rc, 2);
  assert.match(bad.stderr, /the mask tool changed, and qc\/t#1 in the source golden .*r3.* does not give the masked answer/);
  // A source that is gone.
  const gone = run([base, now, "--answers", answerSet(root, { header, sources: [join(root, "r9/golden", ORACLE.slice(0, 12), "qc/t.golden.jsonl.gz")] })]);
  assert.equal(gone.rc, 2);
  assert.match(gone.stderr, /the source golden .* cannot be read/);
}));

test("--parity prints each known diff with its class, pointer and the Go golden error", () => inTemp(root => {
  golden(root, ".", { error: "panic: runtime error: invalid memory address or nil pointer dereference" });
  const base = results(root, "base", "same", GO);
  const known = ["--parity", "--known-diff", "qc/t#1"];
  const diff = run([base, results(root, "diff", "diff", GO, { pointer: "/flags" }), ...known]);
  assert.equal(diff.rc, 1);  // base same, new diff: lost, though a known diff for parity
  assert.deepEqual(diff.out.parity.knownDiffRows, [{ key: "qc/t#1", class: "diff", method: TYPE, pointer: "/flags", sub: null, goldenError: null }]);
  assert.equal(diff.out.parity.bad, 0);
  assert.match(diff.stderr, /known diff qc\/t#1: diff getTypeOfSymbol pointer \/flags\n/);
  assert.deepEqual([diff.out.parity.knownDiffs, diff.out.parity.knownDiffsUsed, diff.out.total.lost], [1, 1, 1]);
  const oed = run([results(root, "base2", "oracle_error_same", GO), results(root, "oed", "oracle_error_diff", GO), ...known]);
  assert.equal(oed.out.parity.knownDiffRows[0].goldenError, "panic: runtime error: invalid memory address or nil pointer dereference");
  assert.match(oed.stderr, /known diff qc\/t#1: oracle_error_diff getTypeOfSymbol pointer None; Go golden error: panic: runtime error/);
  // An unused known diff is still printed, with its class in the new run.
  const same = run([base, results(root, "same", "same", GO), ...known]);
  assert.deepEqual([same.out.parity.bad, same.out.parity.knownDiffRows[0].class], [1, "same"]);
}));
