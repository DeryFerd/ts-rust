// Tests of scripts/goport/compare-tests.py: the verdict and the name map rules.
// Run: node --test scripts/goport/compare-tests.test.mjs
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { gzipSync } from "node:zlib";

const TOOL = join(dirname(fileURLToPath(import.meta.url)), "compare-tests.py");
const PIN = "52168999f3dc";

const base = () => ({
  source: { commit: "a".repeat(40) },
  pin: PIN,
  suites: {
    ts_goport_lib: { "a::ok": "ok", "a::other": "ok", "a::ignored": "ignored" },
    ts_scanner_lib: { "s::ok": "ok" },
    go_baselines_submodule: { "types submodule/compiler/x.ts": "ok", "types submodule/compiler/y.ts": "ignored" },
  },
  incomplete: [],
});

// Runs the tool on base() and the new results that `edit` makes from base(), with the map lines
// (arrays of cells). gzip writes the base as base.json.gz. Returns the exit code and the JSON output.
function compare(edit, mapLines, { gzip = false } = {}) {
  const dir = mkdtempSync(join(tmpdir(), "compare-tests-"));
  try {
    const next = base();
    edit?.(next);
    const baseFile = join(dir, gzip ? "base.json.gz" : "base.json");
    writeFileSync(baseFile, gzip ? gzipSync(JSON.stringify(base())) : JSON.stringify(base()));
    writeFileSync(join(dir, "new.json"), JSON.stringify(next));
    const args = [TOOL, baseFile, join(dir, "new.json")];
    if (mapLines) {
      writeFileSync(join(dir, "map.tsv"), mapLines.map(cells => cells.join("\t")).join("\n") + "\n");
      args.push("--name-map", join(dir, "map.tsv"));
    }
    const run = spawnSync("python3", args, { encoding: "utf8" });
    return { rc: run.status, out: run.status === 2 ? null : JSON.parse(run.stdout), stderr: run.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const lib = next => next.suites.ts_goport_lib;

test("equal results pass", () => {
  const { rc, out } = compare();
  assert.equal(rc, 0);
  assert.equal(out.total.retained, 4);
});

test("a failed, ignored, unrun or absent base ok name fails", () => {
  for (const status of ["failed", "ignored", "unrun"]) {
    assert.equal(compare(next => { lib(next)["a::ok"] = status; }).rc, 1, status);
  }
  const { rc, out } = compare(next => { delete lib(next)["a::ok"]; });
  assert.equal(rc, 1);
  assert.deepEqual(out.total.absent, ["ts_goport_lib: a::ok"]);
});

test("a real rename passes", () => {
  const { rc, out } = compare(next => { lib(next)["b::ok"] = lib(next)["a::ok"]; delete lib(next)["a::ok"]; },
    [["ts_goport_lib", "a::ok", "ts_goport_lib", "b::ok", "moved"]]);
  assert.equal(rc, 0);
  assert.deepEqual(out.mapRejected, []);
  assert.equal(out.total.retained, 4);
});

test("a map line whose old name is still in the new results fails", () => {
  // A removal (at a pin change) and a rename that would hide the failed old name.
  const removed = compare(next => { next.pin = "16c25522e"; lib(next)["a::ok"] = "failed"; },
    [["ts_goport_lib", "a::ok", "-", "-", "Go removed it"]]);
  assert.equal(removed.rc, 1);
  assert.match(removed.out.mapRejected[0], /a::ok is still in the new results/);
  const renamed = compare(next => { lib(next)["a::ok"] = "failed"; lib(next)["fresh::ok"] = "ok"; },
    [["ts_goport_lib", "a::ok", "ts_goport_lib", "fresh::ok", "renamed"]]);
  assert.equal(renamed.rc, 1);
});

test("a removal line of a name that is ignored in the new results passes on its own count (bump C ruling 1 item 5)", () => {
  // A stale Go reference file: ok at the base pin, still in the Go tree at the new pin, but no Go test writes it.
  const line = [["ts_goport_lib", "a::ok", "-", "-", "Go test removed, baseline file left behind"]];
  const stale = compare(next => { next.pin = "16c25522e"; lib(next)["a::ok"] = "ignored"; }, line);
  assert.equal(stale.rc, 0);
  assert.deepEqual([stale.out.mapRejected, stale.out.mapRemovedIgnored, stale.out.total.removedByMap], [[], ["ts_goport_lib: a::ok"], 1]);
  // Still rejected when the name is ok or failed in the new results.
  for (const status of ["ok", "failed"]) {
    const kept = compare(next => { next.pin = "16c25522e"; lib(next)["a::ok"] = status; }, line);
    assert.equal(kept.rc, 1);
    assert.deepEqual(kept.out.mapRemovedIgnored, []);
    assert.match(kept.out.mapRejected[0], /a::ok is still in the new results/);
  }
  // A move (not a removal) of an ignored name is still rejected.
  const moved = compare(next => { lib(next)["a::ok"] = "ignored"; lib(next)["fresh::ok"] = "ok"; },
    [["ts_goport_lib", "a::ok", "ts_goport_lib", "fresh::ok", "renamed"]]);
  assert.equal(moved.rc, 1);
});

test("a swap with a base name fails", () => {
  const { rc, out } = compare(next => {
    const sub = next.suites.go_baselines_submodule;
    sub["types submodule/compiler/x.ts"] = "failed";
    sub["types submodule/compiler/y.ts"] = "ok";
  }, [
    ["go_baselines_submodule", "types submodule/compiler/x.ts", "go_baselines_submodule", "types submodule/compiler/y.ts", "e"],
    ["go_baselines_submodule", "types submodule/compiler/y.ts", "go_baselines_submodule", "types submodule/compiler/x.ts", "e"],
  ]);
  assert.equal(rc, 1);
  assert.equal(out.total.lost.length, 0);
  assert.ok(out.mapRejected.some(r => /is a base name/.test(r)));
});

test("a removal needs a pin change or a kept-crate suite", () => {
  const goport = next => { delete lib(next)["a::ok"]; };
  const line = [["ts_goport_lib", "a::ok", "-", "-", "deleted"]];
  assert.equal(compare(goport, line).rc, 1);
  assert.equal(compare(next => { goport(next); next.pin = "16c25522e"; }, line).rc, 0);
  const kept = compare(next => { delete next.suites.ts_scanner_lib["s::ok"]; },
    [["ts_scanner_lib", "s::ok", "-", "-", "stage 5 replaces ts_scanner"]]);
  assert.equal(kept.rc, 0);
  assert.equal(kept.out.total.removedByMap, 1);
});

test("an identity line is not rejected, and a line without evidence is bad input", () => {
  assert.equal(compare(undefined, [["ts_goport_lib", "a::ok", "ts_goport_lib", "a::ok", "same"]]).rc, 0);
  assert.equal(compare(undefined, [["ts_goport_lib", "a::ok", "ts_goport_lib", "a::ok"]]).rc, 2);
});

test("a pin that is not 7 to 64 hex characters is bad input", () => {
  // A spoofed or missing pin must not count as a pin change that allows a removal.
  const line = [["ts_goport_lib", "a::ok", "-", "-", "deleted"]];
  for (const pin of [`v${PIN}`, "abc123", "g".repeat(12), "a".repeat(65), `${PIN}\n`, "", null, 7]) {
    const run = compare(next => { next.pin = pin; delete lib(next)["a::ok"]; }, line);
    assert.equal(run.rc, 2, JSON.stringify(pin));
    assert.match(run.stderr, /"pin" must be 7 to 64 hex characters/);
  }
  assert.equal(compare(next => { delete next.pin; }).rc, 2);
  assert.equal(compare(next => { next.pin = PIN.toUpperCase(); }).rc, 0);
});

test("a .json.gz base reads as its JSON, and its sha256 is the file's", () => {
  const { rc, out } = compare(next => { lib(next)["a::ok"] = "failed"; }, undefined, { gzip: true });
  assert.equal(rc, 1);
  assert.deepEqual(out.total.lost, ["ts_goport_lib: a::ok"]);
  assert.match(out.base.path, /base\.json\.gz$/);
  assert.equal(out.base.sha256, createHash("sha256").update(gzipSync(JSON.stringify(base()))).digest("hex"));
  assert.equal(compare(undefined, undefined, { gzip: true }).rc, 0);
});
