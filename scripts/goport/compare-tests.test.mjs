// Tests of scripts/goport/compare-tests.py: the verdict and the name map rules.
// Run: node --test scripts/goport/compare-tests.test.mjs
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

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
// (arrays of cells). Returns the exit code and the JSON output.
function compare(edit, mapLines) {
  const dir = mkdtempSync(join(tmpdir(), "compare-tests-"));
  try {
    const next = base();
    edit?.(next);
    writeFileSync(join(dir, "base.json"), JSON.stringify(base()));
    writeFileSync(join(dir, "new.json"), JSON.stringify(next));
    const args = [TOOL, join(dir, "base.json"), join(dir, "new.json")];
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
