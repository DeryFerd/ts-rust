// Tests of scripts/goport/layout-name-map.py: the old-name map from a typescript-go layout run to a tsc/
// layout run, checked with compare-tests.py.
// Run: node --test scripts/goport/layout-name-map.test.mjs
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const TOOL = join(HERE, "layout-name-map.py");
const COMPARE = join(HERE, "compare-tests.py");
// Pins of UPSTREAM.json: layout typescript-go and layout typescript.
const OLD_PIN = "16c25522e123";
const NEW_PIN = "673a5f17d713";
const COLLISIONS = [
  "# test",
  "identical compiler/dup.ts",
  "renamed-promoted compiler/ren.ts -> compiler/ren_promoted.ts",
  "",
].join("\n");

const shards = (name) => Object.fromEntries([0, 1, 2, 3].map((i) => [`compiler_runner::${name} ${i}/4`, "ok"]));

const base = () => ({
  source: { commit: "a".repeat(40) },
  pin: OLD_PIN,
  suites: {
    go_baselines: {
      "compiler_runner::test_local": "ok",
      "compiler_runner::test_submodule": "ignored",
      "support::x": "ok",
    },
    go_baselines_local: { "types local/compiler/dup.ts": "ok", "types local/compiler/ren.ts": "ok" },
    go_baselines_submodule: {
      "types submodule/compiler/a.ts": "ok",
      "types submodule/compiler/dup.ts": "ok",
      "types submodule/compiler/ren(target=es5).ts": "ok",
      "error submodule/compiler/gone.ts": "ok",
    },
    go_baselines_submodule_shards: shards("test_submodule"),
    go_baselines_transpile: { "js submodule/transpile/t.ts": "ok" },
    go_baselines_reference: {
      "compiler/dup.types": "ok",
      "compiler/ren.types": "ok",
      "submodule/compiler/a.types": "ok",
      "submodule/compiler/a.types.diff": "ok",
      "submoduleAccepted/compiler/b.types.diff": "ok",
      "submodule/compiler/dup.types": "ok",
      "submodule/compiler/ren(target=es5).types": "ok",
      "tsc/x.js": "ok",
    },
  },
  incomplete: [],
});

const next = () => ({
  source: { commit: "b".repeat(40) },
  pin: NEW_PIN,
  suites: {
    go_baselines: { "compiler_runner::test_submodule": "ignored", "support::x": "ok" },
    go_baselines_local: {
      "types local/compiler/a.ts": "ok",
      "types local/compiler/dup.ts": "ok",
      "types local/compiler/ren.ts": "ok",
      "types local/compiler/ren_promoted(target=es5).ts": "ok",
    },
    go_baselines_local_shards: shards("test_local"),
    go_baselines_transpile: { "js local/transpile/t.ts": "ok" },
    go_baselines_reference: {
      "compiler/a.types": "ok",
      "compiler/dup.types": "ok",
      "compiler/ren.types": "ok",
      "compiler/ren_promoted(target=es5).types": "ok",
      "tsc/x.js": "ok",
    },
  },
  incomplete: [],
});

// Writes the two results, runs the map tool, then compare-tests.py with its map.
function run({ edit, flags = [] } = {}) {
  const dir = mkdtempSync(join(tmpdir(), "layout-name-map-"));
  try {
    const b = base();
    edit?.(b);
    writeFileSync(join(dir, "base.json"), JSON.stringify(b));
    writeFileSync(join(dir, "new.json"), JSON.stringify(next()));
    writeFileSync(join(dir, "collisions.txt"), COLLISIONS);
    const map = spawnSync("python3", [TOOL, join(dir, "base.json"), join(dir, "new.json"),
      "--out", join(dir, "map.tsv"), "--absent", join(dir, "absent.tsv"),
      "--collisions", join(dir, "collisions.txt"), ...flags], { encoding: "utf8" });
    if (map.status !== 0) return { rc: map.status, stderr: map.stderr };
    const lines = readFileSync(join(dir, "map.tsv"), "utf8").split("\n").filter((l) => l && !l.startsWith("#"))
      .slice(1).map((l) => l.split("\t"));
    const absent = readFileSync(join(dir, "absent.tsv"), "utf8").trim().split("\n").slice(1).map((l) => l.split("\t"));
    const cmp = spawnSync("python3", [COMPARE, join(dir, "base.json"), join(dir, "new.json"),
      "--name-map", join(dir, "map.tsv")], { encoding: "utf8" });
    const out = JSON.parse(cmp.stdout);
    assert.deepEqual(out.mapUnused, []);
    return { rc: 0, lines, absent, compare: { rc: cmp.status, out } };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const target = (lines, suite, name) => {
  const line = lines.find((l) => l[0] === suite && l[1] === name);
  return line && [line[2], line[3]];
};

test("the layout rules move and remove names", () => {
  const { rc, lines } = run();
  assert.equal(rc, 0);
  assert.deepEqual(target(lines, "go_baselines_submodule", "types submodule/compiler/a.ts"),
    ["go_baselines_local", "types local/compiler/a.ts"]);
  assert.deepEqual(target(lines, "go_baselines_submodule", "types submodule/compiler/dup.ts"), ["-", "-"]);
  assert.deepEqual(target(lines, "go_baselines_submodule", "types submodule/compiler/ren(target=es5).ts"),
    ["go_baselines_local", "types local/compiler/ren_promoted(target=es5).ts"]);
  assert.deepEqual(target(lines, "go_baselines_submodule_shards", "compiler_runner::test_submodule 2/4"),
    ["go_baselines_local_shards", "compiler_runner::test_local 2/4"]);
  assert.deepEqual(target(lines, "go_baselines", "compiler_runner::test_local"), ["-", "-"]);
  assert.deepEqual(target(lines, "go_baselines_transpile", "js submodule/transpile/t.ts"),
    ["go_baselines_transpile", "js local/transpile/t.ts"]);
  assert.deepEqual(target(lines, "go_baselines_reference", "submodule/compiler/a.types"),
    ["go_baselines_reference", "compiler/a.types"]);
  assert.deepEqual(target(lines, "go_baselines_reference", "submodule/compiler/a.types.diff"), ["-", "-"]);
  assert.deepEqual(target(lines, "go_baselines_reference", "submoduleAccepted/compiler/b.types.diff"), ["-", "-"]);
  assert.deepEqual(target(lines, "go_baselines_reference", "submodule/compiler/dup.types"), ["-", "-"]);
  assert.deepEqual(target(lines, "go_baselines_reference", "submodule/compiler/ren(target=es5).types"),
    ["go_baselines_reference", "compiler/ren_promoted(target=es5).types"]);
  // Names that keep their key have no line.
  assert.equal(target(lines, "go_baselines_local", "types local/compiler/ren.ts"), undefined);
  assert.equal(target(lines, "go_baselines_reference", "tsc/x.js"), undefined);
  assert.ok(lines.every((l) => l.length === 5 && l[4].length > 0));
});

test("a mapped name missing from the new run is absent, with a reason", () => {
  const { lines, absent, compare } = run();
  assert.equal(compare.rc, 1);
  assert.deepEqual(compare.out.total.absent,
    ["go_baselines_submodule: error submodule/compiler/gone.ts -> go_baselines_local: error local/compiler/gone.ts"]);
  assert.deepEqual(compare.out.total.lost, []);
  assert.deepEqual(compare.out.total.unrun, []);
  assert.deepEqual(compare.out.mapRejected, []);
  assert.equal(absent.length, 1);
  assert.deepEqual(absent[0].slice(0, 3), ["go_baselines_submodule", "error submodule/compiler/gone.ts", "ok"]);
  assert.match(absent[0][5], /no case file compiler\/\*\*\/gone\.ts at 673a5f17d713/);
  assert.deepEqual(target(lines, "go_baselines_submodule", "error submodule/compiler/gone.ts"),
    ["go_baselines_local", "error local/compiler/gone.ts"]);
});

test("--remove-absent removes them with the reason as evidence, and the compare passes", () => {
  const { lines, compare } = run({ flags: ["--remove-absent"] });
  const line = lines.find((l) => l[1] === "error submodule/compiler/gone.ts");
  assert.deepEqual(line.slice(2, 4), ["-", "-"]);
  assert.match(line[4], /removed upstream: no case file/);
  assert.equal(compare.rc, 0);
  assert.equal(compare.out.verdict, "PASS");
  // dup (subtest and reference), test_local, the two .diff files and gone.
  assert.equal(compare.out.total.removedByMap, 6);
});

test("a submodule reference that would land on a base name stops the tool", () => {
  const { rc, stderr } = run({
    edit: (b) => {
      b.suites.go_baselines_reference["compiler/c.types"] = "ok";
      b.suites.go_baselines_reference["submodule/compiler/c.types"] = "ok";
    },
  });
  assert.equal(rc, 2);
  assert.match(stderr, /maps to go_baselines_reference compiler\/c\.types, which is a base name/);
});

test("the base must be a typescript-go pin and the new one a typescript pin", () => {
  const { rc, stderr } = run({ edit: (b) => { b.pin = NEW_PIN; } });
  assert.equal(rc, 2);
  assert.match(stderr, /want typescript-go and typescript/);
});
