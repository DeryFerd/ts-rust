import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

// The removal lines of a gate id map (gate-compare.py "Removal check"), against the real Go checkouts of pin B
// (16c25522e123, microsoft/typescript-go) and pin N (673a5f17d713, microsoft/TypeScript tsc/). Skipped when a
// checkout is missing. Bump C reviewer ruling 2 item 3: a removal line fails for a case that the new run still holds,
// a case that is still in the pin N checkout (moved), and a path that is not the base item's.
const COMPARE = fileURLToPath(new URL("./gate-compare.py", import.meta.url));
const B = "16c25522e123", N = "673a5f17d713";
const HOME = process.env.HOME;
const CHECKOUTS = [`${HOME}/.explore/repos/microsoft__typescript-go@16c25522e`, `${HOME}/.explore/repos/microsoft__TypeScript@673a5f17d713/tsc`];
const skip = CHECKOUTS.some(dir => !existsSync(dir)) && "the pin B or pin N Go checkout is missing";
const SUB = "_submodules/TypeScript/tests/cases/compiler";
// The note of a removal line: the Go commit that deletes the case (bump C reviewer ruling 2 item 3).
const NOTE = "deleted by 0e32aa196a (ts#64122)";

// Runs gate-compare.py: base items at pin B, new items at pin N, and the map text in batch.gateIdMap. rc 2 (bad
// input) returns {rc, stderr}.
function compare(baseItems, newItems, mapText) {
  const dir = mkdtempSync(join(tmpdir(), "gate-compare-"));
  try {
    const manifest = (pin, results) => ({ label: pin, upstreamPin: pin, mode: "full", results });
    writeFileSync(join(dir, "base.json"), JSON.stringify(manifest(B, baseItems)));
    writeFileSync(join(dir, "new.json"), JSON.stringify(manifest(N, newItems)));
    writeFileSync(join(dir, "map.tsv"), mapText);
    const sha256 = createHash("sha256").update(mapText).digest("hex");
    writeFileSync(join(dir, "state.json"), JSON.stringify({ batch: { gateIdMap: { path: join(dir, "map.tsv"), sha256 } } }));
    const run = spawnSync("python3", [COMPARE, join(dir, "base.json"), join(dir, "new.json"), "--state", join(dir, "state.json")],
      { encoding: "utf8" });
    if (run.status === 2) return { rc: 2, stderr: run.stderr };
    assert.ok(run.status === 0 || run.status === 1, run.stderr);
    return JSON.parse(run.stdout);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

// A MATCH item; the case path is at its fixed place in the detail of its family.
const item = (id, path) => ({ id, status: "MATCH", detail: id.startsWith("corpus-emit/") ? `MATCH exit 0/0 ${path}` : `MATCH ${path}` });

test("a removal line removes a case that Go removed between the pins", { skip }, () => {
  // ts#64122 deleted this AMD case: it is in the pin B checkout and not in the pin N checkout.
  const gone = `${SUB}/amdDependencyCommentName1.ts`;
  const out = compare([item("corpus-diag/00542", gone)], [], `corpus-diag/00542\t-\t${gone}\t${NOTE}\n`);
  assert.deepEqual(out.regressions, []);
  assert.deepEqual(out.idMap.removed, [{ id: "corpus-diag/00542", path: gone, note: NOTE }]);
  // A removal line needs a note that names the Go commit, and a move line has no note: bad input.
  for (const line of [`corpus-diag/00542\t-\t${gone}\n`, `corpus-diag/00542\t-\t${gone}\tts#64122\n`,
    `corpus-diag/00542\tcorpus-diag/00001\t${gone}\t${NOTE}\n`]) {
    const bad = compare([item("corpus-diag/00542", gone)], [], line);
    assert.equal(bad.rc, 2, line);
    assert.match(bad.stderr, /gate id map line 1: need .* TAB <note naming the Go commit that deletes the case>/);
  }
  // The same line when the new run still holds the case under its new path: a removed id.
  const held = compare([item("corpus-diag/00542", gone)], [item("corpus-diag/00001", "testdata/tests/cases/compiler/amdDependencyCommentName1.ts")],
    `corpus-diag/00542\t-\t${gone}\t${NOTE}\n`);
  assert.deepEqual(held.regressions.map(r => [r.id, r.why]),
    [["corpus-diag/00542", "removed id (id map line 1 removes it, but the new run holds the case: corpus-diag/00001)"]]);
});

test("a removal line cannot remove a case that moved at the new pin", { skip }, () => {
  // A plain move to testdata/tests/cases, and a promoted collision rename (promotedTestCollisions.txt).
  for (const [name, moved] of [["importWithTrailingSlash.ts", "importWithTrailingSlash.ts"],
    ["allowSyntheticDefaultImports9.ts", "allowSyntheticDefaultImports9_promoted.ts"]]) {
    const out = compare([item("corpus-emit/00001", `${SUB}/${name}`)], [], `corpus-emit/00001\t-\t${SUB}/${name}\t${NOTE}\n`);
    assert.deepEqual(out.idMap.broken, ["corpus-emit/00001"]);
    assert.match(out.regressions[0].why, new RegExp(`the new pin Go checkout .* has testdata/tests/cases/compiler/${moved.replace(".", "\\.")}\\)$`));
  }
  // A case path that is not the base item's, and a case that the base pin never had.
  let out = compare([item("corpus-diag/00001", `${SUB}/amdDependencyCommentName1.ts`)], [], `corpus-diag/00001\t-\t${SUB}/x.ts\t${NOTE}\n`);
  assert.match(out.regressions[0].why, /x\.ts is not the case path of corpus-diag\/00001/);
  out = compare([item("corpus-diag/00001", `${SUB}/x.ts`)], [], `corpus-diag/00001\t-\t${SUB}/x.ts\t${NOTE}\n`);
  assert.match(out.regressions[0].why, /x\.ts is not in the base pin Go checkout/);
});

test("a move line pairs a base case with its layout move at a microsoft/TypeScript pin, allow entries too", { skip }, () => {
  const st = "single-threaded-equal", bpath = `${SUB}/importWithTrailingSlash.ts`, npath = "testdata/tests/cases/compiler/importWithTrailingSlash.ts";
  // The base allow list has the pin B entry; the new item is ALLOWED by the pin N entry of the same case.
  const base = [item("corpus-diag/03599", bpath)];
  const allowed = { id: "corpus-diag/03363", status: "ALLOWED", detail: `MISMATCH ${npath}`,
    allowedBy: [{ id: "corpus-diag/03363", path: npath, condition: st }] };
  const dir = mkdtempSync(join(tmpdir(), "gate-compare-"));
  try {
    const mapText = `corpus-diag/03599\tcorpus-diag/03363\t${bpath}\n`;
    writeFileSync(join(dir, "base.json"), JSON.stringify({ upstreamPin: B, results: base,
      allowList: { entries: [{ id: "corpus-diag/03599", path: bpath, condition: st }] } }));
    writeFileSync(join(dir, "new.json"), JSON.stringify({ upstreamPin: N, results: [allowed] }));
    writeFileSync(join(dir, "map.tsv"), mapText);
    const sha256 = createHash("sha256").update(mapText).digest("hex");
    writeFileSync(join(dir, "state.json"), JSON.stringify({ batch: { gateIdMap: { path: join(dir, "map.tsv"), sha256 } } }));
    const run = spawnSync("python3", [COMPARE, join(dir, "base.json"), join(dir, "new.json"), "--state", join(dir, "state.json")], { encoding: "utf8" });
    const out = JSON.parse(run.stdout);
    assert.equal(run.status, 0, run.stderr);
    assert.deepEqual([out.idMap.mapped, out.idMap.broken, out.reallowed.map(r => r.id), out.newAllowEntries], [1, [], ["corpus-diag/03363"], []]);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
  // The same line when the new id is another case: a removed id.
  const other = compare([item("corpus-diag/03599", bpath)], [item("corpus-diag/03363", "testdata/tests/cases/compiler/other.ts")],
    `corpus-diag/03599\tcorpus-diag/03363\t${bpath}\n`);
  assert.deepEqual(other.idMap.broken, ["corpus-diag/03599"]);
  assert.match(other.regressions[0].why, /corpus-diag\/03363 is the case testdata\/tests\/cases\/compiler\/other\.ts, not testdata\/tests\/cases\/compiler\/importWithTrailingSlash\.ts/);
});
