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
// checkout is missing.
const COMPARE = fileURLToPath(new URL("./gate-compare.py", import.meta.url));
const B = "16c25522e123", N = "673a5f17d713";
const HOME = process.env.HOME;
const CHECKOUTS = [`${HOME}/.explore/repos/microsoft__typescript-go@16c25522e`, `${HOME}/.explore/repos/microsoft__TypeScript@673a5f17d713/tsc`];
const skip = CHECKOUTS.some(dir => !existsSync(dir)) && "the pin B or pin N Go checkout is missing";
const SUB = "_submodules/TypeScript/tests/cases/compiler";

// Runs gate-compare.py: base items at pin B, new items at pin N, and the map text in batch.gateIdMap.
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
  const out = compare([item("corpus-diag/00542", gone)], [], `corpus-diag/00542\t-\t${gone}\n`);
  assert.deepEqual(out.regressions, []);
  assert.deepEqual(out.idMap.removed, [{ id: "corpus-diag/00542", path: gone }]);
  // The same line when the new run still holds the case under its new path: a removed id.
  const held = compare([item("corpus-diag/00542", gone)], [item("corpus-diag/00001", "testdata/tests/cases/compiler/amdDependencyCommentName1.ts")],
    `corpus-diag/00542\t-\t${gone}\n`);
  assert.deepEqual(held.regressions.map(r => [r.id, r.why]),
    [["corpus-diag/00542", "removed id (id map line 1 removes it, but the new run holds the case: corpus-diag/00001)"]]);
});

test("a removal line cannot remove a case that moved at the new pin", { skip }, () => {
  // A plain move to testdata/tests/cases, and a promoted collision rename (promotedTestCollisions.txt).
  for (const [name, moved] of [["importWithTrailingSlash.ts", "importWithTrailingSlash.ts"],
    ["allowSyntheticDefaultImports9.ts", "allowSyntheticDefaultImports9_promoted.ts"]]) {
    const out = compare([item("corpus-emit/00001", `${SUB}/${name}`)], [], `corpus-emit/00001\t-\t${SUB}/${name}\n`);
    assert.deepEqual(out.idMap.broken, ["corpus-emit/00001"]);
    assert.match(out.regressions[0].why, new RegExp(`the new pin Go checkout .* has testdata/tests/cases/compiler/${moved.replace(".", "\\.")}\\)$`));
  }
  // A case path that is not the base item's, and a case that the base pin never had.
  let out = compare([item("corpus-diag/00001", `${SUB}/amdDependencyCommentName1.ts`)], [], `corpus-diag/00001\t-\t${SUB}/x.ts\n`);
  assert.match(out.regressions[0].why, /x\.ts is not the case path of corpus-diag\/00001/);
  out = compare([item("corpus-diag/00001", `${SUB}/x.ts`)], [], `corpus-diag/00001\t-\t${SUB}/x.ts\n`);
  assert.match(out.regressions[0].why, /x\.ts is not in the base pin Go checkout/);
});
