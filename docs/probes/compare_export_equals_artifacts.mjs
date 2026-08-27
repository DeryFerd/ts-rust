import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";

const directory = resolve(process.argv[2] ?? "target/review");
const go = JSON.parse(readFileSync(resolve(directory, "go-observations.json"), "utf8"));
const rust = JSON.parse(readFileSync(resolve(directory, "rust-observations.json"), "utf8"));
assert.equal(go.length, rust.length);
const byName = new Map(rust.map((row) => [row.name, row]));
const comparisons = go.map((expected) => {
  const actual = byName.get(expected.name);
  assert.ok(actual, `missing Rust observation for ${expected.name}`);
  const got = actual.export;
  const unavailable = actual.sourceError ?? got?.typeError ?? got?.type?.Err;
  if (unavailable) {
    return { name: expected.name, status: "unsupported", reason: unavailable };
  }
  assert.equal(actual.checked, true);
  assert.equal(actual.warmStable, true);
  const expectedKinds = expected.export.declarations.map((kind) => kind.replace(/^Kind/, ""));
  const sameType = got.type.Ok === expected.export.type;
  const sameSymbol = got.symbol.Ok === expected.export.symbol;
  const sameDeclarations = JSON.stringify(got.declarations) === JSON.stringify(expectedKinds);
  return {
    name: expected.name,
    status: sameType && sameSymbol && sameDeclarations ? "exact_query_match" : "mismatch",
    goType: expected.export.type,
    rustType: got.type.Ok,
    sameSymbol,
    sameDeclarations,
    goReadType: expected.read?.type ?? null,
    rustReadType: actual.read?.type?.Ok ?? null,
  };
});
console.log(JSON.stringify(comparisons, null, 2));
process.exitCode = comparisons.some((row) => row.status === "mismatch") ? 1 : 0;
