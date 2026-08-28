import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync, writeFileSync } from "node:fs";
import { basename, dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { parseArgs } from "node:util";

const { values } = parseArgs({
  options: {
    logs: { type: "string" },
    output: { type: "string" },
  },
});
assert(values.logs, "Pass --logs with the directory containing the three saved logs");
const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const reportPath = resolve(root, "docs/typechecker-wave152-root-workspace.json");
const markdownPath = resolve(root, "docs/typechecker-wave152-root-workspace.md");
const reportBytes = readFileSync(reportPath);
const report = JSON.parse(reportBytes.toString("utf8"));
const markdown = readFileSync(markdownPath, "utf8");
const digest = (bytes) => createHash("sha256").update(bytes).digest("hex");
assert.equal(digest(reportBytes), "a58e41e250c39874371deff5d087050b2a619ecea26f02e8a0a5ce1548e58865");

function parseLog(path) {
  const bytes = readFileSync(path);
  const sections = [];
  const names = new Map();
  let active;
  for (const [index, raw] of bytes.toString("utf8").split(/\r?\n/).entries()) {
    const line = raw.replace(/\u001b\[[0-9;]*m/g, "");
    const binary = line.match(/^\s+Running (.+) \((.+)\)$/);
    const doc = line.match(/^\s+Doc-tests (\S+)$/);
    if (binary || doc) {
      assert(!active || active.summary, `${path}:${index + 1}: unfinished previous section`);
      const binaryName = binary && basename(binary[2]).match(/^(.+)-[a-f0-9]{16}$/);
      assert(!binary || binaryName, `${path}:${index + 1}: unrecognized binary name`);
      active = {
        name: doc ? `doc:${doc[1]}` : binaryName[1],
        kind: doc ? "doc" : "binary",
        executable: binary?.[2],
        announced: undefined,
        observed: { passed: 0, failed: 0, ignored: 0 },
        rows: [],
        summary: undefined,
      };
      sections.push(active);
      continue;
    }
    const announced = line.match(/^running (\d+) tests?$/);
    if (announced) {
      assert(active && active.announced === undefined && !active.summary);
      active.announced = Number(announced[1]);
      continue;
    }
    const summary = line.match(/^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; (\d+) measured; (\d+) filtered out; finished in .+$/);
    if (summary) {
      assert(active && active.announced !== undefined && !active.summary);
      const [, result, passed, failed, ignored, measured, filtered] = summary;
      active.summary = {
        result,
        passed: Number(passed),
        failed: Number(failed),
        ignored: Number(ignored),
        measured: Number(measured),
        filtered: Number(filtered),
      };
      assert.equal(active.summary.measured, 0, "This audit does not accept unparsed benchmark results");
      for (const status of ["passed", "failed", "ignored"]) {
        assert.equal(active.observed[status], active.summary[status], `${path}: ${active.name} ${status}`);
      }
      assert.equal(active.rows.length, active.announced, `${path}: ${active.name} announced count`);
      assert.equal(active.rows.length, active.summary.passed + active.summary.failed + active.summary.ignored);
      continue;
    }
    if (line.startsWith("test ")) {
      const named = line.match(/^test (.+) \.\.\. (ok|FAILED|ignored)(?:, .*)?$/);
      assert(named, `${path}:${index + 1}: unrecognized test result`);
      assert(active && active.announced !== undefined && !active.summary);
      const status = { ok: "passed", FAILED: "failed", ignored: "ignored" }[named[2]];
      const name = `${active.name}::${named[1]}`;
      assert(!names.has(name), `${path}:${index + 1}: duplicate qualified test name ${name}`);
      names.set(name, status);
      active.observed[status]++;
      active.rows.push(name);
    }
  }
  assert(active?.summary, `${path}: no completed final section`);
  const totals = { passed: 0, failed: 0, ignored: 0, measured: 0, filtered: 0 };
  for (const section of sections) {
    for (const key of Object.keys(totals)) totals[key] += section.summary[key];
  }
  const binaries = sections.filter((section) => section.kind === "binary");
  assert.equal(new Set(binaries.map((section) => section.executable)).size, binaries.length);
  return { path, sha256: digest(bytes), sections, names, totals };
}

const logPath = resolve(values.logs, basename(report.path));
const current = parseLog(logPath);
assert.equal(current.sha256, report.sha256);
assert.deepEqual(current.totals, report.totals);
assert.equal(current.names.size, report.namedTests);
assert.equal(current.sections.filter((section) => section.kind === "binary").length, report.binaries);
assert.equal(current.sections.filter((section) => section.kind === "doc").length, report.docGroups);
assert.deepEqual(current.sections.map((section) => ({
  name: section.name,
  tests: section.announced,
  kind: section.kind,
  ...section.summary,
})), report.sections);
for (const [field, status] of [["failed", "failed"], ["ignored", "ignored"]]) {
  assert.deepEqual([...current.names].filter(([, actual]) => actual === status).map(([name]) => name).sort(), report[field].toSorted());
}

const comparisons = report.comparisons.map((claimed) => {
  const previous = parseLog(resolve(values.logs, basename(claimed.path)));
  assert.equal(previous.sha256, claimed.sha256);
  const retained = [...previous.names.keys()].filter((name) => current.names.has(name));
  const missing = [...previous.names.keys()].filter((name) => !current.names.has(name)).sort();
  assert.equal(previous.names.size, claimed.priorNames);
  assert.equal(retained.length, claimed.retainedNames);
  assert.deepEqual(missing, claimed.missingNames.toSorted());
  const replacements = new Map(claimed.replacements.map((item) => [item.from, item.to]));
  assert.equal(replacements.size, claimed.replacements.length);
  assert.equal(new Set(replacements.values()).size, replacements.size, "Replacement targets must be distinct");
  assert.deepEqual([...replacements.keys()].sort(), missing);
  for (const name of retained) assert.equal(current.names.get(name), "passed", name);
  for (const [from, to] of replacements) {
    assert(previous.names.has(from));
    assert(!previous.names.has(to), `Replacement already existed in the prior run: ${to}`);
    assert.equal(current.names.get(to), "passed", to);
  }
  const unaccounted = missing.filter((name) => !replacements.has(name));
  assert.deepEqual(unaccounted, claimed.unaccountedMissingNames);
  assert.equal(retained.length + replacements.size, claimed.accountedNames);
  return {
    path: previous.path,
    sha256: previous.sha256,
    totals: previous.totals,
    priorFailedNames: [...previous.names].filter(([, status]) => status === "failed").map(([name]) => name),
    priorNames: previous.names.size,
    retainedPassingNames: retained.length,
    missingNames: missing,
    passingReplacements: [...replacements].map(([from, to]) => ({ from, to })),
    unaccountedMissingNames: unaccounted,
    newNames: [...current.names.keys()].filter((name) => !previous.names.has(name)).length,
  };
});

function git(...args) {
  return execFileSync("git", ["-C", root, ...args], { encoding: "utf8", maxBuffer: 32 * 1024 * 1024 });
}

const sourceCommit = markdown.match(/^Tested source: `([a-f0-9]{40})`\.$/m)?.[1];
const sourceTree = markdown.match(/^Source tree: `([a-f0-9]{40})`\.$/m)?.[1];
assert.equal(sourceCommit, "ebe995e1cd7c342ebb7c89fc8ca66600f7ef9715");
assert.equal(git("rev-parse", `${sourceCommit}^{tree}`).trim(), sourceTree);
assert.equal(git("rev-parse", "5b23c2d3^").trim(), sourceCommit);
const sourceLocations = [
  ["source_class_second_wave", "crates/ts_checker/tests/source_class_second_wave.rs", "91c16a21"],
  ["ts_binder", "crates/ts_binder/src/lib.rs", "91c16a21"],
  ["ts_checker", "crates/ts_checker/src/semantic/source.rs", "91c16a21"],
  ["ts_compiler", "crates/ts_compiler/src/lib.rs", "91c16a21"],
  ["ts_fixture", "tools/ts_fixture/src/artifacts/mod.rs", "3ae315e8"],
];
const definitions = comparisons[0].passingReplacements.map(({ from, to }) => {
  const [prefix, path, oldRef] = sourceLocations.find(([prefix]) => from.startsWith(`${prefix}::`));
  assert(to.startsWith(`${prefix}::`));
  const oldCommit = git("rev-parse", `${oldRef}^{commit}`).trim();
  function definition(commit, name) {
    const source = git("show", `${commit}:${path}`);
    const pattern = new RegExp(`^\\s*fn ${name.split("::").at(-1)}\\(`);
    const lines = source.split("\n").flatMap((line, index) => pattern.test(line) ? [index + 1] : []);
    assert.equal(lines.length, 1, `${commit}:${path}: ${name}`);
    return { commit, path, line: lines[0], fileSha256: digest(source) };
  }
  return { from, to, before: definition(oldCommit, from), after: definition(sourceCommit, to) };
});
const supportingPassingTests = [
  "source_class_bodies::static_super_read_does_not_share_a_named_assignment_flow_reference",
  "ts_checker::semantic::source::tests::javascript_class_expandos_do_not_hide_poisoned_static_field_caches",
  "ts_compiler::tests::canonical_program_rejects_a_later_unsupported_construction_without_fallback",
  "ts_fixture::artifacts::tests::semantic_artifact_rendering_keeps_foreign_nodes_fatal_after_warm_queries",
  ...comparisons[0].priorFailedNames,
];
for (const name of supportingPassingTests) assert.equal(current.names.get(name), "passed", name);

const invariantPath = "crates/ts_checker/src/semantic/artifact_queries/export_equals_final_invariant_tests.rs";
const invariantPrefix = (commit) => git("show", `${commit}:${invariantPath}`).split("\n").slice(0, 991).join("\n") + "\n";
assert.equal(invariantPrefix("34b12ce7"), invariantPrefix(sourceCommit));
const preservedInvariantPrefix = {
  path: invariantPath,
  throughLine: 991,
  earlierCommit: git("rev-parse", "34b12ce7^{commit}").trim(),
  sha256: digest(invariantPrefix(sourceCommit)),
};

const classPaths = git("diff", "--name-only", "0efdd881", "e07fc2f8").trim().split("\n");
assert.equal(classPaths.length, 37);
const classBlobs = git("rev-parse", ...classPaths.flatMap((path) => [`e07fc2f8:${path}`, `33081c24:${path}`])).trim().split("\n");
const sharedDifferences = classPaths.filter((_, index) => classBlobs[index * 2] !== classBlobs[index * 2 + 1]);
assert.deepEqual(sharedDifferences, [
  "crates/ts_checker/src/semantic/callable_sets.rs",
  "crates/ts_checker/src/semantic/store.rs",
]);
function patchId(base, head, paths = []) {
  return execFileSync("git", ["-C", root, "patch-id", "--stable"], {
    input: git("diff", "--unified=0", base, head, "--", ...paths),
    encoding: "utf8",
    maxBuffer: 32 * 1024 * 1024,
  }).split(" ")[0];
}
const classPatchId = patchId("0efdd881", "e07fc2f8");
assert.equal(classPatchId, "182b307679de22c1bc8019eb38115a3bb6b13352");
assert.equal(patchId("91c16a21", "33081c24"), classPatchId);
assert(markdown.includes(classPatchId));
const retainedRootPatchId = patchId("0efdd881", "91c16a21", sharedDifferences);
assert.equal(retainedRootPatchId, "4a17f65597697790428600406f071b104541e1ac");
assert.equal(patchId("e07fc2f8", "33081c24", sharedDifferences), retainedRootPatchId);
const formatPath = resolve(values.logs, "wave152-root-workspace-format.log");
const formatBytes = readFileSync(formatPath);
assert.equal(formatBytes.length, 0);
for (const hash of [current.sha256, digest(formatBytes), digest(reportBytes)]) {
  assert(markdown.includes(hash), `Markdown omits recorded hash ${hash}`);
}
assert(markdown.includes(`All ${current.names.size.toLocaleString("en-US")} workspace tests pass.`));
assert(markdown.includes(`All ${report.binaries} test binaries and ${report.docGroups} documentation groups`));

const result = {
  sourceCommit,
  sourceTree,
  reportCommit: git("rev-parse", "5b23c2d3^{commit}").trim(),
  log: { path: current.path, sha256: current.sha256 },
  reportSha256: digest(reportBytes),
  totals: current.totals,
  namedTests: current.names.size,
  binaries: report.binaries,
  docGroups: report.docGroups,
  binaryTests: current.sections.filter((section) => section.kind === "binary").reduce((sum, section) => sum + section.rows.length, 0),
  documentationTests: current.sections.filter((section) => section.kind === "doc").flatMap((section) => section.rows),
  matchedSections: current.sections.length,
  duplicateQualifiedNames: [],
  comparisons,
  replacementDefinitions: definitions,
  supportingPassingTests,
  preservedInvariantPrefix,
  classImport: {
    sourceBase: git("rev-parse", "0efdd881^{commit}").trim(),
    sourceHead: git("rev-parse", "e07fc2f8^{commit}").trim(),
    rootImport: git("rev-parse", "33081c24^{commit}").trim(),
    paths: classPaths.length,
    identicalFiles: classPaths.length - sharedDifferences.length,
    sharedDifferences,
    zeroContextPatchId: classPatchId,
    retainedRootPatchId,
  },
  formatLog: { path: formatPath, bytes: formatBytes.length, sha256: digest(formatBytes) },
  productionApproval: false,
};
const text = `${JSON.stringify(result, null, 2)}\n`;
if (values.output) {
  const output = resolve(values.output);
  const protectedPaths = [reportPath, markdownPath, logPath, formatPath, ...comparisons.map((item) => item.path)];
  assert(!protectedPaths.includes(output), "Do not overwrite the saved evidence");
  writeFileSync(output, text);
}
console.log(text.trimEnd());
