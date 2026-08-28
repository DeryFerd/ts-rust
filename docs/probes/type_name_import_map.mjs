import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";

const rootBase = "4327f7f345c90d59d6057a3f53c4d1c0e81eed9c";
const sourceCommit = "efad1ef7313ae516ffb123a7532c734ba6c128a9";
const sourceLog = process.argv[2] ?? "/tmp/ts-rust-wave148-missing-type-symbol-adapter-tests-retry.log";
const output = process.argv[3] ?? "docs/probes/type_name_author_controls.json";
const log = readFileSync(sourceLog, "utf8");
const logHash = createHash("sha256").update(log).digest("hex");
if (logHash !== "5f9ff1c359549ab7b3d782374e171492b6a7ad05bbb4f16941212e0c7420cadc") {
  throw new Error("The author control log does not match its recorded hash");
}
const names = [...log.matchAll(/^test ([A-Za-z0-9_:]+) \.\.\./gm)].map((match) => match[1]);
if (names.length !== 58 || !log.includes("58 passed; 0 failed; 0 ignored;")) {
  throw new Error("The author log is not the complete passing 58-test run");
}
const git = (args, input) => execFileSync("git", args, { encoding: "utf8", input }).trim();
const pattern = `fn[[:space:]]+(${names.map((name) => name.split("::").at(-1)).join("|")})[[:space:]]*\\(`;
const matches = git(["grep", "-n", "-E", pattern, rootBase, "--", "crates/ts_checker/src"]);
const rootFiles = new Map();
for (const line of matches.split("\n")) {
  const match = line.match(/^[^:]+:(.+):\d+:.*\bfn\s+(\w+)\s*\(/);
  if (match) rootFiles.set(match[2], match[1]);
}
const commits = [
  ["89d86f8064bc68115087383f4089183499d25aba", "Selected symbol key/cache and record checks only"],
  ["14e71e05aa7a37b598146e4a15d8c7df797725ea", "Selected symbol-only allocation and lookup only"],
  [sourceCommit, "Adapter and type-name reader, adapted to root without error-alias types"],
  ["37920d2326a021fa06547b2ec30e12627bfa1177", "Excluded source, formatter, and constraint integration"],
  ["34b12ce79b11a446dc56a3333133dd21fc2ead7c", "Separate root export-equals validation change, not imported"],
].map(([commit, disposition]) => {
  const patch = git(["show", "--format=medium", "--binary", commit]);
  const patchId = git(["patch-id", "--stable"], patch).split(" ")[0];
  const equivalentCheck = git(["cherry", "-v", rootBase, commit, `${commit}^`]);
  return { commit, patchId, disposition, equivalentCheck };
});
const controls = names.map((name) => {
  const rootFile = rootFiles.get(name.split("::").at(-1)) ?? null;
  return {
    name,
    retainedBeforeSymbolAdapter: !name.startsWith("semantic::artifact_queries::"),
    authorCommit: sourceCommit,
    presentByNameOnRootBase: rootFile !== null,
    rootFile,
  };
});
const result = {
  rootBase,
  sourceCommit,
  sourceLogHash: logHash,
  sourcePassed: 58,
  sourceRetainedControls: controls.filter((control) => control.retainedBeforeSymbolAdapter).length,
  rootBaseNames: controls.filter((control) => control.presentByNameOnRootBase).length,
  note: "Name presence is not assertion equivalence. Author-only controls are preserved at the source commit and are not counted as root passes.",
  commits,
  controls,
};
writeFileSync(output, `${JSON.stringify(result, null, 2)}\n`);
console.log(`Recorded ${result.sourcePassed} author controls, ${result.sourceRetainedControls} retained controls, and ${result.rootBaseNames} root test names`);
