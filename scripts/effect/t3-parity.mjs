#!/usr/bin/env node
// Effect diagnostic parity on a T3 Code checkout. For each TypeScript
// workspace it runs, with the workspace as cwd:
//   ours:   <ours> --noEmit --pretty false                 (one Rust pass)
//   ref:    <ref>  --noEmit --pretty false                 (Effect-patched TypeScript)
//   cli:    node <effect-tsgo.cjs> diagnostics --project tsconfig.json --strict --format text
// Effect lines (TS377xxx) of ours and ref must be identical. The cli output
// (the separate Effect pass) is compared after normalizing its format
// ("message" is a suggestion). Ordinary TS lines of ours and ref are compared
// and reported separately. Counts are per workspace, not deduplicated.
//
// usage: node scripts/effect/t3-parity.mjs --t3 DIR --ours BIN --ref BIN [--out DIR] [--only a,b]
import { execFile } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { parseArgs, promisify } from "node:util";

const run = promisify(execFile);
const { values: args } = parseArgs({
  options: {
    t3: { type: "string" },
    ours: { type: "string" },
    ref: { type: "string" },
    out: { type: "string", default: "/tmp/effect-t3-parity" },
    only: { type: "string", default: "" },
  },
});
const WORKSPACES = [
  "apps/desktop", "apps/mobile", "apps/server", "apps/web", "infra/relay", "oxlint-plugin-t3code",
  "packages/client-runtime", "packages/contracts", "packages/effect-acp", "packages/effect-codex-app-server",
  "packages/shared", "packages/ssh", "packages/tailscale", "scripts",
];

async function exec(bin, argv, cwd) {
  const started = performance.now();
  try {
    const { stdout } = await run(bin, argv, { cwd, maxBuffer: 1 << 28 });
    return { code: 0, out: stdout, ms: performance.now() - started };
  } catch (e) {
    if (typeof e.code !== "number") throw e;
    return { code: e.code, out: e.stdout ?? "", ms: performance.now() - started };
  }
}

// `file(line,col): category TScode: message` plus indented continuation lines.
function parseTsc(out) {
  const diags = [];
  for (const line of out.split("\n")) {
    if (/^\s+\S/.test(line) && diags.length) {
      diags[diags.length - 1].text += "\n" + line;
      continue;
    }
    const m = /^(.*?)\((\d+),(\d+)\): (error|warning|suggestion|message) TS(\d+): (.*)$/.exec(line);
    if (m) diags.push({ file: m[1], line: +m[2], col: +m[3], category: m[4], code: +m[5], text: line, message: m[6] });
    else if (/^(error|warning|suggestion|message) TS\d+:/.test(line)) diags.push({ file: "", line: 0, col: 0, category: line.split(" ")[0], code: +/TS(\d+)/.exec(line)[1], text: line, message: line });
  }
  return diags;
}

// effect-tsgo text format: `file(line,col): severity name: message`.
function parseCli(out, cwd) {
  const diags = [];
  for (const line of out.split("\n")) {
    const m = /^(.*?)\((\d+),(\d+)\): (error|warning|message) ([\w()]+): (.*)$/.exec(line);
    if (m) {
      diags.push({ file: path.relative(cwd, m[1]), line: +m[2], col: +m[3], category: m[4], rule: m[5], message: m[6] });
    } else if (diags.length && line && !/^(Checked|\d+ errors|Skipped)/.test(line)) {
      diags[diags.length - 1].message += "\n" + line;
    }
  }
  return diags;
}

const ruleOf = (message) => /effect\((\w+)\)\s*$/.exec(message.split("\n")[0])?.[1] ?? "?";
const stripRule = (message) => message.replace(/ effect\(\w+\)$/m, "");
const keyTsc = (d) => `${d.file}(${d.line},${d.col}) ${d.category === "suggestion" ? "message" : d.category} ${ruleOf(d.message)}: ${stripRule(d.message)}`;
const keyCli = (d) => `${d.file}(${d.line},${d.col}) ${d.category} ${d.rule.replace(/^effect\((\w+)\)$/, "$1")}: ${d.message}`;

function compare(a, b) {
  const sa = new Map();
  for (const k of a) sa.set(k, (sa.get(k) ?? 0) + 1);
  for (const k of b) sa.set(k, (sa.get(k) ?? 0) - 1);
  const onlyA = [], onlyB = [];
  for (const [k, n] of sa) {
    for (let i = 0; i < n; i++) onlyA.push(k);
    for (let i = 0; i < -n; i++) onlyB.push(k);
  }
  return { onlyA, onlyB };
}

fs.mkdirSync(args.out, { recursive: true });
const cliScript = path.join(args.t3, "node_modules/@effect/tsgo/dist/effect-tsgo.cjs");
const rows = [];
for (const ws of WORKSPACES) {
  if (args.only && !args.only.split(",").includes(ws)) continue;
  const cwd = path.join(args.t3, ws);
  const ours = await exec(args.ours, ["--noEmit", "--pretty", "false"], cwd);
  const ref = await exec(args.ref, ["--noEmit", "--pretty", "false"], cwd);
  const cli = await exec(process.execPath, [cliScript, "diagnostics", "--project", "tsconfig.json", "--strict", "--format", "text"], cwd);
  const od = parseTsc(ours.out), rd = parseTsc(ref.out), cd = parseCli(cli.out, cwd);
  const isEffect = (d) => d.code >= 377000 && d.code < 378000;
  const oe = od.filter(isEffect), re = rd.filter(isEffect);
  const effectVsRef = compare(oe.map((d) => d.text), re.map((d) => d.text));
  const tsVsRef = compare(od.filter((d) => !isEffect(d)).map((d) => d.text), rd.filter((d) => !isEffect(d)).map((d) => d.text));
  const effectVsCli = compare(oe.map(keyTsc), cd.map(keyCli));
  const name = ws.replaceAll("/", "_");
  fs.writeFileSync(path.join(args.out, `${name}.json`), JSON.stringify({ ws, exit: { ours: ours.code, ref: ref.code, cli: cli.code }, effectVsRef, tsVsRef, effectVsCli }, null, 2));
  fs.writeFileSync(path.join(args.out, `${name}.ours.txt`), ours.out);
  fs.writeFileSync(path.join(args.out, `${name}.ref.txt`), ref.out);
  fs.writeFileSync(path.join(args.out, `${name}.cli.txt`), cli.out);
  const row = {
    workspace: ws,
    effectOurs: oe.length,
    effectRef: re.length,
    effectCli: cd.length,
    effectDiffRef: effectVsRef.onlyA.length + effectVsRef.onlyB.length,
    effectDiffCli: effectVsCli.onlyA.length + effectVsCli.onlyB.length,
    tsOurs: od.length - oe.length,
    tsRef: rd.length - re.length,
    tsDiff: tsVsRef.onlyA.length + tsVsRef.onlyB.length,
    exit: `${ours.code}/${ref.code}/${cli.code}`,
  };
  rows.push(row);
  console.log(JSON.stringify(row));
}
const total = (k) => rows.reduce((s, r) => s + r[k], 0);
console.log(`totals: Effect ours ${total("effectOurs")}, ref ${total("effectRef")}, cli ${total("effectCli")}; Effect diffs vs ref ${total("effectDiffRef")}, vs cli ${total("effectDiffCli")}; TS diffs ${total("tsDiff")}`);
fs.writeFileSync(path.join(args.out, "summary.json"), JSON.stringify(rows, null, 2));
process.exit(total("effectDiffRef") || total("effectDiffCli") ? 1 : 0);
