#!/usr/bin/env node
// Times complete T3 Code workspace checks. Each round runs every command once,
// sequentially, in a rotated order; the report gives medians, exit statuses
// and peak RSS (macOS /usr/bin/time -l).
//   rust:        <rust-plain> --noEmit             (no Effect diagnostics)
//   rust-effect: <rust-effect> --noEmit            (one pass, native Effect diagnostics)
//   go-effect:   <ref> --noEmit                    (Effect-patched TypeScript)
//   two-pass:    <rust-plain> --noEmit, then effect-tsgo diagnostics --strict (T3's current path)
// Each tsc command keeps its own build info file (<tmp>/<workspace>-<command>.tsbuildinfo),
// so one compiler's cache never invalidates another's. --cold deletes it before each run.
//
// usage: node scripts/effect/bench-t3.mjs --t3 DIR --rust-plain BIN --rust-effect BIN --ref BIN
//          [--workspaces a,b] [--rounds 3] [--cold] [--out FILE]
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { parseArgs } from "node:util";

const { values: args } = parseArgs({
  options: {
    t3: { type: "string" },
    "rust-plain": { type: "string" },
    "rust-effect": { type: "string" },
    ref: { type: "string" },
    workspaces: { type: "string", default: "apps/server,apps/web,apps/mobile,packages/client-runtime,packages/shared" },
    rounds: { type: "string", default: "3" },
    cold: { type: "boolean", default: false },
    out: { type: "string", default: "/tmp/effect-bench.json" },
  },
});
const cli = path.join(args.t3, "node_modules/@effect/tsgo/dist/effect-tsgo.cjs");

function timed(argv, cwd) {
  const started = performance.now();
  const r = spawnSync("/usr/bin/time", ["-l", ...argv], { cwd, encoding: "utf8", maxBuffer: 1 << 28 });
  const ms = performance.now() - started;
  const rss = Number(/(\d+)\s+maximum resident set size/.exec(r.stderr)?.[1] ?? 0);
  return { ms, code: r.status, rssMb: rss / 1048576 };
}

const infoDir = fs.mkdtempSync("/tmp/effect-bench-info-");
const info = (cwd, name) => path.join(infoDir, `${path.basename(cwd)}-${name}.tsbuildinfo`);
const COMMANDS = {
  rust: (cwd) => [timed([args["rust-plain"], "--noEmit", "--tsBuildInfoFile", info(cwd, "rust")], cwd)],
  "rust-effect": (cwd) => [timed([args["rust-effect"], "--noEmit", "--tsBuildInfoFile", info(cwd, "rust-effect")], cwd)],
  "go-effect": (cwd) => [timed([args.ref, "--noEmit", "--tsBuildInfoFile", info(cwd, "go-effect")], cwd)],
  "two-pass": (cwd) => [
    timed([args["rust-plain"], "--noEmit", "--tsBuildInfoFile", info(cwd, "two-pass")], cwd),
    timed([process.execPath, cli, "diagnostics", "--project", "tsconfig.json", "--strict", "--format", "text"], cwd),
  ],
};
const names = Object.keys(COMMANDS);

function clearBuildInfo(dir) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    if (entry.name === "node_modules" || entry.name === ".git") continue;
    const p = path.join(dir, entry.name);
    if (entry.isDirectory()) clearBuildInfo(p);
    else if (entry.name.endsWith(".tsbuildinfo")) fs.rmSync(p);
  }
}

const median = (xs) => {
  const s = [...xs].sort((a, b) => a - b);
  return s.length % 2 ? s[(s.length - 1) / 2] : (s[s.length / 2 - 1] + s[s.length / 2]) / 2;
};

const results = {};
for (const ws of args.workspaces.split(",")) {
  const cwd = path.join(args.t3, ws);
  results[ws] = Object.fromEntries(names.map((n) => [n, []]));
  // One untimed warm-up of each command, so the incremental state and the OS cache are the same for all.
  if (!args.cold) for (const n of names) COMMANDS[n](cwd);
  for (let round = 0; round < Number(args.rounds); round++) {
    const order = names.map((_, i) => names[(i + round) % names.length]);
    for (const n of order) {
      if (args.cold) {
        clearBuildInfo(cwd);
        fs.rmSync(info(cwd, n), { force: true });
      }
      const parts = COMMANDS[n](cwd);
      results[ws][n].push({
        ms: parts.reduce((s, p) => s + p.ms, 0),
        codes: parts.map((p) => p.code),
        rssMb: Math.max(...parts.map((p) => p.rssMb)),
      });
    }
  }
  const row = Object.fromEntries(
    names.map((n) => [
      n,
      {
        medianS: +(median(results[ws][n].map((r) => r.ms)) / 1000).toFixed(2),
        rssMb: +median(results[ws][n].map((r) => r.rssMb)).toFixed(0),
        exits: [...new Set(results[ws][n].map((r) => r.codes.join("+")))].join(","),
      },
    ]),
  );
  results[ws].summary = row;
  console.log(ws, JSON.stringify(row));
}
fs.writeFileSync(args.out, JSON.stringify({ cold: args.cold, rounds: Number(args.rounds), results }, null, 2));
