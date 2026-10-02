#!/usr/bin/env node
// Times the wasm package (npm/wasm) on fixed projects. For each case it
// gives the first tsc() call of a new Node process ("cold": the module
// compile and the V8 tier-up are in it) and the median of the later calls
// in that process ("warm"). It also gives the module size raw, gzip -9 and
// brotli -q 11.
//
// usage: node scripts/wasm/bench.mjs [--wasm FILE] [--runs N] [--cold N] [case-regex]
//   --wasm   the module to time (default npm/wasm/ts_rust.wasm). It runs in
//            a copy of the package, so the checkout is not changed.
//   --runs   warm calls per case (default 5)
//   --cold   new processes per case; the cold time is their median (default 3)
// Inputs (see scripts/wasm/diff.mjs for how they are installed):
//   ~/Library/Caches/ts-rust-wasm-inputs/{query,hono}/repo
//   ~/Library/Caches/ts-rust-wasm-bench/zod-*/  (zod v4 sources with tsconfig.bench.json)
// A case whose input is missing is skipped.

import { execFileSync } from "node:child_process";
import { brotliCompressSync, constants, gzipSync } from "node:zlib";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const repo = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
const caches = path.join(os.homedir(), "Library/Caches");
const zod = fs.readdirSync(path.join(caches, "ts-rust-wasm-bench"), { withFileTypes: true })
    .find(e => e.isDirectory() && e.name.startsWith("zod-"));

const CASES = [
    {
        name: "tiny",
        args: ["-p", "/p", "--noEmit"],
        files: {
            "/p/tsconfig.json": '{"compilerOptions":{"strict":true}}',
            "/p/a.ts": "export const n: number = 1;\n",
        },
    },
    {
        name: "zod",
        cwd: zod && path.join(caches, "ts-rust-wasm-bench", zod.name, "packages/zod"),
        args: ["-p", "tsconfig.bench.json", "--noEmit"],
    },
    {
        name: "query-core",
        cwd: path.join(caches, "ts-rust-wasm-inputs/query/repo/packages/query-core"),
        args: ["-p", "tsconfig.prod.json", "--noEmit"],
    },
    {
        name: "hono",
        cwd: path.join(caches, "ts-rust-wasm-inputs/hono/repo"),
        args: ["-p", "tsconfig.build.json", "--noEmit", "--tsBuildInfoFile", path.join(os.tmpdir(), "bench-hono.tsbuildinfo")],
    },
];

const median = values => [...values].sort((a, b) => a - b)[Math.floor(values.length / 2)];

/** Child mode: time `runs` calls of one case in this process and print them as JSON. */
async function child(pkg, name, runs) {
    const { tsc } = await import(path.join(pkg, "node.js"));
    const c = CASES.find(c => c.name === name);
    const times = [];
    let exitCode;
    for (let i = 0; i < runs; i++) {
        const start = performance.now();
        ({ exitCode } = await tsc(c.args, { cwd: c.cwd, files: c.files }));
        times.push(performance.now() - start);
    }
    process.stdout.write(JSON.stringify({ times, exitCode }));
}

function parseArgs(argv) {
    const opts = { wasm: path.join(repo, "npm/wasm/ts_rust.wasm"), runs: 5, cold: 3, filter: undefined };
    for (let i = 0; i < argv.length; i++) {
        if (argv[i] === "--wasm") opts.wasm = path.resolve(argv[++i]);
        else if (argv[i] === "--runs") opts.runs = Number(argv[++i]);
        else if (argv[i] === "--cold") opts.cold = Number(argv[++i]);
        else opts.filter = new RegExp(argv[i]);
    }
    return opts;
}

if (process.argv[2] === "--child") {
    await child(process.argv[3], process.argv[4], Number(process.argv[5]));
} else {
    const opts = parseArgs(process.argv.slice(2));
    const pkg = fs.mkdtempSync(path.join(os.tmpdir(), "ts-rust-bench-"));
    for (const file of fs.readdirSync(path.join(repo, "npm/wasm"))) {
        if (file.endsWith(".js")) fs.copyFileSync(path.join(repo, "npm/wasm", file), path.join(pkg, file));
    }
    fs.copyFileSync(opts.wasm, path.join(pkg, "ts_rust.wasm"));
    const bytes = fs.readFileSync(opts.wasm);
    const brotli = brotliCompressSync(bytes, { params: { [constants.BROTLI_PARAM_QUALITY]: 11 } }).length;
    console.log(`module ${opts.wasm}: raw ${bytes.length}, gzip ${gzipSync(bytes, { level: 9 }).length}, brotli ${brotli}`);
    console.log("case        exit   cold ms   warm ms");
    for (const c of CASES) {
        if (opts.filter && !opts.filter.test(c.name)) continue;
        if (c.cwd && !fs.existsSync(c.cwd)) {
            console.log(`${c.name.padEnd(11)} skipped (no input at ${c.cwd})`);
            continue;
        }
        const cold = [];
        let warm = [];
        let exitCode;
        for (let i = 0; i < opts.cold; i++) {
            // The first process also gives the warm calls.
            const runs = i === 0 ? 1 + opts.runs : 1;
            const out = execFileSync(process.execPath, [fileURLToPath(import.meta.url), "--child", pkg, c.name, String(runs)], {
                maxBuffer: 1 << 26,
            });
            const result = JSON.parse(out.toString());
            cold.push(result.times[0]);
            if (i === 0) warm = result.times.slice(1);
            exitCode = result.exitCode;
        }
        const ms = values => (values.length ? median(values).toFixed(0) : "-").padStart(9);
        console.log(`${c.name.padEnd(11)} ${String(exitCode).padStart(4)} ${ms(cold)} ${ms(warm)}`);
    }
    fs.rmSync(pkg, { recursive: true, force: true });
}
