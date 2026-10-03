#!/usr/bin/env node
// Runs the TypeScript compiler test cases (tests/cases/compiler and
// tests/cases/conformance) on a native tsgo and on the wasm module, and
// compares the results. It finds wasm crashes and wasm-only differences on a
// broad corpus.
//
// usage: node scripts/wasm/corpus.mjs <native-tsgo> [options] [case-regex]
//   --corpus DIR   the dir with cases/compiler and cases/conformance
//                  (default ~/Library/Caches/ts-rust-wasm-corpus/tests)
//   --suite NAME   compiler, conformance or all (default compiler)
//   --jobs N       cases at a time (default 8)
//   --limit N      run only the first N cases that the regex selects
//   --emit MODE    auto (default): emit when the case sets declaration,
//                  emitDeclarationOnly or composite, else --noEmit.
//                  always: emit unless the case sets noEmit. never.
//   --timeout S    seconds per side and case (default 120)
//   --fs KIND      the wasm side's file system: node (default, node-run.js
//                  nodeFileSystem on the case dir) or memory (core.js
//                  memoryFileSystem with the case files, as browser.js;
//                  cases with symlinks are skipped)
//   --stack MB     the stack of a wasm worker (default 256, as node.js)
//   --add ARGS     more tsc arguments for each case, split at spaces (for
//                  example "--pretty true" or "--traceResolution true")
//   --wasm FILE    the module (default npm/wasm/ts_rust.wasm)
//   --work DIR     the work dir (default: a new dir in the temp dir). For
//                  each case that is not "same", it keeps cases/<id>/ (the
//                  files after the wasm run) and cases/<id>.result/ with
//                  result.json (both sides' output and written files) and
//                  repro.sh.
//   --json FILE    the per-case results (default <work>/results.json)
//   --list         print each case with its arguments or skip reason, and
//                  stop
//
// The corpus: tests/cases/{compiler,conformance} and tests/lib of the Go
// pin, microsoft/TypeScript tsc/testdata/tests, for example from the
// codeload tar.gz of the pin commit, extracted with --strip-components=3.
//
// For each case, the harness writes the case's files into <work>/cases/<id>,
// as the Go harness lays them out under "/" (relative names go below
// @currentDirectory, default /.src), with @link and @symlink symlinks and
// tests/lib in /.lib when the case refers to it. It turns the directives into
// tsc arguments:
// - compiler options become `--name value`. Absolute paths in path options
//   and in tsconfig.json move below the case root. A value list for a
//   non-list option (`@target: es2015, esnext`) is a set of variants: the
//   harness takes the first value that tsgo still supports.
// - with a tsconfig.json or jsconfig.json unit, it runs `-p` on it. Else
//   the root files are the units (only the last unit when it has `require(`
//   or `reference path`, or with @noImplicitReferences), less .json files.
// - Go harness defaults: --skipDefaultLibCheck and --noErrorTruncation.
// - harness-only directives are dropped. A case with an option that the
//   command line cannot take (an unknown name, paths, plugins) is skipped.
// Then it runs native (a child process) and wasm (runRequest of
// npm/wasm/node-run.js on a worker thread, one worker per job), one after
// the other in the same dir, which it writes fresh before each side. Both
// sides get the same arguments, cwd (a real path) and an empty environment.
// It compares the exit status, stdout, stderr and each file that the run
// adds, changes or removes.
//
// Statuses: same, differ, wasm-crash (a trap, a dead worker or an exit
// status above 5), native-crash, both-crash, wasm-timeout, native-timeout,
// skipped, harness-error.
// Exit status: 1 when a case differs, crashes or times out on wasm only, or
// fails in the harness, else 0.

import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { isMainThread, parentPort, Worker, workerData } from "node:worker_threads";

const repo = fileURLToPath(new URL("../..", import.meta.url));
const pkg = path.join(repo, "npm/wasm");

/** Marks the case root in planned arguments; `runCase` puts in the real path. */
const ROOT = "\0root";

/** Exit statuses of tsc. A higher status, or a signal, is a crash. */
const MAX_EXIT_STATUS = 5;

/** Directives of the Go harness (harnessutil.go) that are not tsc options. */
const HARNESS_OPTIONS = new Set([
    "usecasesensitivefilenames",
    "baselinefile",
    "includebuiltfile",
    "filename",
    "libfiles",
    "noimplicitreferences",
    "currentdirectory",
    "symlink",
    "link",
    "notypesandsymbols",
    "fullemitpaths",
    "reportdiagnostics",
    "capturesuggestions",
    "typescriptversion",
    // Compiler options of the harness's program that tsc does not take.
    "allownontsextensions",
    "suppressoutputpathcheck",
    // Fourslash file directives.
    "emitthisfile",
    "noopen",
]);

/** Options whose value is a comma-separated list. */
const LIST_OPTIONS = new Set(["lib", "types", "typeRoots", "rootDirs", "moduleSuffixes", "customConditions"]);

/** Options with paths that the harness moves below the case root when absolute. */
const PATH_OPTIONS = new Set([
    "outDir",
    "rootDir",
    "declarationDir",
    "baseUrl",
    "outFile",
    "tsBuildInfoFile",
    "typeRoots",
    "rootDirs",
]);

/** Values that tsgo removed (the Go harness skips them): avoided when a case lists variants. */
const REMOVED_VALUES = {
    target: ["es3", "es5"],
    module: ["amd", "umd", "system", "none"],
    moduleResolution: ["node", "node10", "classic"],
    esModuleInterop: ["false"],
    allowSyntheticDefaultImports: ["false"],
    alwaysStrict: ["false"],
};

/** Options that make `--emit auto` emit. */
const EMIT_OPTIONS = ["declaration", "emitDeclarationOnly", "composite"];

function usage(message) {
    if (message) console.error(message);
    console.error("usage: node scripts/wasm/corpus.mjs <native-tsgo> [options] [case-regex]  (see the header)");
    process.exit(2);
}

function parseArgs(argv) {
    const opts = {
        corpus: path.join(os.homedir(), "Library/Caches/ts-rust-wasm-corpus/tests"),
        suite: "compiler",
        jobs: 8,
        limit: Infinity,
        emit: "auto",
        timeout: 120,
        fs: "node",
        stack: 256,
        add: [],
        wasm: path.join(pkg, "ts_rust.wasm"),
        work: undefined,
        json: undefined,
        list: false,
        native: undefined,
        filter: undefined,
    };
    // The options with a value, by name, and how each reads its value.
    const valueOptions = {
        corpus: String,
        suite: String,
        jobs: Number,
        limit: Number,
        emit: String,
        timeout: Number,
        fs: String,
        stack: Number,
        add: value => value.split(" ").filter(Boolean),
        wasm: String,
        work: String,
        json: String,
    };
    for (let i = 0; i < argv.length; i++) {
        const arg = argv[i];
        const name = arg.slice(2);
        if (arg === "--list") opts.list = true;
        else if (arg.startsWith("--") && Object.hasOwn(valueOptions, name)) {
            opts[name] = valueOptions[name](argv[++i] ?? usage(`${arg} needs a value`));
        } else if (arg.startsWith("--")) usage(`unknown option ${arg}`);
        else if (!opts.native) opts.native = path.resolve(arg);
        else if (!opts.filter) opts.filter = new RegExp(arg);
        else usage(`unexpected argument ${arg}`);
    }
    if (!opts.native) usage();
    if (!["auto", "always", "never"].includes(opts.emit)) usage(`bad --emit ${opts.emit}`);
    if (!["compiler", "conformance", "all"].includes(opts.suite)) usage(`bad --suite ${opts.suite}`);
    if (!["node", "memory"].includes(opts.fs)) usage(`bad --fs ${opts.fs}`);
    return opts;
}

/**
 * The tsc option names (by lower-case name) and which ones are booleans,
 * from `<native> --all`.
 */
function readOptionTable(native) {
    return new Promise((resolve, reject) => {
        const child = spawn(native, ["--all"], { env: {} });
        let text = "";
        child.stdout.on("data", chunk => (text += chunk));
        child.on("error", reject);
        child.on("close", () => {
            // tsc takes --ignoreDeprecations, but `--all` does not list it.
            const table = new Map([["ignoredeprecations", { name: "ignoreDeprecations", boolean: false }]]);
            for (const block of text.split(/\n\s*\n/)) {
                const match = /^--(\w+)/m.exec(block);
                if (!match) continue;
                table.set(match[1].toLowerCase(), { name: match[1], boolean: /^type: boolean$/m.test(block) });
            }
            if (table.size < 50) reject(new Error(`${native} --all lists only ${table.size} options`));
            resolve(table);
        });
    });
}

/** The case files of the suite, as paths relative to `corpus`, sorted. */
function listCases(corpus, suite) {
    const dirs = suite === "all" ? ["compiler", "conformance"] : [suite];
    const files = [];
    const walk = rel => {
        for (const entry of fs.readdirSync(path.join(corpus, "cases", rel), { withFileTypes: true })) {
            const child = `${rel}/${entry.name}`;
            if (entry.isDirectory()) walk(child);
            else if (/\.tsx?$/.test(entry.name)) files.push(child);
        }
    };
    for (const dir of dirs) walk(dir);
    return files.sort();
}

const OPTION_LINE = /^\/\/\s*@(\w+)\s*:\s*([^\r\n]*)/;
const LINK_LINE = /^\/\/\s*@link\s*:\s*([^\r\n]*)\s*->\s*([^\r\n]*)/;

/**
 * Splits a case into its units, as Go `ParseTestFilesAndSymlinks` and
 * `extractCompilerSettings` (test_case_parser.go). `text` holds the file's
 * bytes as latin1 chars, so the units write back byte for byte.
 */
function parseCase(text, baseName) {
    const settings = new Map();
    const units = [];
    const links = new Map();
    let name = "";
    let content = [];
    const flush = () => {
        units.push({ name, content: content.join("\n") });
        content = [];
    };
    for (const line of text.split(/\r?\n/)) {
        const link = LINK_LINE.exec(line);
        if (link) {
            links.set(link[2].trim(), link[1].trim());
            continue;
        }
        const option = OPTION_LINE.exec(line);
        if (!option) {
            // Go drops blank lines before a unit's first line.
            if (content.length || line.length) content.push(line);
            continue;
        }
        const key = option[1].toLowerCase();
        const value = option[2].trim();
        if (key !== "filename") {
            if (key === "symlink" && name) {
                for (const target of value.split(",")) if (target.trim()) links.set(target.trim(), name);
            } else {
                settings.set(key, value.endsWith(";") ? value.slice(0, -1) : value);
            }
            continue;
        }
        if (name) flush();
        // A UTF-8 BOM (latin1 chars here) is trivia. Go also ignores an
        // option on the BOM's line.
        else if (content.some(l => !/^(\u00ef\u00bb\u00bf)?\s*(\/\/.*)?$/.test(l))) {
            throw new Error("content before the first @filename");
        } else content = [];
        name = value;
    }
    if (!name && !units.length) name = baseName;
    flush();
    return { settings, units, links };
}

/** `name` as an absolute path below the case root, as Go `GetNormalizedAbsolutePath`. */
const absolute = (name, cwd) => path.posix.resolve(cwd, name.replaceAll("\\", "/"));

/**
 * The plan of one case: its files, symlinks, cwd and tsc arguments, or
 * `{ skip }` with the reason.
 */
function planCase(rel, text, table, emitMode) {
    let parsed;
    try {
        parsed = parseCase(text, path.basename(rel));
    } catch (error) {
        return { skip: `parse: ${error.message}` };
    }
    const { settings, units, links } = parsed;
    if (units.some(u => /^[a-zA-Z]:/.test(u.name)) || [...links.keys()].some(l => /^[a-zA-Z]:/.test(l))) {
        return { skip: "windows path" };
    }
    const cwd = settings.get("currentdirectory") || "/.src";
    const files = new Map();
    for (const unit of units) files.set(absolute(unit.name, cwd), unit.content);
    const symlinks = [...links].map(([link, target]) => [absolute(link, cwd), absolute(target, cwd)]);

    const args = [];
    const set = new Set();
    let variants = false;
    for (const [key, raw] of settings) {
        if (HARNESS_OPTIONS.has(key)) continue;
        const option = table.get(key);
        if (!option || option.name === "paths" || option.name === "plugins") return { skip: `option @${key}` };
        const { name } = option;
        const rooted = v => (PATH_OPTIONS.has(name) && v.startsWith("/") ? `${ROOT}${v}` : v);
        let value = raw;
        if (LIST_OPTIONS.has(name)) {
            const list = raw.split(",").map(v => rooted(v.trim()));
            value = (name === "moduleSuffixes" ? list : list.filter(Boolean)).join(",");
        } else if (option.boolean && !raw) {
            return { skip: `empty value @${key}` };
        } else if (raw.includes(",")) {
            variants = true;
            const values = raw.split(",").map(v => v.trim()).filter(v => v && v !== "*" && !v.startsWith("-"));
            const removed = REMOVED_VALUES[name] ?? [];
            value = values.find(v => !removed.includes(v.toLowerCase())) ?? values[0];
            if (value === undefined) return { skip: `variants @${key}: ${raw}` };
        } else if (raw === "*") {
            return { skip: `variants @${key}: *` };
        }
        set.add(name);
        args.push(`--${name}`, LIST_OPTIONS.has(name) ? value : rooted(value));
    }

    const config = units.find(u => /^(ts|js)config\.json$/i.test(path.posix.basename(u.name)));
    const configText = config?.content ?? "";
    const asks = name => {
        const i = args.indexOf(`--${name}`);
        return (i >= 0 && args[i + 1] === "true") || new RegExp(`"${name}"\\s*:\\s*true`).test(configText);
    };
    if (asks("noEmit")) {
        // The case does not emit.
    } else if (emitMode === "always" || (emitMode === "auto" && EMIT_OPTIONS.some(asks))) {
        if (!set.has("outDir") && !set.has("outFile") && !/"out(Dir|File)"/.test(configText)) {
            args.push("--outDir", "__out");
        }
    } else {
        if (set.has("noEmit")) args.splice(args.indexOf("--noEmit"), 2);
        args.push("--noEmit", "true");
    }
    if (!set.has("skipDefaultLibCheck")) args.push("--skipDefaultLibCheck", "true");
    if (!set.has("noErrorTruncation")) args.push("--noErrorTruncation", "true");

    if (config) {
        args.push("-p", path.posix.relative(cwd, absolute(config.name, cwd)) || ".");
    } else {
        const last = units.at(-1);
        const onlyLast = settings.get("noimplicitreferences") || last.content.includes("require(")
            || /reference\spath/.test(last.content);
        for (const unit of onlyLast ? [last] : units) {
            if (/\.(json|tsbuildinfo)$/i.test(unit.name)) continue;
            args.push(path.posix.relative(cwd, absolute(unit.name, cwd)));
        }
    }
    for (const lib of (settings.get("libfiles") ?? "").split(",").map(v => v.trim()).filter(Boolean)) {
        args.push(path.posix.relative(cwd, `/.lib/${lib}`));
    }
    const useLib = settings.has("libfiles") || units.some(u => u.content.includes("/.lib/"));
    return { cwd, files, symlinks, args, useLib, variants };
}

/** Writes the case files below `root`, fresh. */
function materialize(root, plan, corpus) {
    fs.rmSync(root, { recursive: true, force: true });
    fs.mkdirSync(path.join(root, plan.cwd), { recursive: true });
    for (const [name, content] of plan.files) {
        const file = path.join(root, name);
        let bytes = Buffer.from(content, "latin1");
        // Absolute paths in a config file move below the case root.
        if (/^(ts|js)config.*\.json$/i.test(path.basename(name))) {
            bytes = Buffer.from(content.replace(/"\/(?!\/)/g, `"${root}/`), "latin1");
        }
        if (fs.existsSync(file) && fs.statSync(file).isDirectory()) continue;
        fs.mkdirSync(path.dirname(file), { recursive: true });
        fs.writeFileSync(file, bytes);
    }
    if (plan.useLib) fs.cpSync(path.join(corpus, "lib"), path.join(root, ".lib"), { recursive: true });
    for (const [link, target] of plan.symlinks) {
        const file = path.join(root, link);
        fs.mkdirSync(path.dirname(file), { recursive: true });
        try {
            fs.symlinkSync(path.join(root, target), file);
        } catch {
            // A link over a case file: the file stays.
        }
    }
}

/** Every file below `root`: relative path to bytes, symlinks as `-> target`. */
function snapshot(root) {
    const files = new Map();
    const walk = rel => {
        for (const entry of fs.readdirSync(path.join(root, rel), { withFileTypes: true })) {
            const child = rel ? `${rel}/${entry.name}` : entry.name;
            const full = path.join(root, child);
            if (entry.isSymbolicLink()) files.set(child, `-> ${fs.readlinkSync(full)}`);
            else if (entry.isDirectory()) walk(child);
            else files.set(child, fs.readFileSync(full).toString("latin1"));
        }
    };
    walk("");
    return files;
}

/** The files that a run added, changed or removed: path to bytes (null when removed). */
function changes(before, after) {
    const out = {};
    for (const [name, bytes] of after) if (before.get(name) !== bytes) out[name] = bytes;
    for (const name of before.keys()) if (!after.has(name)) out[name] = null;
    return out;
}

/** Runs the native tsgo: `{ exitCode, signal, stdout, stderr, ms, timeout }`. */
function runNative(native, args, cwd, timeoutMs) {
    return new Promise(resolve => {
        const start = performance.now();
        const child = spawn(native, args, { cwd, env: {} });
        const stdout = [];
        const stderr = [];
        let timeout = false;
        const timer = setTimeout(() => {
            timeout = true;
            child.kill("SIGKILL");
        }, timeoutMs);
        child.stdout.on("data", chunk => stdout.push(chunk));
        child.stderr.on("data", chunk => stderr.push(chunk));
        child.on("error", error => stderr.push(Buffer.from(String(error))));
        child.on("close", (exitCode, signal) => {
            clearTimeout(timer);
            resolve({
                exitCode,
                signal,
                stdout: Buffer.concat(stdout).toString(),
                stderr: Buffer.concat(stderr).toString(),
                ms: performance.now() - start,
                timeout,
            });
        });
    });
}

/** One wasm worker per job. It restarts after a timeout or a crash of its thread. */
class WasmSlot {
    constructor(module, stackSizeMb) {
        this.module = module;
        this.stackSizeMb = stackSizeMb;
        this.nextId = 0;
        this.start();
    }

    start() {
        this.worker = new Worker(fileURLToPath(import.meta.url), {
            workerData: { module: this.module },
            resourceLimits: { stackSizeMb: this.stackSizeMb },
            stdout: true,
            stderr: true,
        });
        this.worker.unref();
    }

    /**
     * Runs one request: `{ exitCode, stdout, stderr, error?, ms, timeout?,
     * files? }`. With `memoryRoot`, the run reads the files below it into
     * memory, and `files` holds its changes.
     */
    run(args, cwd, timeoutMs, memoryRoot) {
        const id = this.nextId++;
        const start = performance.now();
        return new Promise(resolve => {
            const worker = this.worker;
            const done = result => {
                clearTimeout(timer);
                worker.off("message", onMessage);
                worker.off("exit", onExit);
                worker.off("error", onError);
                // A crash result has no stdout.
                resolve({ ms: performance.now() - start, stdout: "", stderr: "", ...result });
            };
            const restart = () => {
                worker.terminate();
                this.start();
            };
            const onMessage = message => message.id === id && done(message.result);
            const onError = error => {
                restart();
                done({ error: `worker error: ${error?.message ?? error}`, stderr: "" });
            };
            const onExit = code => {
                this.start();
                done({ error: `worker exit ${code}`, stderr: "" });
            };
            const timer = setTimeout(() => {
                restart();
                done({ timeout: true, error: "timeout", stderr: "" });
            }, timeoutMs);
            worker.on("message", onMessage);
            worker.on("error", onError);
            worker.on("exit", onExit);
            worker.postMessage({ id, args, cwd, env: {}, memoryRoot });
        });
    }
}

/** A short text of what differs: exit status, the first differing line of a stream, files. */
function describeDiff(native, wasm) {
    const parts = [];
    if (wasm.error) parts.push(`wasm: ${wasm.error}`);
    if (native.signal) parts.push(`native: signal ${native.signal}`);
    if (native.exitCode !== wasm.exitCode) parts.push(`exit ${native.exitCode} vs ${wasm.exitCode}`);
    for (const stream of ["stdout", "stderr"]) {
        if (native[stream] === wasm[stream]) continue;
        const a = native[stream].split("\n");
        const b = wasm[stream].split("\n");
        let i = 0;
        while (i < a.length && a[i] === b[i]) i++;
        parts.push(`${stream} line ${i + 1}: ${JSON.stringify(a[i] ?? "<end>")} vs ${JSON.stringify(b[i] ?? "<end>")}`);
    }
    const names = new Set([...Object.keys(native.files), ...Object.keys(wasm.files)]);
    const files = [...names].filter(n => native.files[n] !== wasm.files[n]);
    if (files.length) parts.push(`files: ${files.slice(0, 5).join(", ")}${files.length > 5 ? ", ..." : ""}`);
    return parts.join("; ");
}

const crashed = side => side.error !== undefined || side.signal || side.exitCode > MAX_EXIT_STATUS;

/** Runs one planned case on both sides and returns its result record. */
async function runCase(opts, plan, root, slot) {
    const cwd = path.join(root, plan.cwd);
    const args = plan.args.map(a => a.replaceAll(ROOT, root));
    const timeoutMs = opts.timeout * 1000;
    materialize(root, plan, opts.corpus);
    const before = snapshot(root);
    const native = await runNative(opts.native, args, cwd, timeoutMs);
    native.files = changes(before, snapshot(root));
    materialize(root, plan, opts.corpus);
    const memory = opts.fs === "memory";
    const wasm = await slot.run(args, cwd, timeoutMs, memory ? root : undefined);
    if (!memory) wasm.files = wasm.timeout ? {} : changes(before, snapshot(root));
    wasm.files ??= {};
    let status;
    if (native.timeout) status = "native-timeout";
    else if (wasm.timeout) status = "wasm-timeout";
    else if (crashed(native) && crashed(wasm)) status = "both-crash";
    else if (crashed(wasm)) status = "wasm-crash";
    else if (crashed(native)) status = "native-crash";
    else status = describeDiff(native, wasm) ? "differ" : "same";
    return { status, native, wasm };
}

/** Writes result.json and repro.sh into a kept case dir. */
/**
 * Writes result.json, the case files (input/) and repro.sh into
 * `<root>.result`. repro.sh runs each side on a fresh copy of input/ at
 * `root`, the path of the harness run.
 */
function keep(opts, root, record, plan, native, wasm) {
    const dir = `${root}.result`;
    fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(path.join(dir, "result.json"), `${JSON.stringify({ ...record, native, wasm }, null, 2)}\n`);
    materialize(root, plan, opts.corpus);
    fs.cpSync(root, path.join(dir, "input"), { recursive: true, verbatimSymlinks: true });
    const quote = text => `'${text.replaceAll("'", "'\\''")}'`;
    const args = plan.args.map(a => quote(a.replaceAll(ROOT, root))).join(" ");
    const fresh = `rm -rf ${quote(root)} && cp -R ${quote(path.join(dir, "input"))} ${quote(root)} && cd ${
        quote(path.join(root, plan.cwd))
    }`;
    fs.writeFileSync(
        path.join(dir, "repro.sh"),
        [
            "#!/bin/sh",
            `# ${record.name}: ${record.status} (corpus.mjs, wasm worker stack ${opts.stack} MB, fs ${opts.fs}).`,
            "# tsc-wasm.js runs on the real file system with a 256 MB worker stack.",
            `${fresh} && env -i ${quote(opts.native)} ${args}; echo "native exit $?"`,
            `${fresh} && env -i "$(command -v node)" ${quote(path.join(pkg, "bin/tsc-wasm.js"))} ${args}; echo "wasm exit $?"`,
            "",
        ].join("\n"),
        { mode: 0o755 },
    );
}

async function main() {
    const opts = parseArgs(process.argv.slice(2));
    const table = await readOptionTable(opts.native);
    let names = listCases(opts.corpus, opts.suite);
    if (opts.filter) names = names.filter(n => opts.filter.test(n));
    names = names.slice(0, opts.limit);

    const plans = names.map(name => {
        const text = fs.readFileSync(path.join(opts.corpus, "cases", name)).toString("latin1");
        const plan = planCase(name, text, table, opts.emit);
        if (opts.fs === "memory" && plan.symlinks?.length) return { name, plan: { skip: "symlinks (memory fs)" } };
        plan.args?.unshift(...opts.add);
        return { name, plan };
    });
    if (opts.list) {
        for (const { name, plan } of plans) {
            console.log(`${name}\t${plan.skip ? `SKIP ${plan.skip}` : `${plan.cwd}\t${plan.args.join(" ")}`}`);
        }
        return;
    }

    // A real path: native tsc gets its cwd from getcwd (no $PWD), so the
    // wasm side must get the same path (/tmp is /private/tmp on macOS).
    if (opts.work) fs.mkdirSync(opts.work, { recursive: true });
    const work = fs.realpathSync(opts.work ?? fs.mkdtempSync(path.join(os.tmpdir(), "ts-rust-corpus-")));
    fs.mkdirSync(path.join(work, "cases"), { recursive: true });
    const jsonFile = opts.json ?? path.join(work, "results.json");
    const module = await WebAssembly.compile(fs.readFileSync(opts.wasm));
    const slots = Array.from({ length: opts.jobs }, () => new WasmSlot(module, opts.stack));

    const results = [];
    const counts = {};
    const count = status => (counts[status] = (counts[status] ?? 0) + 1);
    let next = 0;
    let finished = 0;
    const started = performance.now();
    const runner = async slot => {
        while (next < plans.length) {
            const index = next++;
            const { name, plan } = plans[index];
            if (plan.skip) {
                results[index] = { name, status: "skipped", reason: plan.skip };
                count("skipped");
                continue;
            }
            const root = path.join(work, "cases", `${index}-${name.replaceAll("/", "_").replace(/\.\w+$/, "")}`);
            let record;
            try {
                const { status, native, wasm } = await runCase(opts, plan, root, slot);
                record = {
                    name,
                    status,
                    args: plan.args,
                    cwd: plan.cwd,
                    variants: plan.variants || undefined,
                    native: {
                        exitCode: native.exitCode,
                        signal: native.signal ?? undefined,
                        ms: Math.round(native.ms),
                        firstLine: native.stdout.slice(0, native.stdout.indexOf("\n") >>> 0).slice(0, 160),
                    },
                    wasm: { exitCode: wasm.exitCode, error: wasm.error, ms: Math.round(wasm.ms) },
                };
                if (status !== "same") {
                    record.diff = describeDiff(native, wasm);
                    record.dir = root;
                    keep(opts, root, record, plan, native, wasm);
                }
            } catch (error) {
                record = { name, status: "harness-error", error: String(error?.stack ?? error) };
            }
            if (record.status === "same") fs.rmSync(root, { recursive: true, force: true });
            results[index] = record;
            count(record.status);
            if (record.status !== "same") {
                console.error(`${record.status}\t${name}\t${record.diff ?? record.wasm?.error ?? record.error ?? ""}`.slice(0, 400));
            }
            if (++finished % 250 === 0) {
                const secs = ((performance.now() - started) / 1000).toFixed(0);
                console.error(`[${finished}/${plans.length} run, ${secs} s] ${JSON.stringify(counts)}`);
            }
        }
    };
    await Promise.all(slots.map(runner));
    for (const slot of slots) slot.worker.terminate();

    const skipReasons = {};
    for (const r of results) if (r.status === "skipped") skipReasons[r.reason] = (skipReasons[r.reason] ?? 0) + 1;
    const summary = {
        cases: results.length,
        counts,
        seconds: Math.round((performance.now() - started) / 1000),
        // Cases that ran the first supported value of a variant list.
        variantCases: results.filter(r => r.variants).length,
        // Cases whose native output starts with an option error (such as a
        // removed `--target es5`): they test little more than the options.
        optionErrorFirst: results.filter(r => /^error TS5\d{3}:/.test(r.native?.firstLine ?? "")).length,
        skipReasons,
    };
    const meta = {
        corpus: opts.corpus,
        corpusCommit: readMaybe(path.join(opts.corpus, "../COMMIT")),
        suite: opts.suite,
        emit: opts.emit,
        add: opts.add,
        fs: opts.fs,
        stackMb: opts.stack,
        native: opts.native,
        wasm: opts.wasm,
        wasmBytes: fs.statSync(opts.wasm).size,
        node: process.version,
    };
    fs.writeFileSync(jsonFile, `${JSON.stringify({ meta, summary, cases: results }, null, 1)}\n`);
    console.log(JSON.stringify(summary, null, 2));
    for (const r of results) {
        if (r.status !== "same" && r.status !== "skipped") console.log(`${r.status}\t${r.name}\t${r.diff ?? r.error ?? ""}`);
    }
    console.log(`results: ${jsonFile}`);
    const bad = ["differ", "wasm-crash", "wasm-timeout", "harness-error"].some(status => counts[status]);
    process.exitCode = bad ? 1 : 0;
}

function readMaybe(file) {
    try {
        return fs.readFileSync(file, "utf8").trim();
    } catch {
        return undefined;
    }
}

if (isMainThread) {
    await main();
} else {
    // A wasm worker: runs one request at a time.
    const { runRequest } = await import(pathToFileURL(path.join(pkg, "node-run.js")).href);
    parentPort.on("message", ({ id, args, cwd, env, memoryRoot }) => {
        const start = performance.now();
        const before = memoryRoot && snapshot(memoryRoot);
        const files = before && new Map([...before].map(([name, bytes]) => [
            path.join(memoryRoot, name),
            Buffer.from(bytes, "latin1"),
        ]));
        const result = runRequest({ module: workerData.module, args, cwd, env, files, diagnosticsJson: false, tty: false });
        if (before && result.files) {
            // The run wrote into `files`. Its changes, as `changes` gives them for a dir.
            const after = new Map();
            for (const [name, data] of result.files) {
                after.set(path.relative(memoryRoot, name), Buffer.from(data).toString("latin1"));
            }
            result.files = changes(before, after);
        }
        parentPort.postMessage({ id, ms: performance.now() - start, result });
    });
}
