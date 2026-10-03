#!/usr/bin/env node
// Runs the same tsc commands on a native tsgo and on the wasm build
// (npm/wasm) and compares the results.
//
// usage: node scripts/wasm/diff.mjs <native-tsgo> [options] [case-regex]
//   --inputs DIR  the input cache with query/repo and hono/repo (default
//                 ~/Library/Caches/ts-rust-wasm-inputs). A case whose input
//                 is missing is skipped.
//   --work DIR    the work dir, made fresh (default: a new dir in the temp
//                 dir). It keeps the stdout, stderr and output files of each
//                 run: <case>/<side>.*.
//   --repeat N    runs per side (default 1). The table shows the median time.
//                 A side whose runs give different results is "unstable".
//   --stack       also run each case once in a worker with a 256 MB stack and
//                 report the shadow stack high-water mark, and find the
//                 smallest worker stack (tsc() `stackSizeMb`) at which the
//                 cases marked `stack` give native's exit status and stdout
//   --json FILE   write the results as JSON
//   --list        print the case names and stop
//
// Sides: `native`, `native-st` (native with --singleThreaded) and `wasm`
// (node npm/wasm/bin/tsc-wasm.js, which loads npm/wasm/ts_rust.wasm). Each
// side runs with the same arguments, cwd and environment, under
// /usr/bin/time for the peak RSS. The harness compares the exit status,
// stdout and stderr byte for byte, and every file that the run writes:
// - Small cases are copied to <case>/proj before each run. The output is
//   every file that the run adds, changes or removes there.
// - Query and Hono run in place with --outDir <case>/out (and
//   --tsBuildInfoFile when the config is composite), the same path for each
//   side. The harness fails when a file of the input repo changes.
// Exit status: 0 when wasm and native-st match native on every case and no
// input changed, else 1.

import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { isMainThread, parentPort, Worker } from "node:worker_threads";

const repo = fileURLToPath(new URL("../..", import.meta.url));
const pkg = path.join(repo, "npm/wasm");
const wasmCli = path.join(pkg, "bin/tsc-wasm.js");
const wasmFile = path.join(pkg, "ts_rust.wasm");

/** Worker stack sizes (MB) that `--stack` tries, smallest first. */
const STACK_SIZES = [4, 8, 16, 32, 64, 128];

const json = value => `${JSON.stringify(value, null, 2)}\n`;

// The small cases that this harness writes. Paths are relative to the case
// dir, `links` maps a path to a symlink target.
const inline = {
    "external-diag": {
        files: {
            "tsconfig.json": json({ compilerOptions: { strict: true, incremental: true, noEmit: true, types: [] } }),
            "index.ts": `export const a: number = "x";\n`,
            "b.ts": "export const b = 1;\n",
        },
    },
    // Unique symbols of the same name in several files, in mapped types and
    // unions, across the checkers of a 4-checker program. Their member
    // names hold symbol ids (`__@key@<id>`), and members with no
    // declaration sort by name, so the printed order depends on the ids that
    // each checker gives.
    "unique-symbols": {
        files: {
            "tsconfig.json": json({
                compilerOptions: { strict: true, target: "es2022", declaration: true, outDir: "out", types: [] },
                files: ["a.ts", "b.ts", "c.ts", "d.ts", "use.ts"],
            }),
            ...Object.fromEntries(
                ["a", "b", "c", "d"].map(m => [
                    `${m}.ts`,
                    `export declare const key: unique symbol;\nexport declare const other: unique symbol;\n` +
                        `export type T${m} = { [key]: "${m}"; [other]: number };\n`,
                ]),
            ),
            "use.ts": `import * as a from "./a";\nimport * as b from "./b";\nimport * as c from "./c";\nimport * as d from "./d";\n` +
                `type Keys = typeof d.key | typeof c.other | typeof a.key | typeof b.other | typeof c.key | typeof b.key;\n` +
                `export type M = { [K in Keys]: K };\n` +
                `export const m = null! as M;\n` +
                `export const all = [a.key, b.key, c.key, d.key] as const;\n` +
                `export const wrong: M = { [a.key]: b.key };\n`,
        },
    },
    jsx: {
        files: {
            "tsconfig.json": json({
                compilerOptions: {
                    jsx: "react-jsx",
                    strict: true,
                    target: "es2020",
                    module: "esnext",
                    moduleResolution: "bundler",
                    lib: ["es2020"],
                    types: [],
                    declaration: true,
                    outDir: "out",
                    rootDir: "src",
                },
                include: ["src"],
            }),
            "stubs/react/package.json": json({
                name: "react",
                version: "19.0.0",
                types: "./index.d.ts",
                exports: { ".": { types: "./index.d.ts" }, "./jsx-runtime": { types: "./jsx-runtime.d.ts" } },
            }),
            "stubs/react/index.d.ts": `export type Key = string | number;
export type ReactNode = string | number | boolean | null | undefined | JSX.Element | readonly ReactNode[];
export function useState<T>(initial: T): [T, (next: T) => void];
export namespace JSX {
    interface Element { type: unknown; props: unknown; key: Key | null }
    interface ElementChildrenAttribute { children: {} }
    interface IntrinsicAttributes { key?: Key }
    interface IntrinsicElements {
        div: { className?: string; id?: string; children?: ReactNode; onClick?: (event: { x: number }) => void };
        span: { children?: ReactNode };
        button: { disabled?: boolean; children?: ReactNode; onClick?: () => void };
        ul: { children?: ReactNode };
        li: { children?: ReactNode };
    }
}
`,
            "stubs/react/jsx-runtime.d.ts": `import type { JSX, Key } from "./index";
export type { JSX };
export function jsx(type: unknown, props: unknown, key?: Key): JSX.Element;
export function jsxs(type: unknown, props: unknown, key?: Key): JSX.Element;
export const Fragment: unique symbol;
`,
            "src/button.tsx": `import type { ReactNode } from "react";

export interface ButtonProps {
    label: string;
    disabled?: boolean;
    onPress?: () => void;
    children?: ReactNode;
}

export function Button({ label, disabled = false, onPress, children }: ButtonProps) {
    return (
        <button disabled={disabled} onClick={onPress}>
            {label}
            {children}
        </button>
    );
}
`,
            "src/app.tsx": `import { useState } from "react";
import { Button } from "./button";

function List<T>({ items, render }: { items: readonly T[]; render: (item: T) => string }) {
    return <ul>{items.map((item, i) => <li key={i}>{render(item)}</li>)}</ul>;
}

export function App(props: { title: string; count?: number }) {
    const [count, setCount] = useState(props.count ?? 0);
    const extra = { className: "extra", id: "app" };
    return (
        <>
            <div {...extra} onClick={e => setCount(count + e.x)}>
                <span>{props.title}</span>
                {count > 2 ? <span>many</span> : null}
                <Button label="add" onPress={() => setCount(count + 1)} />
                <Button label={42} />
                <List items={[1, 2, 3]} render={n => n.toFixed(1)} />
                <section />
            </div>
        </>
    );
}
`,
        },
        links: { "node_modules/react": "../stubs/react" },
    },
    decorators: {
        files: {
            "tsconfig.json": json({
                compilerOptions: {
                    experimentalDecorators: true,
                    emitDecoratorMetadata: true,
                    strict: true,
                    target: "es2017",
                    module: "commonjs",
                    lib: ["es2017"],
                    types: [],
                    declaration: true,
                    outDir: "out",
                    rootDir: "src",
                },
                include: ["src"],
            }),
            "src/decorators.ts": `export function sealed(constructor: Function) {
    Object.seal(constructor);
    Object.seal(constructor.prototype);
}
export function log(target: object, key: string | symbol, descriptor: PropertyDescriptor) {
    const original = descriptor.value;
    descriptor.value = function (this: unknown, ...args: unknown[]) {
        return original.apply(this, args);
    };
}
export function field(target: object, key: string | symbol) {}
export function param(target: object, key: string | symbol | undefined, index: number) {}
export function format(pattern: string) {
    return (target: object, key: string | symbol, descriptor: PropertyDescriptor) => descriptor;
}
`,
            "src/model.ts": `import { field, format, log, param, sealed } from "./decorators";

export class Service {
    ping(): string {
        return "pong";
    }
}
export enum Level { Low, High }

@sealed
export class Greeter {
    @field greeting: string;
    @field level: Level = Level.Low;
    @field tags: string[] = [];
    @field service?: Service;
    constructor(message: string, @param service: Service, @param count: number) {
        this.greeting = message;
    }
    @log
    greet(@param name: string, times: number): string {
        return \`\${this.greeting}, \${name}\`.repeat(times);
    }
    @format("x")
    get upper(): string {
        return this.greeting.toUpperCase();
    }
    @log
    static create(message: string): Greeter {
        return new Greeter(message, new Service(), 1);
    }
}

export class Broken {
    @sealed
    method() {}
}
`,
        },
    },
    "decl-maps": {
        files: {
            "tsconfig.json": json({
                compilerOptions: {
                    strict: true,
                    target: "es2020",
                    module: "esnext",
                    moduleResolution: "bundler",
                    lib: ["es2020"],
                    types: [],
                    outDir: "out",
                    rootDir: "src",
                },
                include: ["src"],
            }),
            "src/index.ts": `export * from "./shapes";
export { default as makeStore, type Store } from "./store";
export * as util from "./util";
`,
            "src/shapes.ts": `export interface Point {
    readonly x: number;
    readonly y: number;
}
export type Shape =
    | { kind: "circle"; center: Point; radius: number }
    | { kind: "rect"; min: Point; max: Point };
export enum Color { Red = "red", Green = "green" }
export const enum Flags { None = 0, A = 1 << 0, B = 1 << 1, AB = A | B }
export abstract class Base<T extends Shape = Shape> {
    #id = 0;
    protected constructor(readonly shape: T) {}
    abstract area(): number;
    get id(): number {
        return this.#id;
    }
    static origin: Point = { x: 0, y: 0 };
}
export class Circle extends Base<Extract<Shape, { kind: "circle" }>> {
    constructor(radius: number) {
        super({ kind: "circle", center: Base.origin, radius });
    }
    area() {
        return Math.PI * this.shape.radius ** 2;
    }
}
export function area(shape: Shape): number;
export function area(shapes: readonly Shape[]): number[];
export function area(input: Shape | readonly Shape[]): number | number[] {
    if (isList(input)) return input.map(s => area(s));
    return input.kind === "circle"
        ? Math.PI * input.radius ** 2
        : (input.max.x - input.min.x) * (input.max.y - input.min.y);
}
function isList(input: Shape | readonly Shape[]): input is readonly Shape[] {
    return Array.isArray(input);
}
export namespace Geometry {
    export const unit = { x: 1, y: 1 } satisfies Point;
    export function scale(p: Point, k: number): Point {
        return { x: p.x * k, y: p.y * k };
    }
}
`,
            "src/store.ts": `export interface Store<S> {
    get(): S;
    set(next: Partial<S>): void;
}
export default function makeStore<S extends object>(initial: S) {
    let state = initial;
    const listeners = new Set<(state: S) => void>();
    return {
        get: () => state,
        set(next: Partial<S>) {
            state = { ...state, ...next };
            listeners.forEach(listener => listener(state));
        },
        subscribe(listener: (state: S) => void) {
            listeners.add(listener);
            return () => listeners.delete(listener);
        },
    };
}
`,
            "src/util.ts": `export type Getters<T> = { [K in keyof T as \`get\${Capitalize<string & K>}\`]: () => T[K] };
export function getters<T extends Record<string, unknown>>(value: T): Getters<T> {
    return Object.fromEntries(
        Object.entries(value).map(([k, v]) => [\`get\${k[0].toUpperCase()}\${k.slice(1)}\`, () => v]),
    ) as Getters<T>;
}
export const config = { name: "demo", retries: 3, nested: { deep: [1, "two", true] as const } };
export type DeepReadonly<T> = T extends (infer U)[]
    ? readonly DeepReadonly<U>[]
    : T extends object ? { readonly [K in keyof T]: DeepReadonly<T[K]> } : T;
export function freeze<T>(value: T): DeepReadonly<T> {
    return Object.freeze(value) as DeepReadonly<T>;
}
export const pair = <A, B>(a: A, b: B) => [a, b] as const;
export async function* countdown(from: number) {
    for (let i = from; i > 0; i--) yield i;
}
`,
        },
    },
    init: { files: {} },
    casing: {
        files: {
            "tsconfig.json": json({
                compilerOptions: { strict: true, target: "es2020", lib: ["es2020"], types: [], noEmit: true },
                include: ["src"],
            }),
            "src/Foo.ts": "export const foo = 1;\n",
            "src/main.ts": [
                'import { foo } from "./foo";',
                'import { foo as again } from "./FOO";',
                "export const sum = foo + again;",
                "",
            ].join("\n"),
        },
    },
    // Non-ASCII names and text, a UTF-8 BOM, a UTF-16LE file and CRLF.
    text: {
        files: {
            "tsconfig.json": json({
                compilerOptions: {
                    strict: true,
                    target: "es2020",
                    lib: ["es2020"],
                    types: [],
                    declaration: true,
                    sourceMap: true,
                    outDir: "out",
                    rootDir: "src",
                },
                include: ["src"],
            }),
            "src/ünïcödé.ts": 'export const grüße = "héllo wörld 👋";\nexport const n: number = "ß";\n',
            "src/日本語/名前.ts": [
                'import { grüße } from "../ünïcödé";',
                'export const 名前: string = grüße + "テスト";',
                "export const bad: number = 名前;",
                "",
            ].join("\n"),
            "src/bom.ts": Buffer.concat([
                Buffer.from([0xef, 0xbb, 0xbf]),
                Buffer.from('export const bom: "x" = "y";\n'),
            ]),
            "src/utf16.ts": Buffer.concat([
                Buffer.from([0xff, 0xfe]),
                Buffer.from('export const wide = "Ωmega";\nexport const w: boolean = wide;\n', "utf16le"),
            ]),
            "src/crlf.ts": 'export function f(a: string) {\r\n    return a.length;\r\n}\r\nf(1);\r\n',
            // Latin-1 bytes, which are not UTF-8.
            "src/latin1.ts": Buffer.from('// caf\xe9\nexport const s: "x" = "na\xefve";\n', "latin1"),
            "src/with space.ts": 'export const spaced: number = "s p";\n',
        },
    },
    "build-ref": {
        files: {
            "lib/tsconfig.json": json({
                compilerOptions: {
                    composite: true,
                    declarationMap: true,
                    strict: true,
                    target: "es2020",
                    module: "esnext",
                    moduleResolution: "bundler",
                    lib: ["es2020"],
                    types: [],
                    outDir: "dist",
                    rootDir: "src",
                },
                include: ["src"],
            }),
            "lib/src/index.ts": `export interface User {
    id: number;
    name: string;
}
export function greet(user: User): string {
    return \`hi \${user.name}\`;
}
export const version = "1.0.0";
`,
            "app/tsconfig.json": json({
                compilerOptions: {
                    composite: true,
                    strict: true,
                    target: "es2020",
                    module: "esnext",
                    moduleResolution: "bundler",
                    lib: ["es2020"],
                    types: [],
                    outDir: "dist",
                    rootDir: "src",
                },
                references: [{ path: "../lib" }],
                include: ["src"],
            }),
            "app/src/main.ts": `import { greet, version, type User } from "../../lib/src/index";

const user: User = { id: 1, name: "a" };
export const message = \`\${greet(user)} \${version}\`;
`,
        },
    },
};

/**
 * The cases. `input` names where the files come from: `query` and `hono`
 * (run in place, under `--inputs`), `fixture` (copied from
 * crates/ts_goport/tests/fixtures/multiprog/<dir>), `inline` (copied from
 * `inline[files ?? name]`) or `none`. `dir` is the cwd in the input.
 * `steps` are the tsc argument lists, run in order in the same dir.
 * `buildInfo` adds --tsBuildInfoFile (composite configs). `link` runs in
 * the copy through a symlink. `noSt` leaves out the native-st side.
 * `stack` marks the cases of the worker stack sweep. `before[i](cwd)` edits
 * the files before step i. `nativeSteps` are the
 * native sides' steps when the wasm output must equal another native run:
 * the wasm build has no message catalogs, so its `--locale` output is the
 * English one.
 */
function cases(inputs) {
    const js = ["--emitDeclarationOnly", "false", "--sourceMap", "--declarationMap"];
    const maps = ["--declaration", "--declarationMap", "--sourceMap"];
    const query = { input: "query", dir: "packages/query-core" };
    const hono = { input: "hono", dir: ".", buildInfo: true };
    const prod = ["-p", "tsconfig.prod.json"];
    const build = ["-p", "tsconfig.build.json"];
    const list = [
        { name: "version", input: "none", steps: [["--version"], ["--help"], ["--all"]] },
        { name: "query-core", ...query, steps: [prod], stack: true },
        { name: "query-core-js", ...query, steps: [[...prod, ...js, "--listEmittedFiles"]] },
        { name: "query-listfiles", ...query, steps: [[...prod, "--listFilesOnly"]] },
        { name: "query-explainfiles", ...query, steps: [[...prod, "--noEmit", "--explainFiles"]] },
        { name: "query-traceresolution", ...query, steps: [[...prod, "--noEmit", "--traceResolution"]] },
        // The other prod configs of scripts/prepare-query-inputs.mjs. They
        // import query-core through the pnpm workspace links.
        ...[
            ["query-persist", "query-persist-client-core"],
            ["query-sync-storage", "query-sync-storage-persister"],
            ["query-async-storage", "query-async-storage-persister"],
            ["query-broadcast", "query-broadcast-client-experimental"],
        ].map(([name, dir]) => ({
            name,
            input: "query",
            dir: ".",
            steps: [["-p", `packages/${dir}/tsconfig.prod.json`]],
        })),
        { name: "hono", ...hono, steps: [build], stack: true },
        { name: "hono-js", ...hono, steps: [[...build, ...js]] },
        { name: "hono-showconfig", ...hono, steps: [[...build, "--showConfig"]] },
        { name: "hono-pretty", ...hono, steps: [[...build, "--noEmit", "--pretty"]] },
        {
            name: "hono-locale",
            ...hono,
            steps: [[...build, "--noEmit", "--locale", "ja"]],
            nativeSteps: [[...build, "--noEmit"]],
        },
        // The second run reads the build info of the first.
        { name: "hono-incremental", ...hono, steps: [build, build] },
        // The fixtures as they are, then a check without emit: an emit
        // error (TS5055 in basic) hides the semantic diagnostics.
        ...["basic", "cut", "emit", "linked"].map(dir => ({
            name: `multiprog-${dir}`,
            input: "fixture",
            dir,
            steps: [["-p", "."], ["-p", ".", "--noEmit"]],
        })),
        {
            name: "multiprog-build-dedup",
            input: "fixture",
            dir: "build-dedup",
            steps: [["-b", "tsconfig.json", "--explainFiles", "--pretty", "false"]],
        },
        { name: "jsx", input: "inline", steps: [["-p", "."]] },
        { name: "decorators", input: "inline", steps: [["-p", "."]] },
        { name: "unique-symbols", input: "inline", steps: [["-p", "."], ["-p", ".", "--checkers", "1"]] },
        { name: "decl-maps", input: "inline", steps: [["-p", ".", ...maps]] },
        // decl-maps from a cwd that is a symlink, with PWD set as a shell sets it.
        {
            name: "decl-maps-link",
            input: "inline",
            files: "decl-maps",
            link: true,
            steps: [["-p", ".", ...maps, "--listFiles"]],
        },
        // --init writes the --singleThreaded flag into the new tsconfig.json.
        { name: "init", input: "inline", steps: [["--init"]], noSt: true },
        { name: "casing", input: "inline", steps: [["-p", "."]] },
        { name: "text", input: "inline", steps: [["-p", "."], ["-p", ".", "--pretty"]] },
        {
            name: "build-ref",
            input: "inline",
            steps: [["-b", "app"], ["-b", "app"], ["-b", "app", "--clean"]],
        },
        // The second run reads a build info whose diagnostic is an external
        // one (a content mapper's: no message key, a source and a text), and
        // writes it again because b.ts changed.
        {
            name: "external-diag",
            input: "inline",
            steps: [["-p", "."], ["-p", "."]],
            before: { 1: externalDiagnosticEdit },
        },
    ];
    for (const c of list) {
        c.root = c.input === "query" || c.input === "hono" ? path.join(inputs, c.input, "repo") : undefined;
    }
    return list;
}

/** The edit of the `external-diag` case (see there). */
function externalDiagnosticEdit(cwd) {
    const file = path.join(cwd, "tsconfig.tsbuildinfo");
    // A first run that wrote none already differs from native.
    if (!fs.existsSync(file)) return;
    const info = JSON.parse(fs.readFileSync(file, "utf8"));
    for (const entry of info.semanticDiagnosticsPerFile) {
        if (!Array.isArray(entry)) continue;
        entry[1] = [{ pos: 13, end: 14, code: 1001, category: 0, source: "vue", messageText: "mapper warning" }];
    }
    fs.writeFileSync(file, JSON.stringify(info));
    fs.writeFileSync(path.join(cwd, "b.ts"), "export const b = 2;\n");
}

const sha = bytes => createHash("sha256").update(bytes).digest("hex");

/**
 * Every file under `root`: its path relative to `root`, mapped to the
 * sha256 of its bytes (`-> target` for a symlink). Dirs named in `skip`
 * are left out. With `statOnly`, the value is the size and mtime instead.
 */
function snapshot(root, { skip = [], statOnly = false } = {}) {
    const files = new Map();
    const walk = rel => {
        for (const entry of fs.readdirSync(path.join(root, rel), { withFileTypes: true })) {
            const file = rel ? `${rel}/${entry.name}` : entry.name;
            const full = path.join(root, file);
            if (entry.isSymbolicLink()) files.set(file, `-> ${fs.readlinkSync(full)}`);
            else if (entry.isDirectory()) {
                if (!skip.includes(entry.name)) walk(file);
            } else if (statOnly) {
                const stat = fs.statSync(full);
                files.set(file, `${stat.size} ${stat.mtimeMs}`);
            } else files.set(file, sha(fs.readFileSync(full)));
        }
    };
    if (fs.existsSync(root)) walk("");
    return files;
}

/** The files of `after` that are new or changed since `before`, and the removed ones (`removed`). */
function changes(before, after) {
    const out = new Map();
    for (const [file, value] of after) if (before.get(file) !== value) out.set(file, value);
    for (const file of before.keys()) if (!after.has(file)) out.set(file, "removed");
    return out;
}

/** The paths where two snapshots differ. */
function differing(a, b) {
    const files = new Set([...a.keys(), ...b.keys()]);
    return [...files].filter(file => a.get(file) !== b.get(file)).sort();
}

const median = values => [...values].sort((a, b) => a - b)[Math.floor(values.length / 2)];

/** The command of `side` for tsc arguments `args`. */
function command(side, native, args) {
    if (side === "wasm") return [process.execPath, wasmCli, ...args];
    return [native, ...args, ...(side === "native-st" ? ["--singleThreaded"] : [])];
}

/** Runs `argv` in `cwd` under /usr/bin/time. Returns the exit status, output, wall ms and peak RSS (bytes). */
function timed(argv, cwd, env, timeFile) {
    const linux = process.platform === "linux";
    const start = performance.now();
    const run = spawnSync("/usr/bin/time", [linux ? "-v" : "-l", "-o", timeFile, ...argv], {
        cwd,
        env,
        maxBuffer: 1 << 30,
    });
    const ms = performance.now() - start;
    if (run.error) throw run.error;
    const report = fs.existsSync(timeFile) ? fs.readFileSync(timeFile, "utf8") : "";
    const rss = linux
        ? Number(/Maximum resident set size \(kbytes\): (\d+)/.exec(report)?.[1]) * 1024
        : Number(/(\d+)\s+maximum resident set size/.exec(report)?.[1]);
    return {
        exit: run.status,
        stdout: run.stdout,
        stderr: run.stderr,
        ms,
        rss,
    };
}

/**
 * Makes the case's working copy at `<caseDir>/proj` and returns its cwd.
 * Cases that run in place return the input dir.
 */
function prepare(c, caseDir, fixtures) {
    if (c.root) return path.join(c.root, c.dir);
    const proj = path.join(caseDir, "proj");
    fs.rmSync(proj, { recursive: true, force: true });
    fs.mkdirSync(proj, { recursive: true });
    if (c.input === "fixture") {
        fs.cpSync(path.join(fixtures, c.dir), proj, { recursive: true, verbatimSymlinks: true });
    } else if (c.input === "inline") {
        const { files, links = {} } = inline[c.files ?? c.name];
        for (const [file, text] of Object.entries(files)) {
            fs.mkdirSync(path.dirname(path.join(proj, file)), { recursive: true });
            fs.writeFileSync(path.join(proj, file), text);
        }
        for (const [file, target] of Object.entries(links)) {
            fs.mkdirSync(path.dirname(path.join(proj, file)), { recursive: true });
            fs.symlinkSync(target, path.join(proj, file));
        }
    }
    if (!c.link) return proj;
    const link = path.join(caseDir, "link");
    fs.rmSync(link, { force: true });
    fs.symlinkSync("proj", link);
    return link;
}

/** The environment of a run: a cwd through a symlink gets PWD, as a shell that entered it sets. */
const runEnv = (c, cwd) => (c.link ? { ...process.env, PWD: cwd } : process.env);

/** The tsc arguments of a step, with the output options of in-place cases. */
function stepArgs(c, step, out) {
    if (!c.root) return step;
    const extra = ["--outDir", out];
    if (c.buildInfo) extra.push("--tsBuildInfoFile", `${out}/tsconfig.tsbuildinfo`);
    return [...step, ...extra];
}

/**
 * Runs every step of `c` once on `side`. Returns per-step results (exit,
 * stdout, stderr and the written files: path to sha256), and the summed ms
 * and peak RSS. With `keep`, keeps the output in `<caseDir>/<side>.*`.
 */
function runOnce(c, side, ctx, keep) {
    const caseDir = path.join(ctx.work, c.name);
    const out = path.join(caseDir, "out");
    const cwd = prepare(c, caseDir, ctx.fixtures);
    const base = c.root ? undefined : snapshot(cwd);
    fs.rmSync(out, { recursive: true, force: true });
    const steps = [];
    let ms = 0;
    let rss = 0;
    const caseSteps = side === "wasm" ? c.steps : (c.nativeSteps ?? c.steps);
    for (const [i, step] of caseSteps.entries()) {
        c.before?.[i]?.(cwd);
        const args = stepArgs(c, step, out);
        const run = timed(command(side, ctx.native, args), cwd, runEnv(c, cwd), path.join(caseDir, "time.txt"));
        ms += run.ms;
        rss = Math.max(rss, run.rss);
        const files = c.root ? snapshot(out) : changes(base, snapshot(cwd));
        steps.push({ args, exit: run.exit, stdout: run.stdout, stderr: run.stderr, files });
        if (keep) {
            fs.writeFileSync(path.join(caseDir, `${side}.${i}.stdout`), run.stdout);
            fs.writeFileSync(path.join(caseDir, `${side}.${i}.stderr`), run.stderr);
        }
    }
    if (keep) {
        const kept = path.join(caseDir, `${side}.files`);
        fs.rmSync(kept, { recursive: true, force: true });
        const from = c.root ? out : path.join(caseDir, "proj");
        if (fs.existsSync(from)) fs.renameSync(from, kept);
    }
    return { steps, ms, rss };
}

/** A comparable form of a run: exit, output hashes and files of each step. */
const fingerprint = run =>
    JSON.stringify(
        run.steps.map(s => [s.exit, sha(s.stdout), sha(s.stderr), [...s.files].sort()]),
    );

/** How side `b` differs from side `a`: lists of differing parts. */
function compare(a, b) {
    const diff = { exit: [], stdout: [], stderr: [], files: [] };
    a.steps.forEach((sa, i) => {
        const sb = b.steps[i];
        if (sa.exit !== sb.exit) diff.exit.push(`step ${i}: ${sa.exit} vs ${sb.exit}`);
        if (!sa.stdout.equals(sb.stdout)) diff.stdout.push(`step ${i}: ${firstLineDiff(sa.stdout, sb.stdout)}`);
        if (!sa.stderr.equals(sb.stderr)) diff.stderr.push(`step ${i}: ${firstLineDiff(sa.stderr, sb.stderr)}`);
        for (const file of differing(sa.files, sb.files)) diff.files.push(`step ${i}: ${file}`);
    });
    return diff;
}

/** The first line where two outputs differ, both versions, cut to 200 chars each. */
function firstLineDiff(a, b) {
    const la = a.toString().split("\n");
    const lb = b.toString().split("\n");
    const i = la.findIndex((line, n) => line !== lb[n]);
    const at = i < 0 ? la.length : i;
    const cut = s => (s === undefined ? "<end>" : JSON.stringify(s.slice(0, 200)));
    return `line ${at + 1} (${la.length} vs ${lb.length} lines): ${cut(la[at])} vs ${cut(lb[at])}`;
}

/** Runs `tsc()` of npm/wasm/node.js for each worker stack size and checks it against `want`. */
async function stackSweep(c, ctx, want) {
    const { tsc } = await import(pathToFileURL(path.join(pkg, "node.js")).href);
    const caseDir = path.join(ctx.work, c.name);
    const out = path.join(caseDir, "out");
    const results = [];
    for (const stackSizeMb of STACK_SIZES) {
        const cwd = prepare(c, caseDir, ctx.fixtures);
        fs.rmSync(out, { recursive: true, force: true });
        let ok = true;
        let note = "";
        for (const [i, step] of c.steps.entries()) {
            c.before?.[i]?.(cwd);
            try {
                const result = await tsc(stepArgs(c, step, out), { cwd, stackSizeMb, env: runEnv(c, cwd) });
                const { exit, stdout } = want.steps[i];
                if (result.exitCode !== exit || result.stdout !== stdout.toString()) {
                    ok = false;
                    note = `exit ${result.exitCode}, stdout ${result.stdout.length} chars`;
                }
            } catch (error) {
                ok = false;
                note = String(error.message).split("\n")[0].slice(0, 120);
            }
        }
        results.push({ stackSizeMb, ok, note });
    }
    fs.rmSync(out, { recursive: true, force: true });
    return results;
}

/**
 * Runs each step of `c` in a worker with a 256 MB stack, through the real
 * npm/wasm/node-worker.js, and returns the shadow stack high-water mark in
 * bytes (see `probeWorker`), or an error.
 */
async function shadowStack(c, ctx, module) {
    const caseDir = path.join(ctx.work, c.name);
    const out = path.join(caseDir, "out");
    const cwd = prepare(c, caseDir, ctx.fixtures);
    fs.rmSync(out, { recursive: true, force: true });
    let high = 0;
    for (const [i, step] of c.steps.entries()) {
        c.before?.[i]?.(cwd);
        const worker = new Worker(new URL(import.meta.url), {
            workerData: {
                module,
                args: stepArgs(c, step, out),
                cwd,
                env: runEnv(c, cwd),
                diagnosticsJson: false,
                tty: false,
                stream: false,
            },
            resourceLimits: { stackSizeMb: 256 },
            stdout: true,
            stderr: true,
        });
        const messages = [];
        worker.on("message", message => messages.push(message));
        await new Promise((resolve, reject) => {
            worker.on("error", reject);
            worker.on("exit", resolve);
        });
        const run = messages.find(m => "exitCode" in m || "error" in m);
        const probe = messages.find(m => "stackBytes" in m);
        if (run?.error) return { error: run.error.split("\n")[0] };
        if (!probe) return { error: "the probe worker sent no result" };
        high = Math.max(high, probe.stackBytes);
        ctx.stackTop = probe.stackTop;
    }
    fs.rmSync(out, { recursive: true, force: true });
    return { bytes: high };
}

/**
 * The worker of `shadowStack`. It keeps the memory of the instance that
 * node-worker.js makes, runs node-worker.js (which posts the run result),
 * then posts the shadow stack use: the stack is the first `stackTop` bytes
 * of memory and grows down from `stackTop`, and a new instance's memory is
 * zero, so the lowest non-zero byte marks the deepest frame. This is a lower
 * bound: the deepest frame may write zeros only.
 */
async function probeWorker() {
    let memory;
    const Instance = WebAssembly.Instance;
    WebAssembly.Instance = class extends Instance {
        constructor(module, imports) {
            super(module, imports);
            memory = this.exports.memory;
        }
    };
    await import(pathToFileURL(path.join(pkg, "node-worker.js")).href);
    const top = stackTop(fs.readFileSync(wasmFile));
    const low = new Uint8Array(memory.buffer, 0, top).findIndex(byte => byte !== 0);
    parentPort.postMessage({ stackBytes: low < 0 ? 0 : top - low, stackTop: top });
}

/**
 * The initial value of the module's first global, `__stack_pointer`: the
 * top of the shadow stack (crates/ts_wasm/build.rs puts the stack first in
 * memory).
 */
function stackTop(bytes) {
    let at = 8;
    const leb = () => {
        let value = 0;
        let shift = 0;
        let byte;
        do {
            byte = bytes[at++];
            value += (byte & 0x7f) * 2 ** shift;
            shift += 7;
        } while (byte & 0x80);
        return value;
    };
    while (at < bytes.length) {
        const id = bytes[at++];
        const size = leb();
        const end = at + size;
        if (id === 6) {
            leb(); // the global count
            at += 2; // the value type and the mutability
            if (bytes[at++] !== 0x41) break; // i32.const
            return leb();
        }
        at = end;
    }
    throw new Error("the module has no i32 __stack_pointer global");
}

function parseArgs(argv) {
    const opts = {
        inputs: path.join(os.homedir(), "Library/Caches/ts-rust-wasm-inputs"),
        repeat: 1,
        stack: false,
        list: false,
    };
    const rest = [];
    for (let i = 0; i < argv.length; i++) {
        const arg = argv[i];
        if (arg === "--inputs") opts.inputs = argv[++i];
        else if (arg === "--work") opts.work = argv[++i];
        else if (arg === "--repeat") opts.repeat = Number(argv[++i]);
        else if (arg === "--json") opts.json = argv[++i];
        else if (arg === "--stack") opts.stack = true;
        else if (arg === "--list") opts.list = true;
        else rest.push(arg);
    }
    [opts.native, opts.filter] = rest;
    return opts;
}

const mb = bytes => (bytes / 2 ** 20).toFixed(0);

async function main() {
    const opts = parseArgs(process.argv.slice(2));
    const all = cases(path.resolve(opts.inputs));
    if (opts.list) {
        for (const c of all) console.log(c.name);
        return 0;
    }
    if (!opts.native) {
        const lines = fs.readFileSync(fileURLToPath(import.meta.url), "utf8").split("\n").slice(1);
        console.error(lines.slice(0, lines.findIndex(line => !line.startsWith("//"))).join("\n"));
        return 2;
    }
    const filter = new RegExp(opts.filter ?? ".");
    const work = opts.work
        ? path.resolve(opts.work)
        : fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), "ts-rust-wasm-diff-"));
    fs.rmSync(work, { recursive: true, force: true });
    fs.mkdirSync(work, { recursive: true });
    const ctx = {
        work: fs.realpathSync(work),
        native: path.resolve(opts.native),
        fixtures: path.join(repo, "crates/ts_goport/tests/fixtures/multiprog"),
    };
    console.log(`native ${ctx.native} (${sha(fs.readFileSync(ctx.native)).slice(0, 12)})`);
    console.log(`wasm   ${wasmFile} (${sha(fs.readFileSync(wasmFile)).slice(0, 12)})`);
    console.log(`work   ${ctx.work}\n`);
    const module = opts.stack ? await WebAssembly.compile(fs.readFileSync(wasmFile)) : undefined;

    const results = [];
    let failed = false;
    for (const c of all.filter(c => filter.test(c.name))) {
        if (c.root && !fs.existsSync(path.join(c.root, c.dir))) {
            console.log(`${c.name}: skipped, no input at ${c.root}`);
            continue;
        }
        fs.mkdirSync(path.join(ctx.work, c.name), { recursive: true });
        const guard = c.root ? snapshot(c.root, { skip: ["node_modules", ".git"], statOnly: true }) : undefined;
        const sides = {};
        for (const side of c.noSt ? ["native", "wasm"] : ["native", "native-st", "wasm"]) {
            const runs = [];
            for (let r = 0; r < opts.repeat; r++) runs.push(runOnce(c, side, ctx, r === 0));
            sides[side] = {
                ...runs[0],
                ms: median(runs.map(run => run.ms)),
                rss: Math.max(...runs.map(run => run.rss)),
                unstable: runs.some(run => fingerprint(run) !== fingerprint(runs[0])),
            };
        }
        const wasm = compare(sides.native, sides.wasm);
        const st = c.noSt ? undefined : compare(sides.native, sides["native-st"]);
        const count = d => Object.values(d).reduce((n, list) => n + list.length, 0);
        const result = {
            name: c.name,
            cwd: c.root ? path.join(c.root, c.dir) : `${c.input}:${c.dir ?? c.name}`,
            steps: c.steps,
            native: summary(sides.native),
            nativeSt: c.noSt ? undefined : summary(sides["native-st"]),
            wasm: summary(sides.wasm),
            wasmDiff: wasm,
            singleThreadedDiff: st,
        };
        if (opts.stack) {
            result.shadowStack = await shadowStack(c, ctx, module);
            if (c.stack) result.stackSweep = await stackSweep(c, ctx, sides.native);
        }
        result.inputChanged = guard
            ? differing(guard, snapshot(c.root, { skip: ["node_modules", ".git"], statOnly: true }))
            : [];
        failed ||= count(wasm) > 0 || (st ? count(st) : 0) > 0 || result.inputChanged.length > 0
            || sides.wasm.unstable || sides.native.unstable;
        results.push(result);
        printResult(result);
    }
    printTable(results);
    if (opts.json) fs.writeFileSync(opts.json, json({ work: ctx.work, stackTop: ctx.stackTop, results }));
    return failed ? 1 : 0;
}

/** The JSON form of one side's run. */
function summary(side) {
    return {
        exit: side.steps.map(s => s.exit),
        stdoutBytes: side.steps.map(s => s.stdout.length),
        files: side.steps.map(s => s.files.size),
        ms: Math.round(side.ms),
        rss: side.rss,
        unstable: side.unstable,
    };
}

function printResult(r) {
    const lines = [];
    for (const [label, diff] of [["wasm", r.wasmDiff], ["native-st", r.singleThreadedDiff ?? {}]]) {
        for (const [part, list] of Object.entries(diff)) {
            for (const item of list.slice(0, 5)) lines.push(`  ${label} ${part}: ${item}`);
            if (list.length > 5) lines.push(`  ${label} ${part}: ... ${list.length - 5} more`);
        }
    }
    if (r.wasm.unstable) lines.push("  wasm: unstable across repeats");
    if (r.native.unstable) lines.push("  native: unstable across repeats");
    for (const file of r.inputChanged.slice(0, 5)) lines.push(`  INPUT CHANGED: ${file}`);
    if (r.shadowStack) {
        lines.push(
            r.shadowStack.error
                ? `  shadow stack: run failed: ${r.shadowStack.error}`
                : `  shadow stack: ${(r.shadowStack.bytes / 1024).toFixed(0)} KiB used`,
        );
    }
    if (r.stackSweep) {
        const sizes = r.stackSweep.map(s => `${s.stackSizeMb} MB ${s.ok ? "ok" : `FAIL (${s.note})`}`);
        lines.push(`  worker stack: ${sizes.join(", ")}`);
    }
    console.log(`${r.name}: ${lines.length ? "\n" + lines.join("\n") : "ok"}`);
}

function printTable(results) {
    const header = [
        "case",
        "native exit",
        "wasm exit",
        "stdout",
        "emit",
        "native-st",
        "native ms",
        "wasm ms",
        "native RSS MB",
        "node RSS MB",
    ];
    const anyDiff = diff => Object.values(diff).some(list => list.length);
    const rows = results.map(r => [
        r.name,
        r.native.exit.join(","),
        r.wasm.exit.join(","),
        r.wasmDiff.stdout.length || r.wasmDiff.stderr.length ? "DIFF" : "same",
        `${r.wasmDiff.files.length ? "DIFF" : "same"} (${r.native.files.reduce((a, b) => a + b, 0)})`,
        !r.singleThreadedDiff ? "n/a" : anyDiff(r.singleThreadedDiff) ? "DIFF" : "same",
        String(r.native.ms),
        String(r.wasm.ms),
        mb(r.native.rss),
        mb(r.wasm.rss),
    ]);
    const widths = header.map((h, i) => Math.max(h.length, ...rows.map(row => row[i].length)));
    const line = row => `| ${row.map((cell, i) => cell.padEnd(widths[i])).join(" | ")} |`;
    console.log(`\n${line(header)}\n| ${widths.map(w => "-".repeat(w)).join(" | ")} |`);
    for (const row of rows) console.log(line(row));
}

if (isMainThread) process.exitCode = await main();
else await probeWorker();
