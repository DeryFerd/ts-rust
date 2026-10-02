// Tests of the package's Node entry. Build the module first:
// scripts/wasm/build.sh (WASM_PROFILE=release for a fast build).

import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { tsc } from "../node.js";

const project = {
    "/p/tsconfig.json": JSON.stringify({
        compilerOptions: { strict: true, target: "es2022", module: "esnext", outDir: "out", declaration: true },
        files: ["a.ts"],
    }),
    "/p/a.ts": [
        'const x: number = "hello";',
        "export function f(a: string) { return a.length; }",
        "f(1);",
        "",
    ].join("\n"),
};

test("prints the diagnostics and emits, in memory", async () => {
    const result = await tsc(["-p", "tsconfig.json"], { files: project, cwd: "/p" });
    assert.equal(result.exitCode, 2);
    assert.equal(
        result.stdout,
        "a.ts(1,7): error TS2322: Type 'string' is not assignable to type 'number'.\n"
            + "a.ts(3,3): error TS2345: Argument of type 'number' is not assignable to parameter of type 'string'.\n",
    );
    // The same output as the native tsgo.
    assert.equal(
        result.files.get("/p/out/a.js"),
        'const x = "hello";\nexport function f(a) { return a.length; }\nf(1);\n',
    );
    assert.equal(result.files.get("/p/out/a.d.ts"), "export declare function f(a: string): number;\n");
});

test("returns the diagnostics as JSON", async () => {
    const result = await tsc(["-p", "/p", "--noEmit"], { files: project, diagnostics: "json" });
    assert.equal(result.exitCode, 2);
    assert.equal(result.stdout, "");
    assert.deepEqual(
        result.diagnostics.map(d => [d.fileName, d.code, d.category, d.startPosition, d.text]),
        [
            ["/p/a.ts", 2322, 1, { line: 0, character: 6 }, "Type 'string' is not assignable to type 'number'."],
            [
                "/p/a.ts",
                2345,
                1,
                { line: 2, character: 2 },
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
            ],
        ],
    );
    assert.equal(result.files.has("/p/out/a.js"), false);
});

test("reports config errors without a file", async () => {
    const result = await tsc(["-p", "/p/missing.json"], { files: project, diagnostics: "json" });
    assert.equal(result.exitCode, 1);
    assert.deepEqual(result.diagnostics, [
        { pos: -1, end: -1, code: 5058, category: 1, text: "The specified path does not exist: '/p/missing.json'." },
    ]);
});

test("checks the DOM lib and a clean program", async () => {
    const result = await tsc(["--noEmit", "--lib", "es2022,dom", "--strict", "/m.ts"], {
        files: { "/m.ts": "const el: HTMLElement | null = document.querySelector('div');\nexport const tag = el?.tagName;\n" },
    });
    assert.equal(result.stdout, "");
    assert.equal(result.exitCode, 0);
});

test("reads and writes the real file system", async () => {
    const dir = mkdtempSync(join(tmpdir(), "ts-rust-wasm-"));
    try {
        writeFileSync(join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions: { outDir: "out" } }));
        writeFileSync(join(dir, "b.ts"), "export const answer: number = 42;\n");
        const result = await tsc([], { cwd: dir });
        assert.equal(result.stdout, "");
        assert.equal(result.exitCode, 0);
        assert.equal(readFileSync(join(dir, "out", "b.js"), "utf8"), "export const answer = 42;\n");
    } finally {
        rmSync(dir, { recursive: true, force: true });
    }
});

test("refuses watch mode", async () => {
    const result = await tsc(["--watch"], { files: project, cwd: "/p" });
    assert.equal(result.exitCode, 1);
    assert.match(result.stderr, /--watch is not supported/);
});
