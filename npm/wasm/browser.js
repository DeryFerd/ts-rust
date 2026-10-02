// Browser, Deno and worker entry. Runs are in memory: the files are given
// as a map from absolute path to text. The checker recurses deeply, so run
// it in a Web Worker: a page's main thread has a small stack, and Chrome
// does not compile a large module synchronously there.

import { memoryFileSystem, runTsc } from "./core.js";

export { memoryFileSystem, runTsc };

let modulePromise;

/**
 * The compiled module. `source` is where to load it from: a URL, a
 * Response, the bytes or a compiled `WebAssembly.Module`. The default is
 * `ts_rust.wasm` next to this file. The first call decides; later calls
 * return the same module.
 */
export function loadModule(source) {
    modulePromise ??= compile(source ?? new URL("./ts_rust.wasm", import.meta.url));
    return modulePromise;
}

async function compile(source) {
    if (source instanceof WebAssembly.Module) return source;
    if (source instanceof ArrayBuffer || ArrayBuffer.isView(source)) return WebAssembly.compile(source);
    const response = source instanceof Response ? source : await fetch(source);
    if (!response.ok) throw new Error(`ts-rust: cannot load the wasm module: ${response.status} ${response.url}`);
    if (response.headers.get("content-type")?.startsWith("application/wasm")) {
        return WebAssembly.compileStreaming(response);
    }
    return WebAssembly.compile(await response.arrayBuffer());
}

/**
 * Runs `tsc` with `args` on the in-memory `options.files` (absolute path to
 * text). Returns `{ exitCode, stdout, stderr, diagnostics?, files }`, where
 * `files` holds every file after the run, emitted ones included.
 * `options.diagnostics: "json"` returns the diagnostics as objects and does
 * not print them. `options.wasm` is the `loadModule` source.
 */
export async function tsc(args, options = {}) {
    const module = await loadModule(options.wasm);
    const fs = memoryFileSystem(options.files ?? {});
    const stdout = [];
    const stderr = [];
    const { exitCode, diagnostics } = runTsc(module, {
        args,
        cwd: options.cwd ?? "/",
        fs,
        env: options.env ?? {},
        diagnosticsJson: options.diagnostics === "json",
        stdout: chunk => stdout.push(chunk),
        stderr: chunk => stderr.push(chunk),
    });
    return { exitCode, stdout: decode(stdout), stderr: decode(stderr), diagnostics, files: fs.files };
}

function decode(chunks) {
    const decoder = new TextDecoder();
    return chunks.map(chunk => decoder.decode(chunk, { stream: true })).join("") + decoder.decode();
}
