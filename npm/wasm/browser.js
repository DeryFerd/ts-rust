// Browser, Deno and worker entry. Runs are in memory: the files are given
// as a map from absolute path to text. In a browser, call `tsc` from a Web
// Worker: Chrome does not let a page's main thread make an instance of a
// module over 8 MB synchronously, and a run would block the page.
// loadModule works on any thread.

import { memoryFileSystem, runTsc } from "./core.js";

export { memoryFileSystem, runTsc };

let modulePromise;

/**
 * The compiled module. `source` is where to load it from: a URL, a
 * Response, the bytes or a compiled `WebAssembly.Module`. The default is
 * `ts_rust.wasm` next to this file. The first call that succeeds decides;
 * later calls return the same module. After a failed load, the next call
 * tries again.
 */
export function loadModule(source) {
    modulePromise ??= compile(source ?? new URL("./ts_rust.wasm", import.meta.url)).catch(error => {
        modulePromise = undefined;
        throw error;
    });
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
    try {
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
    } catch (error) {
        // Chrome: "WebAssembly.Instance is disallowed on the main thread".
        if (error instanceof RangeError && typeof document !== "undefined" && /main thread/.test(error.message)) {
            throw new Error("ts-rust: call tsc from a Web Worker, not from the page's main thread", { cause: error });
        }
        throw error;
    }
}

function decode(chunks) {
    const decoder = new TextDecoder();
    return chunks.map(chunk => decoder.decode(chunk, { stream: true })).join("") + decoder.decode();
}
