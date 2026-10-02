// Node entry. Each run gets its own worker thread, because the checker
// recurses deeply and a worker can have a large stack (`stackSizeMb`); the
// main thread's stack is about 1 MB. The worker makes a new instance of
// the module, which is compiled once per process.

import { readFile } from "node:fs/promises";
import { Worker } from "node:worker_threads";
export { memoryFileSystem, runTsc } from "./core.js";

const wasmUrl = new URL("./ts_rust.wasm", import.meta.url);

/** Stack size of a run's worker thread, in MB. */
const STACK_SIZE_MB = 256;

let modulePromise;

/** The compiled module, compiled on first use. */
export function loadModule() {
    modulePromise ??= readFile(wasmUrl).then(bytes => WebAssembly.compile(bytes));
    return modulePromise;
}

/**
 * Runs `tsc` with `args`.
 *
 * Without `options.files`, it reads and writes the real file system from
 * `options.cwd` (default `process.cwd()`). With `options.files` (path to
 * text, absolute paths), it reads only those files, and `result.files`
 * holds every file after the run, emitted ones included.
 *
 * Returns `{ exitCode, stdout, stderr, diagnostics?, files? }`.
 * `options.diagnostics: "json"` returns the diagnostics as objects in
 * `diagnostics` and does not print them.
 */
export async function tsc(args, options = {}) {
    const module = await loadModule();
    const files = options.files === undefined
        ? undefined
        : options.files instanceof Map
        ? options.files
        : new Map(Object.entries(options.files));
    const worker = new Worker(new URL("./node-worker.js", import.meta.url), {
        workerData: {
            module,
            args,
            cwd: toPosix(options.cwd ?? process.cwd()),
            files,
            env: options.env ?? {},
            diagnosticsJson: options.diagnostics === "json",
            tty: options.tty ?? false,
            stream: options.stream ?? false,
        },
        resourceLimits: { stackSizeMb: options.stackSizeMb ?? STACK_SIZE_MB },
        stdout: !options.stream,
        stderr: !options.stream,
    });
    return new Promise((resolve, reject) => {
        let result;
        worker.on("message", message => (result = message));
        worker.on("error", reject);
        worker.on("exit", () => {
            if (!result) reject(new Error("ts-rust worker ended without a result"));
            else if (result.error) reject(Object.assign(new Error(result.error), { stderr: result.stderr }));
            else resolve(result);
        });
    });
}

/** `C:\a\b` to `C:/a/b`: tsc paths use `/`. */
function toPosix(path) {
    return path.replaceAll("\\", "/");
}
