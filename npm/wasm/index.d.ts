import type { Diagnostic } from "./core.js";

export type { Diagnostic, HostFileSystem, MemoryFileSystem, Position, RunOptions } from "./core.js";
export { memoryFileSystem, runTsc, runTscAsync } from "./core.js";

export interface TscOptions {
    /**
     * The files of an in-memory run: absolute path to text. In Node, leave
     * it out to use the real file system.
     */
    files?: Map<string, string> | Record<string, string>;
    /** The current directory. Default: `/`, or in Node without `files`, `$PWD` when it names the current directory (as tsgo does), else `process.cwd()`. */
    cwd?: string;
    /** `"json"`: return the diagnostics as objects instead of printing them. */
    diagnostics?: "text" | "json";
    env?: Record<string, string | undefined>;
    /** Node: stdout is a terminal. */
    tty?: boolean;
    /** Node: write the output to this process's stdout and stderr as it comes. */
    stream?: boolean;
    /** Node: the stack of the run's worker thread, in MB (default 256). */
    stackSizeMb?: number;
    /** Browser: where to load the module from (see `loadModule`). */
    wasm?: string | URL | Response | BufferSource | WebAssembly.Module;
}

export interface TscResult {
    exitCode: number;
    stdout: string;
    stderr: string;
    /** With `diagnostics: "json"`. */
    diagnostics?: Diagnostic[];
    /** In-memory runs: every file after the run, emitted ones included. */
    files?: Map<string, string>;
}

/** Runs `tsc` with `args`. */
export function tsc(args: string[], options?: TscOptions): Promise<TscResult>;

/** The compiled module. The browser entry takes where to load it from. */
export function loadModule(source?: TscOptions["wasm"]): Promise<WebAssembly.Module>;
