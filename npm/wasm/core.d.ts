/** A position: zero-based line, and UTF-16 character in that line. */
export interface Position {
    line: number;
    character: number;
}

/**
 * A diagnostic (`diagnostics: "json"`). It is the `DiagnosticResponse` of
 * the TypeScript API: positions are UTF-16 offsets, and fields with an empty
 * value are left out.
 */
export interface Diagnostic {
    /** The file, when the diagnostic belongs to one. */
    fileName?: string;
    /** Start offset in the file, or -1. */
    pos: number;
    /** End offset in the file, or -1. */
    end: number;
    startPosition?: Position;
    endPosition?: Position;
    /** The source lines that a renderer needs to show the diagnostic. */
    sourceLines?: { line: number; text: string }[];
    /** The error code, for example 2322 for `TS2322`. */
    code: number;
    /** 0 warning, 1 error, 2 suggestion, 3 message. */
    category: 0 | 1 | 2 | 3;
    /** A code prefix other than the default `TS`. */
    source?: string;
    /** The message text. */
    text: string;
    reportsUnnecessary?: boolean;
    reportsDeprecated?: boolean;
    messageChain?: Diagnostic[];
    relatedInformation?: Diagnostic[];
}

/** A file system for `runTsc`. Paths are absolute, with `/` separators. */
export interface HostFileSystem {
    readFile(path: string): Uint8Array | string | undefined;
    /** Follows links. */
    stat(path: string): { isDirectory: boolean; size?: number; mtimeMs?: number } | undefined;
    readDirectory(path: string): { name: string; kind: "file" | "directory" | "symlink" | "other" }[] | undefined;
    realpath?(path: string): string | undefined;
    /** Returns false on failure. Makes missing parent directories. */
    writeFile?(path: string, data: Uint8Array, append: boolean): boolean | void;
    /** Removes a file or a directory tree. Returns false on failure. */
    remove?(path: string): boolean | void;
    chtimes?(path: string, atimeMs: number | undefined, mtimeMs: number | undefined): void;
}

export interface MemoryFileSystem extends HostFileSystem {
    /** Every file, written ones included. */
    files: Map<string, string>;
}

/** An in-memory file system. Writes go into the same map. */
export function memoryFileSystem(files?: Map<string, string> | Record<string, string>): MemoryFileSystem;

export interface RunOptions {
    args?: string[];
    /** Absolute, with `/` separators. Default `/`. */
    cwd?: string;
    fs: HostFileSystem;
    env?: Record<string, string | undefined>;
    stdout?(chunk: Uint8Array): void;
    stderr?(chunk: Uint8Array): void;
    /** Return the diagnostics as objects instead of printing them. */
    diagnosticsJson?: boolean;
    caseInsensitive?: boolean;
    /** stdout is a terminal: tsc then defaults to `--pretty`. */
    tty?: boolean;
}

/** Thrown by WASI `proc_exit`; `runTsc` turns it into the exit code. */
export class WasiExit extends Error {
    code: number;
}

/**
 * Runs tsc once, in a new instance of `module`, on the calling thread. A
 * crash (a trap, or running out of stack or memory) throws, with the
 * stderr text so far in `error.stderr`.
 */
export function runTsc(
    module: WebAssembly.Module,
    options: RunOptions,
): { exitCode: number; diagnostics?: Diagnostic[] };
