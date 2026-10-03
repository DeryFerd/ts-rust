// One Node run (node.js `tsc`), on the thread that calls `runRequest`:
// node-worker.js, or the calling thread under Bun.

import * as fs from "node:fs";
import { dirname } from "node:path";
import { memoryFileSystem, runTsc } from "./core.js";

/** Go's syscall error texts, by Node error code. */
const ERRNO_TEXT = {
    EACCES: "permission denied",
    EEXIST: "file exists",
    EISDIR: "is a directory",
    ELOOP: "too many levels of symbolic links",
    ENAMETOOLONG: "file name too long",
    ENOENT: "no such file or directory",
    ENOSPC: "no space left on device",
    ENOTDIR: "not a directory",
    EPERM: "operation not permitted",
    EROFS: "read-only file system",
};

/** Go's `*fs.PathError` text: `open /a.js: permission denied`. */
function goError(op, path, error) {
    return `${op} ${path}: ${ERRNO_TEXT[error.code] ?? error.message}`;
}

/** The real file system through node:fs, for `runTsc`. */
export function nodeFileSystem() {
    const kind = entry =>
        entry.isDirectory() ? "directory" : entry.isFile() ? "file" : entry.isSymbolicLink() ? "symlink" : "other";
    return {
        readFile(path) {
            try {
                return fs.readFileSync(path);
            } catch {
                return undefined;
            }
        },
        stat(path) {
            try {
                const stat = fs.statSync(path, { bigint: true });
                return {
                    isDirectory: stat.isDirectory(),
                    isFile: stat.isFile(),
                    size: Number(stat.size),
                    mtimeNs: stat.mtimeNs,
                };
            } catch {
                return undefined;
            }
        },
        readDirectory(path) {
            try {
                return fs.readdirSync(path, { withFileTypes: true }).map(entry => ({ name: entry.name, kind: kind(entry) }));
            } catch {
                return undefined;
            }
        },
        realpath(path) {
            try {
                return fs.realpathSync.native(path).replaceAll("\\", "/");
            } catch {
                return undefined;
            }
        },
        // As Go's osvfs writeFile: write, and when that fails, make the
        // directory and write again.
        writeFile(path, data, append) {
            const write = () => (append ? fs.appendFileSync : fs.writeFileSync)(path, data);
            try {
                return write();
            } catch {
                // Make the directory below.
            }
            try {
                fs.mkdirSync(dirname(path), { recursive: true });
            } catch (error) {
                return goError("mkdir", error.path ?? dirname(path), error);
            }
            try {
                return write();
            } catch (error) {
                return goError("open", path, error);
            }
        },
        remove(path) {
            try {
                fs.rmSync(path, { recursive: true, force: true });
            } catch {
                return false;
            }
        },
        chtimes(path, atimeNs, mtimeNs) {
            try {
                const stat = fs.statSync(path, { bigint: true });
                const seconds = ns => Number(ns) / 1e9;
                fs.utimesSync(path, seconds(atimeNs ?? stat.atimeNs), seconds(mtimeNs ?? stat.mtimeNs));
            } catch (error) {
                return goError("chtimes", path, error);
            }
        },
    };
}

/** Go's osvfs check: the file system ignores case when the executable is also found with its case swapped. */
function caseInsensitive() {
    const swapped = process.execPath.replace(/\w/g, c => (c === c.toUpperCase() ? c.toLowerCase() : c.toUpperCase()));
    return swapped !== process.execPath && fs.existsSync(swapped);
}

const pauseCell = new Int32Array(new SharedArrayBuffer(4));

/**
 * Writes each chunk to fd `fd` in full, and drops the rest of the output
 * once its reader has gone (EPIPE). The fd can be non-blocking: a Node
 * process that opens `process.stdout` on a pipe makes it so, for every
 * process that shares the pipe. Then a write can be short, or fail with
 * EAGAIN while the reader is slow, and this waits 1 ms and writes again.
 */
function streamTo(fd) {
    let open = true;
    return chunk => {
        let at = 0;
        while (open && at < chunk.length) {
            try {
                at += fs.writeSync(fd, chunk, at, chunk.length - at);
            } catch (error) {
                if (error.code === "EAGAIN") Atomics.wait(pauseCell, 0, 0, 1);
                else if (error.code === "EPIPE") open = false;
                else throw error;
            }
        }
    };
}

/**
 * Runs one request of node.js `tsc` and returns its result: `{ exitCode,
 * diagnostics, stdout, stderr, files }`, or `{ error, stderr }` when the run
 * crashed.
 */
export function runRequest({ module, args, cwd, files, env, diagnosticsJson, tty, stream }) {
    const memory = files ? memoryFileSystem(files) : undefined;
    const stdout = [];
    const stderr = [];
    try {
        const { exitCode, diagnostics } = runTsc(module, {
            args,
            cwd,
            fs: memory ?? nodeFileSystem(),
            env,
            diagnosticsJson,
            caseInsensitive: memory ? false : caseInsensitive(),
            tty,
            stdout: stream ? streamTo(1) : chunk => stdout.push(chunk),
            stderr: stream ? streamTo(2) : chunk => stderr.push(chunk),
        });
        return {
            exitCode,
            diagnostics,
            stdout: Buffer.concat(stdout).toString(),
            stderr: Buffer.concat(stderr).toString(),
            files: memory?.files,
        };
    } catch (error) {
        return { error: String(error?.message ?? error), stderr: error?.stderr ?? Buffer.concat(stderr).toString() };
    }
}
