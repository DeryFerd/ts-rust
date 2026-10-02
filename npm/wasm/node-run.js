// The worker thread of one Node run (node.js `tsc`).

import * as fs from "node:fs";
import { dirname } from "node:path";
import { parentPort, workerData } from "node:worker_threads";
import { memoryFileSystem, runTsc } from "./core.js";

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
                const stat = fs.statSync(path);
                return { isDirectory: stat.isDirectory(), size: stat.size, mtimeMs: stat.mtimeMs };
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
        writeFile(path, data, append) {
            try {
                fs.mkdirSync(dirname(path), { recursive: true });
                (append ? fs.appendFileSync : fs.writeFileSync)(path, data);
            } catch {
                return false;
            }
        },
        remove(path) {
            try {
                fs.rmSync(path, { recursive: true, force: true });
            } catch {
                return false;
            }
        },
        chtimes(path, atimeMs, mtimeMs) {
            try {
                const stat = fs.statSync(path);
                fs.utimesSync(path, (atimeMs ?? stat.atimeMs) / 1000, (mtimeMs ?? stat.mtimeMs) / 1000);
            } catch {
                // Go ignores a failed chtimes of an output file too.
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

const { module, args, cwd, files, env, diagnosticsJson, tty, stream } = workerData;
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
    parentPort.postMessage({
        exitCode,
        diagnostics,
        stdout: Buffer.concat(stdout).toString(),
        stderr: Buffer.concat(stderr).toString(),
        files: memory?.files,
    });
} catch (error) {
    parentPort.postMessage({ error: String(error?.message ?? error), stderr: error?.stderr ?? Buffer.concat(stderr).toString() });
}
