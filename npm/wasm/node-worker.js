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

/** Writes to fd `fd`, and drops the rest of the output once its reader has gone (EPIPE). */
function streamTo(fd) {
    let open = true;
    return chunk => {
        if (!open) return;
        try {
            fs.writeSync(fd, chunk);
        } catch (error) {
            if (error.code !== "EPIPE") throw error;
            open = false;
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
