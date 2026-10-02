#!/usr/bin/env node
// `tsc` on the real file system, through the wasm build.

import { isatty } from "node:tty";
import { tsc } from "../node.js";

try {
    const { exitCode } = await tsc(process.argv.slice(2), {
        env: process.env,
        // Not `process.stdout.isTTY`: opening `process.stdout` on a pipe
        // makes the pipe non-blocking (see node-worker.js `streamTo`).
        tty: isatty(1),
        stream: true,
    });
    process.exitCode = exitCode;
} catch (error) {
    process.stderr.write(`tsc-wasm: ${error.message}\n`);
    // tsgo's exit status for a panic.
    process.exitCode = 70;
}
