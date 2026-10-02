#!/usr/bin/env node
// `tsc` on the real file system, through the wasm build.

import { tsc } from "../node.js";

try {
    const { exitCode } = await tsc(process.argv.slice(2), {
        env: process.env,
        tty: Boolean(process.stdout.isTTY),
        stream: true,
    });
    process.exitCode = exitCode;
} catch (error) {
    process.stderr.write(`tsc-wasm: ${error.message}\n`);
    // tsgo's exit status for a panic.
    process.exitCode = 70;
}
