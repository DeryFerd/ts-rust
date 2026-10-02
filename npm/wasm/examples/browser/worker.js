// Runs tsc for main.js, off the page's main thread: Chrome does not let the
// main thread make the instance, and a run would block the page.

import { loadModule, tsc } from "../../browser.js";

// Compile the module now, so the first check does not wait for it. A load
// error shows on the first check, which tries again.
loadModule().catch(() => {});

onmessage = async ({ data: { id, source, lib } }) => {
    let start = performance.now();
    try {
        // The wait for the download and compile, on the first message.
        await loadModule();
        const loadMs = performance.now() - start;
        start = performance.now();
        const args = ["--strict", "--target", "es2022", "--pretty", "false", "index.ts"];
        if (lib) args.push("--lib", lib);
        const result = await tsc(args, { files: { "/app/index.ts": source }, cwd: "/app" });
        postMessage({
            id,
            exitCode: result.exitCode,
            diagnostics: result.stdout + result.stderr,
            js: result.files.get("/app/index.js") ?? "",
            loadMs,
            ms: performance.now() - start,
        });
    } catch (error) {
        postMessage({ id, error: `${error.message}\n${error.stderr ?? ""}`, ms: performance.now() - start });
    }
};
