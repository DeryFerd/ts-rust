// The page: sends the textarea to worker.js and shows the result.

const worker = new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
const pending = new Map();
let nextId = 0;
worker.onmessage = ({ data }) => {
    pending.get(data.id)(data);
    pending.delete(data.id);
};

/**
 * Checks `source` in the worker. Resolves to `{ exitCode, diagnostics, js,
 * loadMs, ms }` or `{ error, ms }`. `loadMs` is the wait for the module.
 */
function check(source, lib) {
    const id = nextId++;
    worker.postMessage({ id, source, lib });
    return new Promise(resolve => pending.set(id, resolve));
}

const $ = id => document.getElementById(id);

async function run() {
    $("status").textContent = "checking";
    const result = await check($("source").value, $("lib").value.trim());
    const ms = `${result.ms.toFixed(0)} ms`;
    if (result.error) {
        $("status").textContent = `crashed, ${ms}`;
        $("diagnostics").textContent = result.error;
        $("output").textContent = "";
        return;
    }
    const load = result.loadMs >= 1 ? `, module ${result.loadMs.toFixed(0)} ms` : "";
    $("status").textContent = `exit ${result.exitCode}, check ${ms}${load}`;
    $("diagnostics").textContent = result.diagnostics || "no errors";
    $("output").textContent = result.js;
}

$("check").onclick = run;
$("source").onkeydown = event => {
    if (event.key === "Enter" && (event.metaKey || event.ctrlKey)) run();
};
// For the console and tests.
globalThis.check = check;
run();
