// Postinstall of the goport `typescript` and `tsc-rs` packages: lib/install.js. Go's package has
// no install script; this is the only file the port adds to Go's layout.
//
// The bin (bin/tsc, or bin/tsc-rs) is Go's JS launcher (packages/typescript/bin/tsc): it starts
// Node, finds the platform package and execs its native tsc. The Node start costs about 22 ms on
// every run. On POSIX this script rewrites the bin as a sh and JS polyglot:
//
//   #!/bin/sh
//   ":" //; p=$0; ...; exec "${p%/*}/../../@typescript/typescript-linux-x64/lib/tsc" "$@"
//   import "../lib/tsc.js";
//
// sh (the shebang, npm's .bin symlink, pnpm's shim) runs line 2, where `":" //` is the no-op `:`.
// It follows $0 through symlinks to the bin's real dir and execs the native tsc by its path
// relative to that dir, so a moved project still works. Node (`node bin/tsc`, tools that start a
// bin with process.execPath) reads line 2 as a string and a comment and runs line 3, Go's
// launcher, as with Go. The loop reads one link at a time, as pnpm's shim does, because old macOS
// has no `readlink -f`. The exec path keeps the real path of the native tsc in the platform
// package, where it reads the lib files (Go's noembed build).
//
// Every failure keeps the JS launcher, which still works. It stays on Windows (npm's cmd
// shim runs bin/tsc with Node), under Yarn (Yarn runs bins with Node), outside a
// node_modules dir (do not rewrite a source checkout), and when the native tsc does not run
// here or reports another version than this package.
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import getExePath from "#getExePath";

const pkgDir = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const pkg = JSON.parse(fs.readFileSync(path.join(pkgDir, "package.json"), "utf8"));
const binPath = path.join(pkgDir, Object.values(pkg.bin)[0]);

function keepLauncherReason() {
    if (process.platform === "win32") return "Windows";
    if (/\byarn\//.test(process.env.npm_config_user_agent ?? "")) return "Yarn";
    if (!pkgDir.split(path.sep).includes("node_modules")) return "not installed in node_modules";
    return undefined;
}

function useNativeBin() {
    if (keepLauncherReason()) return;
    const exe = getExePath();
    const out = execFileSync(exe, ["--version"], { encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }).trim();
    // tsc-rs records the version its tsc reports as tscVersion (npm/pack.mjs).
    const want = `Version ${pkg.tscVersion ?? pkg.version}`;
    if (out !== want) {
        throw new Error(`${exe} reports "${out}", not "${want}"`);
    }
    const target = path.relative(fs.realpathSync(path.dirname(binPath)), fs.realpathSync(exe));
    // The path goes in a sh "..." string on a JS line comment.
    if (/["$`\\\n\r\u2028\u2029]/.test(target)) {
        throw new Error(`cannot quote the path ${JSON.stringify(target)}`);
    }
    // p is $0 with its symlinks followed. A relative link target is relative to the link's dir.
    const resolve = [
        "p=$0; case $p in */*) ;; *) p=./$p ;; esac",
        'while [ -L "$p" ]; do t=$(readlink "$p"); case $t in /*) p=$t ;; *) p=${p%/*}/$t ;; esac; done',
    ].join("; ");
    const polyglot = `#!/bin/sh\n":" //; ${resolve}; exec "\${p%/*}/${target}" "$@"\nimport "../lib/tsc.js";\n`;
    const tmp = `${binPath}.${process.pid}.tmp`;
    fs.rmSync(tmp, { force: true });
    fs.writeFileSync(tmp, polyglot);
    fs.chmodSync(tmp, 0o755);
    fs.renameSync(tmp, binPath);
}

try {
    useNativeBin();
}
catch (e) {
    console.warn(`${pkg.name}: ${path.relative(pkgDir, binPath)} keeps the Node launcher: ${e instanceof Error ? e.message : e}`);
}
