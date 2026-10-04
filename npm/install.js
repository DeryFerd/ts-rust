// Postinstall of the goport `typescript` and `tsc-rs` packages: lib/install.js. Go's package has
// no install script; this is the only file the port adds to Go's layout.
//
// The bin (bin/tsc, or bin/tsc-rs) is Go's JS launcher: it starts Node, finds the platform
// package and execs its native tsc. The Node start costs about 22 ms on every run. On POSIX this
// script replaces the bin with a relative symlink to the native tsc, so it runs without Node, as
// esbuild's install script does. It is a symlink, not a copy or a hard link: the native tsc
// reads the lib files from the dir of its real path (Go's noembed build), and through the
// symlink that stays the platform package's lib dir.
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
    if (out !== `Version ${pkg.version}`) {
        throw new Error(`${exe} reports "${out}", not "Version ${pkg.version}"`);
    }
    const target = path.relative(fs.realpathSync(path.dirname(binPath)), fs.realpathSync(exe));
    const tmp = `${binPath}.${process.pid}.tmp`;
    fs.rmSync(tmp, { force: true });
    fs.symlinkSync(target, tmp);
    fs.renameSync(tmp, binPath);
}

try {
    useNativeBin();
}
catch (e) {
    console.warn(`${pkg.name}: ${path.relative(pkgDir, binPath)} keeps the Node launcher: ${e instanceof Error ? e.message : e}`);
}
