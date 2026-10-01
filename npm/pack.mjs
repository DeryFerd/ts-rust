// Writes the linux-x64 npm package set in Go's layout at the pin: `typescript` (the JS
// launcher and the JS API) and `@typescript/typescript-linux-x64` (the native tsc and the
// lib files). scripts/goport/npm-pack.sh runs it; see there for the usage.
//
// It follows Herebyfile.mjs `buildNativePreviewPackages` of the Go checkout with the
// release profile "typescript" (publishAsTypescript) for the current platform only, as
// Go's local build does. With --native-bin it adds one thing to the main package: the
// postinstall npm/install.js (as lib/install.js), which swaps bin/tsc for the native tsc.
//
// usage: node npm/pack.mjs --layout <typescript|typescript-go> --go-dir <dir> --exe <tsc>
//          --libs <dir> --dist <dir> --version <v> --git-head <sha> --out <dir> [--native-bin]
//
// --layout is the pin layout (scripts/upstream/pin.py). "typescript" (microsoft/TypeScript, pin N
// on): --go-dir is <repo>/tsc, the input is <repo>/packages/typescript (it already has bin/tsc and
// lib/tsc.js), and LICENSE.txt and NOTICE.txt are at <repo>. "typescript-go": the input is
// <go-dir>/_packages/native-preview (bin/tsgo, lib/tsgo.js), with LICENSE and NOTICE.txt at <go-dir>.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseArgs } from "node:util";

const { values: args } = parseArgs({
    options: {
        layout: { type: "string" },
        "go-dir": { type: "string" },
        exe: { type: "string" },
        libs: { type: "string" },
        dist: { type: "string" },
        version: { type: "string" },
        "git-head": { type: "string" },
        out: { type: "string" },
        "native-bin": { type: "boolean", default: false },
    },
    strict: true,
});
for (const name of ["layout", "go-dir", "exe", "libs", "dist", "version", "git-head", "out"]) {
    if (!args[name]) throw new Error(`missing --${name}`);
}
const { layout, "go-dir": goDir, exe, libs, dist, version, "git-head": gitHead, out } = args;
if (layout !== "typescript" && layout !== "typescript-go") throw new Error(`unknown --layout ${layout}`);
const atN = layout === "typescript";
const root = atN ? path.dirname(goDir) : goDir;
const inputDir = atN ? path.join(root, "packages", "typescript") : path.join(goDir, "_packages", "native-preview");
const licenseFile = path.join(root, atN ? "LICENSE.txt" : "LICENSE");
const noticeFile = path.join(root, "NOTICE.txt");

// Go: Herebyfile.mjs getPlatforms (local build: only the current platform).
const nodeOs = "linux";
const nodeArch = "x64";
if (process.platform !== nodeOs || process.arch !== nodeArch) {
    throw new Error(`only ${nodeOs}-${nodeArch} is supported, not ${process.platform}-${process.arch}`);
}
const platformPackageName = `@typescript/typescript-${nodeOs}-${nodeArch}`;

// Go: Herebyfile.mjs getPublishTag (publishAsTypescript). Go's nativePreviewReleaseVersion is
// undefined at both layouts, so a version with no dev, beta or rc part is refused.
function publishTag() {
    const match = version.match(/-(dev|beta|rc)(?:[.-]|$)/);
    if (match?.[1]) return match[1] === "dev" ? "next" : match[1];
    throw new Error(`Refusing to publish 'typescript' with the latest tag from non-release version ${version}.`);
}

// Go: Herebyfile.mjs stripSourceConditions and stripConditionsFromValue
function stripConditions(value) {
    if (value == null || typeof value !== "object") return value;
    delete value["@typescript/source"];
    for (const key of Object.keys(value)) value[key] = stripConditions(value[key]);
    const keys = Object.keys(value);
    return keys.length === 1 && keys[0] === "default" ? value.default : value;
}

const writeJson = (file, value) => fs.writeFileSync(file, JSON.stringify(value, undefined, 4));

// Go: Herebyfile.mjs buildNativePreviewPackages, inputPackageJson with publishAsTypescript.
const input = JSON.parse(fs.readFileSync(path.join(inputDir, "package.json"), "utf8"));
input.version = version;
delete input.private;
input.files = [...new Set([...(input.files ?? []), "NOTICE.txt"])];
input.bin = { tsc: "./bin/tsc" };
input.description = "TypeScript is a language for application scale JavaScript development";
input.homepage = "https://www.typescriptlang.org/";
input.keywords = ["TypeScript", "Microsoft", "compiler", "language", "javascript"];
input.bugs = { url: "https://github.com/microsoft/TypeScript/issues" };
input.repository = { type: "git", url: "https://github.com/microsoft/TypeScript.git" };
delete input.scripts;
delete input.devDependencies;
for (const field of ["exports", "imports"]) input[field] = stripConditions(input[field]);
input.gitHead = gitHead;
input.publishConfig = { access: "public", tag: publishTag() };

fs.rmSync(out, { recursive: true, force: true });

// The main package `typescript`.
const mainDir = path.join(out, "typescript");
const mainPackage = {
    ...input,
    name: "typescript",
    optionalDependencies: { [platformPackageName]: version },
};
if (atN) {
    // Go copies the whole input but node_modules and dist; its filter sees the path from the repo.
    fs.cpSync(inputDir, mainDir, {
        recursive: true,
        filter: src => {
            const p = path.posix.join("packages/typescript", path.relative(inputDir, src).split(path.sep).join("/"));
            return !p.endsWith("/node_modules") && !p.includes("/dist");
        },
    });
}
else {
    for (const entry of ["bin", "lib", "vendor"]) {
        fs.cpSync(path.join(inputDir, entry), path.join(mainDir, entry), { recursive: true });
    }
    fs.rmSync(path.join(mainDir, "bin", "tsgo"));
    fs.renameSync(path.join(mainDir, "lib", "tsgo.js"), path.join(mainDir, "lib", "tsc.js"));
}
fs.cpSync(dist, path.join(mainDir, "dist"), { recursive: true });
fs.writeFileSync(path.join(mainDir, "bin", "tsc"), '#!/usr/bin/env node\nimport "../lib/tsc.js";\n');
fs.chmodSync(path.join(mainDir, "bin", "tsc"), 0o755);
fs.copyFileSync(path.join(inputDir, "typescript-package-readme.md"), path.join(mainDir, "README.md"));
if (args["native-bin"]) {
    // PORT: not in Go. The native bin on POSIX (npm/install.js).
    mainPackage.scripts = { postinstall: "node lib/install.js" };
    const here = path.dirname(fileURLToPath(import.meta.url));
    fs.copyFileSync(path.join(here, "install.js"), path.join(mainDir, "lib", "install.js"));
}
writeJson(path.join(mainDir, "package.json"), mainPackage);
fs.copyFileSync(licenseFile, path.join(mainDir, "LICENSE"));
fs.copyFileSync(noticeFile, path.join(mainDir, "NOTICE.txt"));

// The platform package: the lib files and the native tsc in lib/.
const platformDir = path.join(out, `typescript-${nodeOs}-${nodeArch}`);
const platformPackage = {
    ...input,
    bin: undefined,
    files: ["lib", "NOTICE.txt"],
    imports: undefined,
    dependencies: undefined,
    name: platformPackageName,
    os: [nodeOs],
    cpu: [nodeArch],
    exports: { "./package.json": "./package.json" },
};
fs.cpSync(libs, path.join(platformDir, "lib"), { recursive: true });
fs.copyFileSync(exe, path.join(platformDir, "lib", "tsc"));
fs.chmodSync(path.join(platformDir, "lib", "tsc"), 0o755);
writeJson(path.join(platformDir, "package.json"), platformPackage);
fs.copyFileSync(licenseFile, path.join(platformDir, "LICENSE"));
fs.copyFileSync(noticeFile, path.join(platformDir, "NOTICE.txt"));
fs.writeFileSync(
    path.join(platformDir, "README.md"),
    [
        `# \`${platformPackageName}\``,
        "",
        `This package provides ${nodeOs}-${nodeArch} support for [typescript](https://www.npmjs.com/package/typescript).`,
    ].join("\n") + "\n",
);
