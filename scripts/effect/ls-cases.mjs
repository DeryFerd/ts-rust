#!/usr/bin/env node
// Replays the language service baselines that effect-tsgo commits against any LSP server:
// quick fixes (<case>.quickfixes.txt), refactors (.refactors.txt), document symbols (.symbols.txt)
// and inlay hints (inlayHints/*.baseline). Each case starts `<server> --lsp --stdio` on a small
// project made as the Go harness makes it, sends the requests the Go runner sends, formats the
// answers as the Go baseline writers do, and compares the text with the committed baseline.
//
// usage: node scripts/effect/ls-cases.mjs --server <tsc> [--effect-repo DIR] [--kinds K,...]
//          [--versions effect-v4,effect-v3] [--filter SUBSTR] [--out DIR] [--jobs N] [--timeout S]
//   --kinds      quickfixes,refactors,symbols,inlay (default: all)
//   --effect-repo  effect-tsgo checkout with `pnpm install` done in testdata/tests/effect-v4 and
//                effect-v3 (default target/continuation-r97-goport/effect051/effect-tsgo-0511)
// Writes <out>/summary.json (per case: same, diff or error) and, for each case that is not same,
// <out>/<kind>/<version>/<case>.actual and .diff. Exit 0 when every case is same, 1 otherwise.
//
// Go sources (effect-tsgo 47cb1ed7): internal/effecttest/runner.go (parseTestUnits, DefaultTsConfig),
// quickfix_runner.go, quickfix_baseline.go, refactor_runner.go, refactor_baseline.go,
// document_symbols_runner.go, document_symbols_baseline.go, inlay_hints_test.go,
// inlay_hints_baseline_test.go, etstesthooks/init.go (which Effect version is mounted),
// internal/bundledeffect/effect.go (MountEffect), _patches/typescript/010-fourslash-fourslash.patch
// (GetQuickFixesForDiagnostics, ApplyQuickFix, GetRefactorActionsForRange, ApplyRefactorAction), and
// TypeScript tsc/internal/fourslash (getCapabilitiesWithDefaults, openFile, applyTextEdits) and
// tsc/internal/testrunner/test_case_parser.go (unit split).
//
// Differences from the Go harness, by design:
// - Real files in <out>/projects/<kind>/<version>/<case>/ stand for the Go test VFS root "/". The Go
//   harness mounts flat copies of the profile's packages (repoctl fixtures.ts, testfixtures.tar.gz);
//   this tool makes the same flat copies once in <out>/fixtures/<profile>/node_modules and links the
//   mounted packages into each case. A package found from inside a copy can be any package of the
//   profile, not only the mounted ones (no case depends on that). Answers are normalized back: the case
//   dir becomes "/", the fixture copies become /node_modules/<pkg>/, and lib files beside the server
//   binary become bundled:///libs/<name>.
// - Edits are applied to the client copy only. Go also sends them to the server and then undoes them;
//   both leave the server with the original text.
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { parseArgs } from "node:util";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
if (["help", "-h", "--help"].includes(process.argv[2])) {
  const head = fs.readFileSync(fileURLToPath(import.meta.url), "utf8").split("\n").slice(1);
  console.log(head.slice(0, head.findIndex((l) => !l.startsWith("//"))).map((l) => l.replace(/^\/\/ ?/, "")).join("\n"));
  process.exit(0);
}
const { values: args } = parseArgs({
  options: {
    server: { type: "string" },
    "effect-repo": { type: "string" },
    kinds: { type: "string", default: "quickfixes,refactors,symbols,inlay" },
    versions: { type: "string", default: "effect-v4,effect-v3" },
    filter: { type: "string", default: "" },
    out: { type: "string", default: path.join(os.tmpdir(), "effect-ls-cases") },
    jobs: { type: "string", default: String(Math.max(1, Math.min(8, os.availableParallelism() - 2))) },
    timeout: { type: "string", default: "120" },
  },
});
if (!args.server) {
  console.error("--server is required");
  process.exit(2);
}
const SERVER = fs.realpathSync(args.server);
const SERVER_DIR = path.dirname(SERVER);
// Work data lives in the main checkout's target dir, also when this runs from a worktree.
const mainRoot = root.includes("/target/worktrees/") ? root.slice(0, root.indexOf("/target/worktrees/")) : root;
const EFFECT_REPO = fs.realpathSync(args["effect-repo"] ?? path.join(mainRoot, "target/continuation-r97-goport/effect051/effect-tsgo-0511"));
const REFERENCE = path.join(EFFECT_REPO, "testdata/baselines/reference");
const TIMEOUT_MS = Number(args.timeout) * 1000;
fs.mkdirSync(args.out, { recursive: true });
const OUT = fs.realpathSync(args.out);

// Go internal/effecttest/runner.go DefaultTsConfig.
const DEFAULT_TSCONFIG = `{
  "compilerOptions": {
    "skipLibCheck": true,
    "plugins": [
      {
        "name": "@effect/language-service",
        "ignoreEffectErrorsInTscExitCode": true,
        "skipDisabledOptimization": true,
        "diagnosticSeverity": {
          "experimentalApiUsage": "off",
          "unstableApiUsage": "off",
          "apiStabilityLeak": "off"
        }
      }
    ]
  }
}`;

const OPTION_RE = /^\/{2}\s*@(\w+)\s*:\s*([^\r\n]*)/;

// Go effecttest.parseTestUnits: split on @filename lines; leading empty lines of a unit are dropped.
function parseTestUnits(content, defaultName) {
  const units = [];
  let name = "";
  let cur = null;
  for (const line of content.split(/\r?\n/)) {
    const m = OPTION_RE.exec(line);
    if (m && m[1].toLowerCase() === "filename") {
      if (name && cur) units.push({ name, content: cur });
      name = m[2].trim();
      cur = null;
      continue;
    }
    cur = cur ? cur + "\n" + line : line || null;
  }
  if (name) units.push({ name, content: cur ?? "" });
  else if (cur) units.push({ name: defaultName, content: cur });
  return units;
}

// Go testrunner.ParseTestFilesAndSymlinksWithOptions with AllowImplicitFirstFile (fourslash): the
// file text the fourslash client opens. Other `// @x: y` lines are options and leave the text.
function fourslashFiles(text) {
  const files = [];
  let name = null;
  let content = "";
  let seen = false;
  for (const line of text.split(/\r?\n/)) {
    const m = OPTION_RE.exec(line);
    if (m) {
      if (m[1].toLowerCase() === "filename") {
        if (name !== null) files.push({ name, content });
        name = m[2].trim();
        content = "";
        seen = false;
      }
      continue;
    }
    if (seen) content += "\n";
    seen = true;
    content += line;
  }
  if (name !== null) files.push({ name, content });
  return files;
}

// Go tspath.GetNormalizedAbsolutePath(name, "/.src") for the names the cases use.
const absName = (name) => path.posix.normalize(name.startsWith("/") ? name : "/.src/" + name);
const isConfig = (name) => /(tsconfig|jsconfig)\.json$/i.test(name);

// Go etstesthooks prepareTestFS: which Effect install (if any) the fourslash VFS gets.
function mountVersion(contents) {
  let effect = false, vitest = false, v3 = false, v4 = false;
  for (const c of contents) {
    if (c.includes('from "effect')) effect = true;
    if (c.includes("vitest")) vitest = true;
    if (c.startsWith("// @effect-v3") || c.includes("\n// @effect-v3")) v3 = true;
    if (c.startsWith("// @effect-v4") || c.includes("\n// @effect-v4")) v4 = true;
  }
  if (!effect && !vitest && !v3 && !v4) return null;
  return { version: v3 ? "effect-v3" : "effect-v4", vitest };
}

// repoctl fixtures.ts createFixtureArchive: per profile, package.json and a flat copy (symlinks
// followed) of each dependency of its package.json.
const FIXTURES = path.join(OUT, "fixtures");
function prepareFixtures(profiles) {
  for (const profile of profiles) {
    const src = path.join(EFFECT_REPO, "testdata/tests", profile);
    const dst = path.join(FIXTURES, profile);
    if (fs.existsSync(path.join(dst, ".done"))) continue;
    fs.rmSync(dst, { recursive: true, force: true });
    fs.mkdirSync(dst, { recursive: true });
    fs.copyFileSync(path.join(src, "package.json"), path.join(dst, "package.json"));
    for (const pkg of Object.keys(JSON.parse(fs.readFileSync(path.join(src, "package.json"), "utf8")).dependencies ?? {})) {
      fs.cpSync(fs.realpathSync(path.join(src, "node_modules", pkg)), path.join(dst, "node_modules", pkg), { recursive: true, dereference: true });
    }
    fs.writeFileSync(path.join(dst, ".done"), "");
  }
}

// Go bundledeffect.MountEffect / MountVitest: packages under /node_modules, /.src/package.json.
function mount(dir, version, vitest) {
  const src = path.join(FIXTURES, version);
  const pkgs = ["effect", "pure-rand", "@standard-schema/spec", "fast-check", "@types/node"];
  if (vitest) pkgs.push("vitest", "@vitest/runner", "@effect/vitest");
  for (const p of pkgs) {
    const from = path.join(src, "node_modules", p);
    const to = path.join(dir, "node_modules", p);
    if (!fs.existsSync(from)) throw new Error(`package not installed at ${from}`);
    if (fs.existsSync(to)) continue;
    fs.mkdirSync(path.dirname(to), { recursive: true });
    fs.symlinkSync(from, to);
  }
  fs.mkdirSync(path.join(dir, ".src"), { recursive: true });
  fs.copyFileSync(path.join(src, "package.json"), path.join(dir, ".src/package.json"));
}

// Writes virtual files under dir. A unit inside a mounted package (Go: one more file in that
// package's VFS dir) turns the package link into a copy first, so the shared fixture stays as is.
function writeFiles(dir, files) {
  for (const f of files) {
    const target = path.join(dir, f.name);
    const rel = path.relative(dir, path.dirname(target));
    let p = dir;
    for (const seg of rel.split(path.sep).filter(Boolean)) {
      p = path.join(p, seg);
      if (fs.existsSync(p) && fs.lstatSync(p).isSymbolicLink()) {
        const from = fs.realpathSync(p);
        fs.unlinkSync(p);
        fs.cpSync(from, p, { recursive: true, dereference: true });
      }
    }
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, f.content);
  }
}

// ---------------------------------------------------------------------------
// LSP client
// ---------------------------------------------------------------------------

class Server {
  constructor(cwd, capabilities, preferences = null) {
    this.preferences = preferences;
    this.proc = spawn(SERVER, ["--lsp", "--stdio"], { cwd, stdio: ["pipe", "pipe", "pipe"], env: { ...process.env, GOPORT_LAUNCH: "0" } });
    this.buf = Buffer.alloc(0);
    this.pending = new Map();
    this.nextId = 1;
    this.stderr = "";
    this.exited = null;
    this.proc.stderr.on("data", (d) => { if (this.stderr.length < 65536) this.stderr += d; });
    this.proc.on("exit", (code, signal) => {
      this.exited = { code, signal };
      for (const { reject } of this.pending.values()) reject(new Error(`server exited (${code ?? signal}): ${this.stderr.slice(-2000)}`));
      this.pending.clear();
    });
    this.proc.stdin.on("error", () => {});
    this.proc.stdout.on("data", (chunk) => this.onData(chunk));
    this.capabilities = capabilities;
  }
  onData(chunk) {
    this.buf = Buffer.concat([this.buf, chunk]);
    for (;;) {
      const sep = this.buf.indexOf("\r\n\r\n");
      if (sep < 0) return;
      const len = Number(/Content-Length: (\d+)/i.exec(this.buf.subarray(0, sep).toString())[1]);
      if (this.buf.length < sep + 4 + len) return;
      const msg = JSON.parse(this.buf.subarray(sep + 4, sep + 4 + len).toString("utf8"));
      this.buf = this.buf.subarray(sep + 4 + len);
      if (msg.method && msg.id !== undefined) this.onServerRequest(msg);
      else if (msg.id !== undefined && this.pending.has(msg.id)) {
        const { resolve, reject, timer } = this.pending.get(msg.id);
        clearTimeout(timer);
        this.pending.delete(msg.id);
        if (msg.error) reject(new Error(`${msg.error.code}: ${msg.error.message}`));
        else resolve(msg.result);
      }
    }
  }
  // Go fourslash handleServerRequest: preferences for the "js/ts" section, null for others.
  onServerRequest(msg) {
    let result = null;
    if (msg.method === "workspace/configuration") {
      result = (msg.params?.items ?? []).map((item) => (item.section === "js/ts" ? this.preferences : null));
    }
    this.send({ jsonrpc: "2.0", id: msg.id, result });
  }
  send(msg) {
    const body = Buffer.from(JSON.stringify(msg), "utf8");
    this.proc.stdin.write(`Content-Length: ${body.length}\r\n\r\n`);
    this.proc.stdin.write(body);
  }
  request(method, params) {
    if (this.exited) return Promise.reject(new Error(`server exited (${this.exited.code ?? this.exited.signal}): ${this.stderr.slice(-2000)}`));
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`${method} timed out after ${TIMEOUT_MS / 1000} s`));
      }, TIMEOUT_MS);
      this.pending.set(id, { resolve, reject, timer });
      this.send({ jsonrpc: "2.0", id, method, params });
    });
  }
  notify(method, params) {
    this.send({ jsonrpc: "2.0", method, params });
  }
  async start(rootDir) {
    const result = await this.request("initialize", {
      processId: process.pid,
      rootUri: pathToFileURL(rootDir).href,
      locale: "en-US",
      capabilities: this.capabilities,
      initializationOptions: { codeLensShowLocationsCommandName: "typescript.showCodeLensLocations" },
    });
    this.encoding = result?.capabilities?.positionEncoding ?? "utf-16";
    this.notify("initialized", {});
    return result;
  }
  async stop() {
    try {
      await Promise.race([this.request("shutdown"), new Promise((r) => setTimeout(r, 5000))]);
      this.notify("exit");
    } catch {}
    setTimeout(() => this.proc.kill("SIGKILL"), 5000).unref();
  }
}

// Go fourslash getCapabilitiesWithDefaults(nil) at pin 673a5f17d713.
function capabilities(hierarchicalSymbols = true) {
  const formats = ["markdown", "plaintext"];
  const diag = { relatedInformation: true, tagSupport: { valueSet: [1, 2] } };
  return {
    general: { positionEncodings: ["utf-8"] },
    experimental: { hoverVerbosityLevel: true },
    textDocument: {
      completion: {
        completionItem: { snippetSupport: false, commitCharactersSupport: true, preselectSupport: true, labelDetailsSupport: false, insertReplaceSupport: true, documentationFormat: formats },
        completionList: { itemDefaults: ["commitCharacters", "editRange"] },
      },
      diagnostic: diag,
      publishDiagnostics: diag,
      semanticTokens: {
        requests: { full: true },
        tokenTypes: ["namespace", "class", "enum", "interface", "struct", "typeParameter", "type", "parameter", "variable", "property", "enumMember", "decorator", "event", "function", "method", "macro", "label", "comment", "string", "keyword", "number", "regexp", "operator"],
        tokenModifiers: ["declaration", "definition", "readonly", "static", "deprecated", "abstract", "async", "modification", "documentation", "defaultLibrary", "local"],
        formats: ["relative"],
      },
      definition: { linkSupport: true },
      typeDefinition: { linkSupport: true },
      implementation: { linkSupport: true },
      hover: { contentFormat: formats },
      signatureHelp: { signatureInformation: { documentationFormat: formats, parameterInformation: { labelOffsetSupport: true }, activeParameterSupport: true }, contextSupport: true },
      documentSymbol: { hierarchicalDocumentSymbolSupport: hierarchicalSymbols },
      foldingRange: { rangeLimit: 5000, foldingRangeKind: { valueSet: ["comment", "imports", "region"] } },
    },
    workspace: { fileOperations: { willRename: true }, workspaceEdit: { documentChanges: true, resourceOperations: ["rename"] }, configuration: true },
  };
}

// Go fourslash getLanguageKind.
function languageId(name) {
  if (/\.(d\.)?[cm]?ts$/.test(name)) return "typescript";
  if (/\.[cm]?js$/.test(name)) return "javascript";
  if (/\.jsx$/.test(name)) return "javascriptreact";
  if (/\.tsx$/.test(name)) return "typescriptreact";
  if (/\.json$/.test(name)) return "json";
  return "typescript";
}

// ---------------------------------------------------------------------------
// Text, positions, edits
// ---------------------------------------------------------------------------

function lineStarts(buf) {
  const starts = [0];
  for (let i = 0; i < buf.length; i++) {
    const c = buf[i];
    if (c === 13) {
      if (buf[i + 1] === 10) i++;
      starts.push(i + 1);
    } else if (c === 10) starts.push(i + 1);
  }
  return starts;
}

// Byte offset of an LSP position in buf, for the negotiated encoding.
function offsetOf(buf, starts, pos, encoding) {
  const line = Math.min(pos.line, starts.length - 1);
  const start = starts[line];
  const end = line + 1 < starts.length ? starts[line + 1] : buf.length;
  if (encoding === "utf-8") return Math.min(start + pos.character, end);
  const text = buf.subarray(start, end).toString("utf8");
  let units = 0, bytes = 0;
  for (const ch of text) {
    if (units >= pos.character) break;
    units += ch.length;
    bytes += Buffer.byteLength(ch);
  }
  return start + bytes;
}

// Go fourslash applyTextEdits: sort by start (stable), apply from the last edit.
function applyEdits(text, edits, encoding) {
  let buf = Buffer.from(text, "utf8");
  const starts = lineStarts(buf);
  const spans = edits.map((e, i) => ({ i, s: offsetOf(buf, starts, e.range.start, encoding), e: offsetOf(buf, starts, e.range.end, encoding), t: e.newText }));
  spans.sort((a, b) => a.s - b.s || a.i - b.i);
  for (const sp of spans.reverse()) buf = Buffer.concat([buf.subarray(0, sp.s), Buffer.from(sp.t, "utf8"), buf.subarray(sp.e)]);
  return buf.toString("utf8");
}

// Go strconv.Quote (the %q verb).
function goQuote(s) {
  let out = '"';
  for (const ch of s) {
    const cp = ch.codePointAt(0);
    if (ch === '"' || ch === "\\") out += "\\" + ch;
    else if (cp >= 0x20 && cp < 0x7f) out += ch;
    else if (cp === 7) out += "\\a";
    else if (cp === 8) out += "\\b";
    else if (cp === 12) out += "\\f";
    else if (cp === 10) out += "\\n";
    else if (cp === 13) out += "\\r";
    else if (cp === 9) out += "\\t";
    else if (cp === 11) out += "\\v";
    else if (cp < 0x20 || cp === 0x7f) out += "\\x" + cp.toString(16).padStart(2, "0");
    else if (cp >= 0x80 && /[\p{L}\p{M}\p{N}\p{P}\p{S}]/u.test(ch)) out += ch;
    else if (cp < 0x10000) out += "\\u" + cp.toString(16).padStart(4, "0");
    else out += "\\U" + cp.toString(16).padStart(8, "0");
  }
  return out + '"';
}

// Virtual name <-> case dir.
class Project {
  constructor(dir) {
    this.dir = dir;
    this.dirUri = pathToFileURL(dir).href;
  }
  uri(name) {
    return pathToFileURL(path.join(this.dir, name)).href;
  }
  name(uri) {
    return uri.startsWith(this.dirUri + "/") ? decodeURIComponent(uri.slice(this.dirUri.length)) : null;
  }
  // Answers in Go test VFS form.
  normalize(text) {
    let s = text.split(this.dirUri + "/").join("file:///").split(this.dir + "/").join("/");
    for (const profile of ["effect-v4", "effect-v3"]) {
      const modules = path.join(FIXTURES, profile, "node_modules");
      s = s.split(pathToFileURL(modules).href + "/").join("file:///node_modules/").split(modules + "/").join("/node_modules/");
    }
    s = s.split(pathToFileURL(SERVER_DIR).href + "/lib.").join("bundled:///libs/lib.");
    return s;
  }
}

function openAll(server, project, files) {
  for (const f of files) {
    server.notify("textDocument/didOpen", { textDocument: { uri: project.uri(f.name), languageId: languageId(f.name), version: 1, text: f.content } });
  }
}

// ---------------------------------------------------------------------------
// Fourslash cases (quick fixes, refactors)
// ---------------------------------------------------------------------------

// The fourslash text that RunEffectQuickFixTest and RunEffectRefactorTest build, and its files.
function fourslashCase(file) {
  const units = parseTestUnits(fs.readFileSync(file, "utf8"), path.basename(file));
  let text = "";
  if (!units.some((u) => isConfig(absName(u.name)))) text += `// @filename: /.src/tsconfig.json\n${DEFAULT_TSCONFIG}\n`;
  const testFiles = [];
  for (const u of units) {
    const n = absName(u.name);
    text += `// @filename: ${n}\n${u.content}\n`;
    if (!isConfig(n)) testFiles.push(n);
  }
  return { units, files: fourslashFiles(text), testFiles };
}

function setupFourslash(dir, files) {
  fs.rmSync(dir, { recursive: true, force: true });
  fs.mkdirSync(dir, { recursive: true });
  const m = mountVersion(files.map((f) => f.content));
  if (m) mount(dir, m.version, m.vitest);
  writeFiles(dir, files);
  return m;
}

const kindOf = (a) => a?.kind;
const quickFixes = (actions) => (actions ?? []).filter((a) => a && a.title !== undefined && kindOf(a) === "quickfix");
const refactors = (actions) => (actions ?? []).filter((a) => a && a.title !== undefined && typeof kindOf(a) === "string" && kindOf(a).startsWith("refactor."));

// Go fourslash ApplyQuickFix / ApplyRefactorAction: the edits of edit.changes, per URI in order.
function applyAction(action, project, texts, encoding) {
  const changes = action.edit?.changes;
  if (!changes || Object.keys(changes).length === 0) return [];
  const out = [];
  for (const uri of Object.keys(changes).sort()) {
    const name = project.name(uri);
    const before = name !== null && texts.has(name) ? texts.get(name) : null;
    const after = applyEdits(before ?? "", changes[uri], encoding);
    out.push({ uri, before: before ?? "", after, created: before === null });
  }
  return out;
}

function writeChanges(lines, changes, project) {
  const sorted = [...changes].sort((a, b) => (a.uri < b.uri ? -1 : a.uri > b.uri ? 1 : 0));
  for (const c of sorted) {
    lines.push(`\n--- ${project.normalize(c.uri)} ---\n`);
    const body = c.created ? "(file created)\n" + c.after : c.after;
    lines.push(body.endsWith("\n") ? body : body + "\n");
  }
}

const diagCode = (d) => (d.code === undefined || d.code === null ? "?" : String(d.code));
const diagMessage = (d) => (typeof d.message === "string" ? d.message : d.message?.value ?? "");
const isDisableStyle = (t) => t.startsWith("Disable ") && (t.endsWith(" for this line") || t.endsWith(" for entire file"));

async function runQuickFixes(c) {
  const { files, testFiles } = fourslashCase(c.file);
  setupFourslash(c.dir, files);
  const project = new Project(c.dir);
  const texts = new Map(files.map((f) => [f.name, f.content]));
  const server = new Server(c.dir, capabilities(), null);
  try {
    await server.start(c.dir);
    openAll(server, project, files);
    const inventory = [];
    const results = [];
    let n = 0;
    for (const name of testFiles) {
      const uri = project.uri(name);
      const report = await server.request("textDocument/diagnostic", { textDocument: { uri } });
      const diags = [...(report?.items ?? [])];
      const code = (d) => (typeof d.code === "number" ? d.code : 0);
      diags.sort((a, b) => a.range.start.line - b.range.start.line || a.range.start.character - b.range.start.character || code(a) - code(b));
      for (const d of diags) {
        const params = { textDocument: { uri }, range: d.range, context: { diagnostics: [d], only: ["quickfix"] } };
        const fixes = quickFixes(await server.request("textDocument/codeAction", params));
        const id = `D${++n}`;
        inventory.push({ id, d, titles: fixes.map((f) => f.title) });
        for (let i = 0; i < fixes.length; i++) {
          if (isDisableStyle(fixes[i].title)) {
            results.push({ id, i, title: fixes[i].title, skipped: true });
            continue;
          }
          const again = quickFixes(await server.request("textDocument/codeAction", params));
          if (i >= again.length) throw new Error(`quick fix index ${i} out of range (have ${again.length} fixes)`);
          results.push({ id, i, title: again[i].title, changes: applyAction(again[i], project, texts, server.encoding) });
        }
      }
    }
    // Go generateQuickFixBaseline.
    const out = ["=== Quick Fix Inventory ===\n"];
    if (!inventory.length) out.push("(no diagnostics)\n");
    for (const e of inventory) {
      const r = e.d.range;
      out.push(`\n[${e.id}] (${r.start.line + 1}:${r.start.character + 1}-${r.end.line + 1}:${r.end.character + 1}) TS${diagCode(e.d)}: ${diagMessage(e.d)}\n`);
      if (!e.titles.length) out.push("  (no quick fixes)\n");
      e.titles.forEach((t, i) => out.push(`  Fix ${i}: ${goQuote(t)}\n`));
    }
    out.push("\n=== Quick Fix Application Results ===\n");
    if (!results.length) out.push("(no quick fixes to apply)\n");
    for (const r of results) {
      out.push(`\n=== [${r.id}] Fix ${r.i}: ${goQuote(r.title)} ===\n`);
      if (r.skipped) out.push("skipped by default\n");
      else if (!r.changes.length) out.push("(no changes)\n");
      else writeChanges(out, r.changes, project);
    }
    return project.normalize(out.join(""));
  } finally {
    await server.stop();
  }
}

// Go refactor_runner.go parseRefactorComment.
function parseRefactorComment(content) {
  const first = content.split("\n", 1)[0].trim();
  const prefix = /^\/\/\s*refactor:\s*/;
  if (!prefix.test(first)) return [];
  const ranges = [];
  for (let part of first.replace(prefix, "").split(",")) {
    part = part.trim();
    let m;
    if ((m = /^(\d+):(\d+)-(\d+):(\d+)$/.exec(part))) {
      ranges.push({ start: { line: +m[1] - 1, character: +m[2] - 1 }, end: { line: +m[3] - 1, character: +m[4] - 1 } });
    } else if ((m = /^(\d+):(\d+)$/.exec(part))) {
      const pos = { line: +m[1] - 1, character: +m[2] - 1 };
      ranges.push({ start: pos, end: { ...pos } });
    }
  }
  return ranges;
}

async function runRefactors(c) {
  const { files, testFiles } = fourslashCase(c.file);
  const ranges = parseRefactorComment(fs.readFileSync(c.file, "utf8"));
  setupFourslash(c.dir, files);
  const project = new Project(c.dir);
  const texts = new Map(files.map((f) => [f.name, f.content]));
  const server = new Server(c.dir, capabilities(), null);
  try {
    await server.start(c.dir);
    openAll(server, project, files);
    const inventory = [];
    const results = [];
    let n = 0;
    if (ranges.length && testFiles.length) {
      const uri = project.uri(testFiles[0]);
      for (const range of ranges) {
        const params = { textDocument: { uri }, range, context: { diagnostics: [], only: ["refactor"] } };
        const actions = refactors(await server.request("textDocument/codeAction", params));
        const id = `R${++n}`;
        const desc = `${range.start.line + 1}:${range.start.character + 1}-${range.end.line + 1}:${range.end.character + 1}`;
        inventory.push({ id, desc, actions: actions.map((a) => ({ title: a.title, kind: a.kind })) });
        for (let i = 0; i < actions.length; i++) {
          const again = refactors(await server.request("textDocument/codeAction", params));
          if (i >= again.length) throw new Error(`refactor index ${i} out of range (have ${again.length} actions)`);
          results.push({ id, i, title: again[i].title, changes: applyAction(again[i], project, texts, server.encoding) });
        }
      }
    }
    if (testFiles.length) inventory.push({ id: `R${++n}`, desc: "empty (0:0-0:0)", actions: [] });
    // Go generateRefactorBaseline.
    const out = ["=== Refactor Inventory ===\n"];
    if (!inventory.length) out.push("(no selections)\n");
    for (const e of inventory) {
      out.push(`\n[${e.id}] selection: ${goQuote(e.desc)}\n`);
      if (!e.actions.length) out.push("  (no refactors)\n");
      e.actions.forEach((a, i) => out.push(`  Refactor ${i}: ${goQuote(a.title)} (${a.kind})\n`));
    }
    out.push("\n=== Refactor Application Results ===\n");
    if (!results.length) out.push("(no refactors to apply)\n");
    for (const r of results) {
      out.push(`\n=== [${r.id}] Refactor ${r.i}: ${goQuote(r.title)} ===\n`);
      if (!r.changes.length) out.push("(no changes)\n");
      else writeChanges(out, r.changes, project);
    }
    return project.normalize(out.join(""));
  } finally {
    await server.stop();
  }
}

// ---------------------------------------------------------------------------
// Document symbols
// ---------------------------------------------------------------------------

const SYMBOL_KINDS = ["", "File", "Module", "Namespace", "Package", "Class", "Method", "Property", "Field", "Constructor", "Enum", "Interface", "Function", "Variable", "Constant", "String", "Number", "Boolean", "Array", "Object", "Key", "Null", "EnumMember", "Struct", "Event", "Operator", "TypeParameter"];
const fmtRange = (r) => `${r.start.line + 1}:${r.start.character + 1}-${r.end.line + 1}:${r.end.character + 1}`;

function writeSymbolTree(out, symbols, indent) {
  for (const s of symbols) {
    const detail = s.detail !== undefined && s.detail !== null ? ` detail=${goQuote(s.detail)}` : "";
    out.push(`${"  ".repeat(indent)}(${SYMBOL_KINDS[s.kind] ?? s.kind}) ${s.name}${detail} range=${fmtRange(s.range)} selection=${fmtRange(s.selectionRange)}\n`);
    if (s.children) writeSymbolTree(out, s.children, indent + 1);
  }
}

async function runSymbols(c) {
  const units = parseTestUnits(fs.readFileSync(c.file, "utf8"), path.basename(c.file));
  fs.rmSync(c.dir, { recursive: true, force: true });
  fs.mkdirSync(c.dir, { recursive: true });
  mount(c.dir, c.version, false);
  const files = [];
  const sources = [];
  let hasConfig = false;
  let configDir = "/.src";
  for (const u of units) {
    const n = absName(u.name);
    files.push({ name: n, content: u.content });
    if (isConfig(n)) {
      hasConfig = true;
      continue;
    }
    if (n.startsWith("/node_modules/")) continue;
    if (!sources.length) configDir = path.posix.dirname(n);
    sources.push({ name: n, content: u.content });
  }
  if (!hasConfig) files.push({ name: path.posix.join(configDir, "tsconfig.json"), content: DEFAULT_TSCONFIG });
  writeFiles(c.dir, files);
  const project = new Project(c.dir);
  const answers = [];
  for (const hierarchical of [true, false]) {
    const server = new Server(c.dir, capabilities(hierarchical), null);
    try {
      await server.start(c.dir);
      for (const s of sources) server.notify("textDocument/didOpen", { textDocument: { uri: project.uri(s.name), languageId: "typescript", version: 1, text: s.content } });
      const perFile = [];
      for (const s of sources) perFile.push((await server.request("textDocument/documentSymbol", { textDocument: { uri: project.uri(s.name) } })) ?? []);
      answers.push(perFile);
    } finally {
      await server.stop();
    }
  }
  // Go generateDocumentSymbolsBaseline. With hierarchical support the answer is DocumentSymbol[];
  // without it, SymbolInformation[].
  const out = [];
  sources.forEach((s, i) => {
    out.push(`==== ${s.name} ====\n`);
    const tree = answers[0][i].filter((x) => x.selectionRange);
    out.push("\n-- hierarchical[0] --\n");
    if (!tree.length) out.push("(none)\n");
    else writeSymbolTree(out, tree, 0);
    const flat = answers[1][i].filter((x) => x.location);
    out.push("\n-- flat[0] --\n");
    if (!flat.length) out.push("(none)\n");
    for (const sym of flat) out.push(`(${SYMBOL_KINDS[sym.kind] ?? sym.kind}) ${sym.name} container=${goQuote(sym.containerName ?? "")} range=${fmtRange(sym.location.range)}\n`);
    if (i + 1 < sources.length) out.push("\n");
  });
  return project.normalize(out.join(""));
}

// ---------------------------------------------------------------------------
// Inlay hints (cases are the Go tests in internal/effecttest/inlay_hints_test.go)
// ---------------------------------------------------------------------------

function inlayCases() {
  const src = fs.readFileSync(path.join(EFFECT_REPO, "internal/effecttest/inlay_hints_test.go"), "utf8");
  const cases = [];
  for (const chunk of src.split(/\nfunc Test/).slice(1)) {
    const m = /^(\w+)\(t \*testing\.T\) \{([\s\S]*)$/.exec(chunk);
    if (!m) continue;
    const body = m[2];
    const content = /const content = `([\s\S]*?)`/.exec(body);
    if (!content) continue;
    // Every case asks with IncludeInlayFunctionLikeReturnTypeHints only; refuse a new shape.
    if (!/verifyLocalBaselineInlayHints\(t, f, content, "\/test\.ts", lsutil\.NewInlayHintUserPreferences\(lsutil\.InlayHintsPreferences\{\s*IncludeInlayFunctionLikeReturnTypeHints: core\.TSTrue,\s*\}\)\)/.test(body)) {
      throw new Error(`inlay case Test${m[1]} has a request shape this tool does not know`);
    }
    const name = m[1][0].toLowerCase() + m[1].slice(1);
    cases.push({ name, content: content[1] });
  }
  return cases;
}

// Go json field order of lsproto.InlayHint and its parts (core.StringifyJson keeps struct order).
const ORDER = {
  hint: ["position", "label", "kind", "textEdits", "tooltip", "paddingLeft", "paddingRight", "data"],
  part: ["value", "tooltip", "location", "command"],
  location: ["uri", "range"],
  range: ["start", "end"],
  position: ["line", "character"],
};
function ordered(obj, order, sub = {}) {
  const out = {};
  for (const k of [...order, ...Object.keys(obj).filter((k) => !order.includes(k))]) {
    if (obj[k] === undefined) continue;
    out[k] = sub[k] ? sub[k](obj[k]) : obj[k];
  }
  return out;
}
const goPosition = (p) => ordered(p, ORDER.position);
const goRange = (r) => ordered(r, ORDER.range, { start: goPosition, end: goPosition });
const goHint = (h) =>
  ordered(h, ORDER.hint, {
    position: goPosition,
    label: (l) => (Array.isArray(l) ? l.map((p) => ordered(p, ORDER.part, { location: (loc) => ordered(loc, ORDER.location, { range: goRange }) })) : l),
  });

async function runInlay(c) {
  const files = fourslashFiles(c.content);
  fs.rmSync(c.dir, { recursive: true, force: true });
  fs.mkdirSync(c.dir, { recursive: true });
  const m = mountVersion(files.map((f) => f.content));
  if (m) mount(c.dir, m.version, m.vitest);
  writeFiles(c.dir, files);
  const project = new Project(c.dir);
  const prefs = { inlayHints: { functionLikeReturnTypes: { enabled: true } } };
  const server = new Server(c.dir, capabilities(), null);
  try {
    await server.start(c.dir);
    openAll(server, project, files);
    // Go f.GoToFile then ConfigureWithReset: didChangeConfiguration with the "js/ts" section.
    server.preferences = prefs;
    server.notify("workspace/didChangeConfiguration", { settings: { "js/ts": prefs } });
    const text = files.find((f) => f.name === "/test.ts").content;
    const lines = text.split("\n");
    const last = lines[lines.length - 1];
    const end = { line: lines.length - 1, character: server.encoding === "utf-8" ? Buffer.byteLength(last) : last.length };
    const hints = (await server.request("textDocument/inlayHint", { textDocument: { uri: project.uri("/test.ts") }, range: { start: { line: 0, character: 0 }, end } })) ?? [];
    hints.sort((a, b) => a.position.line - b.position.line || a.position.character - b.position.character);
    const annotations = [];
    for (const hint of hints) {
      if (Array.isArray(hint.label)) {
        for (const part of hint.label) {
          const file = part.location ? project.normalize(part.location.uri) : "";
          if (part.location && /^lib\..*\.d\.ts$/.test(path.posix.basename(file))) {
            part.location.range = { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } };
          }
        }
      }
      annotations.push(`${lines[hint.position.line]}\n${" ".repeat(hint.position.character)}^\n${JSON.stringify(goHint(hint), null, 2)}`);
    }
    if (!annotations.length) annotations.push("=== No inlay hints ===");
    return project.normalize(annotations.join("\n\n"));
  } finally {
    await server.stop();
  }
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

function listTs(dir) {
  return fs.existsSync(dir) ? fs.readdirSync(dir).filter((n) => n.endsWith(".ts")).sort().map((n) => path.join(dir, n)) : [];
}

function collectCases() {
  const kinds = args.kinds.split(",").filter(Boolean);
  const versions = args.versions.split(",").filter(Boolean);
  const cases = [];
  const tests = path.join(EFFECT_REPO, "testdata/tests");
  const add = (kind, version, name, extra) => {
    if (args.filter && !name.includes(args.filter)) return;
    cases.push({ kind, version, name, dir: path.join(OUT, "projects", kind, version, name), ...extra });
  };
  for (const v of versions) {
    if (kinds.includes("quickfixes")) for (const f of listTs(path.join(tests, v))) add("quickfixes", v, path.basename(f, ".ts"), { file: f, baseline: path.join(REFERENCE, v, path.basename(f, ".ts") + ".quickfixes.txt"), run: runQuickFixes });
    if (kinds.includes("refactors")) for (const f of listTs(path.join(tests, v + "-refactors"))) add("refactors", v, path.basename(f, ".ts"), { file: f, baseline: path.join(REFERENCE, v, path.basename(f, ".ts") + ".refactors.txt"), run: runRefactors });
    if (kinds.includes("symbols")) for (const f of listTs(path.join(tests, v + "-document-symbols"))) add("symbols", v, path.basename(f, ".ts"), { file: f, baseline: path.join(REFERENCE, v, path.basename(f, ".ts") + ".symbols.txt"), run: runSymbols });
  }
  if (kinds.includes("inlay")) for (const c of inlayCases()) add("inlay", "inlayHints", c.name, { content: c.content, baseline: path.join(REFERENCE, "inlayHints", c.name + ".baseline"), run: runInlay });
  return cases;
}

function lineDiff(expected, actual) {
  const a = expected.split("\n");
  const b = actual.split("\n");
  let i = 0;
  while (i < a.length && i < b.length && a[i] === b[i]) i++;
  let j = 0;
  while (j < a.length - i && j < b.length - i && a[a.length - 1 - j] === b[b.length - 1 - j]) j++;
  const ctx = Math.max(0, i - 3);
  const out = [`@@ first difference at line ${i + 1} @@`];
  for (let k = ctx; k < i; k++) out.push(" " + a[k]);
  for (let k = i; k < a.length - j; k++) out.push("-" + a[k]);
  for (let k = i; k < b.length - j; k++) out.push("+" + b[k]);
  return out.slice(0, 400).join("\n") + "\n";
}

async function runCase(c) {
  const resultDir = path.join(OUT, c.kind, c.version);
  const started = Date.now();
  let status, detail;
  try {
    if (!fs.existsSync(c.baseline)) throw new Error(`no baseline ${path.relative(EFFECT_REPO, c.baseline)}`);
    const actual = await c.run(c);
    const expected = fs.readFileSync(c.baseline, "utf8");
    status = actual === expected ? "same" : "diff";
    if (status === "diff") {
      fs.mkdirSync(resultDir, { recursive: true });
      fs.writeFileSync(path.join(resultDir, c.name + ".actual"), actual);
      fs.writeFileSync(path.join(resultDir, c.name + ".diff"), lineDiff(expected, actual));
    }
  } catch (e) {
    status = "error";
    detail = String(e.message ?? e).slice(0, 2000);
    fs.mkdirSync(resultDir, { recursive: true });
    fs.writeFileSync(path.join(resultDir, c.name + ".error"), detail + "\n");
  }
  fs.rmSync(c.dir, { recursive: true, force: true });
  return { kind: c.kind, version: c.version, case: c.name, status, ms: Date.now() - started, ...(detail ? { detail } : {}) };
}

const cases = collectCases();
prepareFixtures(["effect-v4", "effect-v3"]);
const results = [];
let next = 0;
await Promise.all(
  Array.from({ length: Number(args.jobs) }, async () => {
    while (next < cases.length) {
      const c = cases[next++];
      const r = await runCase(c);
      results.push(r);
      if (r.status !== "same") console.log(`${r.status} ${r.kind}/${r.version}/${r.case}${r.detail ? ": " + r.detail.split("\n")[0] : ""}`);
    }
  }),
);
results.sort((a, b) => `${a.kind}/${a.version}/${a.case}`.localeCompare(`${b.kind}/${b.version}/${b.case}`));
const counts = {};
for (const r of results) {
  const k = `${r.kind}/${r.version}`;
  counts[k] ??= { cases: 0, same: 0, diff: 0, error: 0 };
  counts[k].cases++;
  counts[k][r.status]++;
}
const summary = { server: SERVER, effectRepo: EFFECT_REPO, counts, cases: results };
fs.writeFileSync(path.join(OUT, "summary.json"), JSON.stringify(summary, null, 1) + "\n");
for (const [k, v] of Object.entries(counts)) console.log(`${k}: cases ${v.cases}, same ${v.same}, diff ${v.diff}, error ${v.error}`);
process.exit(results.every((r) => r.status === "same") ? 0 : 1);
