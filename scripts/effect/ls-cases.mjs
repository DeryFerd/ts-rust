#!/usr/bin/env node
// Replays the language service baselines that effect-tsgo commits against any LSP server:
// quick fixes (<case>.quickfixes.txt), refactors (.refactors.txt), document symbols (.symbols.txt)
// and inlay hints (inlayHints/*.baseline). Each case starts `<server> --lsp --stdio` on a small
// project made as the Go harness makes it, sends the requests the Go runner sends, formats the
// answers as the Go baseline writers do, and compares the text with the committed baseline.
// Hover cases have no baseline file: the expected text is the VerifyQuickInfoAt arguments of
// internal/effecttest/hover_test.go (one case per Go test, one block per marker). Hover compares
// inflate the `pako:` payload of each Mermaid link on both sides (root decision D3: tsc-rs deflates
// with other bytes than Go's compress/zlib); nothing else is normalized.
// Completion cases have no baseline file either: each is one Go test of
// internal/effecttest/completion_test.go or of the 10 unit test files of internal/completions,
// ported by hand (source, cursor, the label filter of the fourslash_test.go helper, the Go
// assertions). The answer is "ok" when every assertion holds.
// Port refactor cases (`refactors/<profile>-port`, PORT_REFACTOR_CASES) have no Go baseline either:
// each holds its source and the answer of effect-tsgo 0.51.1, which can be an error answer.
//
// usage: node scripts/effect/ls-cases.mjs --server <tsc> [--effect-repo DIR] [--kinds K,...]
//          [--versions effect-v4,effect-v3] [--filter SUBSTR] [--out DIR] [--jobs N] [--timeout S]
//          [--dump DIR] [--effect-baselines]
//   --kinds      quickfixes,refactors,symbols,inlay,hover,completion (default: all)
//   --dump       completion cases also write each whole answer (sorted as the Go client sorts it)
//                to DIR/<case>.json, to compare two servers beyond the Go assertions
//   --effect-repo  effect-tsgo checkout with `pnpm install` done in testdata/tests/effect-v4 and
//                effect-v3 (default target/continuation-r97-goport/effect051/effect-tsgo-0511 in the
//                main checkout: the parent of the git common dir, or /home/theo/Code/sandbox/ts-rust
//                from an independent clone)
// Writes <out>/summary.json (per case: same, diff or error) and, for each case that is not same,
// <out>/<kind>/<version>/<case>.actual and .diff. Exit 0 when every case is same, 1 otherwise.
// scripts/effect/ls-baselines/<kind>/<version>/ holds the baselines that effect-tsgo does not commit:
// the answers of effect-tsgo 0.51.1 to the schemagen port cases (PORT_SCHEMAGEN_CASES), and the
// baselines rebased at our Go pin N prime (NP_REBASED). --effect-baselines compares the rebased cases
// with the effect-tsgo baselines instead, to check an effect-tsgo 0.51.1 build (TS 7.0.2, 7.1.0-dev or
// E0 at pin N).
//
// Go sources (effect-tsgo 47cb1ed7): internal/effecttest/runner.go (parseTestUnits, DefaultTsConfig),
// quickfix_runner.go, quickfix_baseline.go, refactor_runner.go, refactor_baseline.go,
// document_symbols_runner.go, document_symbols_baseline.go, inlay_hints_test.go,
// inlay_hints_baseline_test.go, etstesthooks/init.go (which Effect version is mounted),
// internal/bundledeffect/effect.go (MountEffect), _patches/typescript/010-fourslash-fourslash.patch
// (GetQuickFixesForDiagnostics, ApplyQuickFix, GetRefactorActionsForRange, ApplyRefactorAction), and
// TypeScript tsc/internal/fourslash (getCapabilitiesWithDefaults, openFile, applyTextEdits) and
// tsc/internal/testrunner/test_case_parser.go (unit split), tsc/internal/fourslash/test_parser.go
// (parseFileContent: markers) and fourslash.go (VerifyQuickInfoAt, verifyHoverMarkdown).
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
import { execFileSync, spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { parseArgs } from "node:util";
import zlib from "node:zlib";

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
    kinds: { type: "string", default: "quickfixes,refactors,symbols,inlay,hover,completion" },
    versions: { type: "string", default: "effect-v4,effect-v3" },
    filter: { type: "string", default: "" },
    out: { type: "string", default: path.join(os.tmpdir(), "effect-ls-cases") },
    jobs: { type: "string", default: String(Math.max(1, Math.min(8, os.availableParallelism() - 2))) },
    timeout: { type: "string", default: "120" },
    dump: { type: "string" },
    "effect-baselines": { type: "boolean", default: false },
  },
});
if (!args.server) {
  console.error("--server is required");
  process.exit(2);
}
const SERVER = fs.realpathSync(args.server);
const SERVER_DIR = path.dirname(SERVER);
// Work data lives in the main checkout's target dir: the parent of the git common dir from the main
// checkout or any worktree. An independent clone has no work data, so it uses the main checkout path
// (the remote hosts mirror it at the same path).
function mainCheckout() {
  let main = root;
  try {
    const gitArgs = ["-C", root, "rev-parse", "--path-format=absolute", "--git-common-dir"];
    main = path.dirname(execFileSync("git", gitArgs, { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim());
  } catch {}
  return fs.existsSync(path.join(main, "target/continuation-r97-goport")) ? main : "/home/theo/Code/sandbox/ts-rust";
}
const effectRepo = args["effect-repo"] ?? path.join(mainCheckout(), "target/continuation-r97-goport/effect051/effect-tsgo-0511");
if (!fs.existsSync(path.join(effectRepo, "testdata/baselines/reference"))) {
  console.error(`no effect-tsgo checkout at ${effectRepo}; pass --effect-repo DIR`);
  process.exit(2);
}
const EFFECT_REPO = fs.realpathSync(effectRepo);
const REFERENCE = path.join(EFFECT_REPO, "testdata/baselines/reference");
const LS_BASELINES = path.join(root, "scripts/effect/ls-baselines");
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
// `content` is the case text (a port case has no file).
function fourslashCase(file, content = fs.readFileSync(file, "utf8")) {
  const units = parseTestUnits(content, path.basename(file));
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
  const content = c.content ?? fs.readFileSync(c.file, "utf8");
  const { files, testFiles } = fourslashCase(c.file, content);
  const ranges = parseRefactorComment(content);
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
        const id = `R${++n}`;
        const desc = `${range.start.line + 1}:${range.start.character + 1}-${range.end.line + 1}:${range.end.character + 1}`;
        let actions;
        try {
          actions = refactors(await server.request("textDocument/codeAction", params));
        } catch (e) {
          // A port case records the error answer of the request (a Go panic answers an internal error).
          if (!c.recordErrors) throw e;
          inventory.push({ id, desc, actions: [], error: e.message });
          continue;
        }
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
      if (e.error !== undefined) out.push(`  (error) ${e.error}\n`);
      else if (!e.actions.length) out.push("  (no refactors)\n");
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

// Schemagen refactor cases that the Go harness does not have (version `<profile>-port`, as the port
// refactor cases): self-recursive types, which no effect-tsgo 0.51.1 baseline has. The structural
// schemagen hoists a named type only after its members, so each self-reference processes the type
// again until the depth limit, and the action inserts `undefined /* maximum depth exceeded */`
// (structural.go processType, Process). The baseline of each is the answer of effect-tsgo 0.51.1
// (TS 7.0.2, 7.1.0-dev.20261006.1 and E0 at pin N give the same text), in
// ls-baselines/refactors/<profile>-port/<name>.refactors.txt.
// A v3 case mounts effect-v3 through its `// @effect-v3` line (mountVersion).
const recursiveSchemaContent = (marker, line) => `// refactor: ${line}:18-${line}:22, ${line + 5}:13-${line + 5}:17
${marker}import * as Schema from "effect/Schema"

export interface Tree {
  value: number
  children: Array<Tree>
}

export type Json = string | number | boolean | null | ReadonlyArray<Json> | { readonly [key: string]: Json }
`;
const PORT_SCHEMAGEN_CASES = [
  { name: "structuralTypeToSchema_selfRecursive", profile: "effect-v4", content: recursiveSchemaContent("", 4) },
  { name: "structuralTypeToSchema_selfRecursive", profile: "effect-v3", content: recursiveSchemaContent("// @effect-v3\n", 5) },
];

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
// Hover (cases are the Go tests in internal/effecttest/hover_test.go)
// ---------------------------------------------------------------------------

// A Go string expression: interpreted literals joined by `+` (the only forms hover_test.go uses).
function goStringExpr(src, i) {
  let out = "";
  for (;;) {
    while (/\s/.test(src[i])) i++;
    if (src[i] !== '"') throw new Error(`hover_test.go: string literal expected at ${src.slice(i, i + 40)}`);
    let j = i + 1;
    while (src[j] !== '"') j += src[j] === "\\" ? 2 : 1;
    out += JSON.parse(src.slice(i, j + 1));
    i = j + 1;
    let k = i;
    while (/\s/.test(src[k])) k++;
    if (src[k] !== "+") return { value: out, end: i };
    i = k + 1;
  }
}

// Each Go test: its fourslash content and its VerifyQuickInfoAt calls (marker, text, documentation).
// A call inside `for _, marker := range []string{...}` runs once per marker of the list.
function hoverCases() {
  const src = fs.readFileSync(path.join(EFFECT_REPO, "internal/effecttest/hover_test.go"), "utf8");
  const cases = [];
  for (const chunk of src.split(/\nfunc Test/).slice(1)) {
    const m = /^(\w+)\(t \*testing\.T\) \{([\s\S]*)$/.exec(chunk);
    if (!m) continue;
    const body = m[2];
    const content = /const content = `([\s\S]*?)`/.exec(body);
    if (!content) continue;
    if (!/fourslash\.NewFourslash\(t, nil \/\*capabilities\*\/, content\)/.test(body)) {
      throw new Error(`hover case Test${m[1]} has a setup this tool does not know`);
    }
    const checks = [];
    const call = "f.VerifyQuickInfoAt(t,";
    for (let at = body.indexOf(call); at >= 0; at = body.indexOf(call, at + 1)) {
      let i = at + call.length;
      while (/\s/.test(body[i])) i++;
      let markers;
      if (body[i] === '"') {
        const name = goStringExpr(body, i);
        markers = [name.value];
        i = name.end;
      } else {
        const ident = /^\w+/.exec(body.slice(i))[0];
        const loop = new RegExp(`for _, ${ident} := range \\[\\]string\\{([^}]*)\\}`).exec(body.slice(0, at));
        if (!loop) throw new Error(`hover case Test${m[1]}: no marker list for ${ident}`);
        markers = [...loop[1].matchAll(/"([^"]*)"/g)].map((x) => x[1]);
        i += ident.length;
      }
      i = body.indexOf(",", i) + 1;
      const text = goStringExpr(body, i);
      i = body.indexOf(",", text.end) + 1;
      const doc = goStringExpr(body, i);
      for (const marker of markers) checks.push({ marker, text: text.value, doc: doc.value });
    }
    if (!checks.length) continue;
    const name = m[1][0].toLowerCase() + m[1].slice(1);
    cases.push({ name, content: content[1], checks });
  }
  return cases;
}

// Go fourslash parseFileContent (test_parser.go): the file text without its markers, and the
// marker offsets (bytes in the Go text; the cases are ASCII, so string offsets here).
function stripMarkers(raw) {
  const lines = raw.split("\n");
  const content = lines.every((l) => !l.length || l[0] === " ") ? lines.map((l) => l.slice(1)).join("\n") : raw;
  let out = "";
  const markers = {};
  let diff = 0;
  let last = 0;
  let open = null;
  let state = "none";
  let prev = content[0];
  const flush = (end) => { out += content.slice(last, end === -1 ? undefined : end); };
  for (let i = 1; i < content.length; i++) {
    const cur = content[i];
    if (state === "none") {
      if ((prev === "[" && cur === "|") || (prev === "|" && cur === "]")) {
        flush(i - 1);
        last = i + 1;
        diff += 2;
      } else if (prev === "/" && cur === "*" && content[i + 1] !== "/") {
        state = "slashStar";
        open = { position: i - 1 - diff, source: i - 1 };
      } else if (prev === "{" && cur === "|") {
        state = "object";
        open = { position: i - 1 - diff, source: i - 1 };
        flush(i - 1);
      }
    } else if (state === "object") {
      if (prev === "|" && cur === "}") {
        last = i + 1;
        diff += i + 1 - open.source;
        open = null;
        state = "none";
      }
    } else if (state === "slashStar") {
      if (prev === "*" && cur === "/") {
        markers[content.slice(open.source + 2, i - 1).trim()] = open.position;
        flush(open.source);
        last = i + 1;
        diff += i + 1 - open.source;
        open = null;
        state = "none";
      } else if (!/[0-9A-Za-z$_]/.test(cur) && !(cur === "*" && content[i + 1] === "/")) {
        flush(i);
        last = i;
        open = null;
        state = "none";
      }
    }
    // Go keeps the previous character across a line break.
    if (cur === "\n" || cur === "\r") continue;
    prev = i >= last ? cur : "\uFFFD"; // Go utf8.RuneError
  }
  flush(-1);
  return { text: out, markers };
}

async function runHover(c) {
  const files = fourslashFiles(c.content).map((f) => {
    const { text, markers } = stripMarkers(f.content);
    return { name: f.name, content: text, markers };
  });
  fs.rmSync(c.dir, { recursive: true, force: true });
  fs.mkdirSync(c.dir, { recursive: true });
  const m = mountVersion(files.map((f) => f.content));
  if (m) mount(c.dir, m.version, m.vitest);
  writeFiles(c.dir, files);
  const project = new Project(c.dir);
  const server = new Server(c.dir, capabilities(), null);
  const out = [];
  try {
    await server.start(c.dir);
    openAll(server, project, files);
    for (const check of c.checks) {
      const file = files.find((f) => check.marker in f.markers);
      if (!file) throw new Error(`no marker ${check.marker}`);
      const before = file.content.slice(0, file.markers[check.marker]);
      const line = before.split("\n").length - 1;
      const col = before.slice(before.lastIndexOf("\n") + 1);
      const character = server.encoding === "utf-8" ? Buffer.byteLength(col) : col.length;
      const hover = await server.request("textDocument/hover", { textDocument: { uri: project.uri(file.name) }, position: { line, character } });
      const contents = hover?.contents;
      const value = hover === null || hover === undefined ? "(no hover)" : typeof contents?.value === "string" && contents.kind !== undefined ? contents.value : `(not markup content) ${JSON.stringify(contents)}`;
      out.push(`=== marker ${check.marker} ===\n${value}\n`);
    }
    return project.normalize(out.join("\n"));
  } finally {
    await server.stop();
  }
}

// Root decision D3: each Mermaid link's `pako:<base64url>` becomes `pako:<inflated payload>`.
const inflateMermaid = (text) =>
  text.replace(/pako:([A-Za-z0-9_-]+)/g, (_, b64) => `pako:<${zlib.inflateSync(Buffer.from(b64, "base64url")).toString("utf8")}>`);

// Go fourslash verifyHoverMarkdown: the markdown each VerifyQuickInfoAt expects.
const hoverExpected = (c) => c.checks.map((check) => `=== marker ${check.marker} ===\n\`\`\`typescript\n${check.text}\n\`\`\`\n${check.doc}\n`).join("\n");

// ---------------------------------------------------------------------------
// Completion (cases are the Go tests of internal/effecttest/completion_test.go and of the 10 unit
// test files of internal/completions, ported by hand: source, cursor, the label filter of the
// fourslash_test.go helper and the Go assertions)
// ---------------------------------------------------------------------------

// fourslash_test.go completionTestTsConfig.
const COMPLETION_TSCONFIG = `{
  "compilerOptions": {
    "strict": true,
    "target": "ESNext",
    "module": "NodeNext",
    "moduleResolution": "NodeNext",
    "plugins": [
      {
        "name": "@effect/language-service"
      }
    ]
  }
}`;
// fourslash_test.go contextSelfInClassesItemsWithPackageJSON.
const HARNESS_PACKAGE_JSON = `{
	  "name": "@effect/harness-effect-v4"
	}`;

// The fourslash_test.go filters (`<name>Items` helpers).
const DURATION_UNITS = ["nanos", "micros", "millis", "seconds", "minutes", "hours", "days", "weeks"];
const COMPLETION_FILTERS = {
  fnFunctionStar: (l) => l.startsWith('fn("') || l === "fn(function*(){})" || l === "fnUntraced(function*(){})",
  effectJsdocComment: (l) => l === "@effect-identifier",
  effectCodegensComment: (l) => l === "@effect-codegens",
  effectDiagnosticsComment: (l) => l === "@effect-diagnostics" || l === "@effect-diagnostics-next-line",
  durationInput: (l) => DURATION_UNITS.includes(l),
  effectSelfInClasses: (l) => l.startsWith("Service<") || l.startsWith('Tag("'),
  contextSelfInClasses: (l) => l.startsWith('Tag("'),
  contextSelfInClassesWithPackageJSON: (l) => l.startsWith('Tag("') || l.startsWith("Service<"),
  effectSQLModelSelfInClasses: (l) => l.startsWith("Class<"),
  rpcMakeClasses: (l) => l.startsWith('make("'),
  schemaBrand: (l) => l.startsWith('brand("'),
  all: () => true,
};

// Go stringutil.CompareStringsCaseInsensitiveThenSensitive, as ls.CompareCompletionEntries uses it.
function compareCaseInsensitiveThenSensitive(a, b) {
  const ca = [...a], cb = [...b];
  for (let i = 0; i < Math.min(ca.length, cb.length); i++) {
    const la = ca[i].toLowerCase().codePointAt(0), lb = cb[i].toLowerCase().codePointAt(0);
    if (la !== lb) return la < lb ? -1 : 1;
  }
  if (ca.length !== cb.length) return ca.length < cb.length ? -1 : 1;
  const ba = Buffer.from(a), bb = Buffer.from(b);
  return Buffer.compare(ba, bb);
}

// Names of rules.All and codegens.All in the Go tree, sorted (sort.Strings) and joined with ",".
function goSortedNames(kind) {
  if (kind === "codegens") {
    const src = fs.readFileSync(path.join(EFFECT_REPO, "internal/codegens/codegens.go"), "utf8");
    return [...src.matchAll(/Name:\s+"([^"]+)"/g)].map((m) => m[1]).sort().join(",");
  }
  const dir = path.join(EFFECT_REPO, "internal/rules");
  const all = /var All = \[\]rule\.Rule\{([\s\S]*?)\n\}/.exec(fs.readFileSync(path.join(dir, "rules.go"), "utf8"))[1];
  const idents = [...all.matchAll(/^\s*(\w+),/gm)].map((m) => m[1]);
  const names = new Map();
  for (const f of fs.readdirSync(dir).filter((n) => n.endsWith(".go") && !n.endsWith("_test.go"))) {
    for (const m of fs.readFileSync(path.join(dir, f), "utf8").matchAll(/var (\w+) = rule\.Rule\{\s*Name:\s+"([^"]+)"/g)) names.set(m[1], m[2]);
  }
  return idents.map((id) => {
    if (!names.has(id)) throw new Error(`rules.All entry ${id}: no Name found`);
    return names.get(id);
  }).sort().join(",");
}

// Assertion helpers: each returns the Go t.Errorf/t.Fatalf texts, empty when it holds. `nil` is Go
// `items != nil` failing (the filter keeps nothing, so Go has nil).
const C = {
  nil: () => (items) => (items.length ? [`expected nil, got ${items.length} items`] : []),
  len: (n) => (items) => (items.length !== n ? [`FATAL expected ${n} items, got ${items.length}`] : []),
  label: (i, want) => (items) => (items[i]?.label !== want ? [`item[${i}].Label = ${JSON.stringify(items[i]?.label)}, want ${JSON.stringify(want)}`] : []),
  hasLabel: (want) => (items) => (items.some((it) => it.label === want) ? [] : [`expected completion label ${JSON.stringify(want)}`]),
  noLabel: (label) => (items) => (items.some((it) => it.label === label) ? [`did not expect ${JSON.stringify(label)}`] : []),
  text: (i, want) => (items) => (newText(items[i]) !== want ? [`item[${i}] insert text = ${JSON.stringify(newText(items[i]))}, want ${JSON.stringify(want)}`] : []),
  textAffix: (i, prefix, suffix) => (items) => {
    const t = newText(items[i]);
    return typeof t === "string" && t.startsWith(prefix) && t.endsWith(suffix) ? [] : [`item[${i}].insertText = ${JSON.stringify(t)}`];
  },
  textHas: (i, sub) => (items) => (typeof newText(items[i]) === "string" && newText(items[i]).includes(sub) ? [] : [`item[${i}] insert text does not contain ${JSON.stringify(sub)}: ${JSON.stringify(newText(items[i]))}`]),
  allTextHas: (sub) => (items) => items.flatMap((it, i) => (newText(it)?.includes(sub) ? [] : [`item[${i}].insertText = ${JSON.stringify(newText(it))}, want ${sub}`])),
  start: (i, line, character) => (items) => {
    const s = items[i]?.textEdit?.range?.start;
    return s?.line === line && s?.character === character ? [] : [`replacement range start = ${JSON.stringify(s)}, want ${line}:${character}`];
  },
};
const newText = (item) => item?.textEdit?.newText;

// One case per Go test. pos: a number, or [needle, extra] for strings.Index(source, needle) + extra.
// setup: "unit" (completionItemsAt), "pkg" (completionItemsAtWithPackageJSON with the harness
// package.json), or a fourslash content with a /*1*/ marker (effecttest/completion_test.go).
function completionCases() {
  const end = (s) => s.length;
  const T = (file, name, source, pos, filter, ...checks) => ({ file, name, source, pos: pos ?? end(source), filter, checks, setup: "unit" });
  const P = (file, name, source, pos, filter, ...checks) => ({ ...T(file, name, source, pos, filter, ...checks), setup: "pkg" });
  const sortedRules = () => goSortedNames("rules");
  const sortedCodegens = () => goSortedNames("codegens");
  const cases = [];
  const comment = (file, prefix, filter, n, extra) => {
    const first = prefix === "EffectDiagnosticsComment" ? "@effect-diagnostics" : prefix === "EffectCodegensComment" ? "@effect-codegens" : "@effect-identifier";
    cases.push(
      T(file, `Test${prefix}_DoubleSlash`, "// @", null, filter, C.len(n), C.label(0, first), ...(n === 2 ? [C.label(1, "@effect-diagnostics-next-line")] : [])),
      T(file, `Test${prefix}_SlashStar`, "/* @", null, filter, C.len(n), ...(prefix === "EffectCodegensComment" ? [] : [C.label(0, first)]), ...(n === 2 ? [C.label(1, "@effect-diagnostics-next-line")] : [])),
      T(file, `Test${prefix}_JSDocComment`, "/** @", null, filter, C.len(n)),
      T(file, `Test${prefix}_ExtraWhitespace`, "//  @  ", null, filter, C.len(n)),
      T(file, `Test${prefix}_NoAtSymbol`, prefix === "EffectJsdocComment" ? "// some comment" : "// some comment without at", null, filter, C.nil()),
      T(file, `Test${prefix}_AtOutsideComment`, "const x = @", null, filter, C.nil()),
      ...extra,
      T(file, `Test${prefix}_ReplacementSpanStartsAtAt`, "// @", null, filter, C.len(n), C.start(0, 0, 3)),
      T(file, `Test${prefix}_MultilineWithCommentOnSecondLine`, "const x = 1\n// @", null, filter, C.len(n), C.start(0, 1, 3)),
    );
  };

  // context_self_in_classes_test.go
  {
    const f = "context_self_in_classes_test.go";
    cases.push(
      T(f, "TestContextSelfInClasses_NotInExtendsClause", 'import * as Context from "effect/Context"\nconst x = Context.Tag', null, "contextSelfInClasses", C.nil()),
      T(f, "TestContextSelfInClasses_NotInClass", 'import * as Context from "effect/Context"\nconst x = Context.', null, "contextSelfInClasses", C.nil()),
      T(f, "TestContextSelfInClasses_EmptySource", "", 0, "contextSelfInClasses", C.nil()),
      T(f, "TestContextSelfInClasses_InsideImportDeclaration", 'import { Context } from "effect"', end("import { Context"), "contextSelfInClasses", C.nil()),
      T(f, "TestContextSelfInClasses_InterfaceNotClass", "interface Foo extends Bar", null, "contextSelfInClasses", C.nil()),
      T(f, "TestContextSelfInClasses_AnonymousClass", "const x = class extends Context.Tag", null, "contextSelfInClasses", C.nil()),
      P(f, "TestContextSelfInClasses_V4NamespaceImport", 'import * as Context from "effect/Context"\n\nexport class MyService extends Context.', null, "contextSelfInClassesWithPackageJSON",
        C.len(2), C.label(0, "Service<MyService, {}>"), C.textAffix(0, 'Context.Service<MyService, {${0}}>()("', '"){}'),
        C.label(1, "Service<MyService>({ make })"), C.text(1, 'Context.Service<MyService>()("@effect/harness-effect-v4/test/MyService", { make: ${0} }){}')),
      P(f, "TestContextSelfInClasses_V4DirectImport", 'import { Service } from "effect/Context"\n\nexport class MyService extends Service', null, "contextSelfInClassesWithPackageJSON",
        C.len(2), C.textAffix(0, 'Service<MyService, {${0}}>()("', '"){}'), C.text(1, 'Service<MyService>()("@effect/harness-effect-v4/test/MyService", { make: ${0} }){}')),
      P(f, "TestContextSelfInClasses_V4IdentifierKeyPattern",
        '// @test-config { "keyPatterns": [ { "pattern": "package-identifier", "target": "service" } ] }\nimport * as Context from "effect/Context"\n\nexport class MyService extends Context.', null,
        "contextSelfInClassesWithPackageJSON", C.len(2), C.allTextHas('"@effect/harness-effect-v4/test/MyService"')),
    );
    const src = 'import { Effect, Stream } from "effect"\nimport * as Context from "effect/Context"\n\nclass Foo extends Context.S\n\nStream.unwrap(Effect.gen(function*() {\n\tconst a = yield* Foo\n\n\treturn Stream.succeed(a.count)\n}))';
    cases.push(P(f, "TestContextSelfInClasses_V4MiddleOfIdentifier", src, src.indexOf("Context.S") + "Context.S".length, "contextSelfInClassesWithPackageJSON",
      C.len(2), C.label(0, "Service<Foo, {}>"), C.label(1, "Service<Foo>({ make })"), C.textAffix(0, 'Context.Service<Foo, {${0}}>()("', '"){}')));
  }

  // duration_input_test.go
  {
    const f = "duration_input_test.go";
    const decl = "type D = `${number} nanos` | `${number} micros` | `${number} millis` | `${number} seconds` | `${number} minutes` | `${number} hours` | `${number} days` | `${number} weeks`\nconst value: D = \"";
    cases.push(
      T(f, "TestDurationInput_CursorOutsideString", "const x = 123", null, "durationInput", C.nil()),
      T(f, "TestDurationInput_CursorOnIdentifier", "const foo = bar", null, "durationInput", C.nil()),
      T(f, "TestDurationInput_CursorAtOpeningQuote", 'const x: string = "hello"', end("const x: string = "), "durationInput", C.nil()),
      T(f, "TestDurationInput_CursorAtClosingQuote", 'const x: string = "hello"', end('const x: string = "hello"'), "durationInput", C.nil()),
      T(f, "TestDurationInput_EmptySource", "", 0, "durationInput", C.nil()),
      T(f, "TestDurationInput_CursorInComment", "// some comment", null, "durationInput", C.nil()),
      T(f, "TestDurationInput_CursorBeforeString", 'const x = "hello"', end("const x ="), "durationInput", C.nil()),
      T(f, "TestDurationInput_DurationUnitsCount", decl + '"', end(decl), "durationInput", C.len(8), ...DURATION_UNITS.map((u) => C.hasLabel(u))),
    );
  }

  // effect_codegens_comment_test.go, effect_diagnostics_comment_test.go, effect_jsdoc_comment_test.go
  comment("effect_codegens_comment_test.go", "EffectCodegensComment", "effectCodegensComment", 1, [
    T("effect_codegens_comment_test.go", "TestEffectCodegensComment_SnippetContainsSortedCodegenNames", "// @", null, "effectCodegensComment", C.len(1), (items) => C.textHas(0, sortedCodegens())(items)),
  ]);
  comment("effect_diagnostics_comment_test.go", "EffectDiagnosticsComment", "effectDiagnosticsComment", 2, [
    T("effect_diagnostics_comment_test.go", "TestEffectDiagnosticsComment_SnippetContainsSortedRuleNames", "// @", null, "effectDiagnosticsComment", C.len(2), (items) => C.textHas(0, sortedRules())(items)),
    T("effect_diagnostics_comment_test.go", "TestEffectDiagnosticsComment_SnippetContainsSeverityChoices", "// @", null, "effectDiagnosticsComment", C.len(2), C.textHas(0, "off,warning,error,message,suggestion")),
  ]);
  comment("effect_jsdoc_comment_test.go", "EffectJsdocComment", "effectJsdocComment", 1, [
    T("effect_jsdoc_comment_test.go", "TestEffectJsdocComment_InsertText", "// @", null, "effectJsdocComment", C.len(1), C.text(0, "@effect-identifier")),
  ]);

  // The four files of v3-only extends completions: the same six nil cases each.
  const extendsNil = (file, prefix, filter, mod, accessed, importLine) => [
    T(file, `Test${prefix}_NotInExtendsClause`, `${importLine}\nconst x = ${mod}.${accessed}`, null, filter, C.nil()),
    T(file, `Test${prefix}_NotInClass`, `${importLine}\nconst x = ${mod}.`, null, filter, C.nil()),
    T(file, `Test${prefix}_EmptySource`, "", 0, filter, C.nil()),
    T(file, `Test${prefix}_InterfaceNotClass`, "interface Foo extends Bar", null, filter, C.nil()),
    T(file, `Test${prefix}_AnonymousClass`, `const x = class extends ${mod}.${accessed}`, null, filter, C.nil()),
  ];
  cases.push(
    ...extendsNil("effect_rpc_make_classes_test.go", "RpcMakeClasses", "rpcMakeClasses", "Rpc", "make", 'import * as Rpc from "@effect/rpc"'),
    T("effect_rpc_make_classes_test.go", "TestRpcMakeClasses_InsideImportDeclaration", 'import { Rpc } from "@effect/rpc"', end("import { Rpc"), "rpcMakeClasses", C.nil()),
    ...extendsNil("effect_self_in_classes_test.go", "EffectSelfInClasses", "effectSelfInClasses", "Effect", "Service", 'import * as Effect from "effect/Effect"'),
    T("effect_self_in_classes_test.go", "TestEffectSelfInClasses_InsideImportDeclaration", 'import { Effect } from "effect"', end("import { Effect"), "effectSelfInClasses", C.nil()),
    ...extendsNil("effect_sql_model_self_in_classes_test.go", "EffectSqlModelSelfInClasses", "effectSQLModelSelfInClasses", "Model", "Class", 'import * as Model from "@effect/sql/Model"'),
    T("effect_sql_model_self_in_classes_test.go", "TestEffectSqlModelSelfInClasses_InsideImportDeclaration", 'import { Model } from "@effect/sql"', end("import { Model"), "effectSQLModelSelfInClasses", C.nil()),
  );

  // fn_function_star_test.go
  {
    const f = "fn_function_star_test.go";
    const ns = 'import * as Effect from "effect/Effect"\nconst myFn = Effect.fn';
    cases.push(
      T(f, "TestFnFunctionStar_NotEffectModule", 'import * as Foo from "some-lib"\nconst x = Foo.fn', null, "fnFunctionStar", C.nil()),
      T(f, "TestFnFunctionStar_NamespaceImport_InVarDecl", ns, null, "fnFunctionStar", C.len(3), C.label(0, 'fn("myFn")'), C.label(1, "fn(function*(){})"), C.label(2, "fnUntraced(function*(){})")),
      T(f, "TestFnFunctionStar_NamedImport_InVarDecl", 'import { Effect } from "effect"\nconst myFn = Effect.fn', null, "fnFunctionStar", C.len(3), C.label(0, 'fn("myFn")')),
      T(f, "TestFnFunctionStar_NotInVarDecl", 'import * as Effect from "effect/Effect"\nEffect.fn', null, "fnFunctionStar", C.len(2), C.label(0, "fn(function*(){})"), C.label(1, "fnUntraced(function*(){})")),
      T(f, "TestFnFunctionStar_AliasedImport", 'import * as Fx from "effect/Effect"\nconst myFn = Fx.fn', null, "fnFunctionStar", C.len(3), C.label(0, 'fn("myFn")')),
      T(f, "TestFnFunctionStar_CursorAfterDot", 'import * as Effect from "effect/Effect"\nconst myFn = Effect.', null, "fnFunctionStar", C.len(3)),
      T(f, "TestFnFunctionStar_SnippetInsertText", ns, null, "fnFunctionStar", C.len(3), C.text(0, 'fn("myFn")(function*(${1}){${0}})'), C.text(1, "fn(function*(${1}){${0}})"), C.text(2, "fnUntraced(function*(${1}){${0}})")),
    );
  }

  // schema_brand_test.go
  {
    const f = "schema_brand_test.go";
    cases.push(
      T(f, "TestSchemaBrand_EmptySource", "", 0, "schemaBrand", C.nil()),
      T(f, "TestSchemaBrand_CursorAtStartOfFile", "const x = 1", 0, "schemaBrand", C.nil()),
      T(f, "TestSchemaBrand_InsideImportDeclaration", 'import { Schema } from "effect"', end("import { Schema"), "schemaBrand", C.nil()),
      T(f, "TestSchemaBrand_CursorAfterNumber", "const x = 42", null, "schemaBrand", C.nil()),
      T(f, "TestSchemaBrand_CursorAfterString", 'const x = "hello"', null, "schemaBrand", C.nil()),
    );
  }

  // internal/effecttest/completion_test.go: own fourslash content, all items.
  {
    const f = "effecttest/completion_test.go";
    const content = (plugin, file) => `// @Filename: /tsconfig.json
{
  "compilerOptions": {
    "strict": true,
    "target": "ESNext",
    "module": "NodeNext",
    "moduleResolution": "NodeNext",
    "plugins": [
      {
        ${plugin}
      }
    ]
  }
}
// @Filename: /test.ts
${file}`;
    const plain = '"name": "@effect/language-service"';
    const off = '"name": "@effect/language-service",\n        "completions": false';
    cases.push(
      { file: f, name: "TestEffectCompletionExtendsServiceMap", setup: content(plain, 'import * as Context from "effect/Context"\nclass MyService extends Context./*1*/'), filter: "all", nilFatal: true, checks: [C.hasLabel("Service<MyService, {}>"), C.hasLabel("Service<MyService>({ make })")] },
      { file: f, name: "TestEffectCompletionExtendsSchema", setup: content(plain, 'import { Schema } from "effect"\nclass Foo extends Schema./*1*/'), filter: "all", nilFatal: true, checks: [C.hasLabel("Class<Foo>"), C.hasLabel("TaggedClass<Foo>"), C.hasLabel("TaggedError<Foo>"), C.hasLabel("Error<Foo>")] },
      { file: f, name: "TestEffectCompletionDisabled", setup: content(off, 'import * as Context from "effect/Context"\nclass MyService extends Context./*1*/'), filter: "all", nilFatal: true, checks: [C.noLabel("Service<MyService, {}>"), C.noLabel("Service<MyService>({ make })")] },
    );
  }
  // Port-only cases (not Go tests): positive paths of the v3-only completions and of the v4 Model,
  // Data, Duration and non-qualified paths, which the Go tests do not reach. The label checks were
  // confirmed on E0; with --dump, two servers' whole answers can be compared.
  {
    const f = "port-only";
    const v3 = "// @effect-v3\n";
    cases.push(
      T(f, "V3EffectServiceAndTag", v3 + 'import * as Effect from "effect/Effect"\nclass MyService extends Effect.', null, "all", C.hasLabel("Service<MyService>"), C.hasLabel('Tag("MyService")'), C.hasLabel("gen(function*(){})"), C.hasLabel("fn(function*(){})")),
      T(f, "V3EffectTagNotQualified", v3 + 'import { Tag } from "effect/Effect"\nclass MyTag extends Tag', null, "all", C.hasLabel('Tag("MyTag")'), C.noLabel("Service<MyTag>")),
      T(f, "V3ContextTag", v3 + 'import * as Context from "effect/Context"\nclass MyTag extends Context.', null, "all", C.hasLabel('Tag("MyTag")'), C.noLabel("Service<MyTag, {}>")),
      T(f, "V3SchemaClasses", v3 + 'import { Schema } from "effect"\nclass Foo extends Schema.', null, "all", C.hasLabel("Class<Foo>"), C.hasLabel("TaggedError<Foo>"), C.hasLabel("TaggedClass<Foo>"), C.hasLabel("TaggedRequest<Foo>"), C.noLabel("Error<Foo>")),
      T(f, "V3SchemaBrand", v3 + 'import { Schema } from "effect"\nconst UserId = Schema.', null, "all", C.hasLabel('brand("UserId")')),
      T(f, "V3SqlModel", v3 + 'import { Model } from "@effect/sql"\nclass User extends Model.', null, "all", C.hasLabel("Class<User>")),
      T(f, "V3RpcMake", v3 + 'import { Rpc } from "@effect/rpc"\nclass GetUser extends Rpc.', null, "all", C.hasLabel('make("GetUser")')),
      T(f, "V4ModelClass", 'import { Effect } from "effect"\nclass User extends Model.', null, "all", C.hasLabel("Class<User>")),
      T(f, "V4DataClasses", 'import { Data } from "effect"\nclass MyError extends Data.', null, "all", C.hasLabel('TaggedError("MyError")'), C.hasLabel('TaggedClass("MyError")')),
      T(f, "V4SchemaNotQualified", 'import { Class } from "effect/Schema"\nclass Foo extends Class', null, "all", C.hasLabel("Class<Foo>"), C.noLabel("TaggedError<Foo>")),
      T(f, "V4DurationInEffectSleep", 'import { Effect } from "effect"\nconst program = Effect.sleep("1 ")', end('import { Effect } from "effect"\nconst program = Effect.sleep("1 '), "durationInput", C.len(8)),
      T(f, "V4GenOnLocalObject", 'import { Effect } from "effect"\nconst M = { gen: Effect.gen }\nconst x = M.', null, "all", C.hasLabel("gen(function*(){})"), C.noLabel("fn(function*(){})")),
      T(f, "V4CommentInsideBlock", 'import { Effect } from "effect"\nfunction f() {\n  /** @', null, "all", C.hasLabel("@effect-diagnostics"), C.hasLabel("@effect-codegens"), C.hasLabel("@effect-identifier")),
    );
  }
  return cases.map((c) => ({ ...c, name: c.name[0].toLowerCase() + c.name.slice(1) }));
}

async function runCompletion(c) {
  let text;
  if (c.setup === "unit" || c.setup === "pkg") {
    const marked = c.source.slice(0, c.pos) + "/*1*/" + c.source.slice(c.pos);
    text = "// @Filename: /tsconfig.json\n" + COMPLETION_TSCONFIG + "\n" + (c.setup === "pkg" ? "// @Filename: /package.json\n" + HARNESS_PACKAGE_JSON + "\n" : "") + "// @Filename: /test.ts\n" + marked;
  } else {
    text = c.setup;
  }
  const files = fourslashFiles(text).map((f) => {
    const { text: content, markers } = stripMarkers(f.content);
    return { name: f.name, content, markers };
  });
  fs.rmSync(c.dir, { recursive: true, force: true });
  fs.mkdirSync(c.dir, { recursive: true });
  const m = mountVersion(files.map((f) => f.content));
  if (m) mount(c.dir, m.version, m.vitest);
  writeFiles(c.dir, files);
  const project = new Project(c.dir);
  const server = new Server(c.dir, capabilities(), null);
  try {
    await server.start(c.dir);
    openAll(server, project, files);
    const file = files.find((f) => "1" in f.markers);
    if (!file) throw new Error("no marker 1");
    const before = file.content.slice(0, file.markers["1"]);
    const line = before.split("\n").length - 1;
    const col = before.slice(before.lastIndexOf("\n") + 1);
    const character = server.encoding === "utf-8" ? Buffer.byteLength(col) : col.length;
    // Go fourslash getCompletions: an empty context (triggerKind is required, so Go sends 0), then the client sort (ls.CompareCompletionEntries).
    const result = await server.request("textDocument/completion", { textDocument: { uri: project.uri(file.name) }, position: { line, character }, context: { triggerKind: 0 } });
    const list = result && !Array.isArray(result) ? result : null;
    const all = [...(list?.items ?? [])].sort((a, b) => compareCaseInsensitiveThenSensitive(a.sortText ?? "", b.sortText ?? "") || compareCaseInsensitiveThenSensitive(a.label, b.label));
    const items = all.filter((it) => COMPLETION_FILTERS[c.filter](it.label));
    if (args.dump) {
      fs.mkdirSync(args.dump, { recursive: true });
      fs.writeFileSync(path.join(args.dump, c.name + ".json"), project.normalize(JSON.stringify(list === null ? null : { ...list, items: all }, null, 1)) + "\n");
    }
    const errors = [];
    if (c.nilFatal && list === null) errors.push("completions is nil");
    else
      for (const check of c.checks) {
        const e = check(items);
        errors.push(...e);
        if (e.some((x) => x.startsWith("FATAL"))) break;
      }
    if (!errors.length) return "ok\n";
    return project.normalize(errors.join("\n") + "\n--- filtered items\n" + JSON.stringify(items, null, 1) + "\n");
  } finally {
    await server.stop();
  }
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

// Refactor cases that the Go harness does not have ("port cases", version `<profile>-port`). In
// each, a Go panic inside an Effect refactor reaches the LSP request recover, which answers the whole
// codeAction request with an internal error (root decision effect-ls-go-panics-decision-2026-10-11);
// the inventory line `(error) <code>: <message>` records it. Each `expected` text is the answer of
// effect-tsgo 0.51.1 (`--server` its tsc, `--kinds refactors --filter <name>`), the second selection
// shows that the server goes on after the panic.
const PORT_REFACTOR_CASES = [
  {
    // effectGenToFn with a named import of gen: EffectModule is nil, and the printer dereferences
    // the nil receiver of the new `.fn` access (effect_gen_to_fn.go:216).
    name: "effectGenToFn_namedGenImport",
    profile: "effect-v4",
    content: `// refactor: 5:3, 2:10
import { gen, succeed } from "effect/Effect"

export const program = () =>
  gen(function*() {
    const a = yield* succeed(1)
    return a
  })
`,
    expected: `=== Refactor Inventory ===

[R1] selection: "5:3-5:3"
  (error) -32603: InternalError: panic handling request textDocument/codeAction: runtime error: invalid memory address or nil pointer dereference

[R2] selection: "2:10-2:10"
  (no refactors)

[R3] selection: "empty (0:0-0:0)"
  (no refactors)

=== Refactor Application Results ===
(no refactors to apply)
`,
  },
  {
    // effectGenToFn with a named import of gen in a catch clause variable initializer. Go builds the
    // nil `.fn` receiver with no panic and prints it only in ReplaceNode, so the panic of
    // replaceExpressionViaStatement on the CatchClause parent (async_await_to_gen.go:93) comes first.
    name: "effectGenToFn_namedGenInCatch",
    profile: "effect-v4",
    content: `// refactor: 7:22, 2:10
import { gen, succeed } from "effect/Effect"

export const handler = () => {
  try {
    return 1
  } catch (e = () => gen(function*() { const a = yield* succeed(1); return a })) {
    return 2
  }
}
`,
    expected: `=== Refactor Inventory ===

[R1] selection: "7:22-7:22"
  (error) -32603: InternalError: panic handling request textDocument/codeAction: interface conversion: ast.nodeData is *ast.CatchClause, not *ast.VariableDeclarationList

[R2] selection: "2:10-2:10"
  (no refactors)

[R3] selection: "empty (0:0-0:0)"
  (no refactors)

=== Refactor Application Results ===
(no refactors to apply)
`,
  },
  {
    // asyncAwaitToGen on an async arrow in a catch clause variable initializer under a variable
    // statement: varDecl.Parent is the CatchClause (async_await_to_gen.go:93).
    name: "asyncAwaitToGen_catchVariable",
    profile: "effect-v4",
    content: `// refactor: 7:18, 2:10
import { Effect } from "effect"

export const handler = () => {
  try {
    return Effect.void
  } catch (e = async () => 1) {
    return Effect.void
  }
}
`,
    expected: `=== Refactor Inventory ===

[R1] selection: "7:18-7:18"
  (error) -32603: InternalError: panic handling request textDocument/codeAction: interface conversion: ast.nodeData is *ast.CatchClause, not *ast.VariableDeclarationList

[R2] selection: "2:10-2:10"
  (no refactors)

[R3] selection: "empty (0:0-0:0)"
  (no refactors)

=== Refactor Application Results ===
(no refactors to apply)
`,
  },
];

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
  if (kinds.includes("refactors")) {
    for (const c of PORT_REFACTOR_CASES) {
      if (!versions.includes(c.profile)) continue;
      add("refactors", c.profile + "-port", c.name, { file: c.name + ".ts", content: c.content, expected: c.expected, recordErrors: true, run: runRefactors });
    }
  }
  if (kinds.includes("inlay")) for (const c of inlayCases()) add("inlay", "inlayHints", c.name, { content: c.content, baseline: path.join(REFERENCE, "inlayHints", c.name + ".baseline"), run: runInlay });
  if (kinds.includes("hover")) for (const c of hoverCases()) add("hover", "hover_test", c.name, { content: c.content, checks: c.checks, expected: hoverExpected(c), run: runHover });
  if (kinds.includes("completion")) for (const c of completionCases()) add("completion", c.file.replace(/\.go$/, ""), c.name, { ...c, expected: "ok\n", run: runCompletion });
  if (kinds.includes("refactors")) {
    for (const c of PORT_SCHEMAGEN_CASES) {
      const version = c.profile + "-port";
      const baseline = path.join(LS_BASELINES, "refactors", version, c.name + ".refactors.txt");
      if (versions.includes(c.profile)) add("refactors", version, c.name, { file: c.name + ".ts", content: c.content, baseline, run: runRefactors });
    }
  }
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

// Cases whose effect-tsgo baseline differs at our Go pin N prime (fed0bf24149f) only through a
// TypeScript change, as `<kind>/<version>/<case>`; the rebased baseline has the same file name in
// ls-baselines/<kind>/<version>/.
// symbols: N prime leaves top-level import declarations out of the document symbols
// (ls/symbols.go:164-166; pin N and the TypeScript of effect-tsgo 0.51.1 list each imported name).
// Each rebase is the effect-tsgo baseline without those entries, in both the hierarchical and the
// flat answer: its Effect part is unchanged, and the rest equals the answer of the plain tsgo oracle
// at N prime.
const NP_REBASED = new Set(["symbols/effect-v4/debugDocumentSymbolFlows", "symbols/effect-v4/documentSymbolEffectStub"]);

async function runCase(c) {
  const resultDir = path.join(OUT, c.kind, c.version);
  const started = Date.now();
  const rebased = !args["effect-baselines"] && NP_REBASED.has(`${c.kind}/${c.version}/${c.name}`);
  const baseline = rebased ? path.join(LS_BASELINES, c.kind, c.version, path.basename(c.baseline)) : c.baseline;
  let status, detail;
  try {
    if (c.expected === undefined && !fs.existsSync(baseline)) throw new Error(`no baseline ${baseline}`);
    const actual = await c.run(c);
    const expected = c.expected ?? fs.readFileSync(baseline, "utf8");
    const norm = c.kind === "hover" ? inflateMermaid : (text) => text;
    status = norm(actual) === norm(expected) ? "same" : "diff";
    if (status === "diff") {
      fs.mkdirSync(resultDir, { recursive: true });
      fs.writeFileSync(path.join(resultDir, c.name + ".actual"), actual);
      fs.writeFileSync(path.join(resultDir, c.name + ".diff"), lineDiff(norm(expected), norm(actual)));
    }
  } catch (e) {
    status = "error";
    detail = String(e.message ?? e).slice(0, 2000);
    fs.mkdirSync(resultDir, { recursive: true });
    fs.writeFileSync(path.join(resultDir, c.name + ".error"), detail + "\n");
  }
  fs.rmSync(c.dir, { recursive: true, force: true });
  return { kind: c.kind, version: c.version, case: c.name, status, ms: Date.now() - started, ...(rebased ? { rebased } : {}), ...(detail ? { detail } : {}) };
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
