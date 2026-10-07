#!/usr/bin/env node
// Opens one file in `<tsc> --lsp --stdio` and prints its pulled diagnostics
// (textDocument/diagnostic), to check that the editor path reports Effect
// diagnostics from the same checker hook as the CLI.
// usage: node scripts/effect/lsp-check.mjs <tsc> <file>
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

const [bin, file] = process.argv.slice(2);
const abs = path.resolve(file);
const uri = pathToFileURL(abs).href;
const server = spawn(bin, ["--lsp", "--stdio"], { stdio: ["pipe", "pipe", "inherit"] });
let buf = Buffer.alloc(0);
const pending = new Map();
let id = 0;
server.stdout.on("data", (chunk) => {
  buf = Buffer.concat([buf, chunk]);
  for (;;) {
    const sep = buf.indexOf("\r\n\r\n");
    if (sep < 0) return;
    const len = Number(/Content-Length: (\d+)/i.exec(buf.subarray(0, sep).toString())[1]);
    if (buf.length < sep + 4 + len) return;
    const msg = JSON.parse(buf.subarray(sep + 4, sep + 4 + len).toString());
    buf = buf.subarray(sep + 4 + len);
    if (msg.id !== undefined && pending.has(msg.id) && !msg.method) {
      pending.get(msg.id)(msg);
      pending.delete(msg.id);
    } else if (msg.id !== undefined && msg.method) {
      send({ jsonrpc: "2.0", id: msg.id, result: msg.method === "workspace/configuration" ? (msg.params?.items ?? []).map(() => null) : null });
    }
  }
});
function send(msg) {
  const body = Buffer.from(JSON.stringify(msg));
  server.stdin.write(`Content-Length: ${body.length}\r\n\r\n`);
  server.stdin.write(body);
}
const request = (method, params) =>
  new Promise((resolve) => {
    const n = ++id;
    pending.set(n, resolve);
    send({ jsonrpc: "2.0", id: n, method, params });
  });
await request("initialize", { processId: process.pid, rootUri: pathToFileURL(path.dirname(abs)).href, capabilities: { textDocument: { diagnostic: {} } } });
send({ jsonrpc: "2.0", method: "initialized", params: {} });
send({ jsonrpc: "2.0", method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "typescript", version: 1, text: fs.readFileSync(abs, "utf8") } } });
const res = await request("textDocument/diagnostic", { textDocument: { uri } });
for (const d of res.result?.items ?? []) {
  console.log(`${d.range.start.line + 1}:${d.range.start.character + 1} severity=${d.severity} TS${d.code} ${d.message.split("\n")[0]}`);
}
if (res.error) console.log("error", JSON.stringify(res.error));
await request("shutdown", null);
send({ jsonrpc: "2.0", method: "exit" });
server.kill();
