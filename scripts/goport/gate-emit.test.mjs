import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const GATE = fileURLToPath(new URL("./gate.sh", import.meta.url));

// Runs parse_emit of gate.sh's Python helper on compare-emit.sh summary lines. logs: {project: [Go log, goport log]}.
function parseEmit(lines, logs) {
  const dir = mkdtempSync(join(tmpdir(), "gate-emit-"));
  try {
    for (const [name, [go, goport]] of Object.entries(logs)) {
      for (const [side, text] of [["oracle", go], ["runs", goport]]) {
        mkdirSync(join(dir, side, name), { recursive: true });
        writeFileSync(join(dir, side, name, "log"), text);
      }
    }
    writeFileSync(join(dir, "summary.txt"), lines.join("\n") + "\n");
    const driver = `
import json, re, sys
from pathlib import Path
ns = {'__name__': 'gate'}
exec(re.search(r"read -r -d '' PY <<'PYEOF'\\n(.*?)\\nPYEOF\\n", open(sys.argv[1]).read(), re.S)[1], ns)
ns['EMIT_ORACLE'] = Path(sys.argv[2]) / 'oracle'
print(json.dumps(ns['parse_emit']('emit', Path(sys.argv[2]) / 'summary.txt', Path(sys.argv[2]) / 'runs')))`;
    const run = spawnSync("python3", ["-c", driver, GATE, dir], { env: { ...process.env, GOPORT_MAX_EXIT: "1" }, encoding: "utf8" });
    assert.equal(run.status, 0, run.stderr);
    return Object.fromEntries(JSON.parse(run.stdout).map(item => [item.id, item.status]));
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("an emit project where Go and goport write no file is MATCH only with equal exit and diagnostics", () => {
  const line = (name, rc, orc) => `${name} DIFF oracle=0 goport=0 differ=0 only=0 rc=${rc} oracle_rc=${orc} 1s panics=0 unported=0`;
  const diag = "src/a.ts(1,7): error TS7031: Binding element 'x' implicitly has an 'any' type.\n";
  const got = parseEmit([line("same", 1, 1), line("other-log", 1, 1), line("other-exit", 0, 1),
    "files DIFF oracle=5 goport=4 differ=0 only=1 rc=0 oracle_rc=0 1s panics=0 unported=0",
    "ok MATCH oracle=5 goport=5 differ=0 only=0 rc=0 oracle_rc=0 1s panics=0 unported=0"],
  { same: [diag, diag], "other-log": [diag, ""], "other-exit": [diag, diag] });
  assert.deepEqual(got, { "emit/same": "MATCH", "emit/other-log": "FAIL", "emit/other-exit": "FAIL", "emit/files": "FAIL", "emit/ok": "MATCH" });
});
