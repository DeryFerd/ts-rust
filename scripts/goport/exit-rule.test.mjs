import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const RULE = fileURLToPath(new URL("./exit-rule.sh", import.meta.url));

// Sources exit-rule.sh at pin (undefined: no pin) and returns [GOPORT_MAX_EXIT, incomplete for each
// [exit, stderr text] run].
function judge(pin, runs) {
  const dir = mkdtempSync(join(tmpdir(), "exit-rule-"));
  try {
    const calls = runs.map(([exit, stderr], i) => {
      writeFileSync(join(dir, `${i}.err`), stderr);
      return `if incomplete ${exit} ${dir}/${i}.err; then echo INCOMPLETE; else echo complete; fi`;
    });
    const env = { ...process.env, GOPORT_PIN_ACTIVE: pin ?? "", GOPORT_MAX_EXIT: "9" };
    const run = spawnSync("bash", ["-c", `. ${RULE}; echo $GOPORT_MAX_EXIT; ${calls.join("; ")}`], { env, encoding: "utf8" });
    assert.equal(run.status, 0, run.stderr);
    const [max, ...verdicts] = run.stdout.trim().split("\n");
    return [Number(max), verdicts];
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const RUNS = [[0, ""], [1, "note\n"], [2, ""], [2, "panic: runtime error\n"], [1, "panic: kept\n"], [1, "unported x\n"], [70, ""]];

test("exit 2 is complete only at the pins in EXIT2_PINS; other pins keep the old rule", () => {
  // The old rule (52168999f3dc, dc37b5249ab6, no pin, an unknown pin): exit 0 or 1 and no unported line.
  const old = ["complete", "complete", "INCOMPLETE", "INCOMPLETE", "complete", "INCOMPLETE", "INCOMPLETE"];
  for (const pin of [undefined, "52168999f3dc", "dc37b5249ab6", "16c25522e12", "16c25522e1230"]) {
    assert.deepEqual(judge(pin, RUNS), [1, old], String(pin));
  }
  // Bump B: exit 2 is complete, and a Go "panic: " line is not.
  assert.deepEqual(judge("16c25522e123", RUNS),
    [2, ["complete", "complete", "complete", "INCOMPLETE", "INCOMPLETE", "INCOMPLETE", "INCOMPLETE"]]);
});
