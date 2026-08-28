import fs from "node:fs";

const [goPath, rustPath, reportPath] = process.argv.slice(2);
if (!goPath || !rustPath || !reportPath) {
  throw new Error("Expected Go observations, Rust observations, and report paths");
}

const goRows = JSON.parse(fs.readFileSync(goPath, "utf8"));
const rustRows = JSON.parse(fs.readFileSync(rustPath, "utf8"));
const key = (row) => `${row.name}/${row.order}`;
const rustByKey = new Map(rustRows.map((row) => [key(row), row]));
const syntaxKinds = new Map([
  ["KindClassDeclaration", "ClassDeclaration"],
  ["KindModuleDeclaration", "ModuleDeclaration"],
  ["KindPropertyDeclaration", "PropertyDeclaration"],
  ["KindVariableDeclaration", "VariableDeclaration"],
]);

// Transient marks checker-created storage, not a different source symbol.
// Go's enum names add Kind to the same four declaration kinds.
function semanticValue(value) {
  if (Array.isArray(value)) return value.map(semanticValue);
  if (value !== null && typeof value === "object") {
    return Object.fromEntries(
      Object.entries(value)
        .filter(([name]) => name !== "transient")
        .sort(([left], [right]) => left.localeCompare(right))
        .map(([name, child]) => [name, semanticValue(name === "kind"
          ? syntaxKinds.get(child) ?? child
          : child)]),
    );
  }
  return value;
}

function differences(expected, actual, path = "", result = []) {
  if (JSON.stringify(expected) === JSON.stringify(actual)) return result;
  if (
    expected !== null &&
    actual !== null &&
    typeof expected === "object" &&
    typeof actual === "object" &&
    Array.isArray(expected) === Array.isArray(actual)
  ) {
    const names = [...new Set([...Object.keys(expected), ...Object.keys(actual)])].sort();
    for (const name of names) differences(expected[name], actual[name], `${path}/${name}`, result);
  } else {
    result.push({
      path,
      go: expected ?? null,
      rust: actual ?? null,
      goPresent: expected !== undefined,
      rustPresent: actual !== undefined,
    });
  }
  return result;
}

const rows = goRows.map((go) => {
  const rust = rustByKey.get(key(go));
  const result = { name: go.name, order: go.order, expect: go.expect };
  if (!rust) return { ...result, status: "missing_rust_row" };
  if (go.panic || !go.skippedOrder && go.warmStable !== true) {
    return { ...result, status: "reference_error", go };
  }
  if (go.skippedOrder || rust.skippedOrder) {
    return {
      ...result,
      status: go.skippedOrder === rust.skippedOrder ? "inapplicable_order" : "order_mismatch",
    };
  }
  if (rust.sourceStatus === "observer_panic") {
    return { ...result, status: "rust_observer_error", rustError: rust.sourceError };
  }
  if (rust.sourceStatus !== "checked") {
    return {
      ...result,
      status: go.expect === "boundary" && rust.sourceStatus === "unsupported"
        ? "known_rust_boundary"
        : "rust_source_failure",
      goDiagnostics: go.snapshot.diagnostics,
      rustStatus: rust.sourceStatus,
      rustError: rust.sourceError,
      first: rust.first,
    };
  }
  const diff = differences(
    semanticValue({ first: go.first, snapshot: go.snapshot }),
    semanticValue({ first: rust.first, snapshot: rust.snapshot }),
  );
  return {
    ...result,
    status: rust.warmStable !== true ? "rust_replay_failure" : diff.length ? "mismatch" : "exact",
    differences: diff,
    replayError: rust.replayError ?? null,
  };
});

const extra = rustRows.filter((row) => !goRows.some((go) => key(go) === key(row)));
if (extra.length) throw new Error(`Unexpected Rust rows: ${extra.map(key).join(", ")}`);
const counts = {};
for (const row of rows) counts[row.status] = (counts[row.status] ?? 0) + 1;
const cases = {};
for (const row of rows) {
  const summary = cases[row.name] ??= { statuses: [], orders: 0 };
  if (!summary.statuses.includes(row.status)) summary.statuses.push(row.status);
  summary.orders += 1;
}
fs.writeFileSync(reportPath, JSON.stringify({ counts, cases, rows }, null, 2));
console.log(JSON.stringify({ counts, cases }, null, 2));
if (rows.some((row) => !["exact", "known_rust_boundary", "inapplicable_order"].includes(row.status))) {
  process.exitCode = 1;
}
