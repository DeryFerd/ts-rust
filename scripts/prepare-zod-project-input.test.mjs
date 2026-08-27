import assert from "node:assert/strict";
import { execFileSync, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import {
  chmodSync,
  existsSync,
  linkSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  realpathSync,
  renameSync,
  rmSync,
  symlinkSync,
  unlinkSync,
  writeFileSync,
} from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import test from "node:test";
import {
  createOutputGuard,
  extractPinnedArchive,
  initializeOutput,
  preparePinnedTool,
  readPinnedArchive,
  spawnPinnedTool,
  toolPins,
  verifyPinnedTool,
} from "./prepare-zod-project-input.mjs";

const script = fileURLToPath(
  new URL("./prepare-zod-project-input.mjs", import.meta.url),
);
const testRoot = fileURLToPath(
  new URL("../target/zod-guard-tests/", import.meta.url),
);

function fixture(t, initialize = true) {
  mkdirSync(testRoot, { recursive: true });
  const root = mkdtempSync(path.join(testRoot, "case-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const output = path.join(root, "output");
  const cache = path.join(root, "cache");
  const external = path.join(root, "external");
  mkdirSync(cache);
  mkdirSync(external);
  const sentinel = path.join(external, "sentinel");
  writeFileSync(sentinel, "unchanged\n");
  const guard = createOutputGuard(output, cache);
  if (initialize) initializeOutput(guard);
  return {
    root,
    output,
    cache,
    external,
    sentinel,
    guard,
    unchanged() {
      assert.equal(readFileSync(sentinel, "utf8"), "unchanged\n");
      assert.deepEqual(readdirSync(external), ["sentinel"]);
    },
  };
}

function archiveBytes(entries) {
  return execFileSync(
    "python3",
    [
      "-I",
      "-c",
      String.raw`
import io
import json
import sys
import tarfile

with tarfile.open(fileobj=sys.stdout.buffer, mode="w|", format=tarfile.PAX_FORMAT) as archive:
    for entry in json.load(sys.stdin):
        member = tarfile.TarInfo(entry["path"])
        member.mode = entry.get("mode", 0o644)
        member.type = {
            "file": tarfile.REGTYPE,
            "directory": tarfile.DIRTYPE,
            "symlink": tarfile.SYMTYPE,
            "hardlink": tarfile.LNKTYPE,
            "fifo": tarfile.FIFOTYPE,
        }[entry.get("type", "file")]
        member.linkname = entry.get("target", "")
        data = entry.get("content", "").encode("utf-8")
        member.size = len(data) if member.isfile() else 0
        archive.addfile(member, io.BytesIO(data) if member.isfile() else None)
`,
    ],
    { input: JSON.stringify(entries), maxBuffer: 8 * 1024 * 1024 },
  );
}

function pinnedArchive(f, entries, options = {}) {
  const bytes = archiveBytes(entries);
  const algorithm = options.algorithm ?? "sha256";
  const pin = {
    name: "test-tool",
    version: "10.12.1",
    archive: "test-tool.tar",
    prefix: "package",
    entry: "bin/tool.cjs",
    ...options,
    integrity: `${algorithm}-${createHash(algorithm)
      .update(bytes)
      .digest(algorithm === "sha512" ? "base64" : "hex")}`,
  };
  const archive = path.join(f.output, "toolchain/archives", pin.archive);
  f.guard.write(archive, bytes);
  return { archive, pin };
}

function toolFixture(t, options) {
  const f = fixture(t);
  const { pin, archive } = pinnedArchive(
    f,
    [
      {
        path: "package/package.json",
        content: '{"name":"test-tool","version":"10.12.1"}',
      },
      {
        path: "package/bin/tool.cjs",
        mode: 0o755,
        content:
          '#!/usr/bin/env node\nrequire("../lib/worker.cjs");\nconsole.log("10.12.1");\n',
      },
      {
        path: "package/lib/worker.cjs",
        content: 'module.exports = "verified";\n',
      },
    ],
    options,
  );
  const tool = preparePinnedTool(f.guard, pin);
  return { ...f, ...tool, pin, archive };
}

async function outputOf(child) {
  let stdout = "";
  let stderr = "";
  child.stdout.on("data", (chunk) => {
    stdout += chunk;
  });
  child.stderr.on("data", (chunk) => {
    stderr += chunk;
  });
  const result = await new Promise((resolve, reject) => {
    child.on("error", reject);
    child.on("close", (code, signal) => resolve({ code, signal }));
  });
  assert.equal(result.code, 0, stderr);
  return stdout.trim();
}

test("import and invalid actions do not create output or discover tools", (t) => {
  const f = fixture(t, false);
  const env = {
    ...process.env,
    PATH: "",
    ZOD_INPUT_OUT: f.output,
    ZOD_REPO_CACHE: f.cache,
  };
  const imported = spawnSync(
    process.execPath,
    [
      "--input-type=module",
      "-e",
      `await import(${JSON.stringify(new URL("./prepare-zod-project-input.mjs", import.meta.url).href)})`,
    ],
    { env, encoding: "utf8" },
  );
  assert.equal(imported.status, 0, imported.stderr);
  const invalid = spawnSync(process.execPath, [script, "invalid"], {
    env,
    encoding: "utf8",
  });
  assert.notEqual(invalid.status, 0);
  assert.match(invalid.stderr, /Use materialize, install, or audit/);
  assert.equal(existsSync(f.output), false);
  f.unchanged();
});

test("output roots and ancestors cannot be symlinks", async (t) => {
  for (const ancestor of [false, true]) {
    await t.test(ancestor ? "parent" : "root", (t) => {
      const f = fixture(t, false);
      symlinkSync(f.external, f.output);
      const output = ancestor ? path.join(f.output, "child") : f.output;
      assert.throws(
        () => createOutputGuard(output, f.cache),
        /Symlinked output path/,
      );
      const result = spawnSync(process.execPath, [script, "materialize"], {
        env: { ...process.env, ZOD_INPUT_OUT: output, ZOD_REPO_CACHE: f.cache },
        encoding: "utf8",
      });
      assert.notEqual(result.status, 0);
      assert.match(result.stderr, /Symlinked output path/);
      f.unchanged();
    });
  }
});

test("cache aliases cannot hide output overlap", async (t) => {
  await t.test("output below aliased cache", (t) => {
    const f = fixture(t, false);
    const alias = path.join(f.root, "cache-alias");
    symlinkSync(f.cache, alias);
    const output = path.join(f.cache, "new-output");
    assert.throws(
      () => createOutputGuard(output, alias),
      /separate from the cache/,
    );
    assert.deepEqual(readdirSync(f.cache), []);
  });
  await t.test("aliased cache below output", (t) => {
    const f = fixture(t, false);
    mkdirSync(path.join(f.output, "checkout"), { recursive: true });
    const alias = path.join(f.root, "cache-alias");
    symlinkSync(path.join(f.output, "checkout"), alias);
    assert.throws(
      () => createOutputGuard(f.output, alias),
      /separate from the cache/,
    );
    assert.deepEqual(readdirSync(f.output), ["checkout"]);
  });
  await t.test("cache alias with symlinks before parent components", (t) => {
    const f = fixture(t, false);
    mkdirSync(f.output);
    const links = path.join(f.root, "cache-parent/links");
    mkdirSync(path.join(links, "output"), { recursive: true });
    symlinkSync("..", path.join(links, "up"));
    const alias = path.join(f.root, "cache-alias");
    symlinkSync("cache-parent/links/up/../output", alias);
    assert.equal(realpathSync.native(alias), f.output);
    assert.throws(
      () => createOutputGuard(f.output, alias),
      /separate from the cache/,
    );
    assert.deepEqual(readdirSync(f.output), []);
    f.unchanged();
  });
});

test("raw cache parent components cannot hide output overlap", async (t) => {
  for (const entry of ["guard", "CLI"]) {
    for (const relative of [false, true]) {
      await t.test(`${entry}, ${relative ? "relative" : "absolute"}`, (t) => {
        const f = fixture(t, false);
        mkdirSync(f.output);
        const sentinel = path.join(f.output, "cache-sentinel");
        writeFileSync(sentinel, "cache unchanged\n");
        const links = path.join(f.root, "cache-parent/links");
        mkdirSync(path.join(links, "output"), { recursive: true });
        symlinkSync("..", path.join(links, "up"));
        const rawCache = `${links}/up/../output`;
        assert.equal(realpathSync.native(rawCache), f.output);
        assert.notEqual(path.resolve(rawCache), f.output);
        if (entry === "guard") {
          const cache = relative
            ? `${path.relative(process.cwd(), links)}/up/../output`
            : rawCache;
          assert.throws(
            () => initializeOutput(createOutputGuard(f.output, cache)),
            /separate from the cache/,
          );
        } else {
          const result = spawnSync(process.execPath, [script, "materialize"], {
            cwd: f.root,
            env: {
              ...process.env,
              ZOD_INPUT_OUT: f.output,
              ZOD_REPO_CACHE: relative
                ? "cache-parent/links/up/../output"
                : rawCache,
            },
            encoding: "utf8",
          });
          assert.notEqual(result.status, 0);
          assert.match(result.stderr, /separate from the cache/);
        }
        assert.deepEqual(readdirSync(f.output), ["cache-sentinel"]);
        assert.equal(readFileSync(sentinel, "utf8"), "cache unchanged\n");
        f.unchanged();
      });
    }
  }
});

test("managed directories are checked before initialization writes", async (t) => {
  for (const name of [
    "evidence",
    "toolchain",
    "toolchain/archives",
    "toolchain/node/bin",
    "pnpm-store",
    "tmp",
    "npm-cache",
    "cache",
    "data",
    "config",
    "pnpm-home",
    "home",
    "source",
  ]) {
    await t.test(name, (t) => {
      const f = fixture(t, false);
      const destination = path.join(f.output, name);
      mkdirSync(path.dirname(destination), { recursive: true });
      symlinkSync(f.external, destination);
      assert.throws(() => initializeOutput(f.guard), /Symlinked/);
      f.unchanged();
      assert.equal(
        existsSync(path.join(f.output, "config/empty.npmrc")),
        false,
      );
    });
  }
});

test("managed files reject symlinks, dangling symlinks, and hardlinks", async (t) => {
  for (const name of [
    "config/empty.npmrc",
    "evidence/install.log",
    "evidence/preparation.json",
    "toolchain/archives/pnpm-10.12.1.tgz",
    "zod-source.tar",
  ]) {
    await t.test(name, (t) => {
      const f = fixture(t, false);
      const filename = path.join(f.output, name);
      mkdirSync(path.dirname(filename), { recursive: true });
      symlinkSync(f.sentinel, filename);
      assert.throws(() => initializeOutput(f.guard), /Symlinked/);
      assert.throws(() => f.guard.write(filename, "changed"), /Symlinked/);
      f.unchanged();
    });
  }
  await t.test("dangling output link", (t) => {
    const f = fixture(t);
    const filename = path.join(f.output, "evidence/install.log");
    symlinkSync(path.join(f.external, "new-file"), filename);
    assert.throws(() => f.guard.stagedFile(filename), /Symlinked/);
    f.unchanged();
  });
  await t.test("hardlinked output file", (t) => {
    const f = fixture(t);
    const filename = path.join(f.output, "evidence/install.log");
    linkSync(f.sentinel, filename);
    assert.throws(() => initializeOutput(f.guard), /Hardlinked/);
    assert.throws(() => f.guard.write(filename, "changed"), /Hardlinked/);
    f.unchanged();
  });
});

test("normal writes replace files and log staging never follows a later link", (t) => {
  const f = fixture(t);
  const filename = path.join(f.output, "evidence/install.log");
  f.guard.write(filename, "first");
  f.guard.write(filename, "second");
  assert.equal(readFileSync(filename, "utf8"), "second");
  const log = f.guard.stagedFile(filename);
  try {
    writeFileSync(log.descriptor, "third");
    unlinkSync(filename);
    symlinkSync(f.sentinel, filename);
    assert.throws(() => log.publish(), /Symlinked/);
  } finally {
    log.dispose();
  }
  assert.deepEqual(readdirSync(path.join(f.output, "tmp")), []);
  f.unchanged();
});

test("contained source and pnpm links remain valid", (t) => {
  const f = fixture(t);
  const source = path.join(f.output, "source");
  const physical = path.join(
    source,
    "node_modules/.pnpm/package/node_modules/package",
  );
  mkdirSync(physical, { recursive: true });
  writeFileSync(path.join(physical, "index.js"), "module.exports = {};\n");
  symlinkSync(
    ".pnpm/package/node_modules/package",
    path.join(source, "node_modules/package"),
  );
  symlinkSync(
    "node_modules/package/index.js",
    path.join(source, "source-link.js"),
  );
  initializeOutput(f.guard);
  f.guard.preflight();
  symlinkSync(f.sentinel, path.join(source, "external-link"));
  assert.throws(() => f.guard.preflight(), /Source link leaves the source/);
  f.unchanged();
});

test("source link checks use resolved targets, not just normalized text", (t) => {
  const f = fixture(t);
  const source = path.join(f.output, "source");
  mkdirSync(path.join(source, "links"), { recursive: true });
  mkdirSync(path.join(source, "external"));
  writeFileSync(path.join(source, "external/sentinel"), "inside\n");
  symlinkSync("..", path.join(source, "links/up"));
  symlinkSync(
    "links/up/../../external/sentinel",
    path.join(source, "escape"),
  );
  assert.equal(realpathSync.native(path.join(source, "escape")), f.sentinel);
  assert.equal(
    readFileSync(path.join(source, "escape"), "utf8"),
    "unchanged\n",
  );
  assert.throws(() => f.guard.preflight(), /Source link leaves the source/);
  f.unchanged();
});

test("unsafe archives cannot write outside a new extraction directory", async (t) => {
  const cases = [
    ["traversal", [{ path: "package/../../sentinel" }]],
    ["absolute path", [{ path: "/package/file" }]],
    ["backslash", [{ path: "package\\file" }]],
    ["dot component", [{ path: "package/./file" }]],
    ["empty component", [{ path: "package//file" }]],
    ["wrong prefix", [{ path: "other/file" }]],
    ["duplicate path", [{ path: "package/file" }, { path: "package/file" }]],
    [
      "absolute link",
      [{ path: "package/link", type: "symlink", target: "/outside" }],
    ],
    [
      "escaping link",
      [{ path: "package/link", type: "symlink", target: "../../outside" }],
    ],
    [
      "link parent",
      [
        { path: "package/link", type: "symlink", target: "safe" },
        { path: "package/link/file" },
      ],
    ],
    [
      "link parent after file",
      [
        { path: "package/link/file" },
        { path: "package/link", type: "symlink", target: "safe" },
      ],
    ],
    [
      "link chain traversal",
      [
        { path: "package/sub/link", type: "symlink", target: ".." },
        {
          path: "package/escape",
          type: "symlink",
          target: "sub/link/../../outside",
        },
      ],
    ],
    [
      "link cycle",
      [
        { path: "package/a", type: "symlink", target: "b" },
        { path: "package/b", type: "symlink", target: "a" },
      ],
    ],
    [
      "hardlink",
      [{ path: "package/file", type: "hardlink", target: "package/other" }],
    ],
    ["fifo", [{ path: "package/pipe", type: "fifo" }]],
  ];
  for (const [name, entries] of cases) {
    await t.test(name, (t) => {
      const f = fixture(t);
      const { pin, archive } = pinnedArchive(f, entries, { allowLinks: true });
      const destination = path.join(f.output, "source");
      assert.throws(
        () => extractPinnedArchive(f.guard, archive, pin, destination),
        /archive|Archive/,
      );
      assert.equal(existsSync(destination), false);
      assert.deepEqual(readdirSync(path.join(f.output, "tmp")), []);
      f.unchanged();
    });
  }
});

test("source extraction permits contained links and refuses an existing tree", (t) => {
  const f = fixture(t);
  const { archive, pin } = pinnedArchive(
    f,
    [
      { path: "package/dir/file", content: "source" },
      { path: "package/link", type: "symlink", target: "dir/file" },
    ],
    { allowLinks: true },
  );
  const destination = path.join(f.output, "source");
  extractPinnedArchive(f.guard, archive, pin, destination);
  assert.equal(readFileSync(path.join(destination, "link"), "utf8"), "source");
  f.guard.preflight();
  assert.throws(
    () => extractPinnedArchive(f.guard, archive, pin, destination),
    /already exists/,
  );
  f.unchanged();
});

test("changed archives fail before extraction or tool execution", (t) => {
  const f = toolFixture(t);
  f.guard.write(
    f.archive,
    archiveBytes([{ path: "package/bin/tool.cjs", content: "changed" }]),
  );
  assert.throws(
    () => readPinnedArchive(f.guard, f.archive, f.pin),
    /integrity mismatch/,
  );
  assert.throws(
    () => spawnPinnedTool(f.guard, f.pin, []),
    /integrity mismatch/,
  );
  assert.throws(
    () =>
      extractPinnedArchive(
        f.guard,
        f.archive,
        f.pin,
        path.join(f.output, "source"),
      ),
    /integrity mismatch/,
  );
  assert.equal(existsSync(path.join(f.output, "source")), false);
  f.unchanged();
});

test("complete pinned tool trees run and can be reused", async (t) => {
  const f = toolFixture(t, { algorithm: "sha512" });
  assert.equal(
    verifyPinnedTool(f.guard, f.pin).files.filter(
      (entry) => entry.type === "file",
    ).length,
    3,
  );
  preparePinnedTool(f.guard, f.pin);
  const version = await outputOf(
    spawnPinnedTool(f.guard, f.pin, [], { stdio: ["ignore", "pipe", "pipe"] }),
  );
  assert.equal(version, "10.12.1");
  f.unchanged();
});

test("changed tools are rejected without executing them", async (t) => {
  const changes = {
    "same-version executable": (f) =>
      writeFileSync(
        f.entry,
        `#!/usr/bin/env node\nrequire("node:fs").writeFileSync(${JSON.stringify(f.sentinel)}, "changed");\nconsole.log("10.12.1");\n`,
      ),
    "supporting JavaScript": (f) =>
      writeFileSync(
        path.join(f.root, "lib/worker.cjs"),
        `require("node:fs").writeFileSync(${JSON.stringify(f.sentinel)}, "changed");\n`,
      ),
    "missing file": (f) => unlinkSync(path.join(f.root, "lib/worker.cjs")),
    "added file": (f) =>
      writeFileSync(path.join(f.root, "lib/extra.cjs"), "added"),
    "added directory": (f) => mkdirSync(path.join(f.root, "extra")),
    "executable mode": (f) => chmodSync(f.entry, 0o644),
    "special permission bits": (f) => chmodSync(f.entry, 0o4755),
    "symlinked support": (f) => {
      unlinkSync(path.join(f.root, "lib/worker.cjs"));
      symlinkSync(f.sentinel, path.join(f.root, "lib/worker.cjs"));
    },
    "hardlinked executable": (f) =>
      linkSync(f.entry, path.join(f.cache, "executable-alias")),
    "hardlinked archive": (f) =>
      linkSync(f.archive, path.join(f.cache, "archive-alias")),
    "symlinked tool root": (f) => {
      renameSync(f.root, f.root + "-original");
      symlinkSync(f.root + "-original", f.root);
    },
  };
  for (const [name, change] of Object.entries(changes)) {
    await t.test(name, (t) => {
      const f = toolFixture(t);
      change(f);
      assert.throws(
        () => spawnPinnedTool(f.guard, f.pin, []),
        /Tool|Symlinked|Hardlinked/,
      );
      f.unchanged();
    });
  }
});

test("a runtime executable is checked against its selected archive member", async (t) => {
  const f = toolFixture(t);
  const { pin } = pinnedArchive(
    f,
    [
      {
        path: "runtime/bin/node",
        mode: 0o755,
        content: `#!/bin/sh\nexec ${JSON.stringify(process.execPath)} "$@"\n`,
      },
      { path: "runtime/bin/unused", type: "symlink", target: "node" },
    ],
    {
      name: "runtime",
      archive: "runtime.tar",
      prefix: "runtime",
      entry: "bin/node",
      members: ["bin/node"],
    },
  );
  const runtime = preparePinnedTool(f.guard, pin);
  const version = await outputOf(
    spawnPinnedTool(f.guard, f.pin, [], {
      runtime: pin,
      stdio: ["ignore", "pipe", "pipe"],
    }),
  );
  assert.equal(version, "10.12.1");
  writeFileSync(
    runtime.entry,
    `#!/bin/sh\nprintf changed > ${JSON.stringify(f.sentinel)}\nprintf 'v24.13.0\\n'\n`,
  );
  assert.throws(
    () => spawnPinnedTool(f.guard, f.pin, [], { runtime: pin }),
    /Tool contents changed/,
  );
  f.unchanged();
});

test(
  "published tool archives match the pins and run from disposable storage",
  {
    skip: process.env.ZOD_TEST_PUBLISHED_TOOLS !== "1",
  },
  async (t) => {
    const f = fixture(t);
    const expectedFiles = { node: 1, pnpm: 1111, typescript: 120, yaml: 233 };
    for (const pin of Object.values(toolPins)) {
      const tool = preparePinnedTool(f.guard, pin, { download: true });
      assert.equal(
        tool.files.filter((entry) => entry.type === "file").length,
        expectedFiles[pin.name],
      );
    }
    const env = {
      ...process.env,
      HOME: path.join(f.output, "home"),
      TMPDIR: path.join(f.output, "tmp"),
      XDG_CACHE_HOME: path.join(f.output, "cache"),
      XDG_CONFIG_HOME: path.join(f.output, "config"),
      XDG_DATA_HOME: path.join(f.output, "data"),
      PNPM_HOME: path.join(f.output, "pnpm-home"),
      npm_config_cache: path.join(f.output, "npm-cache"),
      npm_config_userconfig: path.join(f.output, "config/empty.npmrc"),
      npm_config_globalconfig: path.join(f.output, "config/empty.npmrc"),
    };
    const options = { env, cwd: f.output, stdio: ["ignore", "pipe", "pipe"] };
    assert.equal(
      await outputOf(
        spawnPinnedTool(f.guard, toolPins.node, ["--version"], options),
      ),
      "v24.13.0",
    );
    assert.equal(
      await outputOf(
        spawnPinnedTool(f.guard, toolPins.pnpm, ["--version"], {
          ...options,
          runtime: toolPins.node,
        }),
      ),
      "10.12.1",
    );
    const require = createRequire(import.meta.url);
    const ts = require(verifyPinnedTool(f.guard, toolPins.typescript).entry);
    const yaml = require(verifyPinnedTool(f.guard, toolPins.yaml).entry);
    assert.equal(ts.version, "5.5.4");
    assert.deepEqual(
      ts.parseConfigFileTextToJson(
        "tsconfig.json",
        '{"compilerOptions":{"strict":true}}',
      ).config,
      { compilerOptions: { strict: true } },
    );
    assert.deepEqual(yaml.parse("packageManager: pnpm@10.12.1\n"), {
      packageManager: "pnpm@10.12.1",
    });
    f.unchanged();
  },
);
