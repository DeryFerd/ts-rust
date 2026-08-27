import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { execFileSync, spawn } from "node:child_process";
import {
  closeSync,
  constants,
  existsSync,
  fstatSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  openSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  readSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { createRequire } from "node:module";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const commit = "43f729db4aa0cedff6d6b3261f33f8556b3c7102";
const lockHash =
  "03627f8232469285ad0ae0199f749bf5471f71e4d78f709cb74ad63bbf87bbc3";
const rootsHash =
  "0433cde05204a2323ca8f6626dd92c302b16d6cca7f511e13fb95f449573f54f";
const sourceArchiveHash =
  "4f5e26542e189286be4f4256382467f78ae434144e3f0b87ba9edd4ce7114e43";
const manager = "pnpm@10.12.1";
const script = fileURLToPath(import.meta.url);
const project = path.resolve(path.dirname(script), "..");
const gitEnvironment = {
  ...process.env,
  GIT_OPTIONAL_LOCKS: "0",
  PYTHONDONTWRITEBYTECODE: "1",
};
const command = (binary, args, cwd = project, env = gitEnvironment) =>
  execFileSync(binary, args, {
    cwd,
    env,
    encoding: "utf8",
    maxBuffer: 32 * 1024 * 1024,
  }).trim();
const chunk = Buffer.allocUnsafe(1024 * 1024);
const hash = (data) => createHash("sha256").update(data).digest("hex");
const byteOrder = (left, right) =>
  Buffer.compare(Buffer.from(left), Buffer.from(right));
const jsonLines = (rows) =>
  rows.map((row) => JSON.stringify(row)).join("\n") + "\n";
const inside = (root, filename) =>
  filename === root ||
  filename.startsWith(root.endsWith(path.sep) ? root : root + path.sep);

export const toolPins = {
  node: {
    name: "node",
    version: "24.13.0",
    archive: "node-v24.13.0-linux-x64.tar.gz",
    url: "https://nodejs.org/download/release/v24.13.0/node-v24.13.0-linux-x64.tar.gz",
    integrity:
      "sha256-6223aad1a81f9d1e7b682c59d12e2de233f7b4c37475cd40d1c89c42b737ffa8",
    prefix: "node-v24.13.0-linux-x64",
    members: ["bin/node"],
    entry: "bin/node",
  },
  pnpm: {
    name: "pnpm",
    version: "10.12.1",
    archive: "pnpm-10.12.1.tgz",
    url: "https://registry.npmjs.org/pnpm/-/pnpm-10.12.1.tgz",
    integrity:
      "sha512-8N2oWA8O6UgcXHmh2Se5Fk8sR46QmSrSaLuyRlpzaYQ5HWMz0sMnkTV4soBK8zR0ylVLopwEqLEwYKcXZ1rjrA==",
    prefix: "package",
    entry: "bin/pnpm.cjs",
  },
  typescript: {
    name: "typescript",
    version: "5.5.4",
    archive: "typescript-5.5.4.tgz",
    url: "https://registry.npmjs.org/typescript/-/typescript-5.5.4.tgz",
    integrity:
      "sha512-Mtq29sKDAEYP7aljRgtPOpTvOfbwRWlS6dPRzwjdE+C0R4brX/GUyhHSecbHMFLNBLcJIPt9nl9yG5TZ1weH+Q==",
    prefix: "package",
    entry: "lib/typescript.js",
  },
  yaml: {
    name: "yaml",
    version: "2.8.3",
    archive: "yaml-2.8.3.tgz",
    url: "https://registry.npmjs.org/yaml/-/yaml-2.8.3.tgz",
    integrity:
      "sha512-AvbaCLOO2Otw/lW5bmh9d/WEdcDFdQp2Z2ZUH3pX9U2ihyUY0nvLv7J6TrWowklRGPYbB/IuIMfYgxaCPg5Bpg==",
    prefix: "package",
    entry: "dist/index.js",
  },
};

function optionalStat(filename) {
  return lstatSync(filename, { throwIfNoEntry: false });
}

function plainPath(filename, kind) {
  const absolute = path.resolve(filename);
  const root = path.parse(absolute).root;
  let current = root;
  const parts = path.relative(root, absolute).split(path.sep).filter(Boolean);
  for (const [index, part] of parts.entries()) {
    current = path.join(current, part);
    const stat = optionalStat(current);
    if (!stat) continue;
    assert(!stat.isSymbolicLink(), `Symlinked output path: ${current}`);
    if (index < parts.length - 1 || kind === "directory")
      assert(stat.isDirectory(), `Not an output directory: ${current}`);
    else {
      assert(stat.isFile(), `Not a regular output file: ${current}`);
      assert.equal(stat.nlink, 1, `Hardlinked output file: ${current}`);
    }
  }
  return absolute;
}

function canonicalLocation(filename) {
  // The OS resolves earlier symlinks before later '..' components.
  if (optionalStat(filename)) return realpathSync.native(filename);
  const parent = path.dirname(filename);
  assert.notEqual(parent, filename, `Cannot resolve path: ${filename}`);
  return path.join(canonicalLocation(parent), path.basename(filename));
}

// Check existing paths before creating any directories or replacing any files.
export function createOutputGuard(output, cache) {
  output = path.resolve(output);
  plainPath(output, "directory");
  const realOutput = canonicalLocation(output);
  // Keep raw cache components until the OS has resolved preceding symlinks.
  const realCache = canonicalLocation(cache);
  assert(
    !inside(realCache, realOutput) && !inside(realOutput, realCache),
    "The output must be separate from the cache checkout",
  );
  const source = path.join(output, "source");
  const guard = {
    output,
    check(filename, kind = "file") {
      filename = path.resolve(filename);
      assert(inside(output, filename), `Path leaves the output: ${filename}`);
      return plainPath(filename, kind);
    },
    directory(filename) {
      guard.check(filename, "directory");
      mkdirSync(filename, { recursive: true, mode: 0o700 });
      guard.check(filename, "directory");
      return filename;
    },
    tree(root, allowSourceLinks = false) {
      guard.check(root, "directory");
      if (!optionalStat(root)) return;
      function visit(directory) {
        for (const entry of readdirSync(directory, { withFileTypes: true })) {
          const filename = path.join(directory, entry.name);
          const stat = lstatSync(filename);
          if (stat.isSymbolicLink()) {
            assert(
              allowSourceLinks && inside(source, filename),
              `Symlinked managed path: ${filename}`,
            );
            const target = readlinkSync(filename);
            assert(
              !path.isAbsolute(target) &&
                inside(source, path.resolve(directory, target)),
              `Source link leaves the source: ${filename}`,
            );
            assert(
              inside(source, realpathSync.native(filename)),
              `Source link leaves the source: ${filename}`,
            );
          } else if (stat.isDirectory()) visit(filename);
          else {
            assert(stat.isFile(), `Unsupported output entry: ${filename}`);
            assert.equal(stat.nlink, 1, `Hardlinked output file: ${filename}`);
          }
        }
      }
      visit(root);
    },
    preflight() {
      guard.check(source, "directory");
      guard.tree(output, true);
    },
    stage() {
      const temporary = guard.directory(path.join(output, "tmp"));
      return mkdtempSync(path.join(temporary, "zod-stage-"));
    },
    stagedFile(filename) {
      guard.check(filename);
      guard.directory(path.dirname(filename));
      const directory = guard.stage();
      const temporary = path.join(directory, "file");
      let descriptor = openSync(
        temporary,
        constants.O_WRONLY |
          constants.O_CREAT |
          constants.O_EXCL |
          constants.O_NOFOLLOW,
        0o600,
      );
      return {
        descriptor,
        temporary,
        close() {
          if (descriptor !== null) closeSync(descriptor);
          descriptor = null;
        },
        publish() {
          this.close();
          guard.check(temporary);
          guard.check(filename);
          renameSync(temporary, filename);
        },
        dispose() {
          this.close();
          guard.check(directory, "directory");
          rmSync(directory, { recursive: true, force: true });
        },
      };
    },
    write(filename, data) {
      const file = guard.stagedFile(filename);
      try {
        writeFileSync(file.descriptor, data);
        file.publish();
      } finally {
        file.dispose();
      }
    },
  };
  return guard;
}

export function initializeOutput(guard) {
  guard.preflight();
  for (const name of [
    "evidence",
    "toolchain/archives",
    "pnpm-store",
    "tmp",
    "npm-cache",
    "cache",
    "data",
    "config",
    "pnpm-home",
    "home",
  ])
    guard.directory(path.join(guard.output, name));
  const userConfig = guard.check(path.join(guard.output, "config/empty.npmrc"));
  if (!optionalStat(userConfig)) guard.write(userConfig, "");
  assert.equal(
    readFileSync(userConfig, "utf8"),
    "",
    "The isolated user config must be empty",
  );
  return userConfig;
}

function fileHashes(filename) {
  plainPath(filename, "file");
  const descriptor = openSync(
    filename,
    constants.O_RDONLY | constants.O_NOFOLLOW,
  );
  let bytes = 0;
  try {
    const before = fstatSync(descriptor);
    assert(
      before.isFile() && before.nlink === 1,
      `Unsafe input file: ${filename}`,
    );
    const sha256 = createHash("sha256");
    const blob = createHash("sha1").update(`blob ${before.size}\0`);
    for (;;) {
      const count = readSync(descriptor, chunk, 0, chunk.length, null);
      if (count === 0) break;
      const part = chunk.subarray(0, count);
      sha256.update(part);
      blob.update(part);
      bytes += count;
    }
    const after = fstatSync(descriptor);
    assert.equal(
      bytes,
      before.size,
      `File changed during hashing: ${filename}`,
    );
    assert.equal(
      after.mtimeMs,
      before.mtimeMs,
      `File changed during hashing: ${filename}`,
    );
    assert.equal(
      after.ctimeMs,
      before.ctimeMs,
      `File changed during hashing: ${filename}`,
    );
    return { bytes, sha256: sha256.digest("hex"), gitBlob: blob.digest("hex") };
  } finally {
    closeSync(descriptor);
  }
}

export function readPinnedArchive(guard, filename, pin, destination) {
  guard.check(filename);
  if (destination) guard.check(destination, "directory");
  const descriptor = openSync(
    filename,
    constants.O_RDONLY | constants.O_NOFOLLOW,
  );
  try {
    const stat = fstatSync(descriptor);
    assert(stat.isFile() && stat.nlink === 1, `Unsafe archive: ${filename}`);
    return JSON.parse(
      execFileSync(
        "python3",
        ["-I", path.join(project, "scripts/zod-input-archive.py")],
        {
          cwd: project,
          env: gitEnvironment,
          encoding: "utf8",
          input: JSON.stringify({
            integrity: pin.integrity,
            prefix: pin.prefix ?? "",
            members: pin.members ?? null,
            allowLinks: pin.allowLinks ?? false,
            destination: destination ?? null,
          }),
          stdio: ["pipe", "pipe", "pipe", descriptor],
          maxBuffer: 32 * 1024 * 1024,
        },
      ),
    );
  } finally {
    closeSync(descriptor);
  }
}

export function verifyPinnedTool(guard, pin) {
  const archive = path.join(guard.output, "toolchain/archives", pin.archive);
  const expected = readPinnedArchive(guard, archive, pin);
  const root = guard.check(
    path.join(guard.output, "toolchain", pin.name),
    "directory",
  );
  guard.tree(root);
  const actual = [];
  function visit(directory) {
    for (const name of readdirSync(directory).sort(byteOrder)) {
      const filename = path.join(directory, name);
      const stat = lstatSync(filename);
      const relative = path.relative(root, filename);
      if (stat.isDirectory()) {
        actual.push({ path: relative, type: "directory" });
        visit(filename);
      } else {
        const { bytes, sha256 } = fileHashes(filename);
        actual.push({
          path: relative,
          type: "file",
          mode: stat.mode & 0o7777,
          bytes,
          sha256,
        });
      }
    }
  }
  visit(root);
  actual.sort((left, right) => byteOrder(left.path, right.path));
  assert.equal(
    actual.length,
    expected.length,
    `Tool entry count changed: ${pin.name}`,
  );
  for (let index = 0; index < expected.length; index++)
    assert.deepEqual(
      actual[index],
      expected[index],
      `Tool contents changed: ${pin.name}/${expected[index].path}`,
    );
  return {
    root,
    entry: guard.check(path.join(root, pin.entry)),
    archive,
    files: actual,
  };
}

export function extractPinnedArchive(guard, archive, pin, destination) {
  guard.check(destination, "directory");
  assert(
    !optionalStat(destination),
    `Extraction destination already exists: ${destination}`,
  );
  const stage = guard.stage();
  const tree = path.join(stage, "tree");
  try {
    guard.directory(tree);
    const files = readPinnedArchive(guard, archive, pin, tree);
    guard.check(destination, "directory");
    assert(
      !optionalStat(destination),
      `Extraction destination already exists: ${destination}`,
    );
    guard.directory(path.dirname(destination));
    renameSync(tree, destination);
    return files;
  } finally {
    guard.check(stage, "directory");
    rmSync(stage, { recursive: true, force: true });
  }
}

export function preparePinnedTool(guard, pin, { download = false } = {}) {
  const archive = guard.check(
    path.join(guard.output, "toolchain/archives", pin.archive),
  );
  const root = guard.check(
    path.join(guard.output, "toolchain", pin.name),
    "directory",
  );
  if (!optionalStat(archive)) {
    assert(download, `Pinned archive is missing: ${archive}`);
    const file = guard.stagedFile(archive);
    try {
      execFileSync(
        "curl",
        [
          "--disable",
          "--fail",
          "--silent",
          "--show-error",
          "--location",
          "--proto",
          "=https",
          "--proto-redir",
          "=https",
          "--connect-timeout",
          "30",
          "--max-time",
          "300",
          "--max-filesize",
          "134217728",
          pin.url,
        ],
        {
          cwd: project,
          env: gitEnvironment,
          stdio: ["ignore", file.descriptor, "pipe"],
        },
      );
      file.close();
      readPinnedArchive(guard, file.temporary, pin);
      file.publish();
    } finally {
      file.dispose();
    }
  }
  if (!optionalStat(root)) extractPinnedArchive(guard, archive, pin, root);
  return verifyPinnedTool(guard, pin);
}

export function spawnPinnedTool(
  guard,
  pin,
  args,
  { runtime, ...options } = {},
) {
  guard.preflight();
  const tool = verifyPinnedTool(guard, pin);
  const interpreter = runtime && verifyPinnedTool(guard, runtime);
  return spawn(
    interpreter ? interpreter.entry : tool.entry,
    interpreter ? [tool.entry, ...args] : args,
    options,
  );
}

function createPreparation(output, cache) {
  const guard = createOutputGuard(output, cache);
  const userConfig = initializeOutput(guard);
  const source = path.join(output, "source");
  const evidence = path.join(output, "evidence");
  const nodeBinary = path.join(output, "toolchain/node/bin/node");
  const pnpmEntry = path.join(output, "toolchain/pnpm/bin/pnpm.cjs");
  const store = path.join(output, "pnpm-store");
  const git = (...args) =>
    command("git", ["--no-optional-locks", "-C", cache, ...args]);
  const environment = {
    ...Object.fromEntries(
      Object.entries(gitEnvironment).filter(
        ([name]) => !/^(npm_config_|pnpm_|corepack_|node_|xdg_)/i.test(name),
      ),
    ),
    CI: "true",
    NODE_ENV: "development",
    NODE_OPTIONS: "--max-old-space-size=768",
    PATH: path.dirname(nodeBinary) + path.delimiter + process.env.PATH,
    HOME: path.join(output, "home"),
    UV_THREADPOOL_SIZE: "2",
    TMPDIR: path.join(output, "tmp"),
    PNPM_HOME: path.join(output, "pnpm-home"),
    // pnpm 10.12.1 subtracts this CPU count, leaving one package worker.
    PNPM_WORKERS: String(os.availableParallelism()),
    XDG_CACHE_HOME: path.join(output, "cache"),
    XDG_CONFIG_HOME: path.join(output, "config"),
    XDG_DATA_HOME: path.join(output, "data"),
    npm_config_cache: path.join(output, "npm-cache"),
    npm_config_userconfig: userConfig,
    npm_config_globalconfig: userConfig,
    npm_config_registry: "https://registry.npmjs.org/",
  };

  function sourceEntries() {
    assert.equal(git("rev-parse", "HEAD"), commit, "The cache checkout moved");
    assert.equal(
      git("status", "--porcelain=v1", "--untracked-files=all"),
      "",
      "The cache checkout is dirty",
    );
    const tree = execFileSync(
      "git",
      [
        "--no-optional-locks",
        "-C",
        cache,
        "ls-tree",
        "-rz",
        "--full-tree",
        commit,
      ],
      { env: gitEnvironment },
    );
    return tree
      .toString("utf8")
      .split("\0")
      .filter(Boolean)
      .map((entry) => {
        const separator = entry.indexOf("\t");
        const [mode, type, blob] = entry.slice(0, separator).split(" ");
        const name = entry.slice(separator + 1);
        assert(
          type === "blob" && ["100644", "100755", "120000"].includes(mode),
          `Unsupported tree entry: ${entry}`,
        );
        assert(
          inside(source, path.resolve(source, name)),
          `Source path escapes output: ${name}`,
        );
        if (mode === "120000") {
          const target = execFileSync(
            "git",
            ["--no-optional-locks", "-C", cache, "show", `${commit}:${name}`],
            { env: gitEnvironment, encoding: "utf8" },
          );
          assert(
            !path.isAbsolute(target) &&
              inside(source, path.resolve(source, path.dirname(name), target)),
            `Source link escapes output: ${name}`,
          );
        }
        return { path: name, mode, blob };
      })
      .sort((left, right) => byteOrder(left.path, right.path));
  }

  function verifySource(entries) {
    return entries.map((entry) => {
      const filename = path.join(source, entry.path);
      guard.check(path.dirname(filename), "directory");
      const stat = lstatSync(filename);
      if (entry.mode === "120000") {
        assert(stat.isSymbolicLink(), `Source link replaced: ${entry.path}`);
        const target = readlinkSync(filename);
        const data = Buffer.from(target);
        assert.equal(
          createHash("sha1")
            .update(`blob ${data.length}\0`)
            .update(data)
            .digest("hex"),
          entry.blob,
          `Source link changed: ${entry.path}`,
        );
        return {
          ...entry,
          type: "symlink",
          bytes: data.length,
          sha256: hash(data),
          target,
        };
      }
      assert(stat.isFile(), `Source file replaced: ${entry.path}`);
      guard.check(filename);
      const content = fileHashes(filename);
      assert.equal(
        content.gitBlob,
        entry.blob,
        `Source content changed: ${entry.path}`,
      );
      assert.equal(
        Boolean(stat.mode & 0o111),
        entry.mode === "100755",
        `Source mode changed: ${entry.path}`,
      );
      return {
        ...entry,
        type: "file",
        bytes: content.bytes,
        sha256: content.sha256,
      };
    });
  }

  function writeEvidence(name, data) {
    const filename = path.join(evidence, name);
    guard.write(filename, data);
    return { path: name, sha256: hash(data), bytes: Buffer.byteLength(data) };
  }

  function prepareToolchain() {
    assert.equal(
      process.version,
      "v24.13.0",
      "This preparation profile uses Node 24.13.0",
    );
    assert.equal(
      process.platform,
      "linux",
      "This profile uses Linux x64 tools",
    );
    assert.equal(process.arch, "x64", "This profile uses Linux x64 tools");
    for (const pin of [toolPins.node, toolPins.pnpm])
      preparePinnedTool(guard, pin, { download: true });
  }

  function materialize() {
    memoryLimit();
    guard.preflight();
    const entries = sourceEntries();
    prepareToolchain();
    const archive = path.join(output, `zod-${commit}.tar`);
    const archivePin = {
      integrity: `sha256-${sourceArchiveHash}`,
      allowLinks: true,
    };
    guard.check(archive);
    if (!optionalStat(archive)) {
      const file = guard.stagedFile(archive);
      try {
        execFileSync(
          "git",
          [
            "--no-optional-locks",
            "-C",
            cache,
            "archive",
            "--format=tar",
            commit,
          ],
          {
            env: gitEnvironment,
            stdio: ["ignore", file.descriptor, "pipe"],
          },
        );
        file.close();
        readPinnedArchive(guard, file.temporary, archivePin);
        file.publish();
      } finally {
        file.dispose();
      }
    }
    readPinnedArchive(guard, archive, archivePin);
    if (!optionalStat(source))
      extractPinnedArchive(guard, archive, archivePin, source);
    guard.tree(source, true);
    const files = verifySource(entries);
    assert.equal(
      fileHashes(path.join(source, "pnpm-lock.yaml")).sha256,
      lockHash,
    );
    assert.equal(
      JSON.parse(readFileSync(path.join(source, "package.json"), "utf8"))
        .packageManager,
      manager,
    );
    const manifest = writeEvidence("source-files.jsonl", jsonLines(files));
    const provenance = {
      commit,
      gitTree: git("rev-parse", `${commit}^{tree}`),
      cache,
      source,
      archive: { path: path.basename(archive), ...fileHashes(archive) },
      sourceManifest: manifest,
      trackedFiles: files.length,
      sourceBytes: files.reduce((total, file) => total + file.bytes, 0),
    };
    writeEvidence("source.json", JSON.stringify(provenance, null, 2) + "\n");
    return provenance;
  }

  function memoryLimit() {
    const cgroup = readFileSync("/proc/self/cgroup", "utf8")
      .split("\n")
      .find((line) => line.startsWith("0::"))
      ?.slice(3);
    assert(cgroup, "A cgroup-v2 memory scope is required for preparation");
    const filename = path.join("/sys/fs/cgroup", cgroup, "memory.max");
    const value = readFileSync(filename, "utf8").trim();
    assert(
      value !== "max" && Number(value) > 0 && Number(value) <= 2 * 1024 ** 3,
      "Run preparation inside a memory scope of at most 2 GiB",
    );
    assert.equal(
      readFileSync(
        path.join(path.dirname(filename), "memory.swap.max"),
        "utf8",
      ).trim(),
      "0",
      "Run preparation with MemorySwapMax=0",
    );
    return { path: filename, bytes: Number(value) };
  }

  async function logged(args, name) {
    const filename = path.join(evidence, name);
    const log = guard.stagedFile(filename);
    let result;
    try {
      const child = spawnPinnedTool(guard, toolPins.pnpm, args, {
        runtime: toolPins.node,
        cwd: source,
        env: environment,
        stdio: ["ignore", "pipe", "pipe"],
      });
      child.stdout.on("data", (data) => {
        process.stdout.write(data);
        writeFileSync(log.descriptor, data);
      });
      child.stderr.on("data", (data) => {
        process.stderr.write(data);
        writeFileSync(log.descriptor, data);
      });
      result = await new Promise((resolve, reject) => {
        child.on("error", reject);
        child.on("close", (code, signal) => resolve({ code, signal }));
      });
      log.publish();
    } finally {
      log.dispose();
    }
    assert.equal(result.code, 0, `pnpm failed. See ${filename}`);
    return {
      command: [nodeBinary, pnpmEntry, ...args],
      log: { path: name, ...fileHashes(filename) },
    };
  }

  async function install() {
    const limit = memoryLimit();
    materialize();
    writeEvidence(
      "install-attempt.json",
      JSON.stringify(
        {
          manager,
          scripts: false,
          pnpmfileHooks: false,
          memoryLimit: limit,
          nodeHeapMiB: 768,
          networkConcurrency: 4,
          childConcurrency: 1,
          packageWorkers: 1,
          pnpmWorkerEnvironment: environment.PNPM_WORKERS,
        },
        null,
        2,
      ) + "\n",
    );
    await logged(["--version"], "pnpm-version.log");
    assert.equal(
      readFileSync(
        guard.check(path.join(evidence, "pnpm-version.log")),
        "utf8",
      ).trim(),
      "10.12.1",
    );
    const result = await logged(
      [
        "install",
        "--frozen-lockfile",
        "--ignore-scripts",
        "--ignore-pnpmfile",
        "--package-import-method=copy",
        "--network-concurrency=4",
        "--child-concurrency=1",
        "--store-dir",
        store,
        "--reporter=append-only",
      ],
      "install.log",
    );
    verifySource(sourceEntries());
    writeEvidence(
      "install.json",
      JSON.stringify(
        {
          manager,
          scripts: false,
          pnpmfileHooks: false,
          memoryLimit: limit,
          nodeHeapMiB: 768,
          networkConcurrency: 4,
          childConcurrency: 1,
          packageWorkers: 1,
          pnpmWorkerEnvironment: environment.PNPM_WORKERS,
          ...result,
        },
        null,
        2,
      ) + "\n",
    );
  }

  function walk(root, callback) {
    for (const entry of readdirSync(root, { withFileTypes: true }).sort(
      (left, right) => byteOrder(left.name, right.name),
    )) {
      const filename = path.join(root, entry.name);
      if (entry.isDirectory()) walk(filename, callback);
      else callback(filename, entry);
    }
  }

  function audit() {
    const provenance = materialize();
    const installation = JSON.parse(
      readFileSync(path.join(evidence, "install.json"), "utf8"),
    );
    const metadataPaths = sourceEntries()
      .map((entry) => entry.path)
      .filter(
        (name) =>
          name.endsWith("package.json") ||
          name.endsWith("pnpm-lock.yaml") ||
          (name.includes("tsconfig") && name.endsWith(".json")) ||
          [
            "pnpm-workspace.yaml",
            ".npmrc",
            ".nvmrc",
            "AGENTS.md",
            ".husky/pre-commit",
            ".husky/pre-push",
          ].includes(name),
      );
    const metadata = metadataPaths.map((name) => ({
      path: name,
      ...fileHashes(path.join(source, name)),
    }));
    const packages = [];
    const packageFiles = [];
    const virtualStore = path.join(source, "node_modules/.pnpm");
    for (const locator of readdirSync(virtualStore).sort(byteOrder)) {
      const modules = path.join(virtualStore, locator, "node_modules");
      if (locator === "node_modules" || !existsSync(modules)) continue;
      const candidates = readdirSync(modules).flatMap((name) =>
        name.startsWith("@")
          ? readdirSync(path.join(modules, name)).map((child) =>
              path.join(modules, name, child),
            )
          : [path.join(modules, name)],
      );
      for (const root of candidates.sort(byteOrder)) {
        if (
          !lstatSync(root).isDirectory() ||
          !existsSync(path.join(root, "package.json"))
        )
          continue;
        const manifest = JSON.parse(
          readFileSync(path.join(root, "package.json"), "utf8"),
        );
        const location = path.relative(source, root);
        const files = [];
        walk(root, (filename, entry) => {
          const relative = path.relative(root, filename);
          const stat = lstatSync(filename);
          if (entry.isSymbolicLink())
            files.push({
              path: relative,
              type: "symlink",
              target: readlinkSync(filename),
            });
          else {
            assert(stat.isFile(), `Unsupported package entry: ${filename}`);
            const { bytes, sha256 } = fileHashes(filename);
            files.push({
              path: relative,
              type: "file",
              executable: Boolean(stat.mode & 0o111),
              bytes,
              sha256,
            });
          }
        });
        files.sort((left, right) => byteOrder(left.path, right.path));
        packageFiles.push(
          ...files.map((file) => ({ package: location, ...file })),
        );
        packages.push({
          locator,
          path: location,
          name: manifest.name ?? null,
          version: manifest.version ?? null,
          packageJsonSha256: fileHashes(path.join(root, "package.json")).sha256,
          contentSha256: hash(jsonLines(files)),
          files: files.length,
          bytes: files.reduce((total, file) => total + (file.bytes ?? 0), 0),
          lifecycleScripts: Object.fromEntries(
            Object.entries(manifest.scripts ?? {}).filter(([name]) =>
              ["preinstall", "install", "postinstall", "prepare"].includes(
                name,
              ),
            ),
          ),
        });
      }
    }
    packages.sort((left, right) => byteOrder(left.path, right.path));
    const links = [];
    const moduleRoots = [
      path.join(source, "node_modules"),
      ...readdirSync(path.join(source, "packages"))
        .map((name) => path.join(source, "packages", name, "node_modules"))
        .filter(existsSync),
    ];
    for (const root of moduleRoots)
      walk(root, (filename, entry) => {
        if (!entry.isSymbolicLink()) return;
        const target = readlinkSync(filename);
        let resolved;
        try {
          resolved = realpathSync.native(filename);
        } catch {
          resolved = null;
        }
        links.push({
          path: path.relative(source, filename),
          target,
          resolved: resolved && path.relative(source, resolved),
          exists: resolved !== null,
          insideSource: resolved !== null && inside(source, resolved),
          workspace:
            resolved !== null &&
            inside(path.join(source, "packages"), resolved),
        });
      });
    links.sort((left, right) => byteOrder(left.path, right.path));
    assert(
      links.every((entry) => entry.exists && entry.insideSource),
      "A dependency link is broken or leaves the prepared source",
    );
    const require = createRequire(script);
    preparePinnedTool(guard, toolPins.yaml, { download: true });
    const yaml = require(verifyPinnedTool(guard, toolPins.yaml).entry);
    const moduleState = yaml.parse(
      readFileSync(path.join(source, "node_modules/.modules.yaml"), "utf8"),
    );
    assert.equal(moduleState.packageManager, manager);
    assert.deepEqual(moduleState.included, {
      dependencies: true,
      devDependencies: true,
      optionalDependencies: true,
    });
    preparePinnedTool(guard, toolPins.typescript, { download: true });
    const tsFilename = verifyPinnedTool(guard, toolPins.typescript).entry;
    const ts = require(tsFilename);
    const configName = path.join(source, "packages/zod/tsconfig.json");
    const config = ts.getParsedCommandLineOfConfigFile(
      configName,
      {},
      {
        ...ts.sys,
        onUnRecoverableConfigFileDiagnostic(error) {
          throw new Error(
            ts.flattenDiagnosticMessageText(error.messageText, "\n"),
          );
        },
      },
    );
    assert(
      config && config.errors.length === 0,
      "The original Zod config did not parse",
    );
    assert.equal(config.options.strict, true);
    assert.deepEqual(config.options.types, ["vitest", "recheck"]);
    assert.deepEqual(config.options.customConditions, ["@zod/source"]);
    const roots = config.fileNames
      .map((name) => path.relative(source, name))
      .sort(byteOrder);
    const rootList = roots.join("\n") + "\n";
    assert.equal(
      hash(rootList),
      rootsHash,
      "The selected source roots changed",
    );
    const directives = config.options.types.map((name) => {
      const resolved = ts.resolveTypeReferenceDirective(
        name,
        configName,
        config.options,
        ts.sys,
      ).resolvedTypeReferenceDirective;
      assert(resolved, `Missing selected type package: ${name}`);
      return {
        name,
        path: path.relative(source, resolved.resolvedFileName),
        sha256: fileHashes(resolved.resolvedFileName).sha256,
      };
    });
    const resolutionProbes = [
      "zod",
      "zod/v3",
      "zod/v4",
      "zod/mini",
      "zod/v4/core",
    ].map((name) => {
      const resolved = ts.resolveModuleName(
        name,
        path.join(source, "packages/zod/src/index.ts"),
        config.options,
        ts.sys,
        undefined,
        undefined,
        ts.ModuleKind.ESNext,
      ).resolvedModule;
      assert(
        resolved &&
          inside(
            path.join(source, "packages/zod/src"),
            resolved.resolvedFileName,
          ),
        `Source condition did not resolve ${name}`,
      );
      return {
        name,
        path: path.relative(source, resolved.resolvedFileName),
        sha256: fileHashes(resolved.resolvedFileName).sha256,
      };
    });
    const tools = [];
    for (const pin of Object.values(toolPins)) {
      const { root } = verifyPinnedTool(guard, pin);
      walk(root, (filename, entry) => {
        const name = path.relative(output, filename);
        assert(entry.isFile(), `Unexpected verified tool entry: ${name}`);
        tools.push({
          path: name,
          type: "file",
          executable: Boolean(statSync(filename).mode & 0o111),
          ...fileHashes(filename),
        });
      });
    }
    tools.sort((left, right) => byteOrder(left.path, right.path));
    const generatedState = [
      "node_modules/.modules.yaml",
      "node_modules/.pnpm/lock.yaml",
    ].map((name) => ({ path: name, ...fileHashes(path.join(source, name)) }));
    const nodeHeader = process.report.getReport().header;
    const files = [
      writeEvidence("metadata-files.jsonl", jsonLines(metadata)),
      writeEvidence("packages.jsonl", jsonLines(packages)),
      writeEvidence("package-files.jsonl", jsonLines(packageFiles)),
      writeEvidence("dependency-links.jsonl", jsonLines(links)),
      writeEvidence("tool-files.jsonl", jsonLines(tools)),
      writeEvidence("zod-root-files.txt", rootList),
    ];
    const report = {
      ...provenance,
      installation,
      machine: {
        platform: process.platform,
        architecture: process.arch,
        kernel: os.release(),
        libc: nodeHeader.glibcVersionRuntime ?? null,
        cpu: os.cpus()[0]?.model ?? null,
        logicalCpus: os.cpus().length,
      },
      toolchain: {
        node: {
          version: process.version,
          path: path.relative(output, nodeBinary),
          sha256: fileHashes(nodeBinary).sha256,
        },
        pnpm: "10.12.1",
        pnpmArchiveIntegrity: toolPins.pnpm.integrity,
        archives: Object.fromEntries(
          Object.entries(toolPins).map(([name, pin]) => [
            name,
            {
              url: pin.url,
              integrity: pin.integrity,
              path: `toolchain/archives/${pin.archive}`,
            },
          ]),
        ),
        typescript: {
          version: ts.version,
          path: path.relative(output, tsFilename),
          sha256: fileHashes(tsFilename).sha256,
        },
      },
      config: {
        path: "packages/zod/tsconfig.json",
        chain: [
          ...(config.options.configFile.extendedSourceFiles ?? []),
          configName,
        ].map((name) => ({
          path: path.relative(source, name),
          sha256: fileHashes(name).sha256,
        })),
        strict: config.options.strict,
        noEmit: config.options.noEmit,
        target: ts.ScriptTarget[config.options.target],
        libraries: config.options.lib,
        jsx: ts.JsxEmit[config.options.jsx],
        exactOptionalPropertyTypes: config.options.exactOptionalPropertyTypes,
        skipLibCheck: config.options.skipLibCheck,
        module: ts.ModuleKind[config.options.module],
        moduleResolution:
          ts.ModuleResolutionKind[config.options.moduleResolution],
        customConditions: config.options.customConditions,
        types: config.options.types,
        roots: roots.length,
        tests: roots.filter(
          (name) =>
            /(^|\/)(tests|__tests__)\//.test(name) ||
            /\.(test|spec)\.ts$/.test(name),
        ).length,
        rootListSha256: hash(rootList),
        typeDirectives: directives,
        resolutionProbes,
      },
      dependencies: {
        physicalPackages: packages.length,
        packageFiles: packageFiles.length,
        packageBytes: packages.reduce((total, entry) => total + entry.bytes, 0),
        links: links.length,
        brokenLinks: links.filter((entry) => !entry.exists),
        linksOutsideSource: links.filter(
          (entry) => entry.exists && !entry.insideSource,
        ),
        workspaceLinks: links.filter((entry) => entry.workspace),
        packagesWithLifecycleScripts: packages.filter(
          (entry) => Object.keys(entry.lifecycleScripts).length !== 0,
        ).length,
        included: moduleState.included,
        pendingBuilds: moduleState.pendingBuilds ?? [],
        platformSkipped: moduleState.skipped ?? [],
        nodeLinker: moduleState.nodeLinker,
        generatedState,
      },
      evidenceFiles: files,
      claims: {
        sourceUnchanged: true,
        configUnchanged: true,
        scriptsExecuted: false,
        projectBuildRun: false,
        typecheckRun: false,
        rustBuildRun: false,
        compilerParityMeasured: false,
      },
    };
    const receipt = writeEvidence(
      "preparation.json",
      JSON.stringify(report, null, 2) + "\n",
    );
    console.log(
      JSON.stringify(
        {
          source,
          commit,
          roots: roots.length,
          physicalPackages: packages.length,
          workspaceLinks: report.dependencies.workspaceLinks,
          brokenLinks: report.dependencies.brokenLinks.length,
          receipt,
        },
        null,
        2,
      ),
    );
  }

  return { materialize, install, audit };
}

if (process.argv[1] && path.resolve(process.argv[1]) === script) {
  const action = process.argv[2];
  assert(
    ["materialize", "install", "audit"].includes(action),
    "Use materialize, install, or audit",
  );
  const main = path.dirname(
    command("git", ["rev-parse", "--path-format=absolute", "--git-common-dir"]),
  );
  const output = path.resolve(
    process.env.ZOD_INPUT_OUT ?? path.join(main, "target/project-inputs/zod"),
  );
  const cache = realpathSync.native(
    process.env.ZOD_REPO_CACHE ?? "/home/theo/.explore/repos/colinhacks__zod",
  );
  const preparation = createPreparation(output, cache);
  const result = await preparation[action]();
  if (action === "materialize") console.log(JSON.stringify(result, null, 2));
}
