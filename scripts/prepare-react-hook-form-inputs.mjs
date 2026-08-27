import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import {
  closeSync,
  constants,
  existsSync,
  fstatSync,
  ftruncateSync,
  lstatSync,
  mkdirSync,
  openSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  realpathSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { createRequire } from 'node:module';
import { homedir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const pin = 'bb3360f4db62489ed4ab4e09ccb4211a275da707';
const nodeVersion = '22.22.0';
const pnpmVersion = '11.7.0';
const nodeArchiveSha256 = '9aa8e9d2298ab68c600bd6fb86a6c13bce11a4eca1ba9b39d79fa021755d7c37';
const pnpmArchiveSha256 = 'deafa7ec98a1218b6a047289b92fbe2395c1e22d3495bb711653013218ee15ee';
const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');
const hashFile = (filename) => sha256(readFileSync(filename));
export const toolPins = Object.freeze(
  [
    {
      directory: `node-v${nodeVersion}-linux-x64`,
      archive: `node-v${nodeVersion}-linux-x64.tar.xz`,
      archiveSha256: nodeArchiveSha256,
      treeSha256: '7d651642d670837f30481a8dcae4c64ea2f2844e260562287f9b86024f756a0b',
    },
    {
      directory: 'pnpm',
      archive: `pnpm-${pnpmVersion}.tgz`,
      archiveSha256: pnpmArchiveSha256,
      treeSha256: '6afe3ac41ccdec75532fd42b6644eb1143b1d4105a313a0c86e706f399e961a1',
    },
  ].map((tool) => Object.freeze(tool)),
);
const stageNames = [
  'snapshot',
  'tools',
  'install-root',
  'probe-tools',
  'build-library',
  'install-app',
  'evidence',
];
const toolEntries = {
  'tools/bin/node': `../node-v${nodeVersion}-linux-x64/bin/node`,
  'tools/bin/npm': `../node-v${nodeVersion}-linux-x64/bin/npm`,
  'tools/bin/pnpm': '../pnpm/bin/pnpm.mjs',
};
const bootstrapPath = '/usr/bin:/bin';
const bootstrap = Object.freeze({
  git: '/usr/bin/git',
  tar: '/usr/bin/tar',
  systemdRun: '/usr/bin/systemd-run',
  which: '/usr/bin/which',
});
const managedDirectories = [
  'tools',
  'tools/bin',
  'logs',
  'evidence',
  'home',
  'cache',
  'cache/node-compile',
  'data',
  'config',
  'tmp',
];

const inside = (root, filename) => filename === root || filename.startsWith(`${root}${path.sep}`);

// Check every existing ancestor with lstat, including dangling links.
export function assertDestination(output, filename, kind = 'file') {
  const root = path.resolve(output);
  const target = path.resolve(filename);
  assert(inside(root, target), `Destination leaves the input directory: ${target}`);
  let current = path.parse(target).root;
  for (const part of target.slice(current.length).split(path.sep)) {
    current = path.join(current, part);
    const stat = lstatSync(current, { throwIfNoEntry: false });
    if (!stat) continue;
    const leaf = current === target;
    if (leaf && kind === 'symlink' && stat.isSymbolicLink()) continue;
    assert(!stat.isSymbolicLink(), `Symlink at managed destination: ${current}`);
    assert(
      leaf && kind !== 'directory' ? stat.isFile() : stat.isDirectory(),
      `Wrong destination kind: ${current}`,
    );
    if (leaf && kind === 'file')
      assert.equal(stat.nlink, 1, `Shared file at managed destination: ${current}`);
  }
}

export function assertManagedPaths(output) {
  for (const name of [
    '',
    ...managedDirectories,
    'pnpm-store',
    'source',
    'source/app',
    'source/dist',
    'source/node_modules',
    'source/app/node_modules',
    ...toolPins.map((tool) => `tools/${tool.directory}`),
  ]) {
    assertDestination(output, path.join(output, name), 'directory');
  }
  const packageDirectories = [
    'source/node_modules/',
    'source/app/node_modules/',
    ...toolPins.map((tool) => `tools/${tool.directory}/`),
  ];
  const sharedFiles = new Map();
  function visit(directory) {
    for (const name of readdirSync(directory)) {
      const filename = path.join(directory, name);
      const stat = lstatSync(filename);
      const relative = path.relative(output, filename);
      if (relative.startsWith('tools/bin/')) {
        assert(Object.hasOwn(toolEntries, relative), `Unexpected tool command: ${filename}`);
      }
      if (Object.hasOwn(toolEntries, relative)) {
        assert(stat.isSymbolicLink(), `Expected a tool link: ${filename}`);
        assert.equal(
          readlinkSync(filename),
          toolEntries[relative],
          `Changed tool link: ${filename}`,
        );
      }
      if (stat.isDirectory()) visit(filename);
      else if (stat.isSymbolicLink()) {
        if (/^pnpm-store\/v11\/projects\/[a-f0-9]+$/.test(relative)) {
          assert(
            ['../../../source', '../../../source/app'].includes(readlinkSync(filename)),
            `Changed store project link: ${filename}`,
          );
        } else if (!Object.hasOwn(toolEntries, relative)) {
          assert(
            packageDirectories.some((prefix) => relative.startsWith(prefix)),
            `Symlink at managed destination: ${filename}`,
          );
        }
        const resolved = realpathSync(filename);
        assert(inside(output, resolved), `Symlink leaves the input directory: ${filename}`);
      } else {
        assert(stat.isFile(), `Unsupported managed entry: ${filename}`);
        if (stat.nlink > 1) {
          const key = `${stat.dev}:${stat.ino}`;
          const shared = sharedFiles.get(key) ?? { filename, links: stat.nlink, seen: 0 };
          shared.seen += 1;
          sharedFiles.set(key, shared);
        }
      }
    }
  }
  if (lstatSync(output, { throwIfNoEntry: false })) visit(output);
  for (const shared of sharedFiles.values()) {
    assert.equal(
      shared.seen,
      shared.links,
      `Hard link leaves the input directory: ${shared.filename}`,
    );
  }
}

export function makeDirectory(output, filename) {
  assertDestination(output, filename, 'directory');
  mkdirSync(filename, { recursive: true });
}

export function openDestination(output, filename) {
  assertDestination(output, filename);
  const fd = openSync(
    filename,
    constants.O_CREAT | constants.O_WRONLY | constants.O_NOFOLLOW,
    0o644,
  );
  try {
    const stat = fstatSync(fd);
    assert(stat.isFile() && stat.nlink === 1, `Invalid writable file: ${filename}`);
    ftruncateSync(fd, 0);
    return fd;
  } catch (error) {
    closeSync(fd);
    throw error;
  }
}

export function writeDestination(output, filename, bytes) {
  const fd = openDestination(output, filename);
  try {
    writeFileSync(fd, bytes);
  } finally {
    closeSync(fd);
  }
}

// These catalogs include directory and file modes as well as bytes and link text.
export function toolTreeDigest(root) {
  const entries = [];
  function visit(directory, relative = '.') {
    const stat = lstatSync(directory);
    assert(stat.isDirectory() && !stat.isSymbolicLink(), `Invalid tool directory: ${directory}`);
    entries.push({ path: relative, kind: 'directory', mode: stat.mode & 0o777 });
    for (const name of readdirSync(directory).sort()) {
      const filename = path.join(directory, name);
      const item = relative === '.' ? name : `${relative}/${name}`;
      const child = lstatSync(filename);
      if (child.isSymbolicLink())
        entries.push({ path: item, kind: 'symlink', target: readlinkSync(filename) });
      else if (child.isDirectory()) visit(filename, item);
      else {
        assert(child.isFile(), `Invalid tool entry: ${filename}`);
        entries.push({
          path: item,
          kind: 'file',
          mode: child.mode & 0o777,
          bytes: child.size,
          sha256: hashFile(filename),
        });
      }
    }
  }
  visit(root);
  entries.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
  return sha256(entries.map((entry) => JSON.stringify(entry)).join('\n') + '\n');
}

export function verifyExtractedTools(output) {
  for (const tool of toolPins) {
    const archive = path.join(output, 'tools', tool.archive);
    const directory = path.join(output, 'tools', tool.directory);
    assertDestination(output, archive);
    assertDestination(output, directory, 'directory');
    assert.equal(hashFile(archive), tool.archiveSha256, `Changed tool archive: ${archive}`);
    assert.equal(
      toolTreeDigest(directory),
      tool.treeSha256,
      `Changed extracted tool: ${directory}`,
    );
  }
}

export function verifyToolEntryLinks(output) {
  for (const [relative, target] of Object.entries(toolEntries)) {
    const link = path.join(output, relative);
    assertDestination(output, link, 'symlink');
    assert(
      lstatSync(link, { throwIfNoEntry: false })?.isSymbolicLink(),
      `Missing tool link: ${link}`,
    );
    assert.equal(readlinkSync(link), target, `Changed tool link: ${link}`);
    assert(inside(output, realpathSync(link)), `Tool link leaves the input directory: ${link}`);
  }
}

export async function main(args, options = {}) {
  assert(
    args.length === 1 && (args[0] === 'all' || stageNames.includes(args[0])),
    `Use one of: all, ${stageNames.join(', ')}`,
  );
  const stage = args[0];
  const directory = path.dirname(fileURLToPath(import.meta.url));
  const readEnv = {
    ...process.env,
    GIT_OPTIONAL_LOCKS: '0',
    NODE_DISABLE_COMPILE_CACHE: '1',
    PATH: bootstrapPath,
  };
  delete readEnv.NODE_COMPILE_CACHE;
  const git = (...args) =>
    execFileSync(bootstrap.git, ['-c', 'core.fsmonitor=false', ...args], {
      cwd: directory,
      env: readEnv,
      encoding: 'utf8',
    }).trim();
  const workspace =
    options.workspace ??
    path.dirname(git('rev-parse', '--path-format=absolute', '--git-common-dir'));
  assert.equal(
    path.resolve(workspace),
    workspace,
    'The workspace path must be absolute and normalized.',
  );
  const output = path.join(workspace, 'target/project-inputs/react-hook-form');
  const cache = path.join(homedir(), '.explore/repos/react-hook-form__react-hook-form');
  const source = path.join(output, 'source');
  const tools = path.join(output, 'tools');
  const evidence = path.join(output, 'evidence');
  const nodeHome = path.join(tools, `node-v${nodeVersion}-linux-x64`);
  const node = path.join(nodeHome, 'bin/node');
  const pnpm = path.join(tools, 'pnpm/bin/pnpm.mjs');
  const locks = {
    'pnpm-lock.yaml': '7acb3dc72842c76da85d5a9dd0e8c589c18250c2b2e46b0dbe4948798df0d14a',
    'app/pnpm-lock.yaml': '5c31f94a9ae847852866bafbac415bcc68273c678334c3b2fe9277800cce57ea',
  };
  const rootPins = {
    'tsconfig.json': [109, '7963c7ea867f902a71da242554466828fc169034c75c66920cd6d2c41378bae0'],
    'app/tsconfig.json': [45, 'af71e8cab3b67cb538d918b5828317f1e16bc5bdfbb75e71585bf590c452c203'],
  };
  const json = (filename) => JSON.parse(readFileSync(filename, 'utf8'));
  const write = (filename, bytes) => writeDestination(output, filename, bytes);
  const mkdir = (filename) => makeDirectory(output, filename);
  const save = (filename, value) => write(filename, `${JSON.stringify(value, null, 2)}\n`);
  const relative = (filename) => path.relative(output, filename);
  const require = createRequire(import.meta.url);

  assertManagedPaths(output);
  if (
    lstatSync(nodeHome, { throwIfNoEntry: false }) &&
    lstatSync(path.join(tools, 'pnpm'), { throwIfNoEntry: false })
  ) {
    verifyExtractedTools(output);
  }
  process.umask(0o022);
  for (const name of managedDirectories) mkdir(path.join(output, name));

  const env = {
    ...process.env,
    GIT_OPTIONAL_LOCKS: '0',
    HOME: path.join(output, 'home'),
    XDG_CACHE_HOME: path.join(output, 'cache'),
    XDG_DATA_HOME: path.join(output, 'data'),
    XDG_CONFIG_HOME: path.join(output, 'config'),
    TMPDIR: path.join(output, 'tmp'),
    npm_config_cache: path.join(output, 'cache/npm'),
    npm_config_userconfig: path.join(output, 'config/npmrc'),
    COREPACK_HOME: path.join(output, 'cache/corepack'),
    COREPACK_ENABLE_AUTO_PIN: '0',
    PNPM_HOME: path.join(tools, 'bin'),
    HUSKY: '0',
    CI: 'true',
    NODE_OPTIONS: '--max-old-space-size=1536',
    NODE_COMPILE_CACHE: path.join(output, 'cache/node-compile'),
    PATH: bootstrapPath,
  };
  if (!existsSync(env.npm_config_userconfig)) write(env.npm_config_userconfig, '');

  function toolEnvironment() {
    assertManagedPaths(output);
    verifyExtractedTools(output);
    verifyToolEntryLinks(output);
    assertDestination(output, env.NODE_COMPILE_CACHE, 'directory');
    return {
      ...env,
      PATH: `${path.join(tools, 'bin')}:${path.join(nodeHome, 'bin')}:${bootstrapPath}`,
    };
  }

  function run(name, executable, args, cwd = source, stdoutFile) {
    assert(
      [bootstrap.git, bootstrap.tar, node].includes(executable),
      `Unverified command: ${executable}`,
    );
    assertManagedPaths(output);
    const childEnv = executable === node ? toolEnvironment() : env;
    const historyPath = path.join(evidence, 'commands.json');
    const history = existsSync(historyPath) ? json(historyPath) : [];
    const attempt = history.filter((row) => row.name === name).length + 1;
    const logfile = path.join(output, 'logs', `${name}${attempt === 1 ? '' : `-${attempt}`}.log`);
    console.log(`${name}: ${executable} ${args.join(' ')}`);
    const fd = openDestination(output, logfile);
    let artifactFd = fd;
    const bounded =
      name.startsWith('install-') || name.startsWith('build-') || name === 'probe-tools';
    const scopeArgs = [
      '--user',
      '--scope',
      '--quiet',
      '--collect',
      '-p',
      'MemoryMax=2G',
      '-p',
      'MemorySwapMax=0',
      executable,
      ...args,
    ];
    let result;
    try {
      if (stdoutFile !== undefined) artifactFd = openDestination(output, stdoutFile);
      result = spawnSync(bounded ? bootstrap.systemdRun : executable, bounded ? scopeArgs : args, {
        cwd,
        env: childEnv,
        stdio: ['ignore', artifactFd, fd],
      });
    } finally {
      if (artifactFd !== fd) closeSync(artifactFd);
      closeSync(fd);
    }
    history.push({
      name,
      executable,
      args,
      cwd,
      status: result.status,
      signal: result.signal,
      memoryMaxBytes: bounded ? 2147483648 : null,
      environment: { path: childEnv.PATH, nodeCompileCache: childEnv.NODE_COMPILE_CACHE },
      log: logfile,
    });
    save(historyPath, history);
    assertManagedPaths(output);
    if (result.error) throw result.error;
    assert.equal(result.status, 0, `${name} failed. See ${logfile}`);
  }

  function verifyCache() {
    assert.equal(
      execFileSync(bootstrap.git, ['-c', 'core.fsmonitor=false', 'rev-parse', 'HEAD'], {
        cwd: cache,
        env: readEnv,
        encoding: 'utf8',
      }).trim(),
      pin,
    );
    assert.equal(
      execFileSync(
        bootstrap.git,
        ['-c', 'core.fsmonitor=false', 'status', '--porcelain=v1', '--untracked-files=all'],
        {
          cwd: cache,
          env: readEnv,
          encoding: 'utf8',
        },
      ),
      '',
      'The exploration cache must be clean.',
    );
    for (const [filename, expected] of Object.entries(locks)) {
      assert.equal(hashFile(path.join(cache, filename)), expected, filename);
    }
  }

  function sourceFiles() {
    return execFileSync(bootstrap.git, ['-c', 'core.fsmonitor=false', 'ls-files', '-z'], {
      cwd: cache,
      env: readEnv,
      encoding: 'utf8',
    })
      .split('\0')
      .filter(Boolean)
      .sort();
  }

  function verifySource() {
    assertDestination(output, source, 'directory');
    verifyCache();
    return sourceFiles().map((filename) => {
      const original = path.join(cache, filename);
      const copied = path.join(source, filename);
      assert.equal(
        lstatSync(copied).isSymbolicLink(),
        lstatSync(original).isSymbolicLink(),
        filename,
      );
      if (lstatSync(original).isSymbolicLink()) {
        const target = readlinkSync(original);
        assert.equal(readlinkSync(copied), target, filename);
        return { path: filename, kind: 'symlink', target };
      }
      const digest = hashFile(original);
      assert.equal(hashFile(copied), digest, `Source changed: ${filename}`);
      return { path: filename, kind: 'file', sha256: digest };
    });
  }

  function snapshot() {
    verifyCache();
    const archive = path.join(output, 'source.tar');
    if (!existsSync(source)) {
      run('source-archive', bootstrap.git, ['archive', '--format=tar', pin], cache, archive);
      mkdir(source);
      assert.equal(readdirSync(source).length, 0, 'Source extraction requires an empty directory.');
      run('source-extract', bootstrap.tar, ['-xf', archive, '-C', source], output);
    }
    const files = verifySource();
    save(path.join(evidence, 'source-files.json'), files);
    save(path.join(evidence, 'source.json'), {
      repository: 'react-hook-form/react-hook-form',
      commit: pin,
      tree: execFileSync(
        bootstrap.git,
        ['-c', 'core.fsmonitor=false', 'rev-parse', `${pin}^{tree}`],
        {
          cwd: cache,
          env: readEnv,
          encoding: 'utf8',
        },
      ).trim(),
      cache,
      source,
      fileCount: files.length,
      archive,
      archiveSha256: hashFile(archive),
      locks,
      sourceFilesSha256: hashFile(path.join(evidence, 'source-files.json')),
    });
  }

  async function fetchBytes(url) {
    const response = await fetch(url, { signal: AbortSignal.timeout(120_000) });
    assert(response.ok, `${url}: HTTP ${response.status}`);
    return Buffer.from(await response.arrayBuffer());
  }

  async function provisionTools() {
    assert.equal(process.platform, 'linux');
    assert.equal(process.arch, 'x64');
    const archiveName = `node-v${nodeVersion}-linux-x64.tar.xz`;
    const nodeBase = `https://nodejs.org/dist/v${nodeVersion}`;
    const sumsPath = path.join(tools, 'node-SHASUMS256.txt');
    if (!existsSync(sumsPath)) write(sumsPath, await fetchBytes(`${nodeBase}/SHASUMS256.txt`));
    const checksum = readFileSync(sumsPath, 'utf8')
      .split('\n')
      .map((line) => line.trim().split(/\s+/))
      .find(([, name]) => name === archiveName)?.[0];
    assert.match(checksum ?? '', /^[a-f0-9]{64}$/);
    assert.equal(checksum, nodeArchiveSha256);
    const nodeArchive = path.join(tools, archiveName);
    if (!existsSync(nodeArchive))
      write(nodeArchive, await fetchBytes(`${nodeBase}/${archiveName}`));
    assert.equal(hashFile(nodeArchive), checksum);
    if (!lstatSync(nodeHome, { throwIfNoEntry: false })) {
      mkdir(nodeHome);
      assert.equal(readdirSync(nodeHome).length, 0, 'Node extraction requires an empty directory.');
      run(
        'node-extract',
        bootstrap.tar,
        ['-xJf', nodeArchive, '--strip-components=1', '-C', nodeHome],
        output,
      );
    }

    const metadataPath = path.join(tools, 'pnpm-registry.json');
    if (!existsSync(metadataPath)) {
      write(metadataPath, await fetchBytes(`https://registry.npmjs.org/pnpm/${pnpmVersion}`));
    }
    const metadata = json(metadataPath);
    assert.equal(metadata.version, pnpmVersion);
    assert.equal(
      metadata.dist.tarball,
      `https://registry.npmjs.org/pnpm/-/pnpm-${pnpmVersion}.tgz`,
    );
    const pnpmArchive = path.join(tools, `pnpm-${pnpmVersion}.tgz`);
    if (!existsSync(pnpmArchive)) write(pnpmArchive, await fetchBytes(metadata.dist.tarball));
    assert.equal(hashFile(pnpmArchive), pnpmArchiveSha256);
    const integrity = `sha512-${createHash('sha512').update(readFileSync(pnpmArchive)).digest('base64')}`;
    assert.equal(integrity, metadata.dist.integrity);
    const pnpmHome = path.join(tools, 'pnpm');
    if (!lstatSync(pnpmHome, { throwIfNoEntry: false })) {
      mkdir(pnpmHome);
      assert.equal(readdirSync(pnpmHome).length, 0, 'pnpm extraction requires an empty directory.');
      run(
        'pnpm-extract',
        bootstrap.tar,
        ['-xzf', pnpmArchive, '--strip-components=1', '-C', pnpmHome],
        output,
      );
    }
    verifyExtractedTools(output);
    for (const [name, target] of Object.entries({
      node,
      npm: path.join(nodeHome, 'bin/npm'),
      pnpm,
    })) {
      const link = path.join(tools, 'bin', name);
      const expected = path.relative(path.dirname(link), target);
      assertDestination(output, link, 'symlink');
      if (lstatSync(link, { throwIfNoEntry: false })) {
        assert(lstatSync(link).isSymbolicLink(), `Expected a tool link: ${link}`);
        assert.equal(readlinkSync(link), expected, `Changed tool link: ${link}`);
      } else {
        symlinkSync(expected, link);
      }
    }
    assertManagedPaths(output);
    verifyExtractedTools(output);
    verifyToolEntryLinks(output);
    assert.equal(
      execFileSync(node, ['--version'], { encoding: 'utf8', env: toolEnvironment() }).trim(),
      `v${nodeVersion}`,
    );
    assert.equal(
      execFileSync(node, [pnpm, '--version'], { encoding: 'utf8', env: toolEnvironment() }).trim(),
      pnpmVersion,
    );
    save(path.join(evidence, 'tools.json'), {
      platform: process.platform,
      arch: process.arch,
      node: {
        version: nodeVersion,
        binary: node,
        binarySha256: hashFile(node),
        archive: nodeArchive,
        archiveSha256: checksum,
        treeSha256: toolPins[0].treeSha256,
      },
      pnpm: {
        version: pnpmVersion,
        cli: pnpm,
        cliSha256: hashFile(pnpm),
        archive: pnpmArchive,
        archiveSha256: hashFile(pnpmArchive),
        treeSha256: toolPins[1].treeSha256,
        integrity,
      },
      bootstrapNode: { version: process.version, binary: realpathSync(process.execPath) },
      bootstrapExecutables: bootstrap,
      nodeCompileCache: env.NODE_COMPILE_CACHE,
    });
  }

  function install(name, cwd) {
    verifySource();
    run(
      name,
      node,
      [
        pnpm,
        'install',
        '--frozen-lockfile',
        '--ignore-scripts',
        '--reporter=append-only',
        '--store-dir',
        path.join(output, 'pnpm-store'),
        '--package-import-method=copy',
      ],
      cwd,
    );
    verifySource();
  }

  function buildLibrary() {
    verifySource();
    run('build-library', node, [pnpm, 'run', 'build']);
    verifySource();
    assert(existsSync(path.join(source, 'dist/index.d.ts')), 'Library declarations are missing.');
  }

  function probeTools() {
    run('probe-tools', node, [
      pnpm,
      'exec',
      'node',
      '-e',
      `const cp = require("node:child_process"); const fs = require("node:fs"); const assert = require("node:assert/strict"); assert.equal(process.execPath, ${JSON.stringify(node)}); const found = cp.execFileSync(${JSON.stringify(bootstrap.which)}, ["pnpm"], {encoding:"utf8"}).trim(); assert.equal(fs.realpathSync(found), ${JSON.stringify(pnpm)}); const version = cp.execFileSync(found, ["--version"], {encoding:"utf8"}).trim(); assert.equal(version, ${JSON.stringify(pnpmVersion)}); console.log(JSON.stringify({node:process.execPath, pnpm:found, version}, null, 2));`,
    ]);
  }

  function treeEntries(root) {
    const entries = [];
    function visit(directory, prefix = '') {
      for (const name of readdirSync(directory).sort()) {
        const filename = path.join(directory, name);
        const item = prefix ? `${prefix}/${name}` : name;
        const stat = lstatSync(filename);
        if (stat.isSymbolicLink()) {
          entries.push({ path: item, kind: 'symlink', target: readlinkSync(filename) });
        } else if (stat.isDirectory()) {
          visit(filename, item);
        } else if (stat.isFile()) {
          entries.push({ path: item, kind: 'file', bytes: stat.size, sha256: hashFile(filename) });
        } else {
          throw new Error(`Unexpected file kind: ${filename}`);
        }
      }
    }
    visit(root);
    return entries.sort((left, right) =>
      left.path < right.path ? -1 : left.path > right.path ? 1 : 0,
    );
  }

  function inventory(name, root) {
    const entries = treeEntries(root);
    const filename = path.join(evidence, `${name}-files.jsonl`);
    write(filename, entries.map((entry) => JSON.stringify(entry)).join('\n') + '\n');
    return { root, entries, files: filename, filesSha256: hashFile(filename) };
  }

  function dependencies(name, root) {
    const all = inventory(name, root);
    const links = all.entries
      .filter((entry) => entry.kind === 'symlink')
      .map((entry) => {
        const filename = path.join(root, entry.path);
        const resolved = realpathSync(filename);
        assert(
          resolved.startsWith(`${output}/`),
          `Dependency link leaves the prepared tree: ${filename}`,
        );
        return { ...entry, resolved };
      });
    const packages = all.entries
      .filter(
        (entry) =>
          entry.kind === 'file' &&
          /^(?:\.pnpm\/[^/]+\/node_modules\/)?(?:@[^/]+\/)?[^/]+\/package\.json$/.test(entry.path),
      )
      .map((entry) => {
        const packageRoot = path.posix.dirname(entry.path);
        const metadata = json(path.join(root, entry.path));
        const contents = all.entries
          .filter((file) => file.path.startsWith(`${packageRoot}/`))
          .map((file) => ({ ...file, path: file.path.slice(packageRoot.length + 1) }));
        return {
          path: relative(path.join(root, packageRoot)),
          name: metadata.name,
          version: metadata.version,
          packageJsonSha256: entry.sha256,
          fileCount: contents.length,
          contentSha256: sha256(contents.map((file) => JSON.stringify(file)).join('\n') + '\n'),
          lifecycleScripts: Object.fromEntries(
            Object.entries(metadata.scripts ?? {}).filter(([key]) =>
              ['preinstall', 'install', 'postinstall', 'prepare'].includes(key),
            ),
          ),
        };
      });
    assert(packages.length > 0, `No installed packages found in ${root}`);
    save(path.join(evidence, `${name}-packages.json`), packages);
    save(path.join(evidence, `${name}-links.json`), links);
    return {
      root,
      fileCount: all.entries.filter((entry) => entry.kind === 'file').length,
      packageCount: packages.length,
      linkCount: links.length,
      filesSha256: all.filesSha256,
      packagesSha256: hashFile(path.join(evidence, `${name}-packages.json`)),
      linksSha256: hashFile(path.join(evidence, `${name}-links.json`)),
    };
  }

  function recordEvidence() {
    snapshot();
    const toolFacts = json(path.join(evidence, 'tools.json'));
    assert.equal(hashFile(node), toolFacts.node.binarySha256);
    assert.equal(hashFile(pnpm), toolFacts.pnpm.cliSha256);
    const commandsPath = path.join(evidence, 'commands.json');
    const commands = json(commandsPath);
    for (const name of ['install-root', 'probe-tools', 'build-library', 'install-app']) {
      const last = commands.findLast((command) => command.name === name);
      assert(
        last && last.status === 0 && last.executable === node && last.args[0] === pnpm,
        `A successful pinned-tool command is required: ${name}`,
      );
      assert.equal(last.memoryMaxBytes, 2147483648, name);
    }
    const rootModules = path.join(source, 'node_modules');
    const appModules = path.join(source, 'app/node_modules');
    const rootDependencies = dependencies('root', rootModules);
    const appDependencies = dependencies('app', appModules);
    const tsPath = path.join(rootModules, 'typescript/lib/typescript.js');
    const ts = require(tsPath);
    assert.equal(ts.version, '6.0.3');
    const configs = Object.entries(rootPins).map(([config, [count, expected]]) => {
      const filename = path.join(source, config);
      const read = ts.readConfigFile(filename, ts.sys.readFile);
      assert.equal(read.error, undefined);
      const parsed = ts.parseJsonConfigFileContent(
        read.config,
        ts.sys,
        path.dirname(filename),
        undefined,
        filename,
      );
      assert.equal(parsed.errors.length, 0, JSON.stringify(parsed.errors));
      assert.equal(parsed.options.strict, true);
      const roots = parsed.fileNames.map((name) => path.relative(source, name)).sort();
      const text = roots.join('\n') + '\n';
      assert.equal(roots.length, count, config);
      assert.equal(sha256(text), expected, config);
      write(
        path.join(evidence, config === 'tsconfig.json' ? 'root-files.txt' : 'app-root-files.txt'),
        text,
      );
      return {
        config,
        configSha256: hashFile(filename),
        count,
        rootListSha256: expected,
        tsxCount: roots.filter((name) => name.endsWith('.tsx')).length,
        options: parsed.options,
      };
    });
    const compilers = [rootModules, appModules].map((modules) => {
      const home = realpathSync(path.join(modules, 'typescript'));
      const metadata = json(path.join(home, 'package.json'));
      const libraries = readdirSync(path.join(home, 'lib'))
        .filter((name) => /^lib.*\.d\.ts$/.test(name))
        .sort()
        .map((name) => ({ path: name, sha256: hashFile(path.join(home, 'lib', name)) }));
      return {
        version: metadata.version,
        home,
        compilerSha256: hashFile(path.join(home, 'lib/typescript.js')),
        libraries,
      };
    });
    save(path.join(evidence, 'compilers.json'), compilers);
    const dist = inventory('library-dist', path.join(source, 'dist'));
    const appPackageLink = path.join(appModules, 'react-hook-form');
    const appPackage = realpathSync(appPackageLink);
    const installedDist = inventory('app-library-dist', path.join(appPackage, 'dist'));
    assert.deepEqual(
      installedDist.entries,
      dist.entries,
      'The app file dependency must contain the built library bytes.',
    );
    assert.equal(
      hashFile(path.join(appPackage, 'package.json')),
      hashFile(path.join(source, 'package.json')),
    );
    const fileDependency = {
      path: appPackageLink,
      target: readlinkSync(appPackageLink),
      resolved: appPackage,
      packageJsonSha256: hashFile(path.join(appPackage, 'package.json')),
      declarations: path.join(appPackage, 'dist/index.d.ts'),
      indexDeclarationSha256: hashFile(path.join(appPackage, 'dist/index.d.ts')),
      distFilesSha256: installedDist.filesSha256,
      matchesLibraryDist: true,
    };
    save(path.join(evidence, 'summary.json'), {
      kind: 'dependency-input-evidence',
      parityRun: false,
      goArtifacts: null,
      source: json(path.join(evidence, 'source.json')),
      tools: toolFacts,
      configs,
      compilersSha256: hashFile(path.join(evidence, 'compilers.json')),
      rootDependencies,
      appDependencies,
      fileDependency,
      libraryDist: {
        root: dist.root,
        fileCount: dist.entries.length,
        filesSha256: dist.filesSha256,
      },
      commands: commandsPath,
      commandsSha256: hashFile(commandsPath),
      preparationScriptSha256: hashFile(fileURLToPath(import.meta.url)),
    });
    console.log(`Evidence: ${path.join(evidence, 'summary.json')}`);
  }

  const stages = {
    snapshot,
    tools: provisionTools,
    'install-root': () => install('install-root', source),
    'probe-tools': probeTools,
    'build-library': buildLibrary,
    'install-app': () => install('install-app', path.join(source, 'app')),
    evidence: recordEvidence,
  };
  for (const action of stage === 'all' ? Object.values(stages) : [stages[stage]]) await action();
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main(process.argv.slice(2));
}
