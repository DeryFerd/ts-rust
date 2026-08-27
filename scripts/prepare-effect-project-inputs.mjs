#!/usr/bin/env node
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  accessSync, constants, existsSync, fstatSync, ftruncateSync, lstatSync, mkdirSync, mkdtempSync,
  openSync, closeSync, readFileSync, readdirSync, readlinkSync, realpathSync,
  writeFileSync,
} from 'node:fs';
import { createRequire } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

// This prepares inputs only. It never runs a compiler, build, or generator.
const pin = '0d083ba26b2e1afec8d3e8d83db0d05683b6602b';
const pnpmVersion = '11.20.0';
const pnpmArchiveSha256 = '34e198cb1e43237517ecedfd31f9ae26a6c0a3e5366ce58a2d05f4b21fb5f19a';
const pnpmIntegrity = 'sha512-mm8zCpW2ZEbqCI+vFSFAWooB8H/ecSTMmVjf7VLUu0NnN+ZbCPhfN7Rvy6N1CSVYrFEmK4FoRLIvY0Bu0Wa/7g==';
const configPath = 'packages/effect/tsconfig.json';
const expectedRootDigest = 'ef2b0b9eed5911a73e1ed0c29a7945687869473b4ee7f6009de658600095ff3b';
const readerDigest = '569177652966bd528c319171c7dd22860dbf72bde116cbc4f644f1d02bb12e39';
const worktree = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const capture = (command, args, options = {}) => execFileSync(command, args, {
  encoding: 'utf8', maxBuffer: 32 * 1024 * 1024, ...options,
});
const commonGit = capture('git', ['-C', worktree, 'rev-parse', '--path-format=absolute', '--git-common-dir']).trim();
const output = path.join(path.dirname(commonGit), 'target/project-inputs/effect');
const source = path.join(output, 'source');
const evidence = path.join(output, 'evidence');
const cache = path.resolve(process.env.EFFECT_REPO_CACHE ?? path.join(os.homedir(), '.explore/repos/Effect-TS__effect'));
const readerCache = path.resolve(process.env.EFFECT_CONFIG_READER ?? path.join(os.homedir(), '.bun/install/cache/typescript@6.0.3@@@1'));
const hash = (bytes, algorithm = 'sha256') => createHash(algorithm).update(bytes).digest('hex');
const json = (filename) => JSON.parse(readFileSync(filename, 'utf8'));
const save = (filename, value) => writeOutputFile(path.join(evidence, filename), `${JSON.stringify(value, null, 2)}\n`);
const offline = process.argv.slice(2).includes('--offline');
assert(process.argv.slice(2).every((arg) => arg === '--offline'), 'Only --offline is supported');

function inside(root, filename) {
  const relative = path.relative(root, filename);
  return relative !== '..' && !relative.startsWith(`..${path.sep}`) && !path.isAbsolute(relative);
}

// lstat also catches dangling links. Check each ancestor before making a path.
function checkPath(filename, kind, required = false) {
  const absolute = path.resolve(filename);
  let current = path.parse(absolute).root;
  for (const component of absolute.slice(current.length).split(path.sep).filter(Boolean)) {
    current = path.join(current, component);
    let stat;
    try {
      stat = lstatSync(current);
    } catch (error) {
      if (error.code !== 'ENOENT' || required) throw error;
      return null;
    }
    assert(!stat.isSymbolicLink(), `Unsafe symlink: ${current}`);
    const directory = current !== absolute || kind === 'directory';
    assert(directory ? stat.isDirectory() : stat.isFile(), `Unexpected path kind: ${current}`);
    if (current === absolute) return stat;
  }
  return lstatSync(current);
}

function checkOutputFile(filename) {
  assert(inside(output, filename) && filename !== output, `Write leaves Effect output: ${filename}`);
  const stat = checkPath(filename, 'file');
  assert(!stat || stat.nlink === 1, `Refusing a hard-linked output file: ${filename}`);
}

function openOutputFile(filename) {
  checkOutputFile(filename);
  const fd = openSync(filename, constants.O_WRONLY | constants.O_CREAT | constants.O_NOFOLLOW, 0o666);
  try {
    const stat = fstatSync(fd);
    assert(stat.isFile() && stat.nlink === 1, `Unsafe output file: ${filename}`);
    ftruncateSync(fd, 0);
    return fd;
  } catch (error) {
    closeSync(fd);
    throw error;
  }
}

function writeOutputFile(filename, bytes) {
  const fd = openOutputFile(filename);
  try {
    writeFileSync(fd, bytes);
  } finally {
    closeSync(fd);
  }
}

function makeOutputDirectory(directory) {
  assert(inside(output, directory), `Directory leaves Effect output: ${directory}`);
  checkPath(directory, 'directory');
  mkdirSync(directory, { recursive: true });
  checkPath(directory, 'directory', true);
}

function checkTree(root, allowLink = () => false) {
  if (!checkPath(root, 'directory')) return;
  function visit(directory) {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const filename = path.join(directory, entry.name);
      if (entry.isSymbolicLink()) assert(allowLink(filename), `Unsafe symlink: ${filename}`);
      else if (entry.isDirectory()) visit(filename);
      else assert(entry.isFile(), `Unexpected path kind: ${filename}`);
    }
  }
  visit(root);
}

const managedDirectories = ['evidence', 'home', 'tmp', 'cache', 'config', 'data', 'state', 'tools', 'pnpm-home', 'store'];
const readerFiles = ['lib/typescript.js', 'LICENSE.txt', 'ThirdPartyNoticeText.txt', 'package.json'];
const storeProjectLink = path.join(output, 'store/v11/projects', hash(source).slice(0, 32));
function checkLayout() {
  checkPath(output, 'directory');
  for (const directory of managedDirectories) {
    const root = path.join(output, directory);
    checkTree(root, (filename) => {
      if (directory === 'store') {
        return filename === storeProjectLink && realpathSync(filename) === source;
      }
      if (directory !== 'tools') return false;
      const relative = path.relative(root, filename);
      if (!/^pnpm\/node_modules\/\.bin\/(pn|pnpm|pnx|pnpx)$/.test(relative)) return false;
      const bin = ['pn', 'pnpm'].includes(path.basename(filename)) ? 'pnpm.mjs' : 'pnpx.mjs';
      const expected = path.join(root, 'pnpm/node_modules/pnpm/bin', bin);
      checkPath(expected, 'file', true);
      return realpathSync(filename) === expected;
    });
  }
  checkTree(source, (filename) => {
    const parts = path.relative(source, filename).split(path.sep);
    return parts.includes('node_modules') && path.basename(filename) !== 'node_modules'
      && inside(source, realpathSync(filename));
  });
  for (const readonly of [cache, readerCache]) {
    checkPath(readonly, 'directory', true);
    assert(!inside(output, readonly) && !inside(readonly, output), `Input cache overlaps Effect output: ${readonly}`);
  }
  for (const filename of readerFiles) checkPath(path.join(readerCache, filename), 'file', true);
}

checkLayout();
for (const directory of managedDirectories) {
  makeOutputDirectory(path.join(output, directory));
}
const isolated = {
  PATH: process.env.PATH,
  LANG: 'C.UTF-8',
  CI: 'true',
  HOME: path.join(output, 'home'),
  TMPDIR: path.join(output, 'tmp'),
  TMP: path.join(output, 'tmp'),
  TEMP: path.join(output, 'tmp'),
  XDG_CACHE_HOME: path.join(output, 'cache'),
  XDG_CONFIG_HOME: path.join(output, 'config'),
  XDG_DATA_HOME: path.join(output, 'data'),
  XDG_STATE_HOME: path.join(output, 'state'),
  PNPM_HOME: path.join(output, 'pnpm-home'),
  NODE_OPTIONS: '--max-old-space-size=1024',
  NODE_COMPILE_CACHE: path.join(output, 'cache/node'),
  // The tarball worker pool otherwise follows the host CPU count.
  PNPM_MAX_WORKERS: '2',
  npm_config_cache: path.join(output, 'cache/npm'),
  npm_config_userconfig: path.join(output, 'home/user.npmrc'),
  npm_config_globalconfig: path.join(output, 'home/global.npmrc'),
  npm_config_ignore_scripts: 'true',
  npm_config_registry: 'https://registry.npmjs.org',
};
assert(!existsSync(isolated.npm_config_userconfig), 'Unexpected npm user config');
assert(!existsSync(isolated.npm_config_globalconfig), 'Unexpected npm global config');
const commands = [];

function bounded(name, command, args, cwd) {
  checkLayout();
  assert(inside(output, cwd), `Command directory leaves Effect output: ${cwd}`);
  checkPath(cwd, 'directory', true);
  const scopedArgs = [
    '--user', '--scope', '--quiet', '--collect', `--unit=ts-rust-effect-${name}-${process.pid}`,
    '-p', 'MemoryMax=2G', '-p', 'MemorySwapMax=0',
    'env', '-i', ...Object.entries(isolated).map(([key, value]) => `${key}=${value}`),
    command, ...args,
  ];
  console.log(`${name}: starting with a 2 GiB memory cap`);
  const logPath = path.join(evidence, `${name}-${process.pid}${offline ? '-offline' : ''}.log`);
  const log = openOutputFile(logPath);
  let result;
  try {
    result = spawnSync('systemd-run', scopedArgs, { cwd, stdio: ['ignore', log, log] });
  } finally {
    closeSync(log);
  }
  commands.push({ name, command: ['systemd-run', ...scopedArgs], cwd, status: result.status, signal: result.signal });
  save('commands.json', commands);
  save(`commands-${process.pid}.json`, commands);
  if (result.error || result.status !== 0) {
    console.error(readFileSync(logPath, 'utf8'));
    throw result.error ?? new Error(`${name} failed: status=${result.status}, signal=${result.signal}`);
  }
  console.log(`${name}: complete. Log: ${logPath}`);
}

function executable(name) {
  for (const directory of process.env.PATH.split(path.delimiter)) {
    const filename = path.join(directory, name);
    try {
      accessSync(filename, constants.X_OK);
      return realpathSync(filename);
    } catch (error) {
      if (!['ENOENT', 'EACCES', 'ENOTDIR'].includes(error.code)) throw error;
    }
  }
  throw new Error(`Missing executable: ${name}`);
}

const git = (...args) => capture('git', ['-c', 'core.fsmonitor=false', '-C', cache, ...args], {
  env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' },
});
function checkCache() {
  checkPath(cache, 'directory', true);
  assert.equal(git('rev-parse', 'HEAD').trim(), pin, 'Effect checkout changed');
  assert.equal(git('status', '--porcelain=v1', '--untracked-files=all').trim(), '', 'Effect checkout is dirty');
}
checkCache();
const tracked = git('ls-tree', '-r', '-z', '--full-tree', pin).split('\0').filter(Boolean).map((entry) => {
  const [metadata, filename] = entry.split('\t');
  const [mode, type, blob] = metadata.split(' ');
  assert(type === 'blob' && ['100644', '100755'].includes(mode), `Unsupported Git entry: ${filename}`);
  assert(!filename.split('/').includes('..') && !path.isAbsolute(filename), `Unsafe path: ${filename}`);
  return { path: filename, mode, gitBlob: blob };
}).sort((a, b) => a.path < b.path ? -1 : a.path > b.path ? 1 : 0);
const trackedNames = new Set(tracked.map((entry) => entry.path));

if (!existsSync(source)) {
  const archive = path.join(output, 'tmp/source.tar');
  checkOutputFile(archive);
  git('archive', '--format=tar', `--output=${archive}`, pin);
  makeOutputDirectory(source);
  capture('tar', ['-xf', archive, '-C', source], { env: isolated });
}

function sourceSnapshot() {
  const snapshot = tracked.map((entry) => {
    const filename = path.join(source, entry.path);
    const stat = checkPath(filename, 'file', true);
    assert(stat.isFile(), `Source is not a regular file: ${entry.path}`);
    assert.equal(Boolean(stat.mode & 0o111), entry.mode === '100755', `Source mode changed: ${entry.path}`);
    const bytes = readFileSync(filename);
    const gitBlob = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
    assert.equal(gitBlob, entry.gitBlob, `Source bytes changed: ${entry.path}`);
    return { ...entry, size: bytes.length, sha256: hash(bytes) };
  });
  function rejectExtras(directory) {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      if (entry.name === 'node_modules') continue;
      const filename = path.join(directory, entry.name);
      if (entry.isDirectory()) rejectExtras(filename);
      else assert(trackedNames.has(path.relative(source, filename)), `Untracked source: ${filename}`);
    }
  }
  rejectExtras(source);
  return snapshot;
}
save('source-before.json', sourceSnapshot());
assert.equal(json(path.join(source, 'package.json')).packageManager, `pnpm@${pnpmVersion}`);

const node = realpathSync(process.execPath);
const npm = executable('npm');
const pnpmRoot = path.join(output, 'tools/pnpm');
const pnpm = path.join(pnpmRoot, 'node_modules/pnpm/bin/pnpm.mjs');
if (!existsSync(pnpm)) {
  assert(!offline, 'Bootstrap pnpm online before an offline replay');
  bounded('bootstrap-pnpm', node, [
    npm, 'install', '--prefix', pnpmRoot,
    '--cache', isolated.npm_config_cache,
    '--userconfig', isolated.npm_config_userconfig,
    '--globalconfig', isolated.npm_config_globalconfig,
    '--registry', isolated.npm_config_registry,
    '--save-exact', '--ignore-scripts', '--no-audit', '--no-fund', `pnpm@${pnpmVersion}`,
  ], output);
}
checkLayout();
const bootstrapLock = json(path.join(pnpmRoot, 'package-lock.json'));
assert.equal(bootstrapLock.packages['node_modules/pnpm'].version, pnpmVersion);
assert.equal(bootstrapLock.packages['node_modules/pnpm'].integrity, pnpmIntegrity);

// npm's cached tarball is still an archive. Its bytes must match both fixed pins.
const integrityHex = Buffer.from(pnpmIntegrity.slice('sha512-'.length), 'base64').toString('hex');
const cachedArchive = path.join(isolated.npm_config_cache, '_cacache/content-v2/sha512',
  integrityHex.slice(0, 2), integrityHex.slice(2, 4), integrityHex.slice(4));
let pnpmArchive = cachedArchive;
if (!checkPath(cachedArchive, 'file')) {
  pnpmArchive = path.join(output, 'tools', `pnpm-${pnpmVersion}.tgz`);
  checkOutputFile(pnpmArchive);
  if (!existsSync(pnpmArchive)) {
    assert(!offline, 'The pinned pnpm archive is required for offline verification');
    bounded('fetch-pnpm-archive', node, [npm, 'pack', `pnpm@${pnpmVersion}`,
      '--pack-destination', path.join(output, 'tools'), '--ignore-scripts', '--json'], output);
  }
}
checkPath(pnpmArchive, 'file', true);
const archiveBytes = readFileSync(pnpmArchive);
assert.equal(hash(archiveBytes), pnpmArchiveSha256, 'pnpm archive changed');
assert.equal(`sha512-${createHash('sha512').update(archiveBytes).digest('base64')}`, pnpmIntegrity);
checkLayout();
const archiveDirectory = mkdtempSync(path.join(output, 'tmp/pnpm-archive-'));
capture('tar', ['-xzf', pnpmArchive, '--strip-components=1', '--no-same-owner', '-C', archiveDirectory], { env: isolated });

function packageFiles(root) {
  checkTree(root);
  const files = [];
  function visit(directory) {
    for (const entry of readdirSync(directory, { withFileTypes: true }).sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0)) {
      const filename = path.join(directory, entry.name);
      if (entry.isDirectory()) visit(filename);
      else files.push({ path: path.relative(root, filename), sha256: hash(readFileSync(filename)) });
    }
  }
  visit(root);
  return files;
}
const pinnedPackageFiles = packageFiles(archiveDirectory);
function checkPnpmPackage() {
  checkLayout();
  assert.deepEqual(packageFiles(path.join(pnpmRoot, 'node_modules/pnpm')), pinnedPackageFiles,
    'Installed pnpm files differ from the pinned archive');
}
checkPnpmPackage();
assert.equal(capture(node, [pnpm, '--version'], { env: isolated }).trim(), pnpmVersion);

const installArgs = [
  pnpm, 'install', '--frozen-lockfile', '--ignore-scripts', '--ignore-pnpmfile',
  '--no-side-effects-cache', '--package-import-method=copy',
  '--network-concurrency=8', '--child-concurrency=1', '--reporter=append-only',
  '--store-dir', path.join(output, 'store'),
  '--virtual-store-dir', path.join(source, 'node_modules/.pnpm'),
];
if (offline) installArgs.push('--offline');
checkPnpmPackage();
bounded('install', node, installArgs, source);
checkLayout();
const sourceAfter = sourceSnapshot();
save('source-after.json', sourceAfter);
assert.equal(readFileSync(path.join(evidence, 'source-before.json'), 'utf8'), readFileSync(path.join(evidence, 'source-after.json'), 'utf8'));
checkCache();

// Do not follow package links. Hash each installed file once and record links separately.
const dependencies = [];
const packages = [];
const links = [];
function scan(directory, inModules = false) {
  for (const entry of readdirSync(directory, { withFileTypes: true }).sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0)) {
    const filename = path.join(directory, entry.name);
    const relative = path.relative(source, filename);
    const installed = inModules || entry.name === 'node_modules';
    if (entry.isDirectory()) scan(filename, installed);
    else if (installed && entry.isSymbolicLink()) {
      const target = readlinkSync(filename);
      const resolved = existsSync(filename) ? realpathSync(filename) : path.resolve(directory, target);
      const relativeOutput = path.relative(output, resolved);
      assert(relativeOutput !== '..' && !relativeOutput.startsWith(`..${path.sep}`), `Link leaves Effect output: ${relative}`);
      const link = { path: relative, target, resolved: path.relative(source, resolved), exists: existsSync(filename) };
      links.push(link);
      dependencies.push({ kind: 'symlink', ...link });
    } else if (installed && entry.isFile()) {
      const bytes = readFileSync(filename);
      dependencies.push({ kind: 'file', path: relative, size: bytes.length, sha256: hash(bytes), executable: Boolean(lstatSync(filename).mode & 0o111) });
      if (/(^|\/)node_modules\/(?:@[^/]+\/)?[^/]+\/package\.json$/.test(relative)) {
        const metadata = JSON.parse(bytes.toString('utf8'));
        packages.push({ path: path.dirname(relative), name: metadata.name ?? null, version: metadata.version ?? null, metadata });
      }
    } else if (installed) throw new Error(`Unsupported installed entry: ${relative}`);
  }
}
scan(source);
const dependencyList = dependencies.map((entry) => JSON.stringify(entry)).join('\n') + '\n';
const installedFilename = path.join(evidence, 'installed-files.jsonl');
let replayChanges = null;
if (existsSync(installedFilename)) {
  const before = new Map(readFileSync(installedFilename, 'utf8').trimEnd().split('\n').map((line) => {
    const entry = JSON.parse(line);
    return [entry.path, entry];
  }));
  const after = new Map(dependencies.map((entry) => [entry.path, entry]));
  replayChanges = [...new Set([...before.keys(), ...after.keys()])]
    .filter((filename) => JSON.stringify(before.get(filename)) !== JSON.stringify(after.get(filename)))
    .map((filename) => ({ path: filename, before: before.get(filename) ?? null, after: after.get(filename) ?? null }));
  save(`replay-files-${process.pid}.json`, replayChanges);
}
writeOutputFile(installedFilename, dependencyList);
save('links.json', links);

function declarationTargets(metadata) {
  const targets = [];
  for (const field of ['types', 'typings']) {
    if (typeof metadata[field] === 'string') targets.push({ field, target: metadata[field] });
  }
  function visit(value, field, isTypes = false) {
    if (typeof value === 'string' && (isTypes || /\.d\.[cm]?ts$/.test(value))) targets.push({ field, target: value });
    else if (value && typeof value === 'object') {
      for (const [key, child] of Object.entries(value)) visit(child, `${field}.${key}`, isTypes || key === 'types' || key.startsWith('types@'));
    }
  }
  visit(metadata.exports, 'exports');
  return targets;
}
const missingDeclarations = [];
const wildcardDeclarations = [];
function inspectPackage(directory, metadata) {
  const { name = null, version = null } = metadata;
  const targets = declarationTargets(metadata).map((entry) => {
    if (entry.target.includes('*')) {
      wildcardDeclarations.push({ package: directory, ...entry });
      return { ...entry, status: 'wildcard-not-expanded' };
    }
    const exists = existsSync(path.resolve(source, directory, entry.target));
    if (!exists) missingDeclarations.push({ package: directory, name, version, ...entry });
    return { ...entry, status: exists ? 'present' : 'missing' };
  });
  const installHooks = Object.fromEntries(Object.entries(metadata.scripts ?? {}).filter(([key]) => ['preinstall', 'install', 'postinstall', 'prepare'].includes(key)));
  return { path: directory, name, version, declarationTargets: targets, typesVersions: metadata.typesVersions ?? null, skippedHooks: installHooks };
}
const packageInventory = packages.map(({ path: directory, metadata }) => inspectPackage(directory, metadata));
save('packages.json', packageInventory);
checkPnpmPackage();
const workspace = JSON.parse(capture(node, [pnpm, 'list', '-r', '--depth=-1', '--json'], { cwd: source, env: isolated }));
save('workspace.json', workspace.map((entry) => ({
  ...inspectPackage(path.relative(source, entry.path) || '.', json(path.join(entry.path, 'package.json'))),
  packageJsonSha256: hash(readFileSync(path.join(entry.path, 'package.json'))),
})));
save('missing-declarations.json', missingDeclarations);
save('wildcard-declarations.json', wildcardDeclarations);

const readerRoot = path.join(output, 'tools/typescript-config-reader');
checkPath(path.join(readerCache, 'lib/typescript.js'), 'file', true);
assert.equal(hash(readFileSync(path.join(readerCache, 'lib/typescript.js'))), readerDigest, 'Config reader changed');
makeOutputDirectory(path.join(readerRoot, 'lib'));
for (const filename of readerFiles) {
  checkPath(path.join(readerCache, filename), 'file', true);
  writeOutputFile(path.join(readerRoot, filename), readFileSync(path.join(readerCache, filename)));
}
const reader = path.join(readerRoot, 'lib/typescript.js');
checkPath(reader, 'file', true);
assert.equal(hash(readFileSync(reader)), readerDigest, 'Config reader changed');
const ts = createRequire(import.meta.url)(reader);
assert.equal(ts.version, '6.0.3');
const configFilename = path.join(source, configPath);
const parsed = ts.getParsedCommandLineOfConfigFile(configFilename, {}, {
  ...ts.sys,
  onUnRecoverableConfigFileDiagnostic(diagnostic) {
    throw new Error(ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'));
  },
});
assert(parsed && parsed.errors.length === 0, 'Config reader reported errors');
assert.equal(parsed.options.strict, true);
assert.deepEqual(parsed.options.types, ['node']);
const roots = parsed.fileNames.map((filename) => path.relative(source, filename)).sort();
assert(roots.every((filename) => trackedNames.has(filename)), 'Config contains an untracked root');
assert.equal(roots.length, 457);
const rootList = roots.join('\n') + '\n';
assert.equal(hash(rootList), expectedRootDigest, 'Config root list changed');
writeOutputFile(path.join(evidence, 'roots.files'), rootList);
const specialGenerated = new Set([
  'packages/effect/src/unstable/cluster/K8sTypes.ts',
  'packages/effect/src/unstable/httpapi/internal/httpApiScalar.ts',
  'packages/effect/src/unstable/httpapi/internal/httpApiSwagger.ts',
]);
const generated = new Set(roots.filter((filename) => specialGenerated.has(filename)
  || readFileSync(path.join(source, filename), 'utf8').includes('@barrel: Auto-generated exports.')));
assert.equal(generated.size, 23);
const keyFiles = new Set([
  'pnpm-lock.yaml', 'pnpm-workspace.yaml', 'package.json', 'packages/effect/package.json',
  configPath, 'tsconfig.base.json', 'LICENSE', 'patches/@changesets__get-github-info@1.0.0.patch',
]);
save('source-inputs.json', {
  keyFiles: sourceAfter.filter((entry) => keyFiles.has(entry.path)),
  generated: sourceAfter.filter((entry) => generated.has(entry.path)),
});
save('config.json', {
  config: configPath,
  chain: [...(parsed.options.configFile.extendedSourceFiles ?? []), configFilename].map((filename) => ({ path: path.relative(source, filename), sha256: hash(readFileSync(filename)) })),
  roots: roots.length, rootListSha256: hash(rootList), strict: true, types: parsed.options.types,
  module: ts.ModuleKind[parsed.options.module],
  moduleResolution: parsed.options.moduleResolution === undefined ? 'default' : ts.ModuleResolutionKind[parsed.options.moduleResolution],
  reader: { version: ts.version, sha256: readerDigest, use: 'config parsing only' },
});
const nodeTypesRoot = realpathSync(path.join(source, 'packages/effect/node_modules/@types/node'));
const nodeTypes = json(path.join(nodeTypesRoot, 'package.json'));
assert.equal(nodeTypes.version, '26.2.0');
assert(existsSync(path.resolve(nodeTypesRoot, nodeTypes.types ?? nodeTypes.typings)));
save('tools.json', {
  node: { version: process.version, path: node, sha256: hash(readFileSync(node)), versions: process.versions },
  npm: { version: capture(node, [npm, '--version'], { env: isolated }).trim(), path: npm, sha256: hash(readFileSync(npm)) },
  pnpm: {
    version: pnpmVersion, path: pnpm, sha256: hash(readFileSync(pnpm)),
    bundleSha256: hash(readFileSync(path.join(pnpmRoot, 'node_modules/pnpm/dist/pnpm.mjs'))),
    archive: pnpmArchive, archiveSha256: pnpmArchiveSha256, integrity: pnpmIntegrity,
    packageFiles: pinnedPackageFiles.length,
    packageFilesSha256: hash(JSON.stringify(pinnedPackageFiles) + '\n'),
    bootstrapLockSha256: hash(readFileSync(path.join(pnpmRoot, 'package-lock.json'))),
    package: bootstrapLock.packages['node_modules/pnpm'],
  },
  platform: { platform: process.platform, arch: process.arch, release: os.release(), cpu: os.cpus()[0]?.model },
  environment: isolated,
});
const digests = Object.fromEntries(['source-after.json', 'source-inputs.json', 'installed-files.jsonl', 'packages.json', 'links.json', 'workspace.json', 'config.json'].map((filename) => [filename, hash(readFileSync(path.join(evidence, filename)))]));
const previous = existsSync(path.join(evidence, 'summary.json')) ? json(path.join(evidence, 'summary.json')) : null;
const summary = {
  status: 'Dependencies prepared. Compiler graph and oracle evidence pending.',
  source, commit: pin, config: configPath, trackedFiles: sourceAfter.length,
  sourceBytes: sourceAfter.reduce((total, entry) => total + entry.size, 0),
  roots: roots.length, rootListSha256: hash(rootList),
  workspaceProjects: workspace.length, installedPackages: packageInventory.length,
  installedFiles: dependencies.filter((entry) => entry.kind === 'file').length,
  installedBytes: dependencies.filter((entry) => entry.kind === 'file').reduce((total, entry) => total + entry.size, 0),
  symlinks: links.length, brokenLinks: links.filter((entry) => !entry.exists),
  missingLiteralDeclarationTargets: missingDeclarations.length,
  unexpandedDeclarationWildcards: wildcardDeclarations.length,
  nodeTypes: { version: nodeTypes.version, path: path.relative(source, nodeTypesRoot), types: nodeTypes.types ?? nodeTypes.typings },
  memoryMaxBytes: 2 * 1024 ** 3, memorySwapMaxBytes: 0,
  installScriptsRun: false, generatorsRun: false, compilerRun: false,
  digests,
  replay: previous ? {
    offline,
    identical: Object.fromEntries(Object.entries(digests).map(([filename, digest]) => [filename, digest === previous.digests[filename]])),
    previousDigests: previous.digests,
    changedInstalledEntries: replayChanges?.length ?? null,
    changesFile: replayChanges ? `replay-files-${process.pid}.json` : null,
  } : null,
  remainingEvidence: [
    'Resolve the full module graph and declarations with the pinned unpatched Go compiler.',
    'Select and hash the actual compiler library files and confirm options and roots with Go and Rust.',
    'Check whether missing literal targets, declaration wildcards, or typesVersions mappings occur in that graph.',
    'Produce Go diagnostics, types, symbols, and deterministic cold and warm replay artifacts.',
    'Run Rust parity and performance checks. No manifest or parity result is produced here.',
  ],
};
save('summary.json', summary);
console.log(JSON.stringify(summary, null, 2));
