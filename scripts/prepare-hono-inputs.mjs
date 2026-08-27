import assert from 'node:assert/strict';
import { spawnSync, execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import fs from 'node:fs';
import { createRequire } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const pin = {
  commit: '06880c4a2b04de9dd74217f26dd831209b9c01f1',
  lockSha256: '910eec46012b95777558e1a8b568e63cf48c7167d12e7deaa60382d474fcdfff',
  configSha256: 'e3105932180e5845959744d315a68fbfe887abc592eb795d0fbf0444996f418e',
  rootsSha256: '4014df7bbea8c85b02685c887d1ac55ab00d96c7987775a02943e91e4360fb12',
  bunVersion: '1.2.20',
  bunArchiveSha256: '4e9edc4cba0c7c1623a288be01e53bbde11a4d073f2cf339cab026627858b548',
  bunBinarySha256: '79af131f0f24e48e419ae4ce3dd1c8d46d615c2b9c2e10b0259959a2e17847c0',
};

const [cacheArgument, outputArgument, ...extra] = process.argv.slice(2);
assert(cacheArgument && outputArgument && extra.length === 0,
  'Usage: node scripts/prepare-hono-inputs.mjs CACHE_REPOSITORY OUTPUT_DIRECTORY');
assert(process.platform === 'linux' && process.arch === 'x64', 'This pin uses Linux x64 Bun.');
const script = fileURLToPath(import.meta.url);

// Every child, including Bun, stays inside the same 2 GiB memory scope.
if (process.env.HONO_PREP_CGROUP_ACTIVE !== '1') {
  const result = spawnSync('systemd-run', [
    '--user', '--scope', '--quiet', '--collect',
    '-p', 'MemoryMax=2147483648', '-p', 'MemorySwapMax=0',
    'env', 'HONO_PREP_CGROUP_ACTIVE=1', process.execPath, script,
    cacheArgument, outputArgument,
  ], { stdio: 'inherit' });
  if (result.error) throw result.error;
  process.exit(result.status ?? 1);
}

process.umask(0o022);
const cache = fs.realpathSync(cacheArgument);
const output = path.resolve(outputArgument);
assert(output !== cache && !output.startsWith(`${cache}/`) && !cache.startsWith(`${output}/`),
  'The output and read-only cache must not overlap.');
const source = path.join(output, 'source');

// Check the nearest existing ancestor when the destination does not exist yet.
function outputPathStat(filename) {
  assert(filename === output || filename.startsWith(`${output}/`), `Unsafe output path: ${filename}`);
  let ancestor = filename;
  let stat = fs.lstatSync(ancestor, { throwIfNoEntry: false });
  while (!stat) {
    ancestor = path.dirname(ancestor);
    stat = fs.lstatSync(ancestor, { throwIfNoEntry: false });
  }
  assert(!stat.isSymbolicLink() && fs.realpathSync(ancestor) === ancestor,
    `Unsafe output path: ${ancestor}`);
  if (ancestor !== filename) {
    assert(stat.isDirectory(), `Unsafe output ancestor: ${ancestor}`);
    return undefined;
  }
  assert(stat.isDirectory() || stat.isFile(), `Unsafe output kind: ${filename}`);
  if (stat.isFile()) assert.equal(stat.nlink, 1, `Shared output file: ${filename}`);
  return stat;
}

function inspectManagedPath(filename) {
  const stat = outputPathStat(filename);
  if (stat?.isDirectory()) {
    for (const name of fs.readdirSync(filename)) inspectManagedPath(path.join(filename, name));
  }
  return stat;
}

const outputStat = outputPathStat(output);
assert(!outputStat || outputStat.isDirectory(), 'The output must be a directory.');
assert(!outputPathStat(source), 'Use a new output directory for a fresh preparation.');
const managedDirectories = ['toolchain', 'toolchain/bun-linux-x64', 'toolchain/bun-home',
  'cache', 'cache/bun', 'home', 'tmp', 'evidence'];
for (const directory of managedDirectories) {
  const stat = inspectManagedPath(path.join(output, directory));
  assert(!stat || stat.isDirectory(), `Expected output directory: ${directory}`);
}
for (const filename of ['source.tar', 'toolchain/bun-linux-x64.zip', 'toolchain/bun-linux-x64/bun']) {
  const stat = inspectManagedPath(path.join(output, filename));
  assert(!stat || stat.isFile(), `Expected output file: ${filename}`);
}
for (const directory of managedDirectories) fs.mkdirSync(path.join(output, directory), { recursive: true });
const evidence = path.join(output, 'evidence');
const environment = {
  ...process.env,
  GIT_OPTIONAL_LOCKS: '0',
  HOME: path.join(output, 'home'),
  TMPDIR: path.join(output, 'tmp'),
  TMP: path.join(output, 'tmp'),
  TEMP: path.join(output, 'tmp'),
  XDG_CACHE_HOME: path.join(output, 'cache'),
  BUN_INSTALL: path.join(output, 'toolchain/bun-home'),
  BUN_INSTALL_CACHE_DIR: path.join(output, 'cache/bun'),
  CI: '1',
};
const run = (command, args, cwd = source) => execFileSync(command, args, {
  cwd, env: environment, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024,
}).trimEnd();
const git = (...args) => run('git', ['-C', cache, ...args], output);
const hash = (bytes, algorithm = 'sha256') => createHash(algorithm).update(bytes).digest('hex');
async function hashFile(filename) {
  const digest = createHash('sha256');
  for await (const bytes of fs.createReadStream(filename)) digest.update(bytes);
  return digest.digest('hex');
}
function writeEvidence(filename, bytes) {
  const destination = path.join(evidence, filename);
  outputPathStat(destination);
  fs.writeFileSync(destination, bytes);
}
function writeJson(filename, value) {
  writeEvidence(filename, `${JSON.stringify(value, null, 2)}\n`);
}
function writeManifest(filename, entries) {
  const bytes = entries.map(entry => JSON.stringify(entry)).join('\n') + '\n';
  writeEvidence(filename, bytes);
  return hash(bytes);
}

assert.equal(git('rev-parse', 'HEAD'), pin.commit, 'The cached commit changed.');
assert.equal(git('status', '--porcelain=v1', '--untracked-files=all'), '', 'The cache is dirty.');
assert.equal(await hashFile(path.join(cache, 'bun.lock')), pin.lockSha256);
const archive = path.join(output, 'toolchain/bun-linux-x64.zip');
const archiveUrl = `https://github.com/oven-sh/bun/releases/download/bun-v${pin.bunVersion}/bun-linux-x64.zip`;
outputPathStat(archive);
if (!fs.existsSync(archive)) {
  run('curl', ['--fail', '--silent', '--show-error', '--location', '--proto', '=https',
    '--tlsv1.2', archiveUrl, '--output', archive], output);
}
assert.equal(await hashFile(archive), pin.bunArchiveSha256, 'The Bun archive hash changed.');
assert.deepEqual(run('unzip', ['-Z1', archive], output).split('\n'), [
  'bun-linux-x64/', 'bun-linux-x64/bun',
]);
const bun = path.join(output, 'toolchain/bun-linux-x64/bun');
outputPathStat(bun);
if (!fs.existsSync(bun)) run('unzip', ['-q', '-n', archive, '-d', path.dirname(archive)], output);
outputPathStat(bun);
assert.equal(await hashFile(bun), pin.bunBinarySha256, 'The Bun binary hash changed.');
assert.equal(run(bun, ['--version'], output), pin.bunVersion);

const sourceArchive = path.join(output, 'source.tar');
outputPathStat(sourceArchive);
git('archive', '--format=tar', `--output=${sourceArchive}`, pin.commit);
assert(!outputPathStat(source), 'The source destination must remain absent.');
fs.mkdirSync(source);
run('tar', ['--extract', '--file', sourceArchive, '--directory', source, '--no-same-owner']);
const fields = git('ls-tree', '-r', '-z',
  '--format=%(objectmode)%x00%(objecttype)%x00%(objectname)%x00%(path)', pin.commit).split('\0');
assert.equal(fields.pop(), '');
assert.equal(fields.length % 4, 0);
const tracked = [];
for (let index = 0; index < fields.length; index += 4) {
  const [mode, type, object, filename] = fields.slice(index, index + 4);
  assert.equal(type, 'blob', `Unsupported source entry: ${filename}`);
  assert(['100644', '100755', '120000'].includes(mode), `Unsupported mode: ${mode}`);
  tracked.push({ path: filename, mode, gitBlob: object });
}
tracked.sort((left, right) => left.path < right.path ? -1 : left.path > right.path ? 1 : 0);
function sourceManifest() {
  return tracked.map(entry => {
    const filename = path.join(source, entry.path);
    const stat = fs.lstatSync(filename);
    const bytes = entry.mode === '120000'
      ? Buffer.from(fs.readlinkSync(filename)) : fs.readFileSync(filename);
    assert.equal(stat.isSymbolicLink(), entry.mode === '120000', entry.path);
    const blob = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
    assert.equal(blob, entry.gitBlob, `Changed source: ${entry.path}`);
    assert.equal(Boolean(stat.mode & 0o111), entry.mode !== '100644', entry.path);
    return { ...entry, bytes: bytes.length, sha256: hash(bytes) };
  });
}
const before = sourceManifest();
const sourceSha256 = writeManifest('source-files.jsonl', before);
assert.equal(await hashFile(path.join(source, 'tsconfig.build.json')), pin.configSha256);
const rootPackage = JSON.parse(fs.readFileSync(path.join(source, 'package.json'), 'utf8'));
assert.equal(rootPackage.packageManager, `bun@${pin.bunVersion}`);
const lifecycleNames = ['preinstall', 'install', 'postinstall', 'prepare', 'prepublish',
  'preprepare', 'postprepare'];
writeJson('root-scripts.json', rootPackage.scripts ?? {});

const installArguments = ['install', '--frozen-lockfile', '--ignore-scripts',
  '--backend=copyfile', '--linker=hoisted', '--network-concurrency=8', '--no-progress',
  '--registry=https://registry.npmjs.org', `--cache-dir=${environment.BUN_INSTALL_CACHE_DIR}`];
outputPathStat(path.join(evidence, 'install.log'));
const installLog = fs.openSync(path.join(evidence, 'install.log'), 'w');
const install = spawnSync(bun, installArguments, {
  cwd: source, env: environment, stdio: ['ignore', installLog, installLog],
});
fs.closeSync(installLog);
writeJson('install-command.json', {
  command: bun, arguments: installArguments, status: install.status, signal: install.signal,
  error: install.error?.message ?? null, requestedMemoryLimitBytes: 2147483648,
  home: environment.HOME, cache: environment.BUN_INSTALL_CACHE_DIR, temporary: environment.TMPDIR,
});
assert.equal(await hashFile(path.join(source, 'bun.lock')), pin.lockSha256, 'The lockfile changed.');
assert.deepEqual(sourceManifest(), before, 'An upstream source file changed during install.');
assert.equal(install.status, 0, 'Locked installation failed. See evidence/install.log.');

const dependencyEntries = [];
async function scanDependencies(directory, relative = '') {
  for (const name of fs.readdirSync(directory).sort()) {
    const filename = path.join(directory, name);
    const entryPath = path.posix.join(relative, name);
    const stat = fs.lstatSync(filename);
    if (stat.isDirectory()) {
      await scanDependencies(filename, entryPath);
    } else if (stat.isSymbolicLink()) {
      const target = fs.readlinkSync(filename);
      const resolved = path.resolve(directory, target);
      assert(resolved === source || resolved.startsWith(`${source}/`), `External link: ${entryPath}`);
      dependencyEntries.push({ path: entryPath, type: 'symlink', target });
    } else {
      assert(stat.isFile(), `Unsupported dependency entry: ${entryPath}`);
      dependencyEntries.push({ path: entryPath, type: 'file', mode: stat.mode & 0o777,
        bytes: stat.size, sha256: await hashFile(filename) });
    }
  }
}
await scanDependencies(path.join(source, 'node_modules'));
const dependencySha256 = writeManifest('dependency-files.jsonl', dependencyEntries);

const packages = [];
function inspectPackage(directory) {
  const filename = path.join(directory, 'package.json');
  if (!fs.existsSync(filename)) return;
  const data = JSON.parse(fs.readFileSync(filename, 'utf8'));
  const scripts = Object.fromEntries(lifecycleNames
    .filter(name => typeof data.scripts?.[name] === 'string').map(name => [name, data.scripts[name]]));
  const entries = new Set();
  for (const field of ['main', 'module', 'types', 'typings']) {
    if (typeof data[field] === 'string') entries.add(data[field]);
  }
  const bins = typeof data.bin === 'string' ? [data.bin] : Object.values(data.bin ?? {});
  for (const value of bins) if (typeof value === 'string') entries.add(value);
  function exportPaths(value) {
    if (typeof value === 'string' && value.startsWith('./')) entries.add(value);
    else if (value && typeof value === 'object') Object.values(value).forEach(exportPaths);
  }
  exportPaths(data.exports);
  const missingLiteralPaths = [...entries].filter(value => !value.includes('*')
    && !fs.existsSync(path.resolve(directory, value))).sort();
  packages.push({ path: path.relative(source, directory) || '.', name: data.name,
    version: data.version, packageJsonSha256: hash(fs.readFileSync(filename)), scripts,
    missingLiteralPaths, wildcardPaths: [...entries].filter(value => value.includes('*')).sort() });
  if (!fs.lstatSync(directory).isSymbolicLink()) inspectModules(path.join(directory, 'node_modules'));
}
function inspectModules(directory) {
  if (!fs.existsSync(directory)) return;
  for (const name of fs.readdirSync(directory).sort()) {
    if (name.startsWith('.')) continue;
    const candidate = path.join(directory, name);
    if (name.startsWith('@')) {
      for (const member of fs.readdirSync(candidate).sort()) inspectPackage(path.join(candidate, member));
    } else inspectPackage(candidate);
  }
}
inspectPackage(source);
writeJson('packages.json', packages);
writeJson('lifecycle-hooks.json', packages.filter(entry => Object.keys(entry.scripts).length));
writeJson('missing-package-paths.json', packages.filter(entry => entry.missingLiteralPaths.length));

// Read the upstream config only. Do not typecheck, emit, or build Hono.
const require = createRequire(path.join(source, 'package.json'));
const ts = require('typescript');
const config = ts.getParsedCommandLineOfConfigFile(path.join(source, 'tsconfig.build.json'), {}, {
  ...ts.sys,
  onUnRecoverableConfigFileDiagnostic(diagnostic) {
    throw new Error(ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'));
  },
});
assert(config && config.errors.length === 0 && config.options.strict === true);
const files = config.fileNames.map(filename => path.relative(source, filename)).sort();
const trackedPaths = new Set(tracked.map(entry => entry.path));
assert(files.every(filename => trackedPaths.has(filename)), 'An untracked config root was selected.');
assert(files.includes('src/adapter/deno/deno.d.ts'), 'The Deno declaration must remain a root.');
const rootList = files.join('\n') + '\n';
assert.equal(hash(rootList), pin.rootsSha256, 'The upstream config root set changed.');
writeEvidence('tsconfig.build.files', rootList);
const report = {
  preparedSource: source,
  source: { commit: pin.commit, gitTree: git('rev-parse', `${pin.commit}^{tree}`),
    archiveSha256: await hashFile(sourceArchive), files: tracked.length, manifestSha256: sourceSha256,
    allTrackedBytesAndModesPreserved: true, cacheStillClean: git('status', '--porcelain=v1') === '' },
  config: { path: 'tsconfig.build.json', sha256: pin.configSha256,
    baseSha256: await hashFile(path.join(source, 'tsconfig.base.json')),
    roots: files.length, rootsSha256: hash(rootList), strict: true,
    module: ts.ModuleKind[config.options.module],
    moduleResolution: ts.ModuleResolutionKind[config.options.moduleResolution],
    types: config.options.types, mtsRoots: files.filter(filename => filename.endsWith('.mts')).length,
    declarationRoots: files.filter(filename => /\.d\.[cm]?ts$/.test(filename)).length },
  tools: { preparationScriptSha256: await hashFile(script),
    bun: { version: pin.bunVersion, revision: run(bun, ['--revision']),
    archiveUrl, archiveSha256: pin.bunArchiveSha256, binarySha256: pin.bunBinarySha256 },
    node: { version: process.version, binarySha256: await hashFile(process.execPath) },
    git: run('git', ['--version']), tar: run('tar', ['--version']).split('\n')[0],
    typescript: { version: ts.version,
      librarySha256: await hashFile(require.resolve('typescript')) } },
  host: { platform: process.platform, architecture: process.arch, kernel: os.release(),
    glibc: process.report.getReport().header.glibcVersionRuntime,
    requestedMemoryLimitBytes: 2147483648 },
  dependencies: { lockSha256: pin.lockSha256, manifestSha256: dependencySha256,
    files: dependencyEntries.filter(entry => entry.type === 'file').length,
    links: dependencyEntries.filter(entry => entry.type === 'symlink').length,
    packageLocations: packages.length - 1, installScriptsEnabled: false,
    lifecycleHookPackages: packages.filter(entry => Object.keys(entry.scripts).length).length },
  build: { executed: false, distExists: fs.existsSync(path.join(source, 'dist')) },
  compilerParity: 'not-run',
};
assert(report.source.cacheStillClean, 'The cache changed during preparation.');
assert.equal(report.build.distExists, false, 'Unexpected Hono build output.');
writeJson('preparation.json', report);
console.log(JSON.stringify(report, null, 2));
