#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';

const pin = {
  source: 'c92ca435c7e1827e0fd55c539080ef1bfd6fe3f0',
  lock: '53320f9e75f27f93be5161f5c968983597f0b41ca39a90c034afc5e8d20220c6',
  package: '41f2ebe4021d50fb3ce870a18c7228304e855041d6c96b5c93e1919de9645ff5',
  config: 'b53aa621db1475ecd4316db408f54cb41bb43d9bc737561f00985de4f4ff3c05',
  roots: '7ed182ee60381824081ffd18a0db0853bc62ea9ffd9a17b00e82987e5e6f0506',
  nodeVersion: 'v24.13.0',
  node: '53fb205ae78805130177e24bcb459a69a1518c8d98f8965f31d85aae7ea840fc',
  npmVersion: '11.6.2',
  npmTree: '2317d7658fc5d46d52941ee78964ba579ed1736bb664c50175feabdd13a32231',
  typescriptVersion: '5.9.2',
};
const script = fileURLToPath(import.meta.url);
const repo = path.dirname(path.dirname(script));
const run = (command, args, options = {}) => execFileSync(command, args, {
  encoding: 'utf8', maxBuffer: 32 * 1024 * 1024, ...options,
}).trim();
const sha = data => createHash('sha256').update(data).digest('hex');
const json = filename => JSON.parse(fs.readFileSync(filename, 'utf8'));
const writeJson = (filename, value) => writeOutput(filename, JSON.stringify(value, null, 2) + '\n');
const requireEqual = (actual, expected, label) => {
  if (actual !== expected) throw new Error(`${label}: expected ${expected}, received ${actual}`);
};
const gitEnvironment = { ...process.env, GIT_OPTIONAL_LOCKS: '0' };
const main = path.dirname(run('git', ['-C', repo, 'rev-parse', '--path-format=absolute', '--git-common-dir'], { env: gitEnvironment }));
const base = path.join(main, 'target/project-inputs/ts-pattern');
const output = path.resolve(process.argv[2] ?? base);
function contains(directory, filename) {
  const relative = path.relative(directory, filename);
  return relative === '' || relative !== '..' && !relative.startsWith(`..${path.sep}`) && !path.isAbsolute(relative);
}
if (!contains(base, output)) {
  throw new Error(`Output must remain under ${base}`);
}
const temporary = path.join(output, 'tmp');
const source = path.join(output, 'source');
const tools = path.join(output, 'tools');
const evidence = path.join(output, 'evidence');
const npmCache = path.join(output, 'npm-cache');
const archive = path.join(output, 'source.tar');
const emptyConfig = path.join(output, 'empty.npmrc');

// Resolve the nearest existing ancestor before creating any missing path.
function outputPathStat(filename) {
  if (!contains(output, filename)) throw new Error(`Unsafe output path: ${filename}`);
  let ancestor = filename;
  let stat = fs.lstatSync(ancestor, { throwIfNoEntry: false });
  while (!stat) {
    ancestor = path.dirname(ancestor);
    stat = fs.lstatSync(ancestor, { throwIfNoEntry: false });
  }
  if (stat.isSymbolicLink() || fs.realpathSync(ancestor) !== ancestor) {
    throw new Error(`Unsafe output ancestor or symlink: ${ancestor}`);
  }
  if (ancestor !== filename) {
    if (!stat.isDirectory()) throw new Error(`Output ancestor is not a directory: ${ancestor}`);
    return undefined;
  }
  if (!stat.isDirectory() && !stat.isFile()) throw new Error(`Unsupported output entry: ${filename}`);
  if (stat.isFile() && stat.nlink !== 1) throw new Error(`Shared output file: ${filename}`);
  return stat;
}

function inspectManagedPath(filename) {
  const stat = outputPathStat(filename);
  if (stat?.isDirectory()) {
    for (const name of fs.readdirSync(filename)) inspectManagedPath(path.join(filename, name));
  }
  return stat;
}

function outputDirectory(filename) {
  const stat = outputPathStat(filename);
  if (stat && !stat.isDirectory()) throw new Error(`Expected output directory: ${filename}`);
  return stat;
}

function outputFile(filename) {
  const stat = outputPathStat(filename);
  if (stat && !stat.isFile()) throw new Error(`Expected output file: ${filename}`);
  return stat;
}

function mkdirOutput(filename) {
  outputDirectory(filename);
  fs.mkdirSync(filename, { recursive: true });
  outputDirectory(filename);
}

function openOutput(filename) {
  outputFile(filename);
  const descriptor = fs.openSync(filename, fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_NOFOLLOW, 0o666);
  try {
    const stat = fs.fstatSync(descriptor);
    if (!stat.isFile() || stat.nlink !== 1) throw new Error(`Unsafe output file: ${filename}`);
    fs.ftruncateSync(descriptor, 0);
    return descriptor;
  } catch (error) {
    fs.closeSync(descriptor);
    throw error;
  }
}

function writeOutput(filename, bytes) {
  const descriptor = openOutput(filename);
  try {
    fs.writeFileSync(descriptor, bytes);
  } finally {
    fs.closeSync(descriptor);
  }
}

outputDirectory(output);
if (outputPathStat(source)) throw new Error(`Refusing to replace ${source}. Use a new output directory under ${base}.`);
if (outputPathStat(tools)) throw new Error(`Refusing to replace ${tools}. Use a new output directory.`);
for (const directory of [temporary, evidence, npmCache]) {
  const stat = inspectManagedPath(directory);
  if (stat && !stat.isDirectory()) throw new Error(`Expected managed directory: ${directory}`);
}
for (const filename of [archive, emptyConfig]) outputFile(filename);
const cache = fs.realpathSync(process.env.TS_PATTERN_REPO_CACHE ?? path.join(os.homedir(), '.explore/repos/gvergnaud__ts-pattern'));
if (contains(output, cache) || contains(cache, output)) throw new Error('Output and read-only source cache must not overlap');
mkdirOutput(temporary);

// Keep the install and its children within one memory scope.
if (process.env.TS_PATTERN_PREP_CGROUP !== '1') {
  const result = spawnSync('systemd-run', [
    '--user', '--scope', '--quiet', '--collect',
    '-p', 'MemoryMax=2147483648', '-p', 'MemorySwapMax=0',
    'env', 'TS_PATTERN_PREP_CGROUP=1', `TMPDIR=${temporary}`,
    'NODE_OPTIONS=--max-old-space-size=1536', process.execPath, script, output,
  ], { stdio: 'inherit' });
  if (result.error) throw result.error;
  process.exit(result.status ?? 1);
}

process.umask(0o022);
requireEqual(process.version, pin.nodeVersion, 'Node version');
requireEqual(process.platform, 'linux', 'Platform');
requireEqual(process.arch, 'x64', 'Architecture');
requireEqual(sha(fs.readFileSync(process.execPath)), pin.node, 'Node binary');
const git = (...args) => run('git', ['-C', cache, ...args], { env: gitEnvironment });
requireEqual(git('rev-parse', 'HEAD'), pin.source, 'Source commit');
requireEqual(git('status', '--porcelain=v1', '--untracked-files=all'), '', 'Source checkout state');
requireEqual(git('rev-parse', '--show-object-format'), 'sha1', 'Git object format');
for (const [filename, expected] of [
  ['package-lock.json', pin.lock], ['package.json', pin.package], ['tsconfig.json', pin.config],
]) requireEqual(sha(fs.readFileSync(path.join(cache, filename))), expected, filename);

function catalog(directory) {
  const records = [];
  function walk(current, relative = '') {
    for (const name of fs.readdirSync(current).sort()) {
      const filename = path.join(current, name);
      const item = path.posix.join(relative, name);
      const stat = fs.lstatSync(filename);
      if (stat.isDirectory()) walk(filename, item);
      else if (stat.isSymbolicLink()) records.push({ path: item, kind: 'symlink', target: fs.readlinkSync(filename) });
      else if (stat.isFile()) records.push({ path: item, kind: 'file', bytes: stat.size, sha256: sha(fs.readFileSync(filename)) });
      else throw new Error(`Unsupported input entry: ${filename}`);
    }
  }
  walk(directory);
  records.sort((a, b) => a.path < b.path ? -1 : a.path > b.path ? 1 : 0);
  return records.map(record => JSON.stringify(record)).join('\n') + '\n';
}

const npmCommand = process.env.PATH.split(path.delimiter)
  .map(directory => path.join(directory, 'npm')).find(filename => fs.existsSync(filename));
if (!npmCommand) throw new Error('npm is unavailable');
const originalNpmCli = fs.realpathSync(npmCommand);
requireEqual(path.basename(originalNpmCli), 'npm-cli.js', 'npm entry point');
const originalNpm = path.dirname(path.dirname(originalNpmCli));
requireEqual(json(path.join(originalNpm, 'package.json')).version, pin.npmVersion, 'npm version');
requireEqual(sha(catalog(originalNpm)), pin.npmTree, 'npm package content');
const node = path.join(tools, 'node/bin/node');
const npmRoot = path.join(tools, 'npm');
const npm = path.join(npmRoot, 'bin/npm-cli.js');
if (outputPathStat(tools)) throw new Error(`Tool destination must remain absent: ${tools}`);
mkdirOutput(path.dirname(node));
outputFile(node);
fs.copyFileSync(process.execPath, node, fs.constants.COPYFILE_EXCL);
outputFile(node);
fs.chmodSync(node, 0o755);
if (outputPathStat(npmRoot)) throw new Error(`npm destination must remain absent: ${npmRoot}`);
fs.cpSync(originalNpm, npmRoot, { recursive: true, dereference: false, errorOnExist: true, force: false });
requireEqual(sha(fs.readFileSync(node)), pin.node, 'Copied Node binary');
requireEqual(sha(catalog(npmRoot)), pin.npmTree, 'Copied npm content');

outputFile(archive);
run('git', ['-C', cache, 'archive', '--format=tar', `--output=${archive}`, pin.source], { env: gitEnvironment });
if (outputPathStat(source)) throw new Error(`Source destination must remain absent: ${source}`);
mkdirOutput(source);
outputDirectory(source);
run('tar', ['-xf', archive, '-C', source]);
const tracked = git('ls-tree', '-r', '-z', pin.source).split('\0').filter(Boolean).map(record => {
  const separator = record.indexOf('\t');
  const [mode, kind, oid] = record.slice(0, separator).split(' ');
  if (kind !== 'blob') throw new Error(`Unprepared Git object: ${record}`);
  return { path: record.slice(separator + 1), mode, oid };
});
function sourceCatalog() {
  return tracked.map(entry => {
    const filename = path.join(source, entry.path);
    const bytes = entry.mode === '120000' ? Buffer.from(fs.readlinkSync(filename)) : fs.readFileSync(filename);
    const oid = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
    requireEqual(oid, entry.oid, `Source blob ${entry.path}`);
    return JSON.stringify({ ...entry, bytes: bytes.length, sha256: sha(bytes) });
  }).sort().join('\n') + '\n';
}
const sourceFiles = sourceCatalog();
mkdirOutput(evidence);
writeOutput(path.join(evidence, 'source-files.jsonl'), sourceFiles);
const lock = json(path.join(source, 'package-lock.json'));
const packageEntries = Object.entries(lock.packages).filter(([name]) => name !== '');
const hooks = packageEntries.filter(([, data]) => data.hasInstallScript)
  .map(([name, data]) => ({ path: name, version: data.version, optional: data.optional ?? false }));
if (packageEntries.some(([, data]) => data.resolved && !data.resolved.startsWith('https://registry.npmjs.org/'))) {
  throw new Error('The lockfile contains a non-registry dependency that needs separate review');
}
writeJson(path.join(evidence, 'lock-install-hooks.json'), hooks);

writeOutput(emptyConfig, '');
const childEnv = Object.fromEntries(Object.entries(process.env).filter(([name]) =>
  !/^npm_config_/i.test(name) && !['NPM_TOKEN', 'NODE_AUTH_TOKEN', 'NODE_OPTIONS'].includes(name)));
Object.assign(childEnv, {
  PATH: `${path.dirname(node)}${path.delimiter}${process.env.PATH}`,
  TMPDIR: temporary, TMP: temporary, TEMP: temporary,
  NODE_OPTIONS: '--max-old-space-size=1536', NODE_ENV: 'development',
  npm_config_update_notifier: 'false', npm_config_maxsockets: '4',
});
const installArgs = [npm, 'ci', '--ignore-scripts', '--no-audit', '--no-fund',
  '--include=dev', '--include=optional', '--include=peer', '--install-strategy=hoisted',
  '--registry=https://registry.npmjs.org/', `--cache=${npmCache}`,
  `--userconfig=${emptyConfig}`, '--globalconfig=/dev/null'];
for (const directory of [temporary, evidence, npmCache]) inspectManagedPath(directory);
outputFile(emptyConfig);
requireEqual(run(node, [npm, '--version', `--cache=${npmCache}`,
  `--userconfig=${emptyConfig}`, '--globalconfig=/dev/null'], { cwd: source, env: childEnv }),
pin.npmVersion, 'Copied npm version');
const log = path.join(evidence, 'npm-ci.log');
for (const directory of [temporary, evidence, npmCache, source]) inspectManagedPath(directory);
if (outputPathStat(path.join(source, 'node_modules'))) throw new Error('The new source must not already have node_modules');
outputFile(emptyConfig);
const logFd = openOutput(log);
let install;
try {
  install = spawnSync(node, installArgs, { cwd: source, env: childEnv, stdio: ['ignore', logFd, logFd] });
} finally {
  fs.closeSync(logFd);
}
writeJson(path.join(evidence, 'install-result.json'), {
  command: [node, ...installArgs], exitCode: install.status, signal: install.signal,
  error: install.error?.message ?? null, memoryMaxBytes: 2147483648, scriptsEnabled: false,
});
if (install.error || install.status !== 0) throw new Error(`Locked install failed. See ${log}`);
requireEqual(sourceCatalog(), sourceFiles, 'Source content after install');

const packages = packageEntries.map(([name, data]) => {
  const packageFile = path.join(source, name, 'package.json');
  if (!fs.existsSync(packageFile)) return { path: name, version: data.version, installed: false,
    optional: data.optional ?? false, os: data.os ?? null, cpu: data.cpu ?? null, libc: data.libc ?? null };
  const installed = json(packageFile);
  requireEqual(installed.version, data.version, `Installed version ${name}`);
  return { path: name, version: installed.version, installed: true, integrity: data.integrity ?? null,
    lifecycleScripts: Object.fromEntries(Object.entries(installed.scripts ?? {}).filter(([key]) =>
      ['preinstall', 'install', 'postinstall', 'prepare'].includes(key))) };
});
const missingRequired = packages.filter(entry => !entry.installed && !entry.optional);
writeJson(path.join(evidence, 'packages.json'), packages);
if (missingRequired.length) throw new Error(`Required packages are missing: ${JSON.stringify(missingRequired)}`);
const dependencies = catalog(path.join(source, 'node_modules'));
writeOutput(path.join(evidence, 'dependency-files.jsonl'), dependencies);

const typescript = path.join(source, 'node_modules/typescript/lib/typescript.js');
const ts = createRequire(import.meta.url)(typescript);
requireEqual(ts.version, pin.typescriptVersion, 'Config reader version');
const parsed = ts.getParsedCommandLineOfConfigFile(path.join(source, 'tsconfig.json'), {}, {
  ...ts.sys, onUnRecoverableConfigFileDiagnostic(diagnostic) {
    throw new Error(ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'));
  },
});
if (!parsed || parsed.errors.length || parsed.options.strict !== true) throw new Error('The unchanged project config did not parse as strict');
const roots = parsed.fileNames.map(filename => path.relative(source, filename).split(path.sep).join('/')).sort();
const rootList = roots.join('\n') + '\n';
requireEqual(sha(rootList), pin.roots, 'Config root list');
writeOutput(path.join(evidence, 'roots.files'), rootList);

// Read the TypeScript input graph without diagnostics, checking, or emit.
const host = ts.createCompilerHost(parsed.options);
host.getCurrentDirectory = () => source;
const program = ts.createProgram({ rootNames: parsed.fileNames, options: parsed.options, host });
const inputs = program.getSourceFiles().map(file => {
  const filename = path.resolve(file.fileName);
  if (!filename.startsWith(source + path.sep)) throw new Error(`Unpinned external input: ${filename}`);
  return { path: path.relative(source, filename).split(path.sep).join('/'), bytes: fs.statSync(filename).size,
    sha256: sha(fs.readFileSync(filename)), declaration: file.isDeclarationFile };
}).sort((a, b) => a.path < b.path ? -1 : a.path > b.path ? 1 : 0);
const inputList = inputs.map(entry => JSON.stringify(entry)).join('\n') + '\n';
writeOutput(path.join(evidence, 'typescript-reader-inputs.jsonl'), inputList);
const missingGenerated = [
  'dist/index.d.ts', 'dist/index.d.cts', 'dist/types/index.d.ts', 'dist/types/index.d.cts',
  'dist/index.js', 'dist/index.cjs', 'dist/index.umd.js',
].filter(filename => !fs.existsSync(path.join(source, filename)));
writeJson(path.join(evidence, 'preparation.json'), {
  sourceCommit: pin.source, preparedInput: source, config: 'tsconfig.json',
  sourceArchiveSha256: sha(fs.readFileSync(archive)), sourceCatalogSha256: sha(sourceFiles), sourceFiles: tracked.length,
  packageSha256: pin.package, lockSha256: pin.lock, configSha256: pin.config,
  sourceUnchangedAfterInstall: true, configUnchanged: true,
  node: { version: process.version, binary: node, sha256: pin.node },
  npm: { version: pin.npmVersion, cli: npm, treeSha256: pin.npmTree },
  tools: { git: run('git', ['--version']), tar: run('tar', ['--version']).split('\n')[0] },
  machine: { platform: process.platform, architecture: process.arch, kernel: os.release(), libc: run('getconf', ['GNU_LIBC_VERSION']) },
  install: { scriptsEnabled: false, memoryMaxBytes: 2147483648, cache: path.join(output, 'npm-cache'), temporary,
    log, packagesInLock: packageEntries.length, packagesInstalled: packages.filter(entry => entry.installed).length,
    omittedOptionalPackages: packages.filter(entry => !entry.installed), missingRequiredPackages: missingRequired },
  dependencyCatalogSha256: sha(dependencies), dependencyEntries: dependencies.trimEnd().split('\n').length,
  configReader: { version: ts.version, sha256: sha(fs.readFileSync(typescript)), rootFiles: roots.length,
    rootListSha256: sha(rootList), module: ts.ModuleKind[parsed.options.module],
    moduleResolution: ts.ModuleResolutionKind[parsed.options.moduleResolution], strict: parsed.options.strict,
    skipLibCheck: parsed.options.skipLibCheck, types: parsed.options.types ?? null },
  readerInputFiles: inputs.length, readerInputCatalogSha256: sha(inputList),
  missingGeneratedOutputs: missingGenerated, sourceBuildRun: false, lifecycleScriptsRun: false,
  semanticChecksRun: false, emitRun: false, goOracleRun: false, rustParityRun: false,
  scope: 'Dependency preparation and a TypeScript reader snapshot. Not a Go graph or parity manifest.',
  preparationScriptSha256: sha(fs.readFileSync(script)),
});
requireEqual(git('status', '--porcelain=v1', '--untracked-files=all'), '', 'Source checkout state after preparation');
console.log(JSON.stringify({ preparedInput: source, evidence: path.join(evidence, 'preparation.json'), roots: roots.length, readerInputs: inputs.length }, null, 2));
