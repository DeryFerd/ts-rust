import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import fs from 'node:fs';
import { createRequire } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const pin = '4d5139552dac8593c5e020846fa7ce8e96ea97b7';
const lockHash = '67218d513a065e0519a5c032e7b930c50d237af7fc445b3c6ba13b430aa58c59';
const packageManager = 'pnpm@10.33.4+sha512.1c67b3b359b2d408119ba1ed289f34b8fc3c6873412bec6fd264fbdc82489e510fcbecb9ce9d22dae7f3b76269d8441046014bdca53b9979cd7a561ad631b800';
const generatorHash = '3ba6494526ef3041c835674561af4e725054c092c7c72b6c21faaa1c09994ad8';
const generatorDependencies = {
  'packages/svelte/node_modules/dts-buddy/src/index.js': '053a3e9b7cf093203508f2d210827948a9c274d449a21d6d7135347ba42a432f',
  'packages/svelte/node_modules/dts-buddy/src/create-module-declaration.js': '6bfb8df256e02b5650d85373c976588b807b5af49f21ecc3c6bf243b633c4792',
  'packages/svelte/node_modules/dts-buddy/src/utils.js': '5cf61687308968f96c76c53d12123c5ef5f5b1d54caef835ccde6dfc22546a2c',
  'node_modules/typescript/lib/typescript.js': 'f7ff3e27aafe5dcc82d0307575e9a7dc5b053b141da123bec81c858537765b56',
};
const script = fileURLToPath(import.meta.url);
const gitDirectory = execFileSync('git', [
  '-C', path.dirname(script), 'rev-parse', '--path-format=absolute', '--git-common-dir',
], { encoding: 'utf8' }).trim();
const inputBase = path.join(path.dirname(gitDirectory), 'target/project-inputs/svelte');
const root = path.resolve(process.env.SVELTE_INPUT_DIR ?? inputBase);
const cache = fs.realpathSync(process.env.SVELTE_REPO ?? path.join(os.homedir(), '.explore/repos/sveltejs__svelte'));
const source = path.join(root, 'source');
const evidence = path.join(root, 'evidence');
const packageRoot = path.join(source, 'packages/svelte');
const hash = (bytes, algorithm = 'sha256') => createHash(algorithm).update(bytes).digest('hex');
const fileHash = (filename) => hash(fs.readFileSync(filename));
const json = (filename) => JSON.parse(fs.readFileSync(filename, 'utf8'));
const writeJson = (name, value) => writeEvidence(name, JSON.stringify(value, null, 2) + '\n');
const relative = (filename) => path.relative(source, filename).split(path.sep).join('/');
const generatedPaths = [
  ...['action', 'animate', 'compiler', 'easing', 'index', 'legacy', 'motion', 'store', 'transition'].map((name) => `packages/svelte/${name}.d.ts`),
  'packages/svelte/types/compiler/interfaces.d.ts',
  'packages/svelte/types/compiler/preprocess.d.ts',
  'packages/svelte/types/index.d.ts',
  'packages/svelte/types/index.d.ts.map',
];

function contains(directory, filename) {
  const remainder = path.relative(directory, filename);
  return remainder === '' || remainder !== '..' && !remainder.startsWith(`..${path.sep}`) && !path.isAbsolute(remainder);
}

// Validate existing ancestors before creating any part of a missing destination.
function outputPathStat(filename) {
  assert.ok(contains(root, filename), `Unsafe output path: ${filename}`);
  let ancestor = filename;
  let stat = fs.lstatSync(ancestor, { throwIfNoEntry: false });
  while (!stat) {
    ancestor = path.dirname(ancestor);
    stat = fs.lstatSync(ancestor, { throwIfNoEntry: false });
  }
  assert.ok(!stat.isSymbolicLink() && fs.realpathSync(ancestor) === ancestor, `Unsafe output path: ${ancestor}`);
  if (ancestor !== filename) {
    assert.ok(stat.isDirectory(), `Unsafe output ancestor: ${ancestor}`);
    return undefined;
  }
  assert.ok(stat.isDirectory() || stat.isFile(), `Unsafe output kind: ${filename}`);
  if (stat.isFile()) assert.equal(stat.nlink, 1, `Shared output file: ${filename}`);
  return stat;
}

function inspectManagedPath(filename) {
  const stat = fs.lstatSync(filename, { throwIfNoEntry: false });
  if (stat?.isSymbolicLink()) {
    const resolved = fs.realpathSync(filename);
    const parts = path.relative(source, filename).split(path.sep);
    const dependency = parts.slice(parts.lastIndexOf('node_modules') + 1);
    const packageLink = dependency.length === 1 && !dependency[0].startsWith('.') && !dependency[0].startsWith('@')
      || dependency.length === 2 && dependency[0].startsWith('@') && !dependency[1].startsWith('.');
    const dependencyLink = contains(source, filename) && parts.includes('node_modules') && packageLink;
    const projectMarker = path.dirname(filename) === path.join(root, 'store/v10/projects') && resolved === source;
    assert.ok((dependencyLink && contains(source, resolved) || projectMarker) && !contains(cache, resolved), `Unsafe managed link: ${filename}`);
    return;
  }
  outputPathStat(filename);
  if (stat?.isDirectory()) {
    for (const entry of fs.readdirSync(filename)) inspectManagedPath(path.join(filename, entry));
  }
}

function outputFile(filename) {
  const stat = outputPathStat(filename);
  assert.ok(!stat || stat.isFile(), `Expected output file: ${filename}`);
}

function writeEvidence(name, bytes) {
  const filename = path.join(evidence, name);
  outputFile(filename);
  fs.writeFileSync(filename, bytes);
}

const action = process.argv[2];
assert.ok(['copy', 'install', 'generate', 'record'].includes(action) && process.argv.length === 3,
  'Usage: node scripts/prepare-svelte-input.mjs copy|install|generate|record');
assert.ok(contains(inputBase, root), 'The output must stay under target/project-inputs/svelte');
assert.ok(!contains(root, cache) && !contains(cache, root), 'The output and read-only cache must not overlap');
const managedDirectories = ['evidence', 'home', 'tmp', 'corepack', 'cache', 'data', 'state', 'store'];
for (const directory of [root, source, packageRoot, ...managedDirectories.map((name) => path.join(root, name)),
  path.join(source, 'node_modules'), path.join(packageRoot, 'node_modules'), path.join(source, 'playgrounds/sandbox/node_modules')]) {
  const stat = outputPathStat(directory);
  assert.ok(!stat || stat.isDirectory(), `Expected output directory: ${directory}`);
}
for (const directory of [source, ...managedDirectories.map((name) => path.join(root, name))]) inspectManagedPath(directory);
outputFile(path.join(root, 'source.tar'));
for (const filename of generatedPaths) outputFile(path.join(source, filename));
if (action === 'record') validateGeneration();
for (const directory of managedDirectories) fs.mkdirSync(path.join(root, directory), { recursive: true });

const environment = {
  ...process.env,
  HOME: path.join(root, 'home'),
  TMPDIR: path.join(root, 'tmp'),
  COREPACK_HOME: path.join(root, 'corepack'),
  COREPACK_ENABLE_DOWNLOAD_PROMPT: '0',
  COREPACK_ENABLE_PROJECT_SPEC: '1',
  XDG_CACHE_HOME: path.join(root, 'cache'),
  XDG_DATA_HOME: path.join(root, 'data'),
  XDG_STATE_HOME: path.join(root, 'state'),
  npm_config_cache: path.join(root, 'cache/npm'),
  npm_config_ignore_scripts: 'true',
  PLAYWRIGHT_SKIP_BROWSER_DOWNLOAD: '1',
  NODE_OPTIONS: '--max-old-space-size=1536 --dns-result-order=ipv4first',
  CI: 'true',
  GIT_OPTIONAL_LOCKS: '0',
};

function output(command, args, cwd = source) {
  return execFileSync(command, args, { cwd, env: environment, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 }).trim();
}

function run(command, args, name, cwd = source) {
  const log = path.join(evidence, `${name}.log`);
  console.log(`${name}: ${command} ${args.join(' ')}`);
  outputFile(log);
  const descriptor = fs.openSync(log, 'w');
  let result;
  try {
    result = spawnSync(command, args, { cwd, env: environment, stdio: ['ignore', descriptor, descriptor] });
  } finally {
    fs.closeSync(descriptor);
  }
  writeJson(`${name}.command.json`, { command, args, cwd, exitCode: result.status, signal: result.signal });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `Command failed. Read ${log}`);
}

function pinnedFiles() {
  assert.equal(output('git', ['rev-parse', 'HEAD'], cache), pin, 'The cache is at a different commit');
  assert.equal(output('git', ['status', '--porcelain=v1', '--untracked-files=all'], cache), '', 'The cache has changes');
  return output('git', ['ls-tree', '-rz', pin], cache).split('\0').filter(Boolean).map((entry) => {
    const [header, filename] = entry.split('\t');
    const [mode, kind, blob] = header.split(' ');
    assert.equal(kind, 'blob', `Unsupported tree entry: ${filename}`);
    assert.ok(!filename.includes('\n'), 'Source filenames must fit a line manifest');
    return { path: filename, mode, blob };
  });
}

function verifySource() {
  const files = pinnedFiles().map((entry) => {
    const filename = path.join(source, entry.path);
    const stat = fs.lstatSync(filename);
    const bytes = stat.isSymbolicLink() ? Buffer.from(fs.readlinkSync(filename)) : fs.readFileSync(filename);
    const gitBlob = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
    assert.equal(gitBlob, entry.blob, `Pinned source changed: ${entry.path}`);
    assert.equal(stat.isSymbolicLink(), entry.mode === '120000', `Source kind changed: ${entry.path}`);
    if (!stat.isSymbolicLink()) {
      assert.equal((stat.mode & 0o111) !== 0, entry.mode === '100755', `Source mode changed: ${entry.path}`);
    }
    return { ...entry, sha256: hash(bytes), bytes: bytes.length };
  });
  assert.equal(fileHash(path.join(source, 'pnpm-lock.yaml')), lockHash);
  assert.equal(json(path.join(source, 'package.json')).packageManager, packageManager);
  writeJson('source-files.json', files);
  return files;
}

function copy() {
  pinnedFiles();
  if (!outputPathStat(source)) {
    outputFile(path.join(root, 'source.tar'));
    fs.mkdirSync(source);
    output('git', ['archive', '--format=tar', '--output', path.join(root, 'source.tar'), pin], cache);
    output('tar', ['-xf', path.join(root, 'source.tar'), '-C', source], root);
  }
  const files = verifySource();
  writeJson('source.json', {
    repository: 'sveltejs/svelte', commit: pin,
    tree: output('git', ['rev-parse', `${pin}^{tree}`], cache),
    archiveSha256: fileHash(path.join(root, 'source.tar')),
    trackedFiles: files.length, sourceManifestSha256: fileHash(path.join(evidence, 'source-files.json')),
    lockSha256: lockHash, packageManager,
  });
  console.log(`Verified ${files.length} tracked source files in ${source}`);
}

function install() {
  verifySource();
  run('corepack', ['pnpm', '--version'], 'pnpm-version');
  assert.equal(output('corepack', ['pnpm', '--version']), '10.33.4');
  const manager = json(path.join(root, 'corepack/v1/pnpm/10.33.4/.corepack'));
  assert.equal(`${manager.locator.name}@${manager.locator.reference}`, packageManager);
  assert.equal(manager.hash, packageManager.split('+')[1]);
  run('corepack', ['pnpm', 'install', '--frozen-lockfile', '--ignore-scripts', '--child-concurrency=1', '--network-concurrency=8', '--store-dir', path.join(root, 'store')], 'install');
  verifySource();
}

function generatedFiles() {
  return generatedPaths.map((filename) => {
    assert.ok(outputPathStat(path.join(source, filename))?.isFile(), `Missing generated output: ${filename}`);
    return { path: filename, sha256: fileHash(path.join(source, filename)) };
  });
}

function validateGeneration() {
  const filename = path.join(evidence, 'generation.json');
  assert.ok(outputPathStat(filename)?.isFile(), 'Missing generation evidence');
  const generation = json(filename);
  assert.equal(generation.script, 'packages/svelte/scripts/generate-types.js');
  assert.equal(generation.sha256, generatorHash);
  assert.deepEqual(generation.dependencies, generatorDependencies);
  assert.equal(generation.runs, 2);
  assert.equal(generation.exactReplay, true);
  assert.deepEqual(generatedFiles(), generation.outputs, 'Current generated outputs do not match generation evidence');
  return generation;
}

function generate() {
  verifySource();
  const generator = path.join(packageRoot, 'scripts/generate-types.js');
  assert.equal(fileHash(generator), generatorHash);
  assert.equal(json(path.join(packageRoot, 'node_modules/dts-buddy/package.json')).version, '0.5.5');
  assert.equal(json(path.join(packageRoot, 'node_modules/typescript/package.json')).version, '5.5.4');
  for (const [filename, digest] of Object.entries(generatorDependencies)) {
    assert.equal(fileHash(path.join(source, filename)), digest, `Generator dependency changed: ${filename}`);
  }
  run(process.execPath, ['scripts/generate-types.js'], 'generate-types', packageRoot);
  verifySource();
  const first = generatedFiles();
  run(process.execPath, ['scripts/generate-types.js'], 'generate-types-replay', packageRoot);
  verifySource();
  assert.deepEqual(generatedFiles(), first, 'The type generator did not replay exactly');
  writeJson('generation.json', { script: 'packages/svelte/scripts/generate-types.js', sha256: generatorHash, dependencies: generatorDependencies, runs: 2, exactReplay: true, outputs: first });
}

function walk(directory) {
  const entries = [];
  for (const entry of fs.readdirSync(directory, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name, 'en'))) {
    const filename = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      entries.push(...walk(filename));
    } else if (entry.isSymbolicLink()) {
      const target = fs.readlinkSync(filename);
      const resolved = fs.realpathSync(filename);
      assert.ok(resolved.startsWith(source + path.sep), `Dependency link leaves the prepared source: ${filename}`);
      entries.push({ path: relative(filename), kind: 'symlink', target, resolved: relative(resolved), sha256: hash(target) });
    } else if (entry.isFile()) {
      const stat = fs.statSync(filename);
      entries.push({ path: relative(filename), kind: 'file', bytes: stat.size, mode: stat.mode & 0o777, sha256: fileHash(filename) });
    } else {
      throw new Error(`Unsupported prepared file: ${filename}`);
    }
  }
  return entries;
}

function executable(name) {
  const filename = process.env.PATH.split(path.delimiter).map((directory) => path.join(directory, name)).find((filename) => fs.existsSync(filename));
  assert.ok(filename, `Missing executable: ${name}`);
  return fs.realpathSync(filename);
}

function memoryScope() {
  const cgroups = '/proc/self/cgroup';
  if (!fs.existsSync(cgroups)) return null;
  const group = fs.readFileSync(cgroups, 'utf8').split('\n').find((line) => line.startsWith('0::'))?.slice(3);
  if (!group) return null;
  const directory = path.join('/sys/fs/cgroup', group);
  const read = (name) => {
    const filename = path.join(directory, name);
    return fs.existsSync(filename) ? fs.readFileSync(filename, 'utf8').trim() : null;
  };
  return { memoryMax: read('memory.max'), memorySwapMax: read('memory.swap.max') };
}

function record() {
  const generation = validateGeneration();
  const tracked = verifySource();
  const require = createRequire(import.meta.url);
  const tsPath = fs.realpathSync(path.join(source, 'node_modules/typescript/lib/typescript.js'));
  const ts = require(tsPath);
  assert.equal(ts.version, '5.5.4');
  const configs = [
    ['runtime', 'packages/svelte/tsconfig.runtime.json', 160, '27004d241717123c9e1b65303627443cc81dda1b7ea24d78ec2847ba0817f18b'],
    ['compiler', 'packages/svelte/tsconfig.json', 3233, 'abe26182af676fac1d42e3fe5e022b9ac0542b0dd9ee932d876415b9568b26ed'],
  ].map(([id, config, count, expectedHash]) => {
    const filename = path.join(source, config);
    const parsed = ts.getParsedCommandLineOfConfigFile(filename, {}, {
      ...ts.sys,
      onUnRecoverableConfigFileDiagnostic(diagnostic) { throw new Error(ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n')); },
    });
    assert.ok(parsed);
    assert.equal(parsed.errors.length, 0);
    for (const option of ['strict', 'allowJs', 'checkJs']) assert.equal(parsed.options[option], true);
    const roots = parsed.fileNames.map(relative).sort();
    const list = roots.join('\n') + '\n';
    assert.equal(roots.length, count, `Root count changed: ${config}`);
    assert.equal(hash(list), expectedHash, `Root list changed: ${config}`);
    writeEvidence(`${id}.roots.txt`, list);
    const program = ts.createProgram({ rootNames: parsed.fileNames, options: parsed.options, projectReferences: parsed.projectReferences });
    const graph = [...new Set(program.getSourceFiles().map((file) => relative(fs.realpathSync(file.fileName))))].sort().map((file) => ({ path: file, sha256: fileHash(path.join(source, file)) }));
    writeJson(`${id}.loaded-files.json`, graph);
    return {
      config, sha256: fileHash(filename), roots: roots.length, rootListSha256: hash(list),
      configChain: [...(parsed.options.configFile.extendedSourceFiles ?? []), filename].map((file) => ({ path: relative(file), sha256: fileHash(file) })),
      strict: true, allowJs: true, checkJs: true, module: ts.ModuleKind[parsed.options.module],
      moduleResolution: ts.ModuleResolutionKind[parsed.options.moduleResolution],
      loadedFiles: graph.length, loadedFilesSha256: fileHash(path.join(evidence, `${id}.loaded-files.json`)),
    };
  });
  const files = walk(source);
  writeJson('prepared-files.json', files);
  const workspaceLinks = files.filter((entry) => entry.kind === 'symlink' && entry.resolved.startsWith('packages/svelte'));
  writeJson('workspace-links.json', workspaceLinks);
  const licenses = files.filter((entry) => entry.kind === 'file' && /^(licen[sc]e|notice|copying)([.-]|$)/i.test(path.basename(entry.path)));
  writeJson('license-files.json', licenses);
  const hooks = files.filter((entry) => /(?:^|\/)node_modules\/(?:@[^/]+\/)?[^/]+\/package\.json$/.test(entry.path)).flatMap((entry) => {
    const pkg = json(path.join(source, entry.path));
    const scripts = Object.fromEntries(['preinstall', 'install', 'postinstall', 'prepare'].filter((name) => pkg.scripts?.[name]).map((name) => [name, pkg.scripts[name]]));
    return Object.keys(scripts).length ? [{ path: entry.path, package: pkg.name, version: pkg.version, scripts }] : [];
  });
  writeJson('dependency-lifecycle-scripts.json', hooks);
  const modules = json(path.join(source, 'node_modules/.modules.yaml'));
  const node = fs.realpathSync(process.execPath);
  const corepack = executable('corepack');
  const corepackImplementation = path.join(path.dirname(corepack), 'lib/corepack.cjs');
  const pnpm = path.join(root, 'corepack/v1/pnpm/10.33.4/bin/pnpm.cjs');
  const pnpmImplementation = path.join(root, 'corepack/v1/pnpm/10.33.4/dist/pnpm.cjs');
  const manager = json(path.join(root, 'corepack/v1/pnpm/10.33.4/.corepack'));
  assert.equal(`${manager.locator.name}@${manager.locator.reference}`, packageManager);
  assert.equal(manager.hash, packageManager.split('+')[1]);
  assert.deepEqual(generatedFiles(), generation.outputs, 'Generated outputs changed while recording');
  writeJson('input.json', {
    status: 'prepared, no compiler parity run', repository: 'sveltejs/svelte', commit: pin,
    platform: { os: os.platform(), architecture: os.arch(), release: os.release(), memoryScope: memoryScope() },
    tools: {
      node: { version: process.version, path: node, sha256: fileHash(node) },
      corepack: { version: output('corepack', ['--version']), path: corepack, sha256: fileHash(corepack), implementationSha256: fileHash(corepackImplementation) },
      pnpm: { packageManager, version: output('corepack', ['pnpm', '--version']), path: pnpm, sha256: fileHash(pnpm), implementationSha256: fileHash(pnpmImplementation), packageIntegrity: manager.hash },
      typescript: { version: ts.version, path: relative(tsPath), sha256: fileHash(tsPath) },
    },
    lockSha256: lockHash, sourceFiles: tracked.length,
    sourceManifestSha256: fileHash(path.join(evidence, 'source-files.json')),
    preparedFiles: files.length, preparedManifestSha256: fileHash(path.join(evidence, 'prepared-files.json')),
    workspaceLinks, licenseFiles: licenses.length, dependencyManifestsWithLifecycleScripts: hooks.length,
    installation: { included: modules.included, nodeLinker: modules.nodeLinker, pendingBuilds: modules.pendingBuilds, skippedPlatformPackages: modules.skipped },
    configs, generation,
    pending: ['Pinned Go and Rust config and module graph comparison', 'Go diagnostics, types, and symbols artifacts', 'Cold and warm compiler runs'],
  });
  console.log(`Recorded ${files.length} prepared entries. Read ${path.join(evidence, 'input.json')}`);
}

const actions = { copy, install, generate, record };
actions[action]();
