import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  chmodSync, copyFileSync, existsSync, linkSync, mkdirSync, mkdtempSync, readFileSync,
  readdirSync, realpathSync, rmSync, symlinkSync, writeFileSync,
} from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

const script = fileURLToPath(new URL('./prepare-effect-project-inputs.mjs', import.meta.url));
const pin = '0d083ba26b2e1afec8d3e8d83db0d05683b6602b';
const archiveSha256 = '34e198cb1e43237517ecedfd31f9ae26a6c0a3e5366ce58a2d05f4b21fb5f19a';
const integrity = 'sha512-mm8zCpW2ZEbqCI+vFSFAWooB8H/ecSTMmVjf7VLUu0NnN+ZbCPhfN7Rvy6N1CSVYrFEmK4FoRLIvY0Bu0Wa/7g==';
const integrityHex = Buffer.from(integrity.slice('sha512-'.length), 'base64').toString('hex');
const archiveSuffix = path.join('_cacache/content-v2/sha512', integrityHex.slice(0, 2), integrityHex.slice(2, 4), integrityHex.slice(4));
const commonGit = execFileSync('git', ['-C', path.dirname(script), 'rev-parse', '--path-format=absolute', '--git-common-dir'], { encoding: 'utf8' }).trim();
const archive = process.env.EFFECT_TEST_PNPM_ARCHIVE
  ?? path.join(path.dirname(commonGit), 'target/project-inputs/effect/cache/npm', archiveSuffix);
assert.equal(createHash('sha256').update(readFileSync(archive)).digest('hex'), archiveSha256,
  'Set EFFECT_TEST_PNPM_ARCHIVE to the existing pinned pnpm 11.20.0 tarball. This proof never downloads it.');
const proofRoot = mkdtempSync(path.join(os.tmpdir(), 'effect-input-safety-'));
console.log(`Disposable proof files: ${proofRoot}`);

function write(filename, text) {
  mkdirSync(path.dirname(filename), { recursive: true });
  writeFileSync(filename, text);
}

function fixture(name, withSource = true) {
  const root = path.join(proofRoot, name);
  const workspace = path.join(root, 'workspace');
  const output = path.join(workspace, 'target/project-inputs/effect');
  const source = path.join(output, 'source');
  const cache = path.join(root, 'repo-cache');
  const reader = path.join(root, 'reader-cache');
  const bin = path.join(root, 'bin');
  const outside = path.join(root, 'outside');
  const trace = path.join(root, 'commands.jsonl');
  const packageJson = '{"packageManager":"pnpm@11.20.0"}\n';
  const blob = createHash('sha1').update(`blob ${Buffer.byteLength(packageJson)}\0`).update(packageJson).digest('hex');
  for (const directory of [workspace, cache, reader, bin, outside]) mkdirSync(directory, { recursive: true });
  write(path.join(cache, 'package.json'), packageJson);
  if (withSource) write(path.join(source, 'package.json'), packageJson);
  for (const filename of ['lib/typescript.js', 'package.json', 'LICENSE.txt', 'ThirdPartyNoticeText.txt']) write(path.join(reader, filename), '{}\n');
  const copiedScript = path.join(workspace, 'scripts/prepare-effect-project-inputs.mjs');
  mkdirSync(path.dirname(copiedScript), { recursive: true });
  copyFileSync(script, copiedScript);
  write(path.join(bin, 'git'), `#!/usr/bin/env node
const args = process.argv.slice(2);
if (args.includes('--git-common-dir')) console.log(${JSON.stringify(path.join(workspace, '.git'))});
else if (args.includes('rev-parse')) console.log(${JSON.stringify(pin)});
else if (args.includes('status')) process.stdout.write('');
else if (args.includes('ls-tree')) process.stdout.write(${JSON.stringify(`100644 blob ${blob}\tpackage.json\0`)});
else throw new Error('Unexpected Git command: ' + JSON.stringify(args));
`);
  for (const executable of ['npm', 'systemd-run']) {
    write(path.join(bin, executable), `#!/usr/bin/env node
const fs = require('node:fs');
fs.appendFileSync(${JSON.stringify(trace)}, JSON.stringify({ executable: ${JSON.stringify(executable)}, args: process.argv.slice(2) }) + '\\n');
console.error('Disposable proof stopped this command.');
process.exit(77);
`);
  }
  for (const executable of ['git', 'npm', 'systemd-run']) chmodSync(path.join(bin, executable), 0o755);
  return { root, workspace, output, source, cache, reader, bin, outside, trace, copiedScript };
}

function run(fixture) {
  const result = spawnSync(process.execPath, [fixture.copiedScript, '--offline'], {
    cwd: fixture.workspace, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024,
    env: {
      ...process.env,
      PATH: `${fixture.bin}:${process.env.PATH}`,
      HOME: fixture.root,
      TMPDIR: fixture.root,
      NODE_DISABLE_COMPILE_CACHE: '1',
      EFFECT_REPO_CACHE: fixture.cache,
      EFFECT_CONFIG_READER: fixture.reader,
    },
  });
  if (result.error) throw result.error;
  write(path.join(fixture.root, 'stdout.log'), result.stdout);
  write(path.join(fixture.root, 'stderr.log'), result.stderr);
  return result;
}

function rejected(fixture, pattern = /Unsafe symlink:/) {
  const result = run(fixture);
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, pattern);
  assert(!existsSync(fixture.trace), 'An install or host npm command ran before rejection');
}

for (const ancestor of ['target', 'target/project-inputs', 'target/project-inputs/effect']) {
  test(`reject ${ancestor} symlink before creating output directories`, () => {
    const f = fixture(`ancestor-${ancestor.replaceAll('/', '-')}`, false);
    const link = path.join(f.workspace, ancestor);
    mkdirSync(path.dirname(link), { recursive: true });
    symlinkSync(f.outside, link);
    rejected(f);
    assert.deepEqual(readdirSync(f.outside), []);
  });
}

for (const directory of ['evidence', 'home', 'tmp', 'cache', 'config', 'data', 'state', 'tools', 'pnpm-home', 'store']) {
  test(`reject the ${directory} managed directory symlink`, () => {
    const f = fixture(`managed-${directory}`);
    symlinkSync(f.outside, path.join(f.output, directory));
    rejected(f);
    assert.deepEqual(readdirSync(f.outside), []);
  });
}

for (const filename of ['evidence/source-before.json', 'evidence/commands.json', 'evidence/installed-files.jsonl', 'tmp/source.tar', 'tools/typescript-config-reader/lib/typescript.js']) {
  test(`reject the ${filename} file symlink before overwrite`, () => {
    const f = fixture(`file-${filename.replaceAll('/', '-')}`);
    const sentinel = path.join(f.outside, 'sentinel');
    write(sentinel, 'unchanged\n');
    const link = path.join(f.output, filename);
    mkdirSync(path.dirname(link), { recursive: true });
    symlinkSync(sentinel, link);
    rejected(f);
    assert.equal(readFileSync(sentinel, 'utf8'), 'unchanged\n');
  });
}

test('reject a dangling file symlink', () => {
  const f = fixture('dangling-file');
  const missing = path.join(f.outside, 'missing');
  mkdirSync(path.join(f.output, 'evidence'));
  symlinkSync(missing, path.join(f.output, 'evidence/source-before.json'));
  rejected(f);
  assert(!existsSync(missing));
});

test('reject a hard-linked evidence destination before truncation', () => {
  const f = fixture('hard-linked-evidence');
  const sentinel = path.join(f.outside, 'sentinel');
  write(sentinel, 'unchanged\n');
  mkdirSync(path.join(f.output, 'evidence'));
  linkSync(sentinel, path.join(f.output, 'evidence/source-before.json'));
  rejected(f, /Refusing a hard-linked output file/);
  assert.equal(readFileSync(sentinel, 'utf8'), 'unchanged\n');
});

test('reject a source directory that aliases the input cache', () => {
  const f = fixture('source-cache-alias', false);
  mkdirSync(f.output, { recursive: true });
  symlinkSync(f.cache, f.source);
  const before = readFileSync(path.join(f.cache, 'package.json'));
  rejected(f);
  assert.deepEqual(readFileSync(path.join(f.cache, 'package.json')), before);
  assert.deepEqual(readdirSync(f.cache), ['package.json']);
});

test('reject a nested source directory symlink', () => {
  const f = fixture('nested-source');
  symlinkSync(f.outside, path.join(f.source, 'packages'));
  rejected(f);
  assert.deepEqual(readdirSync(f.outside), []);
});

test('reject a source dependency link outside the source copy', () => {
  const f = fixture('external-dependency');
  mkdirSync(path.join(f.source, 'node_modules'));
  symlinkSync(f.outside, path.join(f.source, 'node_modules/external'));
  rejected(f);
  assert.deepEqual(readdirSync(f.outside), []);
});

test('reject an input-reader file symlink before copying or executing it', () => {
  const f = fixture('reader-cache-file');
  const readerFile = path.join(f.reader, 'lib/typescript.js');
  const sentinel = path.join(f.outside, 'reader.js');
  write(sentinel, 'unchanged\n');
  rmSync(readerFile);
  symlinkSync(sentinel, readerFile);
  rejected(f);
  assert.equal(readFileSync(sentinel, 'utf8'), 'unchanged\n');
});

test('reject a pnpm executable symlink before external code runs', () => {
  const f = fixture('external-pnpm');
  const marker = path.join(f.outside, 'executed');
  const external = path.join(f.outside, 'pnpm.mjs');
  write(external, `import { writeFileSync } from 'node:fs'; writeFileSync(${JSON.stringify(marker)}, 'executed'); console.log('11.20.0');\n`);
  const cli = path.join(f.output, 'tools/pnpm/node_modules/pnpm/bin/pnpm.mjs');
  mkdirSync(path.dirname(cli), { recursive: true });
  symlinkSync(external, cli);
  rejected(f);
  assert(!existsSync(marker));
});

function seedPinnedPnpm(f) {
  const packageRoot = path.join(f.output, 'tools/pnpm/node_modules/pnpm');
  mkdirSync(packageRoot, { recursive: true });
  execFileSync('tar', ['-xzf', archive, '--strip-components=1', '--no-same-owner', '-C', packageRoot]);
  const cachedArchive = path.join(f.output, 'cache/npm', archiveSuffix);
  mkdirSync(path.dirname(cachedArchive), { recursive: true });
  copyFileSync(archive, cachedArchive);
  write(path.join(f.output, 'tools/pnpm/package-lock.json'), JSON.stringify({ packages: { 'node_modules/pnpm': { version: '11.20.0', integrity } } }));
  return { packageRoot, cachedArchive };
}

function sourceRegistryLink(f) {
  const id = createHash('sha256').update(f.source).digest('hex').slice(0, 32);
  return path.join(f.output, 'store/v11/projects', id);
}

test('accept an existing pnpm store registry entry for this source', () => {
  const f = fixture('existing-source-registry');
  seedPinnedPnpm(f);
  const link = sourceRegistryLink(f);
  mkdirSync(path.dirname(link), { recursive: true });
  symlinkSync('../../../source', link);
  const result = run(f);
  assert.match(result.stderr, /install failed: status=77/);
  assert.equal(realpathSync(link), f.source);
  const commands = readFileSync(f.trace, 'utf8').trimEnd().split('\n').map((line) => JSON.parse(line));
  assert.equal(commands.length, 1);
  assert(commands[0].args.some((argument) => argument.startsWith('--unit=ts-rust-effect-install-')));
  assert.deepEqual(readdirSync(f.outside), []);
});

test('accept a pnpm store registry entry created by the install stub', () => {
  const f = fixture('post-install-source-registry');
  seedPinnedPnpm(f);
  const link = sourceRegistryLink(f);
  const installStub = path.join(f.bin, 'systemd-run');
  write(installStub, `#!/usr/bin/env node
const fs = require('node:fs');
const args = process.argv.slice(2);
if (!args.some((argument) => argument.startsWith('--unit=ts-rust-effect-install-'))) throw new Error('Unexpected command');
fs.appendFileSync(${JSON.stringify(f.trace)}, JSON.stringify({ executable: 'systemd-run', args }) + '\\n');
fs.mkdirSync(${JSON.stringify(path.dirname(link))}, { recursive: true });
fs.symlinkSync('../../../source', ${JSON.stringify(link)});
`);
  chmodSync(installStub, 0o755);
  const result = run(f);
  // The fixture reader is intentionally fake. Reaching it proves the post-install checks passed.
  assert.match(result.stderr, /Config reader changed/);
  assert.equal(realpathSync(link), f.source);
  assert(existsSync(path.join(f.output, 'evidence/source-after.json')));
  const commands = JSON.parse(readFileSync(path.join(f.output, 'evidence/commands.json'), 'utf8'));
  assert.equal(commands.at(-1).name, 'install');
  assert.equal(commands.at(-1).status, 0);
  assert.deepEqual(readdirSync(f.outside), []);
});

test('reject another pnpm store registry name even when it targets this source', () => {
  const f = fixture('wrong-source-registry-id');
  const expected = sourceRegistryLink(f);
  const id = path.basename(expected);
  const wrongId = `${id[0] === '0' ? '1' : '0'}${id.slice(1)}`;
  mkdirSync(path.dirname(expected), { recursive: true });
  symlinkSync('../../../source', path.join(path.dirname(expected), wrongId));
  rejected(f);
});

for (const boundary of ['internal', 'external']) {
  test(`reject a pnpm store registry entry with a different ${boundary} target`, () => {
    const f = fixture(`wrong-source-registry-${boundary}`);
    const link = sourceRegistryLink(f);
    const target = boundary === 'internal' ? path.join(f.source, 'other-source') : f.outside;
    mkdirSync(target, { recursive: true });
    mkdirSync(path.dirname(link), { recursive: true });
    symlinkSync(target, link);
    rejected(f);
  });
}

for (const filename of ['bin/pnpm.mjs', 'dist/pnpm.mjs', 'dist/worker.js']) {
  test(`reject changed pnpm ${filename} beside its valid pinned archive`, () => {
    const f = fixture(`changed-pnpm-${filename.replaceAll('/', '-')}`);
    const { packageRoot } = seedPinnedPnpm(f);
    const marker = path.join(f.outside, 'executed');
    write(path.join(packageRoot, filename), `import { writeFileSync } from 'node:fs'; writeFileSync(${JSON.stringify(marker)}, 'executed'); console.log('11.20.0');\n`);
    rejected(f, /Installed pnpm files differ from the pinned archive/);
    assert(!existsSync(marker));
  });
}

test('reject a changed pinned archive before any pnpm execution', () => {
  const f = fixture('changed-archive');
  const { cachedArchive } = seedPinnedPnpm(f);
  write(cachedArchive, 'changed\n');
  rejected(f, /pnpm archive changed/);
});

test('accept the pinned package and internal links, then stop at the install stub', () => {
  const f = fixture('valid-pinned-package');
  const { packageRoot } = seedPinnedPnpm(f);
  const bin = path.join(f.output, 'tools/pnpm/node_modules/.bin');
  mkdirSync(bin);
  for (const name of ['pn', 'pnpm', 'pnx', 'pnpx']) {
    const target = path.join(packageRoot, 'bin', ['pn', 'pnpm'].includes(name) ? 'pnpm.mjs' : 'pnpx.mjs');
    symlinkSync(path.relative(bin, target), path.join(bin, name));
  }
  mkdirSync(path.join(f.source, 'node_modules'));
  mkdirSync(path.join(f.source, 'packages/peer'), { recursive: true });
  symlinkSync('../packages/peer', path.join(f.source, 'node_modules/peer'));
  const result = run(f);
  assert.match(result.stderr, /install failed: status=77/);
  const commands = readFileSync(f.trace, 'utf8').trimEnd().split('\n').map((line) => JSON.parse(line));
  assert.equal(commands.length, 1);
  assert.equal(commands[0].executable, 'systemd-run');
  assert(commands[0].args.some((argument) => argument.startsWith('--unit=ts-rust-effect-install-')));
  assert.deepEqual(readdirSync(f.outside), []);
});
