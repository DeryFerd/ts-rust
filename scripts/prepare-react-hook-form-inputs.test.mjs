import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import test from 'node:test';
import {
  assertManagedPaths,
  main,
  toolPins,
  toolTreeDigest,
  verifyExtractedTools,
  verifyToolEntryLinks,
  writeDestination,
} from './prepare-react-hook-form-inputs.mjs';

function fixture(t) {
  const root = fs.mkdtempSync(path.join(tmpdir(), 'rhf-input-safety-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const workspace = path.join(root, 'workspace');
  const output = path.join(workspace, 'target/project-inputs/react-hook-form');
  const outside = path.join(root, 'outside');
  fs.mkdirSync(workspace);
  fs.mkdirSync(outside);
  fs.writeFileSync(path.join(outside, 'sentinel'), 'unchanged');
  return { root, workspace, output, outside };
}

function unchangedOutside(outside) {
  assert.deepEqual(fs.readdirSync(outside), ['sentinel']);
  assert.equal(fs.readFileSync(path.join(outside, 'sentinel'), 'utf8'), 'unchanged');
}

test('invalid or extra stage arguments reject before initialization', async (t) => {
  const { workspace, outside } = fixture(t);
  for (const args of [[], ['invalid'], ['snapshot', 'extra']]) {
    await assert.rejects(main(args, { workspace }), /Use one of/);
  }
  assert.equal(fs.existsSync(path.join(workspace, 'target')), false);
  unchangedOutside(outside);
});

const inputPath = 'target/project-inputs/react-hook-form';
for (const destination of [
  'target',
  'target/project-inputs',
  inputPath,
  ...[
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
    'pnpm-store',
    'source',
    'source/app',
    'source/dist',
    'source/node_modules',
    'source/app/node_modules',
  ].map((name) => `${inputPath}/${name}`),
]) {
  test(`rejects directory symlink before initialization: ${destination}`, async (t) => {
    const { workspace, output, outside } = fixture(t);
    const link = path.join(workspace, destination);
    fs.mkdirSync(path.dirname(link), { recursive: true });
    fs.symlinkSync(outside, link);
    await assert.rejects(main(['tools'], { workspace }), /Symlink at managed destination/);
    unchangedOutside(outside);
    if (destination.endsWith('/tmp')) assert.equal(fs.existsSync(path.join(output, 'logs')), false);
  });
}

for (const destination of [
  'config/npmrc',
  'source.tar',
  'evidence/commands.json',
  'evidence/summary.json',
  'logs/install-root.log',
  'tools/pnpm-registry.json',
]) {
  for (const dangling of [false, true]) {
    test(`rejects ${dangling ? 'dangling' : 'existing'} file link: ${destination}`, async (t) => {
      const { workspace, output, outside } = fixture(t);
      const link = path.join(output, destination);
      const victim = path.join(outside, dangling ? 'not-created' : 'sentinel');
      fs.mkdirSync(path.dirname(link), { recursive: true });
      fs.symlinkSync(victim, link);
      await assert.rejects(main(['tools'], { workspace }), /Symlink at managed destination/);
      unchangedOutside(outside);
    });
  }
}

test('write guard rejects a link added after path validation', (t) => {
  const { output, outside } = fixture(t);
  fs.mkdirSync(path.join(output, 'evidence'), { recursive: true });
  assertManagedPaths(output);
  const target = path.join(output, 'evidence/summary.json');
  fs.symlinkSync(path.join(outside, 'sentinel'), target);
  assert.throws(
    () => writeDestination(output, target, 'changed'),
    /Symlink at managed destination/,
  );
  unchangedOutside(outside);
});

test('write guard rejects external hard links without truncation', (t) => {
  const { output, outside } = fixture(t);
  fs.mkdirSync(path.join(output, 'config'), { recursive: true });
  const target = path.join(output, 'config/npmrc');
  fs.linkSync(path.join(outside, 'sentinel'), target);
  assert.throws(() => assertManagedPaths(output), /Hard link leaves the input directory/);
  assert.throws(() => writeDestination(output, target, ''), /Shared file at managed destination/);
  unchangedOutside(outside);
});

test('ordinary writes and contained dependency links remain valid', (t) => {
  const { output, outside } = fixture(t);
  const packageRoot = path.join(output, 'source/node_modules/.pnpm/example/node_modules/example');
  fs.mkdirSync(packageRoot, { recursive: true });
  fs.mkdirSync(path.join(output, 'evidence'));
  fs.mkdirSync(path.join(output, 'pnpm-store/v11/projects'), { recursive: true });
  fs.writeFileSync(path.join(packageRoot, 'package.json'), '{}');
  fs.symlinkSync(
    '.pnpm/example/node_modules/example',
    path.join(output, 'source/node_modules/example'),
  );
  fs.symlinkSync('../../../source', path.join(output, 'pnpm-store/v11/projects/abc123'));
  fs.linkSync(
    path.join(packageRoot, 'package.json'),
    path.join(output, 'source/copied-package.json'),
  );
  assertManagedPaths(output);
  const result = path.join(output, 'evidence/result.json');
  writeDestination(output, result, 'long initial value');
  writeDestination(output, result, '{}\n');
  assert.equal(fs.readFileSync(result, 'utf8'), '{}\n');
  unchangedOutside(outside);
});

test('dependency links cannot leave the prepared directory', (t) => {
  const { output, outside } = fixture(t);
  fs.mkdirSync(path.join(output, 'source/node_modules'), { recursive: true });
  fs.symlinkSync(outside, path.join(output, 'source/node_modules/example'));
  assert.throws(() => assertManagedPaths(output), /Symlink leaves the input directory/);
  unchangedOutside(outside);
});

test('a regular file cannot replace the pnpm entry link', (t) => {
  const { output, outside } = fixture(t);
  fs.mkdirSync(path.join(output, 'tools/bin'), { recursive: true });
  fs.writeFileSync(path.join(output, 'tools/bin/pnpm'), '#!/bin/sh\nprintf 11.7.0');
  assert.throws(() => assertManagedPaths(output), /Expected a tool link/);
  unchangedOutside(outside);
});

test('missing pinned command links cannot fall through to global tools', (t) => {
  const { output, outside } = fixture(t);
  assert.throws(() => verifyToolEntryLinks(output), /Missing tool link/);
  unchangedOutside(outside);
});

function fakeCommand(directory, name, marker, result = '') {
  fs.mkdirSync(directory, { recursive: true });
  const filename = path.join(directory, name);
  fs.writeFileSync(
    filename,
    `#!/bin/sh\nprintf executed > ${JSON.stringify(marker)}\nprintf '%s\\n' ${JSON.stringify(result)}\n`,
    { mode: 0o755 },
  );
  return filename;
}

test('an unverified tools/bin tar is rejected without execution', async (t) => {
  const { workspace, output, outside } = fixture(t);
  fakeCommand(path.join(output, 'tools/bin'), 'tar', path.join(outside, 'executed'));
  await assert.rejects(main(['tools'], { workspace }), /Unexpected tool command/);
  unchangedOutside(outside);
});

test('bootstrap Git ignores an untrusted inherited PATH', (t) => {
  const { root, workspace, output, outside } = fixture(t);
  const fakeBin = path.join(root, 'fake-bin');
  fakeCommand(fakeBin, 'git', path.join(outside, 'executed'), path.join(workspace, '.git'));
  const env = {
    PATH: '/usr/bin:/bin',
    HOME: root,
    TMPDIR: root,
    NODE_DISABLE_COMPILE_CACHE: '1',
    NODE_OPTIONS: '--max-old-space-size=1536',
  };
  execFileSync('/usr/bin/git', ['init', '--quiet', '--template=', workspace], { env });
  const scripts = path.join(workspace, 'scripts');
  fs.mkdirSync(scripts);
  const copiedScript = path.join(scripts, 'prepare-react-hook-form-inputs.mjs');
  fs.writeFileSync(
    copiedScript,
    fs.readFileSync(new URL('./prepare-react-hook-form-inputs.mjs', import.meta.url)),
  );
  fs.mkdirSync(path.join(output, 'config'), { recursive: true });
  fs.symlinkSync(path.join(outside, 'not-created'), path.join(output, 'config/npmrc'));
  const result = spawnSync(process.execPath, [copiedScript, 'snapshot'], {
    env: { ...env, PATH: `${fakeBin}:/usr/bin:/bin` },
    encoding: 'utf8',
  });
  assert.equal(result.status, 1);
  assert.match(result.stderr, /Symlink at managed destination/);
  unchangedOutside(outside);
});

const archiveDirectory = process.env.RHF_TOOL_ARCHIVES;
function seedArchives(output) {
  const tools = path.join(output, 'tools');
  fs.mkdirSync(tools, { recursive: true });
  for (const pin of toolPins) {
    const bytes = fs.readFileSync(path.join(archiveDirectory, pin.archive));
    assert.equal(createHash('sha256').update(bytes).digest('hex'), pin.archiveSha256);
    fs.writeFileSync(path.join(tools, pin.archive), bytes);
  }
  fs.writeFileSync(
    path.join(tools, 'node-SHASUMS256.txt'),
    `${toolPins[0].archiveSha256}  ${toolPins[0].archive}\n`,
  );
  const pnpmBytes = fs.readFileSync(path.join(tools, toolPins[1].archive));
  fs.writeFileSync(
    path.join(tools, 'pnpm-registry.json'),
    JSON.stringify({
      version: '11.7.0',
      dist: {
        tarball: 'https://registry.npmjs.org/pnpm/-/pnpm-11.7.0.tgz',
        integrity: `sha512-${createHash('sha512').update(pnpmBytes).digest('base64')}`,
      },
    }),
  );
  return tools;
}

test(
  'bootstrap extraction ignores commands in a partial Node directory',
  {
    skip: archiveDirectory ? false : 'Set RHF_TOOL_ARCHIVES to the downloaded pinned archives.',
  },
  async (t) => {
    const { workspace, output, outside } = fixture(t);
    const tools = seedArchives(output);
    const partialBin = path.join(tools, toolPins[0].directory, 'bin');
    for (const command of ['tar', 'gzip', 'xz', 'git']) {
      fakeCommand(partialBin, command, path.join(outside, 'executed'));
    }
    await assert.rejects(main(['tools'], { workspace }), /Changed extracted tool/);
    const commands = JSON.parse(
      fs.readFileSync(path.join(output, 'evidence/commands.json'), 'utf8'),
    );
    assert.equal(commands.length, 1);
    assert.equal(commands[0].name, 'pnpm-extract');
    assert.equal(commands[0].executable, '/usr/bin/tar');
    assert.equal(commands[0].status, 0);
    assert.equal(commands[0].environment.path, '/usr/bin:/bin');
    unchangedOutside(outside);
  },
);

test(
  'pinned archive contents reject tool tampering before execution',
  {
    skip: archiveDirectory ? false : 'Set RHF_TOOL_ARCHIVES to the downloaded pinned archives.',
  },
  async (t) => {
    const { workspace, output, outside } = fixture(t);
    const tools = seedArchives(output);
    for (const pin of toolPins) {
      const archive = path.join(tools, pin.archive);
      const payload = path.join(tools, pin.directory);
      fs.mkdirSync(payload, { mode: 0o755 });
      execFileSync('/usr/bin/tar', ['-xf', archive, '--strip-components=1', '-C', payload]);
      assert.equal(toolTreeDigest(payload), pin.treeSha256);
    }
    verifyExtractedTools(output);

    await t.test('a fake pnpm version response is never executed', async () => {
      const cli = path.join(tools, 'pnpm/bin/pnpm.mjs');
      const original = fs.readFileSync(cli);
      const marker = path.join(outside, 'executed');
      fs.writeFileSync(
        cli,
        `import fs from 'node:fs'; fs.writeFileSync(${JSON.stringify(marker)}, 'executed'); console.log('11.7.0');\n`,
      );
      try {
        await assert.rejects(main(['tools'], { workspace }), /Changed extracted tool/);
        assert.equal(fs.existsSync(path.join(output, 'config')), false);
        unchangedOutside(outside);
      } finally {
        fs.writeFileSync(cli, original);
      }
    });

    await t.test('a changed pnpm bundle is rejected with an unchanged entry point', () => {
      const bundle = path.join(tools, 'pnpm/dist/pnpm.mjs');
      const original = fs.readFileSync(bundle);
      fs.writeFileSync(bundle, "console.log('11.7.0');\n");
      try {
        assert.throws(() => verifyExtractedTools(output), /Changed extracted tool/);
      } finally {
        fs.writeFileSync(bundle, original);
      }
    });

    await t.test('a changed Node binary is rejected', () => {
      const binary = path.join(tools, toolPins[0].directory, 'bin/node');
      const original = fs.readFileSync(binary);
      fs.writeFileSync(binary, '#!/bin/sh\nprintf v22.22.0');
      try {
        assert.throws(() => verifyExtractedTools(output), /Changed extracted tool/);
      } finally {
        fs.writeFileSync(binary, original);
      }
    });

    await t.test('extra payload files are rejected', () => {
      const extra = path.join(tools, 'pnpm/extra.cjs');
      fs.writeFileSync(extra, 'unexpected');
      try {
        assert.throws(() => verifyExtractedTools(output), /Changed extracted tool/);
      } finally {
        fs.unlinkSync(extra);
      }
    });
    await t.test('a changed archive is rejected even when extracted files are intact', () => {
      const archive = path.join(tools, toolPins[1].archive);
      const original = fs.readFileSync(archive);
      const changed = Buffer.from(original);
      changed[0] ^= 1;
      fs.writeFileSync(archive, changed);
      try {
        assert.throws(() => verifyExtractedTools(output), /Changed tool archive/);
      } finally {
        fs.writeFileSync(archive, original);
      }
    });
    await t.test(
      'authenticated Node tools replace an inherited outside compile cache',
      async () => {
        const oldCache = process.env.NODE_COMPILE_CACHE;
        const oldDisable = process.env.NODE_DISABLE_COMPILE_CACHE;
        process.env.NODE_COMPILE_CACHE = path.join(outside, 'compile-cache');
        delete process.env.NODE_DISABLE_COMPILE_CACHE;
        try {
          await main(['tools'], { workspace });
          unchangedOutside(outside);
          const privateCache = path.join(output, 'cache/node-compile');
          assert(
            fs.readdirSync(privateCache).length > 0,
            'Node must use the checked private cache.',
          );
          const metadata = JSON.parse(
            fs.readFileSync(path.join(output, 'evidence/tools.json'), 'utf8'),
          );
          assert.equal(metadata.nodeCompileCache, privateCache);
          assertManagedPaths(output);
        } finally {
          if (oldCache === undefined) delete process.env.NODE_COMPILE_CACHE;
          else process.env.NODE_COMPILE_CACHE = oldCache;
          if (oldDisable === undefined) delete process.env.NODE_DISABLE_COMPILE_CACHE;
          else process.env.NODE_DISABLE_COMPILE_CACHE = oldDisable;
        }
      },
    );
    verifyExtractedTools(output);
    unchangedOutside(outside);
  },
);
