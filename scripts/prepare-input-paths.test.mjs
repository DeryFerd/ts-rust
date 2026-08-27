import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

const projects = [
  { name: 'hono', script: 'prepare-hono-inputs.mjs' },
  { name: 'svelte', script: 'prepare-svelte-input.mjs' },
  { name: 'ts-pattern', script: 'prepare-ts-pattern-input.mjs' },
];

function fixture(t, project) {
  const root = fs.mkdtempSync(path.join(tmpdir(), `${project.name}-input-paths-`));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const workspace = path.join(root, 'workspace');
  const output = path.join(workspace, 'target/project-inputs', project.name);
  const cache = path.join(root, 'cache');
  const outside = path.join(root, 'outside');
  const commands = path.join(root, 'commands');
  const trace = path.join(root, 'commands.jsonl');
  for (const directory of [workspace, cache, outside, commands]) {
    fs.mkdirSync(directory, { recursive: true });
  }
  const sentinel = path.join(outside, 'sentinel');
  fs.writeFileSync(sentinel, 'unchanged\n');
  fs.writeFileSync(path.join(cache, 'sentinel'), 'cache unchanged\n');
  const script = path.join(workspace, 'scripts', project.script);
  fs.mkdirSync(path.dirname(script));
  fs.copyFileSync(fileURLToPath(new URL(project.script, import.meta.url)), script);

  // Only repository-root discovery is allowed. Every preparation command stops.
  for (const command of ['git', 'npm', 'pnpm', 'bun', 'corepack', 'curl', 'tar', 'unzip', 'systemd-run']) {
    fs.writeFileSync(path.join(commands, command), `#!${process.execPath}
const fs = require('node:fs');
const args = process.argv.slice(2);
if (${JSON.stringify(command)} === 'git' && args.includes('--git-common-dir')) {
  console.log(${JSON.stringify(path.join(workspace, '.git'))});
} else {
  fs.appendFileSync(${JSON.stringify(trace)}, JSON.stringify(${JSON.stringify(command)}) + '\\n');
  console.error('Blocked fixture command: ${command}');
  process.exit(79);
}
`, { mode: 0o755 });
  }
  return { project, root, workspace, output, cache, outside, sentinel, commands, trace, script };
}

function snapshot(directory) {
  const entries = [];
  function visit(current) {
    for (const name of fs.readdirSync(current).sort()) {
      const filename = path.join(current, name);
      const stat = fs.lstatSync(filename);
      const entry = {
        path: path.relative(directory, filename),
        mode: stat.mode,
        links: stat.nlink,
        modified: stat.mtimeMs,
      };
      if (stat.isSymbolicLink()) entry.target = fs.readlinkSync(filename);
      else if (stat.isFile()) entry.bytes = fs.readFileSync(filename).toString('base64');
      entries.push(entry);
      if (stat.isDirectory()) visit(filename);
    }
  }
  visit(directory);
  return entries;
}

function run(f, { action = 'copy', control = false } = {}) {
  const args = f.project.name === 'hono'
    ? [f.cache, f.output]
    : f.project.name === 'svelte' ? [action] : [f.output];
  const result = spawnSync(process.execPath, [f.script, ...args], {
    cwd: f.workspace,
    env: {
      PATH: `${f.commands}:${path.dirname(process.execPath)}:/usr/bin:/bin`,
      HOME: f.root,
      TMPDIR: f.root,
      NODE_DISABLE_COMPILE_CACHE: '1',
      HONO_PREP_CGROUP_ACTIVE: '1',
      TS_PATTERN_PREP_CGROUP: control ? '0' : '1',
      TS_PATTERN_REPO_CACHE: f.cache,
      SVELTE_REPO: f.cache,
      SVELTE_INPUT_DIR: f.output,
    },
    encoding: 'utf8',
    timeout: 10_000,
  });
  assert.ifError(result.error);
  return result;
}

function link(destination, target) {
  fs.mkdirSync(path.dirname(destination), { recursive: true });
  fs.symlinkSync(target, destination);
}

for (const project of projects) {
  const cases = [
    ['linked output ancestor', (f) => link(path.join(f.workspace, 'target'), f.outside)],
    ['linked managed directory', (f) => link(path.join(f.output, 'evidence'), f.outside)],
    ['linked source archive', (f) => link(path.join(f.output, 'source.tar'), f.sentinel)],
    ['dangling evidence link', (f) => link(path.join(f.output, 'evidence/log'), path.join(f.outside, 'missing'))],
    ['nested managed link', (f) => link(path.join(f.output, 'tmp/nested'), f.outside)],
    ['shared source archive', (f) => {
      fs.mkdirSync(f.output, { recursive: true });
      fs.linkSync(f.sentinel, path.join(f.output, 'source.tar'));
    }],
  ];
  for (const [name, prepare] of cases) {
    test(`${project.name}: ${name} rejects before writes`, (t) => {
      const f = fixture(t, project);
      prepare(f);
      const before = snapshot(f.root);
      const result = run(f);
      assert.notEqual(result.status, 0);
      assert.match(result.stderr, /Unsafe|Shared output file|ENOENT/);
      assert.equal(fs.existsSync(f.trace), false);
      assert.deepEqual(snapshot(f.root), before);
    });
  }

  test(`${project.name}: unsafe source state rejects before writes`, (t) => {
    const f = fixture(t, project);
    if (project.name !== 'svelte') {
      fs.mkdirSync(path.join(f.output, 'source'), { recursive: true });
    }
    const before = snapshot(f.root);
    const result = run(f, { action: 'record' });
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /new output directory|Refusing to replace|Missing generation evidence/);
    assert.equal(fs.existsSync(f.trace), false);
    assert.deepEqual(snapshot(f.root), before);
  });

  test(`${project.name}: ordinary paths reach only a blocked preparation command`, (t) => {
    const f = fixture(t, project);
    const cache = snapshot(f.cache);
    const outside = snapshot(f.outside);
    const result = run(f, { control: true });
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /Blocked fixture command:/);
    const commands = fs.readFileSync(f.trace, 'utf8').trim().split('\n').map((line) => JSON.parse(line));
    assert.deepEqual(commands, [project.name === 'ts-pattern' ? 'systemd-run' : 'git']);
    assert.deepEqual(snapshot(f.cache), cache);
    assert.deepEqual(snapshot(f.outside), outside);
  });
}
