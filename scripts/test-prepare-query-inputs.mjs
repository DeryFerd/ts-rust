#!/usr/bin/node

import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import fs from 'node:fs'
import os from 'node:os'
import path from 'node:path'
import { after, before, test } from 'node:test'
import { fileURLToPath } from 'node:url'

const script = fileURLToPath(new URL('./prepare-query-inputs.mjs', import.meta.url))
const archives = process.env.QUERY_INPUTS_TEST_ARCHIVES
const sourceCache = process.env.QUERY_INPUTS_TEST_SOURCE
assert(archives && sourceCache, 'Set QUERY_INPUTS_TEST_ARCHIVES and QUERY_INPUTS_TEST_SOURCE')
assert.equal(fs.realpathSync(archives), archives)
assert.equal(fs.realpathSync(sourceCache), sourceCache)
const nodeArchive = 'node-v24.16.0-linux-x64.tar.xz'
const pnpmArchive = 'pnpm-11.9.0.tgz'
const nodeDirectory = 'tools/node-v24.16.0-linux-x64'
const pnpmDirectory = 'tools/pnpm-11.9.0/package'
const digest = (bytes) => createHash('sha256').update(bytes).digest('hex')
const fileHash = (file) => digest(fs.readFileSync(file))
const environment = {
  PATH: '/usr/bin:/bin',
  GIT_CONFIG_GLOBAL: '/dev/null',
  GIT_CONFIG_NOSYSTEM: '1',
  GIT_OPTIONAL_LOCKS: '0',
  GIT_TERMINAL_PROMPT: '0',
}
function git(directory, ...args) {
  const result = spawnSync('/usr/bin/git', [
    '-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false', ...args,
  ], { cwd: directory, env: environment, encoding: 'utf8' })
  assert.equal(result.status, 0, result.stderr)
  return result.stdout.trim()
}
function preparedSnapshot() {
  const output = path.dirname(archives)
  const metadata = path.join(output, 'metadata')
  const files = fs.readdirSync(metadata).map((name) => path.join(metadata, name))
  const generated = JSON.parse(fs.readFileSync(path.join(metadata, 'generated.json'), 'utf8'))
  for (const entry of generated) files.push(path.join(output, 'source', entry.path))
  files.push(path.join(archives, nodeArchive), path.join(archives, pnpmArchive))
  return {
    files: files.map((file) => [file, fileHash(file)]),
    sourceHead: git(path.join(output, 'source'), 'rev-parse', 'HEAD'),
    sourceStatus: git(path.join(output, 'source'), 'status', '--porcelain=v1', '--untracked-files=all'),
    cacheHead: git(sourceCache, 'rev-parse', 'HEAD'),
    cacheStatus: git(sourceCache, 'status', '--porcelain=v1', '--untracked-files=all'),
  }
}
const initial = preparedSnapshot()
assert.equal(fileHash(path.join(archives, nodeArchive)), 'd804845d34eddc21dc1092b519d643ef40b1f58ec5dec5c22b1f4bd8fabde6c9')
assert.equal(fileHash(path.join(archives, pnpmArchive)), '2b567aa66026238078ac2e0a33bec3febd60e962987aac697456f3180819b287')
const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'query-input-security-'))
let baseline
function write(file, bytes, mode = 0o600) {
  fs.mkdirSync(path.dirname(file), { recursive: true })
  fs.writeFileSync(file, bytes, { mode })
}
function fixture(name, tools = false) {
  const root = fs.mkdtempSync(path.join(temporary, `${name}-`))
  const main = path.join(root, 'main')
  fs.mkdirSync(path.join(main, 'scripts'), { recursive: true })
  git(main, 'init', '--quiet')
  const entry = path.join(main, 'scripts/prepare-query-inputs.mjs')
  fs.copyFileSync(script, entry)
  const output = path.join(main, 'target/project-inputs/query')
  const commands = path.join(root, 'commands')
  const marker = path.join(root, 'untrusted-command-ran')
  for (const command of ['git', 'tar', 'curl', 'xz', 'gzip', 'env', 'systemd-run'])
    write(path.join(commands, command), `#!/bin/sh\nprintf bad >> '${marker}'\nexit 97\n`, 0o755)
  if (tools) {
    fs.mkdirSync(path.join(output, 'downloads'), { recursive: true })
    for (const archive of [nodeArchive, pnpmArchive])
      fs.copyFileSync(path.join(archives, archive), path.join(output, 'downloads', archive), fs.constants.COPYFILE_FICLONE)
    write(path.join(output, 'downloads/pnpm-11.9.0.json'), JSON.stringify({
      name: 'pnpm', version: '11.9.0', dist: {
        tarball: 'https://registry.npmjs.org/pnpm/-/pnpm-11.9.0.tgz',
        integrity: 'sha512-vWgtXQP+Ul73yf1ngMaITR51asTJyf4AxTh4KCQxDc+Q493E9Tg18G3669UIXkGFXgvLs7YN4qxburieUDbwOw==',
      },
    }))
    if (baseline) fs.cpSync(path.join(baseline.output, 'tools'), path.join(output, 'tools'), {
      recursive: true, verbatimSymlinks: true, mode: fs.constants.COPYFILE_FICLONE,
    })
  }
  return { root, main, entry, output, commands, marker }
}
function run(fixture, stage = 'tools', executable = '/usr/bin/node') {
  const preload = fixture.stopInstallHook ? ['--import', fixture.stopInstallHook] : []
  const result = spawnSync(executable, [...preload, fixture.entry, stage], {
    cwd: fixture.main,
    env: {
      PATH: fixture.commands,
      HOME: path.join(fixture.root, 'wrong-home'),
      GIT_DIR: path.join(fixture.root, 'wrong-git'),
      NODE_PATH: path.join(fixture.root, 'wrong-modules'),
      QUERY_INPUTS_SCOPED: '1',
      QUERY_REPO_CACHE: fixture.cache ?? path.join(fixture.root, 'unused-cache'),
    },
    encoding: 'utf8',
    timeout: 90_000,
    maxBuffer: 4 * 1024 * 1024,
  })
  assert.ifError(result.error)
  assert(!fs.existsSync(fixture.marker), 'An untrusted bootstrap command ran')
  return result
}
function rejects(fixture, pattern, stage = 'tools', executable) {
  const result = run(fixture, stage, executable)
  assert.notEqual(result.status, 0, result.stdout)
  assert.match(result.stderr, pattern)
  return result
}
before(() => {
  baseline = fixture('fresh-tools', true)
  const result = run(baseline)
  assert.equal(result.status, 0, result.stderr)
  const state = JSON.parse(fs.readFileSync(path.join(baseline.output, 'metadata/state.json'), 'utf8'))
  assert.equal(state.tools.node.version, '24.16.0')
  assert.equal(state.tools.pnpm.version, '11.9.0')
})
after(() => {
  try {
    assert.deepEqual(preparedSnapshot(), initial, 'The actual prepared Query inputs or cache changed')
  } finally {
    fs.rmSync(temporary, { recursive: true, force: true })
  }
})

test('ancestor symlinks fail before creating any escaped directory', () => {
  for (const relative of ['target', 'target/project-inputs', 'target/project-inputs/query']) {
    const item = fixture('ancestor')
    const outside = path.join(item.root, 'outside')
    fs.mkdirSync(outside)
    const link = path.join(item.main, relative)
    fs.mkdirSync(path.dirname(link), { recursive: true })
    fs.symlinkSync(outside, link)
    rejects(item, /Symlink in managed path/)
    assert.deepEqual(fs.readdirSync(outside), [])
  }
})

test('managed directories and private environment paths reject redirects before writes', () => {
  for (const relative of [
    'metadata', 'downloads', 'tools', 'tools/bin', 'logs', 'tmp', 'home', 'cache',
    'cache/npm', 'cache/pnpm', 'cache/nx', 'cache/nx-workspace', 'config', 'data',
    'pnpm-home', 'pnpm-store',
  ]) {
    const item = fixture('managed-directory')
    const outside = path.join(item.root, 'outside')
    fs.mkdirSync(outside)
    const link = path.join(item.output, relative)
    fs.mkdirSync(path.dirname(link), { recursive: true })
    fs.symlinkSync(outside, link)
    rejects(item, /Symlink in managed path/)
    assert.deepEqual(fs.readdirSync(outside), [])
  }
})

test('managed file symlinks and hard links cannot redirect state, logs, or downloads', () => {
  for (const relative of [
    'metadata/state.json', 'metadata/commands.ndjson', 'logs/001-git.log',
    `downloads/${nodeArchive}`, `downloads/${nodeArchive}.part`,
  ]) {
    for (const hardLink of [false, true]) {
      const item = fixture('managed-file')
      const outside = path.join(item.root, 'outside')
      write(outside, 'unchanged\n')
      const file = path.join(item.output, relative)
      fs.mkdirSync(path.dirname(file), { recursive: true })
      if (hardLink) fs.linkSync(outside, file)
      else fs.symlinkSync(outside, file)
      rejects(item, /(?:Symlink|Hard link) in/)
      assert.equal(fs.readFileSync(outside, 'utf8'), 'unchanged\n')
    }
  }
})

test('complete verified tools can be reused without commands from inherited PATH', () => {
  const item = fixture('verified-reuse', true)
  const result = run(item)
  assert.equal(result.status, 0, result.stderr)
})

test('source preparation creates an independent pinned copy', () => {
  const item = fixture('source-copy')
  item.cache = sourceCache
  const result = run(item, 'source')
  assert.equal(result.status, 0, result.stderr)
  const state = JSON.parse(fs.readFileSync(path.join(item.output, 'metadata/state.json'), 'utf8'))
  assert.equal(state.pin, initial.cacheHead)
  assert.equal(state.sourceManifest.entries, 2373)
  assert.equal(state.sourceManifest.sha256,
    'a676eb6dc8968e34a1caf928b48b3cae21c98d11429d096c7e5ecdd5f3b595b0')
  assert(!fs.existsSync(path.join(item.output, 'source/.git/objects/info/alternates')))
})

test('the package-store project link must resolve to this prepared source', () => {
  for (const outside of [false, true]) {
    const item = fixture('store-project', !outside)
    const source = path.join(item.output, 'source')
    const destination = outside ? path.join(item.root, 'outside') : source
    fs.mkdirSync(destination, { recursive: true })
    const projects = path.join(item.output, 'pnpm-store/v11/projects')
    fs.mkdirSync(projects, { recursive: true })
    fs.symlinkSync(path.relative(projects, destination), path.join(projects, 'workspace'))
    if (outside) {
      rejects(item, /Symlink in private directory/)
      assert.deepEqual(fs.readdirSync(destination), [])
    } else {
      const result = run(item)
      assert.equal(result.status, 0, result.stderr)
    }
  }
})

test('version-spoofing Node never runs during preparation or stage handoff', () => {
  for (const stage of ['tools', 'install', 'build', 'inventory', 'replay']) {
    const item = fixture('fake-node', true)
    const marker = path.join(item.root, 'fake-node-ran')
    write(path.join(item.output, nodeDirectory, 'bin/node'),
      `#!/bin/sh\nprintf bad >> '${marker}'\nprintf 'v24.16.0\\n'\n`, 0o755)
    rejects(item, /Tool (?:size|bytes) differs/, stage)
    assert(!fs.existsSync(marker))
  }
})

test('pnpm bundle changes fail even when its entry file is unchanged', () => {
  const item = fixture('fake-pnpm', true)
  const entry = path.join(item.output, pnpmDirectory, 'bin/pnpm.mjs')
  const before = fileHash(entry)
  const marker = path.join(item.root, 'fake-pnpm-ran')
  write(path.join(item.output, pnpmDirectory, 'dist/pnpm.mjs'),
    `import fs from 'node:fs'; fs.writeFileSync(${JSON.stringify(marker)}, 'bad'); console.log('11.9.0');\n`)
  assert.equal(fileHash(entry), before)
  rejects(item, /Tool (?:size|bytes) differs/)
  assert(!fs.existsSync(marker))
})

test('tool file lists, modes, and symlink targets must match the complete archives', () => {
  for (const change of ['extra-file', 'mode', 'symlink', 'nested-node-code']) {
    const item = fixture('tool-tree', true)
    if (change === 'extra-file') write(path.join(item.output, pnpmDirectory, 'dist/injected.mjs'), 'bad\n')
    if (change === 'mode') fs.chmodSync(path.join(item.output, nodeDirectory, 'bin/node'), 0o700)
    if (change === 'symlink') {
      const file = path.join(item.output, nodeDirectory, 'bin/npm')
      fs.unlinkSync(file)
      fs.symlinkSync('/usr/bin/false', file)
    }
    if (change === 'nested-node-code')
      fs.appendFileSync(path.join(item.output, nodeDirectory, 'lib/node_modules/npm/bin/npm-cli.js'), '\n// changed\n')
    rejects(item, /Tool (?:file list|mode|symlink|size|bytes) differs/)
  }
})

test('changed archives fail before extraction or tool execution', () => {
  const item = fixture('archive', true)
  fs.appendFileSync(path.join(item.output, 'downloads', nodeArchive), 'bad')
  rejects(item, /integrity mismatch/)
})

test('install verifies cached pnpm before its version check under the pinned Node', () => {
  const item = fixture('require-tools', true)
  git(item.main, 'clone', '--quiet', '--no-hardlinks', sourceCache, path.join(item.output, 'source'))
  git(path.join(item.output, 'source'), 'checkout', '--quiet', '--detach', initial.cacheHead)
  const marker = path.join(item.root, 'fake-pnpm-ran')
  write(path.join(item.output, pnpmDirectory, 'dist/pnpm.mjs'),
    `import fs from 'node:fs'; fs.writeFileSync(${JSON.stringify(marker)}, 'bad'); console.log('11.9.0');\n`)
  rejects(item, /Tool (?:size|bytes) differs/, 'install', path.join(item.output, nodeDirectory, 'bin/node'))
  assert(!fs.existsSync(marker))
})

function installFixture(name) {
  const item = fixture(name, true)
  item.source = path.join(item.output, 'source')
  git(item.main, 'clone', '--quiet', '--no-hardlinks', sourceCache, item.source)
  git(item.source, 'checkout', '--quiet', '--detach', initial.cacheHead)
  item.stoppedInstall = path.join(item.root, 'stopped-install.json')
  item.stopInstallHook = path.join(item.root, 'stop-installer.mjs')
  write(item.stopInstallHook, `
import childProcess from 'node:child_process'
import { syncBuiltinESMExports } from 'node:module'
import fs from 'node:fs'
const original = childProcess.spawnSync
childProcess.spawnSync = function(command, args, options) {
  if (args.includes('install') || args.includes('run')) {
    fs.writeFileSync(${JSON.stringify(item.stoppedInstall)}, JSON.stringify({ command, args }))
    return { status: 86, signal: null, stdout: '', stderr: 'Installer stopped by the test' }
  }
  return original.call(childProcess, command, args, options)
}
syncBuiltinESMExports()
`)
  return item
}

function checkInstallDispatch(item, expected) {
  assert.equal(git(item.source, 'status', '--porcelain=v1', '--untracked-files=all'), '')
  const node = path.join(item.output, nodeDirectory, 'bin/node')
  const result = run(item, 'install', node)
  assert.equal(result.status, 1, result.stdout)
  assert.equal(fs.existsSync(item.stoppedInstall), expected, result.stderr)
  if (expected) {
    const call = JSON.parse(fs.readFileSync(item.stoppedInstall, 'utf8'))
    assert.equal(call.command, node)
    assert.equal(call.args[0], path.join(item.output, pnpmDirectory, 'bin/pnpm.mjs'))
    assert.equal(call.args[1], 'install')
    assert(call.args.includes('--frozen-lockfile') && call.args.includes('--ignore-scripts'))
    assert.equal(call.args[call.args.indexOf('--store-dir') + 1], path.join(item.output, 'pnpm-store'))
  } else assert.match(result.stderr, /Path leaves|Unsafe pnpm write file/)
  assert.equal(git(item.source, 'status', '--porcelain=v1', '--untracked-files=all'), '')
}

test('a clean install reaches the interceptor without executing an installer', () => {
  checkInstallDispatch(installFixture('install-control'), true)
})

test('ignored install roots cannot redirect pnpm outside the prepared output', () => {
  for (const relative of [
    'node_modules',
    'packages/query-core/node_modules',
    'integrations/react-nodenext/node_modules',
    'node_modules/.pnpm',
  ]) {
    const item = installFixture('install-root')
    const outside = path.join(item.root, 'outside')
    fs.mkdirSync(outside)
    const link = path.join(item.source, relative)
    fs.mkdirSync(path.dirname(link), { recursive: true })
    fs.symlinkSync(outside, link)
    checkInstallDispatch(item, false)
    assert.deepEqual(fs.readdirSync(outside), [])
  }
})

test('pnpm write files reject symlinks and hard links before install dispatch', () => {
  for (const relative of [
    'node_modules/.modules.yaml',
    'packages/query-core/node_modules/.modules.yaml',
    'integrations/react-nodenext/node_modules/.modules.yaml',
    'node_modules/.pnpm-workspace-state-v1.json',
    'node_modules/.pnpm/lock.yaml',
    'node_modules/.bin/tsc',
  ]) {
    for (const hardLink of [false, true]) {
      const item = installFixture('install-file')
      const outside = path.join(item.root, 'outside')
      write(outside, 'unchanged\n')
      const file = path.join(item.source, relative)
      fs.mkdirSync(path.dirname(file), { recursive: true })
      if (hardLink) fs.linkSync(outside, file)
      else fs.symlinkSync(outside, file)
      checkInstallDispatch(item, false)
      assert.equal(fs.readFileSync(outside, 'utf8'), 'unchanged\n')
    }
  }
})

test('pnpm layout files cannot select an outside virtual or package store', () => {
  for (const key of ['virtualStoreDir', 'storeDir']) {
    const item = installFixture('install-layout')
    const outside = path.join(item.root, 'outside')
    fs.mkdirSync(outside)
    write(path.join(item.source, 'node_modules/.modules.yaml'), JSON.stringify({ [key]: outside }))
    checkInstallDispatch(item, false)
    assert.deepEqual(fs.readdirSync(outside), [])
  }
})

test('internal bin aliases cannot hide hard-linked write files', () => {
  for (const directoryAlias of [false, true]) {
    const item = installFixture('install-bin-alias')
    const outside = path.join(item.root, 'outside')
    write(outside, 'unchanged\n')
    const modules = path.join(item.source, 'node_modules')
    const shared = path.join(modules, 'shared-bins')
    fs.mkdirSync(shared, { recursive: true })
    fs.linkSync(outside, path.join(shared, 'tool'))
    if (directoryAlias) fs.symlinkSync('shared-bins', path.join(modules, '.bin'))
    else {
      fs.mkdirSync(path.join(modules, '.bin'))
      fs.symlinkSync('../shared-bins/tool', path.join(modules, '.bin/tool'))
    }
    checkInstallDispatch(item, false)
    assert.equal(fs.readFileSync(outside, 'utf8'), 'unchanged\n')
  }
})

test('internal module aliases, workspace links, and bin links remain valid', () => {
  const item = installFixture('install-internal-links')
  const modules = path.join(item.source, 'node_modules')
  fs.mkdirSync(path.join(modules, '@tanstack'), { recursive: true })
  fs.symlinkSync('../../packages/query-core', path.join(modules, '@tanstack/query-core'))
  fs.mkdirSync(path.join(modules, '.bin'))
  fs.symlinkSync('../@tanstack/query-core/package.json', path.join(modules, '.bin/internal'))
  for (const project of ['packages/query-core', 'integrations/react-nodenext']) {
    const directory = path.join(item.source, project)
    fs.symlinkSync(path.relative(directory, modules), path.join(directory, 'node_modules'))
  }
  checkInstallDispatch(item, true)
})

test('the current prepared package layout passes install preflight after relocation', () => {
  const item = installFixture('install-current-layout')
  const original = path.dirname(archives)
  const originalSource = path.join(original, 'source')
  fs.cpSync(originalSource, item.source, {
    recursive: true,
    verbatimSymlinks: true,
    mode: fs.constants.COPYFILE_FICLONE,
    filter: (file) => path.relative(originalSource, file).split(path.sep)[0] !== '.git',
  })
  function relocate(value) {
    if (typeof value === 'string')
      return value === original || value.startsWith(`${original}/`)
        ? item.output + value.slice(original.length)
        : value
    if (Array.isArray(value)) return value.map(relocate)
    if (value && typeof value === 'object')
      return Object.fromEntries(
        Object.entries(value).map(([key, child]) => [relocate(key), relocate(child)]),
      )
    return value
  }
  function rewriteCopiedLayout(directory) {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      if (entry.name === '.git') continue
      const file = path.join(directory, entry.name)
      if (entry.isDirectory()) rewriteCopiedLayout(file)
      else if (entry.isFile() && path.basename(directory) === 'node_modules' &&
        ['.modules.yaml', '.pnpm-workspace-state-v1.json'].includes(entry.name)) {
        write(file, JSON.stringify(relocate(JSON.parse(fs.readFileSync(file, 'utf8')))))
      }
    }
  }
  rewriteCopiedLayout(item.source)
  checkInstallDispatch(item, true)
})
