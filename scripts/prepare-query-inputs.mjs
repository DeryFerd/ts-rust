#!/usr/bin/node

import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import fs from 'node:fs'
import path from 'node:path'
import { createRequire } from 'node:module'
import { fileURLToPath } from 'node:url'

const pin = '44645e9eb1dafba5f2f229adb328582075484f36'
const lockSha256 = 'dabc851b54103afd7fb67d00d07663d554c89393c2ffde5254ca539f84d81e71'
const nodeVersion = '24.16.0'
const nodeArchiveSha256 = 'd804845d34eddc21dc1092b519d643ef40b1f58ec5dec5c22b1f4bd8fabde6c9'
const pnpmVersion = '11.9.0'
const pnpmArchiveSha256 = '2b567aa66026238078ac2e0a33bec3febd60e962987aac697456f3180819b287'
const pnpmIntegrity =
  'sha512-vWgtXQP+Ul73yf1ngMaITR51asTJyf4AxTh4KCQxDc+Q493E9Tg18G3669UIXkGFXgvLs7YN4qxburieUDbwOw=='
const script = fileURLToPath(import.meta.url)
const worktree = path.dirname(path.dirname(script))
const stage = process.argv[2] ?? 'all'
const stages = ['source', 'tools', 'install', 'build', 'inventory', 'replay', 'all']
assert(stages.includes(stage), `Usage: node ${script} ${stages.join('|')}`)
assert.equal(process.platform, 'linux')
assert.equal(process.arch, 'x64')

const commands = {
  node: '/usr/bin/node',
  git: '/usr/bin/git',
  curl: '/usr/bin/curl',
  tar: '/usr/bin/tar',
  scope: '/usr/bin/systemd-run',
  env: '/usr/bin/env',
}
const systemPath = '/usr/bin:/bin'
const inherited = Object.fromEntries(
  [
    'XDG_RUNTIME_DIR',
    'DBUS_SESSION_BUS_ADDRESS',
    'SSL_CERT_FILE',
    'SSL_CERT_DIR',
    'HTTP_PROXY',
    'HTTPS_PROXY',
    'ALL_PROXY',
    'NO_PROXY',
    'http_proxy',
    'https_proxy',
    'all_proxy',
    'no_proxy',
  ]
    .filter((key) => process.env[key] !== undefined)
    .map((key) => [key, process.env[key]]),
)
const bootstrapEnv = {
  ...inherited,
  PATH: systemPath,
  GIT_CONFIG_GLOBAL: '/dev/null',
  GIT_CONFIG_NOSYSTEM: '1',
  GIT_OPTIONAL_LOCKS: '0',
  GIT_TERMINAL_PROMPT: '0',
  LANG: 'C.UTF-8',
  LC_ALL: 'C.UTF-8',
  ...(process.env.QUERY_REPO_CACHE === undefined
    ? {}
    : { QUERY_REPO_CACHE: process.env.QUERY_REPO_CACHE }),
}

// The scope covers the coordinator and every process that it starts.
if (process.env.QUERY_INPUTS_SCOPED !== '1') {
  const result = spawnSync(
    commands.scope,
    [
      '--user',
      '--scope',
      '--quiet',
      '--collect',
      '-p',
      'MemoryMax=2147483648',
      '-p',
      'MemorySwapMax=0',
      '-p',
      'TasksMax=128',
      commands.env,
      'QUERY_INPUTS_SCOPED=1',
      commands.node,
      script,
      stage,
    ],
    { stdio: 'inherit', env: bootstrapEnv },
  )
  if (result.error) throw result.error
  process.exit(result.status ?? 1)
}

process.umask(0o077)
function checkPath(file, kind, allowMissing = true) {
  assert(path.isAbsolute(file) && path.normalize(file) === file, `Not a canonical path: ${file}`)
  let current = path.parse(file).root
  for (const component of file.slice(current.length).split(path.sep).filter(Boolean)) {
    current = path.join(current, component)
    const stat = fs.lstatSync(current, { throwIfNoEntry: false })
    if (!stat) {
      assert(allowMissing, `Missing managed path: ${current}`)
      return
    }
    assert(!stat.isSymbolicLink(), `Symlink in managed path: ${current}`)
    const directory = current !== file || kind === 'directory'
    assert(directory ? stat.isDirectory() : stat.isFile(), `Wrong managed path kind: ${current}`)
    if (!directory) assert.equal(stat.nlink, 1, `Hard link in managed file: ${current}`)
  }
}
checkPath(worktree, 'directory', false)
const common = spawnSync(
  commands.git,
  ['rev-parse', '--path-format=absolute', '--git-common-dir'],
  { cwd: worktree, encoding: 'utf8', env: bootstrapEnv },
)
if (common.error) throw common.error
assert.equal(common.status, 0, common.stderr)
const main = path.dirname(common.stdout.trim())
const output = path.join(main, 'target/project-inputs/query')
const source = path.join(output, 'source')
const cache = process.env.QUERY_REPO_CACHE ?? '/home/theo/.explore/repos/TanStack__query'
const metadata = path.join(output, 'metadata')
const downloads = path.join(output, 'downloads')
const tools = path.join(output, 'tools')
const nodeRoot = path.join(tools, `node-v${nodeVersion}-linux-x64`)
const node = path.join(nodeRoot, 'bin/node')
const pnpmRoot = path.join(tools, `pnpm-${pnpmVersion}/package`)
const bins = path.join(tools, 'bin')
const stateFile = path.join(metadata, 'state.json')
const commandFile = path.join(metadata, 'commands.ndjson')
const nodeArchive = path.join(downloads, `node-v${nodeVersion}-linux-x64.tar.xz`)
const pnpmArchive = path.join(downloads, `pnpm-${pnpmVersion}.tgz`)
const pnpmMetadata = path.join(downloads, `pnpm-${pnpmVersion}.json`)
const directories = [
  output,
  metadata,
  downloads,
  tools,
  bins,
  path.dirname(pnpmRoot),
  'logs',
  'tmp',
  'home',
  'cache',
  'config',
  'data',
  'pnpm-home',
  'pnpm-store',
  'cache/npm',
  'cache/pnpm',
  'cache/nx',
  'cache/nx-workspace',
].map((directory) => (path.isAbsolute(directory) ? directory : path.join(output, directory)))
function checkPrivateTree(root, packageStore = false, relative = '') {
  const directory = path.join(root, relative)
  if (!fs.lstatSync(directory, { throwIfNoEntry: false })) return
  checkPath(directory, 'directory', false)
  for (const name of fs.readdirSync(directory)) {
    const child = path.join(relative, name)
    const file = path.join(root, child)
    const stat = fs.lstatSync(file)
    if (stat.isSymbolicLink()) {
      assert(
        packageStore && /^v11\/projects\/[^/]+$/.test(child) && fs.realpathSync(file) === source,
        `Symlink in private directory: ${file}`,
      )
    } else if (stat.isDirectory()) checkPrivateTree(root, packageStore, child)
    else {
      assert(stat.isFile(), `Not a private regular file: ${file}`)
      if (!packageStore) assert.equal(stat.nlink, 1, `Hard link in private file: ${file}`)
    }
  }
}
// Validate every existing managed path before the first directory or file write.
for (const directory of [...directories, source, nodeRoot, pnpmRoot]) checkPath(directory, 'directory')
for (const directory of [
  metadata, downloads, 'logs', 'tmp', 'home', 'cache', 'config', 'data', 'pnpm-home',
])
  checkPrivateTree(path.isAbsolute(directory) ? directory : path.join(output, directory))
checkPrivateTree(path.join(output, 'pnpm-store'), true)
for (const file of [stateFile, commandFile]) checkPath(file, 'file')
function checkBins() {
  checkPath(bins, 'directory')
  if (!fs.existsSync(bins)) return
  for (const name of fs.readdirSync(bins)) {
    assert.equal(name, 'pnpm', `Unexpected tool shim: ${name}`)
    const shim = path.join(bins, name)
    assert(fs.lstatSync(shim).isSymbolicLink(), `Not a pnpm symlink: ${shim}`)
    assert.equal(
      path.resolve(bins, fs.readlinkSync(shim)),
      path.join(pnpmRoot, 'bin/pnpm.mjs'),
      'The pnpm shim leaves the pinned package',
    )
  }
}
checkBins()
function mkdir(directory) {
  inside(output, directory)
  checkPath(directory, 'directory')
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 })
  checkPath(directory, 'directory', false)
}
for (const directory of directories) mkdir(directory)

const env = {
  ...bootstrapEnv,
  PATH: systemPath,
  HOME: path.join(output, 'home'),
  XDG_CACHE_HOME: path.join(output, 'cache'),
  XDG_CONFIG_HOME: path.join(output, 'config'),
  XDG_DATA_HOME: path.join(output, 'data'),
  TMPDIR: path.join(output, 'tmp'),
  TMP: path.join(output, 'tmp'),
  TEMP: path.join(output, 'tmp'),
  PNPM_HOME: path.join(output, 'pnpm-home'),
  PNPM_MAX_WORKERS: '1',
  npm_config_cache: path.join(output, 'cache/npm'),
  npm_config_userconfig: '/dev/null',
  npm_config_update_notifier: 'false',
  GIT_CONFIG_GLOBAL: '/dev/null',
  GIT_CONFIG_NOSYSTEM: '1',
  GIT_OPTIONAL_LOCKS: '0',
  GIT_TERMINAL_PROMPT: '0',
  CI: 'true',
  TZ: 'UTC',
  LANG: 'C.UTF-8',
  LC_ALL: 'C.UTF-8',
  NO_COLOR: '1',
  FORCE_COLOR: '0',
  NODE_OPTIONS: '--max-old-space-size=1536',
  UV_THREADPOOL_SIZE: '2',
  RAYON_NUM_THREADS: '1',
  NX_DAEMON: 'false',
  NX_NO_CLOUD: 'true',
  NX_SKIP_NX_CACHE: 'true',
  NX_CACHE_DIRECTORY: path.join(output, 'cache/nx'),
  NX_WORKSPACE_DATA_DIRECTORY: path.join(output, 'cache/nx-workspace'),
  QUERY_INPUTS_SCOPED: '1',
  QUERY_REPO_CACHE: cache,
}

let state = fs.existsSync(stateFile)
  ? readJson(stateFile)
  : {
      schemaVersion: 1,
      repository: 'TanStack/query',
      pin,
      source,
      output,
      resourceLimit: { memoryBytes: 2147483648, swapBytes: 0, tasks: 128 },
      claims: { rustChecked: false, goOracleRun: false, graphParityEstablished: false },
    }
assert.equal(state.pin, pin)
assert.equal(state.schemaVersion, 1)
assert.equal(state.repository, 'TanStack/query')
assert.equal(state.output, output)
assert.equal(state.source, source)
state.resourceLimit = {
  memoryBytes: 2147483648,
  swapBytes: 0,
  tasks: 128,
  nodeHeapMiB: 1536,
  pnpmTarballWorkers: 1,
  networkConcurrency: 4,
  childConcurrency: 1,
  rayonThreads: 1,
}
function save() {
  writeFile(stateFile, `${JSON.stringify(state, null, 2)}\n`)
}
function json(file, value) {
  writeFile(file, `${JSON.stringify(value, null, 2)}\n`)
}
function readJson(file) {
  if (file.startsWith(`${metadata}/`) || file.startsWith(`${downloads}/`))
    checkPath(file, 'file', false)
  return JSON.parse(fs.readFileSync(file, 'utf8'))
}
function openFile(file, append = false) {
  inside(output, file)
  checkPath(file, 'file')
  const fd = fs.openSync(
    file,
    fs.constants.O_WRONLY |
      fs.constants.O_CREAT |
      fs.constants.O_NOFOLLOW |
      fs.constants.O_NONBLOCK |
      (append ? fs.constants.O_APPEND : 0),
    0o600,
  )
  try {
    const stat = fs.fstatSync(fd)
    assert(stat.isFile() && stat.nlink === 1, `Not a private regular file: ${file}`)
    if (!append) fs.ftruncateSync(fd, 0)
    return fd
  } catch (error) {
    fs.closeSync(fd)
    throw error
  }
}
function writeFile(file, bytes, append = false) {
  const fd = openFile(file, append)
  try {
    fs.writeFileSync(fd, bytes)
  } finally {
    fs.closeSync(fd)
  }
}
const digest = (bytes) => createHash('sha256').update(bytes).digest('hex')
async function fileHash(file, algorithm = 'sha256', encoding = 'hex') {
  const hash = createHash(algorithm)
  for await (const chunk of fs.createReadStream(file)) hash.update(chunk)
  return hash.digest(encoding)
}
function inside(root, file) {
  const relative = path.relative(root, file)
  assert(
    relative === '' ||
      (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative)),
    `Path leaves ${root}: ${file}`,
  )
}
let commandNumber = fs.readdirSync(path.join(output, 'logs')).length
let toolsVerified = false
function toolEnv() {
  assert(toolsVerified, 'Verify the complete tool archives before executing pinned tools')
  return { ...env, PATH: [path.join(nodeRoot, 'bin'), bins, systemPath].join(path.delimiter) }
}
function run(label, command, args, cwd = output, capture = false, outputFd) {
  assert([commands.git, commands.curl, commands.tar, node].includes(command), 'Unknown command path')
  for (const directory of directories) checkPath(directory, 'directory', false)
  checkPath(cwd, 'directory', false)
  const log = path.join(output, 'logs', `${String(++commandNumber).padStart(3, '0')}-${label}.log`)
  const fd = openFile(log)
  const startedAt = new Date().toISOString()
  console.log(`${label}: ${command} ${args.join(' ')}`)
  const result = spawnSync(command, args, {
    cwd,
    env: command === node ? toolEnv() : env,
    stdio: ['ignore', capture ? 'pipe' : (outputFd ?? fd), fd],
    encoding: capture ? 'utf8' : undefined,
    maxBuffer: 64 * 1024 * 1024,
  })
  if (capture && result.stdout) fs.writeSync(fd, result.stdout)
  fs.closeSync(fd)
  writeFile(
    commandFile,
    `${JSON.stringify({
      stage,
      label,
      command,
      args,
      cwd,
      log,
      startedAt,
      finishedAt: new Date().toISOString(),
      exitCode: result.status,
      signal: result.signal,
    })}\n`,
    true,
  )
  if (result.error) throw result.error
  assert.equal(result.status, 0, `${label} failed. See ${log}`)
  return capture ? result.stdout.trim() : log
}
function git(directory, ...args) {
  return run(
    'git',
    commands.git,
    ['--no-optional-locks', '-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false', ...args],
    directory,
    true,
  )
}
function verifyCache() {
  checkPath(cache, 'directory', false)
  assert.equal(git(cache, 'rev-parse', '--show-toplevel'), cache)
  assert.equal(git(cache, 'rev-parse', 'HEAD'), pin)
  assert.equal(
    git(cache, 'status', '--porcelain=v1', '--untracked-files=all'),
    '',
    'The cache is not clean',
  )
}
function verifySource() {
  checkPath(source, 'directory', false)
  checkPath(path.join(source, '.git'), 'directory', false)
  checkPath(path.join(source, 'pnpm-lock.yaml'), 'file', false)
  assert(fs.existsSync(path.join(source, '.git')), 'Prepare the source first')
  assert.equal(fs.realpathSync(source), source)
  assert.equal(git(source, 'rev-parse', '--show-toplevel'), source)
  assert.equal(git(source, 'rev-parse', 'HEAD'), pin)
  assert.equal(
    git(source, 'status', '--porcelain=v1', '--untracked-files=all'),
    '',
    'Source changed outside ignored outputs',
  )
  assert.equal(digest(fs.readFileSync(path.join(source, 'pnpm-lock.yaml'))), lockSha256)
}
async function entry(root, relative) {
  const file = path.join(root, relative)
  const stat = fs.lstatSync(file)
  if (stat.isSymbolicLink()) {
    const target = fs.readlinkSync(file)
    inside(output, path.resolve(path.dirname(file), target))
    inside(output, fs.realpathSync(file))
    return { path: relative, kind: 'symlink', target, sha256: digest(target) }
  }
  assert(stat.isFile(), `Not a file: ${file}`)
  return { path: relative, kind: 'file', bytes: stat.size, sha256: await fileHash(file) }
}
async function manifest(name, rows) {
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.path), Buffer.from(b.path)))
  const file = path.join(metadata, `${name}.json`)
  json(file, rows)
  return { file, entries: rows.length, sha256: await fileHash(file) }
}
async function prepareSource() {
  verifyCache()
  if (!fs.existsSync(source)) {
    run('clone', commands.git, [
      '-c',
      'core.hooksPath=/dev/null',
      'clone',
      '--no-hardlinks',
      '--no-checkout',
      cache,
      source,
    ])
    git(source, 'checkout', '--detach', pin)
  }
  verifySource()
  assert(
    !fs.existsSync(path.join(source, '.git/objects/info/alternates')),
    'The copy must not borrow Git objects',
  )
  const files = git(source, 'ls-tree', '-r', '--name-only', '-z', pin).split('\0').filter(Boolean)
  const rows = []
  const hooks = []
  for (const file of files) {
    rows.push(await entry(source, file))
    if (path.basename(file) !== 'package.json') continue
    const pkg = readJson(path.join(source, file))
    const scripts = Object.fromEntries(
      Object.entries(pkg.scripts ?? {}).filter(([key]) =>
        /^(preinstall|install|postinstall|prepare|prepublish|prepublishOnly|prebuild|postbuild)$/.test(
          key,
        ),
      ),
    )
    if (Object.keys(scripts).length) hooks.push({ path: file, name: pkg.name, scripts })
  }
  assert(
    !files.some((file) => /(^|\/)\.?pnpmfile\.[cm]?js$/.test(file)),
    'Review newly added pnpm hooks before running',
  )
  assert.equal(readJson(path.join(source, 'package.json')).packageManager, `pnpm@${pnpmVersion}`)
  assert.equal(fs.readFileSync(path.join(source, '.nvmrc'), 'utf8').trim(), nodeVersion)
  state.sourceManifest = await manifest('source', rows)
  state.sourceHooks = hooks
  state.lockSha256 = lockSha256
  save()
}
async function download(label, url, file, expected, algorithm = 'sha256', encoding = 'hex') {
  checkPath(file, 'file')
  if (!fs.existsSync(file)) {
    const partial = `${file}.part`
    const fd = openFile(partial)
    try {
      run(
        label,
        commands.curl,
        [
          '--disable',
          '--fail',
          '--location',
          '--retry',
          '2',
          '--connect-timeout',
          '20',
          '--max-time',
          '300',
          url,
        ],
        output,
        false,
        fd,
      )
    } finally {
      fs.closeSync(fd)
    }
    checkPath(partial, 'file', false)
    if (expected)
      assert.equal(
        await fileHash(partial, algorithm, encoding),
        expected,
        `${label} integrity mismatch`,
      )
    checkPath(file, 'file')
    fs.renameSync(partial, file)
  }
  checkPath(file, 'file', false)
  if (expected)
    assert.equal(await fileHash(file, algorithm, encoding), expected, `${label} integrity mismatch`)
}
function pnpmEntry() {
  const pkg = readJson(path.join(pnpmRoot, 'package.json'))
  assert.equal(pkg.version, pnpmVersion)
  assert.equal(pkg.name, 'pnpm')
  const file = path.resolve(pnpmRoot, pkg.bin.pnpm)
  inside(pnpmRoot, file)
  assert.equal(file, path.join(pnpmRoot, 'bin/pnpm.mjs'))
  return file
}
async function compareToolTree(expected, actual, root = actual) {
  const expectedStat = fs.lstatSync(expected)
  const actualStat = fs.lstatSync(actual)
  assert.equal(actualStat.mode & 0o7777, expectedStat.mode & 0o7777, `Tool mode differs: ${actual}`)
  if (expectedStat.isDirectory()) {
    assert(actualStat.isDirectory(), `Not a tool directory: ${actual}`)
    checkPath(actual, 'directory', false)
    const names = fs.readdirSync(expected).sort()
    assert.deepEqual(fs.readdirSync(actual).sort(), names, `Tool file list differs: ${actual}`)
    for (const name of names)
      await compareToolTree(path.join(expected, name), path.join(actual, name), root)
  } else if (expectedStat.isSymbolicLink()) {
    assert(actualStat.isSymbolicLink(), `Not a tool symlink: ${actual}`)
    assert.equal(fs.readlinkSync(actual), fs.readlinkSync(expected), `Tool symlink differs: ${actual}`)
    inside(root, fs.realpathSync(actual))
  } else {
    assert(expectedStat.isFile() && actualStat.isFile(), `Not a tool file: ${actual}`)
    assert.equal(actualStat.nlink, expectedStat.nlink, `Tool link count differs: ${actual}`)
    assert.equal(actualStat.size, expectedStat.size, `Tool size differs: ${actual}`)
    assert.equal(await fileHash(actual), await fileHash(expected), `Tool bytes differ: ${actual}`)
  }
}
async function verifyTools(prepareMissing = false) {
  toolsVerified = false
  checkPath(nodeArchive, 'file', false)
  checkPath(pnpmArchive, 'file', false)
  assert.equal(await fileHash(nodeArchive), nodeArchiveSha256, 'Node archive integrity mismatch')
  assert.equal(await fileHash(pnpmArchive), pnpmArchiveSha256, 'pnpm archive integrity mismatch')
  assert.equal(
    await fileHash(pnpmArchive, 'sha512', 'base64'),
    pnpmIntegrity.slice(7),
    'pnpm archive integrity mismatch',
  )
  checkPath(path.join(output, 'tmp'), 'directory', false)
  const temporary = fs.mkdtempSync(path.join(output, 'tmp/verify-tools-'))
  try {
    for (const [name, archive, directory, compression] of [
      ['node', nodeArchive, nodeRoot, 'J'],
      ['pnpm', pnpmArchive, pnpmRoot, 'z'],
    ]) {
      const extracted = path.join(temporary, name)
      mkdir(extracted)
      // npm omits directory entries. Keep their implicit modes stable inside the private parent.
      const mask = process.umask(0o022)
      try {
        run(`verify-${name}-archive`, commands.tar, [
          `-x${compression}pf`,
          archive,
          '--no-same-owner',
          '-C',
          extracted,
        ])
      } finally {
        process.umask(mask)
      }
      const expected = path.join(extracted, path.basename(directory))
      assert.deepEqual(fs.readdirSync(extracted), [path.basename(directory)])
      checkPath(directory, 'directory')
      if (!fs.existsSync(directory)) {
        assert(prepareMissing, `Prepare the pinned ${name} tool first`)
        mkdir(path.dirname(directory))
        fs.renameSync(expected, directory)
      } else await compareToolTree(expected, directory)
    }
    assert.deepEqual(fs.readdirSync(path.dirname(pnpmRoot)), ['package'])
    const bin = pnpmEntry()
    checkPath(node, 'file', false)
    checkPath(bin, 'file', false)
    checkBins()
    const shim = path.join(bins, 'pnpm')
    if (!fs.lstatSync(shim, { throwIfNoEntry: false })) {
      assert(prepareMissing, 'Prepare the pinned pnpm shim first')
      fs.symlinkSync(path.relative(bins, bin), shim)
    }
    assert.equal(fs.realpathSync(shim), bin)
    toolsVerified = true
  } finally {
    checkPath(temporary, 'directory', false)
    fs.rmSync(temporary, { recursive: true })
  }
}
async function prepareTools() {
  await download(
    'download-node',
    `https://nodejs.org/dist/v${nodeVersion}/${path.basename(nodeArchive)}`,
    nodeArchive,
    nodeArchiveSha256,
  )
  await download('pnpm-metadata', `https://registry.npmjs.org/pnpm/${pnpmVersion}`, pnpmMetadata)
  const pkg = readJson(pnpmMetadata)
  assert.equal(pkg.name, 'pnpm')
  assert.equal(pkg.version, pnpmVersion)
  assert.equal(pkg.dist.tarball, `https://registry.npmjs.org/pnpm/-/pnpm-${pnpmVersion}.tgz`)
  assert.equal(pkg.dist.integrity, pnpmIntegrity)
  await download(
    'download-pnpm',
    pkg.dist.tarball,
    pnpmArchive,
    pkg.dist.integrity.slice(7),
    'sha512',
    'base64',
  )
  await verifyTools(true)
  const bin = pnpmEntry()
  assert.equal(run('node-version', node, ['--version'], output, true), `v${nodeVersion}`)
  assert.equal(run('pnpm-version', node, [bin, '--version'], output, true), pnpmVersion)
  state.tools = {
    node: {
      version: nodeVersion,
      binary: node,
      sha256: await fileHash(node),
      archive: nodeArchive,
      archiveSha256: nodeArchiveSha256,
    },
    pnpm: {
      version: pnpmVersion,
      entry: bin,
      sha256: await fileHash(bin),
      tarball: pnpmArchive,
      tarballSha256: pnpmArchiveSha256,
      integrity: pkg.dist.integrity,
    },
  }
  save()
}
async function requireTools() {
  await verifyTools()
  assert.equal(process.execPath, node, 'Use the verified pinned Node stage handoff')
  assert.equal(process.version, `v${nodeVersion}`)
  assert.equal(run('pnpm-version', node, [pnpmEntry(), '--version'], source, true), pnpmVersion)
}

function installDirectory(directory) {
  inside(output, directory)
  let existing = directory
  const missing = []
  while (!fs.lstatSync(existing, { throwIfNoEntry: false })) {
    missing.unshift(path.basename(existing))
    existing = path.dirname(existing)
  }
  const resolved = fs.realpathSync(existing)
  inside(output, resolved)
  assert(fs.statSync(resolved).isDirectory(), `Not an install directory: ${existing}`)
  return path.join(resolved, ...missing)
}

function installFile(file) {
  const resolved = path.join(installDirectory(path.dirname(file)), path.basename(file))
  const stat = fs.lstatSync(resolved, { throwIfNoEntry: false })
  if (!stat) return
  assert(stat.isFile() && stat.nlink === 1, `Unsafe pnpm write file: ${file}`)
  return resolved
}

function verifyInstallRoots() {
  const pending = [
    { directory: source, modules: false },
    { directory: path.join(source, 'node_modules'), modules: true },
  ]
  const visited = new Set()
  const moduleRoots = new Set()
  while (pending.length) {
    const { directory, modules, binaries = false } = pending.pop()
    const resolved = installDirectory(directory)
    if (modules && !moduleRoots.has(resolved)) {
      moduleRoots.add(resolved)
      const manifest = installFile(path.join(resolved, '.modules.yaml'))
      installFile(path.join(resolved, '.pnpm-workspace-state-v1.json'))
      const layout = manifest ? readJson(manifest) : {}
      assert(layout && typeof layout === 'object' && !Array.isArray(layout), 'Invalid pnpm layout')
      const virtualStore = layout.virtualStoreDir ?? '.pnpm'
      assert.equal(typeof virtualStore, 'string', 'Invalid pnpm virtual store')
      const virtualDirectory = installDirectory(path.resolve(resolved, virtualStore))
      installFile(path.join(virtualDirectory, 'lock.yaml'))
      pending.push({ directory: virtualDirectory, modules: false })
      if (layout.storeDir !== undefined) {
        assert.equal(typeof layout.storeDir, 'string', 'Invalid pnpm package store')
        installDirectory(path.resolve(resolved, layout.storeDir))
      }
    }
    const visitKey = `${binaries}:${resolved}`
    if (visited.has(visitKey) || !fs.existsSync(resolved)) continue
    visited.add(visitKey)
    // Git ignores module roots. Visit every directory, including internal package links.
    for (const entry of fs.readdirSync(resolved, { withFileTypes: true })) {
      if (entry.name === '.git') continue
      const file = path.join(resolved, entry.name)
      const stat = fs.lstatSync(file)
      if (stat.isSymbolicLink()) {
        inside(output, path.resolve(resolved, fs.readlinkSync(file)))
        const target = fs.realpathSync(file)
        inside(output, target)
        const targetStat = fs.statSync(target)
        assert(targetStat.isDirectory() || targetStat.isFile(), `Unsafe install link: ${file}`)
        if (targetStat.isDirectory()) {
          pending.push({
            directory: target,
            modules: entry.name === 'node_modules',
            binaries: binaries || entry.name === '.bin',
          })
        } else if (binaries) {
          assert.equal(targetStat.nlink, 1, `Unsafe pnpm write file: ${file}`)
        }
      } else if (stat.isDirectory()) {
        pending.push({
          directory: file,
          modules: entry.name === 'node_modules',
          binaries: binaries || entry.name === '.bin',
        })
      } else {
        assert(stat.isFile(), `Unsafe install file: ${file}`)
        if (binaries) installFile(file)
      }
    }
  }
}

async function install() {
  verifySource()
  verifyInstallRoots()
  await requireTools()
  state.prepared = false
  state.install = { complete: false, scriptsExecuted: false, filtered: false }
  state.builds = []
  delete state.dependencyManifest
  delete state.generatedManifest
  delete state.generatedDeclarations
  delete state.configs
  save()
  const args = [
    pnpmEntry(),
    'install',
    '--frozen-lockfile',
    '--ignore-scripts',
    '--network-concurrency=4',
    '--child-concurrency=1',
    '--store-dir',
    path.join(output, 'pnpm-store'),
    '--reporter=append-only',
  ]
  const log = run('install', node, args, source)
  verifySource()
  state.install = { complete: true, scriptsExecuted: false, filtered: false, log }
  save()
}
async function build() {
  verifySource()
  await requireTools()
  assert(state.install?.complete, 'A successful frozen install is required')
  state.prepared = false
  state.builds = []
  delete state.generatedManifest
  delete state.generatedDeclarations
  delete state.configs
  save()
  // These are upstream scripts. The NodeNext exports need both formats and both packages.
  for (const [name, scriptName] of [
    ['@tanstack/query-core', 'build'],
    ['@tanstack/react-query', 'build:tsdown'],
  ]) {
    const buildDirectory = path.join(source, 'packages', name.split('/')[1], 'build')
    inside(source, buildDirectory)
    checkPath(buildDirectory, 'directory')
    const log = run(
      `build-${name.split('/')[1]}`,
      node,
      [pnpmEntry(), '--filter', name, 'run', scriptName],
      source,
    )
    state.builds.push({ name, script: scriptName, complete: true, log })
    save()
  }
  verifySource()
}
async function walk(root, select) {
  const rows = []
  async function visit(relative) {
    for (const item of fs.readdirSync(path.join(root, relative), { withFileTypes: true })) {
      const file = path.join(relative, item.name)
      if (item.name === '.git') continue
      if (item.isDirectory()) await visit(file)
      else if (select(file)) rows.push(await entry(root, file))
    }
  }
  await visit('')
  return rows
}
const configs = [
  [
    'query-core',
    'packages/query-core/tsconfig.prod.json',
    '0e4ba739fe52b0847accf3368ffabde25f9afdb6cb1b5a4a4ec681a70c6dbb06',
  ],
  [
    'query-persistence',
    'packages/query-persist-client-core/tsconfig.prod.json',
    '0c0ad8ffff35c95e8c6bd29d860f9a3f51d17a0cf01dae90f5867b1263cbc140',
  ],
  [
    'query-sync-storage',
    'packages/query-sync-storage-persister/tsconfig.prod.json',
    '130383e8682ec769f6e036d47c998ffbd8c4ef3455ad61c63152dab89040ed4f',
  ],
  [
    'query-async-storage',
    'packages/query-async-storage-persister/tsconfig.prod.json',
    '091e33d70eda7340fb5bdd7dc84cca09545aa6c38843c6ec5b4bde8861f7f64e',
  ],
  [
    'query-broadcast',
    'packages/query-broadcast-client-experimental/tsconfig.prod.json',
    '8fd34f3b074d10b3e9f1aae8ac20d6534c39116b1593b6bfa626aa2d1ca8442a',
  ],
  [
    'query-nodenext',
    'integrations/react-nodenext/tsconfig.json',
    'bd737bcff9461a3ce63b470c8897f3f473a3758cf6a802d8514df5265eeea541',
  ],
]
async function inventory() {
  verifySource()
  await requireTools()
  assert(
    state.install?.complete && state.builds?.length === 2,
    'Install and declaration builds are required',
  )
  state.prepared = false
  save()
  const require = createRequire(path.join(source, 'package.json'))
  const typescript = require.resolve('typescript')
  const ts = require(typescript)
  assert.equal(ts.version, '6.0.3')
  const reports = []
  const libraryFiles = new Map()
  const resolutions = []
  async function resolveInput(name, containingFile, options, mode, expected) {
    const resolved = ts.resolveModuleName(
      name,
      containingFile,
      options,
      ts.sys,
      undefined,
      undefined,
      mode,
    ).resolvedModule
    assert(resolved, `Missing package input: ${name} from ${containingFile}`)
    const file = fs.realpathSync(resolved.resolvedFileName)
    inside(source, file)
    if (expected) assert.equal(file, path.join(source, expected))
    resolutions.push({
      name,
      from: path.relative(source, containingFile),
      mode: ts.ModuleKind[mode],
      packageId: resolved.packageId,
      file: await entry(source, path.relative(source, file)),
    })
    return file
  }
  for (const [id, config, expectedRoots] of configs) {
    const filename = path.join(source, config)
    const parsed = ts.getParsedCommandLineOfConfigFile(
      filename,
      {},
      {
        ...ts.sys,
        onUnRecoverableConfigFileDiagnostic(error) {
          throw new Error(ts.flattenDiagnosticMessageText(error.messageText, '\n'))
        },
      },
    )
    assert(parsed && parsed.errors.length === 0)
    assert.equal(parsed.options.strict, true)
    const files = parsed.fileNames.map((file) => path.relative(source, file)).sort()
    const rootList = `${files.join('\n')}\n`
    assert.equal(digest(rootList), expectedRoots, `${config} root selection changed`)
    writeFile(path.join(metadata, `${id}.roots`), rootList)
    if (id !== 'query-nodenext') {
      assert.deepEqual(parsed.options.customConditions, ['@tanstack/custom-condition'])
      assert.deepEqual(parsed.options.types, ['node'])
    } else assert.deepEqual(parsed.options.customConditions ?? [], [])
    const list = run(
      `files-${id}`,
      node,
      [
        path.join(path.dirname(typescript), 'tsc.js'),
        '--project',
        filename,
        '--listFilesOnly',
        '--pretty',
        'false',
      ],
      source,
      true,
    )
    const loaded = []
    for (const file of list.split('\n').filter(Boolean)) {
      inside(source, path.resolve(file))
      loaded.push(await entry(source, path.relative(source, file)))
    }
    for (const file of loaded) {
      if (
        path.dirname(path.join(source, file.path)) === path.dirname(typescript) &&
        /^lib\..*\.d\.ts$/.test(path.basename(file.path))
      ) {
        libraryFiles.set(file.path, file)
      }
    }
    if (id === 'query-nodenext') {
      for (const [mode, input, extension] of [
        [ts.ModuleKind.ESNext, 'hooks.ts', 'd.ts'],
        [ts.ModuleKind.CommonJS, 'hooks.cts', 'd.cts'],
      ]) {
        const react = await resolveInput(
          '@tanstack/react-query',
          path.join(source, 'integrations/react-nodenext/src', input),
          parsed.options,
          mode,
          `packages/react-query/build/modern/index.${extension}`,
        )
        await resolveInput(
          '@tanstack/query-core',
          react,
          parsed.options,
          mode,
          `packages/query-core/build/modern/index.${extension}`,
        )
      }
    } else if (id !== 'query-core') {
      await resolveInput(
        '@tanstack/query-core',
        parsed.fileNames[0],
        parsed.options,
        ts.ModuleKind.ESNext,
        'packages/query-core/src/index.ts',
      )
      if (id === 'query-sync-storage' || id === 'query-async-storage') {
        await resolveInput(
          '@tanstack/query-persist-client-core',
          parsed.fileNames[0],
          parsed.options,
          ts.ModuleKind.ESNext,
          'packages/query-persist-client-core/src/index.ts',
        )
      }
      if (id === 'query-broadcast')
        await resolveInput(
          'broadcast-channel',
          parsed.fileNames[0],
          parsed.options,
          ts.ModuleKind.ESNext,
        )
    }
    const chain = [...(parsed.options.configFile.extendedSourceFiles ?? []), filename]
    reports.push({
      id,
      config,
      roots: files.length,
      rootListSha256: digest(rootList),
      configChain: await Promise.all(
        chain.map((file) => entry(source, path.relative(source, file))),
      ),
      options: Object.fromEntries(
        Object.entries(parsed.options).filter(([key]) => key !== 'configFile'),
      ),
      references: (parsed.projectReferences ?? []).map((reference) =>
        path.relative(source, reference.path),
      ),
      loadedFiles: await manifest(`${id}.typescript-files`, loaded),
    })
  }
  for (const name of ['query-core', 'react-query']) {
    for (const extension of ['d.ts', 'd.cts'])
      assert(fs.existsSync(path.join(source, `packages/${name}/build/modern/index.${extension}`)))
  }
  const dependencies = await walk(
    source,
    (file) => file.startsWith('node_modules/') || file.includes('/node_modules/'),
  )
  const generated = await walk(source, (file) =>
    /^packages\/(query-core|react-query)\/build\//.test(file),
  )
  const hooks = []
  const invalidManifests = []
  for (const file of dependencies) {
    if (file.kind !== 'file' || !file.path.endsWith('/package.json')) continue
    let pkg
    try {
      pkg = readJson(path.join(source, file.path))
    } catch {
      invalidManifests.push(file.path)
      continue
    }
    if (pkg === null || typeof pkg !== 'object' || Array.isArray(pkg)) {
      invalidManifests.push(file.path)
      continue
    }
    const scripts = Object.fromEntries(
      Object.entries(pkg.scripts ?? {}).filter(([key]) =>
        /^(preinstall|install|postinstall|prepare)$/.test(key),
      ),
    )
    if (Object.keys(scripts).length)
      hooks.push({ path: file.path, name: pkg.name, version: pkg.version, scripts })
  }
  json(path.join(metadata, 'dependency-hooks.json'), { executed: false, hooks, invalidManifests })
  const layout = readJson(path.join(source, 'node_modules/.modules.yaml'))
  inside(output, layout.storeDir)
  inside(source, path.resolve(source, 'node_modules', layout.virtualStoreDir))
  assert.deepEqual(layout.included, {
    dependencies: true,
    devDependencies: true,
    optionalDependencies: true,
  })
  json(path.join(metadata, 'package-manager-layout.json'), layout)
  const workspace = JSON.parse(
    run(
      'workspace-list',
      node,
      [pnpmEntry(), 'list', '--recursive', '--depth', '-1', '--json'],
      source,
      true,
    ),
  )
  json(path.join(metadata, 'workspace.json'), workspace)
  json(path.join(metadata, 'resolutions.json'), resolutions)
  state.workspaceProjects = workspace.length
  state.pendingBuilds = layout.pendingBuilds
  state.libraryManifest = await manifest('libraries', [...libraryFiles.values()])
  state.resolutions = {
    file: path.join(metadata, 'resolutions.json'),
    sha256: await fileHash(path.join(metadata, 'resolutions.json')),
  }
  state.dependencyManifest = await manifest('dependencies', dependencies)
  state.generatedManifest = await manifest('generated', generated)
  state.generatedDeclarations = await manifest(
    'generated-declarations',
    generated.filter((file) => /\.d\.[cm]?ts$/.test(file.path)),
  )
  state.typescript = { version: ts.version, file: typescript, sha256: await fileHash(typescript) }
  state.configs = reports
  state.prepared = true
  state.discoveryNote =
    'TypeScript listFilesOnly results are input evidence, not typechecking or Go/Rust graph parity.'
  verifySource()
  verifyCache()
  save()
}

try {
  if (stage === 'source' || stage === 'all') await prepareSource()
  if (stage === 'tools' || stage === 'all') await prepareTools()
  if (!['source', 'tools'].includes(stage) && process.execPath !== node) {
    await verifyTools()
    const result = spawnSync(node, [script, stage], { cwd: worktree, env: toolEnv(), stdio: 'inherit' })
    if (result.error) throw result.error
    process.exit(result.status ?? 1)
  }
  if (stage === 'install' || stage === 'all') await install()
  if (stage === 'build' || stage === 'all') await build()
  if (stage === 'inventory' || stage === 'all') await inventory()
  if (stage === 'replay') {
    assert(state.prepared, 'Collect the first inventory before replay')
    const before = {
      generated: state.generatedManifest.sha256,
      declarations: state.generatedDeclarations.sha256,
      files: state.configs.map((config) => [config.id, config.loadedFiles.sha256]),
    }
    await build()
    await inventory()
    const after = {
      generated: state.generatedManifest.sha256,
      declarations: state.generatedDeclarations.sha256,
      files: state.configs.map((config) => [config.id, config.loadedFiles.sha256]),
    }
    state.replay = { before, after, identical: JSON.stringify(before) === JSON.stringify(after) }
    assert.deepEqual(after, before, 'Generated inputs changed during build replay')
  }
  delete state.lastFailure
  save()
  console.log(`Recorded ${stage} at ${stateFile}`)
} catch (error) {
  state.prepared = false
  state.lastFailure = { stage, message: error.message, at: new Date().toISOString() }
  save()
  console.error(error.message)
  process.exitCode = 1
}
