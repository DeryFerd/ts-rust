# ts-rust-wasm

The ts-rust TypeScript compiler (`crates/ts_goport`, a Rust port of typescript-go) as one
WebAssembly module. It type-checks and emits like the native `tsgo`, in Node, Deno, Bun and
browsers. Nothing here publishes.

## Build

```sh
rustup target add wasm32-wasip1
brew install binaryen          # or a binaryen 132+ release: wasm-opt
scripts/wasm/build.sh          # writes npm/wasm/ts_rust.wasm
cd npm/wasm && npm test
```

`WASM_PROFILE=release scripts/wasm/build.sh` builds faster and larger.

## Use

Node, on the real file system:

```sh
npx tsc-wasm -p tsconfig.json
```

```js
import { tsc } from "ts-rust-wasm";

const { exitCode, stdout } = await tsc(["-p", "tsconfig.json"]);
```

In memory (Node, browsers and Deno). `files` maps absolute paths to text. The result has every
file after the run, emitted ones included:

```js
import { tsc } from "ts-rust-wasm";

const { exitCode, diagnostics, files } = await tsc(["-p", "/app"], {
    files: {
        "/app/tsconfig.json": '{ "compilerOptions": { "strict": true, "outDir": "out" } }',
        "/app/index.ts": "export const n: number = 'one';",
    },
    diagnostics: "json",
});
// diagnostics: [{ fileName: "/app/index.ts", code: 2322, category: 1, text: "...", ... }]
// files.get("/app/out/index.js")
```

`diagnostics: "json"` returns the diagnostics as objects (the TypeScript API's
`DiagnosticResponse`, with UTF-16 positions) and does not print them. Without it, `stdout` has
tsc's usual text.

In a browser, call `tsc` from a module Web Worker, as `examples/browser` does: Chrome does not let
a page's main thread make the instance, and a run blocks the page. Serve `ts_rust.wasm` as
`application/wasm`, so that it compiles while it downloads. To try the example, run
`python3 -m http.server -d npm/wasm` and open `http://localhost:8000/examples/browser/`. Very deep
nesting overflows the stack: at about 350 to 550 levels in a Chrome worker, 6,000 in Node.

## How it works

- `crates/ts_wasm` is the module: `tsc` from `ts_goport` for `wasm32-wasip1`, built with the
  `wasm` cargo profile (size first) and `wasm-opt -Oz`.
- The host (`core.js`) gives the file system through two imports (`ts_host.fs`, `fs_take`), and a
  small WASI shim gives clocks, random bytes, stdout and stderr. There is no WASI file system and
  no `node:wasi`.
- wasm has one thread. The checkers run their jobs on the calling thread
  (`program.rs` `send_thread_job`), as Go's `--singleThreaded` runs its work groups inline.
- Each run uses a new instance of the compiled module, because the compiler keeps one program per
  process. The module is compiled once.
- The checker recurses deeply. Node runs each call in a worker thread with a 256 MB stack. In a
  browser, call it from a Web Worker.
- Not supported: `--watch`, `--lsp`, `--api`, and plugins or content mappers that start
  processes. `--locale` gives English: the module has no message catalogs, to keep it small.
