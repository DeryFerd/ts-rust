# tsc-rs

A Rust port of the TypeScript 7 compiler (`tsc`).

It is a direct port of Microsoft's native TypeScript compiler, which is written in Go. On the
projects we test, it gives the same diagnostics and output as that compiler, and it is faster.

This is a preview.

## Use

```sh
npm install -D tsc-rs
npx tsc-rs -p tsconfig.json
```

`tsc-rs` takes the same options as `tsc`.

## VS Code

The TypeScript 7 extension looks for the `typescript` package, so it does not find `tsc-rs` by
itself. Point it at the dir of the `tsc` in the platform package, in `.vscode/settings.json`, and
allow it when VS Code asks:

```json
{ "js/ts.tsdk.path": "node_modules/@tsc-rs/linux-x64/lib" }
```

On macOS, use `@tsc-rs/darwin-arm64`.

## Platforms

- Linux x64 (static, any distribution)
- macOS arm64

## License

Apache-2.0. The port keeps the license and notices of TypeScript, Copyright (c) Microsoft
Corporation.
