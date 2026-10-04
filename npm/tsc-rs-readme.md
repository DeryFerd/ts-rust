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

## Platforms

- Linux x64 (static, any distribution)
- macOS arm64

## License

Apache-2.0. The port keeps the license and notices of TypeScript, Copyright (c) Microsoft
Corporation.
