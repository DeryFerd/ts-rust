pub const MISSING_TYPE: &str = "// @filename: a.ts\nenum E { A = 0 / 0, B }\n";

pub const CALLABLE_DISPLAY: &str = r"// @noEmit: true
const example: { (): void; items?: string[] } = () => undefined;
example.items = [];
";

pub const FATAL_WITH_DIAGNOSTICS: &str = r"// @target: es2015
// @lib: es5
// @noEmit: true
// @Filename: /node_modules/foo/index.d.ts
declare function foo(): void;
declare namespace foo { export const items: string[]; }
export = foo;
// @Filename: /a.d.ts
declare module 'mymod' { import * as foo from 'foo'; export { foo }; }
// @Filename: /b.d.ts
declare module 'mymod' { export const foo: number; }
// @Filename: /augment.ts
declare global { interface Array<T> { customMethod(): T; } }
export {};
// @Filename: /index.ts
import * as foo from 'foo';
const items = foo.items;
const result: string = items.customMethod();
const fresh: string[] = [];
const result2: string = fresh.customMethod();
";

pub const DISABLED_CHECKER: &str = "// @noCheck: true\nconst value: number = 1;\n";
