export {};

interface P { a: number; b: number }
const single: { a: number } = { a: 1, b: 2, c: 3 };
const both: P = { a: "s", extra: 1, b: 2 };
const two: P = { a: "s", b: "t" };
const wrongMap: Array<string> = [1, 2].map(value => value + 1);
const blockMap: string[] = [1, 2].map(v => { return v + 1; });
