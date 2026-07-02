export {};

enum Level { Low, High }
const l: Level = Level.Low;
const wrongEnum: Level = 5;
type Keys = keyof { a: 1; b: 2 };
const k: Keys = "a";
const badK: Keys = "c";
function assertIs(value: unknown): asserts value is string { if (typeof value !== "string") throw new Error(); }
declare const input: unknown;
assertIs(input);
input.toUpperCase();
const rec: Record<string, number> = { a: 1, b: "two" };
type Partialed = Partial<{ x: number }>;
const part: Partialed = {};
const badPart: Partialed = { x: "s" };
