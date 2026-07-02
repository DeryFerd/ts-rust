export {};

const rec: Record<string, number> = { a: 1 };
const n: number = rec.anything;
const bad: Record<string, number> = { a: "one" };
type Dict = { [key: string]: number };
const bad2: Dict = { a: "one" };
