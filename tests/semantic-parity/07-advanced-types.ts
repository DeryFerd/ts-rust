export {};

type Flags<T> = { [K in keyof T]-?: boolean };
type Model = { name?: string; count: number };

const flags: Flags<Model> = { name: true };
const wrong: Pick<Model, "name"> = { count: 1 };
const key: keyof Model = "missing";
