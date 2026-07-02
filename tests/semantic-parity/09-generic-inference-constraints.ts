export {};

function identity<T extends { id: number }>(value: T): T {
    return value;
}

identity({ name: "missing" });
identity({ id: "wrong" });
identity({ id: 1, extra: 2 });
identity({});
identity({ name: "x", id: "wrong" });
identity({ name: "x", other: 1 });
const indirect = { name: "x" };
identity(indirect);
declare const half: { id: string };
identity(half);
const keep = identity({ id: 1, extra: 2 });
const n: number = keep.extra;
