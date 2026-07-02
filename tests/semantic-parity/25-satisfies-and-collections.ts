export {};

const config = { retries: 3, verbose: true } satisfies { retries: number; verbose?: boolean };
const wrongSat = { retries: "many" } satisfies { retries: number };
type Route = `/${string}`;
const ok: Route = "/users";
const notRoute: Route = "users";
const ids = new Map<string, number>();
ids.set("a", 1);
ids.set("b", "two");
const found: number | undefined = ids.get("a");
const nums = new Set([1, 2, 3]);
nums.add("four");
