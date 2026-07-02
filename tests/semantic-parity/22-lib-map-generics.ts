export {};

const ids = new Map<string, number>();
const wrongGet: string = ids.get("a");
const inferredMap = new Map([["a", 1]]);
const wrongGet2: string = inferredMap.get("a");
ids.set(1, 2);
