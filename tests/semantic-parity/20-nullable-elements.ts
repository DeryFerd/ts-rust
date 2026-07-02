export {};

interface User { tags?: string[] }
declare const u: User;
const first: string = u.tags[0];
declare const arr: number[] | null;
arr[0];
declare const dict: { [k: string]: number } | undefined;
dict["a"];
