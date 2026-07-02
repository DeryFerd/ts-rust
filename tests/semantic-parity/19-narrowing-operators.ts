export {};

interface Animal { name: string }
interface Dog extends Animal { bark(): void }
declare const pet: Animal;
if ("bark" in pet) { (pet as Dog).bark(); }
declare const maybe: unknown;
if (typeof maybe === "string") { maybe.toUpperCase(); }
maybe.toUpperCase();
const [head = 0, ...rest] = [1, 2, 3];
const sum: number = head + rest.length;
function spread(...parts: string[]): string { return parts.join(""); }
spread("a", "b", 1);
const val = null ?? "fallback";
const upper: string = val.toUpperCase();
