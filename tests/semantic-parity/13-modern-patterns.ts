export {};

type Shape = { kind: "circle"; radius: number } | { kind: "square"; size: number };
function area(s: Shape): number {
    switch (s.kind) {
        case "circle": return 3.14 * s.radius * s.radius;
        case "square": return s.size * s.size;
    }
}
const bad: Shape = { kind: "circle", size: 4 };
interface User { id: number; tags?: string[] }
declare const u: User;
const first = u.tags?.[0];
const len: number = u.tags.length;
