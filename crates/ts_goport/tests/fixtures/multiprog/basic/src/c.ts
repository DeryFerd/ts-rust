import { at } from "./b";

// No error until a.ts makes `y` a string.
export const total: number = at(1, 2).x + at(3, 4).y;
