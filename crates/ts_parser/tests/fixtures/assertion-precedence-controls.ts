export const mixed1 = 1 + 1 as number satisfies number * 2;
export const mixed2 = 1 + 1 satisfies number as number * 2;
export const grouped = (1 + 1 as number satisfies number) * 2;
export const unary = 1 as number satisfies number * 2;
export const shift = 1 < 1 as boolean >> 2;
export const power = 1 + 1 as number ** 2;
export const equal = 1 * 1 as number * 2;
export const lower = 1 * 1 as number + 2;
export const later = 1 * 1 as number + 2 as number * 3;
export const equalPower = 2 ** 3 as number ** 2;
declare function as(value: number): number;
declare function satisfies(value: number): number;
const line1 = 1
as(2);
const line2 = 2
satisfies(3);
