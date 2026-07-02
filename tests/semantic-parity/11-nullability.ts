export {};

let x: string | null = null;
x.toUpperCase();

declare function assert(value: any): asserts value;
function branch(value: string | undefined, flag: boolean) {
    flag ? (assert(value), value.length) : value.length;
    value.length;
}

let value: string | number = 1;
if (typeof value === "string") { value.length; }
let other: string | null = null;
if (other !== null) { other.length; } else { other.length; }
