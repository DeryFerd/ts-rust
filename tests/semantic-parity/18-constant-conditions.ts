export {};

const fn = (() => 1) || "a";
const obj = {} || "a";
const arr = [1] || "a";
const num = 1 || "a";
const str = "s" || "a";
const boolTrue = true || "a";
const empty = "" || 1;
const zero = 0 || 1;
const flse = false || 1;
declare const someBool: boolean;
const viaBool = someBool || "a";
const nul = null ?? "x";
const undef = undefined ?? "x";
declare const definite: string;
const viaDef = definite ?? "x";
if ({}) { }
declare function g(): void;
const viaAnd = {} && 1;
