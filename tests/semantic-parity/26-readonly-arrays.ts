export {};

declare function takesRo(xs: ReadonlyArray<number>): void;
declare function takesRoSyntax(xs: readonly number[]): void;
declare function takesMut(xs: number[]): void;
takesRo([1, 2] as const);
takesRoSyntax([1, 2] as const);
takesMut([1, 2] as const);
const constTuple = [1, 2] as const;
takesRo(constTuple);
takesMut(constTuple);
const roVar: readonly number[] = [1, 2];
takesMut(roVar);
takesRo(roVar);
const mutFromRo: number[] = roVar;
const roFromMut: readonly number[] = [1, 2].map(x => x);
const roAssign: ReadonlyArray<number> = [1, 2] as const;
const roSyntaxAssign: readonly number[] = [1, 2] as const;
const wrongElem: readonly string[] = [1, 2] as const;
roVar.push(3);

const m: number[] = [1, 2] as const;
let n: number[]; n = [1, 2] as const;
