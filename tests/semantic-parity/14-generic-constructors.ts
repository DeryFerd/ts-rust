export {};

interface Box<T> { value: T; map<U>(f: (v: T) => U): Box<U> }
interface BoxCtor { new <T>(v: T): Box<T> }
declare const BoxC: BoxCtor;
const b = new BoxC<number>(1);
const s: string = b.value;
const c = new BoxC("hi");
const n: number = c.value;
new BoxC<string>(42);
