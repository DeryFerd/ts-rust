export {};

interface MyMap<K, V> { get(key: K): V | undefined; set(key: K, value: V): this; }
interface MyMapCtor { new <K, V>(): MyMap<K, V>; readonly prototype: MyMap<any, any>; }
declare var MyMapVar: MyMapCtor;
const m = new MyMapVar<string, number>();
m.set(1, 2);
const g: string = m.get("a");
