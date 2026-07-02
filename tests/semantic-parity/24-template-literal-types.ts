export {};

type Route = `/${string}`;
const ok: Route = "/users";
const notRoute: Route = "users";
type Id = `user-${number}`;
const idOk: Id = "user-42";
const idBad: Id = "user-abc";
type Pair = `${string}:${number}`;
const pairOk: Pair = "a:1";
const pairBad: Pair = "a:b";
const widened: string = idOk;
declare const plain: string;
const notTmpl: Route = plain;
