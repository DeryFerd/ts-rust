import { Effect } from "effect";

export const make = (n: number) => Effect.succeed(n);
export type Program = Effect.Effect<number>;
