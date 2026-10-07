import { Effect } from "effect";

export const date = new Date();
export const random = Math.random();
export const failure = Effect.fail(new Error("still an error"));
export const parsed = JSON.parse("{}");
