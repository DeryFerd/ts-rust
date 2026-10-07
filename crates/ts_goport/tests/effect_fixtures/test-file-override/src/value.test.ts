import { Effect } from "effect";

// Outside an Effect context the rule does not apply.
export const plain = JSON.parse("{}");

export const inEffect = Effect.gen(function* () {
  const text = yield* Effect.succeed("{}");
  return JSON.parse(text);
});
