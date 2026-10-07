const Effect = {
  succeed: (n: number) => ({ _tag: "Success", value: n }),
  fail: (e: unknown) => ({ _tag: "Failure", error: e }),
};
const Layer = { succeed: (n: number) => n };

Effect.succeed(1);
Effect.fail(new Error("not an Effect"));
Layer.succeed(2);
export {};
