import { makeUser, type User } from "./dep.js";

export interface Result<T> {
    value: T;
}

const names: readonly string[] = ["Ada", "Grace", "Linus"] as const;

export const users = names.map((name, id) =>
    makeUser({ id, name } satisfies User),
);

export const result: Result<User[]> = { value: users };
