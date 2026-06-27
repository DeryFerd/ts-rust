export {};

function identity<T extends { id: number }>(value: T): T {
    return value;
}

identity({ name: "missing" });
identity<string>("wrong constraint");
