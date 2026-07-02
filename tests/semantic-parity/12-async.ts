export {};

async function load(): Promise<number> {
    const value = await Promise.resolve(42);
    return value;
}
async function wrong(): Promise<string> {
    return 42;
}
async function inferred() { return 1; }
const p: Promise<number> = inferred();
async function empty(): Promise<void> {}
const lam = async () => 42;
const q: Promise<number> = lam();
async function chained(): Promise<number> {
    return Promise.resolve(7);
}
