export {};

interface Hooks { onDone?: () => void }
declare const hooks: Hooks;
hooks.onDone();
hooks.onDone?.();
declare const cb: (() => number) | null;
cb();
const n: number | undefined = cb?.();
declare const gated: (() => void) | undefined;
if (gated) { gated(); }
