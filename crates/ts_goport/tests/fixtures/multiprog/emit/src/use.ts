import { box } from "./make";

// The declaration emit writes these types as `import("./shapes")` types.
export const b = box(1);
export const corner = b.min;

// The one error.
export const width: string = b.max.x;
