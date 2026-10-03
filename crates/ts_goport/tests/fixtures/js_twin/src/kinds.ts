export enum Kind {
  Box = "box",
  Circle = "circle",
}

export const enum Flags {
  None = 0,
  Read = 1 << 0,
  Write = 1 << 1,
}

export namespace Kinds {
  export const all = [Kind.Box, Kind.Circle];
  export function has(flags: Flags, flag: Flags) {
    return (flags & flag) !== 0;
  }
}
