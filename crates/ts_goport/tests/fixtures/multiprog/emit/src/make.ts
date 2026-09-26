import { Box } from "./shapes";

export function box(size: number) {
  return new Box({ x: 0, y: 0 }, { x: size, y: size });
}
