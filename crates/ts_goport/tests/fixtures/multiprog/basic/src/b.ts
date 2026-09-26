import { make, Point } from "./a";

export function at(x: number, y: number): Point {
  return make(x, y);
}

// The one error. The union text also shows the union order.
export const side: "left" | "right" = "up";
