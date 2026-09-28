import { Shape, Area } from "./shapes";
import { Color, paint } from "./colors";
import { Counter } from "./legacy.js";

export function describe(shape: Shape) {
  const counter = new Counter();
  return {
    name: shape.name,
    area: Area.of(shape),
    color: paint(Color.Red),
    count: counter.add(),
  };
}

export const first = new Shape("first");
