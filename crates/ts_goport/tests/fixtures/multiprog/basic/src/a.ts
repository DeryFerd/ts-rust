export interface Point {
  x: number;
  y: number;
}

export function make(x: number, y: number): Point {
  return { x, y };
}
