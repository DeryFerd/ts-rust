export interface Point {
  x: number;
  y: string;
}

export function make(x: number, y: number): Point {
  return { x, y: String(y) };
}
