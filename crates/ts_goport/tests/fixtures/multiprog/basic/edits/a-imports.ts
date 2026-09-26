import { area } from "./d";

export interface Point {
  x: number;
  y: string;
}

export function make(x: number, y: number): Point {
  return { x, y: String(y) };
}

export const box: number = area({ width: 3, height: 4 });
