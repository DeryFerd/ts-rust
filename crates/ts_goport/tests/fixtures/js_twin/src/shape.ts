import { Kind, Flags, Kinds } from "./kinds";
import { Model } from "./model";

export interface Shape {
  kind: Kind;
  size: number;
}

export function readable(flags: Flags): boolean {
  return Kinds.has(flags, Flags.Read);
}

export class Sized<T extends Shape> {
  static #count = 0;
  private items: T[] = [];
  add(item: T): this {
    Sized.#count++;
    this.items.push(item);
    return this;
  }
  get total() {
    return this.items.reduce((sum, { size }) => sum + size, 0);
  }
}

export const first = new Model({ kind: Kind.Circle, size: Flags.Write });
