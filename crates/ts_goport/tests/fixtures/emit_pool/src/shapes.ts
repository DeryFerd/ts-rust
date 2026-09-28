export class Shape {
  static count = 0;
  readonly id = Shape.count++;
  sides: number[] = [];

  constructor(public name: string) {}

  total(): number {
    let sum = 0;
    for (let i = 0; i < arguments.length; i++) {
      sum += arguments[i];
    }
    return sum + this.sides.length;
  }
}

export const Square = class Sq extends Shape {
  static unit = 1;
  size = Sq.unit;
};

export namespace Area {
  export const scale = 2;
  export function of(shape: Shape): number {
    return shape.sides.length * scale;
  }
}
