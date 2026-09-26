export interface Point {
  x: number;
  y: number;
}

export class Box {
  constructor(
    public min: Point,
    public max: Point,
  ) {}

  get width(): number {
    return this.max.x - this.min.x;
  }
}
