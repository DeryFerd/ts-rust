export enum Color {
  Red,
  Green = "green",
}

export function paint(color: Color): string {
  return `color ${color}`;
}
