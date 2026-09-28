export class Counter {
  static start = 0;
  value = Counter.start;

  add() {
    for (const n of arguments) {
      this.value += n;
    }
    return this.value;
  }
}
