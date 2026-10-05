function f(cb: (x: number) => number): number {
  const g: (x: number) => number = (x) => "oops";
  return 1;
}
