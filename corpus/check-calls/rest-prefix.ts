// Solver verdict: 1x PITH2345 (rest extra against the element type) plus
// 1x PITH2555 (`Expected at least 1 arguments, but got 0.`); the
// fully-supplied call is silent.
function rs(a: number, ...rest: number[]): number {
  return 1;
}
rs(1, 2, 3);
rs(1, "oops");
rs();
