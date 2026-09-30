// Solver verdict: 1x PITH2554 (`Expected 1-2 arguments, but got 3.`) at
// the first excess argument.
function opt(a: number, b?: number): number {
  return 1;
}
opt(1, 2, 3);
