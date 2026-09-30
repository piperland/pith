// Solver verdict: 1x PITH2554 (`Expected 1-2 arguments, but got 0.`) at
// the callee.
function opt(a: number, b?: number): number {
  return 1;
}
opt();
