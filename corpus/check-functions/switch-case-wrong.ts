// Solver verdict: DIAGNOSED (wrong case return; oracle TS2322 in the
// first case arm, now checked per-position through the join path).
function pick(n: number): number {
  switch (n) {
    case 1:
      return "oops";
    case 2:
      return 2;
    default:
      return 3;
  }
}
