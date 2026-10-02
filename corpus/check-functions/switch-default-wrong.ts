// Solver verdict: DIAGNOSED (wrong default return; oracle TS2322 in the
// default arm, now checked per-position through the join path).
function pick(n: number): number {
  switch (n) {
    case 1:
      return 1;
    case 2:
      return 2;
    default:
      return "oops";
  }
}
