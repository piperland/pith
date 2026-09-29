// Solver verdict: DIAGNOSED (if/else branch returns; oracle TS2322 in the
// else branch, now checked per-return through the join path).
function pick(flag: boolean): number {
  if (flag) {
    return 1;
  } else {
    return "oops";
  }
}
