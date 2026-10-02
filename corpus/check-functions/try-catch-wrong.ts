// Solver verdict: DIAGNOSED (wrong catch return; oracle TS2322 in the
// catch arm, now checked per-position through the join path).
function fetchCount(flag: boolean): number {
  try {
    return 1;
  } catch {
    return "oops";
  }
}
