// Solver verdict: DIAGNOSED (wrong try return; oracle TS2322 in the try
// arm, now checked per-position through the join path).
function fetchCount(flag: boolean): number {
  try {
    return "oops";
  } catch {
    return 2;
  }
}
