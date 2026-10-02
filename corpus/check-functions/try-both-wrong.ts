// Solver verdict: DIAGNOSED TWICE (both arms wrong; oracle 2x TS2322,
// each arm checked independently through the join path).
function fetchCount(flag: boolean): number {
  try {
    return "oops";
  } catch {
    return "bad";
  }
}
