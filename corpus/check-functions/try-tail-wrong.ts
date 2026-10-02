// Solver verdict: DIAGNOSED (clean arms, wrong tail return; oracle TS2322
// at the tail, now checked as another position through the join path).
function fetchCount(flag: boolean): number {
  try {
    return 1;
  } catch {
    return 2;
  }
  return "oops";
}
