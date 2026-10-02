// Solver verdict: UNSUPPORTED (finally clause; oracle clean — the subset
// declines every finally shape with a distinct recorded reason).
function fetchCount(flag: boolean): number {
  try {
    return 1;
  } catch {
    return 2;
  } finally {
    return 3;
  }
}
