// Solver verdict: UNSUPPORTED (throw statement in the try arm; oracle
// clean — the subset declines throw arms with a distinct recorded reason).
function fetchCount(flag: boolean): number {
  try {
    throw new Error("x");
  } catch {
    return 2;
  }
}
