// Solver verdict: UNSUPPORTED (two effect calls in the guard arm; oracle
// clean — the subset admits at most one effect call plus a bare return).
function guardTwoCalls(key: string, drop: boolean): void {
  if (drop) {
    console.warn("a");
    console.warn(key);
    return;
  }
  return;
}
