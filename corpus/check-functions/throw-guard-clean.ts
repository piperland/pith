// Solver verdict: silent (guard-throw join; oracle clean — the throw
// accepts any value and emits no verdict while the tail checks normally).
function guardThrow(x: boolean): number {
  if (x) throw new Error("x");
  return 1;
}
