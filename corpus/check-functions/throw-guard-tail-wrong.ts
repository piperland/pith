// Solver verdict: DIAGNOSED (guard-throw join; oracle TS2322 on the tail
// return — the throw emits no verdict while the tail checks normally).
function guardThrowWrong(x: boolean): number {
  if (x) throw new Error("x");
  return "oops";
}
