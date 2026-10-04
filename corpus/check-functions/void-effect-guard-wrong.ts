// Solver verdict: DIAGNOSED (guard-effect join; oracle TS2322 on the tail
// return — the arm emits no verdict while the tail checks normally).
function guardWarnWrong(drop: boolean): void {
  if (drop) {
    console.warn("dropping");
    return;
  }
  return "oops";
}
