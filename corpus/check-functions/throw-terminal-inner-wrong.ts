// Solver verdict: DIAGNOSED (straight body with a terminal throw and no
// return; oracle TS2322 on the inner declarator — leadings check while the
// throw emits no verdict).
function terminalThrow(): number {
  const x: number = "oops";
  throw new Error("x");
}
