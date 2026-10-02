// Solver verdict: DIAGNOSED (straight body with a mid-sequence throw;
// oracle TS2322 on the inner declarator — positions check independently).
function straightThrowInner(): number {
  const x: number = "oops";
  throw new Error("x");
  return 2;
}
