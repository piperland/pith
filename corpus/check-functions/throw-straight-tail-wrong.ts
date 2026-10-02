// Solver verdict: DIAGNOSED (straight body with a mid-sequence throw;
// oracle TS2322 on the tail return — unreachable-after-throw positions
// still check).
function straightThrowTail(): number {
  const x: number = 1;
  throw new Error("x");
  return "oops";
}
