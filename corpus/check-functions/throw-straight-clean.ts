// Solver verdict: silent (straight body with a mid-sequence throw;
// oracle clean — the throw emits no verdict while each other position
// checks normally).
function straightThrow(): number {
  const x: number = 1;
  throw new Error("x");
  return 2;
}
