// Solver verdict: UNSUPPORTED (non-literal bound `n`: the oracle checks
// the body return — 1x TS2322 — while the subset declines the whole
// declaration with a distinct recorded reason).
function total(n: number): number {
  for (let i = 0; i < n; i++) {
    return "oops";
  }
  return 2;
}
