// Solver verdict: 1x PITH2322 (trip count is not modeled: the body
// position checks unconditionally, exactly like the oracle — a wrong
// return inside a provably zero-trip loop still reports).
function total(): number {
  for (let i = 0; i < 0; i++) {
    return "oops";
  }
  return 2;
}
