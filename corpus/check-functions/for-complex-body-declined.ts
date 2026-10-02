// Solver verdict: UNSUPPORTED (multi-statement loop body: the oracle is
// clean on this body while the subset declines with a distinct recorded
// reason).
function total(): number {
  for (let i = 0; i < 3; i++) {
    if (i > 1) {
      break;
    }
    return 1;
  }
  return 2;
}
