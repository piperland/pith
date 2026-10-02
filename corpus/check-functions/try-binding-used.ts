// Solver verdict: UNSUPPORTED (used catch binding classifies NonLiteral;
// the existing position-naming gate declines the whole declaration with
// zero diagnostics, where the oracle diagnoses `unknown`).
function fetchCount(flag: boolean): number {
  try {
    return 1;
  } catch (e) {
    return e;
  }
}
