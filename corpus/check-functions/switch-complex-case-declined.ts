// Solver verdict: UNSUPPORTED (complex case: the extra statement before
// the return needs flow facts; oracle clean — the subset declines complex
// cases with a distinct recorded reason).
function pick(n: number): number {
  switch (n) {
    case 1:
      n = 2;
      return 1;
    default:
      return 2;
  }
}
