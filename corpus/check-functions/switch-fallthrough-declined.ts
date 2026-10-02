// Solver verdict: UNSUPPORTED (fallthrough: the empty `case 2` falls into
// the default; oracle clean — the subset declines fallthrough with a
// distinct recorded reason).
function pick(n: number): number {
  switch (n) {
    case 1:
      return 1;
    case 2:
    default:
      return 3;
  }
}
