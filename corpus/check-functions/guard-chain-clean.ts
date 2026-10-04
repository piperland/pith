// Solver verdict: silent (three guard returns plus a tail return; oracle
// clean — each position checks independently through the chain path).
function chained(a: boolean, b: boolean, c: boolean): number {
  if (a) return 1;
  if (b) return 2;
  if (c) return 3;
  return 4;
}
