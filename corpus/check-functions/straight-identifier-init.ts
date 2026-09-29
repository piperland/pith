// Solver verdict: UNSUPPORTED (identifier initializers need value-type
// facts; oracle TS2322 — pinned divergence, never a forced verdict).
function fromParam(n: number): number {
  const x: string = n;
  return 1;
}
