// Solver verdict: one PITH2322 (oracle TS2322) — the parameter's declared
// type propagates one level (P048: first divergence-to-match flip).
function fromParam(n: number): number {
  const x: string = n;
  return 1;
}
