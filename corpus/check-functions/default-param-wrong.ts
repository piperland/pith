// Solver verdict: one PITH2322 (oracle TS2322) — the literal-defaulted
// parameter's declared type propagates one level (P070), diagnosing at the
// use span exactly like a required parameter.
function fromDefault(n: number = 1): number {
  const x: string = n;
  return 1;
}
