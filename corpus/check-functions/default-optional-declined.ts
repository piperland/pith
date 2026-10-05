// Solver verdict: silent + 1 UNSUPPORTED (the `?`-only parameter carries
// `| undefined`, which single-level propagation cannot spell — the
// historical optional decline with its byte-identical reason; oracle
// `TS2322` plus the `undefined` elaboration — pinned divergence, never a
// forced verdict).
function fromOptional(n?: number): number {
  const x: string = n;
  return 1;
}
