// Solver verdict: silent + 1 UNSUPPORTED (the `{}` default carries no
// literal fact, so the use keeps the historical optional decline with its
// byte-identical reason; oracle declaration-errors `TS2322` at the parameter
// plus `TS2322` at the use — pinned divergence, never a forced verdict).
function fromBrace(n: number = {}): number {
  const x: string = n;
  return 1;
}
