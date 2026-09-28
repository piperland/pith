// Solver verdict: UNSUPPORTED (rest parameter is variadic; exact arity
// does not apply). The oracle is clean here — pinned divergence.
function rs(a: number, ...rest: number[]): number {
  return 1;
}
rs(1, 2, 3);
