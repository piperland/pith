// Solver verdict: UNSUPPORTED (`let` bindings never propagate —
// reassignment is invisible to the single declaration-order pass; oracle
// TS2322 — pinned divergence, never a forced verdict).
function letSource(): number {
  let a = 1;
  const b: string = a;
  return 1;
}
