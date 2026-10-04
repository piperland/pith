// Solver verdict: silent on `b` (the single level checks), UNSUPPORTED on
// `c` (depth-2+ chains are outside the subset; oracle TS2322 — pinned
// divergence, never a forced verdict).
const a: number = 1;
const b: number = a;
const c: string = b;
