// Solver verdict: UNSUPPORTED (cyclic identifier initializers are outside
// the subset; oracle spells TS2448 plus TS2454 — pinned divergence, never
// a forced verdict).
const a: number = b;
const b: number = a;
