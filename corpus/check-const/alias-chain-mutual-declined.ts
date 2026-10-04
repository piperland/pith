// Solver verdict: silent + 1 UNSUPPORTED (the mutual cycle declines; oracle
// TS2456 at both alias declarations is the pinned gap — the subset spells
// no declaration diagnostics).
type A = B;
type B = A;
const a: A = 1;
