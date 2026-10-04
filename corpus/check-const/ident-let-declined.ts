// Solver verdict: UNSUPPORTED (top-level `let` emits no declarator facts —
// the LetDeclFact gap — so the name claims no checkable const declarator;
// oracle TS2322 — pinned divergence, never a forced verdict).
let a = 1;
const b: string = a;
