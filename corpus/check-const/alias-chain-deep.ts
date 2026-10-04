// Solver verdict: one PITH2322 (oracle TS2322) spelling the terminal
// primitive (P052: chains resolve transitively; tsc has no depth limit).
type A = number;
type B = A;
type C = B;
type D = C;
type E = D;
const ok: E = 1;
const bad: E = "oops";
