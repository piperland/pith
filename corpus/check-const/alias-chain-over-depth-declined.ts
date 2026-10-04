// Solver verdict: 2 UNSUPPORTED, one per use (nine links exceed the
// eight-link bound; the oracle resolves the chain - pinned divergence by
// design, since tsc has no depth limit).
type A0 = number;
type A1 = A0;
type A2 = A1;
type A3 = A2;
type A4 = A3;
type A5 = A4;
type A6 = A5;
type A7 = A6;
type A8 = A7;
type A9 = A8;
const ok: A9 = 1;
const bad: A9 = "oops";
