// Solver verdict: UNSUPPORTED (nested ternaries decline distinctly —
// oracle TS2322 with the union spelling, a pinned oracle-error divergence:
// the subset joins one level only, never recursively).
const flag: boolean = true;
const other: boolean = false;
const tNested: number = flag ? (other ? 1 : "oops") : 3;
