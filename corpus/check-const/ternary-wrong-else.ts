// Solver verdict: one PITH2322 (oracle TS2322 with the union spelling —
// arm order never surfaces: the join sorts by type identity, not source
// order, so this matches the wrong-then message exactly).
const flag: boolean = true;
const tElse: number = flag ? 1 : "oops";
