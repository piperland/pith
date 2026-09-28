// Solver verdict: 2x UNSUPPORTED (ambient enums accept every literal in
// tsc — pinned divergence).
declare enum AE { A, B }
const a1: AE = 0;
const a2: AE = AE.A;
