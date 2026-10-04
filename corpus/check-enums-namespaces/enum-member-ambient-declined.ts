// Solver verdict: 2x UNSUPPORTED (`declare enum` accepts every member
// reference in tsc) — pinned divergence (ambient values stay unknown).
declare enum Amb { A, B }
const a: Amb = Amb.A;
const b: Amb = Amb["B"];
