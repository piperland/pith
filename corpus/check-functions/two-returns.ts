// Solver verdict: DIAGNOSED x2 (two sequential returns, both wrong; oracle
// 2x TS2322, each return checked independently through the join path).
function pair(): number {
  return "a";
  return "b";
}
