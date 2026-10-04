// Solver verdict: one PITH2322 (oracle TS2322 at the else arm — same
// per-arm rule as the then arm).
function retElseWrong(flag: boolean): number {
  return flag ? 1 : "oops";
}
