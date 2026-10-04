// Solver verdict: one PITH2322 (oracle TS2322 at the then arm — the wrong
// arm diagnoses at its own span while the clean arm stays silent).
function retThenWrong(flag: boolean): number {
  return flag ? "oops" : 2;
}
