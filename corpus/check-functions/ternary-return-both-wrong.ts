// Solver verdict: two PITH2322s (oracle TS2322 at each arm — both-wrong
// reports twice, one per arm position).
function retBothWrong(flag: boolean): number {
  return flag ? "a" : "b";
}
