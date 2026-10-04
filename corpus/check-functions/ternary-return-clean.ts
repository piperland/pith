// Solver verdict: silent (ternary return with checkable literal arms;
// oracle clean — each arm checks independently through the join path).
function retClean(flag: boolean): number {
  return flag ? 1 : 2;
}
