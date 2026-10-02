// Solver verdict: SILENT (counted-for body plus a clean tail, each
// checked independently through the join path).
function total(): number {
  for (let i = 0; i < 3; i++) {
    return 1;
  }
  return 2;
}
