// Solver verdict: 1x PITH2322 (the loop-body return checks per position
// through the join path; the clean tail stays silent).
function total(): number {
  for (let i = 0; i < 3; i++) {
    return "oops";
  }
  return 2;
}
