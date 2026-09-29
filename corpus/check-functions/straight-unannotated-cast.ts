// Solver verdict: DIAGNOSED (unannotated declined casts still diagnose
// TS2352 at the operand span).
function casted(n: number): number {
  const x = ("oops" as number);
  return 1;
}
