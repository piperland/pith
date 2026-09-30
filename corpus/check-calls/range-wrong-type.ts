// Solver verdict: 2x PITH2345, one per site at the mismatched argument
// (in-range wrong types diagnose positionally, exactly like exact arity).
function opt(a: number, b?: number): number {
  return 1;
}
opt(1, "oops");
opt("oops", 2);
