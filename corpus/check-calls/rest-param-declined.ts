// Solver verdict: silent (rest calls admit 1-or-more; the supplied call is
// in range). Formerly UNSUPPORTED (variadic arity outside the exact-count
// subset). Converted by PITH-P037: the range/member flip. The oracle is
// clean.
function rs(a: number, ...rest: number[]): number {
  return 1;
}
rs(1, 2, 3);
