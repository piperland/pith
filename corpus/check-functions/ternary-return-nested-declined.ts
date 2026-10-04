// Solver verdict: UNSUPPORTED (a nested ternary arm declines the whole
// declaration distinctly — oracle TS2322 at the inner wrong arm, a pinned
// oracle-error divergence: the subset joins one level only).
function retNested(flag: boolean, other: boolean): number {
  return flag ? (other ? 1 : "x") : 2;
}
