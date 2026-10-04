// Solver verdict: UNSUPPORTED (a call arm declines the whole declaration
// distinctly — oracle TS2322 at the wrong literal arm, a pinned
// oracle-error divergence: no partial verdict over the checkable arm).
function tagRet(): number {
  return 1;
}
function retCallArm(flag: boolean): number {
  return flag ? tagRet() : "oops";
}
