// Solver verdict: DIAGNOSED (else-if chain middle branch; oracle TS2322
// at the branch return, now checked per-branch through the join path).
function pick(flag: boolean, other: boolean): number {
  if (flag) {
    return 1;
  } else if (other) {
    return "oops";
  } else {
    return 3;
  }
}
