// Solver verdict: DIAGNOSED twice (two wrong else-if chain branches;
// oracle 2x TS2322, now checked per-branch through the join path).
function pick(flag: boolean, other: boolean): number {
  if (flag) {
    return "bad1";
  } else if (other) {
    return "bad2";
  } else {
    return 3;
  }
}
