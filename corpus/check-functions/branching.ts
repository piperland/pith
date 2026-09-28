// Solver verdict: UNSUPPORTED (branching; oracle TS2322 in the else branch,
// invisible to the straight-line subset until the flow phase).
function pick(flag: boolean): number {
  if (flag) {
    return 1;
  } else {
    return "oops";
  }
}
