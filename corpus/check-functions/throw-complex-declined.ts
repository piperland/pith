// Solver verdict: UNSUPPORTED (if/else with a throw branch; oracle clean
// — throw positions outside guard-throw/straight shapes stay declined with
// a distinct recorded reason, never a partial verdict).
function branchThrow(x: boolean): number {
  if (x) return 1;
  else throw new Error("y");
}
