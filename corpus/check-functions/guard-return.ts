// Solver verdict: DIAGNOSED (guard-then-tail returns; oracle TS2322 on the
// tail return, now checked per-return through the join path).
function guard(x: number): string {
  if (typeof x !== "string") return "dflt";
  return 1;
}
