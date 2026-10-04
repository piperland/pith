// Solver verdict: DIAGNOSED (guard-chain returns; oracle TS2322 on the
// second guard return — each position checks independently).
function chained(a: boolean, b: boolean, c: boolean): number {
  if (a) return 1;
  if (b) return "oops";
  if (c) return 3;
  return 4;
}
