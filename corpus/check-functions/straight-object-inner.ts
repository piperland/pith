// Solver verdict: DIAGNOSED (inner object literals check through the
// object path; oracle TS2322 on the wrong member).
function shaped(n: number): number {
  const o: { a: number } = { a: "oops" };
  return 1;
}
